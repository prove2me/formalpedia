-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1841
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:52:06.964539+00:00
-- url     : https://prove2.me/submissions/3a52d8c9-4b8e-4df9-a59a-d154caf5519d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 330935251 ≤ n < 331115107 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 330936501 1250 330935251 330935279
    0x30a0f0501061a07261b070b040605040e04020a0317090f030303071b050a020904231c030e1507110c0d051c02070b0d02030103060c0c030f0e0f0406 65
    0x2210380d0091020644604115101c03040c400300720641814203205600105100c41444800c408000006244410380c0d0340400001b680030025081060034502d00c0c11210309030401481d0010400d64024504040c01d000004055226901c101c814074000940440d00327540d1859500e0000f941c3c000c0c0301422920341e1011101c4a900085e03403091203041c3d03c40b4500e4076414040116032140090f41d0364642c07a03241a9603140c0715a05140ea081d14584a5402900010780783c40f40703c01d004500440215100c9040e212030000c0e0a00e200c0c5600555400c0002e4002c00904142c1c0c114020b04074038100030444c3c4404441e2140b6219102c84030b00140200d02090150241e005030128000d03d1480b0203171740031080d004003032000c0d03007a80c0c4e04000d00d143c0c02440740c3d01171903070100300346001c208036441551100b5654000c1030b06503030041440343d401c45ea4004010010000544034120449105040c8040c400040d91809011800f4040c8568248108903113009400e560303100c40440f5080000701f0402c5965244e018200000d1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 330937751 1250 330936501 330936503
    0x4020a0f020c0d0203250306050f041b080a140f06070e1201020c03040b07020619200c0a060302030a0608031605121303020607170d0504020306061014030c09030a0f 72
    0x402000c02420140c284038044118007500607001b400040058a0304481c8205800c40c0303115030000030784010002500c41c0c001c650013040510040443c0c3e0910781000700c0c854034036000b10415042d00403030402c8249004140d04007207603088045002030b200103c01d018200001c0c00d000e02518007902c0204090303a81c00c03940e402c450203016210100d01e456a100a9806c0b8440c500580b511584144000c00199200c50300603d01103101a01d80c50400b0042c5105015400524039520003062212405495000d400d02001a2000441c002010b505540c0c0300440c04008403401800101500007001802410b01078020000074001c00040301d5450404125250041c1048103044031103001d44034180c1003900302d842c10b0f200001c2c105c121403c406840e40c2d003000724136842400d0488100c0c03680065254854040c4010340303548400b01801090354541441094103250f07000b03110038802c1c0890070805840c02c0d44081201040100100c01d1941e984031503074078080500403400c5040d0315110b00140b407810800c3c80c5981340901 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 330939001 1250 330937751 330937753
    0x1a1b03070323070302120306030f060411041416080a0e0d02030d0e06061e15030c2101180f0b150a080a020702060a0302070c0317040612141b0904020a0f02 68
    0x1100c60b003418a10b600c40e00c0c00103001a44146640fa1400441700021908100010220707240034040c000c4580c00c2030400c990030b440d011b04010342895142060f00405880341400d6080406900d07200203000300e10803000800c40200400f2400151030a0499030004120955600440318010100030000390f4a038486190704101904143ca07078005c13801c000904d81e009800040c0400001c00a00604c44d032121011001d071913000150502c0d9480d0b086c0200000d5024981406070f80c0c1d81c51000c07812000d100c0450960207a41c00510000401c000c1410a1510785d40c2120000c010a01465001c7c029002c1c10700e4000607940181c06170a254401601000200f03081c008907200c0400c15503e14074a88100c0c01084c03000794124604202c898140c9200e68018071495101d40d080081b0151aa20b90b00c00b00c3c41d200381c42e07620b06a00001c042c4045904130218400413071210f40c080c0801c1c49800d805506554001c0c2010f00419035840c6404041070300001a2110b03140003600440d01c03204074180091001e0100c030b51600c05 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 330940251 1250 330939001 330939047
    0x1005121f180f15080c0a03052e150914040b01120203120a0804120306060c0b04141b120307020d02060309031b010902090105032d12040801020307090e011a1b030703 72
    0x54181b45030146c0840b50004082c011800184021529060756055014100a15000010408a0180300300030b0982100311124407a2802e001c05882201d0003028290000b840071020000090502018203040d0f48004820064120651001c24549105c0362101c11450401144482806500c00c0d41c8510540c05000b005000088011050f82219540d002c2c00c1c000400b001261000b04120b013840603006489011164000d06046140b5410700e8014074031440f81e4111141c0500d014a0700350540c040409045028500c0d11403a640015810b01c5810300082c0030380004030010304041d5062054a0344050400d071031841c001e2190b00303818000c0c00440012886824610004200c81c200082c0203a880e21109a04914804d4004c0421400c4132a03080d40036503520030740700040e248040550152004005000c005030710390600c001d003d42502002d070041c0004c0c06001004021500c000d00c075010520540368441c590f1070b0a0741c29085100c04400d04131211511000038204d08042c0c0c005d0702d401d2207000c8403441000c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 330941501 1250 330940251 330940273
    0x807080a0810120f020f09090a030206010f26150a021201090b13150f060201021c0203100e06010203041d10090c02030406080c091005121f180f1508 65
    0x1492441c80d0141c0c4400031000c51070f500002d01c0c007100d1095890b00050212020000c0b07a40010107000089590016641000060104041d0104800d5000d0718091111200142c20500b04014222207846000d01a40c3e141d50103017a450030501040c19a40c000c0c8111400a1500b40b00c2240a98890300d01011004501400014520680c0c441c80c28181001400d1f544c8820980c0322107030260614640300c03020501403603000141c40340e04101300c40090005030005178903813410046500c5609e108072440c3c040c0c03030300400410030f51a14a16400d01510b04d250b0f40c4802c192a1a40102c0c036502540c0c00c01494401009820f500240c00c2c51041c500c52901c0e20509a0880e0b200d80d00c1d902641d091821401c00b50380244800d008040c0603040302d583c0701e14420826800e140003540016550780130310000001181001402141c0e1746020326501307900c45c84a02031081d00b62954016039104140620401100d1000f48440c2d94520301e06070000c29120b40b44244c10711480d0410200c10030001070500c25403c081c030400d0f0300c1072 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 330942751 1250 330941501 330941521
    0x60607050d110c010c0b01030b06040e190605130302030301050607080408031812162601020307030207170c06190e0f06011401090b040909030c0c08060105090609090d0e030a0807080a08 81
    0x181c568020b07490341030360f448d641d0390000c07004000e04856401603e40d182c50b03031415400c00c046031090300f015900d43c41115403420480b003201c00241c913104030680c1d5a03044101107600042161704450003942d43c169a507402d0f08201c3d00350b00860300450b150303010004a0791051114044034084920080303810249200041e6041c82d40c820f0001c84203d00b15520f08010040100c000141c004890711104083e0f0000d1100c904d0a4220f030b10450301d41e40032a501165080511803500e0541040e83c82c3c2e560b5861805400f4202e40340d0f41d0400804c00d900b00d03441d50918040c1c02420380c01c20162403282c00200d40340c0000307800c003d544403032090045000c000c206e225111815032041b9940000c4500e01038140340307493305042040c000380c90710315415010b00006c4d10301800007403000f10b000e4000308041c501030503c5505100401011141c013408461181d2140011b0190a480c0440e143d401c25103076082c030929081844000c40d0401e0711400b400781c483d01010581c00305002603100146081d0110b6900c48aa660300c001400d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 330944001 1250 330942751 330942767
    0x509060601120b04020c0102070605100b2b09020904051f150302042d05040506011a0a2a0b01090507050705070e10050603070e0906060a0c0b060607050d110c01 70
    0x560005145100c04844040e0552082e102014094405446e0024501c69942640c1c040c1004541f120355900c1041568028000e20501811818104901d0840c0d80e0070101d00008401c1d600c0c0c8100c42c408681002c02c0c00b501c2d0710503101c003903020300b0100c550714050400c281c035000300c10f041112140c2807a20b10f455040c4c0034468200c000c80c0c4d641035a00f006055400b8840281991420303600641d041444040708005a1014401c07111409800481c0300c2c03800d450120b00302101070340318030844010001d010401041c110141c3e2140040303850322040c182405560181c0308104c0100184031103001981c1c1c501880302e64640d49050301c000c80020300564942c044121054854020043e100380c10100003884000032070f1001d1074204e4091010070318481e44038000503031154819201c941c04142000741ca01e49904102a0055220004540107814050380d4403029002441e14440100014000c40000340c06175250380030754000300d030460b00302e9120151000010300410240d4401500500c00c000d4506581e6101e030b800 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 330945251 1250 330944001 330944011
    0x815271005151b01060816080309010e0d0f06050901140906090d0807030b150301030204050a14060409031701092301060512062d0f0301110906090d06060b040504050906 74
    0x140002a20501d21400c0c2d441e0050102456a15094100c0681001090007040080d243c0000944000724040c075690380c0741e0307a09621030310417078206000c0880d20382c0e004503850100e12025107c0c00c0c080d4601f481c0495181481c141d000344001e140038180309601c501588400d500d22000103190707281d9250550300c2540c07030404542d031030110703030111194840b035034825407155070801c0503810049101c40782c18000a4080380a00d46400c0d6140000c0010402c0d0720302801100d421004100b030801140202101807405600010606401240c90ba601a010140305001071208203028040b14017080d40c4075900c2c007010740306109034240d0740301926640ca203d4880301803101e81202c1190b03c0e48ad00d450a40311903503459502c0205816408182085860300020501c2d068440c0400c0340c981110081c0200303004c00505050310142513010b60b140503440148002c4c5081114162841214131075210200c0c000003948990201800510326404c01030001000c0044901403c1559403c680600c5030381d4510840507642c00301240c0c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 330946501 1250 330945251 330945259
    0xf0a0503090f0312040803180103052e1802040f15080a05071103120117010b010e090a0e24070c2402130b1801020705100815271005 58
    0x108407810310b0a009042c28105002e81515000200b000070401c0c2c640040e0710082894000040750a1625039402205090304001d007403c00071030824111545801903080d40c0c0351034021040f170241ca0022488215075004203003240c6040010300c1c1e1281d521021b90001d1160034244002c0c03000c04a205032840c81c84000d000b10f039a5600a1540e40d0780e009a02500c4003504000a00400b2403000e0001c110030b000401c42d926002a102030706514041d00316840d10054403044082e81d14101301542980c0e445403809040c0203003111442500d4441b0b0340518000e081c1c0350a201c07414441c007108614007840302880e0a48001e10900b511182c1e5641040540b2550310f2a64010300c050700b10a0780642048411000c2c5642c21482003005040160384503c0900d030020350703000b07803514481c08122003080c2c400e07000c040d1010101c01c2c07011306401c030300e0304021584410030f00781c00700d06001d50000080c520801c08000078810100003045010240707040b1928031090604210102d41111061000a000c00002d902d543c2c1103440141c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 330947751 1250 330946501 330946507
    0x7080705040c0c2a030b1e1b1209010e031207030b0a180c0201090b090c0901151b06090215031905100b0c0708010c0e030d0f050901050f070b0c03090f0a0503 69
    0x1200e81035071a4841e604554000340000b00400446c00c095112845100308032111541c581d01c81e2207080301820002c0c80d406040303036070070800390aa0160200780d4040c0d10145c003030750080340c40302c410117405069944aa80e24610002c01d091500c03250503074826014803100c1d28100401c00020003480440d12840c010602009091200202401d100b5480b07100c10070940e100024130100a80ea5402c8031140503503042009038421034019529140c030028407070044c0050883c605480700c80d0003016140140b0000c6ca0003200d040940200140941c9410943c0d425500500100e0300c017130144201d4103d500140c1c0c09401112025001d503204e2103452080c1c80c0907400c2102c6c121550761405040b042d282d485803000a81c0c900848500054080f000d01400c01501702035115a440310180c01c09051030000c02500711001c11200d007082c1030344650407038200c8910200030300e492507540103a22040c405522986600a0a0000c85410000c0060100b00514050540842136a550343e04072502980c3e207000d07803040902160010 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 330949001 1250 330947751 330947783
    0x3060a05060a181509061704020918010603080301060806030a050601090c350f010e0114040207141b0f03070e06040b0d030201090201120606050a030c05090307080705040c0c 76
    0x801e02520240200d40b920640d4800e502100818080566000800040e005462403088030741258194002c2c109615080300c0c4100b6601c1d203442e102c400640040c0c002e20803080802c40c502107104543c80c2d81902c1500070311405079246000100355009100b880001950300c0003141c11480c010540400346074108008190b079900b8145084020140441e40000b44020700e1480008042c50300401914003400d4034401c0c9032100072030601131001d000140f660250011840c018405900c40751a4141510819819540c00c500040c0218009100f11030020b090311a41100302a00d0b45c1000582118003998034100107010209107045c06900a54084202e61603081494140f1100c0e10403000300d0b0b8080401040803580c0c1c5c0d0300401081808072004002d40060f5100c5100809658120355074141070161001c007044910318040c4010f00030b008109088080580b01e03900900240e00c2103007500c3d00c044004059400b404d80d91480591303078110601c034544c010b504040a02603110301440c4600d001c40d4000301120030444076 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 330950251 1250 330949001 330949009
    0x100504060323310305030108060a200309120c0d0f0206090c04020c07091e060f1511010605031c080a02030903041e1208030604050604110906071e0b0103030908010203060a05 76
    0xc0071110b05040e036840420010b00c0001a07083d010300e14000c2e00d80b10307525410031015034140320340101864003081c20070421541c48103590a02282941c1c20214040e100e4541ca4550743c00e00181062001c0c041e2400300d01c600c0d004c05c004c030f600072a87c00c02d80c071260380c0c08800450603a11003104460701101c607007020201585038241500180169410081592003042d141c0b0b622504480010622071001c0e0f4030307116962004525441244003030700d100c10824444918140350000c503d401284200204252a10150b51586003500304e08050300e00102940c99070000030792610390050340100c0c07000000b45002c001c1036595419100700c07401900210091480c2030b04040d6080c1c001d07103848180840000d44c11710001560200b10103070303100c81d500c02c0180c5176603410882c2c10482a83c1020301264070a030702e0108a860412034180c11150f480401b40d079401c1c0c642000e81406803402e49000501c01010051803107050070440c000c15a203043e00d05c01d13200c90400a07140c0508034200d00044480c1600024000014811458 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 330951501 1250 330950251 330950281
    0x3130309150e01090801090b07050901120c0f02010c050412020d0c0915090c0f17060d02040513060e0a0b06010c060f020a020d0e060a080604150302100504060323 71
    0x40682080d4104650319201c1100070400212000d00184200c44000c1c40c40da48144440010301c2104000c3c4010807203612043c01d510b10140018090000015071241c00fa40a20041d9203410380c3c01504100303003440c5e010058540710b5005100700040d441c0c11003040966018005480965000300d21400d000c40d10341c0d0a009200313031002c0c800c1d603000442c4480010003140074050300c2e91500007803c24241003403804902c0300c2900c00b4403100340103000356031a54442700b40d40300410701e80502c2e42c90000da42580365078010546500b808031029420a06000402170704889110b0010080744c4601001c0000a04803810a52200140100107154034115000b041203503119440700398008c0c3c0192000623660f803030813180c5002c03a8420034084d800b40e040070704101d1301c01da0001d902c1c4211070015541d2031328140240d080200304801c010007880c42160703a07400311940d0b02040241c1d04059580685000d0f03105c00d0078400034220f80c100c0c1c401e680c006401c2007080403d01121200f49103103003107464028955500d0b04c000b13080b03682d0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 330952751 1250 330951501 330951503
    0x902070201050f0c1c03020c0d0807030b0a06080613050601050a050702010504240f020102030108071e09060b04030507050f010c02010806010c0b1e010b03041109090c130c02010b010809030313 84
    0x2c0180304108451a000c002810410400402040c180c1402c3c0349580c100c00c50300c01d15200349032041c4140d9139254004a420144a01c00d07180403900d0341d8604006030020424040c105404c55044100854020f810590090080350112031600c000c10456204c1000d4a40407994907002400c207021401140c4c0c011005000124414104181030984401403500800c2141c0212140e504851190544c0740c0c1d000800c0c0344460002d0700c0250708c0c40d0306024049568004a2155210b03151341401d103500c400032043c40720070150201c00b0b014481e166503418000d0254115000540310790158030300000380c0d880c05d84c00000e050f14040e1500c030a6014142c005540810000f41001d042c05140041c20000685100394113101e4064070901490245443d101e90814480580154010001c1082400046441c0d111403a4020004030f0f1010040c3e034070300080900744161042d04a800445070000000214880d03005588207401b194000c0003098103c9004441e20141901d280c005a0020000b160000200120000c151 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 330954001 1250 330952751 330952757
    0x20421170f0d090b010e070806010806131e2c0a0206032505031602010e07151403040507050f06090a03060c020102040803030f09121e130b070302100c0302070b010902070201 76
    0xc144610481026103002107000c0741c0852204005210300311b00c071015150070580c5490034084a152180c0003a14401c2d000c0e040d5441803c1603021500e000c0c54940090320704030b140101c103403004115104088040c002170280c40e03410400c0b0041c05070b0005100005981000c80714001070580c0601e94090102070360002c0e1103107200319000f1081d143c80c25130001c215545d90384180d90f0b00340e4034903040c10002d0014009140030811641070004821082400040300c0302641e00040b1500066042142c0640304441140c1c480310121001008100900c4004034958040710400d0b07901d0325407005080c00f0051a0b105103c400c0c4d9002d4440582840802d0a5034880c00440741e1030300006240c941c40d041c0751407440d081245c0e204484c50b050310402c651004c051080860781c0c0b580104d84d50800901c3d4219481214001801000c801008583c044405141d07045100007410080c407100d5540013039040c000e44070000308a0b20b1000c14240413551810902c24030848032000d4014a020a4603401d00c01240041c0d400a030003a410 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 330955251 1250 330954001 330954007
    0x150d0f060b07050a020103060f0b1e0705060106022a030a030f090f1205100207080d270b1f06020c040e010213170c04050f010306050601021c03020421170f 68
    0xc80c8208000400c0d100b4003980080444145178070005007a940b072a0000020149038402c1040000c2200b025900c05078030240c801403c0c0c107002001e0800d18060110050b011384100300c000a003294001c00d0282440742e13540d81d05506240ca0700080c6c86070350002d884e15500b580c005040440400d200d0810030041403418944009040d0340c40f02a4886001c45821044200d00441c5060041000c10400e560646664400540c180001030303c600c0310b0380c0114606039031160740750300307a03501c0059408885c030100c03010300403800c40c20f000d55040082c850041203c20300102d0b0280d80c401150308456030301d458100c810310341c010321019503180103000c050440c101214550b0364081c060360055841111040001e003000b4180c09401100003982c441c40c0c9100c12441c0ca004d2803405040c40720000d4180486170542c0d810003000f00307098494000403440c160071580040031143c4800c44480c980e03640b50300180100c402d100b000440d902104140d4203020700040d84000d080101c2c0c1e081d10112040004080d10852a00c5802142 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 330956501 1250 330955251 330955259
    0x507030506070509031005010509011a0405360402060318030f040602030a080a02030103151d0a08031e0906041707050f0a0b010909020919091b06020705150d0f06 71
    0x45801c0064642c072010483c04500d01c401c1d41400c106441d24a0a0381100b80305a5142c000800d12403036060050904041d0300340340304280c094103131044074024031003d8200381c0c0c40e140041c1d145445452501103180640100e0341d80800e51040c41c60040c4c020354005055910b1502c0e940b844000c82c40002280150a000a02581c4d041a1428001c0c000404080c2c0143d540c84e0b41c9088000c00030200205040d04c114070500040c00400c0350100d0540a2500407600050118141000c9001e584921001042e0621980529008105252014601a422900754180643c0c007030142c42d01056800c0303031004d0083e444080003c011031440610700c00344d9170310781035403510305002d41d180d207410014900035010240c2d00610f5544100310700100c0041c010400100200010b8000c1ea0005011060290003c8101810700070841215130103540726048030340e486980c090002c5841c3c0164071406440340300e42c0c005401503070400915801c16101108203544a440e441d460580d0100604004bc0300b890a143c0080d60344040200d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 330957751 1250 330956501 330956503
    0x1513030b09060f0a020a2706030e0304060909090309080a060b0f0103091e020f0604121b0503100b22090209010905070206070f050f03010905060901090c0e01080c1e190201060302010e0d05070305 85
    0x3c40c1d0203002d47c02c4c1103200741014006002d884078050510156070041008011440e40040d07805e0542d00350786404240b05800e81000c4800c08210307001030101d40111101401041115400301a00c0a0142c4060807001c2d1444010340407540da40708081d000d01100c8c4454808541c10810700000203100409001c8420038903030100d01c075034215820104521941070341440c00c0c058103000c052000f0f0b4019185440d0300e03040c540440d032140d819541ca203151649501480300c3c0341d60782801e2054000450009404208903c84113100601407440007603014008490000c1846006800703a64481c1c14150002d000c0761300c1310707a02102c0302901021400101b120900034207856051460046000340519400820a810000c0c1080480041a4003d041c200c1c034120b42c0701714103500200102e0246000342803000d660b94400100141512459200344040c513600300703500c2c40880d8800080c3c501856001c0c1e858280d0075444606a00b01c980d64000a4049003601850442d2490701d900d01c904464865001c3d50b181075625983c503 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 330959001 1250 330957751 330957797
    0xc0c1e05040608150604110c0a060b0a0f0b0d1409010c0809010b060f0c0a051e1e0d0f02070305010f0e0d09050a1403190b15190e04021513030b09060f0a020a 69
    0x423450740d00320700b81d0038050000d5401020003280d0201c8410014900e00503c0f00d505042c244103c007452800410320f1b165031042c2e68002d100580e0b0b8901004220710307050502c54001c08020130240d002c100070070042a50726a0501c075113814200090702030703854040001100d511075000007141d04401d00c6400034a1b00000c10038442e074a182c03a10268002c0d8001000300750107003460016400b06101d02c915100c12000301100041c0003001008904005180c1e0010b40030403410314074241c00190a945c02d0a00c441040c42007684a0400f5110030300c00c0e61003400c045a4229940f0350244900e59024800c4d8005101c040d80c101c82185001c00001c0854800c10150640c62880121044050303d40b1188803040040d80300715050841d1a000c0704480c0605440c0380c2c10740d0005002d01c0c40c081c0003440b0008030b00080071511000025000700540303402a13912644a0700c1381d128112030a000c00c0310400024004114400300014400d402010179440745a203503619004100300135046650f240041001e501ca10a4001c02c604071a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 330960251 1250 330959001 330959017
    0x20f04120317090c15091903140105070206040f06050a02071b05010306051002151e010803090102010b01050405031009020f270601020613120c0c1e0504060815060411 73
    0x454111901c1803041214009000f41081c055030403d620b1507005aa50160084854005029180e01d542c60071010030009400040750810224040401005002d401051610080701400080c4210358401104984520081d00c0003810b0011030b0280310000b81813900a0359201074010b1005042c044c1940711b00c002c0b454004110300e9007026a400520055a141c05070130003411068548222510070140700a6541c0052020107211602c44008902d140c401e61141c005605000b0310318a240303585921005840f644038000c114095840c01c2a220019401003060b03078211038004001d4a03d84840300003840250400e4003089a1121400d2100703512561442e50b845c803040e480829851485a0f5072040c210314407009482d042c1554008010062840362001e1407140032603101c1c8a41c42080348451058540768444400102182c01c0c15001041c400602003d007265120104900d080c0c1d19620824401290414010700351260450050b468400d0500b81050703420041c003500001e0304040a4801c4035035a000990 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 330961501 1250 330960251 330960257
    0xc1514010b090406080304050d061802180109050603070b0304110a08010e0307021c0c270204091b03091515030506010b090a1703030f041412031e0c030a020f041203 72
    0x4030200541494031901c0003821004004502d09410b200000c9c1160664003002000c103a140e1500340124440c40c01c4c0c1100d89540613125411500c0c0a4182181503a024010801d000346400001a104c2c44c00045c001d04541c686203070286103407541d442d1110b81e1b008448402b03410103802e44000450103001d01c14110008180d101854603410140304100d07401c000d06180988a092600410020440104210040759003d0307117110481300c0b4100c814070f81c48280301c115500443c80440d0004410f0303200e07080484071448003802da40d0b0002c058242a011200c4031000039010001042a9200b5050f031944000c1c400205043d012850b5030390f0303540c2c5918148090b00b10812801d0003207486049810403a11038009040310320120510480001d140942e00c0c0801442000781c07660f010042418441c11440c10441410724105a5103550400d551500035230380141c440640201d44200010007400000340210300070804c40b401d940c03458489804407c0030b50008404040d01c800708110000d075038140c4001000c078061180d2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 330962751 1250 330961501 330961507
    0x7240e06090d140f0a0305062815050304150b06090909030406092c040303060320030c0d0201020a0b100b1b010b0105070201121e020a030509010c020d0c1514010b 71
    0xc800070303c50001001100490802409002040048001502e0030307000da80c5000212076881400044c02c148040070310295500301d062810341c0210350500c05206503101348401e00d0000640903412030b520310040714094110340d80780001044407941604480e0b810880100020705081ca4600001d400c05000d03144102c2c1c0c5c0c0c1c00020100503044e00b0901403001000c440c820301223005030082558980c0d07035515a052040041c0d4000240c1010301a920050140d43c10403122501061044e650b22000801814031621a21a525034410b81d07140c811888030101c1c2d070613070280c00c11030016601c4c03a504c2c04000c6d000a045884081000c03856481103805415a000c00f501c0401224029082e558211290b0800c4241003250820512000d41d800403ca00d007007400b801b100240711a040303801244140c40b1481c51924035800080d50103242903040d0040fa00800b1307858001c1140640c0824140d9680500304035500100f41c900c48031001269407070b2007001c2052054280407a0070718401a00b144044800d8011000210000c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 330964001 1250 330962751 330962773
    0x14150405062808040c0e0912070803060103110f070803040f05190b0a02040b0f03190e0d031d060c0313060903080f16020309060a0320030f0a0207240e0609 68
    0x1503122070b240e41d54140580ca43c102074540704405c007003902500303120a031030002050013001d0403c1400d500325181c81a01707846410340d01e000c20321a0300682c4c80c140040e08217400d5804111488044840300480b031a4190b1a02c0311030354405045410060050360009960094107001c55420300441000140c203800c1080441228581102c481101030050305040344140801c0c030400c01c46800322000d81250740c004030348994500e0060075984509049011019042480b10200d4280c00120404c2c00c1c5c00399181400054100002802d40348a81d141781251540b2400104e00c503614620b00070b5800c0710142c2d458000500c55621040140d442000040300003030741c01c10800400030f0303503110700c16000546000410b555084400c4d00a640340540c52500b442080f0010303500d0549402584481c415480542c1e440b0341c880071448000354240c0044804140c0b00c415140020a200c000d48212a00141e00c052103038040d0705041c500c451100c421215244543d541c0c0c420f03000c0541300800400344114072110007840b8a45803 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 330965251 1250 330964001 330964057
    0x9030207050a031a13020a090b0f0307060f020106140604030605040804080a03080a0e0a0b04080f1b060402040c021c030216061a0f0409080301090c090b070c0e010f1415040506 77
    0x1e101c5c41e00248a40d481400596440303003106c048804016002c00c07007081c180c000a00402e461500207505100c1c03070f0000244c19030414003004030034140d030300200030f15950b5080345810840045002a4888010041800003400b25407040e81c01c18018149941003e8942800600d0035800c0c64050380400c00800801051040d0f41c011001138118910240c150112195111800d244010300028801c90000c04c04800c4919404240c40c1e91803607144d00aa805051414801d0301c0784820b4405078010b0b414507440d200d415000060064000d0b0740003181090484258104800940042000020414449422a011620a00035030b002901062170034120170a07803004020300700e203507800014041c134200321950010070020341c1504d045600e20400821890f081c8401210340e030f000c030b0b0000c101104001c10700c2418400c140224400359140300700742c2009640c0310f00c01034080007524031031420391015420b203045040c1841c0d0000d98588081101c1642020307150000101e17180c000d20184c26202405000080d14224 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 330966501 1250 330965251 330965303
    0x1e010e1204090c09080c010c02012601140603100e1b2b0e070504020919031208011d011e15170109020c06070804051903050304050d030506031009030207050a03 70
    0x2181c00c01c41301d860b1900c403203c5c3c2c50f040358111035070501c280c2040d01019a40150150001c02c83c1001251745903c124070056202c135002070059120b450304102407109c0da801c00030200e901824486515190051030111000201c0c0d10043c9091840d00e4110400f030341c0c000f20200a0200b4442c400c002001000f200941000d010313000c07060850241b810204000c102d01004940f041c01e40d4030a881c0035960b43e4031040400d002c103460407004a9450210a0008240403081000c0c544400050b0303a050321a0341d0701c0008040e00c6240140c81040000c000b80100300503d00d0f4041800c40484a81c1071503200b580e5142c9904200704000581c0d00481e40c9880009007421082007514058041d01d1011401c0c0340c55168480e80c0d48030300512100a120340500030500b800740802469010ac108800116034040f0180343c010400d8000b500c00702c030a840f0358003010385503074041d000b085e20815000c2c004000c06031800b143d09019042100d0300f60254040d12001181c03a071103400e0b0f2903001c0c502404007055510000510701172a06 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 330967751 1250 330966501 330966521
    0x403110f0d030503070c0305070f061b0504150c0501090605010e07090806010b03070e0a030c031a07020d0206040b100e0108011a01140f030c210106031802031e010e120409 75
    0x222541e111040003e4000c010340e80c01044a10b440741511001d460709442e41e108400020f098810200700410030452941c1200c6042001030300d81602d140070b40c440641c0d1700d00550240703012100b2a00c00c3c92041d80e101d00c1e40400440d0103100049040310450f02d031032040360300070780164500400e110204460035810400010003444802c005002c0741d80341c608001c0183c0006048801041240184a0f286503902e60340031003e0350b0060fa110001a90360b2404040074900103142289481d92000002d44841c00420f0340c2d9044480e5802511450340d0700d50701c0c0300c80d02000808451310144103940214540f05084207490182c0080e4000040c0b0395402507a0008182c0508944c50400000d140f442e0031a030311440549034000ca504d800e464070313074440401032615401075448840281009005200301840c5144045040b11010344042081400c00b142c0d060900403a2000070b5090b90cc0080740b2449500480b6480f12030020b05000000c4500ca1035211a050417840001401c0722003011400f80803141b100d100d00d044413 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 330969001 1250 330967751 330967759
    0xc02030c030a03021b150307020d03051008061503100e03070605090309130b011e05070233030411120d140a090308030a090b090102070c090b03062a0403110f 69
    0x40c0c03a03960000d58a990030743c0052034001007140064600c1d210301030240040c880c6e400200c0d850b4600010000c1d40c43c45124a580300082c2014003003019103880c00d044a042d5000403001e401d5560b107600d041c509100c511f4085a400d88a500800061105248170302c032030100c00d10000c0d683e0754070a418030805481e0060305040d480d410820103043c07140d030389480041c0070031031135030b008034440003680f0040e00c850905241e20600c104000c00c000700071541c000f0003098803d200f00c4481610265100b00142c0c005038082e07000200a100320648080112040080d5510070701c10b00200f100d90030104c000c154840000c02c00c004a0340e001c1410012840d4019810303540e440d00100f4228103101c0c146000525100c1c80d40300c003a202d09400008100741c641d041d0005401703144c2000288140342800000d4034002e52002074142c2e4041050301010901148500070f2100e000030003001025603840b1000b40994080c03000d1200451080150344007001c1e2944071010304010f5006204070720340c0b004003100f0310041b01a040030a52007 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 330970251 1250 330969001 330969013
    0x2031b130209090429100914060105040501140d02040e040c08010509100c121a030d050909160908010f020406090b0307080403200307051b0915040b01120c0c02030c03 73
    0x1525500780c51a401030300a11120445d400344401c00380e0b42012402c00b003001c01203400c200b000440181221308100c0c1c000c06400c201c020051412041054025551940010400c100400c0a988586104c4492541e81400c1524140080c02c81e0812a800f5078018049441c0800401c000d1040c007501030340c002c101d85030080c0420b1900700c02d03058483d41c004014041195aa0758000340080c0718802c2c440f000e07100003104005000100304090440744245940c18440e10848810345a540d20079026500b6092002d27062400d6038a07500c01c0000854000c051748810040f007000d0001e03540350240a4050810007001c1c00503a43c1d401c00f08000c00c001403503001080c0c2c0700c004005100145e80d00018156000303070149003400ca600d01a910740d00200882c1c0505100c80e00c8007048602c103000002c100c1d07840d020300745c82c9030b41000f200c0b0405110034144225599607211001066950060405030003160810304149440c1d14802c0312400d001c41121800b41c4000b0004811096900850408200303441110314100c0003458 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 330971501 1250 330970251 330970267
    0x15011401200307080a0309061802090108070e22020d0b09060a05070507030f0324090e070501021c020a0c0e060907030506060711182e050f100c02031b1302 68
    0xb80e28482e07904000c14880c00090381189107071203a4855400c065101d00184500c03640c0b404c2000e03000b01e0450003a4400c010441c0001075076500000c201084800341c2148100c1360b40e4030a034404846a40359640f080912900b1030302c0c0d0042e51420a980d4001e80314017085503660a10300d01161800308001c00b10000e161409081c1b101c07103a040429520710b07076070501d46a600380720303810707412000351a1102944c150091403007492440e1001502949003a40d405140811109094504841d951b08140c0b240f240543c0045c01281c607062151055040c1509090040300c0340d80d91282e550040392400b0754080322007c02004180040d030701e000c4030100d070081040d10f0240701504042c00000d001d88100800200580490041e503412510b90040311103010781540c102480601d410032070300b48400d01c501175261401009030385410608800c40040020380c0c5000d0824204070f03010000740038800c0c0c29800800e050140c041007403001680c1c1042030310460030a45000401450310002400801e071108024111b82c01c1c0144810070b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 330972751 1250 330971501 330971503
    0x1091a010e12070801021908060a050609060a0207050d0f03020f06060a210f0c0509090a0305070303050a200d14010e0601030902120105040609120215181501140120 72
    0x44405411038018542c000311081d01440c106030780d84241c2595001003440360380070031401540660300c24130b0f407034281d0b0395680c44040125109441c060640e101c8814800344202e410200040c01c88200180101c900003a21980007a41c458000c0c5001c0391200245564402050390501c181c3c1c51121103074006060340e050550020314564968004da038442821f1194108400101d00d8004038202e030411040d001400c1103052540e48080b0324024103004011070004140c60140000320241a1130309035542034285035081c0e070b04030081e00014100460f11a15110f0f98201c1c0e8851c1000a02100030318180643c0e038400090040341600c00201400d26203500c90001086884101c03201154410002d2130002002881072002030010021807a0303019030f641c40c0c8000c0208001d001d5101da18098004ea07449614040403e1041340d0b81e1200039000480c00000c180440c039614546030516a1010040003926205510300d00c0041002c04240d2141030003c5451310540c49558100040c000c1c4e1135116100e80311000b0044a441d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 330974001 1250 330972751 330972767
    0x604030f0336060212011508450610080a020a030f05011e0204030308010e041a04030e060a020606040b040e06010b07030302040b040305100e010209010207030305070807050303070801091a01 83
    0x100951440802e1807a0651112416010001d0740401c0c11516245021506455450240660150100d001400c0c0380101e005138140d0f4402d001d000c0000c80c1803c020520984407450480070241c40462100c180d0b03d401804071100171000c43c10800406151503c0305070340180c0d010350390003000541c100182000142c2c590074842d00582c2c1d00302e40780080d1010130340f40c450b005203600624140001d44424080c9118582e9800801c101c070b01994920002d41d0b03d03202070a0b1a104182c400507c1e070940c0242a81c0100444d80585912038000e060401d004214000410300c3c50f44210318031001600000100300603817a10340700306085108207407020030800080d04000c80c0c0c2c3d89010f005000e404640031070b4007000c0610980442c3c001c0c210180381162210783c5d0b441c00399980d01200c000100c800c6e08080c106d002d0600c0510998440100503801032002e5491070704d041e252640090030560711008200038280c040340042004500a2004c1c0e522080c0c7e640c9814010f02c100c40042800900302115110311030580d80e400505 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 330975251 1250 330974001 330974051
    0xe0307060c0f231902030705071a0301031101020a060f060302090112050304030b090c19090b0d02030705040b060d060303080f090706050a1b0204061401030605042a110f0604030f03 79
    0x5054100700c05001c283e1894000e0800c2054062000024104984e40c04805030200c2840386c801c4400341c5446205007501074230380c1b80780d0043e030000030300c0100301103401c028600d054040180180c0d80d2004064545005136901d03001c07026205a1034078070420441c1420411140140803c0e4804c1c400c0404595803151244500d11005d000c0701c051300089081c0ba8070078000c0140c400802402d95480345503241110000800510800c0e00b8281781188501060a00f21528003e059000340901505400c0400700002402c0d10398905401c4002030100000060491103810081d50103a00e48038400d140007000211241c00040c4510700d1500301d00d0b0300300046070300507003941e070110040d0905683d2102c0300d018070094580c2404000c1d52190801030001210b003516a54001c00760003e98052141a88840901003542e0b18210a0050344005009050440080081d0000d445115150100c03050401c3c2c8202d41c5821401d0380c140c002a00301005001c1010b4122650045030340e540e080510031208c58046807a591181008 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 330976501 1250 330975251 330975287
    0xc0a0c080705042307020f06010e180a03170907090216020901120f02090411060a0e030c0a03020121020906071a0a0501060c03180b0a020c0a1a07030c0203070302040e0307060c0f 78
    0x8110818000d1047d22254041c100494256680d521091200020103640307020101143c001490075421012814000c2030380c05480d10200e0f00c044480c08114040001d000c501503000311180070031809000e0008040401145006c6182440319004010b400380b010790000032049401e00102c40041d900129942c02c00e40c04581d01c240300c0d52345041580002c8804112654800c10000d58115400e42001d400e5400440076003c503042070000c403041c03000000c00f6000180c0441c00c014000c00c00a10144905420b60406890240c103140e02280400c5c86a01302032401c48112003a10303144030f034070340c10445207a51045481c0002d02465150144c041c209600401c40a01040a10420003480b0400c08140d20020046070500c107949402030100251141070820010303102e031701c10362000502a82c6031054a0602d50312940083d25114150b60140e80700c102c1c6c07084c126014001e81c13200202503a6a8450340440d442504051a51121180f0304481103d05014110f400d00c5204074040c04001c0e407000b810612100007039 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 330977751 1250 330976501 330976571
    0xf0f0303190902010e040c0201050901060509063001060f090f090b0a0b010e0603090705011b08040b0a0e06030c0d0f050c181206180f0303061c02060c0a0c08070504 72
    0x400121440000d05c0c501da0f421030301700042c401d200f950540c4003600c20740c103001c02041041e403a801001004ea0041d983c89910204519403440d190042805070761500b031441c8000044071241c10041804d4880c030354009902e2524115040100d560341c0d0040b161a0b141034201048600740706d40e80c19200110150640c542ca90b500c19040100745d0003888240341c4000002c03c2e80b03841b03240421039a03588150500031280015440391350b45801402c0305000d40f2240b42e001c450745080900b40030041c8040c0d0080c000300400c00402034104545511110000c60003826490300c916960740b181e22440f1300b0f88401840d070010480c0740c0810014818481700a4402d5007091045441c0350611002c00114035480d51812140e180c0640c6091025011340034136458940d03000c210a03540460382011440380c03a400100d600301c2d00000c1c142d40018020701071042c61415203100404040c10900740030303182861f081d03140304100c48040151a0032310091008100a1004120031201404030007285001840c0c119409502080c0d80c3c8a00d07 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 330979001 1250 330977751 330977753
    0x31406040f0b1e01170d02010b0a05091015080106030b0111060f0604090503040902033921070804150612110a05030307060506010914030303040b040c090e0f0f03031909 74
    0x8010311030b00311500e11403c2c12503561505150309140301c03046242c06072840b030714166000c15801801400b0501c8001014000e02500c0e20040c890700301c0b00200146c02180510102180c078500074418256400301c03941c1c41503000d40c1440d0b0090122240c5029060612071078407440032503650001201c80e0300201d00c8241c0b040c00d0304c4440110b4058140701000030440c1c0800720780880d210101d030780a5031054180c1c0c03003010140c13a60021800b03940000e211001c0c01459410200f0085091403400929070000182013900341c2d03140c10814070021038802c0e50306600246040092000b8400845000301a40c01e00704010858140b401b00000c000c1814824000c0c10482070841c070000d607a035102034081c01810043c040d02d80d100668501071006210031912240407440160001c24809142102d03c580c4440140045141d81c80c0c5884030741603030030b0003807080314128003042c0301150742d00c8a4040c01110640301001170801100d000708460030180c07000e0546019034414002c02080c44101c1401039185401084001181445 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 330980251 1250 330979001 330979021
    0x5061803030f2b020c061b1308010911010302190804020d02091e09011e020309010605030706050901110606102106140f0a05090a020d0b0a0906031406040f0b 69
    0x2038240038510480045803403091101d41c20100710841c3e003010303030b0401400e80e8000342d075080340a072808500301075020100003008991880040000c0d050740175082d50510352000304001c03540141d40c02464080e519031860340200042e0144101c00950f007401c2c00e50510081640c20000042908114001c020000000c64159165060b0861400d500a00101e61034a410801d0020203000303034a0f800204c040c28000251901010b201e800c1d5641c1841404181c0c180c12403074500c0107904040c08803a00e81d5660900028141d0781000385000a000c2500c41540f80ca070b41500240c0620700c20510300806410060410405550716006d023416041d0070300700b4600e003059a03155284c12400d41121100d40300d192820118142400c005585c0902034100c40b040c40300c80c0c1310350500640e0f141d5445041d41003040080400e0551590341c000e0800354a5402c00007076401d01100000d04e4034401075115103192a40c444051080c401070303500030348034010304038000d00c00b80c1816550f020101c6480034020f080002c1490204401d0701e8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 330981501 1250 330980251 330980257
    0x9030203010c18080a05060c03151305010501020c0303070507060f17070507060e0d0206190b03010515100f020d0f031103090106060306050a30050a1b0b040506180303 73
    0x6006002041510000080a0840e103409000040f03031825142000039141400101008065445005071855450715801126a40c0003d861194000140a8140c0c3c60b48c854000201c82065803ca0215080d45010000381c1001da030703c0c14103402608100901c1000c5500080c2c0441225014a0b2006688071030400440c0d041c01456108141000140300303228926030b205010f850b46034002c4100304803018804225a0b59000c0310f5041d41c0140e00300d04002211220507280c0320500840d01c035400309864060600103405c40720120346440d03803402d10301c42d021100e04252200c100070000764204403080079403140003e5501c0b130499481e80c04200c158414804124840d81000c501c0009208d660303034036420840c7c800c0c0e018080310300951000a10389200011149040ca09a00894001280208102903d82c09d4029082c00850b4001800781c854501200040d408000403801d2a024014002c50b5140084140d80d540b038082d4001c5440c2d160a000912040e80d03100b00325003401e8400000d00c0d00d4030140502084c1540 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 330982751 1250 330981501 330981503
    0x91f0806150412080c03250203060f04200f030706090e0603060c1c0b1804120315260a08040815040305030705030a1b050d0b0d0f08070303060906090c0f0804020906100903 75
    0x104244282e0401f1041080010354000d00c01c50584101e55a064021100301c801201c000d04113690904000016000d11900d1004400000d40400ea8800f07a81c40400d1500c8200d5101c2e50008149500402100e28618200c5400110880181100d4204070881c19190f02a156219074004030b070400c05524002d1580c401e030748500d0301400c4020283c0c1c007141c0714401d480b411603041c0c540420702d0b420319500501c284101c001d01300c0400c140e5044035003403003890f000c60b040e100050010083c0e45211824010000c001340c02c00b80b13208000281d901d6040c44011800c004101a907a060b00f502d82051100281c1c0041c00d41341e00c0009480c1c92074480c4da60300ca0090207000c4894000104c4040b020f00075032503503408401013045034518031040c480310581006102001410310000b4000d400c400245000091408005103203290007480c1c0800c5150f1151011012504280d12030000c803a500c200024407941c1001c6a5140514141411969413805030007141c0242c0340240094440c41d1106040301000e8096100c40c8051 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 330984001 1250 330982751 330982777
    0xa23030307030f1b0b0c180409020a121403191101020f0301060311120a0f06050d05060f0c0d15050a050d1505090304090905010905060c0a020a08091f0806150412080c03 74
    0x901b403030011502a035000741e241110590001c000318109081502550390850750141c000900305250240d942060342c02000d084810034040070740030450a608101814201c1603007500044181e100c10009410503c0751440400580d0044c4040c140c0a000c59090740d0440790141400f145100c120305141c1c4480c4030303c0480e400f05000603800d010303060810780c1c04181c0c4003545180401c0025251005c00040d040f18040051484d801040001c040340c1d15907511079042401008000d042410511651080e20602c4105144c00c420981c0100264600681182c00030402903c1095150480e5180c1c0a8204c085841c000038450b2154041800204c04204490081c80210400c009448152506c6800307000b10b007005807090704c101404206404800c00403074282031120380007084076000a0f0344c2c8840746d81141105075806106089048454105130105114000003a500d41c04c441c0b5212040141c82c40e007004000d001c540f01030105201c1c0c0140c1c02e5980d007500d90480c40e42c0351640940c40d1007900e588a808100765003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 330985251 1250 330984001 330984023
    0x714010c0b04121103072001020708060f06030d080613110c070308040807090516080a200703020d020304271518050f0402010e100903020a23030307030f1b 68
    0x90148810004040301c5681d540d5030b601d5022031108642e680940c03000900400c0d888021038a42e052100f071800c7d08584180117440c2202e66071054641005d008540030003c0140c2041003050920703051000c45282003060401d0999803e110b0085243e5840e203036202844140c0d00d426400001d5480404d641c80d01c20a441180d03803041e12403400c050f01e032f0401e00c242e0505100b4120f01244228450040da445404510f00313aa82004022200f2201c0e040c000c0d081081c200e503102e00da501d010544111081c0d81c0030410310b0039640d649440c68000d01d080682d0040c1350464000748420312864040d01060501440c20620422803130385100e41b605c00a20f002144542c00004100300000e4040741900c00310b01200d8040d408001c02e503a13015201c0c80c07903201201e009000824200750141e05181c0058130182c038204920380310b00c000e62240d0100c2d102e01c10b0340d0441101c2c01e405641810464503440c036000356032001940510b041078203c0e034001d49803884405054042c092146a40316075000800209440e0640016585003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 330986501 1250 330985251 330985253
    0x3030702010f06051e150c101b020d120c0207150207060f090509040209040f170c011505061e0d0204150f0305160e0409020d0b060901060c050714010c0b04 68
    0x20007045010b9240c1c02d46820014001418900b40301c0419055920b0000d00005c02e00c09010400042072101540c10072081c1400b1100c000340e001c015081007081800c4001444829895003001940150701c4003d0031544200001d19500d60721440171142c0c5444035002040d40c1c13600400036814140f40c0d8029025419154050303501c11a80080d4030b508850b100e0310f0f84907007030000305012140c1c4030b40e902070541c2104030304000c81e005040840e4400d0340306014040048a030401c642e00c101e82c0d60074a98001100e18000300354844121000e00c41d60f01540c2c1c5a44000d00600e1404011a81c00e01404103146500e0b84180a10400074821408503102c460003850115a100d448072020710031a010786021000103000c1c00050a2468040d1245900420142c0c007020200c1c0c0c4141c400301c812500365010190403e849081c0080180c95040034009168406c00d0414800d240280603ca8040c805034041e100b04172601808102140001c20300c101030314108040c8040040f807034070040c0e61080e00420001d11800b59001008 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 330987751 1250 330986501 330986503
    0xa0b16030f1211030f0f01081c0903150608010b0319060504020a05060f21071b03051c06080c0301050403090e0408071a19020405030d030b040e07030c03030201111e0904090503030702 80
    0x50710410269804144903100c4c0c6c0e07050104a6824011500c06c2d41c40311030810340c11910b400c041400c26000d4900400625201c0e078650818850318400c040c00075850b02014000c00d602800f8145141106400a11070031140f8400300c0000c03c03003600050f118175a074502003010740d11142984005007601500c03c980d5940c00c0c0c015000c1c02d50000414071001c070b044421200c1ca181921046c1c902840f001e1f51141c20390030401e101c2d40d1220180641c01c0381808030030002421003204a0301510701040380340c00c1c0010b0051602100f18288a80f03558694803a0340b4202c03c01c000a600060080c0039590149180c00e0281d60314a40780040c2e01c2500005080d500a07104500310080d1010340c51072007420285041484030381c0d800c459400b41c1c000c0b4055030b5819001486a0302c5480d00c00d0b40800c0c01ca00303000300045480030b01d0003001810b1032940d401c02d45600759200403d00c14960240a62030480c4841144a4940240582e15002100307850000302500c40d400110510350396240d8000700a82e580150030b680e40c03401c0075800a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 330989001 1250 330987751 330987757
    0x110906220e0415050f04080a030f11040609080703020a031202070b03131209061202250638060307110f0c0a0806010e07030207051612020a0b16030f1211 67
    0x849962035481107000803140b090140d140100b900c0d0148101d1610b5035580e070030307e0340c100c0700c800d504040c0c0c1d503e400070643c4598018001d1060780c400b034103a501c43c03c294000b40965031903001602d00ba84041c40410050711007807440021250880070400328801d00301c030101d00f0810160300981c43c4201c0401403080081c0c030319000894061050300b044041c580c0400c41500e0300700c110f2003990040f0340342c0c12050351620131940080051542d82c2c03c84018411000c90054856000341109585166480040310015007460340710314130254603010300212021540003807050023514281401e0007104040040391055000c0d44c6104040074055050795a4185c5d20450307e44d5489898019a04c142c014502c00103149001090b298140c0e8640c1e02c0d040459603544905602030b6000d5103007100c4501c00d048880c891546202d010802620b43d001502c02a20301a004102c003d0509400a1000c404200074643c1500240c0300c0200d10194181003001c48401008000e40d00e040a100c00c02c3c5070141000400441c10480d8001 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 330990251 1250 330989001 330989003
    0x90b060c100218010813021c020904050604030828110409020705060702010b121908090d0c180605010f0c0c0f140916092106020406030c12110906220e04 67
    0xc03c030401c2d5003000440e00c041c01070ba6800700c61750080da058400f40c2400500e03040000d05410b05200004001da002c251940343c1107606680e44c0d0002c005000405a100c500f90390031903038401445107490032034080b600405821000c0a41116030f900d440e613802e4020030081d0b500500c0005400c64440616003402c3e51a184200e400e80019480c040b208805450091428220101300d400100341508001d41da140d4120200c0c103007601c25000921944007180d613000200c0c0440c62040304409082840d00070081c1d03d424000d018400c215080100a00c0103036488200302d1005009842c2c6a0301710501401c000803151010780002d034555040342c0e00402c56448144039540324480c2a600107402e40d40e410b0864010015242c0f40000044624504006c1050110104464000b9880c1030401d00902946c617401240e10950000300444d407182031541082c0d41240400e16005c45500e0140101c0c40518040019881042802880b400c00442c9203c85004182c010320080d0a5114920281c1c40d1910065124608101c2d0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 330991501 1250 330990251 330990277
    0xc030b15070c050406210c08011d2b0f0903080a0e01020705060304050a02100201180f02090a05160324060201090b1501050a0507080921070e060a090b060c1002 70
    0x580040c030781c10306208180484a40c1301507441440f0000781d80010b400548442541d050b00c5c2e010010492020a2049c05004506201d42c24181d441c1c3e440d559050103500300307804c01001c410418a8800c003404c910bd9800d4080b580ca441c07840320384003002c1030360201c4264001a100050200ea1810b907190071640d03900311780c0302c00d0b02118005551482000a988011103000f4465007118541d43c2c01820301200030001c210302800041441140040d4800c0b010481030015160b14184070714040030750401c41c2242d5007010780005c1c00e108514000c50302103040c040f149000420181e9880c0c0c900d0414608048940369400e510300d81002040c1c0d2000b0090290149541c203468980300c11010802c4540142480d41031001e040e110a070805851520982e00c6810a81060303030000820000c100656a5084512100c4452001901b402441040e1100d10702455900104400c1c03182100f0b00c0340568400c605901103a40700b00f000b01d25106904080303003c41c0180c1010760490300c070700c00f10956182015005004402c0800c5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 330992751 1250 330991501 330991523
    0x2103070b070c050706180906030f03050c0a060207110906040c0e101704060f060617130f0803090a050d050a080105090c19030e1006031a040809030307030203030a0c020705130c030b1507 81
    0x20620021a084c41c48000c0c1032070f00b03062b00d0f01c000a004401506400a058060780c03207e19090715088180c0c1e01080086070b500b42d150003111203030b1500c002c0705034000800b03a908011501000a010b0249000c090056100c0c01103034071000ca901e84a01001c155144180800070810b040ca0b10302100580440980b0600060a080b800314009100300c074020710752040524a1500d84e10341c0b0f5005e101c019202030342500c035812000d0540002c64800b40c01107004003800c40041c5280001801c0c6681080580c88aa40c1013007c100f0401c0700d1a9031000c4d0f0a810749000721350101c040c3d2900448007800d44214000000040c01c80c0b90640340446cbc00d0307840140305140c0b00083c0c0f00c010034410503030011100640001000c1c21103010748a03610228442c441c59003e4810303d4450700d0190000c0c0001c0c038603048800d04070700503800001089407800b04c0f8000c0d00410f0701c060000b4188070b03080100080400020400c010f1119507200c00042d00756120703801042d16281c0c060003201228240503c9104290b100102c10341e1404004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 330994001 1250 330992751 330992759
    0x50901060c0804060f20030310060e130509010b030f06180303010303120509012403170304030203040b030c12072006010521031e0304022103070b070c05070618 70
    0x240804810745640005100c1c0b0786401d050041e03031400505020f10007040310b40801c04450346032010400c0d0740100020021740e00d83c902101c86a14240d120341002003042180c541c5503285403a1031000b121110000040070941d56980f440f01401400c104080c980e141c41160400c80e542034022591a00840700d1003800c10002401798000d950300c0c4001e210080002c0d280d40e0319030380d40d04401d511868204804a001083d80c8840080d85000c4001192225140c21b10300b2204000f00000c042d40c9003914800d0141050540c41d25450180d1203000314403441c25841400000102c40a500b18200c514540a0090310a060304254a00404074007001c001c03001d2468518000c51601500003800f04e04907000180306062603d44601500d0082d40c03441048601d45c8810700108014459810b1720b0b04400c0c0080d4402d0b62245001c1c01084455012560305200324941c2551040658074040f00300c506d500e8000001034025168413404903a42e85a0702d401800d01c0c0150040030814960120b1100056821448901a01d58031 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 330995251 1250 330994001 330994007
    0x40611120f19030c0807030b0f0405010b0301060e0301090b06220609060e06010302130510090315240b0a08040c08030d0f0606020d0504180e061005031014060d020a12030905090106 79
    0xf810f13000c0d80c046400500010f41d120311076080b09003d03413030207021908036882c0c1102007000d03141c080e0040340b40040084014008550310956000740070b0720440c020302046c4400e403180b11016002a100304c2c000c1c0301d18100040b03401a0028100010007070060100070050381c5e00d05900040c07002d03000e0300b6464059900800d803198071900940300030f03c54401d0302e40d1500b0701d00300410802c290166106001c5c485080000030126032140c941c0c1000c0102100e000c5400102d07010240315003140441c6c8802c01178000782040c001e083e446802d507404070219080c0b0084a895904040700790241580c40740e001c038031001403004905425500040169030b891202807049075191141aa11603001100000000348284801c1024103a0480200c11507080340400150306104041c1a42c2440320440314910300149011040080c0c1c102004041c0600722405820402c5200b80c22a244a00300003400d505d100d244621440c1055685040300c0030010310040104140f954294517019250f580c0c10311580d031091600d1800081c0c1540 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 330996501 1250 330995251 330995261
    0x209060a0e1819030804150603030503070c05010204030c061706040b060f0f0d09030207060210141303020c04020d1d0304030f150b1504031e0503040611120f1903 71
    0x41c1c1c840d00051255035240350040b020a54501d50100380c482e0f01c0c10802a01004042d100c40c4500035910a48030349442e003010350171000705650021101d40341c903d0820102e17902c0b0041e684c20003007518007081d248089080c0140a030049401c09000c98281180001d081c13030308030040b4103241e24850344007103c80c0d44407010070049548212036107400c128104440d10129120340002e02c83e08036141c1c252402c207456020b0200840328407100440260340400c5051144540412240011589680060000ca0f00e032130394419401e50050f003d0390b140c2120070182c03010980207202e00c481042010381f04540382d0742100c0c5134102a2803011007041442000743c032440b140f22001b0041314140ca81001036200006010740c1d40500c04018491100c252a594951100c1c0680c1d400418042d0040e219004c0c079221030450a29800c600e4800c00c00b2001750380c00030820400154080161400c49a407400d001252039403818040c0d04100940c40c030000e04010004541440006c2c0fa00605030503186206140042c50311540160200c0e0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 330997751 1250 330996501 330996509
    0x1c0f020a080301091e09060e0f0f0d080603030d050a0c1128020d0605010b070c090b0a03080a03020408032703030a05030a020702060d09060903082d10030212010501030209060a 77
    0x20810001131062102c02e40110035868401c1c006a4550302500008038104d88982004540d041c1e00e45000800000080194001c4040094058403c10b06002017042e0340300c544002103400d1050b06000290a40d60920685000004140c0e0500280c83d000000c200100b022603d0700000c9000742e44030307000c1d400000400300c00c1c6156110b51034891340004103a41401501000040380d0101860001c0000600280507490090521055640c2c40f513480d0301d402c0c41e034031005800c18500d440c0b4000300b59800742e85040c130400407260481400d80c0d4840d01648101d02a200b07541000403184000107841d400020070782000c01d010250354003807043c8408030030201a203074891080403000090003440801c292030207039401171100340e100a140e180f070035204114081c2034848140040e60b0b003071b80e18040002416040100700b40c0c8582c1e06601c0e641c10000700d032010000d055610100110700f02d02c00d070020305a0070044008a014680080c00305456081c0400e81030b01901003408124003610403c0085103140c180310741c035001a1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 330999001 1250 330997751 330997763
    0x2d09070302160f051e06130618032a081e0d0e0606091005030a06020c0304180f060501020705130509070839150a02070504020d0614090603060708181c0f020a 69
    0x90311628458000c02c0d0087d030054886a03900c10350010840f40140c1083c036800e2190319140c0c00a100c0310107503443c3e00c1c1504c001000161912001d580050703542000c8030b910508001d8414544a5030004203106800b807510591050fa14005c1a00c0342c00c01c0000c2d03003d211b08022074114000da603450640190307603161885011f42550001c2540400208103401510640407102d084034242943d900b407c0c066401d02c0608602007654520120405918034090b403030241600380000e1600d189420042101c0c20302250f2041200750359100030812400090104500400c2000204c0e4100c1d490f080081420b026021400401690700440c0341002c1403c2102c1c4a51030003000b00400c3c4c0c4100d071644403070b41036402044030710110301400b48003080607600c51002d000800104000055000c0c1018103000100c55101040c5100e40806401c014040d6800035809601140c0c1d450030030120340301c6400322510b603140281410164081c1002e1002d5079010303002c00000701451a0744501040d012000280d07220f64021002a080d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 331000251 1250 330999001 330999013
    0x3070f03020108130c0909030f0e030d0e0415030809011d0a03021e09012c1504020c0a050303071206060c0b0103110d021309022d09070302160f051e 65
    0x1d98029030301694000022050581c0310a15aa200303641080c49411054080c2e40e20200f90081c036a0020b8000104441428016180c08018000030365540c11404400c1c03c00c0300c41d4924000c0c0380c40e50303000600268404010440c4a54882c81e21122030340200b46078500241c608011981d014038021020ba00100000c4c109030610780c03c42d000d106443c0b0100b482151b81c510400c200040c141c41d601c1d00ca5008104403c0d0707000c801d014000c076500311900e004d140140102a2001030196404403903c0001548904031801640c0c1c600c2d40c960541481c440f14400342c201d01003c010003104c141c004039030a84090054004000d240d4a4400030b6840e8000e844014000c4800303c0018800203514490045218a0050401401c0c01540e80010040881c0304241d207895602c0d111803008508100806584640035507a400400b041000d90001d40c08400383d02c10fa21a007140300204240368000ea04488902240040042c024580c03810001500d5640100441d600e00c645241ca00e908411528800c1035801c40101501c5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 331001501 1250 331000251 331000253
    0x7080a081006120b0406080a0309080d050a050f0c07080d05030f0a02030c0d36050f190b06180f1008030322021306030c0e0a0c080c07030e031e0c03070f03 68
    0x24081501d484d50001d640c1d05000c0303800d600400401070341502c240d854600c0941442842e904103102c01c82008140a01841208049a000801d40f14060f0344a55a00d45644210005518001040c0d03c03280e028000d10354003107a8150b2200045100e40c03501c2640c60500d840b0660301504030f200454050074504028001421200303c281c12482070100c519150703c01200710000451008034a0f01d5568a2842d200e400c0902007081c2881100ba1208500d40075107640c4041000c04c04018850140040c451150300d40040c100c3d54809000003409440d02125003101e1424a10720766605805a901600d424061140001d1a440000071070b0310a03040c043e00c1010743c3c0340186980d01c0302c403d8a0804c980c0060080b00500c0221303a02d1241500a50149112a802518080048a6044003c0c2100303005600307004101300d0035504591010341020010800c1c41d40e803110360408940d190460700c500c66060290308149081011500c0d021841000c00d0401da4107071008810800d07030381c0c0b1681d10070f070320542101041c100 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 331002751 1250 331001501 331001537
    0x80928020906040605041b0e0306010806060108041704120b0f041112070e0a090c0b0a020d0e0102010912080a14060a1703070b09060f01080f070506091507080a081006 73
    0xc0e402c680003038004100b858903900040c0c1034400c59038651280710106c1c442ca090340c6034003a103140a261401e81c00f9000650608580a40b42e900040c200384c14040f100300800c0030044411132011342081981d91040c0c540d5299403007123058590001c0e042d07034050300b40701c0405c0c2e01c03822050416005030b03808104d018905c500103051001b0307080c1411114109000c2c251000440344083e680c1a48182c00149000464031294501803401d44000e8000c480e9003801809111112600041c418a00c2105401d1100004140b000100c0c050000d0110051400c814108045030b0590884001c81c02080d4034901402500c0c2d41d81070242030188229069036015100c950100f017119111054450000f1045050700d01d00492600e0303042c0d2900c0c0a45060f2184e500040802c40429011307c08280500003d4003d48034980481e105590703a030b505405124412000000c8031546030b5201c0104002d443d40c031080c00c07a2944081e042c14400364000142c05000b04005d5400100583c0c01045100700b80c03034040d2214411032149036150 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 331004001 1250 331002751 331002769
    0x60b03040c0b1201230d080705010507080108030d0b1c0f03030c020c0d0813031407030b130807030807120c05090405070903031403041a0f0601110d09030b0a060b0a08092802 76
    0x240d2983c0962085000c142d89a20f8410300700c460243c42c7d41c5a41e0700322883c0a500b180c1004280301d04001044005109900c0c00fc0210355203010034080102d40509108001107400da143c40c3c403520303004003c1158008204001c00d440d16020701a4808212030040454142d8031400d444a800c0c0d0700c501003181410000d030410014003144c000c1e602c142e2041d20388956034900b40702c2c84120ba05480ba84009030800c200000034107115070056202580541ea00d50703940d00c0c502e003030084040050500070490000f901d0310344210f650340618601c1c2c0b5010702620a0100e005001640f156940070300560810001448050141008804030f03981a910003d0302503142d600400690400f5000321f815083c2300c0700e0380c425100c11702e40d99401800054103102c0513042c40710000d0005500f807009640503410140c565508560080c050030b085075046514003603240d51b08503440000340010340041d010444003107081c2036500e603c81c4000340328401040031203001501d00b04070b070039111008516000380003521041d010014103084980d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 331005251 1250 331004001 331004039
    0xe150c03040f030f14030f072910030203010b060a08040b180a06060510030b060a030902030c03030c1624050703020309030f0d17160e01020709060b03040c0b1201 71
    0x2a41d04103902c0c2c03001110610510340c400c2c0c8a500c50030750b044050011284010b850101400003c51902c0700441c44000607020356040035201d08500580e021081c0300d00d54207090000a0004100d0075803801031380c21421301441c0e0209034000d61911894080a040400440700c06025503100c04081741e907180e8901481c510010080040c01c50503020f40300d0100d604210b4074180300c1c0326007070110741139040409002003200076500710b00405050854848468848500b1914038060500e00416501c425002203480d09624441c0b00750107100004440c07480e14008210f09501d00141110254401c2d904d03910160001c1244981c8420012844484508036008400610055200340152070030010104002400c01100d00014480350700004401030559a100700c107884c9410454008401c28100014080c005d140405003000601010940400f40c1e607000b004190000c0081c000203000c841d4079a813035110305400c166011640305004c05008280d0481650950b03062074200b40310a41e03181c0c80c004411702e00e114030f401 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 331006501 1250 331005251 331005253
    0x1a0412020603041b06080a0e0a020114030705071e05010606080f161202120105090606120604020a030204080f0a060c090e0402131e0501140919050a020d050403031401060e150c 77
    0x4e66603900340072032542d4000304902c0d200c4989510340700507218140c7d04201c0582500d0f4000340e012400517038000d0011840303114100340007600c80e910320000390b5183c4580030015022041e4246420001c660815003125aa44100000d020315580c6103015200d51a050750086020060040050440740c1d10307d2030700d040c82e50f6501d40240c40c002106a0f80c022a409141000005501c0c00c0c01405182000c2c511a60408422f8031100e241410300036015007210f1018000900c40c540010b1010034140c8642c040d1009807030440140d41440081840c901d0303135034007071000c1201c3e8181003100510444d030007441c40c0001c4601c00c0e0000100c9a4a950800070440d1640d0b101c81c007110b81c4c0b105840340e4600c071220500c1c2551080500011654100301d82070050843c031017031861007440088200128100d100f0310f02c0340c001c1c07415032000c10607807150b0070304402030701895203140025441c0000300024503915070840d0b2100401c0d1007180030983d8868400300d82e25400421b055401050801d800520720014038010090340440c40 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 331007751 1250 331006501 331006523
    0x50613030f0203010207020d030216152304210611071a0a090b13110406031a070c0602182d0d420204060903060b01030e06040605011a041202060304 65
    0x340c00907520365409034044c2c005a0100b1855045034005c2f0000802801c20070703541c0509503c0810f4001c0010300e0000e110b1400e00a00070f0300807940e404500648d000760114840c218100100d4003c084503080005000b96401410900195083d00140c003c5400300798001c1401c1d42950580f4030711500c0740f41d014003210340d001c0e40e07020a1004a4030140c806d600030811200d54006036400d81c103010072200c2842e08082c0c0308914001d020030008000064020300080d60f000d03940c11076a131b1240d0589059102d8940a030951b03000088400e07500d648803542454050084032031030a0072031484d04a15100305030780139a441c940700b100c3c504450751401d000403500003403044158032600403400c0b01d0282d0140c0c210b24001420182c2c41001034050080c43c4250040000d10103085084c20703d0442c0007042014103110190001c0d030346902809441c2d120303400013284c0740002d038200d0394a82807601c0c004000340802d2003290074155a00130384240d980f4401e0100c8007128410710480f00510899001c00038690f0000d0401c480544600d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 331009001 1250 331007751 331007753
    0x50c0417031e04080f161406040b030705040509011d0403031517060a0c0507051b06040306050f09121804020c010e060c030709051f030e0f010e01090606050613030f0203010207 77
    0x18900c0310b01206821038040c0c0c98519005442e481e000d0303001700c94005170700641149800c2d5600240c001c03084400340b0350104030311031020340452118410b42e00701c14042c003400402c01001903085001070086507001e660313281041e0703603440180c1141c5040b40c0d1000d400d4007464010801280c400d41000003808020900302010594401200303410000c91804c8042c0303070300544100f0149007000d201d00854800d079410090315000c2c0aa42d125101c0c0540404460309400400b50a9000c3e155041614091903201c4020489814215a041e8484008881e8509079100fa86242e0310303610118020b4611112001eaa250a04020802084041d40003418008840d65882548141007502001114060b0000a480769924141110000c0060703110350089405241070560003a040348002149860982c424500001c50610000240d0300346083d60040358415800c1c000c0342c110680c010744c480c2d205184074010400c0103c0d5210b0501c4114001d046103424a02d0480f0000c00110b4101291102040c2c03008000628002039 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 331010251 1250 331009001 331009027
    0x3040f03050c03070b040b0403030c060908030a0902031c050d0f0207120f111204051207050307080d02070914132604050f010207051f140307051c050c041703 69
    0x394400e56660788221071080403400c00f4844030020b0400c00304060710b00340c01d00c042d1912500c10391200030b0800c00640a180e0038048580e0203003810641c018031455aa06020720343c80701070a02018103038428091603d0701480c4016107443c091443e00d1360b445075818042e010048000401005040c00c0c400307602080007038000f88401014051721400c036103d50039000b10101d00244140030b146c401062540c0420f81c074448521401c01035800b183c90840300d03460b00c0c0766018541420a042039103d540c0610860001144c4820f0200da8400661055800c0741c3d207244c0c0d11a201c1e4251100c2510280c91002110b01080300000c110755503050f803c0c0140401581d08a00c400741c0c6040003200c0d07995041e40000460700b40064501042c41e044498024401000e20030304040000d131402114030790340742d032410040d150b400b28070b0b0050200340448003454400541304d150414000c1c2c1594031000e80207594072030300100908080d40b240b0500b80950040c0c10f11a00389418031105e0009942032184004940c481444070342101c1138 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 331011501 1250 331010251 331010279
    0x905040911060a05120a02130b0a05071b0503012a0507031806050901140c070612060302090c0c0708070803090603072706020f070e0609040c12050106030b0f0106050a080601020304 79
    0x203e07541c84a944950469421940c403001a00340c0c171605004100000c1100148580c190035665246902070341c43c58910405d4902c1c2c410008006c9c50050701c0b103d04451030103815410400c81d80281c00a202040b0a0300800001c4a844030303010203604220410070454030700c40c6000e85003261107820002c21303c100d02c81e01d0140d014101d0703100c480002c0c0e002410542550b40110000380001451030b0b01c2c0d0800c10020440c6407220711901841040001615500341c510f000751b0418802541c0103000e650550807d03000b940320341e52181e003d880b0288281d09001442040005215040b286514007950801d02c031a070400c02d007030b84003a0030702c400c0050756640d280c903003925a18481100d8030005652496a071401d0006801d04201c400b07049200d400001c2d0402c0003080900440303610040c2100c040b4500c2c0d94a2402c0280c0b11400c0d080128000da1609401041050550201e01034034011103070070081e540c0b03031074501040319000d0261000040e0700303111080605000d00c01d41170700940140140ca0030300c3c1c0c54075601030410b6 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 331012751 1250 331011501 331011517
    0x730140a0c0207090e060a0b0301110c0604020406050a030210050d020415020d020f07120f0f3c030c02060c010b061c0b0a060207061d1f0e10090504091106 68
    0x80d61180d0480d001501044800000d1203d14001c1c40540c0b569003a00b070300d407074000301f640a05544480390103070b0969080d4031140080c03050001664407144000025680c1d050b084034102d009030b28115000c9010314103d030841d42201e9006003a902d01e400c58140031181a0484d03c511410941c00344000301e40100d284001c0c44801160780e0007418504442e00c00203180c001a003c000401340c020700000d2203a04541012915a80e82015101d01040c02524244001208415028010404800c65845441d29503601200b40d100c542a8014094080041d040c0151103894002404549255000001030a001004d1b000d980154000024a5240c06000c41d145500091400d144462042d140f504042c0c468030030b1108101040d81d1818825041c01c0001c0c0d91001240645018022403805c51400c11500c42d0100807100c030701403d440040d4140e400300c070000740301d0804840045011085404d038141401170407441880c91507030300c06206030319200030301c030080ca1548400e40d240c40607220740c580030344c4a40000304120 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 331014001 1250 331012751 331012771
    0x5040c050706140601021e1507080907141809011e0f0c030905060a1e02070c06030e0607080f070504050301021303020f090702031c02250b073014 64
    0x1d800c60314029045880c0c5070303041003003040900c0c107208080c0d03400250310924070300045c00d1090b0408245810f516100c88144904204101075007001a4558230110040c00340a0660860b9001919412036546110744814510303002100418500d141c982c012034031540140800000103800300c1c3c4110304500000c0a00440c18910351a003a0311604c2d061148203540c00080d0500d02000314126580d102505c2d80c2c40541012500c6447c1c030300007644448840d00b4010715400000085550300781c54030748287c0f0803000b07121f0b0902091074400301c1c60681d00c0201d203642c8200b111340c0c2d4405044d80d95a0744201d103014050001d0b020844184000310391500d007407004068040c4501c5102d0307020391940c410804100364694502d4000c0c030064003442031040e000000e498071002175100919000129130010340c001e000d640001d140c078000580101d0b5828034500c60040209005245500003070f80e0300c007826660b040200c0c1303e08001ca03070354084c01d030940506001c0008103141c0e66000403c0d2580102c000080c6c40c2400d40b417040c21 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 331015251 1250 331014001 331014007
    0x204060918020910080a0803070315060207030314280908010c080603010b03120f25060f110a020c01081b040b0301090513020f012106060e0a080f0304120c05040c05 72
    0x1e6141100605600904e1240240e0040341000380c250b4641c0d174032400c000c1484038040701080b1454002c3c0c00584e140e0304034802d080d2700d89a68080007540d90400c0e00c82600400c1000c00c481c11310b039000e04203c84442c1e290400c2c458144403001302040381054150b000b041002b01415010a0740c4200f80201000d07002240d54103c0301d41841000c040c00c540450540b0b0b8482e9000c06000c003280410390060340d8000c00d40c10f540a0700c524902c80c0450000c4108000451740ca12400c91304c3c8200302059100207400c0650341810008100c941c11480403900c45d040b500c1015034800302440381550301c96420113500c81030300c1c04400e44002650806140d244c02176001482c0e01000032006024403040b43c410580d00080210041044184a801050260740e4002140b81000f448c3c185c90b5119416411202c04112001c0c0740c00c0250b1036807220001e00403902c1d05c009a2040e84241c00c002070440001076100b44590b04480650718282c50034611880001018608540a0303201c0308000416503158802c58056520326110169 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 331016501 1250 331015251 331015253
    0x305061003031214071803230c01030908090d050c100915020105061e030c030a030e03071418091c0207060e010534020a0f060206010b071e0204060918 66
    0x311010180a04042c43d618100074807102030324245040d90030013154100b9000300c5d89010f615107400029904040c1403c2d0404410840c2d4088a2041000c042c000006507000710f965480110203481000030054441d0600780100c0105103400c0c0300500c0803e214204683c158015840411f035220100c49241010410080d410004010140e20014a001d2544000c00c020303c0d0810025a41c80f41c0e51106501e0050040d01c503101d59141044417100d00c000080490b03180c0e000c10304e401041d0b03407946003006000e8019403000060780300185411240c4904028121099a01e50240ea00d4000b1b90040c400c0703916122f0800c0c1b042883c6003000d019001c03412a80e0140c00400e08240b4094021303140c1914050400404101c0081c2c68021061070f0041c6107520515031911100c046064118560301c00340107581b03c12000310000340101c25080500c112005a004e944081e03a03201140109401601c0e40a40151142c4c40e5549030f1204c220711210000d4801040010095195103c0d442150780091050305241c1400040310 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 331017751 1250 331016501 331016507
    0x2060106021612020607050a2402250303060e100807170a030f1202040914090619150f0905061f0504091d03070506071805100503060109030506100303 66
    0x19014151500042c108104a4031240c002d0140500c075121180e01c0340500a4110f6442e001100ca4580d00603045070240080380c05c02c6144140b00b070b5440c0740381c1e0030f40d004001a000d50718002c3e01e4900d80c100401466402158183c40101e0050803012010143d0b03400000c2880b54a20700c40c1401240c0d5210310300342050502e440715282401c0c42c1c11000c2c501041a2428420760400522810242c0d8580303800000c0c005147c105680306080000ca6804080c00407401040c80d1606a0140d00c00c02a40d10060031903032101022680c940100f82c0e0424055003081c03400307121040107500301140300e00144030003072901750740d8541d111107003d11600500780058592052206620305880c04076018a0a209910700e4800c01c2d034006030603481184103000040e51141560801d801111101001004030a010340c2e64a02680c50b1440c2c84010458809011441004844403410803100400e001c1d601c0240c6216440070303050509175082c4c1c0000304440d0401204020100c00a50300b400414002c801050b0085800b5040d85409 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 331019001 1250 331017751 331017763
    0xb070309080105160f210f1107170309120a081f0b0318010b040204030501061d010807060809100e0601050126010605070203190506100909031421010b07020102 70
    0x3066950f8145414401194034203081c0c420000058141089003007003d000035190518000e1402c0080d00d902c0d420b6010000c4c403608200ea607440da00c13004000e108035080001000d409001809040c0c3c2d16842d42141ca1070300000021130f08500c01400715000c210a4501c7e203140740d88404880c400007005001801a010500b0843d07501d41c2e520f242d03041c40c2e42d600b0b210002c201400300a043d116103030b01d05030038440c4012080d40220340111000c0c00a42d51030ba100d040440c0680120322178010b050300641c20702608003482200980c141e82c0c0c02801b404282d482d045040303038203040181c080d8016001b007014120040c962441804150b49410000d030405616040015081c89040c07901502e20907841c0901007805180714020605440301d5050035502c5a440340046440e10850400262881d1740f059504418424002003443c0700380700482d00401e6481c6c07500b40210988000800007030100d40c2d60000c020403200d00101400d2800c00c18516880c81960319424400401001e034010303504030f200094207400f50b59060007a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 331020251 1250 331019001 331019009
    0x1a0105010c2004150b070c0b071113020904021308060106030b030a02041d0a0605010e06041b2a0309031b05030607050a0302040b120603010c030b030a060b0303090603010b070309 78
    0x2410500541c0350241159144600581282d1800e20b0248980da03c50b4001c090f000302101e810b00715603449006041d403907030003843e0950708050f80900c0050011040030485c0c0c41141e210080050b048400800e03c4589107910050040c01502403145614a840754406001c520200c1d02c81803a845140c00c0c143c5041480680094041604141ca00c50b4a03860024460540744c1c0d065900003110440044100308460000c0313004041e034041d078210b032024000a6004541a501c441100e0225521102c017008200c81d0407000e00801c0e26003144100c40d03000e000f005401440d070f00407001100500020801615a140b010004402240804c0c10500c1404580d41e0f280c440c5010700490140078074200800282e5906009114000300728001413004401031094041c2d03402000762104c4c59480d850340d03254982403c0011241c85010b0740c40c190aa0350124428000d1048070b4030081d01070700a841254489a0103410181010368042c03100f003201d070000e915000011802052040c52498941d103441c50010241c1c000380d44 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 331021501 1250 331020251 331020257
    0x507050d1214090d1106070b04030c1406060901171608030c060c1806071a0f2211010f0e33030103020102060105060d24260c0d08070f1a010501 63
    0x4505140d136141c140500c2c3c20190030008024043e21041d00180c018400c062006001600d2082032000b01500107441c28040780c443d054050f0001103048c14103585d003104894240c1d0080c0200010004951901ca2a080d00040c25040d00c010380500c01e98050130303c0e5a50b202c8016075000180c03d041c0110140255034128851450851402142a01c203035101b401903954030380700c0c0c90000399540801c0b5001c070700180e11310304010300d4000c5881c0045944c0035034134084a4070101c5030103030746640515521100351030400da0352201801582007094401118820101c800100522500e4440f5290598440710140d0600000c0d05e0a55003203400000074035804a070400c28100c0083c1c0030700c01400140e802003200c0f4191002516400d80f14003811240202070440041c880040402c0c800c1d000900d11070016410060300e0804200040390100e080c03a08804420041d82c21301990480c042c210fa0914160781c501d6001ca00904005041c0084ca4440c0c1c2001344080b00d0440300d0201d941591803415542d15801b0b801440242 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 331022751 1250 331021501 331021507
    0x1506090607060b060d090b040b061c032f030408010e070305060c030a0f0509010603060b2d0d050d021006051e0d05100c0509120604050312040507050d1214 68
    0x90085086030140e070a0050600380c8829007000703951a10800e603168a17289035000e002036101ca00b4225104281540c055075100000400070f442c60a01d44190112001245e581d07100c500d0301da840c112103c096040c1040052881035800b41e03600301c46c45002805c00b1901c00091581c5a1a14900e2800c45100da150030f40690401182000031a001046495120100b500c40355506d65903040450001d2414114000c80c080c41c2c072007842225401540a841501c0c800c85080010743d240100300040c4c100a5140140b00e846900c5408048440408140352550300140540401810680d11507040c9001c0301e445000586c020f00759801c49402c40d020714801003200b61080e050380e034480f04145554401c019070450081c901010a44200001000a440440d450313a1081000301a4400010810350020504034818103d01213020078548010075500e029650100040d0325003582041d4542d00100c00400c02ea80c1401001800211034680c450125000d51154181c204004004480540b501540103030280500d0028 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 331024001 1250 331022751 331022767
    0x30f0a12030e03070602040602030a170c0a0e04020c061f05090c0d020c0f0d090e060406050603070c140118060f0501080d110102071b080715080c0a020c10081506 71
    0x46484003001009480c0c0030401d0420002824518412904002d081e54800280004d1059000c00546410003590390b403460303a10700b108810505200d050b00c4100721b6003000c03c425440786010740707c000c141e5840130300090306001a036000c080c03c01904440b0800d0400840303890007a43d40400310702d070015140449101c01e241c2455005a8072501aa80b6608d100c540e00240001e0303481e500700140c00100d0014011940c03400c02649005040702440d2244014509404000c030300d480c5028010b100079500085c001c03c0c15643d8190086481800c646410703543c3d245080e610030003c0400f0700a0302d64040d030f03621049485a002d85005c00440b034410741c0700b0ba603091030040140320410011901e2000d0402d94581035404401414441c0d00905c5a4180200f180c850b405088050000c1410389404840702c80041c1e9007144d940703140e1074400c0161600c0c9500000c0d4402c00140340010b000d00608640100352044500b4800d0703200201c0c3c1480c0f1400701040100f0380075020015101044c540e0b0700b141410a5901c1400c0c580f003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 331025251 1250 331024001 331024013
    0x30c080607051c0b0f0d060c0210020f030403200106030b19050601020619020408070f1a0f1e0f071119050108010509071b1505010f23011e02030405030f0a 68
    0x4074106107840c05448660181d02a03403204e8081083c404010002c211411b05807134040000c145170080d40b409801100c410301300c5200030b4070030707a04044040381000d480c0d50342d40d0340c044a00e16922014101041100d40d00a56010801d10503200907500c1003c01d40000c1c1011111406841c00c101d031001240ba04090400c89941d81c041141da40125030300200c5106000100702d90400f0f40601e0304154000d204620b00000e404100c1074880c0200c079034080030f5510000200036082d4040c030034840c0400d540c010030461a82d102031500c0c07101c20030400c00801036040c0507624a06107103e40c40080242d5065418101041c80b601d1301d203010049413400c0b50b08410181c0e1420380044d100c42d005100750341c407400110340010006030150b900100b12142c280803001007688980740c44405105551072068149280c20000b14005000390140f03010b070760084400c0c6922040000c0721030f0080c080d90342131504210301103000602c0d03520719010943d02c1003107a40266485500b004289883d041080107503100a500501820002c199 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 331026501 1250 331025251 331025287
    0xc03060f06180604180b1006020d02211606240501090e0a0f090308040303112b110a05070b0903090f0613050310140f0103110f0d020406030c08060705 66
    0x100d00740b01c00c11140d0720200020001c041e40e55800322892100880d61082090410a0a205d550058081b032000f80e01d6000407a641d0719406030f070f080964041301c08404450b0010031038525030410b0380d021a24003005202400740d080c4203903030700b216016100d0813400c61510b0700072440300d4165010703640f084200d0718200c0024440340c3ca901c03403070181890840114036050301c103402205080d0180103082c41404c6051034000c02034241280c06500092174240c503544002c03a14011903040044019003061a0104031003862580d1001104001e1040d65a6020440d001d88000103007002c030340141c8945481d10303030b035003001041880c00403c40071840d00100050b622070307030312039145442814082e00c1d000d84400214406000b068000d400c481d81c10300c00c0260b40404907050390030945490551211207121034581100c0c20f0a030f2882030000612a154000c892001800c1c9810107000c1c54100a00942c0c2141240e0041000c40300103030001d0f2a2400132050501c0f2903101000000d4003c1d07090714010f45081c05114908426035 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 331027751 1250 331026501 331026529
    0x9010f1409041d01020301121202030408150c120106050d0c090803030c0903070e01141305060d02150912010608010c020615210f1c020c0604090f1d0c03060f06 70
    0x680c0c0f034441c0e501c000d0310031a03015901c000c2100215a6545c581102024502c0203e8003100d6010181520a10ba1840441590200d83c0d8201c0103101c2d0f1065100c14070300aa80c01094101850000d0080100040c00011090f0003807440741c864035681d200c012101400d90b4074403a040b000740701c030055040115840010481e41e00c6804802199110315054002a043c03841c254000f05c40040701d0400411105040d10711103903d0102100c14441d0340c000d070300900d410f44c0e0040b02e045601c5a2000d851501505019514102c8801d5504803940380c044c0e880c00040c0c00303e0104d003101c1080c0e0341d00c00c410b12805c502403140d4204989680001d0560b4030b0f00c401140890702c51542441d01a03111008482040b02c40001e201a102560600380c2c1d000d40155400316545020a44841c8020070385c45207009081400800c0e031079050400600500c0c035160602c010781c0c02800500100c0c20100d681d858143c135000341110b428988090005018121510040301050720300507016005040b41041d40061000a540d00c180030403080c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 331029001 1250 331027751 331027759
    0x1060e01050d020a08060f07030b0405060906010305040606090606080612160b0c03131409060a051c050703020a060503090d2105060d0804090b03061e1f0b0d0209010f1409 75
    0x20302c0620100744ca210455219000030b00c2070b03500f48030743c2e06001d0b494113204181d10354041140100403800c01003034820035520503401815107400304100e54841d400c0b16a001e40a000041046942e030800c2d1000c03944c281d80a2400030f401803003446030030f25000181c034406140d59002000c80e030303005464500c002441d0307115554400e14001040d04480e207040c400e41d0300f140007000c0e0002c1400c0c0c0d20702c418100542c490344183c0c42030760143c00041c410304d4400080c0044e20b001828007000c540300220400b160112820742520b00e84030b89840000160740e00707420000500b51540e1402d84074203041c44114a0042c00e40014030138000746403041d24059030040b020102c3c1c06518500860a500d0b50b00114210703012400c009055500009404104102e580c0c118001d0f000c4280d0440b005607a81600113042000d10301c802c1419140d40c1300100711703200103e0361402c004c41e03c0c3c5080c042c031aa50707a5405c0801c5610420200c0031043d004140c2502c80e41c3c00000542c203880c2c25041951154190065032003e0b80f080d000100d100d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 331030251 1250 331029001 331029019
    0x3060a06050a1103030c0705010c0801060503070c05010e063c0c0d020c07030318080102130302060a1e02010c0806060c0a120c1704080106050d080a081305030714070801060e0105 78
    0x55031191910f40398041540059903560300741040141c85943c04808143e940c0d60a1203101911203201c1c45400d0f048a00966500382141c50301101192050b000b4138040e2000c0d900ca808011000342c00303000603801034226a41c8001c203200104000c01c2044000301c02d451311312450015010606a040c1550355128400748040c0e5940e024036440d800007070042905540e0a40f045030408410190441c0c522100c2400707807010300307140c036a8500b0715500340d1240740404100410501c00810047c20850058580044a4180109007500b19000d940e80e0700c1041d1614030041c0c3d10341c0203203401140c11000140d00240140c400e1490000003a55055880e000c030704c030080c0711042001c0146880ea2051900b2071416174040040000613010380e6000009402c80d009010480d4a007002c0001c10b440c041c200841c0441c0c2c49145682401c9218070145c2d00c40c40300504640144040703000c1240014028070013400e41521810100c5441614440e400340740c001c0580109032940e140c5582400b41c42a0b0045582c1101c808071200c0d10 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 331031501 1250 331030251 331030267
    0x10507030c2a08010225030306081006150c1a101a04080d2d0207052d060f040512031b150603030a050406030b0109080d020d020f0303060a0605 63
    0xd0610741d201c001602e403a000c0086011082048680c03030846410440b0762003802510398035264203c4c410340c0e2614240304030301600340030100800c0d00080015070180c1400141c150f51928001e003001000c200c42c1c4801ca0351103074180550019058008100030300e41ca8151080d00b078950781c1202c02003060b1a080d0200c0c0c140400580040e184101e0440605000c058103d0900c007100d180003043d4000d4001c1112a0080d40b1411001a200d44801255490100428032081400b6502d82103100c241910700021401514004500c0d074a0302400c40700f000d80010591000d0340b0040a078180c440781c0c100f518034428102000204400c0301c0c00e2050f1400c2d240d0803600c20980c0c9034101e109510b50320032420301d6000c42d4844680c0707c0c0c82203004180040060070038060564595100d9040540328410004150003242d4148010700c40d00e03109500c501030082041c1003601120340ca80f400c03245414101c0d0030400c0140c2c420306d5041100c60f414004a1240f00c400d0008604504000e00000d080800c28001d0800300000416001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 331032751 1250 331031501 331031507
    0x4060f14030705121b0d020909090d0f080c0d060b0406020d0c0b0109020c0312040305090a06050a0c06020c16030b1e060d0b06150706061401050c1005280c03051e0601050703 76
    0xa11045c0342c6200e495501c0c04920341c450b0103500404446445003034507000165402d0070100c2d840c2c030b403415a56548106402c411300c0a6802e80c0c00589407182c1c038032083c48001884100c0348105400303021031415044e242c51800d0700091520165030102f030104000e003041100019000d24240341034410300c10025860341c080c01c14091440c050b080d18071420405000600040c16088402001e410006a03180e03c0050703103e43e405c1d141b81c8130743c4081000040a150030700000c102645d0203041026041000d42d9140c40085010b501d5020090300b0640d58500f4407070a1081c03085001a1061a2090360000315541d03190103000a0120120740d00040d1810f0794020000d40907568140c5001204141491010740320840c50401034014082c80c0207130581040345040c420043c0d80100103603042401d410004120350920400200054140981115650800c40c482a41ea02c030000c141c07401c08003020729001401c08034504e0010306440c401b8056089001800100703421030003011542c2c0b50702c0142800e1440d590b4100d49421 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 331034001 1250 331032751 331032781
    0x1d1605191b020d06020405151602190e16020c0102010b03121317070602121c2403030314060a050307090209011709060a14070c03120e0304060f1403070512 68
    0x1c3d0702c94a4083e03220300704a120b9000d00700303480e01901d0820b480e402c2400440e10b548515003456030900544800d000c014038007901a0052446c2a0413070300c000c40e64174140f0241014050343c01138005002d102882c901c10342e0400918164000901c001c1c007103004e0b000007107030301e0f10011050602032a03000100d500c0d119002d5803440300100710a407078020180454021107600e507908d6018410040c05000f0200e07850680140586800c4100c00e035050b42024070005404004140c07600e01c07034020b1b040030031001c003044181c0e0301e00000450081c1c90100ea04200b03c1c1c8081c8000300001c1c05180700303034203200b001d1103da2000030b1550180e031510040141e44060003001603504900c00300704400f10701070100400505060201e0418081c001860041c88054008010028a07100444452001465294140c00480d110b1968440c9001c50070400003510601d02070258296403281e00329102160302c1640454074907030f0140f4100c00c84580c00d03540509605249e18010500d03c60100f480da0403901c450045241d0224007000d03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 331035251 1250 331034001 331034003
    0xc0507050a08150106030501060509060304020102070b0d090201140703020303010b0f04050409060603150b220b040504140d0c0503030612011d1b030f06010b0c071d1605191b 76
    0x40c10040d6603081d855a5401c3c4640507800c00c00000c00000800310301034011903058400e00e4503840c0c20070b80f0640900040c1e400c0140141c4c118404c0d10f1001410380c6006000340404035410b540854241c1003030001403c00f41280d110707000441010054000441d50200582c1e054400b0185d110391b49110540116905029035041168054940003e16081102ca5030249080b2031059009081c0d0000fa80319003000c0f10a00109030f500100d00c013200f0445031444210702240c10700340c00c00000310703502d00382d000c6001c4620032101111121404009102807031000c00214a134009180391800031102e0503907a070b03510f81c00301402680c06500000d15020125100390840030003042c0036042c0701c18000d02105040d075904a41000e03c42040300d00d00001006040115842c28107070340d89401002c01303074a01910608a0ba0141205034000c0c010f000c004247d8600d0503903100440095110440c410f4203221280c41c481000c024100818404100700e0440c00308240c0b00e4038030341c2014500740f08001030f08000c0149904d82110b00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 331036501 1250 331035251 331035259
    0x403020a0507080706030501240810030c030506040204060b031003020d032105010e100302060f030a02090907050405030c010306030b061513091b0c03090909060b220b09160c050705 79
    0x900890881800104041182c1c100d46e800d12031a640c9184c1c0011000d0003075691064400d00d403080c1c01d2010b004000c07054100359051022904540c0c0c9464040d4010b0050300700b11a9034006030240015440d10b8061400942682d545040c514205a1113004c064402440003d0043e0441e01d91441814041d03c030034805403500b1805d140050020307000000040a09000c0c03000c1e079000301780129a1202e5110314510681c1c0d406440285050f111110400b0b403500001c02d60503003503808024041e2542c4461400600401040d1110f90300d07141410100350800504a41a504040c42d090040001c50002c0c8103941e0002c5040d600e90000070b0012114128501c40d8010290700c0300c603110f130001a03169183e4011040042d111a4401a50303600000441e070704020b440300540000d925810074018024940d1004101e0343c801c4500251008a03500810401e040d15165111291411100da01000141d4014100c50310811540d00396189000c1c0d24071440c0302a81202c01082001c00904081046001c002d12809004018 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 331037751 1250 331036501 331036513
    0x30a0e010906050c073e0a05150c060f0f1801090605070e0a150f050f0c1009030305090c090703090602041a1308010203062d040c05191106060402030403020a05 70
    0x50b002c030140b988030707583c111028038015066451b00750750f100b142400c84040312100c02c81609003045a4124080c250000303680120000e10002d62544d42c0300c9400e4102d00c1e281c24031525501840c41c040c0c00c0010003480030f0600fa40703a034100300340d900011888540c006065206402c215107100700003801840c20800040c00070349818140130509400151314201d001007142d15100450312884104802048030310340902044104c110071601a0142d80504030010308031401904000303154a07814031f490002c0b00c0d03504410b965203c200e006e240c0d240c0262a40503810380001c0c0588482040420910380c0020110010150b94a81e08410090382d501114014408051110941d42c0502c1c3c50100e00d52100700d101603003000c40400002c1d000b5041c000e0700c0c450744005001000c0e10076030000102030240201294046420000c2002c01e0540d41d41c41881036800c02ca995080d112000c215040045420300c5020390240f09540e510078101c02400a420b69000d0401e0b240941c980d1a02c0ca0143d00d40015517000a18a015513 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 331039001 1250 331037751 331037761
    0x504030e0a0f140415170a05070905060901091a0f040908040e0f060108070903150e2a010e130906230411040b0120071e14040b0105030a0e01090605 65
    0x515642c0d410b03900f843c042c05140040d0b800c1004100c40a600f000101010340c0d030001c00803c0400360440c3c8410100340283c032600f0040756105800c000d200c6e008040400d6840c3c06011060a05000450141c20302110810400c000c464050781214601d1681038400d41c915605901a91103d4210310420380e40030180e15203854031544880603520303044a0303d07200c0311011030003e9003e600c1000e41a00842d426101c160344541507403a45400c080d095105441015155045860f1b1280d0410000141458030708500c6e03805003140c000c0050300d0030b50305401410004100a81109541c50b014a10300c100321143c40000c403007065140090140c02207802820218050940e009490300030349015912031807040d0100c03007000f050181044100e07003c403400c690000345812210300f440c5c6400c209100c82010404100d4440582d150104080900c14000425050002e4501000101d19401c80e45000c454201d41c00c3c0048207035400000c019000080941d0a01a00e913a48040862020f40c4003000d12908290300740824030301 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 331040251 1250 331039001 331039019
    0x1021b130c0c06180f111804030c02090c030c0a05030402030f01060f06030b0931050615040e0d080c070c0f030b0f09012a020f060112030206090609030703030504030e0a 74
    0x40b000c400c3d5641414000821815a100d191001c01a54440c2581000c0c01550f2900401c1014201c51160068000d030459400c2e0f80066200d41e100741d00c80d40e107880c054050380c41441404a0040d044106299090003070207820038a04056031001899803500035203a59a900000780780c62a521500001946011ba0200700801311503078117026541c140c1c07400d04c0100040000e22010042c00c40e012060180e0390400b00c00411380f40c2080c40110701214540e80c80e200c0c1d150f290541000c40c2510b4060f0350342c0119025180300d040900a150164400001030b14a40d184400003030f1520200030920680040300281e15003c01490751b145d41c014160052004c0c200302d859107404500c2e198103550007588a0401400034074074400501500c00c810794003004171400043c14a0030710003103616840c9030318158000d0010101c20f28004004942c0203014480c070802081603507042c0681040c070098121249500141d0411648010000444001d16410715001540d5940d40c1421180840d44110060b803080c2603000004074184 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 331041501 1250 331040251 331040267
    0xc1208040501081f03030c02040213090204060216081506011215050a050d0507090b03010e1b09010e071b03090e180105011e0b03040f02180103110a0501021b130c 71
    0x1200781c89030320f03681e101c0030080422180c1404844d180c08050000a10002c0e108007020340c007051000d0400760030105482403841c40e214081c1c0003030302c03d40d80c041410800c696040100b4000c40210110600d482401c080e141601d4078003c800340540c88011502051a99202e07800180041071100001c00c4a0030540b104202c0d20f0303d10307202d05485404483d80204540c9480d04214010f503a12000508140d89019082c8000d00858140c2607855545d03000b40d1002c00c0c00c140491010003440d00c0218014403980f00c2000040310040e000490520101c0301041506074012180462171903d00311020707010750240c9002c482c169540e811190b01c40c100c02c0c1c2801070703075040c00070034140c0350034484001d2000d0307a00d47c540104d5141034803103608004100341004000e0204a03d00458000c1c1c0510104490f0301c1140d000701c1d40000341049181040703c041c03030041080c000e005480356540002111103103019490080001d40e644072080d910407c0018446200125aa9401c0d044030440700814040c04450303489200a4071140c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 331042751 1250 331041501 331041509
    0xd051005010824010354030c0804030c0308030f01060f0507080c0705150c01230604050a2d0b090601020d08040623090f010c05090d0c120804 62
    0x185104602088a60103884014414980310314107458580d1892068000c1d0314911050314185544c950131110102c01e82c0300b442c0c030042c0c8244c40c10130151300d2200d039a09190381d4500c50701d01c6124164414445482e84025141c03c1160103240c10031510714242004a210720503640010000f0010f404000300b080484009148035030003295082d1407aa90b100820b403039041035040000000340d0100012070004582e14042c2011140000032a040b0315180c201107015034103c0003c41c0400e036004503182c1000348c030900552000c55101d003030750801400e0b0680160308003000540b541e0310454983e8001143c02000340d1000c6542016003001803880ba440d452819400100205c050700803e0820415035054101001e40a00480060b80201261468604202e4130404090320440b00117450310301e11a5403e4290740701845200f011501300100d070400c09a21440c20803100e00c94459a41840d0083e1207064020096a0314075805541c00ba01945c26490145060106a0020f45a2541d020354200c00e21aa0318003410a90b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 331044001 1250 331042751 331042771
    0x915030304060305190b21031e070c0f080c0d020d0f061d0a08041208280e0d0f02060a0509031504030201050f040512090406050409030201052d01140111030d05 70
    0x1110309200000949500d000080e8000d04074149406e444603141012600c3e0042c1f260035a82045100300050444c8203000c580828082808200700c018422001500c40c010210b01c41411102440d1501080d19501139000d286e201e00c040300c103080c041d900c81c140710504090b40300ca21100412a0f6151110040c4180740b440840c24411082510b8030000018090b41100e421101090800e440d1086000c40c184801400f2514050240311b1800c00c6914000070401c01d09800d03a18508160320708200404016410304e500d0b1140300c4095003000412124805611031075015240143d40d600b200506480700e205804420343c0612030b0340c0c414446046407085041c040c5201e5070081c029611075801c00345041c8010744000c4c140fa0409940006c7e81c2005600405000d0000f0300080740c0e259a03440000c048811444058015075107031000c0180441c0215884001d00100c00352013407140c08032030031302c04111a05000348107910220941800a903806a001c40c99150a400c0407656900030070458030014000130b031421468 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 331045251 1250 331044001 331044031
    0x306050709060306080705011209050c030a050303010303080c0a0f0c021f0801090c0e01020d03150b071a07030e03090409151508010606021f05070c02211c05090915030304060305 78
    0x920300200ba46c03011518141d4400512034440301c3c01308014480714004840174031980c0480c003090745050285100280c0202d0103035440790704d5420051300031f4070010952030421004000c0c40320306075041002031403608028070302525084014400328600c14210040c0c40200100c241000203141ea00c08e21081c140c0c1d6100d04244160306041c0402d8800034111424240503801c0301c0ea61040003407182e840040c01c05c41008500b054203135910070340815540150800e59408080a2031900b40d5408503407848d800c10b0300d40c5002c1000360307010340305507449001c0d00c0507992085855640c104c0c1444a03548a40c102082c1c0c0000070000e03601e074101c11160f08211032280b42441e50801200140d12400410440c02e48842000d4415000340135039000c0b001044028000c0d0140880d4100c0c01015072110b02190340c021440040c501400131070103500910f01502c2c40c400d00d01e00c4821444100041ea8401d06407400c6400a444081c05502c618140f8107080888059054141c48041030025903141c0c190080c0b8003d0340c0035421000d03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 331046501 1250 331045251 331045259
    0xc04050610212c0c010203300a020a0e0a03080a030e030d050c0c07060503060607020906010c1a09070b040f211406060a0905060f2101060801050117030a020706180306050709060306 79
    0x901d031548010031501581050003074000c4c198107010940015500707104042e50307204048c03803161400e80e03007179691507039455010651a1240c0c0e00001c00d8052581c084955901803451740e0341e9400c641c172a40c0d404500b0180c980c0201603c0350400c001352843e0300780391081400503190110180701d450b009800c80e10b40c20322400f0000507020f4042c8003180d00415000e0150391a0500340c0d001e102c0d030b2440207841c070342c1006a2490703030742c001c5130504240420b040e1601c44402c0050426000e5180b0304210398025400c4014200030400c000d40b8150601c400722071260340c0d8035011100d0340c00070841f400080d44024000200038002582c00303071404074400740f142000b00c8003105000e81701c0c0040011181c0031075040d90041070040d082c0f2980d2401407501c0b001c4403030b0504e1818041d038204038051f096402c0d40d07100c1c1034203a4583c0014000e495458600b1450108080000d504000b19200001d650383c213603105280500104840215910b0624503851000d1900410705201c2400e202400512440c0b080c0701d207100181c500315001c1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 331047751 1250 331046501 331046503
    0xa02090f13060b01122c0c031c0e130e070e06030a030c02061c020310050d031d060702061b0105071404030305131203020601080c04050610212c 63
    0x58080d45161011044254150b91110b00070400801d00c00c1c140502c01041481d2200070f4001c0b100f148180d100c046691845002d044d43e1652044040409190001a0055103075200000d50307400c40500d110341e0381c000043c40e10381980c1074100300c24400d030030556003032951a034500660000480c3c1003180c2c08407002c5566607141071a030fa5070259035450f4960007000614000c00c0c440c1c001c0078150340c002850107241c84450b2804000150240700c403524a0f980100c1080602800050508020902900c0150203034016540080a50049803180b20b419056440191880c2d160402a2454107034084c10099481c5488807404914106c165604400d035030928000035055803203129666485a244031409042608680d8240c0d40354204480100c501040002e0004224500303500f88400c59001c1c4c3c02504c40c035410024014101520700311801c8c040c0d400c0c6014050291285034111301d00c0d10342c5203006200180d28205550441c540c0307510283c62903051071041005018080d2040703c400b48018586165000504005 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 331049001 1250 331047751 331047781
    0xc04050103020604090213050604060903020405010803070b04080a110a0f0b090c01140c01090501180c0f15030f02190f09050103050c0a03020705030d09121101020306030703110a0f080a0209 83
    0x94002d003003408108440d402c5d80c1c002d02141807240492060b469220008120642c04c95405940007442c444410419030410348606409880c050b000345241030700030b890740b9140640140009054400010f80422054800d2800ca450140d0020689a100e41c00f8109003010408480b025900c000e01a404200d42c2c880000f54291200c5068450032002d0070100b0300c84003e80c1005200422a54031140c185000a00071321072004010010b1102880f40484c50508084c0c01c11981c0081c004c5080c0f1013400e00c000300a1b100d40071040045443c011a4403035000c0079120190048c03c050001c0400e02030f202e840c40e180c1110790a030452410340e0755004c0e481c3c0c1e0b0300011810b854055800000d10b0104100083e2418829002424107074010f404032172814880000450440300c0c541002d560500d90400004a0035500005151020711400025811401c00200107a140d80791440024454089018000781c0743d02c890700824001d020780740a0404190703807020015240c0c2c0c40000101d03c50f0900a001520106081d104 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 331050251 1250 331049001 331049003
    0x150102060a0b040b090406020409060f1410140c0615042901020708060f010503010606090302010e0d02271603021303030c02180c091305064c020c04050103 68
    0x202501c0d201c5055041c0207040d0602401d800039125841504107440d6042000d018070310034100141d07181d00c0d02034000100c0340d168100c000007c4450b0400c00c5102104010500448400c03110480d03100d01e502c4090742e0710803195801238100100442c00208420340802c0c0f00388500c40c110081c40580c0c861004010072125020000c206c442e243c42c800c808110300c944191031081e8018011a1080c5440e1145240380c088211100c140b40b501410040c0840c0c01c0031700030304005040c94244010b91a0540e40040e080c1e0440d40f21160160821044010955440140b11040410280e58141810350307403903020164003800300c480d0605005142003100300303640b20b817003190800d40b18020304100b02803d42c1c0e822910040c0180099074007040c0341c02e9040e180b145a50001c0e025586101c540d49e41d034422741b402c2c002086000b05030715451500d01300401916854207800900b94259421038a42082907040076400c003c800a1445d0040200300852110340640c440014581742c0b282e0740840e480908828104000c0d2102404 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 331051501 1250 331050251 331050253
    0x30c090609030b04080f122a030103061503120302040905061c02010804170d0b0306100305060c0c010e030301121401051302061810020705040c110703111c0c0905150102 74
    0x26041003c00d11010105070000c0c4201c480c0c605e4402400c00ea940690000252010046907030b038140b03c0b012031030484610710600902292502e0703c802d09001c4440d40414840030f8000ca4030303048540340e6042034840f40b102850780180380c0407200f949054000c00a401c540503801085240202050307182c0f074001d501c4c40c0150460b0445c0d071f0140209500445000001400c04c40e040c02110450540381e00458000d045100380d0040001070b1003036101c080500d0140040c0164105030000001071003c82d002092041d4003407007070b40f00c055845031201001401000c07195105070441c00003000128101940c2e40c1c405045602841862099075a4515511f00704e4000f81c4040319000d40300340c1054014100382010708400d19400e6054985d070504a800318481000711883c90740140c020071410302843c07616100741035400340c41c3c0c43d01d800020035400055030744000502002e0b042458182c040308031540d84141907010f905004100c00c00381211440c00c001c043d2010300500c0c40301c900b000c0000d0041ca036012609200369034164 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 331052751 1250 331051501 331051517
    0x190e03030403021c0c0e0a1a011211070503030408120711060f04060e060406090b22020d022709120c0c1201021b0307052104180213090c030c0906 64
    0xe820002d50b400500e08076680130000d40307410340100e02d021140070001c00c42040400c0452400d076454504441c03114000000040b140d000d0b260309645d112103100300070744114000260300c05150000503501c1c0101030009005100000821041210b01000780030090b0080700300420644544a00343c422041c51510124190712280020300c00005039a0095046406144001214100c1143c15428200d0894054078025111001d4408001c43d910b842640820465181c00c460941c0c100b00040180e55440064481d010207100305c415980c0300c0302c0c010700004458a202e039601031040401030052104079180090f6000b004048040c481003e01114006400880503010070032100c000c000b032103d1190280c3c1d42c81d43d42172103150000340100500b10198018103004640751206840e059103048145903c00700c0c20400d504000980d5400391040c1c40980e008ac0010780011035240ca0520003e001e440f203103550b084010312002504c080c142d849000715488664040c000341c6100302043d1080304151007000b0001e400d038 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 331054001 1250 331052751 331052753
    0x902040b150304060b0a05040c021b0108010b09040b1906020609160b04170a061a0a0f030201020606010809150c0301090f060501020d0f0203041203110f0a020609120c0a03030203190e03030403 84
    0x19403241e005c46800038014a40f04e44c079140844e045031742d100201e4015070b00c00484000c241072110040b154041c42460504082d605190038203520b4015910361074003c07900e0b010001c03220783e1020154803d030301d41441460003d55a80100958900d4160341411346030080d11001d94480d1005400c0e602541d400c07c0300145041d01d4181586d000a40b403a044d01a0343c0681d121950005006010b4022070f05043d0014041141c4043c0c10020103509550246582d04100b05082005076000704aa603841082400e11520995460031b6207420301d00301140c070054680740302080020444181c0041c6050f925a00e034100562079120780c0e00d0044070694068140540d020041a00c51144100c0c1c00755118080d40c810380c0c1c1495500d185080e104442d122040700400c50420000c10541030030010b00b0500407024008160580c3c450700032070742d14850543c015014182020703d1340c109040030003159901c00400761800b640d059607404c009480e42c03c805650b0704540c5910000d81032180c441c00d00c10400d1040100510300d800c1c83c1d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 331055251 1250 331054001 331054013
    0x40b040b09031b01020a03150509070305070504170a03032702090601140d05041703010b0715021204050a0221060f040302011401121703040305030f040201020c130902040b150304 78
    0x300910400c0c5501c000c2015124004000b0700000511401c4000940c9900c550036029064940c0074410704490b8a0050080285a5890003901d4001a0b981000500d41e116690100c8c0d04c2d1245800c50030f1800940c01e80c3c080302c250f0005584451034080d607002c001d0074080402d00b001c00e554070000540458280348003c800751501044c51504003405050070304070700b8420161030705c46400c8400c0820b0000e80d00c000300010b201140c4019220442c00442c014503541c14010001c10701d0040b844050801019101c20030306201305581260711a03811500041c00303c1c41c140c074100359100d00c690700c01c0b0302928100c800c0c03c2000c810003c001c41d003084190003802503a034424901c9815680010000d900710740d2542e0f841607003600401c80d03d50107050300e01341e01844027001c2c1c00e24a6184021001c0300446020410402c40401e501a00703903900a6014a4042e0076a1160300040b45008480e00856038088101603020802c076046502c4038210900c2a5001d1060080080412241c400d0381c450180310100308100040000311 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 331056501 1250 331055251 331055273
    0x90e0f06040b0a030f15020408030d1e1e0b0907210209180f010e06130e07030606120c0509010803070f061e0204030b130c1e0506030429040b04 63
    0x90301c005458141c6800040d85501907a00a640300c401440c14035061020703071481841001e90420b01503142c5890701e10483c4e568030031680c0c0c4c0d40c14070369a26040c0e0700d400815107a0340c00300d00402e0018081015041198100c8640710003030f5031030061510102065608245454521441417500c03003080040c054107002452000303043c09842c00b507030700700050710881d900c0d0201c00307a00344031440080c21540360004003410340d0201070b0024170f2182c05080810009654000141c1c0c54600c000e440800d800700c40d0404c00c0d02c1e05156402c020045803c1c00c00101e0744039954a0104440e130b00641254100e25134503014420455020300132601da0340c004000100209080710280100e030352058034001010118080300c404041140030b04a049640c00040c10814040c000c0351482e044180d003040650541e0a9550741c06420310a44a82c1c4032450180c40010040380881070400300038240a4480c681d00d01e041c1c5400b060040e880f00c04c580907070b140368808803180a060319020748220fa01540f0f401c000e88458880044046c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 331057751 1250 331056501 331056511
    0x1314042703030e03040303050307081f151e0e0319020a0303030e030f030a02070c090b030601092d0b030f070e0a020d0605040c090f05060903030304120c0804060806010f090e0f 77
    0x1501c4120203480210100005d10095010756106074490800301801400c0314009400b1003003803124030722812100d04001c83c0d82021203086201c859900e03854002c0c26a035483c021108100c2c0c58ac01820580c903c40d40005003d0750f590012800d40b5030a2240d0481d50700088006a4060340201441d9814000203000c0c2d4064400040d0701011070f800e00c0348026080340c071036100b29055041c0540204440c02001007119070200a4034400f4020320600342c8680200b5584c903014850310070313842c0d1246004030011065004c0820524041c04807005840c0c0282c00f40310140015502c4240a8800c60504640308140403400d401078640d1345103103050350340720001d001c4040c0d0000d40d1103101c00c903590341002410380d81e10311407205400900c6c2c46d01c0582c90316002c02002e1444d1154003060241c8802c10001c0502d80e0080b00b2268000d42c061060b40040d00b00880480b0302c560007550050158200041c0440d02c6500a0f681c1c5200e030350240d031800d00c22156600101d4480c0c800b8032503030082940c0100840c1c524084624619401 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 331059001 1250 331057751 331057757
    0x1501171311120303240616110405010b0a12020d06031a0a0e070627030f0b06040209030307060e0a020603010b0408060c090105040302061c0510030204060518040f0311031314042703 79
    0x40d8a1745000a1b40b60340c07041d608001c2018980f107040b07040054001031080f000380221010003082d890126850034a214011074001005030311003c46003802c0065050729990b1110203410804980c49103020192200200e02810078030b22840c00041030b101060040800044140e0082d09a061030180241c4080941c0422100300e4440355a90030449550b1900c5000158046e00005927102d03003070300b414150520301505284c0224010007407141151800004c079087c01d5403000000031b1b040d285030602c50900000d200020350156002000007048075411026206403030700d91342541c405407101140b01000348601001c0d54041790080c0030030400b5103420000340c424003034680403822848201120b140115541110580ea18440403002803041d41014468140078240c2601c40f14030500210380041d0003940018030041001d200d98400908041c464901c0d00c5414401c50100ca88403828440d500d040bc0080e03014202c0e55140c103401108492800d03004010102013081154120060b040304034041300322200d0303000e03014 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 331060251 1250 331059001 331059061
    0x150501050703050c101b1d06070501140112050601090b031f1503060e101509050403050d09080a1704020d031202041703090a050a0e1501171311120303 66
    0x184113820300c5000c6000440c190300044808a81c140014104090f100440400c04c01e14138001c40402032030101c2c0b00440003118003a4882010b8030f00301f03000d09000e01c406030800c07984070000150314080c9070840180d10b1140058504907a01c0b840b4000c1110000320100340c1c5588071710402c000f00c0304200d64408103541d02c0000131404103503901844040c03c0d003951040794402d548150076051603100703000342240400100c1003880107036014024848034010741d01400c5611035803013010030304142c003400444580f00d0781503100f4040c55025050410003034201400140c00b081c44410071f80c0d90203088806641c4500e5004151080b920b6243d00c0c2110f100078041844044940d003040f010800300601d01c0311003030f80140040210790301c0a407201480741c00303035050b44054002c40c00c030b020030701904076010180c40c0e000d24005243d400f150036580048400c00d4285000c03a481503440c4041c030200b140c2844510481500444443c072285e04040c0074400d40f0450300c241384819410034000b04007030300301e14074602c41410121410080 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 331061501 1250 331060251 331060267
    0xc072117030c07020d2f01080402210a11030c0103050c0a0309020a0807081f1118040b041103040201080106050a02030a1b0b0c04210804060f21020904050a15050105070305 75
    0x103190520b0440c02e507120114418941c0c0e10310442484c10303d48146c03a100d0603030f030b06104a001821000e00070700300901c101c003810107444004d5002d169150742281c4038011548008131509000e0307000000c81d48420f000340514041410344c1e500078000c0500410055007514509030700030504500400c0240c030103d0b4452401d0740d00250340442000f505020f011444090050001c41c4801e41400f80700002c103000380c003400c01c640c0000c503440ea2000c5d02e414100443c070114100000900040081c107000c4881640b16240c0851106503070b13212809140725501c03c1c0c0340c001d2240d0300c0744029681401030080c440c0c0141d1040012000603403040c1101d402c0801c829980561582032503a50341010312048607102503111011604021901140078407101554054004244114640c0c07522511449140108418004e425031448480d40c0b04690b240c40d00c0800d1500c9260341c994401c070070130213544040d080c1072080d81880d01040305203031a4498490b6060081c0d0803003060528190041d14550030000d401c3d0107124080c40042 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 331062751 1250 331061501 331061509
    0x201050f1f180f0e1902210d090806130206160c0902160b07050906030708060316090c020d05160f03020f03030f061003021804051008030c072117030c0702 68
    0x82c03a8048003000114901c00c85a800c00211456040c5000340c039800561000555031410b54000380f00c0360103840a151110a41901c549000b05030b0030000d103207100304800d0700440303540b060500040d5016442543d01613200d40d9044104005140c601079885681007103030392030311540a5000c0541c07a20070300310324003182c0d95032090100f240c0105059807158940725510408000b450746520340d01c9155810440d05040100c80450698000188588244425072002c00d506035010041600d100300c1000395100349948070818403015004101c407100161240107104545640110140d81341d0780c6a20603486241c075182d13206d5016421040d0f82c01d400398010104a0800c0b07841c1070001b944140c20494041d81f00b814030138103001c200c43e048100c41c1c080620520085414401c00c45030950540c070210b50200b419110b6a010503680c051581c40001d0074400014a440000400315100b4212074228020000c5002030f042001d8902c000c0070001440c0c3e00e9016201081c5128040182da007100345d100307480341002820340c045 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 331064001 1250 331062751 331062779
    0x30602030a0b0316060e064b0403050a021c08030406150e06010c0204090305091002070f060302070206030112080405042c07061403090312130606060201050f1f 70
    0x29401c840d120000e09407503007020880c3c1510184414810503483d854458010419004044000d116050014201603501c201c104655404005400100601000c2c01c8940c220600b5803201000342807412025008110781080130745048a40082c0036000e040081c0e802c004812038141140491050311102d040d02080c01030000d507100da8400d4000003130a0b0100942c28001c1c0c80e160b4000300741034245508000320399134042c050300c4100380c2c16071700070601074064a0700f9a0315004401815400c02c004008440320b444c4d000a080341141c44145003104019220708040701070344600000030f9000002000100280002c04070314641807405104a541019141c000003003d0b500640000c81c1250203601c00c180703022600380712404021480a00600a41d460180d0192141030300c8440500e0744c400103c00100c4803d0f080c02102c91248008601c024149030882d4101c240c500800c0058940a24041d004a15140148a024001c40300340c90414500d503602c1c0304040f03800030652a406120184000d0000c3c100c000c002e02 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 331065251 1250 331064001 331064011
    0x106061b03120f091b0b0301060912050c09070f0912080f0f1e03040510200912012d06030b0112020402090a030605060f1504061b050d0c030f0806091f03060203 70
    0x1100d2285c10100361210100200d500800c0d07016074200010000b007034000c4880c000721000f10600030543d200303a082039400c11010031400c03500035031120100130103564440c1c100340140126484044030281c036011503028128010900800c6801c2c20403201804403408009040c2c03001901400ca0301d88090b003116610100601c07050700c054654040b05005c00c1280a00010300340b0a50008104000d940607000c0204061800011096a43c0d00040341c850a498140000200c5055030001340149005060002107040800440b06801011640070000c44107003402010704580d00301c414144280d082115066031100d40800483c1e00590070004061646c81d45403082c0015801031500247c6490a90140f00003084450a5103100304107851920206070541010340301650200c2c0b0301400742090325882d0040181e2010070141191240c8244d4521843d03000031150700f51846a07840c000d4088200d001612094015191180d2042484000407900380c03420003141c22480300202e09000b5203540307442d00401c036407083d10 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 331066501 1250 331065251 331065263
    0xd050403030507030c02070b09010302130b04080111130504110702030d030b030c150301140d140c1302163206060f0d02090c0708090619020106061b03120f09 69
    0x8100500d5003601c182507010149007014019a142d202c002074480c40b560292800208001c101c000c0c0d0f507482507058504100707201001c02a290b440d0400f040d00e03a00076104441d525070a1201409040e081c0100b9a04204d1700340741e5400d08642480100b2001d0490000341e21354542c414080c600c0503036420410381801446a440004054607100145030812044600f03003802810a0303a0a01c0c0b007040d00c081100d0449040a04580b40f0300142c50010fa0000040d0314042d0a6810b1030440800354040070841180c040d00032501d00200d0f0311009502c0040e40036000c201c14500003094500c10214a0025800c03404055400b109a0303681c400581410080d091140c00b000107500003003c202041c20000c0f04030b0940002200c00c000000010b07030000b10508802081102c4500001c240801003240040a44a11003001400a42c0b500c00b030a1709642d69034010200f41c1d0041d800c02c00000b49003030080714811005041c0102c03107126040703039860030b443d016540a4140407441e0b441100a00c1115035210302d0402c0e5205032 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 331067751 1250 331066501 331066511
    0x340f030c030807181a09060c060a0f0605102304151206080c060a09080d08060906040c0246020114040b0a0c0501020d0c0905040609020c1002031b0d 65
    0x10074001c10441c801003a001c02c2c07002d800050b0305070380c1d007407009041203c500c8800683e0105110a40c41c81c140104048583c00000200b1454250b1001180c200d05c2886042000c06c1002c000e45010410f44486204290300103079100c1e90a502d29101e0b01011140892511190044030b401c20010001ca1740181d1040c5907040845522010045c1c0c8000ca00c02070040c80d21041c41098203008042e5103070040c0c01001440344038002110748856010f00c0121008080050903103034014a201400f9010b01c80458800b84070350310441c0090690301c1c0038410f82103500e1083d4002c111003104915800451184c81810702e1900800b455140c0e05141c0300d9189203104080d00d00600043d000610015103c004030344084507103640244414007260718000280c0f0426517142c038010070560480c0c100341e4024402d80b112494558200301e1960321080c0c00103452012038105884c1044419900da8503030080340660820108240c10244205a8651941e0055038224840c0080500401901880c00038560b001a41c4d5101450310340c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 331069001 1250 331067751 331067753
    0x50c0a0215090310023a020a05120117060103020103051e01142e0c030504080f0105150d080324090f040b0609040201081315020c071505340f030c 64
    0x502c5414415604c062080d81802c0e548000108600070f410f400c042c44540648443c03c3d590341e8800c031004500c0000100719034510160400034040e85c090801440082690000001d100340c211001c0301002c00400042c1045909640c01107016100103056000b401014103c0241071401d010a103034000c02080451304120401d880600c4014070b4a503010b00c032103d22104405245014000d0b0045144000c0d1800c910707405024502a1042d0103560840354540c80b40d2083c0314040700055025a0103030655001480d402c4007404100500d207000007500814071002440850120405040d20307035213002c515200400c45a1081c0702050711558102d0750190b10703198000504c02400700c140c00c100e42110043da1003000502d0f0580001e80210b5000e0a68041c0c0c00074003049500f80101100d0105a52818540a564038000380500c507540f01407030301940b4080d1000030300d46010036000d14100d5044a010040804241d07200062803840c01c2290525a0741d41c0c803000d2081e2000640c88101140940c0c0700340c650603010003103 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 331070251 1250 331069001 331069003
    0x1080105070c1a0403140c010506011103190e04060503030c210f09010f11060705040303080a0e07120309030203030f180301140a09020d0b0a14090a02060a050c0a02150903 75
    0x201514220078008214818004106624990403100070443c020200a490313925086601c10960a11035041c0700c808112030300182c5040d04441d00a00090f81c81030140305625400a841c3c4c0300d24012201d100083c02c814100a41c004c000c802100e0702c008100166040d500c0380402e0451303101040030070b0381c4e0304043e00c1c428000ea048010b0a0100288000c0b00d41081414005521381e4071560700d80505024403c05414013a610502420600113501d030243c03003031424515070142141e08207000071004503084400041580b2960701c2440007444100b00140100c9242009000d6000c5da441030a80400c00c1030040031000d40c070f04100030111103000c5040a980d95540071003c03042c00024202c1c180c071903418607103a41c40300340302d101800307801140d08000000e807202c4510018165400746007000b4031a051540400c14010619402044421500440d0000c1039982069013a260307008141c00a40c0041e0038001c481c20544210094441c0c14412421980c001410303400290118000c19103d4081600c005408552410 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 331071501 1250 331070251 331070261
    0x31b010204050114070201050a050f1303063215010212030c040312031b08090a0f060b010206090a03080f10081905010b0d0c090b060f030414010c05030c190210060e010801 75
    0xc20000704a040c9030031703036000038158464010210304001c400b0484d0346401184604503003c010032010b14403c5107603a45001e001414089541500441544250703009501175001c0030f034004c18880c84148103c0d0b80e00d220b100070364000100c446045208290700700540e1003030302000358012008048041c2c0c40318038514141a080c5114100001007508004007001c07413507000388502007a1000d5040030091540d038810203070b00c2d202e0070340f1018040440e00703880f180c207102c000e504c00700d85400f00303a0070b5400554400c40555a101d138680380060010300c00e07000181c405141044c00036040b50403240307030400b007030f682d082c0881c83d0203040819801c84e41c02841480c420080240700360b403400e06096500030a42c5e0701070303280e4441d0303459036119150585031501d8000c403455540030210b0303048a00343c20b09103883e400c0c2800d10034642c50003802c4962342586010f00d4018294003c000792440740e605805018600004140c0c0c6100c0056004000d90551007151608a01ca02943c06008043c0c10f41000004e51589803505042c20340e0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 331072751 1250 331071501 331071527
    0x3290103030201050f3102190906030611031e06130603080a18270e06130605090303040213090303111b06010b0406020717070e041101030f0507020c040905031b0102040501 75
    0x11100c2c440b1b03140122100000b0303005502c00714a158800b00140d00201d5000031501e2104800f030100b6a0010440903107640c040c00660703000c0e4008105141f00400c0c02483c500c415600b41c00d104120032501d1080d0f07100366902990208000c0c0208419181c0c400c060700c00d0740c00b01d400858a03400046580340d0341c664405e1104802110181e8003190562a0034075060f0349001d0848920380c41c402986501125005c2d035007001d801319944c10111025460030081d1038803200540c5001b100c8060074200418080c020010503a80101c1d0010006910402100d402000030208074104805041e180c0b40300304054960000540300c88140d160300710300c401c01c42d01d521500707020058021902e6000203200c18412a50300094400c01c0e20040149080380c0d40a40025525144041e0310510742061000200000c1040822842d18410b000381c90a101e101c0c3c2e080040c40039500201c89510042e4007003d103c02051420750402084d10b4000e9065030726186030100c609061842d101e0b03148190703a4000070301700565607004007070341540 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 331074001 1250 331072751 331072771
    0x405070e030f0106270603140303040302070608070f08041a040516091a04021308030d0f06140906210321090610090510080f0c0102240103290103030201050f 69
    0x2030a01004240301c180380c140005171090300b1910341e00c0e29070b00b951201015640044816020080034a0b01941d02c3d0b0045a0403030046c0150f00d4002145409030303d4090040415403038404003c0c242c44811140c4050050040d80d80d00c078403414604e204d200301401d89000d40d0050002d0a180224010030000c01d4629a0000c0005858482407071083d004600c40f44200d81c0b000c41703002d40e952100d035419818200b0560460201ca00000484d80420943c0f94084003100c4034580c0c040c0442a59404240b90090040304450381160081002071090700d81020007880c0001064800c119040700349201519603004400304c0c8a40c1d001810041c606c902ca0598810fa018840344000d022514111505034a007220901c13400300c6040d101d5003c1404601070b210114041c148640403201c18404250640740d940610a00c118007500605c4038191665001d02c81000200c03020240d101e602c2c4c1d00e5079444516641202c40d10003a840480741070a0a054503115000d4025802039002041c0790408030014a50400042d042d0904 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 331075251 1250 331074001 331074011
    0x114070206030627010e09010f0b01051801051c091a0103030c03080601020a39080304140418150c020604030c020108070e060406030c0206060a0608160e0405070e030f01 74
    0x1030741c1e11412203030b0040e4240d50404ca0440700c0312042c0d044811007041c0316090024200003141e0002442544c5200d000003a00034054803807103ca00c4011540c83c9801180002c0c0b0070041e2103004440d080c11849109010300d0668500806a010680030b416060038005034071352103241d440140a4011818081039220f001c20300581d501d19a0050010301e00020000d0511942500058440c2e00074072822079100e4004802c44004407140f16084809860040380c42c05210b10515101c01c8503100300420320942d103460005500d000c1c2440c030040d0401240101d07e81c0d0044d114880d180301a20300c2da0421401c01d1103451412803024100c00c0c28020360f000f9204150440d0f009a0401020070b5100000410160302801c000c3d84549494034110340481d140030704150230010000780003880300c1d0305030b0004021180aa003919402c0c3ca6040c1042102001031040300d00003520800442e5140002e2519078084241504100608500b04000304064803002c036040c0f80402d1500102c0d103160f060030301c116180c4075654002080 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 331076501 1250 331075251 331075253
    0x1a0907030201180807120503281209080d020c01020c011a01020d0f0e060a0e030a0804081e0d0806030a1e0204051312120207050703051b03071404020f190c02011407 72
    0x5d034074207503482941c054609401070365003448014021149031004502c62000302400503204283c1c1c201601c0030040001d00c2504c04a03070010701600c50003078816404280075180c09441550b10020303400005600d141d55608108010052009110b08040126840c0f46140d20b551201c00184c1410305450090062280d40800d40e130740246d0010f082c0381e48900852392942c990042c1181215811610300780b590b014841e145580701030003c0e00010340111074052003100c0c1403010054401c4000e074100700c05001694010302160401501030b0003107a43c000d00242c1112484d030704e651200c04025804a56202c0001500c00c03505040d81071a00030341e9840703001c080110074203a5542c5da8110544508081a1003000951545880c00300700a404490219400c10102d0f00080c0c1c507800c004d519881c4030091540b100000f10080c00e07040c140030035540304030b8059006500762006203205220284d07024404d410781a40c0704200380c8410740b10342d119041002655685103100002c26100140c402d81d10703803509041003101400100 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 331077751 1250 331076501 331076503
    0x18070917151608011e12060f0c0801090b0a03021c05010b03150916080a02150409060f0905060405090303040611040905010b0309010501080c0d0204091e210314010b071a09070302011808 81
    0x10304407061340b18005424082814641f009003840780640b00761909000c007030520294000300090582c0c1007098100602e1040c1420412751a01510009402085c5a10040c1c1f03000f40c4d019010040318012000801c540c4280c2c00003d06100b941068841d814030390009110310007500308201207000c0251046440301c141043c1d0125520303000302200a200380f441075400340540103104103950050400441c18001b864441020842002003401510360043c9800001042880c00c0d0066a0182404c0f4002e03501d10f444640383d0740d010340250000780503c11000c00000660100e0313031103180d0007041343c101e50310340303034201b8000060a5400c103a0100c4a24bc0c000c840f02700c40d07581e85080160300359034100d40026070b101c114a031101543c203a00340008132800405c00d582c018000d18048024000c0341c4080b103542215482c01064086540c000c031021505203280c00181300100c16480106240c5004000440716440044049102c5035000c654280c080d401c803140800455811800c00209c0c21080400c51604130b040a8101d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 331079001 1250 331077751 331077809
    0xe07080a05090c100507051002040303140c03040e0705071b060518150c1c03050108060402010f050706050403090f061d04020901170103030305061807091715160801 72
    0x2a0034100e9981001c524100020080c0c980c40c1e80c000740403d05140c22504014003e500011000e642a0080c2d0400550190180c800c40c2d065a07450b489003601c0151200108030a038000c0c80e501600b81c0300410003c01d00020035688244280c3c4c0d00d0361015618522890070362000003e69200309540184e18506104040d0000140c0d0010070085c1d00f02c0c0419082c10b0002503284600500e680003012001462205490380803c504400184d45c4810740011460950103c040360310274406c0345455040301000c5801507101d41c542004e07090061a069062035020385071041122000d0320110085081c4402c20400142644803120040400d428a040741450034461601c0c15081600d400d4440d603400a56040d25031b0040f409070045070fa00044220f49580c4034a03015008103001d0300c410707101c5c004400a82d8961142c6043c1c03544211507950394000003524010100040c0d140a040c0d45110740201942c0704100a95260200d1180c448000025030000540700083c1040700107070000400712203020044032158091403e0303 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 331080251 1250 331079001 331079011
    0x3153d0c05060a0b01020703140115080d090306090201090e09060103020109150c0209040212030d150902040605120c0c0115051009030b040311011e09020a0803090d030509040e030a020d090e0708 85
    0x400300d82c00780c4c0c04d00105e04004403904000d100e0003d00030801c1c85135005500c141c02c460b11304c010180425480388400c0e959200c4041078900041c40000042c80025650b41089601c144103050010060ba200c1002000c07201d011580b104e039550004004200f950380c01031089c4001d00800030240d02c07084040b0740c014a109140d0750007034050641c40c03012404640f917005624240c50707100b00c1601d8850819090b2000035017041c035540030000c1030142001c03c0c10846482214203c92894444516080100038180b1316407a00418080300700300140144084004d007801418124031701100a80a41800c2604000c007100051441d00d0030400c18010600004c4c0087c1e0420360002d0301070806004d030200c8012428003600032547c2c6213500003440c1909401341a040d802c0819128800c481541c0115116042190b40740030300c1102a130b01000000c00d800c0440c2c003039401008100d80240c40816030341c02d42d07100b20340f4680c080c00e894070050340074a44030241d00b640549400e000d40741590300300c00542070100c8003d08800b00600 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 331081501 1250 331080251 331080271
    0xa1a04030f050a060e0d02070501080105091609050a0909020307120b07050c0307050109202d030c1f080a0509030409020a031401060f020f06010b03153d0c0506 70
    0x9104081c4001000700c41a801d41c004e50034800d1641d2100c4590b244d44044407140058030484601054541c042c1c0f010b241030741c0d4080c1c1a01111b40c3e13403c0c80e20546a100c00201804e03c2847c11001c2604d031a403500312800f4080c14000410409694418140750200d5640700c1c00c2211ba000e468070700081c50034441c07a500440c083c54a25241c6040c031008c107095100e0107000401540c42c03c003c50082115085090003c44890304148080803140414050030003002c2e00c9600c03403c04002501d00714148940a040701d4440f001e0b00701d901c00745140703000c00c2d28940074001c003074802034207035900d002030903401407a850780004c0166061001e41403a5205994900883c000c60001035000b20705403601500ca43c1c070801190384600c0e0744040c20750391190082d00341d813504000070b030042c0640a4201060200011503904a03038651007554590351300d529001c0038444860941c4c80c0c0c071600120a0380258820900c050042881060704220194801c121409118203070300080e10910440d014400c01003a03000c0b521a0313105160750b03 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 331082751 1250 331081501 331081523
    0xc0316030b09030f070c03020a0905040c05040c0507020a030b1b070b01090209060d020307271a0306030319032406120509010608010e0102070c050a0b0a050c0312070e0a1a0403 77
    0x10580740d00354084c02c058401400c03004154901840f194219941c201c90098440c01c004a46411114041d640200c90141100819800c2040b41d4141640721400c1610203241460518030140d000494540c0b00307a10640740e83ca1a1010710017841920810903006150407011680791421a0f0f884030038043e4148556100c40364045142001c548502c0121341100c65150001c43d0340380b41c0190041c000300b2155203901031250340862004a13156180b01500300317036050504a4078044038841103501d01688024000ba03050300050100d50384991410580e00700c0080551070205041540328070304030344400700704294407901d802500c0400036913800040345817216011080108050f07413007240300c0e409028036600c070982e250311b07140c0015509041035000d024643c0c0310340140c44489a0b14410081d4103103050107103003c050420891107a00a009100800f0041600d0341924241040041c0c2102c4001e021103015000c02c9040440d40001c0c0751405031a0054013400700651f9081d600300101501d2030046000c0101200009 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 331084001 1250 331082751 331082761
    0x3100603050601120c02010510050108060f1e040c200d0504090b030a0503190e0d0203031605010b0916020d0207080309041112010f050a29250302030c0c0316030b 71
    0xd01d105491213001c050090180341e40858000340280740403105010440d000d6180130031f01d0f40c402e80e42036000710307401002003150b602c0c4d150401c41c64080f0600303007160089607600e14000c9a141c07401213400d0107070030741c541e00002118240482102c50b10f620840d5500c0d04203411f01854640c01106580c142e50b6032280006000c1484000b0034540400c0c09406410380c0b001040800c40c100c070401411142180683d5905210000d220510000c184411002989904148410281c0c01c0c02a60044071355400b9200214042003c800820054001550810a04040c017044094496010800c007403a41005200415545190a0704541c50f400b46030390b16807050345c5130301009100307280d00d10540e10344d03049180315501c45594500b09802c0c03511043c89503034015801e20340300048020321020f1551484032840861040d001d200c82d401703000780d406800014401d030482d401080000780e850300f0a40d0720f68070940007940e617039104106240c070701206140440d201c2e074271807a14142c51440280c1c3c41c10803240d02000c1007203d42c50b9 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 331085251 1250 331084001 331084007
    0x3020a050105010b04051002030c030a0e010903080f03040614090c0f0103020d02030c03040606050102120901120905011d1009051f0204120c0614280e180f0c03100603050601 76
    0x90904040c0656081500100d07051030990700500440700f04032940c9030702c2500324000380e84130f000d00500c400d0183c2050002108480c0500c0c500d2650060500d03000a40e903807a590340d00c3c600d822441130340c80ca0801c084104810401184034040b180030103108038491354944401842e07916803001d015280030341c140c40e25040c6581d0003501a680c01588110b019905c3e80360502c21360a60350400c4500f0341d5030300d042101c0002d8035400421018a0002d414420600e003140660054506800c04000c01c6590780d6940424404a5000e12a014802c2d0809080b2019640710522013860a81d03041c4146901c58135100603a00068400100d022a030810404071104540c041901a030003801590310081c4002050203851f030810242004010036100151540304041c002c040059030180076500c4600b12801d0389018140f600c07503124071011440045842c2107000200c4900100e4183c81480c40354010a5451605020058811b00541030340700c4140210b507400d601c1c08a0200c4049002445158149582d80011440030f0344 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 331086501 1250 331085251 331085263
    0x12050904090b0405060615030a1e060605030703061505040306050603190305031e06011d0409060f020903011a0d080a091203090608090a0804090b01050918010806130302190302 77
    0x4000d1003000110000d042568600340d04680854490140c000000d0541c50506401a080c0310f025403401c0c02c6903076090750400100340c02103190f90582c0c51200b040c0d07034640e45070013044040c20041d9203e5440b03040405001d0195085500300d140d0401417841c16080c0d0325800010750b400c9940200c00450180c441102207420120a80c25150448050150032418140c110005500440301d210008000803111918088016400d070340d414001202c00e600d84009010f000100810964000c0000550f1940742e6030b03982c11140701144888171180c02090766a903c0c07400384076030160224030003003200310023140c0300c001030b18444845001020f01d200891a00149846074200e24082c0c8075040614030b29401d503040c0548080540d1196100142980300045d000420124900c0b455a50010301c0604281c203040111001e05400c0010300e0401c8030a0280240654038440c0f002c05880344943c041086504002c04036051450092803140200310740120003001940c006160042e5030b400c0c0034103280040907442e0482c00c00e1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 331087751 1250 331086501 331086517
    0x723010908091f12150e010b041502060106021b130c0305100e01050f0d1403070302010b1002011407030f020c060a0605090105030d0c0b040c030807030905010912030207140312071a01211205 83
    0x94100d00201d90041c0305002401580c8ad600600742c95184840402c0ba43c401d024090711005810000f4204182c0c00b581e0341c0300a0703400e00104504006028423007040c080f101034800e840300003602c600c144100c0c02c8091072070601900000080300000e60410010034841c4007505c0215000300c0c8090403c0c8180810100c03d000c841395410b01b034a945c0d40c01c2d070800a0290103d80c40c02442904560f142420081c0148211200e80341c49262a080a0b80c3d003542c01d40040104030541d00000c1c1c0c0800800e1075200c41442424850202c0b003e0015200341000240000114140c11083c0207038400f05030040c803241c002075050041a03002040c0841e50380e0f6171a201840d4421503000403c10b6134042080c800f007540005008003035440aa950b460f0440e5242d0b07030044296494100580903821403007040c801c5041021507210210f801404442d55003202d0890400c06500c4804155120000c81c1c403901c00c42280764601c0d60040013483c644030300d140060014034851100801c030060104403c034109a810f1070040d0240c80c032803 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 331089001 1250 331087751 331087769
    0x30c1203110a0f0b060d052d0106030b1602060c032409070302030f0c030606090613030c230a050a05060c0703060e03120a0c050723010908091f1215 65
    0xb19910b40f90a120030f649a00046408803078040028980c3d017820f00d5000d6031190014028030f01d189801d01001d030010303100780700e10744400e0145d03003034440c007404c00d0003580025403061205599904c0c2885440d082e0040071124081150802020301080c0c580e1a02134940003224800320740a900728007008005079484042b07a45411100c0c00b010031070110340590285104010003000c581075076a41044000140c8012030300158884d505001d8011141851005040c1983c020078130a0461512a00c03455003100c000c0d4416030304440110503004081407200c0c0c9840ea0502c0030b0f03940546a43c02c1400107201c016950245a00034032000c150704242c04000c0040c64001c42c0c101c00100040c5c1c10b40d40704580c50b5441040c0d4a600300e8010030201d01d80001620945054032142d6860504048460b0384901d154020385d0502c40720015a85803d00404a0a20612000c00c2c4902401590352900b1003c0c0400e58078904e400315040321054000140303044e00201c0c06031a02c8030a500020380760840c1d030603a031030300c1910350000968 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 331090251 1250 331089001 331089013
    0x6030610140d0c0c051b010909090609050601140a21020904060f1b140301030b1305070e0708010303030b01080f0c0904060308040803040801050117070501140705010207110a050406030c120311 84
    0x10340d034004041d04d090074095802c3d1244a000c0049015071121408041400100180c1d400c1080726900d41c00180c6980c400c200c04941d20010744c50b138518110082e0043c0e04200d4003490200c06610b0814000402803a031a551140000c24100c0030025910341d20202030b0188000000040801c00749a01c9400c008000410420000e4140030391048041703100000312010a1608040c3c0c8020a403d4041d00c6c104e0303510810449d17495841161140010301540412500c038481d240002c1030103107811a207a0f1140c856a51041020343c950700b4002c05a500f560440f41c14407869000780b0101030150341125521499105140d03a480c0300c1c80c80441e00900c43d5601c0030b0315402000c2000300d60f00c1d0000c0010f0003101c603c03100a00c016600e40301044070f5607a800f03842c0b0400d070744032260400c21540180c5034130f681c41e201c1ca0f1841c0e0400400c2e4450b14260fa2056074215413036990603040781428075102c0803d2000d41010384d01000824150f690b00300440c46507014440554104410030020140f14800a00302e4170705107815110 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 331091501 1250 331090251 331090271
    0x150e0105160f020405070e0d060e0c03030307110c010801081b010e30010608030d0507020109020603090a03090b0309150903090d0c1811220f150e06030610140d 70
    0x3102408040c0124403507410701e8041528640b098004007c101c90042403503074820300c15910f12004045807444c09100d07005034a01c02e8465a4203102035031103441207460303030099402291034082c180085203218a05102c100401440307030780d10014240c4140e01034038074050f0000b1039250044e2400b52103044030756485000008404140e55440890102d20f114131884511036100504038182a580140681d903400d500a000002c4242410b070005a00309810b8000004c180c40b2079008a0159401240c00704084d030302000c2340303208040c0d00115543c01400440c91940c2103040c22600c25403501d90148084542e01010700210340003c0060085440421004040000c401c0b40c0d850220300d045d0b00c0d0300c80c01d400c07603c44244003103107003005024010800d0301c010706592070011140c010f09044a039446a883c000016800e02141c14200403508030041c05440841c100212141d5034014074241c40400024003911061081c0407881d00d40d50b40300c01c580041c1d801d00c981c4800c211000d6aa850090f5011040058200803400c2c03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 331092751 1250 331091501 331091513
    0x120114130b06040507020606090a0213030305071a0402090c0c010b130b030d0906020d081323071406160305070605010e060a0602010905070512010e01020715050907150e010516 77
    0xd442148511420000c03030b40d80c102000120340303003141c1e5000075030041000580d86290000f0101d1340103410300c0006040021031003403d0402043c0b60400c038080b9400040146c00d100c44500500c5024052801c0c038400c074a040d50206030b00c9100681144051b100c00f01e65040080f02c02c3d003000345a804090f0514031b94100402d040d8015103000403c1500030b004440d009271005120706401d1003654035075001040940000c0c5811140403a0041807500003090106e21040054042d815072400650b1800509c08551542040e00d41400030341e62009203646d00c0394241000741e0b1240c40a56049580090614071f1042881c1030907100fa02c54044000d00c41c0b480c050000c03c00c400b40a40c618021401661071252494032400217034220351248170054560703030054800b044246003980034513045243c600004200e900e01412a10709a0f0404001100c8800e102442c803900d1001a129045c0c0c0950b4140082941900d0032101002000500c01003404021861100758060390003001110320400811008400b070600c0c0f0f040c0701c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 331094001 1250 331092751 331092781
    0x63607180f0231150f0908030a020a1704061d0d0b01120605010504091110051e0c0c01031401030807030e090a05070807020102091c022107090f1a120114 67
    0x22100702503590940fa1120300b0310201d0740050b1142d60761520f28641c01104c0070b4805c09180f074510b03420411a564003084054080c0050310905034150010000d82d11a450540c3d00b138000a01459203800c01800108601540000101c144001080c10045400c0d580d8001c500c0c988005d603005004d024496000003900810448465680d501030703141007000344d89034401c200a03035250480113000c44000b500c0d007007140c5c074150580080c0c9111500f0003a2524100c080d958800c40f1401034580c00210003c1245807003000c0522038541c0c4207400f4641004500403203c6c400d0441003040c08050a401404100241018000c41d03000e0801e420043c840009031800001420103040f0484d51040002d1194011030410341c014000d83c0c140c13250040081d8007003401c0c000d44100c20308111809170790200012040200c1e05000c14001403c40381207402500c01681800c8504007594000e14010001c0c030701e418110099400780418900111a0072141c0c411420300ca03141c0d260140200303c5c3c5243c0e0145a00c81800346d9011880c080c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 331095251 1250 331094001 331094047
    0x5040602040e070c1a010e0f1302030f011a0a0605030412020a0c0b1809040506071b06020d0b18010f0b0d0e070602010606030f020909040609080408063607180f02 71
    0x95808000403a12140c1a03100138410078031f81c040380c203002c1010100b101c01c5807a840075822103490b8440c002c640003c0d00d00010300d80c05040c02e941d214820400210302a801005940c0242d07404001a4039000c80184107201c000c00140c000103040700c00c1e01003d4424042c010100307030004e03826a0740c0c90304c41c50064840ea0001201540c02001051080002d08044044510403a0002d015001d40d55903200c0c103503040025030223844004400c0c81d510000051440c4090645921007903400511000c0740003d2000c1041e00d4003016001c0d605a10040100d03445004060f81624a0030039400e403502821300c40c1c0805003801800e00b0b0064000d011011490a5055003c00c0440d20140d5041c40310318402c508800c120701c82d11407640d0f046624603000a0104100350030800b4401d102e4161b0390710709962002c2881c1800f0069a0107810030300b002071070b0340209103c0000300040c407103107a084000d0349001c1c181e1180d49500e0380c070543e00640ca4503420403c8181140c2e00c40c44007003003404420b40d500c00784110410010b070005a8 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 331096501 1250 331095251 331095263
    0x10030b010315180309030204020a140c0d020f0f031905092e090f03260a0503010503330604060b0406031e0e2107060c030213060305090c0405040602040e070c 69
    0x3081e2083d03e20001d80e50455107815860358200d0781e003583c00b40400303580007018400c1440f881d0041c3c000c1549941d0700805210443e10040c0800c0244614001d041031060300109000780c0c2f20401200e00c1c0c0c4008400c40b001c4a14995002d003d8810001c1e06031514054584851f0f032000c0c00b8080c0413116590042c0e1403860220324003041d40d9002c08a5800da0710a002c602980c070021001810904c002690341a0549070600700c003ca822040010304c01711070749540180d1603038000481c0840108090b040400c010040041e80c0b41001c42080e00d00310f254603440002c2c407441142002007102045690319594045000f400d8888070441d50703149c0791603000e4045e01200b0341501152900d07107081040184903118642c480302000001c1c1056003087c0355096184800c81e102c0c203180c0f0700108030800001d02c1a00c02c128012800da200540c440c5815041883c0c84000b6520040a250405040040c505d001244450014504680009a0b601ea80c00c0200c001e00454010540142c4070f901404880f5401001e60486070344140307 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 331097751 1250 331096501 331096511
    0x515090906040308060613030303020306040207120f031404110402030a0f0c03060501081303170718090b1201050c030703020c0f010e060108060a02040f1202010e130e12090f010810030b010315 84
    0x200c00d11403140300d02c01f0200708401c2d8000003440020310030b40013190030950080c0050b007000c003030f9115014203c820b005a02e01180d0180b02d66101c0541500850032815842000c071021ba2030a034035100150046064000d2103154004005170115040b9403109042195401c01046484d0005401800402c010b014440c041100540001d841d0606480c88810055065032200300010103240c0e010007848001e0009818040c101c6194400b0200e40100203006100c410070105001006000b44100b542c401c000b1503035640d05141c10011800080c10032283c0101d1903180050b500d6054000042c20141480c0c0c0c00c12071075080401401c0b084000180d2581a5241001034030125100c801600b0228800c920407465441c44c2040d041003503e540d02c40703101c1b0390350040c107040c114006a900002c2c100905800149802d950390901c00340c00000800034100c40c6003140b6591803030f2044020020340303e16004890b171410040640c0004003036012540d2940d00450784200700e8421540c40e8500303600c90074242c0c802541020b15207 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 331099001 1250 331097751 331097761
    0x90706031802100f02100504080307090518160c020301111801020303070e010e121c020c0d02030c1203070f030503040b060a15181707030204060b0f04090515090906040308 75
    0x20300c044030445a000344081d020003254941a0b0311280100702e83d04c298090170f03407940817124845c00340e58400c52040018a81d24075001c04003802d0401190405030007007900e0415100314a5130a0285c6801c10034502c000c60b650300d8050811141c850095600035019400c1148082041c4450740c044e00d100c400c51084002d82c1e2005c400120381d03a00049960800180729608401050350243c1035030b18450001402440d0441c0d282c03a2803e2510f02ca1420b1a1f59100e50304030252081d5038180840b520450b4100c8030180c071a01542c00082e40d41c40800389840c070070f951079010303404089000c00495000f10f9010010072100c0c00749041c082c0041d00200c40541b462202c04000801ca46806098a0241d4100030300c3d901703041540500442d047c00240300c02c8120900b200e2000710f00521000c0003540710065100060040c54194030510054403190383c0400e0003d2800d21101c920f41c442c2c40156015a007031003100041703940d00e10b0024000c601600e60510b0f0000b061100f40042c01c5004205030f48158001e032141c11168a030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 331100251 1250 331099001 331099031
    0xd1a0301140a050a020f1b010209100e1f0e120a0b100303090f0e040305070606030c0b04091a0a1203020a02040911040e06070e130b0303040e04050708031804050c070b09070603 77
    0x30301011052400b404108112490304c8001e80001c00704211f100040c200200c0706c0c0402c0f041d85a20780e120002c06c2e45201d80011600d003c9141c2091405099690507007241c0300600a007030340e1a641e94081c420f00f20500950313a48a0200041c0c081642c101c1240b0702282006004030a080e070480c041600016a820804078881039880c55213811200750600c100015a181c2e10105c41540101c1c10466a403615110000b0224001a940c00c1c0580b881100c050b50b079a1034003191008840d00e400c42040560070810b64a1010354902f02d10604440b048280e4007071084140c0307400c0741040308031103000f580b2526280c00e001c00e1012201d10740d040c04405071001c1004132032000c074203561350344100c0390000060102e182d24042c1c3d0070300c15040000201180310104d42c0c0d003003030f00c002401d40d04186c010791203c0b03210034100300500a04004840c0180f40c81800b0f107180036020b0420955005410300998004d503200c802203a159803000f4212070f880ca800280011081c107000d807242d40c442c2c0d054130800d00000d003082105800000c0f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 331101501 1250 331100251 331100257
    0x909090102040b0316180603050712150e04050321060a050418080c03040b040306090606050901181d031602130b060405040b0a031b0305070b0406050d1a0301140a050a02 74
    0x2402241960b940d0000c160384401112005e104000c4400c6080011004122010b006440d072501d0204803490039110042800703d0f04203445d0709460816105000010035403007604c05923444440b50b502c0c95525810610701d14401d1061058516101000040050611500c854041cbc941256650300c02c943d22270801003580c003001c4d0440b1600c440c01c40d0040001d5100401400444000345c01d403410141c1d2424902c1054000e070340300341d0303a8a844030145002c100d05031148030040c05003190080030315414052020f0480b00c020703942c44090740e82d5002c0610307808444981142c0741c110b0b900481360b07a81c86005d00d920800000340b204038021040e00211242c00c2501c1d004407414460040d140a00345850842004080c000004040307403c40d200d00d4000c004100746044520031003a40c804080d000307614500d0510300c2c1034074a610400d401101440305001840c4e00204550890035205e5020601681070031800103000c000200c40b940c150704c7e01c040036181010350800944941c0c005030f010000c9131307179400059090784 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 331102751 1250 331101501 331101509
    0xc0a12030905090f0f10080a030818030a140a0c140d02010f0c0c06090809030106030b180a030509010c061d01330302090a0b040203042f0604052211090909010204 71
    0xa0800001178030200b0201c9010b600c4a01c0f00740301c40340c0656801c507072800c1603c040405c0d00011810401c11030007245c2500e4880100f4404030080d03103410180c5000422070311084008451082c2c00084d01d244e5240b00d0b00001106903044a1051850000d05442964510410003080007550800031101c50f9828107100741e9072110400e465501080c8075580d0382c4e0008081c81003044401c14424844001a500e0900c101c4014621030813541096040441039091902c1894089950550054003d04000f80e07000050361014482800d0040e400d582606d045406000c2141d40382e403400503031140c1568034450540082003280301d02a117901e90041c101000000c03c6030404041c5140c1c0300c1e015010001400c1c19152150300524a0b40c002980e03030b1280c8002801d980c0196016282008944c0b03500351610140c00c0c140d100c802001036200540c45003d80441c0e030034003e5100d0f007880746a003181610152450500d0220365500b014604001d104c80055002d00103130447c40082c1c0c00740b0200000244680414802c5400303403 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 331104001 1250 331102751 331102771
    0x10f0c030e010614150408010501080a02011205010302030a021c060c030f0c02070806040311100c0c1a0f0f07020f0f030c010b01090305070e1302040218010206100e04020d050c0a1203090509 83
    0x541000014840d117104c4003048070060000402000134810000e114031400380000340c01600e54504d4900004041c1070300000040c42d1180307400010001aa00040c0212417503030b0603034103c4205903401280c4214030022100c081c10b01ca06254008401c141d2591040c5071a110900c07041288014051049980380041d010307200007a80050701150100e4056009490b441c55108100ea070100c08240941d0160340c0c02e806054003052a0031129420404016202410003080131130054180c6090007a16058210240c10000e4a445000c0411440e078401e0001a007022101400c54103d100002c2100d6a40e500500410005500c0d00c5a264070715071156044504494024008002843c105a0822003544020b0a0981403080c2c5560480060302c59002500281c1103810007410003c0348500013a003003160050612141c9a22804284041049500015041a01075864140c490030300e00d8002d1030042041d50a55100405410007d048081c4000e41c0902521998885008980c1c1c3d80501c058414180e44140c05 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 331105251 1250 331104001 331104029
    0xe0f07030206032505120a0c050316020c0a03031107090203040308070e0a1229070f050702040609021303120503071b0f06020f1209070506160311010f0c030e0106 71
    0x25181080c0559040f09181c02000c0c01c0c3d040c0d13480440809a1008183c001095010804844102d0350f5040c403070340200381c40000d0000284020004082d0721001700500700c907030702c2001d000100601c00c004446403900d01030b043c140110380340d040242080958484920040c0b01c1c400000c26211001d0081d81d0081e40e050f00c0302038581e100d040060392410030745c0f19202d410a0034400c0c0041c510314107000226a1a014072000303024182c1c1010303030008462150002031304805081c0184030703003980d0240a1859401c071030b02d0000d4903482c003480050003918990b84801c000d240046440d443d034000c210f1000701100d04c14040100310b0000c41005540c6400100c6542c008a00c1030001d180003520005840500c5074421070080030b82c8030700b40e43e0b4002241c00c592140358051902003400807142044403c02c0e90040342c45e00041c81001c4c58080007600c2441078042080c0184030b00803400082600030304e040d4010a00440083c05003c2490b003208004160b01c8100100090801e071141010f080103114081c00c1d2822400c00b280 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 331106501 1250 331105251 331105253
    0x5030c010518060307030504030210090203070b0703110a05030a0f08042f0909060105010e010e0d0303020c0f01020c010510062102090d05031216080702061603020408031207030e0f0703 81
    0x4454008011000c2c016100c860420020354a1000035480741115450015203410a420000c0c41d01d00c2c1d81d155108410706d403c80b1840941c1d000180c3e00102d8044080b240d9032a1060310301142c87d401c644014007036038031442e0885020040044003808a62449544400440032411000c4824620a07103000d00841252940c2d840e48000024040140c91101d0948a18a0401d007000c9209524200c40700c14158111030700600080d0390266480501240c01d02e00445151214800194940c54204005050560004081c3d2428209003c05664400300d40300840d02d0780d46244503240070748021500c1081101200801103a450700483d5800050030640124800c454105401030b4000d40c0014915944807104a005a0000354104002d00b0410700400f280031071401c0c20a2042c00944100d1036010030700c51132030b0801c110164001542c0c0e5115003d010610302c0300300211800e600a00c900e8008002d00d020010701810520b90048001d805602182c2e810130001042d1403171031740c0f12008001801c1080d000302c28100 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 331107751 1250 331106501 331106507
    0x12c13082b0905060106170a09050c0d03051c020429040b0c0f010501060c120f050d0c030e07080d0e0423040c030501051f031e0b0a0f110405030c01 65
    0x51500d003089600305403031400c01181d1081281e014200710a038507191050b0400400303104050040509041046204100c003000b655800c60007000b00f000550b98640910038080e04001c3c0401d0351340040c21000c00c100c02410001d1607a03008d188410001008881d0540c1c0c508500d200700d40444881203d010311000c0d4222240007030b95486529a0410941440042194981d0500800000d84108001c0c10030708e80140106c4d09542c1d050340000140440c4015041c003207804403035806040702880c502090304000007907054615020f10381c0301001032454280c8000545070160b112003000c6414604071003400d5518400f582e80d07a401000d000002501940e1428103900b0581c002c0d8078003d85001030413200700c00d900500502c02400703d506817200075410500b0803e04c4021b00c42c0541204e40070b109404800c1c8844a01c0c056800c0d9071200811100d503076100020020310340e002c0c001426502210000305810428140405480c558110028140ca00400440c0b49480c48003101c003181d41c094007800400800358015 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 331109001 1250 331107751 331107757
    0xb010207060c060e0f010203090a0b010506040506030408130801090303020d1b02101104031506032603010e0601030207230705031b0f13050403080709080c010804020909030c0105012c1308 82
    0x91130b0750b04c56940341080280c004c1c00a948140d40c40720040c02ca1054030705000340c4078541a8804c1d4000e0b00c04100c103000d252910030890b07511940101c2541c1e40c0b40000309041c0c00c205059400750059511380130b00c0608040e4181c00074440c00b6020b55041c80000001020700044e5008030800c0c0300503900c404030211015445412607041700001444c03441c00c040e80d80d2604120038449280b078050880d9515414810404c1d007000f14000541c1e01c40001c020030451801c5803207148018003075200752410850003d20300768801d8049406543c0d0003500402340160080135201ca0640704d803400c00d201e00a0f1301c4007284a040c00240b0760546103c58044822030507508042c4003071415400061500404242c0100380014100e005103030060340700340c0e6817080d0b500d80704100400044954110001c0e580040d6480b085a03a0700003c41d542164049440c6113031900c0303c1ca41e5a01d18441c4d064020a294281400016000b410090707003990001c144c1c140ca5026031b6102141c4052103000c540a205490000c0015070104140e000a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 331110251 1250 331109001 331109021
    0x25150618180b06181614040303050f092d040e1506041503050313050102160312080a0609060b03060f0d0201200a150b0f031f0e010207080a11010b010207060c06 70
    0x3c4013000041c5034a040f440f000483e5800028006664540c4a403640031641041c502c0344401214242402d40e03400034254428042c2d051503403a4085a8241240e440b0042c40c6000400320321103c0d0409800d03401d1070844540d409040d4880c9140c14800d41c000800070503c04148074424295881c40d82e629420040180f040d050103d80c20720300d220020001400400040c0090307143c40700101c041c13902d0322000a1910201c5080a100303000380360003c20002e1501414002401044d0804c50340303a954894500004207401e501141c501820400002429042c0708025400f90000b0b64600f0b080c581c190b0181700e03401400980090008211503070001058044c040345020021403401174401070950340c0c0f10981c10042e494503681d01c0c503a84058400d1303a8a49010204079454003a0007506001d00340540c0709110903001c3d40e03500d10254446c030420214604c29411144442e92040305580c5880c610b000c0242400900603040844c1d40ca4040303110b61b1580000350080480e8515038860004225650728203000c1c0c100700d24 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 331111501 1250 331110251 331110259
    0x6010905040e1504030c200a090f200c010b040204030f020d030c05070609080d020d0503060f04060b030f010611190210030f0c020610090b0625150618180b06 69
    0xc40107015100f00c1e40440d000e03034001da490325914503107401e18040401c20702603411940e03405042c00e4540740e00c55800a1003211703441d40001809146c030202071784c050800c414009510340840314103041c07001c40a0000c0d01c105406e5074000c01c01d4601038824071040b03203d980006003004c0400044200103150030800040028400c0ca0580107810359a66001d1511807160801000b1400340803050207040010040c10400600070300c0140705076407146001034030030720004d043c090049828410603081525681c11003402003603924540d40e907038034010703030400c40303052080c010640003d030030724200b43c0b80a100050040707142c40030305210f0030a8440c5900300504200a0340b940c00605071558000803c20250384250700001c2c2043c1c01a003807514104c110b100c00c2c801d0503001030120310b151000c00940d60701d03074406480b4414243c103001088403404403200360315a006844c004180d9140400c2e1301c12000d1207500300c83e00303d0340f807055140c076103490024215040c0e0f000e242d503821060141151b0032002c2000214030719085130b8068 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 331112751 1250 331111501 331111513
    0x19230c060d020a02070e0c0a08060102010506010914010e030f01020306040c05130501030207031106040501060608071112071a012309060d020d020406080a110f040e070902031005060a0309020901080606010905040e 93
    0x44aa030301407010888841f0044a00401ca003166240c02c00501640325209100030069440c10720000703801c04a043c00703005007900d40307004001c13000e9019010300010460020f01b1200c4841004200078080c1d80708846882c000c40c01c091102148501070416501c80003040e42c0d0071091241001c00440c0250481c0500342e040211070102d44004150600c0b00b640258007850000c0b03030103400d050002d044ca01d800740c071030400c001080c803295809171400b00c1c904c0c11220294480320342d03680103030924070031000601903c40d000c0314070308000103000107039141c1400d0b084040149814280010004000c020102121030039041402c142c4c1c1d000c0145005010240c2185c40200700042040e202c1c1149441e12490040458404200840340c0c01d8500d808480041c2c8507800322010720111a01010303094651241e4400c684401c0e4000c800b185001300c00c0c440b4800078080c00b03071403980c49005201c3c00402030081c400c41079010349400c1c0c0001c40d500d01c000c203050b80f0521068499002d803900d0407090200401240000d8416400b440c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 331114001 1250 331112751 331112759
    0x209040606020f150112260a081009051017070305250f0605070b042121060e0c1b0a080405190305060f04020319230c060d020a0207 58
    0x512900000d0019980100300508002c0c51051134141e0800720b40c500d10410000420a20a92003204c0c4100c40d0f100b07100901c3c0400c1d0300b01816480c001c0d440110b105074004148100401e600503070492007210a0116000701d555110403c0702140c1c82642d0908071401c910b0b600380910102d1030b09000c0040c4c3c3d03070003c85032840c0e503030b4403028144415202d0b031098100424408105004251503020050700380811042100c900d408406021072051013402064580b1000002c0d042c041543c28031203260510480c2c003144500071010080c0181c131001c0401c05014036120b060000c1c5419803242c0710076541c02c44d07800001910b84049402003500000340440f41d51002c6c0c0207a0441a2080c412108458810003804ad1618280010014039010500c00c0396a5424a50401c00214000040343c607040311004400543d503880b00c3c00883d003442194004a6500044c1601040400500003017601c07031030403100800b400e0300b000c0c03100e866101c20100307513402d034004810302280e894405c07194024080b000c8640111440c190b51 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 331115107 1106 331114001 331114009
    0xc0601050418060e0a1a06150309030d060b09031e0c01140d1805011802060f03150d1a1e0f09070801150f05010804031707030209 57
    0xc4000101d102003042c9010051039821800c1400b4211070492520b0b03032000c1c000e408460428401080502844a4945140c05041c00500d4081000840c00580c503568002914403429400100461403124078144501002001800101e5441d401d04100f01400c11902c01141001c1d84066483e81d00d01074408a0f10b40a250740908200000d03c80890710103500b401000c4805040758509180711003a0311680c010319120a20643c020300c84d2500501d81c0c507260011400d030081d0400d0040c8180f4240d40d6480d0050750388688241c00020750320140314000b4018000389001500c0500e81c041c121008101ca07181d40030351044000d00901e400c50580168000a450010120903c9180d400007040499030107104480080150000034018240e001804900070030340e501c03481460320842071000401d5401280380318403458068480c00fa11a1a860007040b030003600926090415500b04a00003107541c03 = true := by decide +kernel

theorem cover : BRFrame.Cov 330935251 331115107 := by
  have h0 := BRFrame.cov_init 330935251
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330935251 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 330935251 ≤ n) (h2 : n < 331115107) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
