-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4593
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:07:18.635977+00:00
-- url     : https://prove2.me/submissions/15461de2-e4ef-4bd0-90e2-102723bbf6af

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 825899280 ≤ n < 826079136 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 825900530 1250 825899280 825899293
    0x122508042f06190f1b0b070309021302030403030f060302030d0806030f0f0a0203010e0102090603010614070f051e0105060607140f0105100305070b03041a040311010e0c041d 76
    0x80c0301d2120407421030045031105080304031581c640000d2041d0300803108903075040e00500303460241c55044107096405a0b450f003410030340844203c0c1055480d4110807030203840d440980300403504041c000e51011400d60b4001d002c8084011108a07400302030b5000f51400c0380040d1500c60000706210785c034820340e02900c1d801406001d03001100c3e13104954551b03018211551601802425403103940b820803000312404401000780403040c210740100350850300c1c00440811240d0042081500b00d44d80d01b4100ca0642e030302420080c0200309000440f01c0f4034000c40000a1983d01001c20364014000000389466800b8047c60400100106184005003a9401910010741088003031092400040da00380da090014100e1004940b00d0500680d001403d40700203035003404050265010502c18040148041c1340500702c0b0204513499030070b0a0340c80345051070360024440c1c1044196008101054822258607100411070300090044aa1407190552a4110700441a1042c1e00c0c015659400c4c4e440c401c0c2030300c00c0508070b00c041d121 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 825901780 1250 825900530 825900563
    0x3120f031a04021e0c010b091f0b0307050f030c091f39120206070504061209030c0b0414070801050402031009140a030c110f030a030302090612250804 66
    0x39421040d0001100810060136002291034107014010141c14800042000e103c41d0080c4090250f0182071410720600c0e40750f82d261030107240c0c07164000301c4503044030350f942e240c0d00c5c42c004a034140140e401070b240103c0004244503403020705001621302c00c1d00469100012a881240c5020b52071a54480c40000ca02c0d030a07088a030b00c1c8034020343d04070381062030304031051103109240ca2140d844a40703040803581030190403211032074103904102d455400003141c01d000b0b18003030805c500905509942484183e011743c80c1c0943e8020544101d60320440359921034003110503400c00d031030310800100400c22080c50501c1060400543c513001406020b02864000d00645a03140c8600c0408015140e489015036241e041101403110241d000c000c40310a0314085e6540050701041894080040d0074800321080c1700d50070b808038072a5995004904210107a60505006031b684d40c2240c08105a8001c0c00f00300ca4008409a003008107141003c0c41845420b20036a11043c0034081194098420450580b4058030a0081c182d1440 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 825903030 1250 825901780 825901789
    0x903070608061909061d01120b070507080307120e07030c030b09030702030706080f070c12030c110d0e0f01050f16020604030819030605030c06071704090603120f031a 73
    0x290026006840c1a640b0040300c020b42c2c0401441d940600b1904d40d582c001002403010303030404000500c0355081c0d07480103075140070a185031848052034040c0004000c0800301705510f00920864550a40c041406a100d15021001500c5031101c41c610308941420303c41070818041c404501c1c00182c1c0da100414060841c11a00e540c10002c1004000c0005440b08000d40c0026940c100110300003801e160342ea01c081440e01d20725030310109034045c2c070341e20a2190402d204800130b0080d40d2843c003090036a00d00080c0e01c08050300110380d040100c4090384018080c1100310660a035029140965a00050352803911203444400111050b1044000c0c540e440c01c418880d01d00c1c104105007900c00c5a0340020080c1c0d0400c1e032281c031100100e5001040104101c1106900c041880790503000b18001004210098242d41c882c10011400600c11600028401d0014841034544069901d0541e4040e00c0156030410501e40c0f2031030207030400c400500701000442c0260300118021486802003101104840700b881466010701c0d001e11 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 825904280 1250 825903030 825903047
    0x203070b0c1504020a0b190e03030a050a030f091e0b09060622060b03150321030a0b04140c21010b070f0503071b090e06060d02010f270e06030309030706 67
    0x499100e2041c0301c1c00a1191b80540c05003008841c4142c0d80c02031812005800303400b5508d540750080c001c0d00300344850038a5981203000c2d180e054603d81804107154000c074401c2402020076290041400580600c0c0c1d041c03c441c07003c10401814890302100042e5200c0702810382d0382c0c0c0f1048a00c1648011a1316a00c3c40d420701400c070200b621401a00c021502079203980318003145030012214003440b411501700b15180c40c44c041080d240306130841c0038400c0c1c00c040100c0300d0004c28400148a0314005e13444d4500712070030b0340702c46d40081401999503421801d0707803c00040310400c56002c00f06242c00380a1086040014001e112051ba04940d0b51155051800040d9941d031203482c00001015a81c6002c2881008007091070301074075420b248544160307640c2d402e0a01c040c07035003220000858503480d6400a130412805440b001c0310344101c240c09003001d200103003441c1002c5840d1010407101c1545006013603920358214050180a4041c0c1d108841031881c0c2d07030703206028903560740101c01340241d06600c220317001c110040c010200d2 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 825905530 1250 825904280 825904283
    0xb0402040e06010e03120a0503190509060f0907030507090e240103030f1710090e0321150607050a03080f09100f02090d0804181b0f0315120203070b0c1504 68
    0x42d1b8641c038180080d81002600a0304030800070807000001c10044107010402000c00c81600c1c2d008000303909203004a02d030fa440004000c44014104d460200d0a026020003200000307590100403181c40e0b584500415015002c0e01984c2221807150310b103914600080103081d00c2c850b103210240d0300c805038a582c41c221840c10200000380148041580c1141e02c40885a50300c0d0b12650104d0201c0c024280b80ca40c11004070781c403402c12400fa682052210050008200034841c40c015102c072942c0015850b407088001c203106840e0031780c990101e00005e000040090108007580c1d0035009444140159807001607044100700101c441c0d42007a084440e0110600d042c907403110313109180c9200018208040031000c104211b0861000340d400000c080750030050340c01a44d80e01c403e4041c1c160400c0c050110203246098022003944009401e0040d06880e081d003c0f0300c2544016514040610035082c0c495031851303d00b154482d2508240d020340540100402c0000e01442201c0902c607140e0010309403404003a5460b03c004d20003520 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 825906780 1250 825905530 825905533
    0x60903030c0906070b07050c0d110a030e18130b160c021c0b011d060a051539010c0f0e0d020a08010608030c100c05030c0d09020918010b0402040e06010e03 68
    0x101000f107000c01750402e12502440c1c0300e4640c3c51a850007070a141c900102c03220b404005c90503030a4412400d0108802c040c03150305040884900461038002540c103d2030307440b0030b100c9026003010800c102001a580408450003101c00c01e1540e102d1002c044160615076208901003011401000018200601101240b405a0340041300c401060341d181f00036418203902a070b50030810307401400210307410009450f4100b0004c555440540303143c1008281b03000f500001542c082040071602091007a8206256061441042d514520002d6418514090040280c0c0440595844c0403410403140d8011212204040c3c09a11100d4060084c02c0410100c0d003081c9070308a8016606020001d100d4400b4000d81000d07001080c05580c585c084c000700343e40740081da0440d0300c408c6424504265223079908442240e8106008511041d902c48240c1c2c0d402c0050720700e0200081d0448480c2c02000301c0c011918100c810b100008000a00c445100ca100300420707405940039200201c250000400c07010360180f03081040c071794800340 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 825908030 1250 825906780 825906787
    0x1d01080c0702120d02010c09030f060e100f0c090b07020906240313060c090f030b0a0b06130609061403060607111309050c0105042d0807061709060903030c0906 70
    0x502040000c0c4411806510310740c4030303416228403e1707028018a80d0b802c0c4245042401e19283d070b01c61011003089071102404180c1d4034880421058800d00c41e04189500a0805020a9003070316244001810349014000004138914004104100328104841c0381c1034009104103410303251a410001d20210812114103455a0ac549410381c12408001451056802c81815070051040d41002d005955001d811030080040034181408108107507420b44090b0794214459969130340e13032041103400a01c0c40c0f00c50309034054008162005444481014481514a07595410707040d542d80d00b80c140c8080c0910300700c40c080da0005000082640c00c0c0903000c1c18070f0354005d00700100300705c2c00d043c00303d41201901790070070350600e40780c00400090000800c0030011084007840d110340b0345480d00030010500016001400da00c2e03201120440002000018107401500d10441990701b07056540d130000d000007100c0740f114680307003c0701000103403040c4000c84c4007486142c1c0140038602e9640c2c1d92030004104d90000100076032154050 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 825909280 1250 825908030 825908033
    0x40b06130303050d0c0c0302060f0618240301051009090816080c01140402101817101109030606130f1d1b1c0204092a061d01080c07 58
    0x40d4000086000e911203d0b50703128550004010303a485551103905200c0d10040780c0380003950014640f82d1040c0008420f03e203940314440003a41c0700c0c40902003032a20300010002e11a4405202d03140c2644141c4060044210110708818582610403c690328524404000300822451919070040d00b80240b207612450b2a01c4c001c80300c1544000d424000940c0d0850000c10700d140c051109100b030040c035030504030380d0402510b440d90000b076809900301103800400c1582206543c0d61039082740e1800203040140400e140346800c01031030a949011158a0441783d5041a403801a426039100031100001005409131107156a590b040c0400000e030702d4a480207555443c441e00d212070301e1511505449010f20800d0400900c0c103044030515000e101d00543c00322841409010480d83d440da4030b0540c0d403620310400288401c41c46e000040c000c5c01c8081c0060448100d082440c908003981d00080303108002414a8a40e40725100c0b041203480c0882641103082010400101d4007480d800342c3c4000b41e20000b1b08010601d080f029 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 825910530 1250 825909280 825909307
    0x603012a05130306060e0903070f022e1214090703030f1e02061608160f0e12070501020708060c0405010509040e16090b04090f0605070c0c08030a02011506020c040b06 73
    0x3950f0040e034540e0b540b40d000b40821000115910f400c000020300440c1401580d13110704110382c42420009220ba110801030900c203148200070707400c1518011980180003150302c1030180c80c20f0540702030b44650700c0ca0042400002c0c08004046400341c4840e40090a03418215039043c1c8061000b1030410040c0030440c07043e80c0c1c004030030800e89442e800850f80544001c2c102044031003000c2c0114031100050101050822002301c5241030000011061481c1c80841c4645003882906c0b1000421141d64101c00441c08045d00c105000031024229542039003114005940e400c11140c0300c2000780c650980555040004200961044014115680d07004000080d401c8005800d5458110710002040b00c20410349010080e11507648a507100d04007040d50140405206503451440040c0350801c024112940c88010800062003071061140300e03a4004801c880071034850a81e02e90340c1d04422250130041d801c4c02c9150050510780e0300c1c100126403135600280700c4c10401c01c0030807015041070b010042d0040740c18000740e018090f8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 825911780 1250 825910530 825910567
    0x16030c0b01090218040519091106180a0510082404060e0f0702011e020f070212060f0a0603110f01020a06020a0903140708150c070804060f080603012a05 67
    0x300800181d0b9013111002210150404212040c4281c0c41c0100300882038041105884030070508800000d100c0d520341c82d00090412a01c9800c1da00018007041c11085140c9089080100340720031601060a107543d0002c0009800b01c09a440000803010ba01060036048070303820312582c00c3c001e04c40a0403000a41000b00d821202c1d181d000c10702c0b041980e001d000302c0c21012007426401001170b00c004e000060244e030281900d088403285129600c0e41c001f4180c03010310000802e0714038880e03005003840d540700380e0034411954405090310f90042851182020a000700400d200707800880c1d0f0f00142200b0101d0b96801000b40d1000490303c0030741580141c4031300100141c0c181c401840d0780d0302161551325481e803c604041c0795410400c00684150b0344444410b010341100040ea0790300c0d01030f50000003038003691040c071b44511501a4040c0240311620100e4007040441d0084441815142c4540c0d918000f561000308050984121081e06010000d07181e103219840304070426040c05509079400c0080c039003540407014290429 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 825913030 1250 825911780 825911789
    0x40309180b0111070b0301060e030a060e0307020112090c0306110c01060609060e15190507050a0b0604140f010509060301180b18030c03040b180d030e09060d030516030c0b01 76
    0x195649034609003980c10081d841e114400032401000c41508085d1140d95521041c000c01d0248044000030750440e644c10028002000e500007020302a1203203660403150b494128000481c041081c040074488c42a94503c00c00c403515030006800041030b4910b449500042c42403581c18236002208101e0451100002d01a0b0401041a0799604810b00d1400c0e0000b0310302813460f040039101310610b650275030b409003e0a0540b05c081c0013907403100000d072500399800e440c41e21806900400c24000c4031900300c14040341e0780019200b188240c1d410b00050301e400c030543c6212a01240c50317440c1405680300610407400c10042e40707640070f10301400005120903928411f0110031000b00d003c80d008a03041d420015031000790390443c642d2241c2a0021414030701295169900c1b40224040c07440c02040114400410483c501041d0074144005400322003401b05034200205408018604030340944104000320324142403a10903810743c546c0503920241807960031400030300c0e05a15100c054041182c90030248010500044141e4001d0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 825914280 1250 825913030 825913079
    0x18140406052d12150907030b010305010501060311120f0a020d09080714030c1f33050109080705091314060f010f0303050f0c0708160501020606030303070c0803040309 73
    0xb45800c840c001c03049030400c036a450050f580801c103850b064100003080302e001c0d41d5140940c0350542e200c0c46868540340c503560010344a050300c0c00001091000c10b500143c141c0305070b07030b40601000b01c01040a40987c401e07a82c80c6c0c00203908203000146809102c0200641050342840058540402c05452100b40c1d991403509580c0e202d0f0000e0300c1030800c04141d5a411032007400d80080c1d03041c003284040e0710343c944112219039891841c46903407406441841358401e8080d03108080e13400d00620462075081224602680094010b810801c00200e000d6010f10301500884000d0307001498241e0804003440040c401c0603040a0005c0b00444080c00020450404502986080300040981e8a441054000300c0a81a070008a840388036640c03d00120354031100b02c030410020351014560310120f0301051072610b2181e0340030305502d0065410054403000b0034101001219030907801c40360140c40c0c040c101526448181c502d00d0200f00c1501c20f010029640801a642c458001d0400d92801540e92031081e048010350624050007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 825915530 1250 825914280 825914329
    0x81c1206090e280b220f0c060e181f0e1e01090e030304020405150909060613060506031b1c020d060b070506041b0302032a011814040605 60
    0x281d00c07442e00b80c03a00c00c9020f181e180048400d0b164180c0101c400b418000489500e0b04a2036002d000c03c4813a00340c61640301a01d0440c07030041d4103141102061502691002a41480302000c0078585600b1320007110f103c00d404510281c8401c55150340d1010483c010400c0321206280c000360b41c010b0320554a200d403050b052880180700741200d50300000c104c16008080b083d85000803000c1c140800001356035016030f06980026490301e403a00c1101d8074605a03030b00d0a50004010041240564000c02e9003809102c06540c407069001da00702401c0c040d41e12134011b2035003100c03007070002902c0d56480340c242c030482c441030303004251130b00e0894000c5131b10414090152189091b000580210308950500c540380c02052074996040c00c0a078560b8440f620f0f0203014002414040032012805680c11040740c5000046900508070380d8200381000790b490101c0d03040700c002800c0b0402c0f40144c02d16540a00c00c1290042052900c2c2e4140d0303810f0000440e600441142a9604595104004500743d101e6942c0c16014107540d00c100c000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 825916780 1250 825915530 825915553
    0xb0409060e0903120a1112090705011d0d02090c040b0d09031404031a0c130e04020907020c0901060503090c04050705070c2148081c1206090e 62
    0x500a8081c0c00300406074000c01c268460048104135268224070341c0100800c8414140c2d09000e00390140248440c18846c0040c1402030784000022804101c40c020b0701c9101d03a01e22410780a280000070400000c1c0c010206022810040c9000d00e201540020b00c2c68030181419102c107030320206a089505811070281c1e4803081841416040a0619004000f044003140b070141143d48001c00c03840502045c1090a210802141500c40720b8410745e00b0300e4400c0701c04124425a00d000b4180b41d5038040e50240e00503401d420200d816603102155450742030b003028021103a140d00e024411501940300400d09002402003c40e48040e5035240e00420380960b000e5079a80d41c4840903420581e185500540c0041006a2940031340c114108000708800c000a401090b40701810130740c41145ca0461100c0010740d0700000c14402030584907042d250000641c14175950005924135250742126680c0e0f070066070308104910240c0258484184140f0514011144903400805d401d40c3d900c8065041c2e03002010f070b9110350b4028001148 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 825918030 1250 825916780 825916799
    0x510081b1503130c0509191e0c0c0c05030f06070804060b10120f1505010c051009080316050a020c0402180a15030c0c110d05031606020409060e0610030c02070b040906 73
    0x10003030a41101c10801b03604100b441001010187c0181c0000c080d1541c48158007280314004a48411207211814080c8105646c0c0c010003961035414202c9070900c04140c0401d007400c0009410040e08104d5005107015102c464065070040c2000300200c900c2600e03401000043d4564070310b031080149050b00c488160b00f06140304a025200c0c8684240c0c426031902c405c1076201410110000e044620a080208015000d81006400c003611001e000c208603040020300c1081200f508020f5124000c0000401c40c40e01d0305a40440f00e84c4a641d241c200184d21140240781c040c03405600a129000c60680d0920005820202140b0750040a0f4060040a95a110700301001501070054680c120024a4400c8150510341d4840c2223001e55464605e001e410403505050800c80d04008849000c0c500c0c1184820075015403801c00e01030b42c098026031010702d08003680021042c0d02605980d018450040c010502218801001c6000b8104145810218803c040d40000d401050340d00a101030308810002282e0300b4204807121 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 825919280 1250 825918030 825918053
    0x30c080403020a02120a140d021608030f030c040503010c0e0f0111030d0f140903070c320303160506100b07150b030a06020a030509010510081b150313 66
    0x4050010100030032001a40c0441d03070b82d0030b10390b0448100680d0585004090319005003400e004182d011030114840700900002950820303071070b05a003140c845004144180020010f640b080c00e2140d8410b0001190202420006d0340c0c0c0540a9003220b0f060903500c100103400e44105080350750203d030000c660b950545c04c10401500c90030703e007030800440820103009420740d244694103507480c1c42035640c2c0800200f241d054200c49480707a8040309082c005c0c204030441e240c40740c1c050002240c0c8101500310000e8a08021030400d105c01c800d070328000702040b07949041c0c1c040b00c5a005070b40301c1e8135000401030303064000340006c060314402d4011740003040c26280c05641580680c40715003108112200078000b01c00041c188140280b18100e140d803010800410740000300b454802c0500d002400701d4000304980740440e515600c0701d803180c0c400c05d0080c050350700d40140205005041d0f005070100c40c0c1091005402c00e070780c0707034a4110f01d0b4800548054105220f070b21070503d058005403606d500c1c0c0301c042c1c1000014080301282c1c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 825920530 1250 825919280 825919301
    0x3050307032403030309020d060c0f081b25060f270503030705390c01091a1c05090c01110c01020304090b03030c0106060522030209060d02060c0a06020a03 68
    0x10350500d881d82d030345a600b00a218803005003016143d98108003151904c40c400342d0300350b9100c101400284400c50300a406040000103150008890b5030029169800d2800c0201250030400c02c2c45140c80f0f640402c41150480151540c1c0240c440002c94a0010f6064840c2c1d60080741ca6000014000f001191802050300f0300c0044102070f030004030100000320300b02000700c0e80c0003236282c200640c1d90003d50b01207206006000320b064041c040001001c02c3c05100c804500032041c0480c0d400e54601c04094401964040c180e401400d00741030940541d4030760a64048024010044400340c1320142a0350200c1101c180d0703104585c0d0030480c0c0c1104110b035000c0c0d40c01c04003039410046204060b0001c1c41e69200001d44da4007840c03240c03031140c50300c0e0b01c01c184503620148103c41c030490300d400090000540b1810094999401001c55011010301c0e0f600e9801190500c100380310907280d000f0710000154a410341000301e0f0b01c181c803105980c01300c000c0215241c07005041002d8819039118500242e140c85212030042e0440e5044144c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 825921780 1250 825920530 825920561
    0x50d1e0509010f020c0705120708100b0424090f1103090c03010e03031306050403090314060105030c271b0703030c08100506192615030d0207150e0d0305030703 70
    0x110724205000820b0f20821f940b82650f04e0901c14080222032031508043d684900b155000d10342c54044002d450f82c0040c25880d5041d1000e10040c280e410300c06010700e00002f10703030809103007e40c0f00340b09125561f008607140c44800f510129060040090104060380165079007140350703114a0b5100302504085c0101020140c00030003840c00e501e401650200d42c0000c074040200900e42c3ca00000d8101401150503002540d0801901019541100c02207507483c042802414400e11842010000904e42080740306408030100031024000005030540c5d898813400500700320510f8104521138982e40344100044d0006a0095501003101c1940c2000074190100c05403507400c1c02420745000380300d41d45601086a10340044400740d040311881c904e034200c130014130024501c00828400481c11200c0e1807a488a503001d400c0c4682000e101802c6282059915090400d00c0b01c05608803803800c0208289400800d50703c140d1600302810602004000603084801e19401140440c10200a224182d039142c410001c51040104 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 825923030 1250 825921780 825921787
    0x4050a02030c1903110f03060306100614030a090816060606030c05040b030a150b04080708010c0e09150423240f13060e041a0115050d1e0509010f02 65
    0x10200046200e07041c1085407a041a50f441c8400c10720960101210020210685031a9107502141c54429403040d200203200b0700c41c03c0b020070004241402941c0440c0d1a54030b6201ca00ba02d00803d020494100402000307106030344070000c50204841000402c0350140c02c0b0003400c04040c161400314100c0b501500610101480d0202104001c1e0700b00080701c00762a44020159100c2e51282a980c1c060003581048241907007500303600080c0f16000001a00644204074140e500302622030b0092802c81c0c007000300390400582c01600c0400e02d07082950381550090034075103203040085020408102a00c0c6001c603108481c0501805006030403201e00e101c1030304000c05e100b402211044104069505070543e50034584660403000083c0d9940e614118009101c1d0103081041c00b003107a94050001036000212004c3c0c94000c0a00303555440c03080c420300194182c81c000c581d4021150f001c0a401c4903d6000f0b2900003560503901c1003034101c4d40040f5a200000058807460208003480d104014600790380b2a0310304800500d0042c0f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 825924280 1250 825923030 825923041
    0x106090903090807060806011d03010617251202010903051207060b06070309032d0c030b0c030c0a0804081c06080c060408031c1d0705190501050a03150f1404050a0203 73
    0x441b00d0b0750040024640414007480f03502e007443d800039000c80010303032641ca0000006120150ba0206840364045001a0f9030301421000100400800c0c0307002580010a400c6001c5c4881075080c0c410040f4180185404c00c0203d460356201c038508000c100c41401109001704ac403d040021600420f41d0800055408605000b95a034014180d1030540c08010704142c506a11102e8118500d00d20f034041001c0e10030107002c004000c0c14030500341c0c0514003085da10305240c000019020b843d84030849002d0044614542d141000599003281c0e885006401120440c40422180c03c02c003203551504000620046000075000d46050f4500f890701415101d40c030b0052030240010048140003200b41e800301d07040c2c07210300b80d806c4940c40c4100c1c00401188040746c400d000320308180001e0005c00210f030303c299501514622100e01c00b0001a1454164902c44d581c00104100305845041e0301c240c00460345002004d40003041c0d5030315009408072104954012011880034000c045d20070b480c09004040c2c001071880c2c030071480c50410303 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 825925530 1250 825924280 825924287
    0x190c05070f0228080d0203040f0e07020304030602070b090705041a040515090117060907050604060f0e03030c0f060f060102060612071505040617060109090b060c010609090309080706 80
    0x48000203082072018404003415901c801d41a890240c02e01c28a0341107071902d031003481e01d0802d0305000b83e0040e4030960703c0b030790900c6000000300c0e8240c2d0054a01e1448252400100c130b220b54170300900d54402c50105100010000c0e10b1390000d020b80c24841d5060101a1a120203220700c0c106080e484a031045041000d0b0401c0e0010380302c0c81401015003500c02040c540c3d9000045c900c03244442a029401901030000000c4204200c802c40c410b400c007142c03d841a5444694005a5807291802410303403120041100300000f50142501c0d0000c1040740c1050607094060600280c1180c21030001401c5a4200d46040341601c10188002030303000d008441c1920503414141c000030750f90350340107100f50b0003220100e5000359801010003038240100004030220101e511000030041058100b441401c1c00f19000115090400038400e48040c07085c0c0044c0c2d40c1a410342e240c004810041c02d6110074613a0070500030416000e540700c0a001d48005481d0301c9001080d18802464020844403a07640720420b2504814030070b01c00680e0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 825926780 1250 825925530 825925537
    0xc0f120313021804050708241504090606031113060b09010e13050106031a0402071a071202070b151e0915030607020a0524040f030903050307060203190c05 68
    0x203001507481018480c4086540c0b11070721a0b800070190b618408000400c4000102d00d01511240415070700d0490440c1070340203010019070000d0500c00303110400038111211a051070140c9940042000c0303009959030f1103203002c554030b80d0001e44145d0140c003460312250038903034040c4214580c171180c200902880d26400141034065105503030304210241d040200d19568014a40000302d0a41c82c0400032540e5481e0058001c00c02040107a810070040c455040312442d0610a80304003d41040c1140c481150400713030045404c1d00140700d48180080d02c440ca5111610900c00703461058860160f0308081d0074882100e0f154401c01c440c42e00d00c01c41030403504003c01d041c0150306c1203481000b6110f00404e80c940440c19402c40c404500d000e60544100801c0016050b8002401c2c003100c0d015400791442c252890b590030070900248401107070540c03000d2000c680000d00403004805414020328001c1852034a0703550722400c42d440b4520681d10350360044140418038a8802012001034520801040401c541003805802c0d0b01 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 825928030 1250 825926780 825926791
    0x60d0c082a0d02131823040212030c07060201050105090105040213031502070602070303020a03110a0e012111180901061205041704080d090f0f0b0c010e01110c0f1203 73
    0x1d070202d0505080115501640c0c0030448a51000c081182c03500800b202c4016a0050106050705007018456074140c83d013984040662100c2c0d04040e143d407280c0a025404030a0001103203103200401103500351403c00d02c02c220182c0141e0b03001048551405041214100042c1c04c0340d4421441041000388049114007003c08413603120042d444c040740c45603103420081c0248074026081c13900020f0000c04040d1725600509800c0016181089600e0101251100900800034ae80020900200740f41c1507a42c019200725541380841d03000026101d41300415641038500707800741400e03144404101010114449104036408940c20345051100350300d0020003c0841c14803100e0300300b0050380c0e5800b150510400800307946407085c800030905d0766180d4580b80c044d40c4072a07852501d40005c44450001c030746105510305880481d00c8207529001c070315081428280d0795600c05940001d4540d61804000c03810030b002c2c0034150035410754803c82070b01c2d450890303410703801d096007001d400625800207085a0340000400c42940d4108 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 825929280 1250 825928030 825928111
    0xd090503120405030a170915030a0c0801030203210d020a080708010608040c1202030a1a0105040609020c06010b0a1704030c12050319020a03020f0d200705030f0703090302060d0c08 79
    0x10746801c10706c9400c0c0c4103103585140c108007408204129a03849000860207007008000070000924640000c6446610a020081d4950404080350f8001e00b0303c0ca02c05200c00360941e0b00c40d8034081d00f11f01400c0480c0d0000c0600300c0400c40d11030422155941041c1402e0040559050528447c40c00c0d59680f89080c0c0d481c0100391035002d00c10808410f64404001c1403450035071042029040002ea040c91400201d000d10515108500b400404560840b5078025950748001d1140100026420918165034940103a0ba00c2400c1018005220207003900070405507001d14029250040c81345424100120a01d900500001c00d00c1410004d1140e0f0b1800006000c4c012164107800580710010b10008501900c200b580a040302d40700803816803412603241c1e00a04446221140321800701181446e0b0741c01318040c8540c007401c580c0082c0b00c4a410700b840c050003814a9486032500e84040c070317204c0c1e0000d0002d410413207149146980d0745411000c0d658225992540000543c0700c0040f00240494114404094a25442016 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 825930530 1250 825929280 825929303
    0x5060c0c150c060702062a0d0f09020604030f0b0f04050a03140408070803040906140918010f05090606030d08011419080316050d03050601050d0e0f0d090503120405030a 74
    0x840d0890801c0d25004844141958a04d04201200075652441624034410300100b03ca402e5401300c1c00900c1c070f60143c1c3c00e003007407190400c0321408400c0010050798000300c4610352140f008000590380d8030028005144608010114a03205080c05880004c0007000d9401246606003840045280020008001030307061070003049154019840075000e020345d501000e0340f0f01c0350640c041086030000c400f5100382c442e11501005003035550540e5002c4904410754594000802d0000315162002070669501c40b000d2800000c12910801501907085070000c80c1d946104d50410b8042c0400340c42c040c00510300c1c4141c0c51078509403039414501c00c03004c0d03601c00740b0b121842440000001102c400c20308204000504406081d0303520354428002805080307592007401c03a024040c00fa9200a5680203114841c020403043e5102c6090501c01030760034005101c5851090700700e1050003041c0018100811140c9404103065540c00030f124541020b142c81d10800300c03290319241c3d405000c01d02203030700c001441c0c00a007900a14500ca4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 825931780 1250 825930530 825930559
    0xc030a031701050105210702151302090a1b08150a0308040e0928050a1a040b09011103070f0c02030a080405040b01030504080a1808060f0103030806041b050306030c0d0b010f05060c0c 80
    0xb4040d00d509c819812208210200100812888000740e0f04034002c0c0c641d95040e540304481d680c215006103d85080d0072200300258181c4612900752030f81e024050141c500040011032000500c01d9109501c1281c1c05080054140b20070681e0801043c1c01c400a00300600c2e001c0002d50425202d40a45009140c01c03422220040007446410071207041d5a9030814550007441031816103043e44001c0469090300c403006503d01089001e4414802c400c2d041040240311421516190000c446041000c200041004050100000541d4080c419035410a10034084c1545d00c034940400c1c0010399a10880341030525280c80c081101140600f000ca41400e0000e181590704000d00346107400580304590000c0c4014800c6a0030005440100c814440c140c0780030761139003c26035440a0400003503541096290700258402401035200e070340140090340e0071540081c152001c900384400451421001c010b000e4800142000040103204841d140c400007801081c1e441c0703403510f0440e00c1844d07074a055140c100f03401100404040c41 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 825933030 1250 825931780 825931783
    0x1206011a130b0306040e06070c0f0311010203090109140703030207031103070b160b0a0504030f0f2001090606060323070507060e0c120d0f030209030c030a031701050105210702 77
    0xc84507401c102600c411152107024405968200701c03549401949030240ca00c44504001440a1141200383c2d5009034200c0741d5500e211803065502412000c3c0041c980403100c03103103000e002440c8134080b00c8000148000107414080d8050b01c02c8600c0784031a130880c00003403001c00e501064030b20560303811181c43c5041c0001d070346c0030914082e242c4d80115042c01000c9403011b65200700c1c1c01c02c1d00b107581c01400c00404035205c81190034100e5209690041c0820001070180d45c0c681d0181c01c140494058904125a00000e0b0030f00144003440b9030010a0700c280d644041c035404024039440f500303001e880946404c01110000d6541e0780702022070503510000001450340041c1e4500c0c460b0f412240c800d5402903060000d45009296642e071107104150080c03150440a214440d03e21000271500d4040074640d9171503a900c6405034068000f5800220b4168050048843d180442d4800b0442c00380850701c255111a500004120f003113a5100d030607045a0304014082110f019070031100c07986906d0503514010515056201d00304240d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 825934280 1250 825933030 825933037
    0x30414180f04060b030c010e01210518071d040201200d0804060b04110d02070f0209041202070f03080a0f182408060a09090227151206011a 61
    0x1850440d0418100140ca090102045010390310a907802d004c1d655200e000c1545406180d0443c0380021805a04242107601c240c04a016030703601260204014100340104c3d40a40314116a0490352480055040c4412601048280c0c01006c180c803008443c03504c511144021b520f07010384042e04001e000022210008600042d200202500034211000283d004402420b0190116010340740e082c030f48414900e40d42003d000d6010305000d0709031070307a10742060f90200078001d400150040d102d600e4400d190000580340c4c510601c2c080c6014440c036805038010f81200030700c2c0000d1b50b04000c0140f00c8810081001440003c241c40c2e060009081003014103040c0c0204550000b015181030381500020300000401505004000003801403608454031035102240081c0e0f54000d082e110349800c0715442004000120190b444100c081d480140501254017007940c1c1d04584855901c807050840e000c0c101440414503851850a85200741a280c0e115001d0380e20310f51649034641442070310310005800c01d150103482c5c1450102c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 825935530 1250 825934280 825934309
    0x120412140f03040f1d131401020706050a0504120f021c030e0313060f0203070b0a05090a05120a1704150e0c0a0803121b03070507291501090602030414 66
    0x1140c0d100c40d910011100304540705e10981041a4071040c1007208009150b42040c45241d402d0400c0c841e42180f607650554007100061404015542842084001641401601c0c0a41c400342408299420107082104000254440a0040c0f10781201c800410a802103200403010b01154507010f58180b1446c0f080c1e000c1e00c0510703851003081c0000241d546c6066428440d0710291a07155031303101c01041107617501388d9503031142100141c002e003501d9000502c1d8540039003015520194050590b5150112541c2310b5242003181c22503450f43d00700100302d03406281d0b40021014100c2441c0e0000c01440c3c20180c44446c1c5200c1074010f40c0e04c0c01d03519002c0d82e4050f040c08101211081902030303e00e104060340c5032a455103d4200c43c4804810043c0034011503a40300c0140d080503861480561800d10707580b940d88098400c0c1d40800780c1160401c2441080710b0700603041a160141400b200070b038140b6a860300055205020130907640c01c905024110500f0b200c1c1030750000036182901c810159a5000d01940070029900241c050380 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 825936780 1250 825935530 825935533
    0x4150e100c1808030a09090213090e0f1f0c0206160c140f01060f0801020c0705100c0c0b04090c1106061011010e15010f15030f022a120412140f 63
    0xd00150f82c440000013072050092075610300d4075403078564031042c0592080315030024076030038800424800742845911004c0d54500c0641164407602002486078103010300f144071041c0d07103004101c0c0e003880070700315000c0e0b8406100c030351001d4219807070805151111404031030f880354208444040c4040402c69490b003086006044202118072040100d80314a020302021700484003414603550000030240414001e850002d40b40b0000b40c0419414101480a100c5405580100308510648028045180760f4040c5000d0a0a401415600c0e03041c058018103441c80200003100304540c60200407007043d40410496045541110855030304105501d0480c0c03901c04555142d8915468000184003600d40091205802d00c50142440926a6200d206411248151050042403c0810784503e00341c1e00c603a0002c05000440800141013281449610340b401d9003140030358201c0005403008440060040080711507560212901c0d5140905001441d555550310210040019028030101d403413040007404111400c000540 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 825938030 1250 825936780 825936827
    0x1206080703141f0c110a0803010306090c1212030e190204020c0f0114090d0c0521190c0209061219230606150408190201031104090504150e100c 63
    0xf0000741400960400440e400c01e2245141d0b0b8000f241c59800f160708051400e0030750f0320b0343c0c07100c034040d0800243c2251008290000821903418841c009400b0302c0c041c8000d000c260740010005003c58481840f4041c880e440b0a44160300d030048445000c20460b81542c0145e140c80e40c1f0000c45140c0460280314039915420403112015694150348058810a07040040b030b2500031105009484071044014098401d8000855810788044007100702c9003004e031101e440754039048506503490b402c000e100c221384d0005410f000f508015881d0281d41160095401c55075030414903400400965a00249640d81c02d8001e4907100c0541888a00008400a03000080950406404203120651207510841d0101d100754119048240346041600654098275080d000030301c45024014900c0d900c5400c1c04504904040e141c50b001404181e0f0240640001c01d01e100000c41d55041c0f510b0501030780f8070010f05640419250003010340c4050800502c666402d00e403604002901240d5003005c540240c8070751b451110051000e07 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 825939280 1250 825938030 825938083
    0x30902041e091a0c0703050309070e09010e0105070806130b0f090c0a02010c08071209051e070801060506070f032303010e0a05101412100c020a03120608070314 70
    0x2500504000d0740f18400c00720044041c4648000311800c103640c82070150b03c0511080d00040d01503402160002c1c004407ca44402d90750700d0064052850448000003141d464540022003070509010f0260049410b00782045076113000d5000c40e0380c1d4950440b00c3c8164039216401440c55031291149034103000c5000e81011441e15200040401d998000c0d114040158603220510400911842b00117000e25107580c0d6415400c82d40020000c041d1400c04002c1d85c4500400a02d1003c20311403500b9040101e1001015040880c5008030041c2110300300d60000340900010404000082e80070004080f40d164141803800100003045000702903072042640d03104a41100000108140000c451182d11840c8580c6d001c0c0629a07402552149003c1c2a11a0407401150102c2000481c0341c0000c41403041030043c412900c0c40e84584000c001a0b90008088001581101e5440024182c3c840d940036070b602600d075028070071540392038400c1e81d0340d10f82c0d40300c090051000c0b04680340082c81e0600034114150303000380305404440b03011f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 825940530 1250 825939280 825939341
    0x90216020306130b0a050613090b16020c03030a0f0c060e1006060507122114040b06100906051c0e0106061e05090d0204092103060b0306030d03090204 66
    0x266405038800e109030300c00aa4400090800c5030f00d110f41c043e031048a19100c54015034080d15001d0b01460703000c0450307c1043c041c40024820344000038001c06482d05c0e9420154644101c1221032403050013150403403400342d00d050b1000022180c54410f07900d4900000420354200f2500c0d2800c401004007201e040000c001001c0c903001944103003030002c4003820801280e8a10040c3e0300c1c0d10600034002c000100a05000c410f0038080c04034420020214204080c503c030030300c00200100d40d07a02c800341c5c80d912020414401804421a0126404841903c0748003c00140c0f18000e420000310703101d40c90801c07400083e507403421118210040c0000341160420b01c00c0c01c0500d90040c0c0a086c0ca40034207400286446c101000410740b9280b210444101d90300c45a1a0180800a200011300c6840007a6045510707104203000007840e2207049142078016070705800070800c04200040640e2020b5104410b007c0003407050004070b40c0c0c08280981c2c501c413103040000e411401031010501801d507030000c40316100e404e044400809940b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 825941780 1250 825940530 825940567
    0xc0d060c0e0604120339050105070c050a061e02190f0e01120f18081209010501060f08130c090609110f072307062d140d060902 56
    0x101d440d8151205000c0702440007602591045035281c107500c0b10074a004c0b90080c41504501c0c00b4140c0c2c40421506206000e0804204220201050750107907440b4605000081c032442c0c1d0000358500e07004d14000800d4903616614446141d0103002c25030ba940300001e5090011340b0008410950800654444861318196407040c80c010b880a03001c038080d1401c0c13205042c8249511560300b10140c4610305540001d0304070310000c10a41e0f0019045556032015036403602507450b0100c0c0a640300303200d1165508d41c070991180b01e401024103032080070307070400005000c0c0c1504001404001207141c85c11900695400744410754a40d24400060030658a04c0303000b0901c80425003101040d43e040b4803091000e41428956401144220b01060101c80c1d4140072100020b007522140e103079060342c9494014030a01041c441c840c204142a4000d80203d002840135402c21a03440301e051100c41114a050500d00405410141841c3d00d91104259030a000142c80001c1d0b17541607020001a06000b20210348410300c1a406041984 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 825943030 1250 825941780 825941801
    0x60a06050f030f0303011406040f09022208120304082217030304082a0115030b01080f07140103141303030e1603110402070f0308010905010f140609030c0d06 69
    0x8400811078010340c01c00083c00380c40d05400030001c41c91a81b131b10203a4020a141c5491841d4480000c000006400b4800ca1000f0081c0036220f000682c2e4010080c1402c1c83c81001d0303100d031480320400050410501031f0104000c00440078807615240d45c3e50702c80c601341080d0f1091036401707a01601d644820824601c2c8907200c85059031171a038018078a83e4640950f6981d00d0100b110f0041501a0030041040502d90340e81c0703100e100c11441d445091508988101c41829941c1285e0041d0310000c0e003e40030418130500014050051003040f01038041c60400b1a04c840d00c4a00714001d03400a80b21543d01d000b11a440381d8440f0302e0340c850b450031084072070074805041400c01c1c075108419800242049043e0481c1400890000030a11600c00c1c0071188600c0c503512101342d215502d07031003a8455424000000800d403c04c3d060090640719940c2c0c2c103015030403c0440c1c01141c0060700004640c01a0301c03404d0010488440da02c200c00e110031511640c0f1002d2640002c1d00d05064241ca207608030030200b04081c20447c1d1a00705d80b1180 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 825944280 1250 825943030 825943039
    0x60902030411090109020702060403200d081305040b010e0405070e040906090213060e011a041a131505070803041518060b150306101404060f0e040c0e1002030408060a0605 75
    0x69983d17451a030300741d028288002e0342c4003408200410018896154081410020585803401d100149000901c040780d0524107951203a400164540c0b2180a540010054101140e041000946080c0000e0039490100700c81800340d5910008524580e00442101c0a8044018010700902d42e0519041000e820640801c901840790b00f01000d07141d020314043d6000b43c0c2d0703c216540520781c2c41c0c00e90030300c130105074440500b525400422001c548440c007042c1d00e09020348100d200a5490f500504080c07807004050b8080205500302d02840149180e02204490355190407080c441c4d181c0d102c42c01d000b010022100c4000b054613280ca107011240124600144180901803034041108100b22800d000000c81c00319810b2400210800020308589403090361102e14080500e4100b003a0a00302200c4a0300d9801500080003203072240d64100c0e4030503448800000c80101c1990144809031101c80b0140c550001c810189114a121720310141d41c0e00c3c402c1007581d00400e00c86081741d451b4102499181d00400d91070141e079016 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 825945530 1250 825944280 825944299
    0x80d0b1215060904020f01052511010809060c0d0b06130609170a0b0601080405031918060203041a0903031c06050f03010b22140f16080c0403030c06060902030411 71
    0xc1d25200c00b1042c8113980140010f00c00e40c132898011141c680c090500780d403240c09010745007542e00503800c44030245a403184d10200510005040050081d001c01401161158407910811840940e100180c5030345034000400400d500d00741c400090500d000e052001440f4240c0741d03d0004029034000c0a10b4102c0d2001c5a200c00c1c903040082a480d20341c0e015000103010f02c680500404c000f07520404400e980580900180c904201c086200e0705c21440501c0303603410014910b03600c04d0010580101d000c100a0003180002d510303261403c6008825410082c0c040750139010302140d45071441d2402e00c100c07000303500411a07400e41c0d1201d0343c2542005006500405010740b0070480e480d0018101442801400100149a06c2f41a80c0340c120003600b48046190003540c0b41d44891100705100c07448100300d801101100c25800052900c80d1610015001003840c61042105990038030850340e0201d01110281c0b905481c0c0309000b4003460030110040d241e1a4440307003180744000204003e020355a0002960351008075840490f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 825946780 1250 825945530 825945541
    0x503031210230108040602040b0a030c0e0103020c062e060302040f0b030108030714161706060108070903060e01060f0b0c210d020705011407050a1416080d0b1215 71
    0x400384440e2542c020240400c456003803198004c070040c0360700c540b10712070140c0703091b4036900d0a008030b403c02c059100c08291540c1e500314905401c11490a490b02c0d080c6011414502c01d02c4100f07a0350031003d4048061070200100541455890700031140c0c0c1c040788103200c9100241d0b10840103009502038032031551990380b10304010502c0c080b194122812112500011070400d149600c40408200301120b0140941c404e201d4010000e00800346060014207007004020101121074a0444c28000000c05a60411000c5020829111b401950040907240c20400c0098003140c3c0800d0369004110342d80007002110008000000e030306074044010409603002c007050398070314000900307200060401e0a401e0403000d90305009551507010340741d001c0c00002c0e0040b0000316100d030319400010030b10601030340c40c0d00001d0300002c0e248000c40d4006001c5411020520340b400e140558161200c80080d0220303030004e140c290000b03a40110b541c2c050f0008204284020004914504444186552401c60b00b002501054898000a5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 825948030 1250 825946780 825946799
    0x70311010504060e0103020307030f0608030d050f060a030803150301140915091002160209010b0403050708030301061704111801060905010507021305072a20030c040b0a0503031210 79
    0x101152681d40b19132520100100065001c0c0d003005003080c003010794411141060542c0d50040070000c20790301c00a55991840003500106681000304001c01580f001d074284003803a11040c1868044a800c902c0054580d100d22151801070340c0c2e02c0806503030540c20817805014100501c2c80b080d00800e244012640d01110401c40c00c000c401080316050b020b5040f150000c0c2e180a0b090b001800344e5034604466594000460b400a070b030001003a000030080c007102240600c1000030420a40000e04a050019401c66241c004020715094048618004161030400031404014502c3c00e03003092980020600325800108902800c0c00010074401d00e0009050000300090650060341105c402c00d401400e1081024542c43e81400500b4014000c0c50402074051045401c031041d00c480c82c03a0400c8417041c81d0501c6c1d846428100366141920100801f0500c0c002c250350895600062810350070302c02134401141180c1204001800150140d1080b40c05020001d090400070310743c0007000f0300c030f2a1181c0010700e0090b103400c41907 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 825949280 1250 825948030 825948037
    0x503090405180c210f030c070509131719120c030c0c0f11030d020d0e041109150d1104031e080d0b0a0b07061e1a010c05010e0304080703110105 63
    0x81d2070980089842c04404c1c107000400180101e2060040000d03030b4544c041c90703850700300410032201050b0004508003948280501c03000740140000c844107241801c10604905103c201164000c2120361006800721034058880e0590724031520854811700400d9500c0005441e0241000402081500e03215207030942c179002303101d0011a403440b0f5640c58058042c0c0d940d02086261400e40c00c0d191081c0e002d410007803036601007003101008659071b4041c0c04101618039002c0c0c1910040300742c0038403e500f4504040c200b40c4040d81600d01030708048812405000d4a442c140711248150740c1401102403c181440c01804104002070085078402c9030405215a01903e103024003a0300c08a004010380e104010805030050a50401805108000c1040c1c540a80d0b800b950340140d0b2290f207045990340d464040140014418841c3c03440040034014080c000c41c42031900760b0b000d1200c0034032242d0601c01521012414000c2c25440301003070b240a00c040f070b55500c1c3c407081e03456560800f9110440e01c0b400c16805212055102d60182c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 825950530 1250 825949280 825949321
    0x90f15050c04080c010507060b0a0f080f06190b040608060a0b150702060a050a031413051606021e03040e041b080f06011413110301090b0402040b0d090213090503090405 74
    0x4e020250b4400004490741c1d1f01034001a140b03a900e07814030011315a51407903418000c0c8003069001d0026031820440c1c41c102511a03000310541d030000c20801c140307030300d004491a000352800741001500d00d4442c030016004109a030404107043c03240c3ca00700001074000c1c1d442000d40c000c08403001e00c1c011401c41c00401444c03007003540081d0400c1c001e111600003140144003500c10703c0030a00300480e1500428030404080181265443c00761242c03010710205101e81440f20030603445501e266081420304202d03019541c3c2c1c40140c1e0640040040c0c2c03141c610301410610a40307000d00202c1c83c0b05112410b05041001440110a0782c000c05111344a00000303807403900243d0340ba941550b0201401060b0300e00320304501000070b4250b4072600203005459000800a00d07104144000070964590380d205d506002c42c400441d0f00d00c258140c040d510400090111801c80c00686a01840c00100841c42751010710101e0700307109010090404c043d0070080c000080080120142c0847c080641d0100700658444034010361041d59140d5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 825951780 1250 825950530 825950533
    0x6010308040b072306160c0201020a080f0f070812090601300609150501080a02060301092007030207141512041712040c0608010621090f15050c0408 65
    0x204000100d1101d014011460091a100f42a00880400d800c0b8011385031481c0780003508200c0401c4540c0921900e0f04160080501d0210400c10701c5900203507030b944401c04090511b08000c11310000e810038200868000300401402c040e101c00042c54950300b25007000d042e0005120f40d80000401c04e101c0020640c1c100c03856000c0d5000014041030244008001400c072a03d083c158032848440403501d5406114202c902c91700c03440b000c141a00038102c044500603003002d0b201790002003900000d60784240c143c1e0b05603002d48000045440c0b80720104c0a42050080e0310045100010594500313040d00807405d8400c03580c050314240e44128031a41000440441c10342d0710071090030207200aa0344090300b20951940700744540700c00d0814513882880c2080d10340092030823849244080d0208000c108440b20020010110760610b252954141280548242030312030701c43c22400380418801c3c0d94113809404c5416056000b1241500801b02c6046c2006604104104841038070304110100e0072110118040310102c4e0714150 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 825953030 1250 825951780 825951787
    0x100608160302251a070f120218030f031206040209100302131703090a1a03011215060b0904200301121506090b1c1211160803091206010308 61
    0x4040e4000e401c035010f02c2004014802d68110544460320155850f140103456040850704401240f180001c0010084000c001c0e0340e9002c190080c5d00905813050345290702c21b01603101c0741c100360005540d0741c0e0b24500f61741c0743c404c61b5540b040005e404401000c03000660001800c4584c1c03907005100036480340c889c0c100e0300318460341540c1100303920035030140c05d140c61001c0041420381d0b912040410210740d0680c0d2041c4982000407404d140346814a505002483c10b41c00152004000030704164a5000520801c1071040602c020281042140e2030444400c4203120410000c0b29101e0f008640250428000c044c0103520b0503504201c400310115000401101c41c1c100140746070300b030003294800710314220011100280080071401c041034035030003048064400f5920005165160804100e03400c0300e90030650808084081d50b01d00803401d49641c0f80e40554650420000003103500307004500e002801c01c1412560302d00b411012a8450001c03008000d5048102c51011005c2001c0ba00107440d40c0082c4001024281c0c00c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 825954280 1250 825953030 825953071
    0x50f180312091905011e020102090415061205270a0b0a090c0b030f0103150209060705100b0126150616050717030409090c0b03013b2418100608 63
    0x88501589024047c0b002505001c0054040f40640b0707250004440d440d10608024441d03580d0025400b091014100010302403070802c0a000301700c00394040d1265030705203191641c000364424200840803009a000007601034501e0012185001004030309011200c6c042c0d0b80ca4009078a40d0f01c4070660b8000e00031480c0002d10b603440c41d9503600c14107010030b00c4001748580030b1120741d0007a80c07040090a40e46000314042c00b031030603c00201c02d0895990b406940c4c1400801d0501613402d0080182d900c0991080f0b008170203098603402e44079109229500e00d4a9401000040d00020140000e500f0032009441041103c0185849481c0d221250501c030142c50605d40c4180300401221045800400c0c0503409038100d452241d8a4080f180b14551090b00b1020000f4607588000806130901850300003038546e0010007400c0e0398100605846070b50400740c03080c0e0076910840521907040c080700414940391f00008051001d10b907095064120f103141c0403107152400c10703010680014854001c0c04064491492503080001d1503000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 825955530 1250 825954280 825954317
    0x709050907030b12070f0e070306180e0111030a020d050f06060723070617010801270212030a120b0d210903081204061b050f18031209190501 62
    0x140143d540c0f203000414208000c4c0400d001842c040c2c4080310710317244031074140003000351110b20240203031003098900b00d010030080d4411100d03120041c800c0c1d1004280344803245c120320701401c2503103c0500740c11400428407107149040d60081641c074140490030301240d5203120040207126030480b000e036048a804c112403400246e0a07129020900b003c0c40400c040b10300c454101034600032440c0c02000101340352a440100f000c1c1c1a1003814014860540240021142c1040c0c0c80c0314001c0440d1104e951485181b0b40c1c4c0304560300c1ca604a650200000200c030703160000c50400800702039905640c141d5091918940750005d080c80c10074000940d42081240b41c6152000c01e87d1500225800320180801c0154031000c80050b213941e00a00d8210501101ea0f085030030182421f50443d0b4003107044480781c141c428400e420198220003030300e060180d41c041e404e80b6081c000d48158445444504100c0c1c1c90701945a81c00e85040c854005450003041c152820a04030f6030b0303a507541d40c480c0928051107003c20248215000d51304074 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 825956780 1250 825955530 825955541
    0x30e0c01080c0f0903070b030a020310120c060f020f15060436080d091208130b010915030507031a0c040315050402010908060f040210020c090c092b020306070905090703 74
    0x6012141d4887c0e94070207140c2160000d03142070f051903400005100300e003240c0d09007101c040c2200c1c1c050b00d03002204541d10141032508034440d0000388403003000b1240c0e48a00910031907040c0c44480c81a00c02411064061141c40301080314000d20852a1894501d11450040490609001e4040e40b0281c0542d1a1800c40c01d0903283d02c408a4904c1c0c8204005445d1103214011400030301d22400076610320199140c03014260047c0203141000728641050407102180c000c40030b050460794820b200140810b21100c000c0802c00e5207401c050803500c10640d00004001121101c14030100e2040000400d03500ca40b64150740a03c100e00c000b0f003201907105400001d0f00107079484036410920504141041039070b0b0b084000d050803000c642d601c025100d0030040009500b0a030103402000c03c40c52000d04000d944880c000f800061004d03020b80710410000c6000d03055034403200e1200c04e240c00180c10709420003140c500002c01c2001010307803c034001d01518002c160107a004100040558000424440c1c9554420208500900 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 825958030 1250 825956780 825956797
    0x2030913020912070303020111210601021006030804170c0904060c0c0b09061504360611040f0803040e06061e0f0d0624080a060b0307030e0c01080c0f 66
    0x1d60801080354281d90f06107900502d460042c0240035054598200a07003121824100703604040c0e0700b00702007039110303014003a100042d0300e540b4881c003190b8035078100403442c100e0114501d901403860807a020090045c140e01420850b040c82b03100008411488001d40e07128090182c5036a080301880c3c0c0803c000924540000460740a0782c5070a0100d5204d07600d0b00c201e459400c2c0e9901c21035422140a0145102182da01c2403015941550305015903484401050f601c80c00b00c140c104e250111315900003401c0c3c017016541c0021703560044020300c4049008214a605c1ea485442600340c2c9442000f00047c1c498000b105907011200821070003521682c454051059030b52140d9000860710001c3d00c42c0400c020201e20141000031000e025042e00c0d0458038807038004072845504865241c01c251040d4070360100c5945005c0080d42c1e801d282404060700c42030020780c05000690840f1812f0305002c0308003e40c66605034045506106030100b103d05542c415001910036400c01c1d60030f085608030402224071010305400007003c201 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 825959280 1250 825958030 825958069
    0x18040e152a0703050a110a021e041d06010b0f0c1c0f03050c16050f0114060a0e011a07020a0f030b1e07080c0901090b0403110a1703070b060103060302060a0809160501020309 76
    0x680c4039400100001c9810040f6015140325400810342d60500e8894515082c181000c1c00e01c441500b14032a41d034810b41481005065880000c0c418110b040740c2046d11140d07020364080f01c051c2c8802030906210815800322a200150308040d040c40d41c03d20901415010fa00684078240c6000241c2680c0c0590718450381060f6420320a84040b0f81d01500248903801d40c000c0c4684d182c58a50500c0300800900c2e80d402e0b406604400b1480c0014030114608003c0548000a00103c1a689020500c081405a00b80d80c1c440b100c5010070341030010901c07450906852007070700000e4103110b8068100200204400702030300c101001580410021303851000b008001c203981c5005040c10218075640e00121a410b44c0182c00445040c2d80200001b800c80c140034000030040c00222034001c4084140700301c004d94900541740d0260820380681c1c0031504503400b03a480203000d180c002d003106640e98070549024100001c2a1510203031071088401c04184044200c00f180d0a40f07405074007461602d040b850801c0b0500001035041244e5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 825960530 1250 825959280 825959293
    0xb12060916032705061008010905061504060518070305070f0c020d030306080f030c010605030a020315060d06050411010233040c0506040303090e09010218040e152a0703050a11 77
    0x11070b4060000000f4580300d44024403e51400076105501003a2503408201d0582c1454490000194040b440c26403041921008481540130500000c01804650344003d4000e0440420100e200451002c020712030026900c01380036580341c882040302c0307448500095200141000b130301035005107011305140c0d400034000d2402003000c0d5201c161080c00e088100b4144001680000b031001c0095400307015038070050108038040c110705015a00443c2d04c5d4081c0d0880354041880000014025944808030b41c0304181e08410100a58603241c5416424440402d12040c094896030500c0c124a1042040754810600e00220954000500d00100021100003a000702c078074010b030020208103070302c801c0041c0004502aa807100901803030060741c100360400103005254036900411400f10380134000b0306000e1340b02d60190307000100c3c54688071440782000c0320188802c42c2d02c030003001403002442c018100107a010b58120030820591098008801042c407400394002c011820070b0080c030300418042c0f5010202c4000e404103681c070 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 825961780 1250 825960530 825960581
    0x40b030a1d01090320030301061209120f120e031e0c010e060103151a0f0105220f050105070f024005060306100b03060105040f0b1206091603 62
    0x7207140095595005503035441003c0390504d68400d01a000c06030044401024021100408030388a2205000d400c040c081c0d0010b000182c96410350011600c0740c2c02000f6103803000c51030074004141c03601190140c00066001c01002e15120a28429813114598070001103140000d124400c42c5050305500d840c0001c0300302802440c1c801c000a01803003036920851400f5001c150f04604e864030840e401403444072821854005041095506104110316814080325489440081500126034510402101035000780c0d11804902e08060014100d00a5031800d6081040f0307070380c4540044404d80501407010700200e40103010720b03025092036207990100003402043c0400350030444034810101a44d80e42c0381e44501d40c02c4100141d0138400e4bc414240c012008501420b82824a0007101401d8001c40c01003245e1030b5400008111076a0088040704c0c001c00340c2d211420300055844152180c180c00542c1c240c00480e844c0310003e8040c0c641440114440e604007824002c4c50031288030203c0007003010f40d4810b40d12840a255882 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 825963030 1250 825961780 825961811
    0xa09020a08071b050703060506040c08150d0c031b0315110d020f070c060203070203060a050103080702310e07050a060507122d17061008090c0a2301080408040b030a 72
    0x2000d14010507000c1140d04010003402b0455503200345c0541004101814840c5030140d800781c40b810320b6000c03240d80c0c10540c118185010103100c1030380000c0000501500c0090b6480b864000c007022a406440b600036244283c01014040e202c1020320420f101d0000c120704000d20210f68003030880110740700940c9040506a0740d41106c03582c401e40110340542d0020420108600c0c00b00156940b107002d4600600403542f45907030b90300c05400b03030740710080c0304200d0103454480c0ea032400440000700f100c680a01c0c40e059680d07212060010101240804050702542030040b50078140341421401716090381d543d003841d0405685420039801a03240482c02040b15154040200004103c45810201c0105110074800900810098502c0d0742000b10100c4460112040003600c0d03a8a80074643c692140d03040c034030859540d08402d54100641d20304040ea01c8000007001152550ac07040a0030070742e500d40742240b511111824015207030842e045a0050050030100824040d04548a014540105410720007140b11400898002c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 825964280 1250 825963030 825963043
    0x909060204051002100f060e22020a1205100b0f1003060503061e06090712020a140c0609070f05030d0c1a0a0f06120c0e0c1b0601050a09020a08071b05 66
    0x2080181e0000c075158032070b50b00e00d100d02d00d030b2061b0030001080a02c0c1b13018a2030700000b40040c200351110001e094540b542031020f1540104041d402494100b00a880e50a5080804030a92068450313109840111308510701d50b00c03e0481c83d150040540007402003400030000140c031000c0d00c2c1003c054680c400090a038604004683c081c0c0944d801946d40810440a0108144802003241e407045413840103020f5550703040014842266030940c0090f80e250b110150681e02c251881da2a000c051784001002401d1201c00705600c1d020f40110001d8a1425076242024034454200f03000c1d1b6a890780160742120f9036075028031602507a4521510f010500040043d0041945500440312074542c01c2e140e50348003806036401d02c10980500411078180f0b5410105450340b86a5100034020000c8001288011898021140c0159920494056488040021203c0705203031255801c4c40342e140607001e291002b01d014070315030080d1020100c5a95840d80c4030703030b0b0340103003100d0a80d15900c60940c080c07000d59401d00455000d00c4076 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 825965530 1250 825964280 825964309
    0x9010207021f0e040203060406030b010803030601030612030203041e32010201090b04020d080f0d02041410020d30091709091303170f1618090906020405 67
    0x50312104580103028405001c03000d080106081e0b80040316203aa000340090744042c00641c0c0050301c1c0e84d40d10b0081002040d15400141c4410007080c0001040000003004502c207007000c2e1703406c0c403a9a45d03400c580641300030542c1005015030801e000074844030150360340d085100c0c001c3d00414040030356144801108200700350400b16440010034581c03418444c480000034440d4400307100030001c15000d622030842112024000034850103d060025040c041d180081d17611251404140c00c3c0c2d601c2280d1040c100951161140a6002c908144803441501c1c01c030320314030103401c240e8000d0b007a01c4a101c0421144042e0280040074441000b04078000301c44000b10f2a482854208400020300c040241003040082003010039481107c907042140c5e20084e05c980c540301b5080660381543c0c4144003060720b010340f2035042103561002c40d401510300b00300010b0b105956560082020003442c501c0307803420650807140101c80c54a0180c0d04040503000300801580d41d48400701c4a8042c81006003483e45900015a1315480d2611 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 825966780 1250 825965530 825965533
    0x10302130611280303090804050405130b0901020a0c30050c1605150a0201060b0d0603030f0c1119030203060c0316090e0f180105010303020607020f0606030a1b0e09 72
    0xd4251a802c04000c0310100c69a41d10455000c002c0308800c1c409220040e10000b801c15482d60380c140c041018042c25100641001041032000d89801a043c0907800c05002c1e0596800d0508400326808440600c2118001d100b256101c000c0d0040c1502c5803451550140300d000c08000c1280d940051810203142000b01074501551200e40d03031030b6030741d080b00d24091b00c00d03c03e8a000552510104003544e119080c448400c451440d0041c0c03031340740c81c410503401004198000c10040b540000da00e48141c485600c404c007070328801d0311905080346c0000c100b1102d2242030318000303060403550170152940b4600b207041d10f61160f1504641c9184a9142c0e0302081c10441e040d82c00951303114011003480100c920154021025071101d2604146031442c042d20354045c1307440030340354809890121011400c0c040c0c50312803030310201004800070300c055656440c2c000c4da40d8404542090050090b245c0610207108041030031800340c40010014007101c031541d12035803061a8108980028411114000102c9142201080f4803c41040e030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 825968030 1250 825966780 825966797
    0x110f1e0a1e051203040806040f02012703150b210f0a03050703050f0c0115050306240907021c0e0f0603270111070c0f05030102040b0a08060103021306 66
    0x103200e400c0565400c030510024401500711601c000440c07040d8201c0d80304990f01022283c541c1001411340c40f440e0042c0d2400e0244108220a01c42c03000403a03841c00307100303903240c40300382c0054010740e11444200f042284d64042005403c202140b41c51036031950050b83c00c000003540380301680000b070712141c24541d504c40841c400e44901100107000d1001680f0101480301500c2205140e990041041c8503800005052000205402108440303980a681403110b02c43c000300708400380c6003aa02003021041c4280c5209104a0000502a11214202240b000b400c040a5140c0c10198000c100c1303e030100510321021480b030a15114014100c0c0c410540415200ea1100c80c444401d00e414402c255100b019020f0044e441002030002170300c56080161044440148603164603010002c42c5405094203402c42030880d50040b620b00c00703000b0070608080468904c180064217441c1d03240c0c145802d03801a440343d20308450003448203510b540d0003291580e5006e5070500d40180740c440b4210000c08000c00d0341d00511300050052 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 825969280 1250 825968030 825968089
    0x10f0b0306100c140a03181517091f05180102040f0e130c0e090d0c0b0f1816081c0e011206050913020108090f07060c1505090303070219080403110f 65
    0x47c0ea41d101400f481c1500058650b0342c1840540029100d0a05d403e031103001d180091a002402d014808640681014145030304000e40065005000144c44503040300030440d80207140b081051084808440d040540403149030700c0e01c00782e480140e400811200c0e549a80700d80c0100000c02e084140c2000e400314110f206060b0510f11850791410010300400001d001c60010b0410100e100002403030341c860410440890285e0300c1c440e002c001300000303480017091880b404110300400302c1c1c2c0c0310702d02c015500d4120072100c0100e0182c0d8200b030761241240b82440070680044c441e02c3c0725407180f000303010320300e0081c0800300300784e079403100468090842190b003103040faa02c650b499411582e00082d80c0340c100e086a401404119049503482d601d500c203a01c00e0340107100e404000901004190205c4440c1d041005004004030301d00250081d840754411104032005010b101c0603241024140704220711819004846242094110b94505811402c0f00c00e5030341d400486090900025551181900e9a50350001c1d0380120300d4129 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 825970530 1250 825969280 825969317
    0x3030b060706090c290904091b170718020a023919090b030c0a0806090c10050f0d0608100603022b112403010f0b0306100c140a03 57
    0x102c0c0c02c90166643c0001e081540d05e45851134a0038038003051202c0980c0c40c80041c0000b0000c0070002c00080603c4a114032400c03142201400b0202291000c5d09a2078a40f000c0d4203031079031140002e00502c180d00d0800702e80c681c1c4640c00781d4040c105140b000d0046800c0407014480460002d007441c00e441421740740c4006100d48030580100d524018500c06d8840750025846100c94441250780c0d4060700403490b917244402007085d9400c101074661004003403d05000aa100d11589031120011038082c0080d11440c29011001d00f031090042d0450b004e25940c05040c10240300ca50b83c6641e012a0142d581261200c4010510210a000e1070268441014000404078a036105100500f42c0040c48001d01c4002d1001c6040110840030b840300b0300c0d43c0d000741078004d0101c0344000a9030001c0071100951469807003003032052000c80040015410b8a41d40e4902c41162940c1d188110414401202e105801a92003603418402034043e0119607026482600d83c09906500b504aa91070b01d6404001a030014803290800c00140070b2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 825971780 1250 825970530 825970553
    0xe060c0c01061a07030806060d020708030f060f0a0905040c05090a0b03010606031503060b150a020a0312051302060310031707020a050a050a0302060304050f100207020102010b1f050703030b06070609 87
    0x60820148100524a0f000007901401c14084c040c03008090000f003803903807580c04880a150508000319201c085c5801d0920403604215a00250804c0c803c3c00305036140b900700f401c944050b00050060701e84900300300292014200180c0102c0381401d81441c04074150361000401441940d4010300016804050030802d42900c80c0e5034042010b161900c0d040b176208030305540810082d65084140491040b40241c0400d4030906025440405501301040704600c5580c040342d54145540a59251100302980b481d240381200c005452090003220003121000060411b07402a542c480781c09c1c0701400c000b607030765210002d4041c84040380f654030450015281085180505003107024250a5030b101d07000d90304040200724007003450301000e4424000400000d081080402c030481c07042c074004081d143e212900310507001c0030b0741000c80120b0165003884a80301541c20610f180c5145030401c2256000d01d01d210b040280e40562000074180c0070540c0362610104141c492200420b0660b2061000041030300030f90825062098 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 825973030 1250 825971780 825971789
    0x150f0f020c011a100e03030f04032105030609160c050d0810081b061c0903050a09120201022d01090b01090606050406020309040c09030501180b0105030c090a020d0e060c0c0106 77
    0x103c40100102c1c1ca51a1049144000001c5050031090f2070300d2180000d20310f00594111450304c0100280c00b00c00c201c8500202c08032188a252130b904021030b00507040d501404120340450304a418900001d034041c0340f14648009200c05414003449140441d16403508007034003450134174041a1b5010901c0201240d40c0c0300013000b041030202400c46445c501a0307030300c030500381007020a21850b00800d030244100d04402035803003102c11003a804c0100c40400d28010380300742c111400780004111003081c005051000041d0399240a41c0c16809456910706440101e10004a002c003000807c0b0f99865484920790b601f417150316001409030912030400d601d4941d8500035607507690880b204012040c0010089160008142c400c407490858010806010940c030494420b00c032540090015824220103154220410f542800d115005640c0901d6030780c1c8039824140d45000000350103400450b003c0008030f19040310390107007241c0d00502d000440c1c1c0d0391040320704500c2e118040c0e401c0600c0c2c0354002a01c3d030f5170301e200344200340040 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 825974280 1250 825973030 825973061
    0x1b030a0911102309030304030308010503010f1e0c0306080304090218010f02060c28050306040b030c0f19051503190c0507020108090715020705010810030b04150f0f020c01 75
    0x50385098002031001540800104140b401c401800e041c0700704082c10713900952409001c8039200d0b6a2800d004003c0d01d070031f114240c0254a0310006c080080002d000f0313040b240094003020340244011202c940300900b000130b003e0081558441003c50460030a00003003008208a9101507100d00d101248000d20418120300f8a040c0806000101c0850b500401e016904c0b4900c0c5240766100c0728091290f807202155440800444d00101c05207400a64001020754064981038401b003000c40c003000309141d50744180070586640408021100b12107032a000c05641044441c8251900d1902e507102c3c040380810751118604c03841c0c0d0102000704012005030040c2c105814019000031301a42d507040302c01801a00c0f660030302a0400500c040082c2085070200f002d03800600302e910480f8914000b8040094495000e4018180002e10030004500c0e00e0300300c42c2c8100d00344ca4100c800400251265602c1401c2c0c0e590411400703d0403501c0b24a405805c618500c151404c0d00e801d01005030b500d1100c2518282151130400c11140c04 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 825975530 1250 825974280 825974299
    0x80c030414062521200d050306040f0b03010e0607080a05060612070302120103150c0306151b08040f030b16020d0e04151203081006020c06031b030a0911 67
    0xb0481210390012074250404010980c034005030804030204030340c4040340c242030740d440c06110b0b645070345c0000b0b00003403030485801120458190b149029181d014050b80308002413003e001248061a11b64011030f11414411400204400100007281c02d68900b200d011401e80c0204c0c04000c0f0040d0005915540004419420421868040001052402903080205590080d640040c070014060350488921554a05e5101899130703580c03402e02c8542280b800c600881c18186118a5115030003401020180e40c4198804403a12044080c201e030b4060700100180c644840c0418203e01090700a0028005400480c03221000b090031030901c034a070003034050072426030458121220300c82039a000c264000103200a2034110b50003d40e03030000a02a207100c9803844a4400c074807000094000400e400545c0f42842901c4215035507555030325107010f500d202d01c280405030704a20740703082c143d01c0e001c1e00035039108079a2480825140080030500510303803c00c803119080c11b5620800ca106000105a04038020102103400200 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 825976780 1250 825975530 825975547
    0x6040b01060806011701060c020a0e180c121902061b010c0f0c080304020904060e030a110709050405030301030b04030504170f010f111615050c1e16140703080c03041406 74
    0x52017a4140718074010813407416452811075071900c032804014500c1d00009a00c0d81098080f10344e40544200304041e151280241c5102d840c20000c080e030011010010181c00e03040c50018404524000d03d9104030390001d0308001990400c0c0c01d0280084807155607a0000a528107000d501515070826100b4580604c070180c41000000b454120850b50321990685030300d6550f80780d518001d8040c1c80400c0302c03c0709a000200312640d41070381c0071011800e40808801203c1c2129075502c1002c04841d8265409040341e00204014008214086a0309400610a1402c1454241c2d60000d000901c03000002003400c40e041500070344c0b212403007405003000e0070840070800c100c6501c80c4c01d5001d0f1a031054020194171b42c00052241014483d1200c801109804140010702441c82c1c40a295811680010341c0da402c006c070705075008410300c0208030a4441d00040310b02e40e01c50450b5580c40d440809110304851190a105148012000400301c0c1c3c041c1c076948404400035902da07070816507803510a800701c0401a02401080c00f200d035 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 825978030 1250 825976780 825976817
    0xa060b09040213180c090e04021008040503132c06060a030b030a0501020d0e06070527030f0706091d0c041a130b0a08090c0a0905090f06040b0106080601 67
    0x4620003401c03100180d40782540c0e614803544408541c80080401c0f03603081048007410554001c66485030381641e80b0200c50fa00c8030030b40c9010030b50542d1b000c4d4114003d040381001850241d080c3ca03821038010401c40e401e14029162100c02406650041c441c41030095800240410f1010100f86180c41003100181562500c400402c0603400b03031a00080402d91244030100154505000f5100410b400000039591101c41044200241c020703c2d0000081780300302d44c0001e1002c1e10420035518064004079034405504800e00c446c0018442412023035905016101003902024070400c0714800a00051b11111101460000c020300d92031303012030650010706060810484183c10000846042d1840200100014501c07810f14600500580350442c01c0807411140c045044d202c150302420705e4a21035610750006544002c2c00b1522001084105500700905d0700e403e05c0070f1720541d08000c1e0f101e03181c03c2c100c4800c0741032078800902e841d10a03542580e500d80e83c20014001c20b5071144034542e001c242824601500c1c00c1c01940174 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 825979280 1250 825978030 825978037
    0x2010f051801080c0c2a01140406030908041d040b06030c030a020d05071502010b1c020d0b1909030507051e1507020732120d030b030a060501030f0302060a060b 70
    0x1d04110030740f00001e0211204100b560344680c01c040031a42a0a80c1c19070a400c404541e58580340e04401c10f090002256101d4894007001422a482850519280110a40103804c0d901c03c1120802424071010403901210038544070241c100d501460694142820b01599040c000f0740000e000c0d030031901c10948207450020705141c00c1c941c1507801420203407035420801d041069540101c44031100d007241d0420034275415044091268422144480039580700c00800440b4018000000c2d008028a40341a020607002e040046d4054410300460b06000748503503a41781180e004d8101200803420100760841440010000d141c180f28416160040d4152195080d6960f582c00d201030003894103082c0c1c00290184e10074041c8400801c0c0e04100510201b488064800c0c00412601d4401303d540581045000340e807820307001405a000c1d8840c041c01c8107111089086000d051038801040e0503218080c06403000440501c1442d00a601990081c20442c800d49002418490040e0042003103505240e014005001000100e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 825980530 1250 825979280 825979327
    0x506151c031215030f120e010c2003061e010e04022206030f0803090f0106051c0201092102030d05031005100c020907021c0215070c0812040f02010f05 66
    0x1c0c10ba1072001e48000242c0107a60f01642c40b0032040000100f00501e40e009441501e2141d0b0105986054268085825000002c10580090384451a5001003035082c400345980100d90300c00015403c0d03401c00072038035040094a0810b483c00303c1c14070107505190706d050110701400f0a0401011142495000110400d49544200310b5441c0910440050881141e001c1402513074000c50548003c091402d0081668004407409103050040004540d6422410303c10941525402007160003410701d0500c0048654a1840c0d04032b05004a880d004617000c0704c14599683c8035144a52a001c00300c0700c92052600300301c81c0c1c0004c0400d10409006107d69481203089420541d1010b179100780d03201c89020411281c0b403002020294008101005001c1c4459000c03805220f0b4105410142c107112084150880c0d81d40030b161103200003901c440000c0350a55115001403049180203000d01030501441c9100d58110b11000c0d20100c0d01c00030300c0b00c0d0200c110758015403401142907541c20300700d060039034040300f26985504540300c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 825981780 1250 825980530 825980537
    0x9240c030406051914061239060d0e0114040f02100309080c0a0219050105120601021606050405011b051e03161115030103080406030504020f0405040506151c03 70
    0x2038003403018140241441e180c007503018014800b842c1c4003034a0b0851705490700c502440040402a01c0010000fa1004130405415100410440524515050401e4491081c158580d203545500425607650001d410300314848040080c041000488980c2180e00065070b1900450303560341000f0124a442501e5146507405440e40d9800d18110301080b8000c10b619000200050804134800c0035030240013411100040c401c4ea10140d6480754440c4544c080210742c80365a000810070003d841b440410703202e9854022074180100e81501100946542c004400c941041c00000e001281c1007003a0f60380400f5010181c41c0c0e091028080882075182c8a8807a070060413101c51100c03105040c034480340420011039860307a01c01700103958100101e140581c15074001c041243d100e2005002c40005e85120007045030704a03580b20280381c0c901803418070203a015010003001a603100d05e81c5584080c2644440c0210b500c9030f407180c03002d040d00d40b9049041205042c0d01c101da10340a45104801c001c142d00703400c466031288980500b03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 825983030 1250 825981780 825981791
    0x42019260706050d1b050304050d0914010c06140108100c03090f0807020a03170c100c09051002030705010c0e0301051302030d0e0a03020d0335070f1709240c030406 72
    0x5148034007500608180440e5036121008074100d05d54490080d40c000d5206005680301600303180c13400c0341e03d0280b601401c1600340e2060724400e000c0d0300170700c20b01d0030311481442b000c0380361001c0c9812503408500990000004e40c0050340308414036403081c031846108490905041115261310f480f03000c421314440c84c00070400c0500040f61790544d502d40c6418801903510110415609001c500400426001b08195140c0d42c450301480c1800c00941d802200e24141d055610804517038507200400032883c401d10101030a43c0010040040400c40c28000d0074980150b0361502a82d24182400b411300b1224001c103910720318051401d00c540180d401007032034070410303200c0d11300303c0c81c10002200024051401c9510095100305140406e03410160080d9844e9003011004884c000c2200d0746200845081220460502403500844c0010f024640281d4044991410034501517103aa00c3d13214403414504019520603031144c4c081d0015540542c0b90405001428030496002c28040c100194141e0b183d01000c1c000400e903d40320b0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 825984280 1250 825983030 825983047
    0x8280507031520040f06020a1505100e090705010f0e03060a0b0102030c3f0403060f0207021e0306090312060603090c03030307051c060501050304201926070605 70
    0x1e42112a00e443c10708501810398943d11081a070b0b9074800e1203504a900f4007a503001036150700200e0041c60060b000002002d26a000002e041c0007132070000c06a884000c020308000c1a20310f140b1140300c1c461030413a40284841ca05200000d4041c0261040c248100711000c00c0c0f80b0b4440d1070205229030464004103012490a1007100140d0450048102c01502403160680e40560300240c4020f00e550200f46980d02c2c811071900605600d10040000010150444100410400175009500240d90276052072401070500b06250f0015842c80b504507030060303104000030007842151405000300d40d049001e1400035481c14003825040007100030001c10303d030b100d40800710004244550a0001514031a4000d06030381d0799150600f4040e0258020107001c2d04502c0800413601c00e12101846154140c070300c16101c5905540d240d907a0b41c140241454070a0100c1c1d40140c54000b0641c9418041201818040c13030301c6c444040c10001c10200c112034241c00c00841d5051100d0380d000c10680410000c0540d42549421552010b00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 825985530 1250 825984280 825984323
    0xd05071b03030906060510021509010f0603140715020c090405030c0f0d020c19030807030e09070c0201020f0a0b010b13030804120302190308010501050705070f0828050703 75
    0x22a4501040d02100c410524201030389580a0b2080c0e40c8500c1c0100f2186480d80140080003409210030b4004d40d0040c00c400408060f52500140c2c401c018000108514040c0003441c0203840c901c0e0b00841c2d4403510f041403c4078400c401c0c80b881c1c1c054900174008c110352502d0150300071b50b51241c0f04100e5004172044030206e400c2c00024412280c203500f80c80c040720000c0365500211690392107017626100041c0034510110589241c801044110601a001100c0c05c16055417940030055000d000d048043c0b10081c1e0b0700100d00d45a0a402e1032042d80d131a00c0e40e03000648140006414107520801041d011381014000000280c04410030034151020ba0b032005455034000c0d4100100f20810f500050402400445c00103044980700c111501442d00c2907003134490381a00c040d0f426050351009480100840d00140040c82994464405400d900303004000304c45c1040c2d52110388503101801da4201c403516030451000100d0140d4110741c0480c141050200c102078022207074880e5a101e0403a40402010442641c46500c0031805 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 825986780 1250 825985530 825985547
    0x9220204020c0f030307110c01080f0903210a0c05031b0901050c060f040c0b070c0512011e050a0b1e010e0f10090e0705090f0d030c050a0606140906060d0507 69
    0xc0d00c0b021a483c202c0440c0840c2d80e20b40048403210300041d0710034035007004040041030003254000c040c0c40c1d489490710f8080c8007e040843c01040e41ca1588000d010190103584003d104500032006c0d07903031401490078802a00c005a640d9914540c082c42410006c3c00429135105210303110342600c030020039071100c0d002e000482d003030321552000740118071804003408581c0d51134000060003203224030816074586a07181900207050251040140c621200d02e102000a0305261180c0d1255112040001030300c056001d0010008405032000007403810343d41c7d401c210440d015072003201c00314641143d10060140080c1c45000c030311100c21030700314100700a0b80c5000040b5100d03002d036000603041c020a0f5a10640d034400b0010b013512294803d14006244600101354094010000c49001e100d025020054203a034860a1101000058000300c0c10883d010b00c400002c40d100b404084403691045078042082403a154841c00d010fa004021203100b00d400d001484919542d000c1101d01d400b0703910101182c40e07503035203d05584560 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 825988030 1250 825986780 825986797
    0x30503040e0402190306140a230c090a0801050a0c0203090904060b06040b0a050307120b030c15070501050106090f0b0a050703081b0a02010c09090603050604020112151d060922020402 80
    0x4c000c03020041150a400000c00192011840c183e1550b03034040c16001c0d00c10310212144c1031021a090074801c644140fa0751031b4400520080c3e14a000e80460100f1041d0101b980f08182c9659a4004d101c49480c0f903000c1d0802e01c41e100e10040d07040452801c0011240d801c050402000326595824100c120f44910041c2c90007000c1c10b2010700d8072100c035214041c010750b004075110b00020710814403142c084180f61113250502040a0300802c2004005030900100d24421900460640014032040d40040c0c000d006850180c010307581c402912078641444020025402d400150320180c003840b00d035003050b61050036a000e00c1d41510348200c6a484a0744d014980c00e003070010868040c0e0000881a08054054004032002091541e43c144441c0d942c00403182154118000200150003843c0882e000d90b1148034044109500004d002800380840c01c02c2022000b510b03403000e185081070308040010b28400c840355591080c0207480d410303442d01c0d0404000c540e500207981c40904070450b211540c0e065445a605075103810 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 825989280 1250 825988030 825988069
    0xb0f09071208040303030f0e03250f0c060813050c0f060705121803190303020a09090c0f031103090604140f01020708090306131101081324060f030503040e0402 70
    0x1509609000b82140e20900040e408641444242521401d6a205080c128001c00003d1400e0819840c001d45a10305010158102c071000c812006000c11030f01c10313501010328410002445254030f0090054507081e40200200f11510300004e08101250001c90340c80f01e05081280c44901c00120040010000c1c0101c141c0a4a60312650501206506404000382025000c1907101c1c10031080040070941da42200b0018910b024155003640360003e4000e4000c1e00c001c40d003070708040031200d8a50b0021003c0b100c0c0304440038009050099402c207815010301c01c0800304020b0f41151460b620b0310f84c01c22a90782c07001a0000307082e088802034014900c2018000716441245000080d962521a03080010243c1c0000c03c1861082c003412010030008a08441201a001d6000942c040d03140300c407000648007070100130058005606000090000100280031090701010000c1142808041803a100021141c054108890041103084140301061000082c0e40444542c03070155240381d039803840031507520004907801301d155 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 825990530 1250 825989280 825989309
    0x815040f2d03030e010e030408030403020906040b180105040f020306100f020304090e060114061903051308070f1419020411040b031008100507090e09010e061501090b070b0f0907 78
    0x40640c5500494483c084c554000c0c0825001090360741d40300e1145216a00c0c0b16441040200018181045099406a0b00500000f80642d40c1c2001c40c0b4107018450302c0d010301101000040c404c62806106503210300280703034070450451410102080b619044000f039403080c001011036520200b88208112005014204020300c54202d074400850303036070302c1c081c0030340c90700c1c0001c2d54441107403400c082043d03400c44681454400020008964207500034031020f807840100e0a4030f9202800030881c800b002f0130010348500401d00707416071181800c080006a20111401981000080c00d01a0150002d030301c05080d01110000f800b5014101280300c01e125aa110114520300441005001c0451124010031510401c0c01d0b190007841020b11801228000c03541c48010401c00c440c2404450340c0141d1840d80b02d141c98000003568091a84c1c85441c10070101e80480e207064240a4a94055074444034520080c034031404041d040c80c14580d11240076080042400e00392052030700009015050411858004180240c6040203 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 825991780 1250 825990530 825990533
    0xb0403020111270f1e031921090503120a1206060806130b041b0f020c060a1b1b050f010804021f020a08130905061c0602210f010815040f2d 61
    0x14845075240c1c4942c420701a03080862401036010059000c015484148840303081d071083c0040b0004400c003800c150409c00215804142d41e1010000814084490382506844203a040d02c001c0100c0320307074a203102150341404410800f654020180d00e4000c3d104441c000903007c01d030481035004198005107181c0c00703800c007640f40610688062821445032031030360340c0c00310b1251450f07005d070398421a44018680250f010400e80410350303c81d807081c1c403007015440301006074072042d600d548a002682003000c009100f026a01007200d8503000031100760b601420308151100340303060740020742d04038640600403038032100e9400031015007403080c440800016800703512591110049540d00c007440f070f680d00400007424500000704156181441100448a4204402100c510040c0c0d0381c9001a4103d4004244090441c420b07030b800080c40fa41d00780d807090072000032001316503141008041c64882d0301b11082403035186000c10300c0082620341d0000030000b608030a41140e402880c1b0661000a8600d10765144490340c007003440c00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 825993030 1250 825991780 825991819
    0x70b060306060d0c0b03130b070e010905010e01080f04140601080615041107020d05031c0207060b040c090b0a0516060c020601080303060d030e040b030102070b0403020111270f 77
    0xa01912040c0d0440345690b6800040c07050380d4107849030103050920424002c20550240304020b540c000702002d0f12001107034607a62040c08094054038580042107104e00d00c1d0703000b035a0090303c0c08010002445e140850420780c9001030b080d80b40c05010320007660781c10300020701403000450028051240c2442115050340e501d58000d03868141c00c0d00c02480d031125103110b100c0759107031500641c40720f4550905041c0c54050140d003000401024200c003250503000620602440d010002c02c144100c484002000d070b940d40e042d10706002140e40380607220348203500c0c055507080780300d03805968003064035a041d0100f5550400c180f03082e1564000d44c021020302c025000c0681d810480c80e0340005c3d00901040e022940e407030341c982e0f0030191240400c403040b83c0c000441864820110b03211b51019a0000d0001e400040c1122040000ca402daa01c40101503964003042c0007070000705030b42445511051b80450b0301440c24070a00e1400103526000c3d40c60400d100070001312691190340d480e4140c0000341a001007034505422075440905 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 825994280 1250 825993030 825993053
    0xf090d03021011070c05061b0613060e0708060118060f0603061d0702030d020d060509070f021519020913090c18020c030306010c050a081314030c03062202040207 71
    0x6424503800c0000d14103c1404078800c3e201940c1d4000d81e0403513814203040900c0001d801802951969851001446140810900c003a501503c1929642890400d450a048081d44c008003680c8a803640040c0e4200402400454483e054400b0003080c0c6c821101c1c051900d0016216580291070300f602d110100140440d0583c0c4400f0884901d41c401e100c43c00184508066458001c80f01071015070001c22140d440540640d0040c0342044092100007940e40d1206c02042c00c141084031141e002c152041448011550100036151010601542d258810701c0c00300700301c031255a07400d600c82407250f4020407004503955400c004007a1700b9a07884402c2104103001d0170000d01c1c50340c19104540000b420350002400114541c000c40d00b04130398039001549907440710340c011104420708070000c0d21a80181d00303d050015075443c0c010a0800841c10200d08290f00340b84100d8042400c00340180d1199015100f12072441c0c45c04900a0340c4420407158242411000d03c4000a2204846800035032092000a0140400c034180004 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 825995530 1250 825994280 825994303
    0x40201021006060806120a030801030b0a0917124209130201030c050f040302060d020708030a050609060d0f0611040b130e070905130c181d0f100501050f090d0302 71
    0x82d000c20044002d4219120548810b0188c000b818400050011404031000a40c100a40c0700340000e0440181d26020542c4464801c0507200480000700d8962800710300c0e041d660850980c1c900f50103084445c14000c450070351060102040d000c2281250b40d251121680034501c1c0303c001801c15115840c2c000c02070b00301d0f00030501c003ca010034a041c4480400340d1241d0180c0d010b01e240e810b07599240a056408000090700211403000d0119003c0001e100001d0045018600550758028041203a0502034200003401d007004100394006c98951084101154840c550b01c6241504010300194802d550b44070200f49100d42e421a40e099040010711011081c014240d5400700c9242c00820b04e15500c0320001280e10307150900c42c50741e01802c00020750504000b10361100032101070310b080003040c0184c00303403941200c0d0966038048240c1c0140090100203115100d00078543c001801c0c40c40075a2403820020490841500d40101d604010340410030f0f58540c0c0c5903e0480b600040000c0502c18170140c245002540c40c040f4441 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 825996780 1250 825995530 825995539
    0x40503331e010b0301050307170a060903080114041e1d19170c0307030518270702012711030a080405011b0816021c050124051503040201021006060806 66
    0x12150000804d0324181c400c0100900784162902c2c1031040403201145030080103006140c105030015102e031003034044c2e0910a40700c0700d14642c03400029026020044a03003a0040381003905500204140c904903000c0b48400380030026046544100101850013502c80c2d1b403000d841403000c0ca0000002e102c54082080e41320b182544d08220759884000e52a019542101105034802d0080f20002402000588420400714000e04641048000051502d0050083c80b640039a004401190018466000b40f940030086000910071702817565000d00d5100d4004c40100e182144d02c0c0310b08003c0062150032403d05603c020101c070100303001c60500c409240c1c040e20486004c90715001c0340200c604030070040421841d81000f2401e0500351030800807440303c5028207003282e100b07c00c43d0740031400390742192590203440d000386c0c00000c07244607074503440100310300c260040302c003001250758200000e40c0d0320242c00004404059030b450702c079220383c40107070701c1d1040818107041d0990070140d01251855004035014840c0b0b40454 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 825998030 1250 825996780 825996841
    0xf0f0b0f150d020703050c12132108090301090b041b06090f03060213090e060402100914060c0a0b070206160311190e03032d04050333 59
    0x20100546045603080300340a184041c442080b42c41190f9010345105070080c00d045240681018601c0d0a1045024846e130019101040070030011900415030000f402c5140300c40c0345203c03010300151481a0040f04020010880007508039a5034400390800703501180d1100005200b41440d251100d103e81302d142251219000070340c00051258030640028080740c10642021a1290460310b419002c1d40c46400d541d85806800a000900740e41c403842124040381c415030203000241031034810800700d1303c2030100c1c0b41c041005840d000d01641c0c1c520384500101d068102c3d6071581c0d0348242d02405003030004084018154869503030800040ba5008950688980e5204144e034112111b040d03c25412a0b6000707500403e80513042c0711041c80c090800814402184150904803100044000081c0c034507440300a008000c07120a00d0821140708404108103810360500255505041c1046e000c00d0351803502d41750f140d181c40c0b9201c0300d5680000c071110982c20300c44510f02d6410701925024540801c0c40590b07102d0241c000140c02c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 825999280 1250 825998030 825998059
    0x15110d020601031227180501091104060c11150a1101020f0a0309030c0605180610050906150d0203010306050726010510020319030e1b0303070212010f0f0b 68
    0x1c00e1580c140ea50224500340b00c0e00c0c0c003550032151840305071020130315010f000c1e100d034407010280d01c0610010034500700b03200400005040c0a200343c1d10180c3c0070215003800c000400a41c0d42511017a14259030b01458894200041802c012401e5999081c4064106040780300302e81e040301150000740100700864640d0003100e4414041c1600b00d00ca511aa40141d600600201000900c03a4020450303060003841d00c20f400001503114032045980545034011401400004101420014040e559002c041031901828035440c5c100801c0c004030340107111074031681c0034170044002c04480106a8050b00740d114407c544079a180d00d84800104001e80b94907000c0380003548020f40c0038001ca401001c00c2000b00b69440c06036483d0805011902c5c8212441c40d0079400309100384020030f003020218282248841d9004520320a0002c020707410078070403542c40320f01c2c400418503d00a6450000031528225819580f00d000c40c070440d000a801030400741c014114003801c113072102000d00c416421400050a044403000aa00c3e0b18 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 826000530 1250 825999280 825999283
    0x2a1e12100509010506070521191701090506060d09111c0f060f0b030307050706110f1f1805060a0b0303070309090e0a050a0f0b07050a0509150415110d02 67
    0x30340c800c141d400407096005218904194001d03001051180040322101500c100422100000358140725040341d901290f002e409256529031541120581c1c10824900c0016058440c8840b40c14040e00ba2826180c40c041010b9465440454034403007072200d000c110007040c40c42e10580d10030005003050711444a41301002004000307856151140b582c00305180303840b010b00b552036001801c62150204122542d0710280e04203a00d0910003805424480c00151012500b800c0f00601720a510700d030800403d5028141c1040021000100703400c0107049a0324500081d8262000704000e00a103111001c40c503082c00c4c000030f00b008030001786540a00240075003403000f5244e41c030506507030f0300890401030f0002d0b00c040800c001c3d101781030340078580e1b100f22101552048a46a26903500d0b00810752811560b1142c00140c07182413015184c09550820408e00c0c096160080d042c6000308940541002d092080070421980e2103540509401c640007406c80c00c60241c5c1540d9040c10151400d0581b12070700405000742402011036a10 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 826001780 1250 826000530 826000561
    0x303010b04032d1704090213150305060105030f040f140102120106050f04030f020a0801111b06040f0b0601030609060f080f06070f081b040b091201052a1e12 69
    0x400640e40f001c046440c2d1a9803104000e8424440b601e441c04002c0171682d1125030005100c05e0708400301d490402880c04602040e440001210181003616200611000380c0e0301000f200d400c07150300e2842c0070558840b030415040042040100901420703040701070f03648080e4190003030202c1651301e0301100311507a80c1d4101550b02c1c0c40b50940d0000300180810003071000a81c080907814046002074200000640c440104a00b1903454065410391050045050344203104400280e6403614018405080a4142a5600b4000105220740208605884000034550740d120ba40003c00034195124244403c580e51541c40540c101035010f0400f0034040c0c50401c240494000034007500480c04e80e9520b00b80c1d201c5c132100888017001c1c050071940104d80140364150340140328502034000f40142c1c1e02030f070b80e84024032003c00104028800e900000360741080b0801050310b00340e020300c41004207500760050005106800800c000d104a640a4032100d4242040d203040013421005000078400d4122001d40355210138080005001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 826003030 1250 826001780 826001843
    0x280203100e100312051b07030c050a060e0f04020d2c07090504080306060901050f0a0909051e040b09100e060108010510080307021302040909030305061c0206030f070903050303010b0403 81
    0x203005000729100ca407190005000181806c4440480400c1e08403040c2d00300b980b180d10590703030045114000d001526001c0313099001005241000d951100d1040081002e844c5080b001c1881594040b03002040c4100c10b8001211065409150040c030b4640c4150316040d0200315824844030344101100424029020720845000b80c6d045103e0500715640e200411019038071003c02c06042200c00d10a005898650300040e050140e025141d0510090400380407904a40300140416000c5001502d40010140700701c11080c2c12a810210701d484959400c1403e0b4904502106501003142ca011005800300b04003081250680383d4040091040c0d0700c4002c40c601c0c01e6403842c000c00c02c1680040181d40018034003000d2003104c1d02d21115016040c41d50b596140340c100d03401e150f42500032944500812241e0324140010101d003210425010854030348a03000704240e800000c041e4118090303420040780c4424011060f441c0110b030711200301d035920342c5c640714080c03100c0d00548011600f4103c0072014030000c0700c40411000c1800e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 826004280 1250 826003030 826003043
    0x90e0d02010f23060a0e0c0d1109100e01050417070305010509010b1c0f0b13020f0306010b0a0804050f060718050108280b0a0609030209090114280203100e1003 70
    0xe004058803c990030242156501c41820364000a0303414402d40001d1080402401e2244c40311404040d00e0103480c0b2031f02503074540c5142040240c3d5180c0d00e034030010280b60303a6480c0101007003520703500507035591086800001c0c00d0001000d8048002e02c3c00030342c540c10f40344500024807190b00c80480c1642030f1140c11201b03c0e44072502101050306a000781810070281e600607541440c2d40c0344e003a103c074280c1020035039807540c04000301c1c0c42e54415802c00c100d140d0601d01c0250001c00041d854280c001595000c1d1703482803010416035001050920002700711110142c44604191a84c50500040203030981c604480341c1c40f803882d44010001a598020b0031244d105139900d01039100780046007030030f00e01030840e40b05044200680d02c2c09255a66194100c11001904194036091481419401001505600200401c0c1682c3c100484440b034401d080620a400c200592000c2d003103100160f034900044082e2000050802c4d10200400864004000140d411607090011541d6203454000550301c5003001d80c007008d07220 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 826005530 1250 826004280 826004321
    0x30302070b0915030a090614070807090f050111070e0708040b1509161803081314031b030f010c0c110103050402090c03070c1524080c0d0309090e0d02010f 68
    0x5500c5040f00a55020501c1d041c0052080c840e951002e00322005140c20f581c000d1b582d04100140d05410a401c150050780c02e0500c1c40301540b900c6410815034100707004007410071284041e08980b8240402c5550050030000c0d000480c0c501d062100140307000340440307007580c828007a02c01181c1c189160400201e00518040d180450640d109881104400b9060400804102103069082e0240c0c0f51161b2010155110398400c590300d4401c000e02200f030159130b8000d4030040c100882d02c1090f695000640d030891a40c0c01d51568800c0d0b01c0c100000e420428141d8407000103500b0130015502060388460b01c0b28010707101314074014490305001c1c0110112038040707400940015001003c6120b6034640340285d0703440303491407600310244252591140b6141040100300b080c581d84861010700d525450614842c40e04242443c0b00d801107141030381c60f43d500c010514640740500d43c0c03c010703001898070070000a03000c2c0212480a102040d0000c9680b075036a98050f078818015484e00404a0000f40540148090b85400740e811070f11 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 826006780 1250 826005530 826005559
    0x50619051e01030b0c0d0c030f0c1d09072303092802010e04180302010212010909030c060c0528031413080f0403170a03140402150d0b04060906030302070b09 69
    0x15013001902c0090141c00501400c214442035001c2c1450f10401d9a40106482c003074040f07100b0941e002c1c0d458242c24060515144002030605024a00410300201ca480340700381c8801c1000d070341c0b183d50000e41e0b461080144072006041814040114020410304080303500d04a0038144841050028407002c0c894920301d0191080598450010b81802c041b0050000400541e40d00101140b040b40c9641180581d40110720904541000714003140100030301c5605000c0c000340d80e03900500d0000301102c01058144d03101101d07070b201482501550855064002d0750039504e612000c44c003501d420414400d4001a0402e1111115150100e0700d85026071070b46901481c0382444d075034030200c55400c82648559151010320000000c030700c51042d42e508402c4c0a00106650340b0170482c00078140d4244035112007402050718107010060721002e000030b00403d5008500c0c0e07103c0300240000d4000d8104148456170241c1003030030105a00c480340d0301887c1281d119400b00d40c8056981e50040003d4041e59000950000c0c00e80290360 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 826008030 1250 826006780 826006793
    0x6080a02030a060902030915010b0f1218060c030609100522020910210902012c100201020c0f0f0d030b010c080f1201062d0507050619051e0103 63
    0x50300b08190703020124034a41c03502030748003c9810840e4428829444100034401107104c100c102e82c0949240780034507250041390b9030000310a100b0b00d081c01300030441c8040040c2101c8102c5c03032500400d40c0c0080079141d00b801c000c1449102a0000c0d5600b40c4a89416004204407161041c100c4088801c09401c214111201d6142d810402080d01c0003803c4103602004207240d01da85040c0c030204100300503203860f0743c0c0d010b480414290a20180018804c110300c1d10039510007507030300900f40071588501440c4001010008101c201010488622100c0c0c0007482030514100983c2c043d00030b0f080b4002c4000c219540e61514058469607052007180c1e04c001a0040f135034460400d84240c124042a00060510103800000b651320045a84d1084034003035103140001c124195000ca080b0b10046c010146440c2031212142c4060000820b10024a420b009403151100024102c03400381d0155440c464001007900d500749003641c64010002d060144001c45246440d00244000030b40810f05c10480980300c044201980c02c40e031300d05 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 826009280 1250 826008030 826008037
    0x4170c07031b03060e07032406080a120e010c0b0a0e010b090c0d0b0603040218070e040c0203090a0b03270721020307090203191d03040f0314030406080a02 68
    0x11080340035480d0080049000d011050a00400c002d504079009459814004110340c111291690f03035030801718041001c01c001c040000f083c0f03a910340c95030807007601c40c0c1d40708401007980f588065407500400d08806d0500004440304d0380780395603030f8950100d45a01d9500440d012003500000030003000b0420081810003100b44c2c419417299100d50000143d00c016000060890b00045031000a580c10008a2029094082c0145440e442013036406c181035007026400141d80b0f01528100d02c11031146400081d00a511910414100342c4029008004180070211300948aa025011140c0a07a51016000400d04d28880c106d921511138424500303071a566000218035104112840854036104075a000701d0518181c1c0c1a174021036083c0903441041c030709144185410207103280c0c094000d0034418800c10020311052480d10b08400070400c0c00080c0001b4220549500300c1c007182ca601424880824041800c0e00c0c4c46c2d00c540e040d40d00409001803010500210765580e8480e03801100c0005a079003000c681c110941d03030061b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 826010530 1250 826009280 826009297
    0x5070e040f180f081315090603110f0c010906020310031707050307080a180f03030f1107050105090d1406180c010c020103390f091508130506101d0417 66
    0xb140340074409006a01c4c10805908004420146152018585074008600d07d00402a50400340100340c840c0455500b1801980d070307061032007440020440c01502c020351040d00040c3d801042152281040c600440c4021611700007284c00c030f540385482585090446090305e1015601000070f502e46040c0b96188503064000502040174401203610000300001e00d403649101901d2901d6242c080503196042c020000324450009206200080301c07441c3c04024007058001c180c07402030070501e07600e000c0c900202c0d0700213030300fa0b0018089920501490007009004a841030203205030031142c8401000d50980640ca88a4280001d8040741c0032040c850300550080e04003120754000c0844d54004000080d1304500000303c105c5c840c0a500c00c9000054030b40300e1304507040e52848880e0707262040060341000740324041060040c2550041c007240000103454200180050f103c0c40340e002040d500141044c12111071040d03543d00820b1a40034100c181c10140914100c1c02610940d0802c000c10240e020620f0722560680c81180f0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 826011780 1250 826010530 826010543
    0xe06190b12190f0f05160e060906060a2a0b09030f2223090c0a230f1909050d020904260c0601030b07090e0f06030304050405070e040f180f 61
    0x440c0100e42d85580c8440224005c1c80501210443c0341c00501c04440701d6004030303a02419140c1407180c0ea85803000001ea110009682441d038030b01c007000c42034642070700181d4141d80c00100c20310111541540e00f0b0341c5401c6140700d04205041901e805440a13200c0c0605007002401c20000d221603281200d200d92400305e01b801c041c84c006c0e00701e80c031203d0040881c4880c452121907102080c0714042ca03814258111031348440741d0400c00341400f00c1184014a02e9418440525542c85042d508519904660089810446480da440d995506106035003900204101c41e124000c20143c20001529090900e0001c0121340e0041caa00c80a43e60b03542d9440075019001186451108012030345151250031600614030442c50710000c04c1c49601d540351810441c40000c0a00081100703012003045080001b00d0499001031107070410760324664400011a00d5401150b1110340c1c440d080c070f0240040d01c2d40080807451030050070344050040414450102060ba5104d50900740c2680c0e901c5000720101d58074110414544d882100b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 826013030 1250 826011780 826011803
    0x6050406050d0b0f2106090d0e010c0611210a021606020c10050a1a03010902010504150e03070e01051c1e02060f0307030606080a0c14030a0e06190b1219 67
    0x10f01244071802c1d80d110440605c12580901d00c4a81000c01080c0d5000350100000d001c08900080010040c1c104090030605008141c105a002c0001c0c1344c0220a1004030103222544407201c1802c480d82c0002c1c41180401c4002c1860042440480b003030089600d00e84005030b04907000860390341c0d128000e601c4034682126601500040080d881c009000e028000c507020032001c02c078440c0301001c2c020350015424006102e80c1c5030042a20050342c10400f078600f103403850705403440601c640303c409541201d103059409515008188010818202881c00c0e241038030340036038410105c4181d0f801a2686032818840c00382c00300a910026003a150304001c109550a44007408050a00e19200040d01c41600161080c0021135262071084c07020542c8111030030385c05614003005100204402d175018181140e4180c0c21841c0c0720700000080c20303042c40c603005100304105844c11030740d00740303803c000d2840403207070070160100201d00348840d1900a203880d81031320a01c0590500035003001810035143d404001400c1004440300c00030b4a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 826014280 1250 826013030 826013059
    0x6070c11090405071a030123010207031505010e070536061c0506240a2106050127050402071e031205101421011a0a06050406050d0b 58
    0x4101d9140282d02c00c000400c0524149801c8a04245080359038602e1500180700412200400b10290307000b0500340c0c440e451a040c40d64004074141290703500081d0100070606000110320310181d020754105d45412008210325110004200c51034801c101c0000284515a6802d882c0c04c0c0d01c20884e4000741c04521800d00c0d0494604e4081000d81e00900131080d0a42d81c0070350300c043c2c0c155881c022980c0c407100c125450080300c5d9145e4100c000c19400c850028807100d2020805c103c550340201c071094000c101c02c901034010140070100344800740105001c1c2c14000b82c60401404402c80c806410304191000051a200d1082e081a05000094000c50001d84500126140c0207501102d059800800c070307030182d0b4030000c42c900b0101050742030b218041d029189039081ca036410480c03901080620301c0078030411907020092000719106a450061a00c0b40c03181c803546003c150701e0181210710b40144441406541c1a508507a0b1920242e1711070185200e076101284040014024412007640842040c1d9070041c0603900c0380006 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 826015530 1250 826014280 826014289
    0x203010227030715271a0c07080a03230d02030c09010e27090a1a1b0702010503060d03030b030610061403060a0302101404091a0405090c01032703020a020a080106030506070c11 77
    0x85112050a1003c0000c040185140900c990070103003089c2d000503c6044081c0d07400600107000000702c4400015480c41c102111450001200c000041d04001551241480307800c5217056401324508a002c2209200c101da09400d001048401c0401050071358102480c080f1040d00807598028202506070048040c02c500203085c400740500c040c8038903a1003d0382c1303180588882c4420307609000d5018a0000600420300141e0340213040f0b0394030480984a48807440c66526050300605002e224113a4107000784000c10258511454200c821140203542e8401c40d0403544107c02c0702c0344000e89010f0340040e01c0b014180098104050b14405420075403501120200c030303142d42d11030f4540150708280c05050311419862100c418450182d000c0c4c041c00c50f0104010f0405c03000165a8000701d07044c2070305043e110200c00018080208118021900c10400359050381c0039407038020348651100d002280f241604000c00b203540881407040d5020b42c1ea02c20001d0402d601c0c0e4140c01c0d18040c040311030460303605981079400d0400b07495 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 826016780 1250 826015530 826015559
    0xb01030515091524300a1805010f0203070215061302070203151017033c03010305160e010308030103031b02030a0b04120509010912020301022703071527 67
    0x120107062a11208400c46910703104203c0d2402d420326207003000c0c0d60b8911054903038019811507686e01001a458140010502c881d112068000c3c0c265442c140c00e80da106010b54006621403071642e401e491300b0548064080d40d9004040d1070046c0c1002c07501e40d116581542d194020300205c2d000074112607184621104080e000902100c01109804824a04001d00400c00000c01016982000518200511080041031030482e10503000b4182103000c0508030601500d000140c4400e079030920301b55480da16401c2c110755030042d10008140d200003a1320001b842030b000200042c1626031204d0a07615503481c1d0745003214000c280c47c04d044c40240241c1102d40050790704102c0b0050940c46801d00d01a285018200201406504488042441003c0041610a84e406404082980e441c9a41d1000551060002ca130081c040c00c0f0031080150302c041000e440c298040300f400440c541046003114401034075803c41001200e11200a50f0118501c104104d01003252481001541824a81c0344c601507a980e41c0920304204 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 826018030 1250 826016780 826016839
    0xc05090603120313060b1203030402040b19090e0606011b0809010e09010303120b0402160308101a04150f05040311121903020106050f01171906090b010305150915 71
    0x307811041c41e200701700050040800035030341100c04403807000680082e03030740324440180001e1003070b5030303403516201c2d241e955003400341001400b022000742c001c1d05c945001c40202840341c9251144e00c910300004480c0d40c41035069040c00c1c2c03071004c018171101410380c0c0c4000702d617081010114140120002540c005445060b807080c02103000c1d1f56031105001000032241d04640d841c0400301d018030f00400c10304c040b01408032010300c00194036240c2040700c2e9680060a50181c0c440d50007800141c280c0b1208000e59a0086020744191500000c0740104c0f008050400e5032012091490100860002d00007000403465541215158107809044910051500d00c480c0e4200b082c03003102e80e260a02889181401e25a09210391000b4003070541c0c5500e10000300c0c1001908120071a10651820f00c002e80010784461448500181042a007071740601100b0b48406100c00075000c3d400d016070000e840d0200003803500311107030304244890b40c010341091550740f00c0103800d003085003900100366000310301c102982d078000140703100418a0700d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 826019280 1250 826018030 826018051
    0x60f0403090e090c13020418051510020a0c081c09030b191803051c2f1207020601030642050604030b0a0e0f0316020a151106010603090c050906031203 66
    0x45041240791480f4854002c8e491420310b00c1d18080004401807809a0070303035200111150031610100407070072071800c540e03c01e00410360b0103002800184803000041305400903000b910540398403013241c9c034100d5a91225100282c10301080d01d0200d55104401c00342203943c00010040441d01e5601003095034542c545603078044001034000540703402d46480710700e0030f040c103048006011b100400c8090700101e01d034001008403808401c1440c2600420051000840b28580104004920340780381400c1d001c2d465000c24030081d5509410074100d090240341c8060f507490303040f2201803020940403e103c01e00c880c03d05000070140c0084031850010031196991000340008510910b12400c541c603044668206403102d49410355003961142101503035400010064403241c660b2000144a064001d00010f08400380507801140d022030000c403c2c0b60100d5202050b01440032990f01200c503141d03030303405085085804100c3c01404004003024103210720325201041c2034105200a046558080002a50041c01d62090b101025003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 826020530 1250 826019280 826019287
    0x61b1217090d090510050931091703070815010504090e01020702120705060f0c0304090608031315050406080a060f15020601060305070c021c06021803060f0403090e090c1302 76
    0x10b03544440c08001821003600d544108452010014155004004420344509940350075030a280d8194800c0304c60400621881100480288201c500208094132050399100302e0040c03540003c54840c801c890140456a07203000c450307540c201480314440001c03891141000f0b020000018010310034001c0d0340120300303d14001640c840300703481041301110070305000f45180e4010080401895440c8070580b01466401088d15941c0e41600b080b940c15071003503030000000c4500d404404201a40000050000c04000340c4e140004207440b0b01c3e802011000440e07013080040c0381000144070303940c4a00691500a41c500078081640382d152035550943d03c003941c11100021400018907095243c1c10800103004201a0078100403608042c50001d2280078034100113805400e02650364586982003802280c1c03a6500803c0441d21005c074803180c8182c5000ca6030203940309204141c007241c00c90248420150145925448500d50301d071910240c91005000102210700301d0064070920006078443c403070041c907851824140142d6 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 826021780 1250 826020530 826020553
    0x4020301091505121507050403060507030903320703030f18030909050702060c0c150711010f29030708030a031401080313051e04060f0807061b121709 66
    0x418003100d6010512800892026030500000401c0b00310032009175185014043d500e603901910070b403007180e0006211500c0d04c000c0000541e8180d0195036550711941e903110542050ba0031a0324100f4a100036400502000078060714006e00000080013024800e040110b404400706000b001241c0200c502100400003141c071000070036034030000d003002400107904200451b041100b0000d6640e94005c0030900780c4480080d005000500030170400c940b4055600c0030113560f11b48030400800640e2440b0b1032006a40c00e2a000d0402c041c0da6001d02402c103038070403035040602c01307494403003004900d804541f664140c000e03503601080955003031004269500c1c0d43c0e01d01080d2038144003a20010400147e0214a20750810300c840551030100c2400d490446038200c070218040543c2d103070b0f081200351104941560161801300d002551901c0c4160000446403404195a5003d03940d4409603101c84c00b10001c6804149606400d6000035866540351014480c0741ca00440c11511041e200900d400d4290785030300d11503000e00040f52 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 826023030 1250 826021780 826021811
    0xc010806040b0f0d1a1821190f1b110f0414090a031d031f1821080106140c0a080c0c0a05030c0102120904230a050f010f1809020402030109 61
    0x103801149100380704401041c000d000580303c7c07a10030b1451000300102d508600300c1000f0130050301c4100c04d00d140c104454200c40c81e0060079840400c880c803004140403108180f0200100308018521f26000f43c10703900c08404d44020042c2c56100c004810b40d00990302d5074803600c1d02e00042002c43c0704008150041200000609000c3c0c401d41e04000c440c028031511a600700707220f0720042100d042d40380c5045090303491074003180c02e80d20183c8540309074010415111143e100601c07000112a00e410500c509400c84440441d180442d0210b50900a030404a14204010034200d650100105130201d42c0c581510b208030702a0747c98407100e071f1003c02c17261256800001d1415841c504141030714010042140200302c2c0744202c03030003c0c4d1202c2402070982507074600818000f465855940054200707807040000c080320031602c2d03d50103c0c1e4030016981903402c20318041c00100701c0c80402603044d041c1c07400703490000842854601407400c02c1e0100324030300910b25141d411070401030719a0300185002e4115007201180d00304a598048 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 826024280 1250 826023030 826023083
    0xc02031806030709090207061d0a0201030e070e130c0f120b07111b0a050907050a11120d021614060105030c0415030212031605011d0c010806040b0f0d 66
    0x1c0c4502820018446840d8101001d5800c07901c40403001740c1ca0f1041c0c1e0070100001c0c48000f81520a42d024603001011411010034500c8445100f40ca08010516581c441e0380d9850005014080c2c42030071000200300e200c46000b81ca1001c00c1e10031244111181e4071040380b028010002c0d84182c01c0440360a801704100003c0c242d00c160f0005461034651142254640015a0749000014200e0f044014031001e840366101d04150034042c200103400c800b818200a4401041a80601401c0c1c0000d891504000071440c00070820355120403848200b9400c3c407a000648a00075400440c541040c100c00a0150740054150300701c000c102c201c8074024043c02d6241c0400d060030280301c140c8081c0300328a0809400e01d0f0003541411503017500d405588002810720011040c1c2d2451041c5541d090310181510040020820150003414184284c0d41e00325040c4030159241c1e69460307241d840b52601142d84080080c0071802c044d03000c3c03010381c02d004107408015814000484c0940309a80016541c031103418400c0340002c840202c04 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 826025530 1250 826024280 826024327
    0xc0c1806141905121e03030a0c0c03020601030204050a060e07110705010c02061206060c031305030d0e100e04020913061d040b0c03061906030c0206060604060504060e0307090c0203 79
    0x510915800911820102c0b00d903002d507521803038083e2100b5055100400a48003802d008100c0f41002070440102990740340c00448070403100074245000c85c4034403440f0345410501c19505400a200a03401d5038204801340c00c1c020f0141d0001c598806000a000cbe00042405001c2c00c001c1c0ca4816081d04040e5809003805000e800c564140212269045c0040c0c40d50800c841c1036043d5900000c0c1151a0310b00065030911400205a06c40e04c0081580b420800d03c140e5808201d070f80440440d20164103810b001d4810102a0607080d034030010707818540c14010302401d03038402d61200040c40180740118040c0020036132226112080318465403500c007404141515034079008484044a40c281e05441c0c1980c0d082071840d401086141c0c0f02ea00440801d000d40c80d01d0740c210501256064070440100d0f19001e009000b40420100c0d0401446400041181c3d07090601c03c64040e9940c80d5240b9150a0a1a406550400740c0b04103140d0984548240003030a150680308100540541e540616a2020000408800143c14500 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 826026780 1250 826025530 826025539
    0x9030f0106080d11010e010203010b0c01051006050904090221160b070819181d07080408191803031e0203040810050a0b03011401090c0503160c0c180614 67
    0x1c0a101c00385001420b1403048081e49416a100346040f2110380c05030409050302d0411350300200010444074640c00182c40a0405c4100801060342c4201081c912060a885607a01055081081c80b200e801c05802010725680081c004010280f400c0000c2c0307400300c9a8040106194101a141045448040c81000010301100c40007608140c17154a860391a442045103d00400106c0c158980e4928096114088403860b21400701400325592032400d03c852402135a44001d07038819400103190a8020b85800c1d00a6411104050800b03402070b91425175032003101d101d602031140704c00c00d25440f40601103070200603501c280d503041c100c0d9100d0316806400228405005043d5002444240f000440008104101416042c0c000c0f40540315a01400002e2014466064255090414800ea6445003c1000c0d040b564130750810084005278003011241c6000c15620043c0f0002c0c0040000101441101d40050701c0e80160501c00b1000e640748040d03020b1404038041c0d80032160b281c580130460300d0310b1110300140350300007504c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 826028030 1250 826026780 826026791
    0x1215010f02070f05040e1002040b041a121503010207050f0102070311060403050a03021c090309080c0105041805041b23041407141c02030a1512120c0c030809030f01 72
    0x1001c0f641c03806050091900440d80c5d202c84041420041240a800302e00c0240210b50f00c5484282150742c581c000d0040b802e00030700326a4456503030304140b0121000b06107020b02040b01c68451710010034000c19600d00d45541503400703100c1d00000c600c051100c401000085070005a4a001518000c1c0c40d0300502c1c1d1410b0300c2c1c0d8001e1002c0202098011040391110a21450016550240c807400ca02050000c001040d0300d003864840d80d10101038010303458030259141322040b00c4081e5400401114035100702e019a44848150380e500c0100301000b5000f054205108014451211007a00004015000f256000d13261142600d825040540444014810b1041050364103208a0034800d030000c0150f0006030468040041440c0400300001c01304041d15a00781c541d102c68000c001054206e40b0103500103a8032801940d2a241c2009094092402401c3c1143c0c00900b0a041a80240e202d402c070003c564440e0209100019800200048040301c0c0e110166201d01c05040e01c031300185091602e0b02018101c103100507031508 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 826029280 1250 826028030 826028039
    0x1204150b03060c090126100503010e0304050f03240a11032e090507030c0e06090a0e100504020403030507060e210c03040b0313380604021215010f0207 66
    0x2007011944500b0403c40f641d502c02c0d404004907005241c4202c00f4811040b42030b00d074040c07404802000c600407035180c0d24101c044c0340c4500405080720180149207040c0d034420002040386040c800c03095102e40705d004041d14100d030b401c2e890301c00a000003c3ca1090130400322030200b1910040034070850541c0b243d21410740e401c41c82c210648140c018080c6210502d044017002003945000307205007440014115031f2000b8010790900791f0780074015107044240e58000c5810941d00320600e050940a40d01c91071001414003010340c0c5400403d10991a0180103403500089840740844c007511140000c0000398403950720140e8801c0941400300031160b06140441c0d06800400c1401030400d80e617201030300059821086c1659401c00641c0e400d15502c5180d10451801a0100401400902805210402d00e0181518a0101081c9450003802c851b0203c0030200102d1010b505001c0100007103005980014003a100601d00484402c81e00b00c0000700316480d120004d00b141c070008441d41c0c0000c1c0c01c80c421081d80000d000c1c042c1030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 826030530 1250 826029280 826029283
    0x60a0309051b0918011d010203010f081207112106010f05190308030c090a08010e150403080c0904060b03041b0f051f180608070215010501120903141204150b03 70
    0x1800d036202c2960548502c5608040c00c1d4001d044d10f003030396022503603659452086c50380030390424801e0041d04590310000007491100410041141000e1007117540c6058519907a050400f0424074030070350400356280e2090512071014440310200784440b4002c00c070a6240810740a41001550800b07170189000ca4140d040b005c02e83c56854050b65481600d442d200d9442e441c8003c80c2e8042c0c5e802140d40000c05a80000e0400c40c198000a5000040400c0d0f070f50100800c4a019040882034800a000441040016007800003030005003002c06402880440c1241e03603180c1c905e21640007a07406a41c0010640040707160b01002819078001486054241d914481c40c050008800d042d41d25109040f41d804201d161444a01c03446841000c0003242c1f00355200340340c45070002440000c00310f8044001d0701c2400010055590102d1885048940585d6078000c0c410364520414040c0400400840c24000c80501c65010f0181c80c07030252004595049816030103180604000c104030030500c8209414501d400103000702c5480 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 826031780 1250 826030530 826030549
    0x332060609010e011101180b0a050105063a020a081602162112050a02101a0d15020d0f060f03050705010503100f06030203180c06091905060a0309051b 66
    0x3800d0074044800b07000280390324050161f200482c2030300d0001402680400090080701030194810090400590781c850050021a100340c5690889041d80310f188e0701241d403d9100c00c920303206d5034046504800303102c0d84000e03c02d9030402840840400e07142401c001074041c00300030210740c2030240d20040810010115082c00b40c02002d0140c4402031444800e00c1040b40c2c0303840042101542c0c800000c00660f4506040284035420102840c00103004154440d032000021340150980d641c01d05102c9085442c004d020850300e000c041d01e08035070010819200d408030070304074070140101615582021403e040c01c0844c0b002113584540000000c4400000140301091000403500c00740c0c1c1c0700b0b09080703660792900a84488182e006510018403602004c10214103964907801940c020700d201c10503521400c0c81100b82d01d85030111401016044070b0700b400990460f10b4050102c2e000c04110301c034032401c1e1544420209646901001204011940f600503039010010208400d03060003c3d1281c056012080550015280d180d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 826033030 1250 826031780 826031807
    0x3180201051b1603030f090b031504050604092a170303180a080c1b04090f021e0d140609120403030c060b04020d0609060f08100507033206060901 64
    0x40362840000004941040f110b02042c040c1c52440c0d610b2681d038680144030640f0390b1100300005a0038840044c00410344820703680240f26410300c0b10304551040c000c1c40010300c40103010070390068403078041c40c0121742c50141c8c8030040d01c2142d0014002d9450154042145c1034070350310080110300001090402e10101005480d0031142500c0100000c26a4200461400d0786012014107503120000d02c00c070740d1110020b011142320007040254501580c29a003000121580c625020700ba2205000002c40186458058048071848a4140750303c0540780300081080b50702c40c10411100441410300b0703401903420070010260b12041c00c000074640301e5104500942c4501591000030244056400d541c030030890b0940041340c1e550f401400440d22081807110400150165110341c031038036840c14101052245220224600f900e84000c002d0100d5128424150000d00000340a03100f056079442d04040c0009240e0071400b0303d02c003000a050400c0081580101034803901a0000d8400c081c200f0045201f0317604008816a1311 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 826034280 1250 826033030 826033057
    0x108060d0506180a0c0609050f04020a020d0e0a080109030c02031e070b0904020d0e10060e060319020a050d052a0f06070303110a0c030e04060b03041e050d0f0318020105 74
    0x1824581010340c42c01c00c031341d8030003001400080d0000c50000d60103d400c03400c480c401c840c030060074004c000030b00c01284981400800140c01c2504000d080a000302080d1407444006090503410f19603d10006003110500903048000650f44103241c01507103010448a4241161521700b1110b60030030021866450000d032189640c2c4090214141840e641d569055901d5521106014400e001951340b03001e842e030f080039641d00781302d51808001250000001d81c0061140c140540140040c80c21140c5e050030840b600903040303070720403407500b40070805484801c88460b04512440040c407101500400004800d01c0440b40c081c3c114088400e035410b00d0b543d903c6e0301e128409080c1c032441c1da20a2141001c0780130302200b00801660560004403204c13a40d520044080c0c0c1c840c001da40b5000301c44c4030b200402c03007511081d00c28068240d90a00228002c02c4084904c02c3c1041d030841d000f544151000d41d100c81c10308041840000c046000c200b4102c44507505805080c8000304203000d1903200c00d846600103080d6000302c078000c900c007 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 826035530 1250 826034280 826034311
    0xf150807020a02030a031707031118060c0d0306030b010e060307060e01020c19050109231c0b0103030801030b0a020313150b12071401080132040510050108060d0506 72
    0x1000d00900c00b07007015607000b40584407101403608002c0c042d00080103404610f01444800a00d9180c400e21a242c481c0507000d0605140004600800c41c0350f08042c108035510200800c14150f680c13070100246c2048211030b8901140003891804d01581c001c105030700c5125910300705000c0000969010500b80151207903428840032600604004038900b41c030034041e43ea04022240340003401e450240028104a4800f40e852954891300d0b1184421201c00060301211758140071401d0600c3c92800c2c06080c0c004040c1521030390030384a51034548911000d401c0e841503020a42c40c2c80103100b4400300c9190241c0c08481c402055240d41400c10546003041035030700d000303015203141200340280e5440c00d0700b100205420041440004680004100e51200e0b05807042094089a2840010315075005008040c100c0790b0710103013400100c03080b900304c0ca0a2000042c40b5003031903c00300e00c800e44690b547c0c03181320b00071040c81c200c6054541c06c020000d03003070107009403c152181103942042000a41c000408a0f0710440f00c0d11030016 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 826036780 1250 826035530 826035541
    0x150e1306020705060703050a0f02120c0c0f0d0e030c1002190203010216110406060e031009080d180b0702010623030c06030f0a0b0a0308032e1706010f1508 68
    0x74010b500c001069409110f05004005034150000c0340580b696850800c00904010140c1080340300700748070f2500e001704240014058080b5000a4550708014038180c0312540c1c0d001d0712160615401c440940080340481c0302610207828100308072a813150040d100060a17000006020355a00d01d19150210407a61443c02803045440c2074040d80d14031740300c00e020420900400d2900c20448054003a105000324544a00020110f1203030342c482c051010060301801040d00803540070006002c0e1000b0580320b6403010003e405007070210344580c03c55485c4000c1d020345941d171140340604148a0141001045a0604d034050080c1c280d001d0078041ea03030366448030310022414a071002c80d0412900004590380101c0100402015181d00807001b48100e4150200b0400748030140c080120424260002420825090000800300c0746c411005030710320102103d4800d0540b01010240720040d6903031b0061200c414064000c00401d540c20400c00c0e026081032540b105a5600b05a801604a124450340000b0803808001160 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 826038030 1250 826036780 826036793
    0xe16081606050f0c2803030b04020304020108070c050a020a0b0c0d020705060301090b030106031218060f050304020f04091b080c0a08031e0f03280b010801030b15040609050a150e13 79
    0x851700a40208092070101c00c0c2c2100190301e0400d441c1c103a01090a2403170004603841c09108591140d5416102c10480d500e0304482100c41225818080310984541c0c1d40c0400541c1d5191b06410007840800a02d81c1e481d10303201071090811130b0343c030307030b03c1c020b540c04808140142d81d00c00003a00e0646080351400210380e0f10b40c41c002409801c0e96400600001c0340540c0304602c4680c480d15010243c6025001703820700d5030b1f0301c0e00115180c48a083c08100028070500201e00145040c20504030340c140b00070b10200f003100c1d0342e0701d811181800a080b50104114001800c00c8440e50a102d000403100c0d0848421071160b14068825499100e17152202c00d4640d40c01c3c0e8118402d100c00001d40d0314046105000f00c2e01c0349030800305100c40e5051821910701501e0740b040610a211505e01603044408030696603c0b10070391a40e500c805c94840c0103021464916100d0f03450002944030b038455034008026101c0d02003060704090b15024205d61481307035441024456510103003c00b00e94000c4941c1c000e0400003e0114165103414000c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 826039280 1250 826038030 826038043
    0x406120912051c0513060c1b03140f0c01050a0b1c060c02030f030103080d0b0f18090127021801050d1103011104030b06400e16081606050f0c 62
    0x1100d507501c1d00c0140f006450032040e1940200e4400c000801404050700c0c0113484000e640c01c1054400444426032303d001074030550700304815004d0000c07058100410030900c0741c0c16170401e05101406a549404000b5020703090b0052030b0151100f41e0394076242c501c413260400d80070092100060142d03900c81144400280c0f08104540c56806c0c1d41ca001600c0b56100d26002c2c007a644000b65450b031181c24020018032a2a0202e00300d51464001000c0341c1c04500c00000c00340403568000d08104840d5030320303110803000c1c05282c4071001c00c1c0c14003a03aa011a480c12071040180c2034403440b0014109606102c0140841d1319032004040000c0d8001c69115082820407000134090503045e44a204410800b060000c01c100c1081c2c0058041e0900b11002010710720201300780c0e03604d0061424000740d00c80d15030751141074601f0410020000b00203201d2000c10b40010500789035141005005d80d08601c440310352010808000b051080b8400c80c0042d40c0c1414030705283c810001d280d0f0041e1845441e16610005503061649002c0015 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 826040530 1250 826039280 826039327
    0x503101203050d051509150a0f0b0405041d030a1808070b0c010f0504441b0c01020319020c040c03050702070b160b1317040612091205 59
    0x6894600301071030010403a4000d440340c88011810132010031901400550b01130304c1500f01805070005940c49100007054108030400c010307000000418081000350760300302e042c03020f0300344450b025981c1c0f4070702000e0000b12039018450000d4040d501a44c41c0d580300c80401107600582082c07410400084040c0b41c04000113182d54005c01c543d2154110004811481d407014080300c0f8600b20080007150013642290b02a80c1c4101c40c010450031848400c0044480290a054048007000c851980030000074444580c8007062004042d0311010046500166282985400034011124001400b05030b41c0500010b0350340c1c010301409810580040f0101c040441c800c110815105400400a0004d40395048010300109000c0e03890304018080d41c5404101d54007480226100840c041402c00c10018007903c40ea4420070001c2e159a465041454403d400f054143d0703040e8041e41c403038464859071036103400e9001d0810103003402d1601429042c100e0000104100c0e2350303468070001080c02e01d00d070303201405060f00700304e034004684 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 826041780 1250 826040530 826040549
    0x20103020c030f07051c080712051e012303160e13020409060b03010b010905060f0a090317042105030921101b05120a09031704030e1809070303050310 66
    0x203050090010001b920900124540d10b1044500401e03002100d502c4811100c00000c5003031492091803a218070780c002ca81c050114103800004038441005210681e0081e0b20243c6c011200c1c0e000010304180e048002c0c4011281100144541c4003a0070181441a180748512268002c0501c0003620301800d8105240d05076500500c1040b414090f4507141c0001e1441c0080140650728100034082d072035000e281000c003541e03002840a07041c044901000c00280d031040f10340d02c4c01c0014204000000600c6c0b4000521016405240c55440c0c500344010007000300c13040814142075240040002c0b0110310302104854002c0e0098545800c0942045240e080c0c282805814003603502c00e80c4150700d007601c203a52161f6940200001e07011421502c3c42000c076080d00800710140801800c0d1004541039040340d50040c0c0e1054464140104500703450401203004000c111415070104000d080b03070307134150302d403895008109980e2103022151504101110a540d01000d01004003802400030100e24200c14000d84007008018026 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 826043030 1250 826041780 826041787
    0x433030b0607240506010e06250203070b0d0b2403041b14030120090d0515040b010602010e0703032313300f0b060103090b0a0501080c09040c03020103020c030f 70
    0x10504111108070703e4060342403030503000c0759080d80b007900e00c90f4503505d00921090903d20915054424400121009800f0741440e400d02c400584003803040074020030032985540d031658a00300d0404240c4007110340c040d104180801c03400d01900f18445485010221442c8450f4a0341d58900d8411824821003010790008032034030200080c8c40f120314040070312140c015002404448031400c0720021ba0ba02c5070040003010714050145141c10304101d0f0728400018002c504460b603401110b8902007441c1030989054901070352060050100f00e03024064030800d64604001000d6081c9551402010b480244005501c5071400051010801d071001c81540c04100c600c806a8000c1a80e0303110b401c0e09460903c840401c0181d207030286100d41480342442c044055042500003803090000e5548455030400107004a051594070a000f00105000c610594801c0d8110080051154142001c440c604540240d0140c401c0d40c10408000000b081e04030707103000300d960a08015840d482c81c0390b140e60844c041c024244003480400f2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 826044280 1250 826043030 826043063
    0x305030418180c18020f0909100315020a0809160306020901031d0109060b010504030510050406020d0c0206060a080307030509090c0f2b050103050d0c060e120433030b0607 75
    0x2003800c80304844d0100d40c3e8604d4013640c2c0b40c1c4d5006900842d20007000c5402c06200a0525040c503000590340240356004581940391241d841ca0341c050241201d03840e40c1580810301000c0181c000c4500c3d900040ca100041101000607031a0400e082d01c00d0000a0000d41c010440d991240d0081e00080750050604255201e88881484141c0c020215028156101400c1041580301940903000711020350307402c8405044079080c14600003018050140c02103070070543c20011320400040302d20400c1c4d82d42482e03901920701c0382001000c020001c0240d030051603580d0002c2100d01c0c000f907004401c40c0c0d40c0403001d4550300d407665201c100e58003481c041c010740700706040300000c2e6000109048584442e19400050048400466500520401c4850034040241303d58421900c0d0740e204c6015245805095216020200b00c1c1c00242e000c0030b00740307400500365411215003c901840200c0e810807050780020b036401d00078003c08141847c080c08581080c00c000043c10b60300c00f8900b446803651421102481d8220503546a030310640c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 826045530 1250 826044280 826044293
    0x1050403050c012a0506091b1e0114070614061005040e1e0c1c020405011704060b0a080c01020f030a0e010f021002120414012c0309151c06030503041818 67
    0x441e10501c1d58020038984c02d0501c00a00480300d5a404080c003001051390700ba21086200c009e02c0d000320f60612560f507000240140030301c002005554030400012801c850b1059903a84400b10261100c0d01c50b01c246044c1103081640407040e10304807400f42c0703408115038984450340400c444010340c20b4100b10389182c080000400c154030080489220881000200c60413a0091900300d001e940146400100c8074040041503030380f040c082c0c5070842d028190024042d000c0d0300c0011301d0b1086d29807201e19507420007a0a80495030b01441211011486080694501500c50400604c50100300380c10b01c0c10b03c00e508070041d800c00d10070042c541214004080441daa0b03c3d012007c80e0341505c1c01c55088901c4094a0b048106444060251404012070719442200506545001f12440321480d000c582c0c1c2448103128508050342c0b40070703030b4580401c0000800359a0303000d050920f00c1c24071141440341080038241402000001c13400002c41d000c44101000710000e01d090000000084c0014901405d0019540d40c11a0180b042c1d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 826046780 1250 826045530 826045543
    0x6120f0b1f11070f180e010f0e0d0c0203122b0b0f01050c1f090203060f0a050c1e090f030d08010905090f0c060f09190305010b01050403050c012a05 65
    0x40340c99030448001c020b003040350340c0c01e8076008022500d10140001c00152000000c441196170016101198140d405044e00b803c48042002c01c205847d11480d2440e0000c5051008043c112041d2412107030b04102a004030b1780d101603520000722004400508102e03c504240000004031041c10760740002000c041101c80090203405604138403481c6017a042600c0c542c0540b0440c0c51407441ca00c00b82051885551000503120448441c40d2aa15140c03500d4800698051100c184520400305400c00c040c03d20000b088100e410052086002e801c0c1007050200d0311114003901841601862640da5841050724040303485000f5544405806206880310140c00e25001801036058503075030032042109684c1d2040c615541d8503208031101280d0040304075040d1900b0424024000d4424071010f04d407401e4105804640900407500d45040b020115501c1401000428021114400030919049042c90704544625071600707481c111203414444241d4081c5900f414844e07031405031411158005001081c1424929150007 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 826048030 1250 826046780 826046839
    0x50603010f15031e090c080111030901061403071202010905090721020a090e100e010602030703020c060304020f120a060606050919030b060907050d020f120a0606120f0b 74
    0x3080302d4040c0e82c0881c4603102d500385107454803500010241042c2000300c0100018201a102090600804500b07a01b0034010304511900b26081c003603880c5424003104e82107506580040400c0c3c001e800ca903021580d0000341c522f068a0740801c600004209034801039607401142c0d80f089030010101d034108018582c002c64200e580d509042c0c03003668401c070740c400c0d046c08910a2160a001281c12807400b40070442020310441e40c02003000d21030382882170b245d200c8116442426801400140d05c002509410594184100401400103556807819400c0c01d0740041e400100d0502d165010b40c0301e5041c0385a51020405c002c84003d41c00002c00c00000342c40302c00007030096100701c10307060164201c2c8030120003c4180310000000c0306c0d00042d03000c3e1b20340c5804041101c80e24010302030310308001c0c0900a080e043c1400b8030007040d00b034024041480e580c80740084550002980180124035451402a04018003604200c1d40c0c041d405100000003040c0441003034042c01041401c2c401500205004c10005813610300c0c000481148 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 826049280 1250 826048030 826048049
    0xc080601062f102403050d0c030512040b06190e0a0b06130602010b0a05121c2c090c03090628050a05010302120708030712090b070605070e10090308090a050603010f 72
    0x40300c50181044c650459200003032556100322030449440344201c1c0d40814881c464503100d4500313100c103002c0220115042d44d098520f04008000d000076403400c0c030304c0100c032207140381d41c4503172064a007028811b10360100401c4a04a180c03141d44c00c1c5460750300d50080700c014003c0058030010700b070340b102d1300203009114850755540581040400450b9038500b42c0c002980c64488036000309145104800000a5a100441440c0502c0a815081c078074811129041c075008140c50040d20a040c1d07840b008110072100041c28500502c0010410b01480340b41c0890650703031003004a003941084c01609180002c0c1070700c5001c3c45060b603d00d00403e2011180e11904154102c038000c84000702103d1703010b1394441e1625128400e00e40f031039008100080000b180b61813401302144443c10f01200c0b0765501c0b810b240c6c01c2d5204076022180c061342c03101001070080c0c11003130b07004003894144d8010281e255480c0014121114a02016116800108001820740e4450f020400900300252900c0d0326965a1024448001c0440c0500c5402 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 826050530 1250 826049280 826049321
    0xc120c14100b12070e060607020414010801020c010c080103120c14010e060411060903030d1509020c2a0a090f060510021b0108040c0504090c080102030c070c080601062f10 75
    0x1011000804406a4030a150f080170180c40e0001002416840500d04980194031201d20201282c0c00301c00407130080800d0f07800540d0320700c0130030806030855440c0c40d01507051142030801070010a4001c09503140d200510b08103030345400014100b400c03600c425809040303c250701f4200e070360807900c0d00801d200c0e01480c482c003002c0e4400990002005850302030303002055010340c014041144285142c1d00b1100355802c40000e40d20000780c0364803c0c2030a0340d0060000020030707400201c802c3c40a030f442d081c00d582036000650207a10485403031000602c680c07000c2d21445003c01d4840c045c88170889480d82c40716000b0b00c401014806101c5454402075200c1d02d9004401007407901d9000007141c1940504204c1c1d00c1503038041840b00310f03203007001d0801005003801003050b106858007070000324040da001d02c0298025090700315030347c0d202d444a2a21010803040f42d00314100c06e801c01001007140b950031560303940c03900e0094000c0c0300c00d0203621455030071003041009050300e0902c84c0b00c03921a443c0001e940408032240308a0284600d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 826051780 1250 826050530 826050559
    0x51605010e04060602151306050c30070c020f0a0312021005060f061602030703030302220806150d050a0c060e19090c020102090a080f07060c120c14100b 67
    0x483d5800d03c07075070002d40c01a000e104041c078000031086a0000c1251400000000300e0748601e001c4407800c0b42c0200d441100001d0300c01510203860f0207054514022400f59800c0c03905072109076132850002e441e001c10300400c0d8110004540d1b071000007070b55081e00a410062402e0f030700e007050841c80d0420b40c1800e0250160b009088028055401242e10450000c0c10403040c0490800c04c2c4903455120084220800482800c0303c0016941480150001c5010f9500961911840030529000d01c20441c2c0825403502d11210411000e4008991940e10400300800424102d8142020079594805800f004220340100b92211040040c240c05040650f000e0b5903803c201103499005001c0704800920341101100d070004c4c001c016030791b500d030003100302110944009402d0040c1c0703001082409407a50001005500101c8405110381810040240203200c1440d00c1c0140783c501d0b88070380c0c061803000b030101020030440610f10018025100c1c200c030000c1e00004201e407046035000400a00401c1c0e4281c0303061041031980b42d07030403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 826053030 1250 826051780 826051789
    0x5010f0807020c0d03030f1406030c0a0612050c1216030f0b060d0e030f0c01060311061201090218090717060907050a1d041508010c170411010309051605010e 69
    0x1407141c2070075002010f10a6a02041180112920f00f00b113041540751680c16214103042c1c0241e102c070300d0050207462401c0c207110081505040400d0303407450040103118010856194040d00c4001c0e0680003040c00036003070301c4002c100300311841022984821100380707805224007103d0103410070510021582d0104a0b24504083c0c030b41c03e465600614a40c400e01c20300200d14101010703440b41018680040c1203030301e45482102c00404c181c0000c5904600ad964030101002801004042c03240240d500300c1c0c075945000c1c1200d031000d42240040c010185520303800701d8883d0520110103406030545400802c001c0310392402540007007410425030480c030040d10410740451624100602d84a0054225442e85401d0941d5284100c4811104440c0d0015486002039114280c0d00c41e0f2050914051100a04e040024240114142947d8440da9071108000204100000030b8000c0500710b90403c1e4061700744442070102c038004070007405282c3d002403c00d020355408101c46d8181d4404a804880080c1c030386140c2030500da402c00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 826054280 1250 826053030 826053047
    0x10060f0e06010e240409060f0f1802090901170f010506010806010f02120706091416170a240b030c06030403030c090b211f150c06021305010f 62
    0x21403080340401040c0c03198003410054821a501510850b03141e03645039401d42c1c0381c6000e641003844400c00084c1c24084684e49015160180c02d517a014510080c2c5003183c0f540c906a014130405607031b01d054001180c0801e540e80c044bd0f42c1c5100c010891079203541c540c81c180f10034054050a4000ca032058a062000640041c029148900c505031901c805035521000107440118440307000c1011801b6210014800c184040083c0c2030817401081c00244840d4545480c094091901c003400b509130b8000c141c0100c2864240300800190740d002e02100c0c0c02c03041c100f00d88a28012070460020107840030b2281c645c04140b00f80001d401141c007a40024070031107140c0070601d601c40c200d50341300300c0e0040740070000100428042d130005000c5004a01c0c01094a03941d0f0356440d065500152014480d41c5d14488c030340492060940306035500149140d0742c100c14100307004082c01c9140940c1c440e6610300d03a036480c0c5841c0524020902c8605c5503410a8081d0340d40c491050303450802d840e0078001c8501017814800543c69051291007007 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 826055530 1250 826054280 826054289
    0x1150503010b0d060513053304050c040218040c0e030d030603020901050f0111061504060f08061801060506070620040509010e0c0f19020c010206070e0913120210060f 73
    0x41d8240c0301c10f0303921607002400e0300503c0c5501790714804d0406000644100680d03041c52907948040000e101c80800e41e0403802100804000c4460408400e210105601003079400c4034801c11075006a40e000c482c610340711007545583c1b40c19400ad00e8044c0d0b050146801009040141408506550400d420100290708440b0070340800307500003070344100600c1541084034101c51071040506103a508201e40031499460200b080b241084044240d08100196050078042c07000940210241c800d2100c1c10b08020340c0e541c80b8010241c128001c03401021b002280001c2d404000a00130103440c0c0b0f51f50340143d04110b000742040ca01d1244c903902014000198034080e00702920180c1c3c030010300201e926460301d40500d020407800741c40003d034480204400100401540c2c01809007454098001007000c04204001e07081030300c0000d00c1415508600100b001035584141c0d80d242d2a00201c44000c20b41e260110034688074034080c54010b109200b554081e080c1da42e00003451001034004500c0501c00d042c1c40b0400303d03414090034842c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 826056780 1250 826055530 826055539
    0x150906070c080705010204030b010b13090209060d020304030e130213080a02010c030c032601330c030e0409080301082e0c050c01063017210901150503010b 68
    0x80c1c1c400000c4001009003400f0b402400003504140e1030ba100c0354505682a032000b0b10120001030164006102c0c201c0e080c0082c0409502181099480700205820307110b842e400240c490360020000e820103009542d14031075100081d10200103000c08051348002580b011040c41c1c0460603038070000441d03000c002002c0104540c10395035000c400130560f030f0980740d0302079019040701804500607140600f221890031550f46461411340d18030103945090542051600c540c44040c88041110b4102e2081281c2508150002106031500c51030356052414102c60307400c0f04410641d0310604021510041c0055040598143c035143c0c41603491b50390140e05a01800c0c2c40c03222071100d035003240403000380380d588856118041d00c0340c150405520b0311014026050131210740e5008488900c2c40d00c004a00c1ca0541207158503420503082c4500d265031a43c94031500c000d180c001d81990400403000665480d0003a40700a08003245c4041500048036040030482c40d400703842018502445007031458000240d901d81400b4a20001038003a0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 826058030 1250 826056780 826056797
    0x10050906150f0c06040c090f020909150103020705030f0307031b020607030c05070210180605180f12061e0601030911010c03050f0403110f03030301050a140a031415090607 75
    0x40724600160421180c4014101c2d0038400420f0341c041c140015841541300d40141032010f81004010b400311000d4488421030280b060040914907240c024200d074003c05481c40340ca142c00040c4004074040d1191b9400100345000108007901048078605c041c2d4010009510140404070400d0350010425070715001410041c0e00c0345001c41d10b510b0207540803800010346841c20b689840156000304041c000d9071900e840018012800244080c020760300800040e10041c60400d01d0700c0f0041c0d4940004400b400030280c40350140350421121a41c46a1007a0f20090101c42922000e1502c1603100f0480c003003c40c0300c4d1115260f1000002c005610921a811030158401d12680082c04883d004640c00022000e044050003030401803224050701007005003005611510510580180e84409d22003184a80081c6c54000ea000f0310061110f9030302c40d80050b080e20509040a026680454009807183c001940040c00c00d20800701c0c00610f1520105100031441c42020200415450301c0d100c0b40da8031441100c58000040901 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 826059280 1250 826058030 826058059
    0x9030a050f09150417120f04050f06070f0804061101091e050c1e030c040e0601360606030509070e0619030c060807090e0c090d0f05010509010510050906 67
    0x10003404290703201038a59924003200c50640c00c0c3da6800f6801540d00001440034003100c40c0030811014a168541e007510b51f05001115210301c02d00d0146014007889080804010341035610703a1070596041c1c2e070704401200c03514009414042c3d5240d020340603031400201c11000300c101c00c800501501003aa175205145808000f0001e006034502c0b0035142d0111040e000701e0140981c180da45d2520700000a0000304e401100c508600201460300040404490007a42841d05050b0a9040458004e0460701c2030116030420171100004101408503025082c40003041344404561907901031b5120b0020f6908a807000c0181d030b181c041409030780e080948503001c00c44041d18005120b0b420684182d001c896148044804096200d5440300c00005194020100141040040007840e5070b0064144008156103228404142003880344d031034951141000c00350040490100440070460090144841e55820000802c42400d08100450281105075841c514120209a0204143c07034064030080c080c2c6001020440b009012 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 826060530 1250 826059280 826059307
    0x9060f090b0d02160b07020c0102010e1501060f1b26090a0b1b070801090b070c111011031c050132060423090709060c0609261209030a05 60
    0x10929044440313508110020010b82201c03089801585180c014009583d44100024212202075444101c5030340b1000702640b04900a90700c1340d064a85920704041c20700d0501a06680007081c45070910096010061400f0a00003081c4101d01c1a0012a03101c040c000010981c1c087c0601a103a03105900c4200c0d80004c0110b10f000c10010000c2c1145c5086032118005601101c9040c03c40650100700c4a945444480f001c1003010f0000540c81941c1e424225a1310a090710b8410304507032450002c2e40100c1c90042e0f00c8403d50300420b50031020007101421a560307031070340b1020103001007041040f81e848541808000b160303041e2101e4107900032083c0440c10300552010041144902c689000d42c02e9085042040b003c5070300e1034901e400c413003000d0342d92000c2c1d0701d170740d001e1024030860100040c60b95007000f0f500c6009100f101d5101c008002c2042e04100041145000c03400c0440070799615104c107800e40303039a070080b00c0b52000b05080681100f0317201140280031503030740c60a026143d11603d051180010010041011301e542e0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 826061780 1250 826060530 826060537
    0x60f0a0203281d06180d050a034b06180f0f1404030e0603010f06050a03060f06021b120a0b041104020703031e06030c06050a020c03030a09060f090b0d02 67
    0x1c2000c00070a2151641040d00d200c220340e4841000e00303030415402c2209000801025640040c3c1e004014070140134046c20051650040c0d041d03220426849400900c944403101080b10300340d8814800808045648890f610403d608182403881d11603440500c2c039410031450b20901c41114078056801c0c1146415800880003401703000313002000349507035000840e915032481c441c020400141503402d65160900f030070054540c50100503210711612007000140110085140000100d03104c1d03041c0207848801070b01c400c0d4090510b68001418440040900040c2d00368002400002402d28003142c41d03000a0950510000da61701c0302c892000350703011340b0595000403d0548070f240d000303014850107409200407074002002da83c8106000c4c0c000a4841c1041c88049035865220100c4000010040083d03a24542d0340d06074229052084006102d800300c1e5000726a0300034800010908001410f49503174078034402001c1c024504030301504001941441c81614814012028030094801b0780e800e440c140403078021306502a62 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 826063030 1250 826061780 826061851
    0xc0f0207270606091d0402060f0d23100605130512030c0601060903030801050414060108091603081317060c131806090e0c1f02010608030c060f0a0203 66
    0x103050050700000d1403103481000041e000030703941d0603e824075018a1040400080b00143c41c13041d980000e00c001a9110004c4030500c95140d03010544800c11074031200000d001c40b0303103140440b940503041c900d0402c0c1c000404500c2035102c0306e603004ea00754031040103e980b402520b0792104000d500d0001440546409001c100094a0400449290142540026040640171b0b0f028001043c52001d0520403d9001000f05014000582d020080e0301c1d01e520f800e410329603015040d103040c000c0f6070300420401041480140c07160803003609007414055a03440c0000c1160301904810560042c240340100760860000e00141c0a0070200c40200f1240c1c48002d4060070950003400f4030903850140d10800141e0000c50150344030201401d05000800c50320b420b20b14015500c18001c4500c881d041060100582d41e00d10840a2004842c94000d280100c0311000513401481581c005032000d10001c14852041d00002403680d00c1b07503d429200340c0960f203841080742d090707000942c3c800c0601801c0507542c6d01c0907005407002c2039504 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 826064280 1250 826063030 826063079
    0x8011409060d1b030809010206060609011209030306050a0609030203011802030607110a0c12051b03030a05130e0c0c011a090f0702013e03041106030406020f0f07060c0f0207 76
    0x10411107044000c3d00c103103580308440c44a008201e0000079a0184225980078005983d81407800b1000c04c0004d00001c1007c90008089603101000c0092512907801100070702005802c140f095603c8501c09481b4802d0f510040b4400d40c00c08101400c0750341c103811102007042e400b030001d000c15268001c050f00c4140c0050075a0800e40304e85001c0ba404038031410550b00c01400c409100000c00742143c01c05501701a250f03a210015071401d0012410941c9002003140d0100d4681e00e08613854070003025543d90f118206900099031042500140000609044020502040100b00810001e540403100c4c3c4001485c0c150450340c00744c0c03554006079410105c100c8090740320155100008103410580d17076500c9003102c01100c1c0e410300f4000110b01015068540081c0f000f0100c91080c0904510f0540d443c0c0000145003500c582c05860040045400c02509405581d01030716505641a04d032902007d510700c458018407816a007503400e115840c04602d02880b03d000001c4500d50152004a00300303400c2840c3c0f03051000d12004003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 826065530 1250 826064280 826064303
    0x190c0209010303032301061b170a080106120b01050405010302030903160506161b06021c060e0f1510180329010503030418050615030a05060108011409060d 68
    0x140e031404a100d001e14443d4900250401410b040a0109084510500d288a80700001401020b03084218503528001024210b440032089240501c0c01d0410b440802c07655040205e49a00b031207412911880c1038903520b54560b15540f10780c170181030036104038551244c00302c0e204002c2803265500ca5001154800c0b1040308407440c105090703000101e0400c1c08041514141c210006100d4081098042c280d41407609150156004000103e010100309144100078041c99000440791800340034800f0400082201e1a410000d050381c804092101d040d0071501c02040e1200e080008508890340c2c82083d200c010090a050310601040c44e06480e2110b05440c140c540c1c1e404198000001071541070007200c0201c0100c4040c544450815803008d40e40d0041c3c0149102c2d420a210510094003203403000741c690014000c0102c0e181c0c45600105802c0a50400c2c9811300600010030003509a24503001507000f950300f86e0342c1c010603a9039842c108184034408102ca660000c4071101207680703850b0251194000f02d0003854001c59 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 826066780 1250 826065530 826065533
    0x180c050616080d27051203060117193e131403060105011b032102030702030c0c010201050c0702060903030c010c120c0903020a0e090a080a020f01060b0906190c 70
    0x105504501e94a03030001d511040004c920f8000c04d61000c43d0b00d42c0c0740001c0c4001c4080743d0354090f01e0303e507210201d03415400c010002400c2684511000340344241003c410780c0c110f0806110200103000251245070929003440c3d00043e0952101a80554001451902c0310703a1400701a203006502c90070211880900c03c080c02250b4001082c28010340060400505050f5050a40b4042c10300b0301e5416400355052168000900b00381e0100310034100400d95252829844081c4400c1210051250f80d11070690340358400f108002e4034640000041600721010f83c122500d21155600482c00da030b4048404000d0810b09000f60401801c010000c1d0140704030041c2a68108420020340c5800c50f07018482180000d900080a9540e8003030500c60546a25403e1a0040c0602e0554010517a07440c85031080c0440c903c20301d40090310304030092002e150305d0355004050b42e0b550200e03030b040250744000e02a060040c6528040002903481c0e000e20454140002c06000d035400d06203110022542104002c0364541448080d103035880 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 826068030 1250 826066780 826066793
    0x305060a05060c1011180d03110615011e120c020f060a0914060f070e03160f0807050616022709010f0e0d1d01050f0c10180c050616 58
    0x8080030f07010020710282d038601e1400700c2035820b44100c04800071001c00884501c00f10a01c662060000265007071030550307d251070102c82000d00c02c0300018003801560140700100d016003c0820362050240e8450551804501880003d41840381c82c04000c142c01036020b400c4041540c00c40f460300200c41c01030b40c10f02c0880303100b224200701086554650141e5070382071510820003000302c20404000d1100050095150a0b5400400707060b000d000320043c0020300c1d81ba1840b0381d80421202030040c110b030310792210003039450500e4022031445018440141c0620b40011803e420b04000795048203c12219a15031140c0c590203100c55004512080c0d44182e04640d81a001c800440c030038507005505020000414094855a5508851136211f181072190000d940c148000b661000d0000f210340c0003511114007601c03004e80103942910501104100303144001c604140842004540040e403880484001d00c500191421203050303000c00a01c00408100301da503800c0c44141001c1001d02038950000160111036945a1900f1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 826069280 1250 826068030 826068037
    0x2151003051e15070507030e0d050a0f0507080c0a0902031b0403120306060c030e09070905150409053d030606030602090a1a0406030b040f0204080604032d0305060a0506 74
    0x2c0440e0100e610500220000401003c40c8010403e014000c40d0706021030001d08621034880301408201070880b1489081e0b48803d40203041341e03405421140c17038680c41e1034409000f46940c2401d50b502d0007030340c50025404201003a45084018000d040f201310504045102000750009020004451030510200044940003c003e20103036000d0040000700141209004050360403030f800ca0400c020801d560300000075080b0443c20302031002156101032540d522442291002c480350701c403070360084281c3c244080b0410480000d0080d9900c81509104c00c0d6100c55800181440c03001a07030500c8010304080044c4051171780300c80c4034040c040000c0c1940d10356890721000d0558070039410548605d980002d0020492529140b80c1c0002c10005880314403005000034000220300503441007905144d203d406880d00f580d41d03a030240d0340e10700e980c4000319200c3d80c940c0145a0344000840c1c00310045070030746501070070850280d25031144540700000640541410417401720702030300014058980000380380c0800b00f42e47d641e21018 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 826070530 1250 826069280 826069303
    0x80a0f14060906010305210307110c060a230c030306190e0a0e01050f07020d0e03010204030204061202030d18141909151208040b090d12030207020f04020a0215100305 73
    0x4004950440c00d249007454504c03140d407c039619189402c7e54282c040d074801d0303940c02061402d00c1c01003400510480b0b0300344001100d900350720420000392014440d0300480702c3c60410b034003881503404445c110003502141c1e20030b9021904580d4001c2c00040d01e50b141c0007000007040b1540b031084031140c6945481031540754000341d5080c0300711621a81c0071007081109105c1c465009181074800682802e1401010b501c50f9048900d840c10000c003101808603039107003501210029903000d0420800c1e1a6074007107241c0c01c039034035182c101d129000c0d064240c000c2a200d202c0342d040340c45230b0020700200e1520300900300e088004151b10013600714180003a00345072000816190002031007025801b007040d841c05040d034814012541c0000d0101900e8440950104003041d084c0e905403103c0c44d02c0c4d1030b40d82e240400010107042007400020030818540b003200700c0f030a9154014000b694801d45480000104550400c002d901a0788519070061703000581c01c04030b5016404e00d040d00000031310100d207202a2a900c4072418500036004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 826071780 1250 826070530 826070533
    0x1317030c070e070e010e012f0a11010e061206040507090902070309080c030312010308031305030417100b180c13060e0a06030504030917152707080a0f140609 69
    0x4003d4660342100342c401082000f464894500d03600000042d1450220341c11048483c1c2e0f00000c41031560b005440c04680015528003220048100c51425200e00311000c3d50a500044c0c03215911503450504805555000070400030f40850b07562810140802020300400b003908200044e00001072140491004003816400b03541c032800328504004e00c0754035280f403e07050f05010303034820001c00207482101038156064030360201c1459aa615407140d43d05030300c1c4500001400310b001c0041c0000d1303402842119502c404078800f0079100c84d042c101d00d24100321840b014443c0e41090134203c204103240c1c24460160303400b1840765091030502c2d01ca0320f0f02008680c0c880e00650b02140b4981c1904000c2d190480034030000b4652031405100c2d0386402c2d075006060b40800e114400107100440d0002100b01800c0c0600400c482c2146103900c610f10b0440c0541c01841030f121034401d050040e82400001001c0007098040035503c43d140200305075581c2da9100710300c520000d5401e407a14403680b0b1500c04521818494280224207000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 826073030 1250 826071780 826071809
    0xb01050f03010b0c1501060e09130813170102070c03020d0f080315010207050f0303120705090415090f09170f0c0304120b09190b040303090b0108030d060603021317030c07 75
    0x62031980781400007810b01805c840a0b42c01040180d611501c0b5491030703003081d54661844e4950340b564022842c030901006200907404200e5000a00b107442140040702d488602071020810f0094143e8200e100303000010740200c60640d810300141c01c04009030031603580300342588045814651244d0801c2c0d04140c8420480000c401040c2240c0c1da8108000f401a0074210f500c121020940c0002035580e2260a036030342144038504000500d014011000e460760520302500a1149540d8007904548ca2401400380f590602d00e841c2100608246610030400d502e07070700907940c440200d800c030607000c000e801c03604013030788800d404200c0040200000c2c0046c00c02400c0d17007545400d03080c90f589000c6503400c40042c0890010390051002c44420b41a21040340721060b040300c0103a5417520742c0e040850141004c0704000c1d005016134000001d80c504000000e103503c40c080c0e0420044140c039400100d050b03116144028191000104060044221620707801d00c1c1c500507401164500310411400740d00741410740c4e20018a040d182c6 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 826074280 1250 826073030 826073047
    0x100608102c0313050126250302073503060a1806090b0114030412110607110d020a0314180d060204050a0504110a181a0913050105030601090b01050f03010b 68
    0x3c00320068002400c10001c803800c00000c940e4480050b004840d410000000400c105200c004460444040300c4004412209880080035019502200701100c407a074152040d43e40c1011904c122924011103450b940c1c1100145194046403600b014111981c88200b0789800039400701c8060f564070201c8801180410090b10740311000702105c19285c04103041c45030402d40b5950400032032044036401075001c42903c010110b0548102c40c0103ca09411403c1c80c032171030b01030010050b00405507040400d5800c0c01c0b43c080da99030000407a11241c07040c100030042098001780f1551006080094402003020140541d440c0a00c0000640341048010b0f050750416400102071045003005901000a4181070ba014006d015003a85651001c0c072400e415901002440141100c40f844505030800060801d501c0020b1741000c1e1220380e10ba0b690100c41d045101d440c9074030001100000340d0007524100d4a0007009020260b02c0c0c810444c2c042c10104a2490400c4020048400d5490401c400382d8041c000c100076007522400403 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 826075530 1250 826074280 826074307
    0xc0a030b0f070801050d0318030c230301020a0c0b0402030c04020a11060601090e0106031806020c0c04050a061a07170a08041406040c05041a03150405100608102c03 72
    0x34100ba02040b901c00010300498481c030b209180100d0341880d09a184080e060f2600810901a0700b0080014158000c0004c01d0160180a0000b1007103003140c40110941c4101094204d02c182007185000c0b403100040b120228041680b0366500c24000b505803018500303c400000c2c00c83e4090324082e4013181200396817000204080120b22f0b0302c058282400c00f50a07050070291a161041407003260100750b12150301d802035121907646031400035480f0304159290350b980c0610586074003904200500039864000051061245c034000c8604881071035081d4803415155030341610751a405480169800840394204803c2170701a200100b28454103542d81100350300382440c254a8158014011032001e9104100303000100b0b0f46014860202c030803c03200003c0c444441840c44060340300303040e0a540d040c02540207404074807052820307651095100b08140c48807885401540000c0b00c400c1e010f1030420764000b102c0100f040d855540038448410f905100a10034001130110320b40048600d210b14083d6403c00f141603006401e5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 826076780 1250 826075530 826075561
    0x1201060f020a240b0a06030204051c02060d050603160e07110a030f0e0411030a05070e060304050712030903120207031b0509130c050a0b040e0a14180c0a030b 69
    0x262010381003480715502c4420400d0b855407108015004020b40c803d1202480707601c0f0900368000945600202c3e90f8409018000350003500c82c40b0300580740d2075000010102848414116141d0007001c43d81003a02080d040340080c8402005660507204403c60850100b00103c0b041c001040516003078012071900c100000d02c40c0801e8125601c0342c0d071203502d0440009800106101d545295480e00c1c0301215501030004000d8030714081040b060304000410300004203e140c0095104010b02c0d1100014501d2100034410103100807a4003030f000c0e4225400500c80012004001e288041c000d1401c65503140e01d0303442d0340b5013401c10f401d0380c10056031004000f00f0402216200884801c10759109801310316162002040c40c441c0d006140b161403000211040d020060105a040050301014120170040340d102c140c00f1920354028010920009128000545e1442e81405081c020305030304002c01210341c40318500e00c0c110794111403c68441d4041e828102a00740c0b10429101e004500901e2143d030345091601100c40f402c0c1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 826078030 1250 826076780 826076807
    0x50a0e0411010c0f020909072c090304080d05030c0708040b1210050f090901020c0f0d1205131e150b040b04060506040b0f19110c01230d020708120106 66
    0x41442140303c0803604100300c40071a41e4060b191130b0500d80c3d4a41a0314282030041e045140c2c031001442152000041d440b0304548030341480300d488004e5448224949550340900d00c54064254452001d00c0700403441000035540146103050382ca8207202c241da54102645d0080c2e000a4192400032a0340f4202e40309050f01d468100c41940380e0183c10b1424840454010402180d405005091020100380c3e000f2096040b41d0454501c0d00c02d440d1100c140640315521804000705200c001074050b28440c85100d9a44a45c0307010700c001c0d0905620070502c0d59a02d440400001201c0400b0030381010f8440041380300c4c8034650001c2d8150f03c80000c0c0c0401884100002c841c884070780c090055140000601158440740c0455043c0d40b11040c02c182c40c2c000e060150600f600c510846080d81d000e2201c0380340e0100b50011019115880c240c41a03810750f1031104c0c01103a650b08a6041c2617410b0070302c55141c5607600c40b400010404c8000360752025240c90041c0e1122000ca600040c1e000100c1a44400104102c81d840012002c410 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 826079136 1106 826078030 826078037
    0xa0b06070c031b06020102030907090b0d02040c02031308061501141909180b0f060d0204230a050102120f030a060e041b0504020a02030f03040606050a0e041101 70
    0x2001c2d4200140d00700d00002601084d43c90041c004e0741d20602c52440100107107881c050680300508042d50000b90040004903d00000da210303805000720600041c0c0003140e03290340c80001c003401506c166000d90499000301080c8011500c0b44d0a03042c003840024a07000c000705442100e030044911801520045440280c104c07508020381085202c0210386108045104c0215461030080a64451202b5158004400200807100e0f29105000e0201b244490100505098640109420001c90801d1142034000c245c2007140f440d207090064030f0081c1c4420302c00b90200c050050034640e1907021701c48815002c004007000150381c02015912220052180c4d0030800c1580c00c1905102d6054040400c103005c0040030002c0100380760500c0e000321504d01c42030f94019441d068443d00c41da0700d1904088c000f101c41d207072074240001d0160b032881c0c103250251031035070308400040c1024078061800c00703649040e09050 = true := by decide +kernel

theorem cover : BRFrame.Cov 825899280 826079136 := by
  have h0 := BRFrame.cov_init 825899280
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825899280 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 825899280 ≤ n) (h2 : n < 826079136) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
