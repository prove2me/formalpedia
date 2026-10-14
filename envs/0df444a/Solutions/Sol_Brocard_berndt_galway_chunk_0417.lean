-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0417
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:42:18.77432+00:00
-- url     : https://prove2.me/submissions/8e479587-e77a-4718-b489-7b7834747d30

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 74820145 ≤ n < 75000002 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 74821395 1250 74820145 74820149
    0x10c020a06030228030614030a0506160318080d140c030114060c0d0504031505010b07030e0315040b0115030e100e1903020102030f1f030201050c0106030b1807150206010618 76
    0x8104400706032118298564031420071f81d8012003030520050795160401d65a0000101d0203082500720002007020300c04041c0298101c1842e40c1404140010300e1401048500055141941c503070800080078044243e00384500e10781101030311601c41c4c050810008035051070205000700c09180a10b0b16090040d5a21b405c10b542c00c41c09214203c1c6c2106941c48001007160f0408d11017104c0300d0340c658054914040c40c60040d241610b04000041c2d041010603281240c00c0100022800d4150150903064a00710b0400b60b800c0c0d02c40d0780104980c620a5140c014042c2e504d140b510100e000305850042007200122000c514010312481081002c900303902861001410300602c0c0c0e201e00c1c5c030b08901c0d01c250400c25030190059031041481d580086541c0e40d4108012a182c002840c1005106140d11014001507000c1e0000d03100403010035000080854482d0b548900880040c1c074039060700c1595007600d06082108026003030140020000504112808400103541e40070103024003020301880101902c100d5002c10220f00c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 74822645 1250 74821395 74821447
    0x70801060c05210405090c04061107080c010c020103022802070603090c031b05060304051c0305010302090f040c0f08010b0306070e010c150209100e1e10080c04150801060905010c020a060302 83
    0x1b01401d02504100040e0b200c4c0c820030b0b000c146c8400c01c00d0310001c0c0103e4058101c80313541d806042d1041c0458011034110300d4111089040c19400d104010204011103509040c582083d506040007100c24900a45400540c1c1c0c0550100340c10700b0419400103010782c0f0400d04a940c000c00028001d400700c050800101311680180da0481e02c003100300030500c100054411044581c01c100101c5c01814030070110203584090201a400a00c4680030901036020b02440355031007401115402080354640100c81329401f10b0b0760182441e6916003030304240340c3ca4180b001daa0841d43e01e0410000b010449030010b0308108072400f010744040610300115401d200c454040f1540558001c095816800002401034a039480c144407090141c080040b074448521554170480d15140c1e00203001942e44c402d0502d085814450040604000352414003001858a1040b01c009202e07440e19110000c1303a43c180040144410043d51205041051103241303080540c940b41d01c0b00e42038aa4030314026036506425001c203031080710000c80c3c01d0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 74823895 1250 74822645 74822659
    0x70905070203030f0a06060e10090314030d050c12070507060905030d0615080405120c0a1a04051207150209061b010c0e040203061008130812070801060c05210405 71
    0x121403030758040015131240c0c0d801c0700c42814584075503484008a610038002c910108041c01011030302441e04c100089081c2e00309242001a0646035038981c140200c0c80480b0304510752000c168402004014098243e0180c10030520908100600301140d08000c409058401030060014041c0284002600540c81045e0440c003120750300c0480d1206800107000360b10030107000130324040305810300e6886800301c40d010b01d41020050110301304a88a5050941c80200c4c00021352040a2106000aa014880c0b00c40400196100011307460f0908055043c004a01d8203d0482c00007081f503900052890303c140c0a21245084006898112090102d01c8500c00c0c1090008039030002250840441415006640301040680d030306980c03107960a060000b81d00080d1140c9a0002c00e10810841061186504a03071042d0450f07500640885c454503909419070108020b003652034512020085a0750b0440340c42c2c0d0040c076103460401010a020744906072524004900050983c260b540e00c000104400d10603900a403000424407 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 74825145 1250 74823895 74823901
    0x20a090213090605120a03080604150305010b1206040c0b030c0903030c070614070305030f060307120506040615030312110903100b04140105090c072102010c021c0e040e070905 77
    0x1070540c0514900c24040458203018002c54582004c4807030f07482c4d03001004000c0c44c50445641d806c1da9104001800c0340d80050740d40c40348640c140c0c5214101c1001b14000c00000031010f40785810301800d000c0801d0102d001b64002c806000026240c1c01c09070080300c9980707400585948a941400d0b4a910a51084a605100109042e6528503001c103401044410382d40f604001c05181c04c0701201140201000070300400e00c10700c00a1100c00c84081c00c0c59010380c008054400054a4215072070708a02c03065000c3e980c581c801003c010800207144140001181c610648112030b51940e60000c01d20700d44905105095a1503c0e008000e0607208400e41e4181c2100070184c42e07810890084d980014484501c02d07500c0b81e81003207415082000d5411046050741c2016169800c565580c2c40111002c3d40110740444101c0c2c00b0759060103061008840c80030003c11103034001306403401700c1e00000307283c4980c00c00a04403200f0081d004000164008521040e5003405450104480b40c0c0b106507035007409151b50194044500f08020 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 74826395 1250 74825145 74825167
    0x40e040b06010f092102030705030102130e060405060607020d060603020a120506010506130e070507080f1911030301090e0a0f03021e010e070605090f1f030b010305090a020904020a0902 81
    0x18035105070820703640c1410f103220b00700c030440b0f40350a00d10074001c41c1340540354121042c014080b0400440d50024003120f0045644d1004a0b08a80c80521042c101070796024051280c090f5004071075800840454081c041c500700304c80060020710440308020301c00c03014424a20301300301081e00001c0096400519802d44a42d550056140c1e180510908450b240600e03000461030345020010340e0011010010116a100d0074075143c5035000ca40508075a06000d802e2040000244102000701049640191240c9d03c2d9668290594100b0302a0b541840600c84c1b055400c000c807110001c20750b03045552810f4007050b014000d1540a09207030302050b0240496861002e81c809054000401c0c08280e8484003a0056a21084082a00320b820ba89106101500280420001d99100d0b02c0a804c0c030007002852148100c018400054000c0b10443c1c0c245980340d55840f108500755050b01c15584440c100782010f1001d89895058036880b03000a01c8028807844810020606540340d040a15000c0c103510b820455480700a400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 74827645 1250 74826395 74826413
    0x7260a0f0809030d0201060f0303050309030409051509090c09040b0601170c070506010b04080304090c091508010e070c1e060b130b09070c030813030e1302030613060608070507050102040e04 83
    0xb044034000d114181000d0380d8640f052042104661015650064484c1566012640350b800606120740500c0180004101310722035110f000d004a5160350005035446070707081805040070000700100c00c141c00c815080d04007600d44020b519030141d40b2607031542184d91203038011388410420118251840403120200072060903040020f1076214003440450b000c507a601c0709500294401c5000d84107060b00244410000179a0355044941e0f0030026003000805181c840401307a01d0701d44d0740c152003000952800d004111104800720320542100306440d05900e11241501c0d10007181041c6217034019005515480001071205940c0482105040200074000d101080c2070030402a104c180030080c4510800004a4102d03405081c072904415403640354038483d559050385c04aa842075a0405405129018030000b01c5e0390b8803901040205040600016160b0410400784140b0945883c9890142c626240c2e0034080150020341099001e40113140603aa1007039107282c030f0303806405182c0c00038503424039050070702c010001205 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 74828895 1250 74827645 74827657
    0x20618070810140901020c1f09080a08070e0103020a0c1b0905010f080d05070c060e010e0a0f17011125050109060207020103181211071a03090f07260a0f08 68
    0x1140d0034291340c840301c428134201e00c151442c0541651000940c01081500f003000301074180700718240003889441a071542c803078076400240f0400015041d0070403c01d000b03801c20f0b0500804c0b0b0082c0303402c6007490740424002d84550000300001d441c080c0030070000100000d0303540004010780344a83d13041c0305959480b004603243c08020b028601d000d026070f010145015100f00c040e544440c0c0c000b48001d42c22441c00301d068500d030840204080c1045000900c4500a443d8054400d00074115100c080a0f9640b61010f2a80d141c0c105007841d140d41d0f4144481582030140210650741442c54450000c0107c80034045000d900c44400380004001e0b50800c0038040178081d565002c0c0220600070780f000e0094400041822026408a074001040f41010100510605104004624900641c6022a1901c644812440c6104503800d15a000904000020450b08030000c4c855800010820350003001003034100850050800c0907000f8a0400c1144070500c0d8401540400480480d0f680003541c200401e8424202104507034809 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 74830145 1250 74828895 74828921
    0x4020d06050411270105030c0c0309030a05030405040608030304050a03030e030c01060e0402040605010c0f17221e0305070608151009030309080c090a090804030c06090503070b0307020618070810 85
    0x2020302d0050511007604424004c034030595810385555a64016506240c100410f50005840140400001924200720307010045018400031a00d480c030341030400c019904d40d0781040006400c180103020000d0b200050040c8410380c1070070045034115000002c14030390702514070403501a40c2080742c00107002141c146000e020381e00980e0f003404425282e0005540040c404d2200400001c1c0c201c0d12900410391100310301c001c0d400442c490f180340c8480c00f0310983c3c020032007a00451013a4421a07040281e040c6602055403042d143c08144c0780210300c0c40e1070701d903280d60040c4911014401e101c0c1c001115440c40480200d1044001807612048045c02103000300002c50500003140414028000810032200c00144044141d4009104071541d03682c4003034420280c024404121100d00d420701c00032000800c190610303c080c0c0200c2d92058011854101058a000c66503800091071000070800c0c01101c50b4007045047e0720003901c00c4c5688020050101481c0362826527444400e480c0900540015610941d4204200c00300c60 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 74831395 1250 74830145 74830177
    0x30804170405010c030e060f070c0f12030c1202030f040305010c0e0102011e0908090904140d090302090f041b0f080f031201050915030106030305030703050a0903050904020d06050411 80
    0x460300c03000300c0e00c114041e50740842d281c043d10782c002910032101030039940006400b01341821414402007086400510b021285041503d10511440742a800d1440c0100610101002040700c00d881c06000700d006d00300302401c0301d100352140084003070007001118400070741a521160303079665a0030081e00034900d66825200182074000d071815150f01c14041c00707003000c4409070100380d1002907100f0b180003400c184078222074002e002d0000d42a90740d10041d0251089004041e0445000c4000d40c40d5410554130200443c01d00944803000e1026031100300c1e036150b201d000c40d00020101d460b1810488080c0644900100b800010707460701140700b030707001e5404400310f4820800712030010b00c00c4c070704c9141c0b6030194030f50001d103500254004200d24038258092613006032510848444404821011034299a81604141c000c1034000050040303840e81031040700c0d44040c111008000004190754024a94800c0b441c1c0544110b4000c1000c806005040e8040001028020403c115041e00d03554141026000000303844680740b5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 74832645 1250 74831395 74831423
    0xd0603030e0306010b0f0903070503030a09060f140d0b011205070e03070e09100c12050a02040e01210201030f020d090b06180c0403150906021201090b010507110603060d020a03030804 80
    0x1e00250f05070594170b0031900340341482c40c0d2009204241d007106d22015854460032000013003640307040c401000b580c2490f0b52030310809410000090280f40c844240300c801c20954607500c840301c013040819124041c01c5182e02003290817403000100c27074042d801d6031042c024074503100501915a0300001200ca1164060b01540c4203142e54181c048140642143d804249800110721803109105650001c940c0c240b44d0f050170034450201c048410f080b02c408440d803042c1c40340d00080c2400352916150080b4010b000c0390310b080d5001c544902040300c201591480081c149912036818011f602d803250103841c0078441448042100d0401030601522005060302c0190140c000009105413000c0000d51403881240644c52042ca054959a28a40081101250f85504030b580705008030000d00240018040022100503a55440d4103250402c422140c4050515050200c104010f400050741e41c00c14804000701160210f40302e0b9104008198807240c0007400039404214854003004064202c903840340940c2c094244004120 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 74833895 1250 74832645 74832649
    0x603210306090c05120c130b0a091517040c1a0304290414031c020310050301051603090206120903030901050703150e09010b040203070c110411040314010209060d0603030e 75
    0x4002c1e05140d400070b0000c000611a08071000c609a8014410b1b8168624016008085400c042c0640d003000303040f40c0340051b84000095020b80114050b20346592120450355503c08003a050038a01c480301302492243c0000202800741884024004040c1e12050b0504c0d0f000c1800e080c402c0758412501141c0091740d40b07403110f616111900541143c1c3c040c121042800b03882d1629400c40300c141402030b035101d0744010402e840c0340b5040c0c2c0e141000240e01c01540580c69003400c0c070003040c6858180d081a8041d80c5400200108190104180c959803045400c0001e0008682e0000c00c43c03504c038901d010300302880d028050001d6140f0000080d44180e41000080206855103c1c08809a40c443c3e00d0181c0540440641448601c2010b070f1080c2d00b088140c4000500151404040746c1a03801c21140540410601000c81d024401d400098005000d02201c04000c3d500700700303400100038001d0b400f005d03007a0004051869440802513040300c0c04c6850013816517448140010024014000c680021000600400c00d040c11034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 74835145 1250 74833895 74833901
    0x803070302190c03031d130605012303013b07090906030b01030816140610080705100509030a0b040b060a050f0904080a0e090901060e0c03070906080406060321030609 73
    0x661200140c42440e195440407900749041b0341300c121b4020b40382c0362041e21325540c448000b02020700c4a00301159031894074002500449003500f504690801270403940e0001c15480e811241500c611401803010241000f0a01c004609008000c0892040c1c01100c102200c80c13240c0007030311840099541c6140300d0b4485c0c0214058a00341c1c840241081c2108005100059030100517040d500c0c104505601083c4458903540d0300784520549400b426002102801002a0b001c1200006441c40000821030240b814022030310340004003170900204840400e0300748080d40d0600503403c5281d0040340700c50b0903044c94140a0716181080e078515109840d038203000210b60901c24030080c03007400010070015003650b036519400090350156201f0000c1040d08410f11865548cc680046d000d0f01c0041d0000a0f982e091401f48100150094206800580c0a20800c80700710740c0314915100396a2a031608140c29199454460064425504010102e034801c01600841090205da083c0c0e180981e43d81c00c3c001940e5a403410811 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 74836395 1250 74835145 74835193
    0x20c0a0608131a3c07030b03010c030c1d011b02030f0d030608070914060909010e01060605070c050a030c03080703141b010506011b0602070206090411070308010e0106080103110d02030102040803070302 88
    0x5008003a80d602140b1004c2248040d5100c0003038280840c10008010000342180c8001400d40c02080e543c4540300e40d2a46c0c00700c03100c0c1a0600c82c0709a088200d0a51002070018007001499440100d0b40c12407001c01c40d00e040c003030145004804c0c400c440c884061460040c0c09440309002e03d008612a5240c009403801c03045c099600f000d0200041d0103601d8031401f05012080100900118a0399228400007010401c2403092400078003042d0b481c251207000518080c1c03852415a03021600c00d4513220f0b400e1010509026403581243ea0041d00c0940e603040c5840c0940d581c40201c0c040b40c007100004181e01c100d03044000000c1070a00b800c031008014503582c220040d01d88404007414012400380081000001809c030758018500180020020380c203040700303d4001001e13100c0e20703141d581c10b0b043e000c00d03014101074000004a014000a003120102581062001400e030303403051001424400d6807007140c209a071075019000d00b8540c0c010f8001d5503a1a00c610b00b01d42c1e01c3c0c3c054501180107224080b000d5514403441c00c08010703 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 74837645 1250 74836395 74836471
    0x150c09090a020910021c030903080c0a140c0d0809010b030c100c02040c0c02040c080108030318030403060204030c1e0e04030e010c051203220c06050a140c0a0b0601020c0a0608131a 79
    0x410b501d800740be049144e003101f0400810301401300111490301013608080d140580b080303801003000c1b40300d4010003400e250000d07000f41211381c1415003402680ea8081901a0743c44000da800c00151800703036100302c49069410381c000c1e4000b841c1030b4407125525030015803045d9141c001c0c0d40500c01c002e841002118000424828001075400507c0410b9135880b403150212019103400b0222401c3c65241d450303c504030381c0710350b10490316084c1c01d403410404407070f452015410070b03045c0141c0606800d00d0005208404a00144010200710b4503034803010440e8000e000103450540c10100320707004014a01c20820450780141d0f202841c0981d150001030042d640b241c40c2d210601e91196005c0d001c00e14254080ea040d8101e400c001d42401060f0200020b07005480d806001038522040040c900e000803401c103200d080601034003150454110444200c2e0307580f140c10845c800c440051810f81180d584245100703107003906100e4010507a41200c0a60070003840040c1c045401405207645c4842e00303001c800b4812038125049403c202c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 74838895 1250 74837645 74837657
    0x20103050f04020f210f060403110601060c110d060f0b040b0a0506040e0421050d06060c0b1f0b0f210721020712020a05150c09090a020910021c030903 66
    0x4d0090078855200f140e680e204915008079425034240305428410680d18951196000c0b02c100400c1c594411441d241615420340034200390f50400300c00400c001004800a841d039440903194000b540c950701c2080340c0b4036030404010040584001202005420300085040c422403e0200040710f914140c58600d085440040c01140ba00303150022203111480d00400541d44104144040c0c992203183c0851030310a5003040d91415038032888002d41e41701304d41a513002001007100304a5580005900d8000c041d0300490441c510000c0100c00381e0000e803038040d45403c01701400b0004100000114449005081810840500300d0b1034904070744101401d0540485000e000121003c1e8000030500c10400c0944501c01590009460594540c03030b03900b12040c4070b582aa0060b0301c12511001482003c0c04100c90030001d00000ea219420050300150050140d591802d10aa54590206540d485c82d6812950b0000001e09980d000044445010752151815009080506640224010601c4c428460021700d2503161b1504 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 74840145 1250 74838895 74838919
    0x6040309090b0f01110f0604050f07060509090a021e0a050409060b0309030f0310080703120807180504020903011404060506210a1101050c120901110a0f110613030609020103050f0402 80
    0x4503484040c0c605100c0c0310b070040810b1361001b50f0050203d58406d9026500400900003444066480d2402c0d5503c12020081c003130094030300543d40d07400e8064100100d0000580c85820410300e40301f051000c0040080e880c40e00066002a4036009401303042112601801040031942c0e8058000035444212481c0d03580d60001c00640c1000000b1700f01940c3c2044250700142c0099485c2d540080c90324000b90420340b02921040b04c81003800d80d011080d96442002c0d440c01849035648031500d078900780e000707000e014491900070410140c140c500358030140209860130b54a18050500707003865401030006a403421b019440120720240d1004902a00c1d0b400200302c80010a5555401d840e00f18494448031100381c1008010028581d09003000c000c000e031000c1903215515a16029040054881e1603030104e0001c2c290000140300010408090012003269005080b0184015012000a8551042c0c0e0349a0803180c0071180048284226580300d09100d91007a03e00300540c1d212010f58690108040301c00030f6004841d8201 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 74841395 1250 74840145 74840147
    0x3030302032d06040f090210081f0b0c0106050d08070803040201110a030207090c090305150901110a09030303150b0306010c030e0a030f1e0804060c03020a0c060206040309090b0f01 79
    0x30766004000e10640d000300a1001260301c10015607244082081c00c0b400d05010003840c042c41072030300c000c4c00300d00100411740d074980c0414090070030046214207205401c00000c81249101c601c0700c50b29030300340540d0b107a00d5440d6002d0f00c000d0b8205804038025586012000710f601d09000c1c403081e04071034001030304500700f0910341e403000d0503544000c00480c1040100c800b5035140740810020702e0000c502c00d4002c1c01120b07003041c1070401194a001061020401048001c1010440120f44000c58405582c00481c107a071310b000070107015110700b80c44000d145000003a440304482c2d20259020590f031280e9000e1128a2030b41900d20700403030b000d000d16a0103050400c0887c40c0b542c055030300e03401004d00c00d00f0105203100c08480041d41254880d4400d45640800b00c0521042014174005015501d16071041c2e04041e90342620303910038a001d80e01910080c00603c0301c1a405150082100c020480c1e4490001c0c1a1503880721002501c030a0151001c501140c02d0500100c0c461030305000e0454203190150503149200c00d2000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 74842645 1250 74841395 74841397
    0xb1602070807120303091502090306090d0509120106080a030f03050c03100501030903022514060c0c09130b1608061806100c05010507030209090f04020d02130e0d030e1005040206030103030302 84
    0x4401c4090556514102c0c000820410001464a0b40302e51f0060304c071542c540600d420803000038042d4840c1e402c04600301d8119a0030009030f503400f607416203c000001d8440c06282c4d0041c10b050304100040c2c0b040101c500c040541c0007220f15040c5009035028046034880744a040f030389c0e0005559840c0519174651090040794403c2c1d1040803024003174811100300d030b03881d200c11600110b1042542403084075220301c1031014402c10f0361411044041a1317103940c5001584059175442d5403024405520601c0040e012a121000e051001c0740f58581106100510f4102000360320350085c486122076000c01c01100005d446860410505a400e1500700a508920707551182007061001c1d19000000900c8103000c14031000c80c0c4248503042c8510f032207071401665800e1403020404120002810600c540c0400c60402c0016218002c02080c00d941c1aa21140200b40501001000e050012036040c41c5104403407103a0300050341b40e0010309800c401c00c070986a6070841c0344c40c1d00d816a0b13030454002e90098420001040041e1180d4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 74843895 1250 74842645 74842679
    0x602030d020705030d05160f0903210908031c1107021f03020403060204031a01050a15030515030f01060e0604020a05030c09010908060a050103150b1c06060807030b1602070807 77
    0x4030a9902e0016484101d85c1122015070305280000b110480d130460703030340c0c011124500341c031005d0400e1042c003403550392800e41059511031214541c103c03110b94044454020141040941005c8040d6500d49084034480c2e4068400903113042c16030750808110301c03014000300c421a80500c1e0090807409061640240891400d62104100020182d00308000000f04030719101910142d4418407103000450041c8100121808041c0c000034861150480c0801818041d007400202c0070b00755050210b5181e4400294102d030000742c90403583c050040a00c01289a0410b40c03044003a01c106d001800895103861007801304a004210707100c00030560403c0495200406d0402426084405152000741a41c40e00310103802c5c148251608100b0fa6200d40050082105e21034001d42d041c085180c040009904150000c0c9807007280c0c40803101030000c900791031418420300d9000440540aa90110b5000550320315100800c0ea004940103540c94114801c00c880c8035101084540c00c0b81c42e180000d000590070200c03907a05144041d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 74845145 1250 74843895 74843903
    0x20918130209064e030301031a070504060c060b060708090901061407021e0315090f0d120c17010b04080c030c0307050121060e04030f020105061c0501060503010203150a0905010602030d0207 83
    0xa42c81010f13150f0b4201e11213450a040c3c0c080071390349a5141d0b1420b80103d0588204203401d50f0010010002d0041d41300c0181c0c1c080301c1c02490940c40c0100e8078101000202000b061042e0030050008460081c0160500141080c050940380f0028980c6d03516400c03034008a58444100d00d80108218002c05442e00a81821078101700402800112001c040001d00d008a20b101103110034803101e0030000d9500302480981d40c12040e44c00030380303031009003400c004050503d50111000c0340c0d40c0e41e496107484944544000e804544195540d845556102c02d07100c140798110b4881c0690310701c10703085112402d050101d204500518041c0041c031201e42068015540b18402c1c61417246600c00e00039107070300271020900503d4000c0200740d11b10707261030801d810f00401c15046400325000b5a81081c00740800d82d207410001c0304030440780500b40c0340480010302e0f0040c00750910340d010542c0742d170003c42400000c1405003000c2c000ca0900311000502c1c85c0c0c2d1229540181c50003481201d016070000c1c0f0000d510b4a059400410009202d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 74846395 1250 74845145 74845249
    0x409020a1701180f0c060806310c0e03071d010603050405030712230a23070b04060c08060d0b061507120e040c110a020402091813020906 60
    0x203080341004141501c110180d588000f9180044140124030700e880c001b82c0031a182101c01480c08401188510a11102500c1e01c00040c2845040903086942036040094409000b8004090110030040680a18245051180c011010f002032042c3d06c03080c0469510030f0711204010141e203014019001040014403e54a90004100704400950a04585040c0c009142c6400082d9621007800c0050180660b5059910000c100300d00011a500305401c2001d07045a29048410030076215291011800303903070b10060441c10140300b804104032040c0c103e104003034500c0d43ca00200742d03200820002812403001018081f44400c001083d1242030120324200b540b850190002d180c000d5540c0c0340700440661561140024001d00e560503c0d038917041c05401917600d42071030826074003402040f5258403520b004900030310a540c0050041c25a80710504085e40c0c0d1483c1e00081c00042c03400440f81c444005009004030300c60700c42080000c0b05803600100383d00da00a01d6074080c448131000c62900404400005151303843c0300c51 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 74847645 1250 74846395 74846411
    0x50303090112090c0f1d010e070813030905100306080f0d050a0e15030403020c010206242202030c0406030b100507031b080a0f08010918030f14041706060409020a1701 73
    0x2111201e030014180355a0000c01e100401322046e0031a06d040e001072081c02c0c203140038414004e0b804000b003070700721158075101081d0229515054038044525070102c0d41246108521511a41e00b40d40264100e80807070701911186001c0f2901c0d80c1d04c3d40001d58007080466800d20580f000e141c42a400d07041a80c501130000b1140500088031b5801c5034000f00c90480050b800000452032a59040c002140c1003055500303084542d02014140d8407600e00c10b180d60300d00413401001f00200714000c01c5415208071007894000c550328100702e003c9121950090190002180c1080c3c0603c491b4200744100d94107000e910354545040003440da8007251102e41d011440d03003d030419440f1b00e1000c00c102e18000c0c40954030584402c0b48a00103210302801c01c0348143c1c000d508403403400800882a03030f01101250003950f81881c04005034030816605403a4030140900790190305902140100f8021035100804040e428004125100c0d40d68020800080c0d0300740100003904410720740c1c020030800e9480c4c0d8001000c2c00d407440002c15205 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 74848895 1250 74847645 74847659
    0x32102040b2b0e0c0f010201090c030c0305060f040305040b07051606020607170606180a0806040f02130c020715030b0303030c090f0108041a070318030c030306050303090112090c 78
    0x42c21503102e214048032101e0104210201080c004a50b0011104040c0040100d94500304d4407200c2620030640103040c078110403600ca80c401c0d8000000250702c00c81000a458407030401c2007503032010f170100b180c1a1050b0380215500817001c44049225540c1a036609103040c0c01c0c0381700c003400ad030040d010440b464410109800c14005480d009140a00650390051089150800d4020088074081c041001420b00010500c400da44400d8100c540c85120700b20b29400c81c510340c00204007010800ea02c2118680209410710082050785140c20304424001ca8521003d10313034647c081d80881d1503401c0c1c44005603020071002c01c0b856844418081c0350a1766801e00040c8195010040b030300350f520440b8440700f01c43c00011406030390b2811201c1403640c0e40d02032a12503120715260382c0d510110703000049281400142d010003c0d5440e44240c1295801c40c0c000a8150350180743d6140151180c5002c110440c00710b400c01d840442c1b00e05000081c0c8883c960165540d1100a074040d0900700203080710b060503100382e56040800302d409 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 74850145 1250 74848895 74848897
    0xe060903010c17060103090201020304050d1119090b100e0111010e0709151406030c0c01110c0303060405010905090703230105250c0b06040e0c12011d0703032102040b 73
    0x400a4448000002d4080340100003400c0003844e25060620701102c902c0580d07400010350b8162502034810344182c2d03c5c00e0510805042d40c1000199104810b91800388540704000800c4080300d00c025010b1000c20190000c2100e0340601f289040c0006450307004590300c0e984191903644070390035890700000340184003890290034000903411016005440b0310329030781c1010307603030848900a080105010f04034150440008043c0c0c40040c10403c44d012000c070346104910f5080d070103240390440d44400190f9a44200081c26100e4100702d40c598807462509000050111882c041c0c00e1060b0201d50203060402d046a950000c2e03000020201240350110010f09100c06400344a018052004000c50060b92044e44a0303440260100040f070720100810340c041940050009100241c100700105c80100d4401c00c0005502e10700703031400f40d10030b0b40603c0e002c5403601068010360101104d0001c0224550f03005100a503116620340851100900062040d804055480c84101c0d074028801031000000d441c00ba81c50644481c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 74851395 1250 74850145 74850161
    0x120b0406060e210d110705181f0302010e06071b080313080f030a1b0605070504050406090605150307140c070e0106030e0d050c03040f1409060603040b070e06090301 72
    0x224002008182c440e01d005641890014102c851001d4504508030b0350b181c459910302590028003502c26403c603c114818008040035002c003801c1102500c41100300c243c0c04220513500413402d03030407503c2154070340c003400043c4205581c6c043e101c10380c0380340310041444141d03070100d031054035900c41c6d1205c141e5506500042c84001005440010b6440d00320f00092031401c1400e560140080ea8018005c12582d0240403007607401062a5081208980911014682c007030791251b40001e04d0740d45060701f0410300d2500240034009848040d40c00301305141c0c0310704014080303d8030360040750350009a000f2b280c40f09088034002141c0c841c03400e10700a81402c0c1c401802225640101620610b143c00100041c000941840c58883c010310051038240107580c40035002c2500c0e02e12000500e0104a80041d070807490010030011074005100c941820420310b5500c0007090400c8110002c0280f10700700f000049003080ca804016640110782004000c0d083d0703211201c0545140e50001c00301504400148015502c0e95800c0c46840c0c4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 74852645 1250 74851395 74851397
    0x903020f06250303110c070b0f192a02030c0d08090a030302030c0d090b09010c14030705030c0601060e06030c03040201020a12080702010e03040602070b03060a030c0321030516120b040606 82
    0x680c40b40c601d0b0141c1500e4800c510a14843c0302840f490340d00000005400e81215038401d41543d8891092179502090300c12688001518104007130f01074400c0394020041d115490b80a00c0504c0b041e20b0314814a4a1742c0c0658102030f6050b84040d00605041c5002c1076035032983c500c2640b5080c80c01160b00b0100390f0700081a8401e502603007000c6132280c1ca5020612008450710703054030b420b00c0d006040400c400e805001300c401440c1000400000042082810142d0090f0188854101c81d11040a4039015949900412070080e841c0110000000d40d14081c110403071030b0120041410307041d0340d22909880c4030742d040140244d04500c200010300c004649440c4204103052400d030b87d90349032850400000390030740300c1c0d5800380c2c060342c1c1c810401004503d078081241c2080ea910386200fa940c0e82c59840024a09944030340001d480314070700340c4000080252540901203209005d034a00780d010619110151304807082210a80c414007000031000c03182a2040c1003280b191a01803c00094000d4104d02142c2120a00c0d08400 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 74853895 1250 74852645 74852707
    0x80c1f0c0f270f06030e011e050402011101060b0a1806020307031409060706020c0c12120705010b10051b0712080309011d01062108071407090906200702010903020f06 73
    0xc8004e550500a005442c41824000e111f86032008514a409103042c8200d0045255a00d020408581c8100f98040e10381440d40000d1040a4540c99540101c1d8005070301140400c071515500c0c00b800026094003030460741c294000c1d50800800303843c1902e1a228071407014151f00020010304100e555000702070720300a1700032070700161601210038001d4034104074442101d00c00d03030032015814840f140000350150a43c0604240a0f143c070740518089014000c00780c4640c1c3c3c881e80f80700c403405010b94820040d250080d02410056200b00e000c0d10091740394080360090398105c4042d01030036408100300100864104038140c0001900ca60078500000780d00700400c080d8401651a05e02c00c019070140500800106400316103114280d003125500c13503103580b00c0e11100901c501d254004801e05170300c040c00044000c0100210910a403c410f1500800800303e4883d0002c0920300c0900c156072120064060318680360341a1035041c0b07100d05507020800880d200301941540308904021643c10300c88940701b451400b0505140c00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 74855145 1250 74853895 74853899
    0x30c04080709061d04020a05120705090c0901020c0108070503060108040c05040e0a17040608010504090f050f0a06050106090501020d080903040510030504020405010608040c0303030207020607080c1f0c0f270f 91
    0x2041d11340324240a0707052142140030a01001d60340700708880044540c11607000505600021203241032080d03030307401142d00c44c121008100c0580c040708000c00300008242c0c02e071200c080941005480e55002600ca20000650078400a2000c0d40120780d482e4100b4040d43c070540702c996460002400741c03021042d183c01f0030380100c0c50751001c0200641da120803034a13802004904003801c2c5a0300a013a0306c41441200e01c03807602c5030742c000103008030034001c00c00709030300042580e02c607403855005c6690b2000b0844040714100d10f000b000041e030506c40d01c000e42c00d0713800580c060300356101001001c13038422001404241c001e0204200c00182941c070710182642d1408540c1b008581c0740382500401044810582c8403009000d071240410002034509038211007a42e5050400680303502c55400801c1d00d900801ca0020807a480004451a002034001024140201e2035046154001c2c07041e0100001c0d00c510355050b00c040344146050002c04d5008902d01c490498070401e01d1400c0b6403108894803000304465105000000b500041 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 74856395 1250 74855145 74855159
    0x209031006032f010c06020d02131e0b0406050a0806120f010c020714030a02060d0207080310050918060a18050a23070509160e030105010b1908100308030c0408070906 73
    0x1841c16544140608003d800600c00081c0502442180040c00d541c0d001594120416440d41501c65440003844105641526070b40d90b918840d00c80c121444820241c0c40000070f111940d10b0845040c1c0300075030740d064100b180550f4181d40c4d21401901243c0d005212443c0c2d54102c201c200702402c0d590b02d03100008541030008401c06401d000003038121140e91400032410103400d4500003090905d0943c103454a6554039107281d8004000e009250008041d0000041441015410402d890080d103004564500c0e042d1241504030804081c00800308095401c9a4001080c102042c1d00203000d400300009020b10155143e510141001c0f80e071201200d000440c2c2e00c51070b0346180704031003140c03640c4000c00040a803141400300003188110001c010a60600701c0c1d00d0724100851041c031103070140d01e0001e802408a0b503101c0042c08403642000c906404603040c2d903083c8500702d80c401c111540c050403038030040c100140e04648034424103900080c120b214110f41003000140380c81b0204a0800200b60440b4001005810301c08 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 74857645 1250 74856395 74856443
    0x2030c12340501140a05030702030f04030c06080a090c090528060801050f090a06050a111305010f17010e04020d0c2d141002070803040306060e090a0b01030303020903100603 76
    0x40c0e03040012071105450403a0048048034406001790615a03260354840d20200c1c95031050f0070070398146038804500001084150200c00f030a60300b032922070304450b03901c3c0034052046901c400e0000c0d0403481d0404041001120590140350084891200d07100180c07020319405610007654140940c5140c1c1d1a041005040c8082c42043c0d082080c0664000c080d051000303a0310b9448185060280000c6c0c0c7d170300c01140309900c40d039008480441002084640f10b019820504444003564071840d8085114450054400340c0300f40e0300111150604008400300e80d00307000744140d094034010070491300650000d840801191030488428003c1054152504a041c001405440c03003004420496902490265003482601d450060402c1000c0c41034511144030b01508000300d150000c81d6020359018000014048180030581e04083d02380c030310951560202d0f8480c8500c3d40d03a1070510b9400944003400040c01172000a10903001000082d40081c215a0301120000303291003251015841142c1c20741304590b40c40c0f84400808 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 74858895 1250 74857645 74857649
    0x30f05071406031906031a09121e0309030f07080706110702100c02012c010e0d0b1609030503030703020c0f0115050d0f0501110901090b03010302030c1234 68
    0x1020401c59071254034081001c1d030201400d031640180084040420601e4641e100300c2c010354110303002804820341e4100d8018443d00030b030303980311150003405902d412403900c0d1001c0340c413400d030408004100c1a0001e003c034403242c0c00250462140f40020001c081044940da000340c00c20b035004d030040d541c1e9540759103000e40c00c6680c0001d4000502c0c00030f1100c0005031351245040e0f105c1200c182010000003820f4401201d02540543c440c00d040c1d030707002046500303500c0c0c94150203202d5002030b01c1f00d091400b4440100200b012440400518401d0440002512420b03051115070781002103007024102d05441e6034030141035410840e807030000281d010500341a245410451a11850303900c40007040a2140544203540826640c002c240c09110408841001c001402076584040e40e00f0000801c07100c039404d941d00440d035020542043c0010200c0d2404506440c0440480341200d0780180104150305684003406503103502240e5400203402200300c07103c1242d2032010300b5101000000d4003101100041e001c0c2d00300300b00d230b5a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 74860145 1250 74858895 74858909
    0x111060f010506070201020c09160e09010b07060b030732010c020d081606020409141006020d030c05040b0d060e0a06030201020a0b180f030c010f110901121104030f0507 74
    0x240500c25503154200c40a419200140d5500c2d070f4405103400141d1800c98841c01007504040248104a0418140001c040b0000450751700e202e040405001000110b21003800f521002da10304000e0382c00024401e90000c00c0f001005004e640c0c490395240840c15001030590300c03076080c018000d83c10b0300d14031038241c1507a102114242080003114031290040743d200241103500500107030780080e90048150b0818040e0100e294041415990f51b46c40304562000f9020f03114034031401c00301940c045051034a6100881096540359401030840c1082c028085014210380400001488020040401c41142c400024441016414000704680389443c181c80c1d61000020090341d000d9180c0f030010b1006030f0380402c0d4100840d420400c1d248254403100100081c03044140c0e00040140b28124030b5030010000400900700d280201030081280e82501c81042040c0d6120b01825045542c00b080b65211541c041d0300d804001e1005071800050070b8403226406041c540c8140c00584904039078044030401c002d0100181c401501c45 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 74861395 1250 74860145 74860153
    0x30203040f0f110a08010e0105010e06061611181510090e101e090b03210c070f0906091d2d0303070c050c030615010c0602090a060302090111 62
    0x7900e4861a040107a01c0c01800080c071100364100b8000100546000c0882c000c102843c45585c81040600800e0607070722030601542040000104000c4441704c0c1c84c850382001d810a40381c01e00c43d40d07600030809004c0300c04076079188244500010584a0038000d03203c0c4040214000b1003030400c210044210b0130b00c110907500c40c2d025040380305481360f440700034402107400f600e0300c246290b01ca0003064442103046030001e03126103141d21410882440c100700c0040889034070b050108204000d21003490f445074452240050704540501d07001c40030b03004840c020305411551106036040c482d1948020150260381303030b120280c40742e1608801d0003038000328030075244000346002031284220154400d242d260f84141181702c000c140f203220241d580701101c3c05070b50000c044840950356645080c1b10b01804003040700d03009603014410182d00400d9400c00140090180c0080f842d041f01c41001c201c01110140200da84c1107850036000d202e003a00540307400000c900134000540780903868184a400040c130940407084a0205a40 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 74862645 1250 74861395 74861401
    0x806090c04030b0c2503200c060c060601270b16050d020d02120711010c0c09050106090e09010209010212090301020c071d0702030f0304121e0306090510240903170a0807030203 77
    0x18100f03c200d10070391f05991100401031200300900341005a407900054029400084910141e9000b25016124080988031111403148818901009442c3c00c0250144200416010302c0100c49440c090508969084240c1c0030106450355224240842c80d0f510300b015a11211030030741940c2d0180b02ca040442000040f071401d081c5a600c400060800100326503040c45250f030041400e06c21a81e904e440039148542061240d56902c1070002d1000840d0310540f216094880701107035840506008030b6500080c1603000701030030403040c14007440d01d0340031014590303140d9401c00006040700c80500c65040242403100b02104410b03854451400d031050020070701001c40d0420010204240b00d21400e0b20341181c1c110855400481c109101690042c0e005450002e07122a0b40c1d5412000035450b8210300c05a41060302e00740069181d43d41d000c20904028017034405004110049006a4001214017040c0c000c01807500c1644165680c03903607164441c0c0e0080018a6160000c0e00030141c07500300c000c4681042051a086195103 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 74863895 1250 74862645 74862647
    0x4030801051903110d0503070503030702010516080406050c160501020306040b1c0305030603010f050a090501060501090501020304090203060604030c03080a080906010e0117010609050a0e0606040b010806090c04030b0c2503 97
    0x7070b20740c0001001c8800c01054821640c840d01184001e242d0b102c000ca903514481070810756a40c0d001140d403c401582400e00040014100d040052016822900d407034085440b03030713542d2102600004080181042c0c05000c8c5504000808105961090040b8001070f524140b95040c04191400700482ea4028018611034002041c15410801d14950f09880d10b151a91152400203015001c0c0141c914000707800c000a22022110551190446600c02c3c0020000c9564a0300107403001002c911a250168006000802405009400079580124000d151601d8aa200e44d6210b1245003a90026101070340007290000f002904801c0702030300150507070014201e541c5028120391001405001d141042d0755840302e07628802e4003d420560140052450074400362606002000081002152003400c5208400c00b00f480e5052910a020304104180e4075070201e0380c0e81d00244446884050009e0040756010070000021036000c039601400740d8138a120080d95140424441d100d41074400b5514000b042610301081e0000f = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 74865145 1250 74863895 74863939
    0x90905010806071b0227070305090303070e0f04020d090c0e190e0114043806040b0d051218030d0e0405070e030f0709060608071407020f06120403080105 67
    0x4003c0514045903c5000e58506101407100c0c1d031402900014a01d40c4014110300c44070900c0e00d25002084201c600e0390329580c04070181c820950b18000349802c2000465896485204404c2c0401d802501801c0404030400114049900500e030310516566a0a80070f02007107040200507000305030006a201107030600310b12110055040c017005108107076882603881700d913400a410481044118000c00f81c80c500d054101605192107410020f03414038610318402d000d40c0001c5602e00741d08039025032514584d44d90f0303030180700052420030750f40e5038005495140503000a100308203c2204a42116a040d01c42820010a031890011000781c14031a030404040b06012540c400c81c3d00d00d0004044801040680303c0d40b809603100300d00c06480039010b0007032880402007190001030245c11110186020003130307130b6500d580031211420191000c2c00007584103a20158030240802c00703130824600050804090083d2107001407680d0307120f04011012130861400b080b00349500709400900403d020781d203810948000803440808 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 74866395 1250 74865145 74865151
    0x13150203031603060312030b0108070201020a0801181104090b010e0109032609030a210c050303072105070216050306070c081303050303240604030f201f090905010806 73
    0x20302c94001c0c0d41e180640c4280c22000c01181c1180101183e0142250018090801c180303c0ca8003160141303001c1a00c0e2403051007126500c104942d0b84a080c3e0f420103051a8901c2c80508030b01c645151906114080001c0d0600104000e001c07911000522200040016040c1440c0c130b81c226041c001c049404002242503d4403010b000400301c40001c000503000041e14400e0f00a45405541504c51400d0110070000401c0e4a2480c9030340e101c9080c02402e1000d41c04440102020704000c00e5500188049041540201c1800501050070209080b40b200810007281c2100c204403002c5005a0248a003c4007000340b48500e1801382c04140e02800340e92400f45809020450840da000b050800300158800d801c1e2100d0300d01c074000d140d000090782e07940d00b805160030349000c45841c8001e0311981061000e80c242e144c000d0486088079803080117290421082d407550081110000c14415400440e000300c103149a451815040c100c0f0200c10404440c040500c600400c0c03c0010307000483e20340d01e0500180304200d40003171141d034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 74867645 1250 74866395 74866411
    0xb010b03010f15030e03191103040501090303050f0c120d0c170c0f1204060603020310050402030a02010507060b12010614150906090a030f060209100e0d02010e21031315020303 77
    0x10481500d410110010820450b000d50300d400045080900580d101e043c406480b0700603230b00c26039010155180d0703684903c503600c103142c04550a0381e000c10009004501400e46c03048003015042c1090380000c230941c10b021900302414a8944002003c0184104600c5945c51000103442d02d00480041101942011800607004601341c240201e02030b23120642c168200c0d0144101c070450820b2a0a0034680388010380f440e030208a100b800f801d5030700c40d04400304c2c0c800d02e80700d02d0b00100113186030f109030380040da06544000c0068a4068455400d0200c58079154509040c42c0707c1500009100340c5050903400800e40c4829034584551503640e101d50400c0700e5842500c105040840b01d03140c0e2081d202c3d002804521037a0f100030b1490100b00d2800c070510026502503d0348010a4444e009544580744044410b550905551980074020840500241d403145d0510148400080c1c200210710180e0b0148206211030700b54042002e901c001404103460130314000c918020200350881c410442241100a52070b408004d0a40e4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 74868895 1250 74867645 74867669
    0xb0706110a0207060509030709060e090c01020f0c01140708120402010f020c090f150909070f062f01020f0d0e010605190311010c0f080c01110c0c0d0501020f160b010b03010f 76
    0x1006c40c1d40c00780a40b00c000e00b8220400c001081e80d07482254540307841202e40c1c0d4054001d562420740c00b54000310300700d243c0c8000c940103402c10381c00d420015614040c04488803000f248041c082480090001c000070019020441400754051400d44001811080070992200c215000b0034100344142e202c114146401c001c00e40c1ca0700c0003a41d00c1e41e0034015050342c94180682e00c483c01e80244080b12201050380c00a44002207610300c481e540340c040a5840d41001000d80c80314000b03141240381f41c201554080a2180170400026103050240340507034505400101a91070040d0b13a403262222548424401c040c01814140c401c0124010000140b401070902e40c800170300750110b900e019000e241c0c4621501c003002940034283c0d81a14540342407000e002e030040e04480c0091741c42d000c83d07410740003040f100f91000340c4001c0004200b00b10300c1801340070685801070001c0f1210764080c400c103803510800002416101150a685824a110710f085c60581c01206074030003069154100014448540801d80d0401900d6000c0204 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 74870145 1250 74868895 74868907
    0xb011205090f1204030c0b1c020d0e030d0605190608070f020a0f03170a05093f0a0207060c02030304050409030203070212100b010215060409020a0b040b0706110a02070605 75
    0x81414080c2c0740040c8412402102c0264030f850381068041e000b524010f8061420090702c2d1b50b00f4844034800c40e281c080c002d0548e40808000c0010940040c00b000c140c20700c020802c40581c0d80014170751380045c40600106901c42c9020f00041c01e04c910721421031000400da050b0000d1900300090b10003100540300404111580014402c414001c2040d22030050740043d8181120071541001080e4005915802d4140340c481d00110300440811f004690040002c0b00140a8204140ac0d01c10282e05030b90410ba8001c0c06d5915142038001c0003c41c2d0300f4505a451501550350307010301d030380007811300720586c02500502031500303000340150b180002940c05440c800d440c0001e504900742000e92441c01000303c001d510202d02c104004105402040001000444030028450350000e40016601e80c058a01050600b420342400529141f515401c0400d049002400300d9800c15243c04443d103803a0311942100400c2c0c04001441c404104085c0f20380440c50200c505880d05100300d000000b0345580c1d0520a04040200200c1c7c4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 74871395 1250 74870145 74870161
    0x1081006110316060903030c02060702060a05370605150708070c170c1c2a080d080103030f0e030307020919141602070602030d020a120509031201090b011205 69
    0x3203c802c11920515420452002d1a00202178200000101e002904042032001454000a80b86000308143d4003d8101769941481c054002c120061040c1182e80c0c000c03444520920307150385403000d54080301a40c440c00c8031030124280d06850306940311a01400000e40b514215180400603078282e0b95014040903518900c83c14107581141c1c0030b0300310401c0c240303101c0d08510b80c4100c005202048000f055600002036211401e1483c040c1d20411006010300c4074020480c140c5400c0039818505501c0d005040c0e002003902c1d8022103240c00501d140306004a010f00c401171040c1604800c0c1d520a0100f10701d04890201c0d070b102c0c003080d00c1c0d0040c410002d01481b641f8000c9449241902c25a6034a008485001c116428001c20301944510090f2a0007540840c61500c076821180f002c00c4810a5a906800442c0f400302490310500003941310202010400000d1035845500e615140250b9009105440085440c0c054944044e1142001a441120051300e007680c42c55190740c00c94580c10170640030074000a0039503180f4603 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 74872645 1250 74871395 74871397
    0xc03050a0e0402030f060906030106120602070c150503011409010302010c030305060301110c0102070c0803030c0417070504090303020a12200d02071a01030b1501080114031609020a020c010810061103 87
    0x2840d0381c0c094004803c000b02c01d00341c00c5d0041e10505045500810984925003494202d400d1405404803001062184401003910380d0002e240061240701c07000080e81e611070000f6006160040018005000000104954a424203a0b00d00a40049912140c02d5155500103001c20b81e030351800409060301d42c40081c1080d0b50a501011a41004060040e0354484c0128564002c0d40f0105044510301e40c02c00000c2851003002044d248101c012045c0035140a0410000078038280c5010361104242c4100725000c1500c2e10746000ea00c1d030359882900c002da1101a503c00203404219000110080c03189494100303003200341001c2e5526034024510b20780726a141070320030b05400170f44518480038200001c00c0580740c0241004604940c120fa0150031111040e440f5075001c5600c0c0c40e80000924001180c0750014003501f080c1002c000e6281c14028201d1f00010105020403d83d41c515038010003020740d0104214140c07507010b000c4003021010901e4502014079010556810a4085020345000c000d1440d0140c111010200 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 74873895 1250 74872645 74872667
    0x1e07080a021b0102040510030908030406090f0f0b060f010806280305120a031508121c181b0b030a05070516151103010303080f0403032301050a06020303070c03050a 72
    0x200c861034040402c440080d0107580b16115641c042e04d005914100e00610074800c0301119a804801c980c50346c0c541da1900e41c080d26a122040d00c0d46003409092000194482c244010300b09d104150000440c9860010040f40445910845040c86840001c02680f0741d5000704404003520120301d07249002442c1c182c81410300c80a5000189035200d01d1084040c4000b5100142402d080a503505204848c110011000f00c224a84100f03002c503030001d00e000076014500b8018007080c018004000c1d070301c410071207030303003000d40d0000e01404428500c12441801400002d100702d4580b080c460050b4051a4640f41c0740a18500c0010304071214150b0b94400b20f508180b056084581c0c2c61030110501040740c410f402c1c8210319041114411310720a00e070040d030101700701120061364101c0340c040c3c9506c42e01da81c400000c0c25021034014401c804040d52070b07120340d00030b0f8048640c0c02c2c040b038001c8105605c5d6604050522401854a40045041d503205200f009251f40d405581480c041c1c1c2d0614003d511901000d5041d9a021101 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 74875145 1250 74873895 74873917
    0x12041403040303050309060108070f060c03140f0a02060906090a02010e060f0406050406081015030504020103090204060807050102010b0a030b070c0507090609090510050f07230c0606091e07080a02 86
    0x80000c03e055124010754040c9606405851160340c0c0c0720200b40d0350700030038482c1519034903580d04100301407805150b110028a01a060202e8038480705104130615601480343d40c085510301080546004d0750400546034406078510042289003800c8003103a035a401c2c0814004e04006900e200000d05803100c0042d50020b11441d100d280c0c81d04d07203c0b040a0419046070181d5000142820002511017060903080310855003004101c035840802c1d082c045010344401882607050544a100240050f15584501d00c010300080d006440c1141c140000242515540081303248502000c40c4180f01142018000c0c507003103815401e20482d8002d49140c414109441540078083c514a840b900091039540b0350041c0f5101413040069406603041c44404030100d800c2922004029400040090b280307900540440302c40c40e055541a803003607516060145080d502c40702c80c500540d0008014070403942051700007190406c82d0404040d4503c5082095041d000c13a00410710342c00c101001c0003040c207010507541150011002 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 74876395 1250 74875145 74875147
    0x6130b030906070f050405010807110f0703060b0f0901080c210102120708010608090705010f030207061503030e030303091005070c021905090108010e071401050f120109060b070812041403 82
    0x300d6160303100c00c0101c1d03ca2003c00e40201c2d40c080110300c140225011307110140c690030f42c02d4844410450307021540c0d00800700b65114803034500c0c02e4980b04002c510015481f5510200e8141010f40074401d52640c128503041c0a4060700c001031000d40380c0410b13020500daa0a441c1c10341101400000980000808080e00c0d00b15440000d50400e04103201c01d02e644190100e0f150740100e41d984403011500003408694040d1641c020040502070fa41c0b00d042c01c0d000e152a2890b0240c1420802d495040445500c02025120041d00c0c2c4401c004242d0080c2c002190980c1c124050f50951801e20321003902e441c2c0c520441034504d99520002920325008000804060380c02510025408541d00440b18030001c25008072440f481a040c00000c421505010741d04411120502a0148a1030101c00484402c103403448141409824000301d442e202c0948050460400c10390f464420070b516142d001c20403150070344c0003a01e81e002c0030803904001c100303480c044130b00302d070f600d2607481107d50744600b40525090010b007038030855400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 74877645 1250 74876395 74876401
    0x3072d0507090b010c0503121b0a0206060a060e092a030a09061401060e150f0307050d240501050d090203010204060e0301060906050a05062203060f1505090606130b03 73
    0x4000149031080c0e5203442d00c00c0061400220066449044011008001d50f0041206805007024040d0490b00300c01d22010754445070000780c0c407101c15600a107804c10300590000c0104051458464100d6000784018240b484080240708003040341c1c00c2000717180d0b201c8049004903070b1609001100c00d0059449854141d07985a0920040a101a02a1642c03d40d030140c01c02d0041050011070f042042c0c120b903c15240c00022500140a001d0701080c80ca030640130481d000c0c01042c0390f20180c20011403241c4407950360191f4800441e0381c224126480c003000d40815103102d001080c1c00d01c0034511a80299802424400c0c0c03540450341d80500604a0700f0b60082d055400440c00240058201c0e111010000c0d00b14000d00550b910303078440304100d5003140f044942c0010401010000b505200000f03000314a004684200400c049103003032145c1028a40c4200e55071583c824003d10066030921601403804048048030383c1d080e1402000415600008c0e100342d01c030301c3c0009450348000290301d0000c401442070745115902c80c5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 74878895 1250 74877645 74877653
    0x30c0c070803120108152203120f05090f0304060905011d030708070609170c0f0118080309010908010b0a0b09010504120f0c05060f03070e1206040c090f0b0303072d 72
    0x2003c2071242e172005105180041c2c282038003650303401c0d00c01c00040e16030300d5400708840b280700c1007540941070540a00c403495440c002c11440600800d9010840b0010216039401c1c00030f412868403500d1088042560001e12003404503650101202c41240d4091a085950142407104114220049142c04d5851310901d00001036440700070412100311400e0ba2a814941e9507545480c405680001c90340b0940c640040b01c080d6900d02c6c0101c10345030456418580360100400e08c2d07d800d68100b01941003140360754004504c554076076038491001005060450020b01101303207600c01180344032411740100368030a0004564000e85921504c1550b004040350743d69688550002d060000312101d81d5501903541c1c00782c004d0013003194280801128180c41882042501d560b4920300101c6255034804141940174201c1a07080310301890821030b860145019804101010f440e252010301214100090445820304100481c041a80c0c048151400c20340c101c0d401910281c2005031080403050200d0a0943c0a41081041c0c3c080c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 74880145 1250 74878895 74878927
    0x1a0409060509010c1419110a0b01081b090f07050c0102041e0603050709030f02030106030206210f071209060b0603040c180213120f060c0f031a06030c0c070803 70
    0x5240060002c2082d2404500112601002083d054029080400c0b8840780c9980c1c40340c00206d04861403401500c50340c1100001420302608402c20350b801c05040006001942c0107000c001810200e80103800280303003480011490b031040c000c0030703110086061070004020f64010021250498006402190b032a919000f910000b1058000315003100300e40b01501040c241c0c0031b48986401104561100301050b8615641d0450182c3c9114049805540350003001005032204030103001d03645842034182c9170240e03000e0402e00c000c0c00000c3c200390b080035010707050040e9180c208450300226002e0718404654580c42e410000d0180050900954100400000300030a100b1144100c0341900d001c030180c0007440340365200510980c0030788244400d05000c0182d04210410080c0c1c442d00c00749202e5000c110000c0310f83d44505d001c5448101102000c1800411044445035140c4290a020640c65000c507045100f0400400e442c0d000050070401080800140750810000400080c0020480300d07048a0352903405e09240009 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 74881395 1250 74880145 74880151
    0xb0105120a0c121103070b03180102040306020307080411030706080c09010c0b1008060108010e0304050105160c060302030603010b0103020313061d1c1b031403070309020d1208060607030801091a04090605 89
    0x13121a0b0080010803403030003103103040441d218a007c3c24116120001020120b41c040b00303600c01c0c1d0350742c02c110007c0002e07001e001842c8101103544801c0c09525003800e1005040461070387d15403090704210403d2040720707000400f03650080c0c001102c03551a9040100140d50314100a40043c0414a64000300044000101c1d1000e00317540144056401a0343d17501559402da0f07600c500c10030140d81041c4001d105a500c260042c2800300c1d115240071600f001c242d01c41e4010003006421410001c1d8000003081540d0600340604040c0504c20f10302107165281030012010301c8605100002c0c031640d1104450391110401d2043c05803602c3c1d04205903140320300360b03540102070000c120340990007060002e0314204c40718500031a103400070340d059200c0c0c0980f40c4040e451203d46900c010250001e05a82c1e003c04030160b11200c4056084521441035a41c60808010001d0907901c00140741da482540104202c00019074469045411601e00d0750012a0612141340702ca001c0203c0e080c905030b04640f41c05010410300200e5084980 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 74882645 1250 74881395 74881403
    0x30204110a0f1107030b0402060714010c0207061103121e010b1903060302060d2d06050307050303030112060504050102091002030901031a3703080d180b0105120a0c12 73
    0x8010b40641009450780d000c01d81d90401c00ea002600c0400228451081e140d500c14401841589080b1150f6039039100c9020301e107505d40940e9510b90707d14201039010454100500094201111580e420b5150103949124101c1c1c0c012640c00d0700408554070121500071400495a164035412a640e128070f602501a04900444001d16034250302c0082c0c824007038070074441942e80203058185020b508014400242c00e117100075210501801511400104020700d110003a401580004039016250000300340c600783d469008503110350001c02c01044a40352480c000700c0c0580e232106011540b0340e04c6083c40740c02800390001043d0054a210424001198080700130102d001c000d88080012408000e0306050f8a5420010071790031090040c02450286005100b42129520303070121640782035650701307113800000d82a500c211802c0364049842208000a80134a08a0140c01102c01142400345c0d19203042c54030040c0310b071501807948004052010030003400f980103c980c210044201095880b04100711180409005031 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 74883895 1250 74882645 74882657
    0x30b0f0f0c040e0a050717011503152105030903120405121c0e0a030f06140714040b0906070b0f07030e030c06010306150e07080105010e0102010905060c03060109030204110a 76
    0x2036420030078406840c141c4600c0c1c100071440343d441241a4000302070260200040c000310202d034a43c40204003007041d010340701c0e152820800c103d8405015094800c0c0d9a14808814803143c001e1240e54842a10751907034101760420312881100505001c5d00750306c903408a641d018000d0030314003510b91624100078011507500b59000060040012413843d140c0700550005500121980500c0b041d10744201c000c020102c00c000c000d08240c5940c3da032030b00004202c1510858101f034892811002c00e410070300d0425800301e081d0800d6440c254481a000030385120700e001d001c00c08400899503031801d07102d12080e00c1d040b583c41000494141000301142504000c2140c080d0006814003900402942d070201c2501c0c4840035580050080d6400c41c0e8600c07002e004002610420269005030024042c86050044e500070100c1d81c40d40e0301d040d41444001481d40c142c0191076415a030510380c414000580020754194000062140d203a200d07110140121445a00f980c03001c2c0d8413074180101e100c006c290510003409284500c2d1240 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 74885145 1250 74883895 74883901
    0x30403200304061101091515090e010c080f0903070201230c070807060203071703060d080a030b0117071706040f0c021005100b0d0207240b0a0b040f140a030b0f0f 71
    0x84c030309880040a0042ca0a0784025040300788103c103070444203d03c1000300e00e203d0310507180c03060041103070608201001e2a80d100c0c05440f441a8004030b845800080741030720b0515030f00d040c031100e40d0790340325900c0024100b02c5681046002014030748030302004840d1225200d0b03030721030400340710b1795550750a400780c11094041c4080001c1c0e268000000c803034a4550045140464949002c212141030b08018001130300541c95403a2140045e1340080104000c9081d902c00080b09840100014079096101041000f4402c022082c4242c981c0c201244804100d0085500c001d1542c640c80420701070180f0681020079941000e0b03000300d2140d00401d00c461312204030781d0304000c0c80c0e8441020014155007882603d81540040104085001445d002810554042c45001c20b001d04000319049141d20407038205c004095540e030600c4c1083c6444091600140300c041a11410a814100c20781c5600c4054814059103401c010000d07a0140c0301c11a00d00c0045802052002040c17901c02021024100c041700c41d0f6000d01004800 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 74886395 1250 74885145 74885177
    0x8030403120e100e010b03060106170603070b03040b1b030a0e1504020105041a040f1d06010c020f10020c030102030a0501061806021903300b0303091503040320030406 73
    0x488000e000341200420881e09200060320040c203880514098075500d4804921240d07c040240034001c03c5036540309811004840004124400003510692003074002d2001046068080016242c0098002ca81c1d00760a48a2500d140703408440c82c0c01039403c80001208201c0da6140c2a17016550b00c0003040d0584510f910402c0840b040d6940460b402070214805001c1070180e541005c1000c600003d01700d40c0d051800d1345440e40300b0820a290703803090724040304e00d580700303e80c20141e40c000320f8100e00282000c000c1e083c103a80c000f80c80c1c003010410482c0a1804207908400c0740c1e2080242071800500940215600c1c200605010040c3c01c0034083c00340414049040d0140201000ca403032002c0b5181c035400381207910191106841d820005140581c200004100c000301212501b040c03880d8940420703125210240420010301c4e0940c2c40009400344690011302c0078640c2511001070350841a00001d840c01c2c0c1e02d9444d8541521111200f074029a42d045149000d000c0c0d4010020090040d50740c1925041c02c080c0d000e001c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 74887645 1250 74886395 74886401
    0x15060e010803030c0c071a19020318040b0a1d0703060503120a0813080c06010503071a1b030f030a0903120515010f050904020a180f080303040f03020c0405040803040312 74
    0x401d03018507510070400124150703000009400700850010030f80b5049550351044400c00010f002500c01c041000140e02e03024803005001342c89020900340091070905409520400359001a03141440c011516211080e441d41d0f540d00300c02c405018543c004555211420300301c540760b8030048070031502280c0782c1200455907180025140030345852080c0040d107494907660007251181c502a28440b85000e5442031a00050f8a10010306010303401800100034a616203420035203085010f600c4800e085110000f640d080e0780c0305e8411a21240d074208400700c20032054a440c58a5403007007600d01c5070301c1d817004414072551407600d4210500c824007941da00c6040310224209081100c0096891507861000e1261280c159402644456800b0300c07281451402e01c1050750114090364899403981001072038826840d804d5100d1054070304082d007240400701781143d04145215599100c00b510181010307142a804904061007000110109007020b4000d001c54101490314909071380040d10110040390a90480280001140c4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 74888895 1250 74887645 74887649
    0x501080102030c0a050c010b0a09140703060602030406030e1914060f100302041503060c030204080f070308030402060f070f030806010e010314011806030602030c0403050d03050105060702010806120a15060e01 91
    0xa110f985803135002d480944040d80704206030800c55413034240740c074915030710007810b0070013450304440c046161154000080751001008259005143c034084060010a60000076941918080d050001e041e812020080303241040c0c2c02c01010955041d41038800030814245880c0781e2800c0400d046407080d032200c2c1840c5110a80458400c603074036800810030009481c05402c0302010300b1107a000c24811035242d8540a099901c01780c4182d0100c0e40003d400c0110650801650540c04403080252010a003541c3da8004207200181000c2d106140c040380c04120b0040e90001c542c0310303980c082e41c04064485580307000780c541030044980741d020030b22504900c500c03540a40210071040301c01807407024882c1e003490120101341d01100070b01000b069843c01c01200142d260300c0114000d003509418552070711303d9807030124500705080841d0010103041c9001044944c0314201619403140e42400c05d56555600e40002c2040c0c0d1076450250341e0241b00c2c1010f034000380000110544d042c140c0c100030a2080300e484040502400000b8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 74890145 1250 74888895 74888911
    0x702010c080a0203010302011e0e13150b0f040330020c040c051204060c050c06090c0a0803070302060105040906020906130e0a1104050603060103061508011d0105030c040e0102090d06050a050108010203 88
    0x400e4400410f289603400490321064145010b0ac00800004102c09403d02d0b240c1e000708a55410f030091723210303040c40b090748010001601030a203041c0440346980128052440021f003e60401201113440c50820a1b02e0f0b045002a50380d0b1180c04078036802d00030351700d0511482d0ba5000c0d9203000b91800c0d4140c41a01100d9a000c7c8119224031152101d43e102001002000c010000b004030074031180c6900d040900002d8002e5000748000d14040206000300400110507610243c020391041004200098000c5100d1b41110320460300003404c00c20500f003030f2003e0f100d40c801c0150b104200042c15200403c81180c03000550740c050f000b1021680e1050303250811220a80341802c00b03a9000d010400462518800540d4484010300d0046001c983d81c90500f60701c00c1910f907044012402240041c0410081031203100c5103c90410705600700d0794501750219807114100110540110349a080c002040c5200750110b81600002601c407056511041c00c0c150001d15045d07a84812045c1444e000040b000014001d82e80203d600c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 74891395 1250 74890145 74890157
    0x91409060319050c04060b0309010e01090201020601030f05070306050106021b03161202060d0507051803010203100b0706060308030117100204031101120e1207020f100504051306050301050702010c080a020301030201 94
    0x1050082c00e00e50b50414108070340030301c034201c0c0a014640b40c0e8081e0030020803441c00025202d05144040c1400d4a07110890104582e00d04104100580c0c0e002602c141140e40101007030f406600241001810314500c2e4001a240e5414903000080d1070380c0c0028191020110b1849101503d00744500305500d46c10301c194044d00100304081d0600c6500d118941d140300c80c40c03004020070b1070a0045082c038815a031080b900345011a10214a94030b0b0200c0c04180c10002d0a0210001c51640c076260048214010450142c0090390034041500340c1008040c0d48603034051a080b01d00c01d80c6960b0b540101044a04420700d4102035401410212075112100b40266070540740e00002c1401c00140c840011501c45003106a1aa8000e41392049a20640c00601c002c202d845015151550750380322074014480020000c85a55006802c1e00200314200b0354090151025910100c40c03a0588400303100c6541c2c0500619001a585035281c03c1c10b0052054055002c1c05c00c1b4011915804441c0d038546005000302d000c2484040c0c0806c00c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 74892645 1250 74891395 74891413
    0x1003060b0f030706110307050a0c0e0c030c0d02031f030605090c06040b0906030907090507020601050414090703061e14010305060709060f0509011101050f04050f19080c0f0a030914090603 82
    0xc0a0080384500e045e104c02100d0810820342c503464a0703c46c51010a4954070840b88040c0803858096001d540d10905030400645541072800e52802c0d035101d0b08004022080d4044045a014201d000c1d034200c103801c01e04c0c034001c807a40d00c81c1440d900400050392040914800e42ca138608040c108541070b10111040e0205a07130500c074180e42401515480200b11405500521030007050046443c410369000b03600070b50041585604000503c02110400341c00b40c0c0a0300035200411415441c0002c810040e640e010101040c8854000440e4003000003000d40103036490308044082c0450100b4481c0d80d4100ea0151040b50b000782c0351003400790f800d41403502604000034140e0140003400e5024200a0041c51018500071404140d04204039007100d000303580080c8809444000e000034040c0810181c5041400c146c003410100b015512101d050900303c2100070002d04e804951400c000006005c000640d414103016a120900c282c030300200b19100e180100c00400c5980d4928000b01d04110b005184288405002014086 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 74893895 1250 74892645 74892647
    0x203071e0b0c0f0606120c040903140d050f0a020301030c030828030b01020f01020415030504080906040e070201060608040210110c060f04060314070c0b091002031003060b0f030706 79
    0x26039151040d48003400081400241616a0002040500d0000c005440b110740202c50090a000300644014420380c54131003d1105c1503004170710110740c500701301e80c00914543d91345030a03100f24405d40c13000301055801050b100c00e41d0032203800042c8544c5c203600340c2009035a80d5034a040203d003c203001c09403046100400a0000030504401060360681414600c0c41c2010201c44200c05448007442c400e00080e1641c8841d69503580412001c03c000300c8203030082d0300340b5003048103842d815030792294080201622540460203001ca42021105502e8000d0310035035a0729125052602803200a503403480041d8605200080c5480c425510700c2c1c000c0340d00904c84c03480880103420407115410311040440d028011464211200e40d43c0100601d9600c4504040549407450100c01030101c503107aa00c80300c1803181d0b000802903940c1d4044100b24146601009521980c2c070303018500343c600f000a01c410b058882c40003060041404420448104880c4150400c1c00344081d4041800345407402c0031405605503002401c14040342e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 74895145 1250 74893895 74893919
    0x2100905030304031407020603010906050906041a1302090301090305130b120103030815040e0c01030c020303010b0906070c030602030c13080a1703090a0506040f0302070e070e01030221040b0f0a09020307 89
    0x5d10324050700d580c20540d203034000940e561304c280c3c4400c110300d955440810040c00c00c82940c1d50300c8a41114200f104815400c00f106440c1d0381c0c1c10f40d0b54401c5040c50b4040c0c0000509a05580780304001500070002018546800703440d55005481041440040800020b620031118003100d4130300e1a41071054900c2d174a1544c0940c0c0c4100c0282602c1203011900c5290103803902d4520800e843c00101000411320b4041e04070014080b00d01d400d1941045420030001440382420340400c43e42140026a14181c1d12080c50a00c4800c00b03105800c0140114000001e022710b162120001d0a03850301c2c1d240c05008100d59840f02c0c1583c50204180c010700609400c0b4486419044c1c0c080610761000e40c140584501c240b40d9660305003004000c940888900c0107409504c401e15a0400860020380b85104514402c1e0074000e001400155090100d64109a00041c0002a4840210701c0100c602c05501000c280b6041c00e103010447e1110032a00d81d80724040c0c0800140d08504107000d040c2c4059006030150078483c1c03c01007900c0313034 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 74896395 1250 74895145 74895167
    0xd090306020d0209040c0c030305090a02030601030803250201020405010e0609100e150c011505040e030712051b031801091202120703020d030f021204060f080a1e0209010210090503030403 82
    0x540c00d0020750050317156400b40d41c6c10002c955070780b00c640650500d0064112207000e858295558090701c00c1d4001620001102419039410030b139429101c0e5600044801c081c9008070004841a940d20070303507031646405402600554400341c88801d03030204014140280c80c007030800a00e5004da484011940d68501800300640c0240024018000480c584024210607a02030058801d06030741d80d5808200c000b104030200000ba1a040b5000d00c1213000c0a218142d0701d01841c1d00c00b0b004a20095880305000340500101c440d464001e80c100d003e1507684051081e204d40080408040c0c0e00c0c0d800c0b0400c00740b0740c860b444c0e18041d01c40d01040c88030248a9502405010303000c2e892403400911071000c0100141e60340241c0b0b42801c6119039075001141d004204003e08124402031042c6412009000602080d40c0041e5a00c1606c0d4451500f00c195590305200c0703101400c02c2c60150520708a065405110844050b0000c16000d5000e80844040d0404032010400300d0b1700c001c1018240fa0006c0c000b160000c1c0c810907088203 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 74897645 1250 74896395 74896417
    0xd030908090f03010b040e03070c0909050c01050f0403020a060801031406061f2303010f0602060f06060306010e0901030309080d0206010b0a0f211a010c05100b030f030310050108090d09030602 84
    0x4980d000000483d00b11030800341f40f05201c0e440800e003402001052a180400740450040030700002c4070b166111584c8200920303525045c00400303e0b0b00241000001c0540e8000e6400428032841c1d5640c2c0c070406060000203001c2901d0340f020004040d14810000590180542d4002c0c240032881100451969000c0b4080da484504200c4100895142282d00078044c000014103184503d40c0e0b5450420010305099a0b580403409540101c820803090b05104041982c1c0824107a55583d5265903440040322450190300b19681e1040e00c040002c002d041d40b260602090300c11140407504411a4071801782da50301d07024821042030440c01c10030b001c0224411000c9084070708650809490326154803103c42c6000c052001441d460554074602a5007040c90b11001d0b41018a00382000c115840c00d0352100d94541250000701940152200306c1000a0b4401300040c0c41c001b540d94040d00e0712801d2a50319481004164812540000d00800119208000c0030902210040c0c86848500304d4030324590302c59010b904260b0100c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 74898895 1250 74897645 74897651
    0x213020a020604080a021e0705010e09130201030203040606050d050a0b01090b13020c01060b03040809090c0a0e19080a05060405010e030f1206060702040c020309011710060818030c0a03020d030908090f0301 90
    0x103400400d80c00490a40218010302920002e2708241c001088405c0318402d40e03214203e000280104210462808021a6020b28015070380b41d6443c240000034042a42c0807030b801c00310710b803040401d11a0228954250610400141c880350340da4401c0e4005a60010400662000e0714400e0010108680c3d0300600c1070309080c03400400c6e4155103401c070060300e030011501522a030400017283c070411314208020591000074502481c1c144041600300034100858030b881140a034a102c032400340200f40c54040000140786070b138201e4603542c42030300d08542c40b00b0040d02c04880304e600703124441004400100c151190076000081c00c0e800c019001a03210390120014101a42020080198501680310390003016980043c5400640d075819041000401081c904030340401401070440a0155811b03510005004803402c52034816425107444800c030101412243d0303d041d442c480001d01040001c0003044101c0550b00070f40a40e0b1446040407c194107448000c0702c01000882d04114410941c90000c60030494008050000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 74900145 1250 74898895 74898913
    0x3060a08011d010c0813200402030c040527070503071107030317060409030909020c01022107020d08041104050403050d050109020c0c1f030216060504060501030213020a020604080a02 80
    0xd421504404150480b16000041d0490030342801d0141003c0c0c104149042450b44ca070680210004455560000f00b1800319508407480032100000aa420a007005004550303a0034000c110995551192003458000c100c0420aa200a100440301b121808048a211402039458800444155200400d00e800b0310241c9160403400410401041000c0c41c441e84409200d080091095007090000408a900c524148400500001d9000a50408540002401503141d00a04034111b0181c011032b4001800e62540300720b629041e007201c124140c0200c000d602070302c5594454070012182c4540440c6c0140c1408086404040c40d41402da100703941c41402403500320700b4078503201241d41c00e4410030ba0000c012542c02050200385070f40203128081c0c41000441741061401071843e941c2803410304d8001100c0a059010441a000403d101c1d111060300d54004401c121a240500e04080188001e01040e4014150310f4642100300d80c052007101c070201c005400403c040c0c0d031f841d03448000783d03440121110110701500c060 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 74901395 1250 74900145 74900159
    0x7050304082104030801050d0213050c09030105090a06051308090607020f0603130605130c031401180305070c06080c0d0c021c09030b06010f050d0b030102040e01030b0a14070203040b03060a 83
    0x846016103010b40c0824000d0401d810700a042c8581a00400d21580c48070300c03c0741c0160303500320300c031012040b0000c0081019070303402c50458114000e920600b40c0550a050420017540b03000300320890818850442000103458904202035001e09134100140030000400016409141c040007030200244000d0000c81c092032004042241d0703030000d5a250700040c1c0b1060b940307400c010702401281d51000c056003001640089584400900041c41e20014001c1d00d031a1180584d00c5034290001002400c0440207c000002c461800900035400100181c1da492000003000c10424171a00845018026074890903050a04042080c0020302c4180c021809500c01e1420b1441141e01c11034008032501510744501c00b045e49941020031705488020515410040b12844190405070480143c501c030003101c2d040003c2d2041200d01290091246da0044686a58420000401c100f1b41c6610b492051301c5a58040c8001ca0149400b45141c46d0305441d0107001d038005010910201031104d020b10f80c400001844004070907034a901c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 74902645 1250 74901395 74901427
    0x2606091306181115161506030c030b0708090d0e06030619080a1a060105030f040c030813170106050109060507061e0c020d0801030c030b06061b070f0503030c060705030408 75
    0x40b108160f1028281141e403a01341403000800c080d084009140500b0010701c032000700000000101111505c0842a00d03c8041d030780540091640411940d1300e4680b80c0c140000030481c1120400000380d51200000e14064002c109111a01790540b01d6203965480c80f0700b04182c0b50001030010f0b401143e4100e190b001c10b0311a0074840000c1016070082d0030394404a00b41092814246403980d0305003c10744040c00303e60b0742d01c2000c6030b6100c0030042a500d110703151071800718031240041d807001d022801c01080d8104402ca650403070b10304403034048110584c441c5c040030b122030030303510940700e030b14085895010100200c60107000101010f0344180800260096032580664008144c1514440915a00ca0f040f801243c1c040203801d58002540c01c0141c0d0f01d40c5155076641d9124401d000c01030080041a001c0b406540341d9005840130b22501c90700301001012120f0125039100c8641c400d4202c01003001400003041c1c100070084500002c04032780076245d140da41140541d480d50000d4002c40b905a4104100241519005 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 74903895 1250 74902645 74902691
    0x108191e0b01030f02030606070f0201140a1805090907090506210304050102061f0510030b180702060c0a09091a060c0c040605060a05030a0b0303192606091306 70
    0x580c00640989088001401c4a5405505500041c410000c0c030180399075810950b8940d591109030340300c000c401803004070303901c44008001410380350300891000d401079000400c180c0090524140510001e40d40d074108100c1e038005440d445401e410509040c41805d0450308110382c0070602611580c80040c160400340d0110f60b0b022200e40d11038002081c180142d6a040c80241c1c0c0144d2000c1d031107076211000100041810760315204061040f11008030500c0f41902070703045540c082c8402001c41311410313503d094140000c071085800200601407a0001106541a9000c0d1170140d800f50b81c50410440c28003070100004c010729150010034200c0c04080c000075649000007880d50032241c10251295500c0305d4180800d464481d040a442010306101d42220140d00030b050301d52106e000c074004540030080401081c2148680c80d41480754910442d81e20800c00d80041c0c0103220501c001076000d0551201e800400d40d10403040d1056a44000220302081e910800c1c101100040ca00484c00020080f80903818885550460 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 74905145 1250 74903895 74903951
    0x905130204080106050f03120a030b040203090604020301060e090c0f12030c1b0a0b0d0b0d020303130e0c07020108041202150a0903031503050c12070305010203040302010e0d020c010819 81
    0xc040c401200b00307014103801080240c1c1c2c0540d0103401c88000a03181d01c9000822100003030040364600102e482500f24010f01480540115900c0c02d10303084054940c501140c060380a0f40c00c2913000a007011160701d44134403451030803003d07140030794100c4204081201c0440a40e40d02528005034254056000e200408550b0010401007515505503003070289a4081d1f1401c0520520301c0075002c12283c500041160705a011041c0300141d0921080002814203010000c080e40603c8040361344414682070002c0700e000c0c0c0b5008030601540b030f5907805c50481d4a00c0f507510000e00007011803000c240040c41c2414203852018880c019140056880100300d480707201c045498140d0680c80e202001e060541504c01c0d800000003110718904e0142c1161070322070f80d622090510340c3c001c140588032040d42a10a10808010350f50000c000d541d40c0c101414028082c20504020401c3e07402106400c0b10154000a40c10443c00b0042e1101032041ea02e1032000c640540c240b1070103d81c2c03035869250382e10a030b001d803800200d011070103 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 74906395 1250 74905145 74905147
    0xd080f0a0b0d23160b030c0313170901032a030203090a08031003120c05060705030a020c0a0503041a03070804170903011b1215120c18090203060703050c030a0b0109051302 75
    0x3510f1045140c203100070510404072a1402d018017003481107074210791b803091003007119565035101d24000310301e540c0b61802c010303009500c5050884030307840002000b06500007099900340158000e13841d500045000745d0f40741d1410100250b00140c0300600a1700a584d0054546047c1c5446144648803050641d00c2203035a0100e00c0c401d40018400c200c442c01d0040c0340c40341946000c140c01c02242d0307542952014054000d0303040c08000b01c000b8600e11040d4045443c904803040c26039240314544c0c0381440e80c0c0e422130700072900105400b6284118803000072007668403900b25a40c9018440e16261142124106c04c46440e100e4814100422540b9440c240500c0022104086151004200f4424000c0003c4461420316014900704111020f0400c420348500341230b9400d00100c400c4114403031414181c2c5141c03079031080e0b009c4089071003840001080c5a000441c101d0080c0c4c1951081d40e42d90b44100c08544044400d02c81ca804107102280a40c800b50348109100c0c0c4040c1440d00690780c8400004d5a2080b004154a03803080d0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 74907645 1250 74906395 74906453
    0x21b0a0506010b270a0b04090614120d050703030603021c0201030c050c12090310110a0311120403030e010b1f020106050f0a0b0319060609080d080f0a0b0d 68
    0xc200080c0303006200c1d103110681404005940d03040b401403601d91418005850b090142165520078030000010701003030075a140c3c1c89a03076141002c090405403040b040d48900030188829941007a80c040104011000301402103007192070307400d581c00e82103035209608240e0f451001000584a02403022840602000f442c84850300501c0010245e0307010750701010030000c0030f01550181040015820125001da13001142d201c80f8040042440d050800320ba085061781410310303000030501400010b080456155a040c82400341d005030407815446000480d01c140e014050015000c2842540b25090b0340310a040049004028040001d110031219042c0900c40c1601e95648100944c0900c91a4000c4c2002d80704002c0070038684001500803500707071261541d42c01c00000054050000b403208200b0340b4494000c1004655120f050091140d0000c0c01181c055105070f11072004418083c5403940c0c130035110340100e01d95070340d43d10302a00c0c05401c0385940941c12041c0030341540b0000d08107428040143d41c4034604024104 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 74908895 1250 74907645 74907653
    0x604090b031905030f0d020c0a060e10020f0d050702010e07080705011706060702090414010e030310080309100f030b031e240402040902010e0607060c02010606110a0b0a021b0a 77
    0x40c00034840b000d90320b64488060b0740041c00200c251405005403500c0261105000c4c2800c0011b4420241e201d6254002c482c52038013000044ea000c1c1c5205981c0400302c0301d611150b0035440e8201d100703004040303210081c2403000740320000490700304070342c021500c1c800480d00102851149142407120340142250f600081024002964410707001a030800740d007040010b80d418440c01013078840c400d50130080e0060724041e000405110102034003188010301e29001b00102d0364900440c545a80055030000045108100d0010302060004140c0d09e10080003003a0505941d4a40e01c00e60310341203080a40f5040c15107508030700c1c1095800b441550540198002c948c81403080c41e010703060600070040c813100c40c1481c24104c2c4420000f40003909035440340d0b06660000d2081c41c2030006a07115485043c1d21a441240001d5074010401ca0741c0060782d9841d00c907002030000c1900e40234260390540701c00c81051415400f909407000418560840b064000c250328030018603104007545844403041003454450b0300c65008a802400704 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 74910145 1250 74908895 74908903
    0xd031b1e0b061002030a0e0402070201091e0501120204030302190203010f0f061701060305100b1c0807030e0307060c02130b030d050c0d0918050622060f080a030804031d0604090b03 79
    0x90248040d506e0036210301c0019180c0078004c03070102c1c0525800b20b08170086900414090000c0d2005500540400607421200959480c9600400380040c110f40044d410b20f00c641d0007034030240e035850380141c2800340d00340f41400710078080b501c010b2f44c0c10740d250400ea40030030303000d84140745000002100c081082420031005541d40c001c41c200c10300e040da04d040010800300f900892000009039040c00040b4800007528001480340c840001c00204c40742407038824038200400c8600511485109848020310b4205603020140c9848880c815a004030303501c20081801032614603090400d4041805001071181c2482c400304c1e10b003585451003080440c10018a440f0300d0142000b281c2000e1005151504000c1d0911403880d103141c100d06191285562202d0115002d55200c1504000d549245103181114038803054102e0003901042c41030281c14203906102080080b00803c2c144a03586c0c15840701120b40c1c6881e40c040303401010319044c1c0b4101d00c100d0101159190b507200700510052440c1c0c170011403140c10710381c105410 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 74911395 1250 74910145 74910169
    0x20a050f041b09080618060106050a02010f020a0f110d09060e030a120f1202030c0703050c0312240d02030a0b060a08030309012009030d111504120305060d031b1e0b06 73
    0xc0e1b441c031215000504440003424506588a03440c2c16900d070031080710203078050640c80880390000c42c00800c85103c07441e40305041e552100c45d1991030040400c5141c0000c4d403102269032405001464241d13081c040140250010300a501014048804072416a1118954074107030f21100c034000350900b01070005059100301c6503a13017683c1c69101140b0358100740780c17900084c0c41560002001c0c00340c0403030b03002d01440040c000d942e088042da040503915071405002843e4005c941d484900000308410300c0c103c80e1801c080d0074250415501034001c15000806031200c0b20450002884142d0003130600c1d80108078000180050740c0903507810000450f000c0349104210541481e1414442a00482800070300043c0d40c0001d91007100e0007040c11720110480241c0c141c24103010084c00040804002c1006000403c8410024105410100d5800b0050303a20340404020407509c3d50748014000840c0d41540c485c0f209030580c101081a0311440c041c0d401150301500350401001028002c0e29280340880400c03002e030910901040f0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 74912645 1250 74911395 74911411
    0xe040b180706020a11010903050f060414030a020606061803030a0305041a15010c0302030408011109030f0d08040b09010902130507080c040602030a030e071a040609060c020a050f041b090806 83
    0x5102d0070000025950b00e003101e07010702112040540300720300fa400f0742200c102031030308070060b01d00341540c04030f003e503480700f041d2001c54002d40e0188202d04e032403a010080d101468003a030b024056644452041000d250000540316000c920050024109907404100611581d6026100402e0504e0310f4100f216141078008403c4481c0d071a59800c02890032080750103003540304000d0901c401d0040351800d0803840d601843e0021145507107403601041c04c1804200180806103002c8044551071041a819281c49101122410300450700000101e00068184400ca0ba40006401c00008804c03420ba000948040e9600c540100c0c09655403050010040c0d01c4041d4940c0f19126034001c03890180f409000954070b208080c00c150030142e0794042c0b40c00040080c014040200342d03080100e190050f0f881d0307441946074403034418000070a1010340d00040460241c290b008240750010b0450b054140741c64240f001c10010b0f52000f942c415a00c40f54104a1040c41342c103503e001000b0703a075806141c0d0904040034601600036040701 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 74913895 1250 74912645 74912653
    0xc1e0b011703030105062a1b0405160804030c1e0f060b0901030b0c0706060b0d0507080901090206070803131a10080109050303070f02031603030203060f0103090b0f100e040b18 77
    0x4071041e10350070304845550861588041e5003c0060607190103a5501013048510b50003422301c0344030b4418043c14440c10410f8216030030820390b103603000306400c1c0685409040d804240c0a80003d0301003401001e0000c0450301915850550303072034488040103041d02c020002c0f40d01140340850130b018440703103200d2101c0c0300e00c05a4005200d0350440e11400100040100720401d440d80c0050302404000d03031b54110500034546044056201e8180f505000003510084880c100081c4808000400c50360701402a0b0b60300136000b41c44c40d80b034200705490b000e049610041c4504803480711000407e002801d02072600d0010224150803405504001001d0700d54a00203a005244903030401d1140340209070088100c035044009401d04034058000342c0340507030560040107075540b550300d002c184140505070503800035880b400702100c10361052400c842c0107504481c24408050160109032002031b0700651441c1c030080d0007503c20100340c0d000e00d5491801048400c8101c42c101d90305044142840075050480402904a01c2c40c00064 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 74915145 1250 74913895 74913899
    0x4060c14010524030a02090a0c080f0f060105180d0f05070506120a0b0414070e090106050304030f031a03071d0a271109090105070207240c1e0b0117030301 68
    0x140e110400c000141e018807080100c0d083c07019607001c0145007159a4060305200161034550501001040448664004a1341c1a0005a048010660700c24851345003c80d14910b19101d96004650903002414100c15044008140c203540c0c2e900c0728844442c5601c0b861000e0940741d5035103040c0d420700b90585d10aa019410078082d182d40e034104d60854540c86564003400061058107000020003904d208802058034403406000d2004595000401200005090b01c2c1e03104166642c210407a5540300407503020300050034022400003010300c29003245600c021224240340e548400311000a003030003c0340d44120622a030fa007015040240e03a42c040903500c1040c84d941001024a059001c00441000700402803409000e06003d00410001003e0301d0203805020342484c070030703103041c00545008010582c0c4901c090710400c40d0005928101c02d641001c000d014901c1140b0000440105441803410b244044840c1c4800030106034440c0e80401040200600176283e0b2001545040080d4099500300400c5a00701d420030401 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 74916395 1250 74915145 74915161
    0x60c0905010507030c0206090a06180b030103110f030c03060a0c030e010203010f05100314040f03120e03040504110c01020a05030601140a050906030403030e0a0b06041103090d180b04060c140105 85
    0x2503c2110744c050500250500452002440c907114030710189510003032a010115015034043e07005251800d6182c400c00751551075101d041e80c580000d1200070100160304c024a41c59003010070340c1d150b02c0705e0084c0841d110003001c0c5000905028084428642c402d80e240001181d45525001e025900203258000b1450b550514484100324441ca00a060052903180004e000341ca210740d100210b40b4001101d0500c260401e8070703198901150841d0203030001107042d00402d800404038868904803050540055180c40d14140520014141c103114544070030805001440710300000380000c051480da19690590740745403620014100b0100418028028082030062803e0203820030210703020b0201c115081d5440766503c0c42c003140582514004942e80e80607001c45003080010000106000b49001c40f01071086003418041603202d400101c40041c040d501500d0440026400b4042150100404400b0b1300802d40d210802c40311654015803064001426004586051000040b00b0100c45080e2030001d10003401c020b81 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 74917645 1250 74916395 74916397
    0x40608012c0c0405310639021213030606060207030506011a07060e0c030606040e060a09050c0a03030c0b0c040312112112090601051005160605090604060c09050105 72
    0x4030395400703030384e50b28045258591089590000201804051040c5441c00d116003800c1031001c1000300c461904100303035a49a00300205a007030401918540014000ba80c080c800780c03d809603c0e01c603200754050400300c91010301081d001000c810741030781150141c003459480c1080807070b0001d40c0204119042241c041c8009140800c1140c119640d407000104603546400c0721007814418618010002031412541d01e449503130205083c280c01408406850b41a034030a03052105035261112881d03020f8200c1000292480c1140c1e00003486e05001e81e084605000c94800491003184450304250049140b01100108100c2420f104c00c0c2c1c00003516000070300b4180345507a0524019203800613213041c02024000388003104002c10008407000d001c03111886500303a0101c05200d56521004c840c0102480d01400107502040004541d030488101925150030401241021541d42d0044a07414501880d0040c8101c04513500303004027070160346104080c2401c0e0425283c0030003103070840003405d0240014240704010b2a81c002c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 74918895 1250 74917645 74917663
    0x11d06060a0e011412070207080309010507021909020c0601030b090312010501030902150d0617012d1b110f0c01091a0403080a05030106090f03080f09040b040608012c 73
    0x4105244003840040061311000d00048140c10030080101e83d82c01c2440740c04200740d0240300b0903029215a2034881c0c045c2512441082001c5000c99001c0003008014100303c450800350324500c00c0301c02411038403801c8500c01c0c1c0e03101310303144956039216400500601140403051500250f03040c0095240041001c240501c0c0c0ea0148102c034145682d401ca484155180c5030314961516a5180004c0e07030358103601081c20000c00250190480c001154032154040c0c150511940c1ea403140c0200010541448035202046c5a81c1108116142c090f220701da5189084408a140060708409440e8019401310707a0f003200780f038406101e81924259201101c0c403003040c2d0b040090001034403d00091010140401c1c0c1d0518801e10466100505408000403c6541c0070751050165041c0c41456440b5220f55079914080503901e015400054038a2404208107030100645000901440d8405072000c14040e0920000a040711450b5124520594440407a01c40724404814556440f05a01c45c4242c0c26813844c01a150343d4513010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 74920145 1250 74918895 74918897
    0x260403080406050703090506040305040f060801050d11010c0f060b04050f130803091204080a031b08030c03070309020d0b0a0b04090c17030c06011d0703060503060a090305040518011d06060a 83
    0x40010400d018400c0d01b100503170940020403203140f8142450000c00a5000e03100d016481c91813484045195841203c441e41207560040c41034000070f6182d141d11244282c0381c142c05041c0214140e0318800141c00382e220704110342c0034400010f100200383c0c1c02d00c001e60b20700034540c4003221100010130290002d003206809149821000d030a4036560382000c000d26110030740130700f0b10130b48901140000b50880000368040440d0300c2940ea007080812010318102090503035035001400300c03030207000080a26091101a65100350301d03103000f14406010b50041164007490001c107030781564054007000064980c5024006240009440800404000b61581c0c010150315010384842c840b01c51184240464080050b10900086001030345d1407942e544c803034424200d82c0301c6490b140b04800c10002516260007807145a0403268084c010f05020b941e0503d101e001807504103c01c50510005020205203511200c0c0c00ba2009460071b00d0f007500c65410480c1031880b010007504500302000441040014036143c02042d14400505 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 74921395 1250 74920145 74920151
    0x122604031b06060f0801020904060506120106080403020312010801020306040b2d150c0703120302120411030a050f100b030c181b070b0403082a0c0111030403260403080406 75
    0x81c038501000034050390341c013490b03003c80c0621011a885a065006140a21044808101e01c5a40d030091000358042c580715007542a05020040050500032002141d00500c6031050341e00d440c002a41c20400702d84c0030b801c0041940e40c04810082c0d981018407405803844421140b03074030142c007071510440c03003c4014060a5004480803c1e204002e0300e0700d031803403480c615031034440035210804d030001141c0c1d0b29800d21040da4841102919042040e00134401c54186d80c01c2103200340c039103a440751120b0144050b4008025018801c440d000c602040c4140042000e0b0104000074100c949400c003410410b840110000c50710a0300b02002c00440e580d5110000004089005040c003103c1d0741c0c03014012881000381e000c400d00d0203000222001040803041e143c91186200341c07034192454482021441d940e07160050001c0d040298041c0a190500c080340c040d0111050902c0081585401c545040c030164205807012004600f0300c01c03800d0340c41c81851486465556509003848690f25003a140100800c8020788058a43c981d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 74922645 1250 74921395 74921447
    0x6060916030b1302040801050417030609010303110307050114010602070602010218090705160609020a140d02040f02090d0f0b01060203031303140c03070309150203070302030316030912260403 84
    0x4500e407030b0811680b1240000c40d184c91b0307104600d40c042d200c1107404844254240902081aa1505c1c0c162401541c1c044d0801a540c2e085aa0503106c41c02c8280981c4054482400950006042400b61218000006c00c2040c01945840006890035180350400020f5900600c85460400c0c458186002c00303202c1103d00c1074080d03c03805007d03601c600c1100c1034000601c040c41c207640280003454020891161003904d0001c241c0d59108100b0204141f00400142e010311411100c0003d49042d4224220103500320300014507040f074040014810068001d001c036800c10b540c03075503a410f1044130714580b0700402c1e1074006545180780c800d03441999029628402824460010700103414103449900703a802c6000b5400403255928030504010f0006000c0b885030024001078440580000c62010040d40d00c0d95505800071411a00d803200c2c05d00124402441e0f800030950783e0200000840c40c00c00300443d5015841d1640780c1250702049030400c13880ca110fa100d0301e410800350140000a58842d50840320342c0e1007201041042c1e1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 74923895 1250 74922645 74922649
    0xb01110c1c140c01020c120c010305180109030908010c0302130b130314010b1009050a0605090d0b010e040b060d0803010e040c0807060906110a030519020309091003020306060916030b 80
    0x38001240c041d10548418201d0b00c01e0650000c1c1c00c03035102c88241c084905003c141010000b20101007000c2030283c1d040080d0b81285940660449904000c86d500100360f00c5070820400e40c21144611000c0d40000c0b010241000403440030301c681a07052640b4a02580b405229941040c9140114420580000307000074850085c20381c07144490015603800000c401000c0b00c080801800b030300030b490959104035500d051050030b142c000c24813030003141c0700070340011002272070204181d50076080030b92215044044074070080700061164110601800c10650401800d05260070203262803a4020b0601d80980401850100410841010340303046400c00a449500c655842c07810403013085469120203c0c3e40315142d000f040f201d81100044058900e5035903006218115030007100d648440d81c90700500030800401400c0c48820718405008060203603401128901303001070340812044103044030101090900e211003401103107414480d050300240304031404003e13400c1c410713414140e0517200341e0170781c003030550340e0045802d19 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 74925145 1250 74923895 74923939
    0x604030f051207080702100603200f09040812010e0106020a081c0606020309040f0203060a03260a0305010306050f04030e01050a0e030601080307051c02100b0f0603090705040b01110c 80
    0xb15040702000503443c24003100c0545020301c01d03540000940101d4201e0f407100b003004e100d1102181d80142915400411000004400c01c01c407c0c1859004a0103000341552074603001da103640228403540c0740325594001d4003461030303204c601030b08402d0003082d9030710041010300e0340003c00b2028583c00500840da610600144230606200c096220481907080c00030004a160b004000341c401c000003541c1c02d00c03c2202c4680c000b0120701c81103400c10f511000c00b0380c00f070000c601c0841442c40d410404247e6066951a034105c0c1c0c83c1c450f0408020078000035241d0005204000a170300440e40c01200707600d1040f255003005d40c2c020f454100700c4107443d410042c1c0826800c80140c81a1492541d012014007650030a5840d610616181d51042c0c2c07041d100340c0728dc4080804103602c59010100020322690140600040800c48040541480101117034010190b2001a00c10f584510007035005804990003468181c2c940020300c816140c203900801d051100500601c009a00d000c25400c840f528103d03a00d4100c500740384508007a0b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 74926395 1250 74925145 74925157
    0x120409060f0303050d020a0c02041b030506010e011b050106031e020f04060b0d0908091804050f060609010314070504020d0207030809120d09050a0501092a05060f161e0c090e0604030f05 81
    0x405810454513500d048bd103549020003408051ba0b0900255513200015074107030200707061480c00201403920080d201d00542a00c070302400d100b13000224400e43e99460304103201c0b004c245083d038101910003c2e0011481c0c281c256801c0800107031014070501e841d0601c46541c0e80541c4610000d071076107403d8000d0400608030100d4400d008010080725a0041000c580e00d98003408031011106441080075243c802c403c0050040c2c45840000d000e1001603080d42e807001c0700b080d20110044060300c200600815070795a40e00150000a030404801a2901024140203004440242c0300d51096001aa99004c04035000d1040792201c142407103000c140300e0380f84d03d442881d001d54031030060065440c0c2078201080004203100f1000b804682c00701c0a81c0a010240070300900c0c0c1c41e51045c0c0e9440a810003070508005c03031420150001041e45070052108224a488400c80d46944003000a0a4074086070380b8020491014001380280402100800682020350650399590380040c001605000341000c03203118192207001101d007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 74927645 1250 74926395 74926399
    0x50f150f07050717040b0406110705090105061b070b191106010b0901110601060329011b02010c02090c04080708060402030304120507090609050a050f1905100305120409060f0303050d020a0c02 84
    0x29071940d560046c0460b035006030003000000390810000170b2000e00005002d8041d100c4c002c26080090340b81004012013580004140d007407003000381c0c0c0b2860002c0001d1201d8401099a031043e00d83d00c0c001a440404288602c2d142031381405400840030f0544800080d40034151040e22402a648885540c0103a9004d9400b1018842030700c1030400115549603d41c01c1803408403030200034081c4145c40360034180040d00220018500280091070b062200b000e018004121203401030500d805010040e030040390041e28102c4180d0082d110000b81000604001c02240380107141480107041e80d4140f55000980f24840d41c85548200e074192035480c41440024000100180032400302000120f80d035664840207000200c4003d103180b46014002422042400107051107030300e010200c0074034042e28403400002418007038489041c2c0d618904020001810410041003408181015252039034505286a025a00d1540101c1d0098902442c100b0009821000303451401d20f0080000d41c4440c40c0704002c649125031100065 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 74928895 1250 74927645 74927647
    0x80a05040f0f05040e030c0307110f03010504030e09060406120204050703060b0a0306050f062104140a05030301090e03040b0304030e010e13020315010809280f050f150f07050717 78
    0x40c00b40c0b00140381c44210392080d50f0a218503a013001080d81c8900030141090810f401c2006181c0001d500423900c0c10f01000e00030087c480040c021030100c0c0c21504111412004104060441c10f03044c906400240c1d0301030004c441c1402461b040c0082c2d10400c06500038005e000d180c50700b02144207140241c11010150040007031042e29904041c00c000d01030465446818043c0b0700c131142c190b51500744401181c24a40071030420140860400c00500d8400c0001042a10079600080d204141058280420885280501c00a54484d41404000d20071a040000c41c54842c1d40100003c03c0342c000d00d841529845a05410045649824900180c8856040342c42041d40401719000c1d20316103030810b9000d98052196076820300141081ca00c0191800c4070700303a95010f15070b405501040307035100304015030b0071510303802c01880c1c515040c41d40d50319540c0b9100d11004403003540150001c0e4881c003408000f05000092041d1101d24903051580400740942c401a2408040210005154092080300120191680380c410803507 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 74930145 1250 74928895 74928899
    0x60b09070f03140f061c08040b07020a05040203060306070c050a050a150c2109060b0603010f0e0702010203060a09091e0503090a0b0403022b05030f07030e1804080a05040f 75
    0x6011035003580300c000c08645011280e83d181c0c24030108140c40307008190802d4820780c0360001080801020113402c0c49640981c2c1451000050581c00034000500c1c04084840d240c4030f4030710402a44116680140340118814402c0020380e40c0d001403ca600300b00c1303605205103013075a541000350403ca031310040600030344074080320030302000008030204050b10303402c21041103442c2100700210784030003a4410303500c03084000b40d4581900d4070061740300d41c413940e00c01c400014104810002080741d0360000d9100442d15100110208101141d140340700ea0b0000051008602d07620f810400109029503c0c01840c00c21548c130711002d07040012160724151050121115511a00c00d01d1809903940d40c040303500c0c14081c0c840d000bc0011456900b60944050320341c01001e0400044241d502c0490181070b1161441c095040c1100c0f1801149003400149004060180c80c0e0360b0320651820f024002403a08030205015155400e0b404400170709550f9500d030802e505c0780155640711920101200d031400740d508001c00c072034940100 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 74931395 1250 74930145 74930147
    0x15041506080606120a0c0302060319060b07030e030d09150c050303150f0a08071a0f0706140f0903030a0506040b2106070c1a04020114030406090b01170705040504060b0907 75
    0x10b10030101110303660b00840680c0f1358581c0b507102d0781c60000c00303030200301c1c2d0148014034000003d50342c020041d5032414a4550080c8401042e1001c5a2003031082400008801e01816400340c6800e51402c0d00760000c11040700d001c0d0005142d20554880d0740c0c3c4110115103003d0803a8400d21494050b2078001e000c032610703424030004003003c07103040c2d00c0c0c614402c0341442000119030804c03400a10454910b4003f07802c40030f140003501e01f07038100d4801186248220400c014621490401c015003001802220001054120740c410805d6041000c0d02d803d4001622004103c1c000c580007003140d9101c040c3c03020200d1152076800200700a40000340900c0e90042c03254403a0f100703e0741c03907121030401c00000c0c1080b07440300d480300e40040d260700718178140162400302c00402d840e180e030203812a05a0024410300d8602581e01c003595030102d00e80c101307607411145143c5551551040c4602d54040c81c2c098180d01008040400750300000c29507959140c400c0500132500e4600040905c841070b0f000f80555100646402840d1a040354 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 74932645 1250 74931395 74931403
    0x1050d02040b09030c040501080a110a1205060106080c030c040b09010c020616050705090907060c0302030904090605090c011106070c1703070203030108061e01030311030c070e010609080a051504150608 88
    0x8043c5020f8410700d0060703215468030b4007400f4100e840c000c01a00058842e520360b032240c411504409900070440382c800240301c069048480309014001c40107807480d5410060002c082d881e0162819501c50703010300c1400120000d00b01210704a620b03a06182e07a0312201000140c07500f028082c1c01079406000460003550480780850a0030074940710f1000ea924a90b1074104124509c50b003906d82e50305650100c40c05005c0c0601401d03081c00e1490107801200d003410107140005040e22880141207840a8862090005100d000c0040c026007200c2420100d4035144079440c01a629030b002000c020400145000b800e0a1041c20401032482008640400340c0c1ea14000710b010f50f80750710a1080f1405407054000041103440300601020014241c1d000308003550746103807811566069404e203c00d80601041044801e4003108200150007481290340c01500c5614040001d411810360f80e0007003c0a4020240000001d100070030701405921442c2250725250b1998101445501d15040c0c2ca50700341d030300e170070800300c2c0a0750001 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 74933895 1250 74932645 74932657
    0x30a290a08070b070204090c0305010203040503090109080309130f0e010e03041433280e18010b0d02120109020d06090c0518031903080a0c11070303050901050d02040b 73
    0x154150034155034a82003556141c0c8180b0981102c11814403d01c0010b01d800d401020b01140140381c85000da548a0b2030312401c82e07200341c07821141c690000442d0045541c00c540240018032007800a1810b003180180441e104c02144400612007a80c2c60304100e410b0b4449510056082403160000c00900d0b000c1c00c401a039a03405806404901900c40030071485902c0c0005d0107481078020501c5200302d0139110206550814100104000c1d5503005104a0300c40e85080c1c07a0284002c1485001c1c01821401042d0203403001002c1c404950154400116180c003030b0061602190440e031020001c5a92800c410101030000d0103020400710395000150300000d041d0020b500581501031101e80c04000480d80e410305078003103610071004100440e80c103204212012080441069070f288000e03094800304014010324000911404504401040c00342d0705008141215100310351180f81d0500b05010b07555a0310710125501e40680c40700500300000060913801c04d034410800c1d580c844090b03207c155207407501d5001c02801030b0020 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 74935145 1250 74933895 74933899
    0x13210306090f090302030406080709051305190b01020a02010c0c050409140f0307031706041401080718090c030210030204030c3002010503010b090315070e0a12021005030a29 76
    0x502c5503000b100902c030700080c0c82d038181c009600e0903207018410b65a07004014404824401c1c001d000050726200e086568841030002e00c400103c1d4a443d0b01c06a0740201c60b00c9990720a41d01d05840c0b250566000140a101c840d02424000b0031680a80b40400792084580c0145400c1030904062100b04160798040b246a11030700c0040d500341000b0901c20603900c0c025440d0180024030b02c04a640000507009011030303000071010b8804510002c60703a40200c41c1d0030342a44594115402440e0820181501c404040b81810340084207000d589240e8440f07240f039081600004e88152048940019080d010f0340c1128001e50f8400c44c0d508071b0943d60a003903d40c000359100710030070014040208104480b13a05020000c013681c140c41d071030b00f180d00b02041558a50028000d05402d4811a0582e61b0007480c4003111074461030351235450020080f24035081c8615107000754004040c2da4240040200141c0e034411000c41c20008901c0d005d40ca035070362000130402518450004038040c0700e401301c1c1c0f0040c001b10110f40302005681 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 74936395 1250 74935145 74935151
    0x10e12070305100c0215040c031211070f090c0504050a091d070f060f030e0601090506040618020d06050607030504030f0218070804050105180a080a0203130b03010e010e0f1321030609 80
    0x1000b10004040308200e40091980b08c841c2d100f8000905540b90100c0008201d10380b1529443c001c10415103050040e4201c0700c1c15448001d01045140164052010220380e1468200e00303051420000c5080c0344014028461842c0e1030700c200515101c1c0300410b4400d11418003044621140e55030100600314015809508002000e003621304070403c1c0207002d000f110420b800f00406035603181c040042c00172702d40034252650054440c01c0005000441740c0032102e442000e554010ba81d03940d01d480c1b001c100d0300558420340c080c0600780800004a40c00406a0701160b4010111540d210200d20009690b03070104040141c08401590610101170751003014a80314a01c100001c00040d150107400208004142c10080e40d29441100d0b400300203484000508060a5540112420305005860b80600000d290f00120f000e0400032004002070108240480d00504481069080d507060080120310f910360b004007840d0010420000010802120b86620050845050040c4008603100880140609224440c45800d41c3c2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 74937645 1250 74936395 74936413
    0x80105010608040807030e03211201090e121305060a05030a0b190b0c030c12030702070f06050f0c1005090c0108060909031b0f07060908010f0b010e12070305100c02 72
    0xb0003103200502443c0c00c02e0815080201aa904a0f03019802000c103d400d400703091201004c0035503805840e0a100d030588003584c1c0700e44607070b60104002c8105a00418100f800c141300c8910300c100108201c191048020a8203035616002c140000b442c0c4484d5102940040000420f441c010b0346c0139015501640703040106002c410070303910400803070412841070314002246d181e50422803503400310b0040c8121406002641d041054000030306040150f110a0498484bc00008203d25181d042c0000d9000c1c00d051040020300504001f001449030060b0894845142c05c00944032007240420401100756241c1c1da94203001c0c41c6020b0000c1034545180c3d2020f0780c0030176606800301e410f5191034500030344280c0048009504000141c4445540030807400c8e90851b02e8060b130071013807500c031009001c140d000d405ca42d01c03030b01425072030030070843d08450018011003000b52a01840058584e800b411100510408a4210344e40c0c4400b200380c1418030620f03034001000e40c80360f109582c043c0009504010000115502070303aa07050 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 74938895 1250 74937645 74937647
    0xa0614130209010b1c0e0705090a0e030409050403110a03030c140316141b0604140d020c010f050c0106030f0b010807030f02090403140a080910090f0209091204030c0801050106 77
    0x14903100070741c4229200010b12400742120081c00d100c1c180c40f100528080e140c101c481017100d082160081d0039401002050110303003001011190080040e100412002d003460481c6a280d000303034080d003c10b50341c440f07010905141c0b1541280704041507150555604001a140140013012103400500125001101c1d9441c441c03460800d0720320681074206440546080840304a84d1040c00301e281d82c1441e80c0a00220b44003c001c1110880d0f540c070010010a09400e203400e001880006103030107010720380d015198019140e42d0216801211082c2801e0100c46111100026900750241c04000001507107802c0e000020301c958255004e038114004c050228050742ca80748141e40380e6046020240454400c003400c41d0060034000b4034141d02038080d181c1071158502005181383c640e804143c1c2034001481c950244020b0180501c070310041010740010403c483c42213586c41c1c2100903c07000d00a07104000d440d0010720348510038003034128600b6807030351170310394071034992a2006070b41c0704902541506610340300001c0340300f03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 74940145 1250 74938895 74938921
    0x90610030206091003020715050103030212090f010c030908010c030911100507030c050319020c090105030105100e0a0228090503060118020a02250501020105150a03230a0614 76
    0x941d40250580340743c500c0aa05110700c0700c00341000441019400c110300e002041100c0c3c0f074801c0c0045c407400003191a51560070009d141010703161002d101e0120400c04405181d440022902c5a07000a0034100c200040a09060322100c00c43d80c0035004550070201551006941a480107500501c102020a0015144011700904605c1d03c84441c0105a0070080e10002c00d000709800b0290364881c034200c1e49400140b4803954070320584044000096441000e2460503031401d608810b0141c102900204154030b0681e5000440403100d02c101c500440c446400303c1c4c44e485a54044540686224401c214003d400c0c42003145601400e1001000080108402050303510b4041502130403601e480840030300407400c4994242c020352080800c2d00070b5104002e010a4044001140080d800c400e01c21032445203803504001a0035128000c104413540311841c20031000b81e68400401000b925000340f0305680c4070f0205004076a030b003040314441c1816803003900c0381c4c002003080070740019249542950941903a62600c400748034007 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 74941395 1250 74940145 74940149
    0x705090112033f14090609030f0a030617030a110d020604060c0309060501031112010e061602070305030c060114010f0c06020d0b0604080c041b020304090b0612070305090610 76
    0x51070343d000034030450b036075590f0b41c02c0100d070070600501e54443d03a00403152005000320b1081c04950300c503400c15040c1500407a060303501041c2e0310043c020030714000d82160744910400d40c0162000c000865603843c03a44c400d41c0018042c00c1d20703071844241014070b4101144e90f0740007103c1403c000788100c40c0b04401498041490301c5454a40e80050071a500d860ba00d4a010345504820070303041607070310350903600800c0c000c1c01100c0c021170080d41860309010b00282808a251301c00c050307003861a810400050007019001072106d0b40820701d180603603008404144100e09080080c2d0010307142c1c3c48085100405040c02003045412546ca298039500244811001510003452018212010441e008900408506e00ea0010080e0b0890224009000f80710709000aa840d002904044101d600a401424150805105a407002415154207501d840a1018000c0da03178400d6014030348441c0c0c2c8030604501d0035110403060381c000801c8003003502007a26203000e006009010440395401144240300210b0000e811000f15002 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 74942645 1250 74941395 74941397
    0xc010209030f191101030f050f06130c050d050c070c03060f1b02030901030e030c0a03050d050c0405150c01060306020a030b10110709020f040b040f03120305010e01091e020c070509011203 82
    0x84040c1c503031031398100c0c40c0301c02a040c5d06143e10f03010141c054840c503224091240000420036109401d102040c8040f140c9a460010107036840c0503001c81e81c541d0010145c900b1604284004500385d0381e6941400e280f4002c0d0207000346600300240d408010003a4541044001c0c220303800c010407650400c000c004410706520301d091005600200540304465201c2d4210030b401d6540070040328540403404110300d00d402c881c41004e800040c408038070850300160740c0c0141a081440400c02c5402c05051000050f0100411715141045880014030180f09000a40144004581244045445000010b400740152044115003480360041c003d0448801d8000c410501c0035019050003081407500b4900018001c1d48122801d00e00441c0c00c3c0b0002415000c424018000b50001200030b100b41e514500d800e28400040707803044400e15082000502400f441c03290510704441c0b0fa10310101d086007284049488100140d9000c80c8064000a44104001d40010b010021188180d0700710520b0f80e65206800c00030000e100d0020 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 74943895 1250 74942645 74942683
    0x5100b18040204020705012a03200a0c060917030a18081603020a02030d030c0f030209030d0c0206090d110111030325020f060406060612020a0905010f11030c010209030f 74
    0x34015043c00d0b8050a04035100e01c000094898400d1100d803080da000482444500c03209641e10500c250b49800340071602c66400302c440c84e000c1040c40302c902407070289140013010000c0041070001030011680180649507040b16a40c02c507001440c8001203650300032900c01c04898100a02501e0702c40e0141030510303409400a61013401c0059045001520340245d00b025000c41c4280c0001c038025a03000d0101303114442d4079860024800b2000344c005000d501c20181044189403052040710821f4a020840680b030400b03d00d0b0281045009100080940c054149030310340045414056a00700301a80d11000718000003601c0d030006501c41c00c12816543d200032180760b4941e940b480c00340e0f0440280703840d0105416180d0300503500025041c21060b07242c040101c4040c0e44e1151542c108202c5190082d009603205000143d040d484c2450b03510003c0e0202105104581c1004105810060010704c01d04850600d500d0307450a6035035401c0711038181340c040c0d000107403005c1c0b0034002c40700c1c201421030700012190424a1051855 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 74945145 1250 74943895 74943901
    0x80c09010b2101091b0807050a080406060e070f121104030803060d050a0303050f0609060d11060d020a0c110402091005071a01030b040b0610051e09090405100b18 71
    0x5025150440103481c0c07415503000c40c00d0440002d0340752409029040c501000aa00301c00c0d0440216058164990780d0107008450061040040d0b120040364050180d5080c8450b49494510380b8800804455210803040c800f6001404030040d13020102c0b000042e0780fa55003c0c07080e00391027252130460705284502c00c00c031003003040108009070300c0d64040e5500a10003005005e101034035803115820820281c0c01240000d03035072000c100b1a90264900d06801c08803e44900d5581d29100000c00c4109443c2603015104195012501d50755030758030b8085640003205200150340310341c59000d01a0400c61090821101d2000c0310b03052510030708061007619880c3c4c0004000c0c00c526000b807541565039034030985041e44e10036400c0000d21116484002c3d054000e5200e078520503400d00d00380c01c20105118010381654859207480b00300458899119080c0c408452005658041201383d102448440b031150000e110b4001080b88100018084007040c4000414003170203050204032010303010400740742c00c880d80700c2c900410b040c0e001c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 74946395 1250 74945145 74945159
    0xc020d1b0b090a03020f270f2503050402040914030a0305060303030615340b090f03091909050106030e0d1404030f02040207060e010b0f180f0702030f04120c080c0901 73
    0x1500c590302c09481e47e01e118081e08a0300c0d08484840780212440382c814407d06c040d68000207407542e40110291300030349601d040c0142460503180342031110000c1544071000b0800f55038480d800b44203002e6014242024000c4a54006030312030300a42d0074100464540700c009909410003004580c8900c10083c500808000d864000f28280c3d000710307901c90045c40410204810400c48000208403081442c4428552005c42e40742442c299000104421203a4011007001140341c40000192909041c080754012003446d000c400d010050703a10740d40325525060800e0b00000310303241c169010b94224600307a02070340c00d01005040d01350760420703030f02000700d10000c810401040803400d484c0d00c800d2164402031025240c10b901e034841b03006032a80440180e050b81d6449007891910300d4003c2c4111136000c0c042d100c02c0c1c8406000b0035507260340080100a075a900c40040001400280b00b401143c20681c0107400c1141c0300d580750b1044484469580c04204c0751103404201c017140c0c602c0002580d229002004240141e6a030078880d07 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 74947645 1250 74946395 74946409
    0x1c03061404050c040905040c0e06010507151d10050a050105010801030b0f07033305010903170c12041401020606040e100b04020f070f0c05061908070c020d1b0b090a0302 74
    0x843c03a000b8074103000110b0054420f0040e02d0181c2e024240441d282420299050480c100290a240c14400304015000014403030515494030700b4120140095803286890411609000d4a4081c0c03809010300d00b0100d4402036164081030254102030020041680c81d24010740c0c03054000e0201400d2014540c000500000c4008209a4130034024940440e0068110500c9050705d14800001b0144410003460f03219101c450034080c0004010919100e010703145191620b04c0300c9009207102c100710220014005480e04002c12004640030502441c1980c3c41e69a600c0540580b0034100119005003e458080b4117545841c4c0143e00491240901801240c101031200e600140381264611750415000c1c400002da8a500070090207410380141c0980e03000813483d00e054200c8038602d802003849104140040303c80305e800e0000d40c0840d9055401c01003600e88a0120907160342e036919070001e601010f0045035a08024005a0810540c3d031545510007400752a484007198500618560b48e800041600c0700b0005454110307 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 74948895 1250 74947645 74947651
    0x14121c0311040305030c1005010b0f03040203011107050a0b01090504031d01020c0604060e1c081218070303050a030b01090509060d15021b12120a0e100e1c0306140405 73
    0xc140000e0200401490100541050344180c0e000c1e000415030a0356207400b80f000d41c800303044c0780604004940c10b014007042d650099040700b0001c581d000c4001421910254800d00041008407116601d50300140303845503035071155020444003c80540000030303201d4098060b65014961540f101d82d0080404401d07030a580da440708030181103100d0103400d10121b485141c020405401c0b01e13138845010425107420702c04212102d0400556245412038402c01143d02141540e221040542d10706551307071112140c80500165004501c4134500a0803000010140c21000500114030b85480070300c81402940015240d42000740319042c0c11116401c0040c0c0c03c4d1900078200d02d250791283c0401c03030a40c110040b5070802c80e0030440b8003010500c046500d000400e0400c1103040b1600116600f10351400940c2e072880104520043c0584240c1c640312054404000d006101c03082e584491a417003040701c0302c480140d0070b545803c00880041c005104c400000851840b030b00034102607401c10081c441c1e440105200740301c0102801 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 74950145 1250 74948895 74948897
    0xc1b02060d050408030603010b01080408120c040f0603020301051e03060105040e030f0301080c030705031c03180203030a0305060906030706081f080a080903010c0905090415020409060e0114121c 85
    0xc210380010311007a80304442c0141e014003039150700c900d8480141402c43e500401d48074180072481040000065000080b60b00069210100703003171a0b00c602c0035800785da000d240c03c5074045030800389003c00e951b0f0b410b9000d5812078004407040804401e441015100740200a002c468058000303034014005414107402c00180c1c0c4088400303c03454880f00241580c41d070f4000b83c00440c0c080e02b0031002c84145140c2007000348054a0200e0240001c409010302c15241c0c64111540001495142c1004906003504100d400c4c00554000e42502c1c0da0742030102c40100141011592a0b108407850400f090f103074180080c030303001615102e803100303850f98880e0117101c80c0024015a11100040385c0032004203902c41e0a03c0741c00c0c105481102103d840300c0d4440101400d40303d03503040078420000740401c200b01545d5600006c40e08150406c2c1c03d02d11889820301c1040282c4a560406560181404e03070004080d00011a054100c9a5101c264000512010100182840c00f41002c1e4021351247c2203006441262044600b06400b507 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 74951395 1250 74950145 74950147
    0x3020901021e0c0a0f1d06010206070c0804051302030604060b0406020a0f0206071718030105071b05011d0c040b06030408030c13030501051503010c03050105060412030207050d051f0c1b0206 83
    0x80f0b002421050490300304015804192a040100b001d1903101c0400001043c86240b00501e08580000d6030740c04000d080c0c03010041211150028000b00760f04440184c0000782c00514a814420104400395000780c0d02d49019926103000010140034240c00c5d1410b44603a5030103020984901c1c2c0b03400d01c3c0501f030340742c081c4d074405020403115000030310b407408801c031100c5000101525201c5110101d00110444201240241d041c1010030243c2940f1481c11266003030b070360314440f12130f40d01418094018017415500c46450700248401c03004016002800803401142282c06200480280c400c4c001d40b40070644000b003800206002003034540503081d0244c22480e48500300c107495645e403902c9160075070f00c0a030f51645a042c020703149543c8605007802568440c03810380c24140880c0d403401c00414240e12543c0701c0c00c06040d08001418040620030b020074001480b009044135007103046410801d45841c58006d84c001070404000154000136018040e11305060b8940d1505558070046c0d020641c00c0f4107104c070040b644844 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 74952645 1250 74951395 74951413
    0x804060e0303040f0e1f08030712020313060305151207170307061103010f1d010b03060409060e0f0f070f03020d020a12110a120506060d0219080609010c03020901021e 73
    0x2500f5500013001c11001d040c00b86c1c104545e000864000305c000c2e0480d01c80b01144240030280000084641d000c0c0d02c015461400c1d060f40d80101e0440c020140854038001c1c1a400001d0800d516400160040c100e0360003940c2802c02040400400c0b40e80d07141081e2840d0800300d003c024000d401c00c00101e0a410140c00d80386020080c0d6103840c00c031501c0140000d00d45c1c0002c4018040884805180c201402c1d1904080981c404682e0074405416014031614109030320000c009990750325242c101c854803552029042c40344454070982d268503403507680f24900d12407045041c0f2140c1c510000604504a8000c4031902d10391341e045400f440030f01203d00c202643c002d402c400b070001d0160021422603401a00580312445012000d004010700c1c001c044d4031141000d000e181412000c11004155660401030840d121800b002103032010520140c500400c2c01d800440720b880c00980707e440801c0300c51140c040780008104442d03100718241c080b8020b00c600c150061307001c1211070b00c11000084000e40704402c0c0c00200c41c1805 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 74953895 1250 74952645 74952659
    0xa031e020a031202060115020c1306150c02090c0301030c1401022803200c01030f0905030a020d23030c1b0102040603060602010501050a03080702100e040f0204030209090a0804060e030304 82
    0x41c0040e882141c190001100035150f90b035052102c2809844003040701050100e00c400c0095881c3c0c034a05e82148101907a81c4507150700801d80e0710510080c070702c0c0074118a118440c0f020141c04d090010300140c2c042e009410003c1c0300602000222410789501142c145040c03400c007031004440380f01d02c10384241944550b1900c1a050b5500055030603034180d0074000c00342c0104c2c0e18907004000b04141d1784420780481484178030151440d000702d15041510000c1c40d0000710419101c1d680405403000ea42c0241141c0800144041c00725800305030308030401d03610740314030700e02d844011040c05107200769540c45807002400384081202c401404004101d524098211060700c611071b0f411003401c80c1d00036031019000c2503a80800300981602801280d00405080b1261400140380d0703250305085100b201070080c800c42c450f10b0070031082ca01a04954031307001c4c1d02510070004000f90582c41e4000703500a0009030701c5490200001501d005000881d14520795210907028102031612009440009a41030440e0345800148000304043d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 74955145 1250 74953895 74953909
    0x307030b181006030302210a0f090504020c0a02150408210904060e0105010306080105090601090b06040e0a0906060e070e01080a06080f070e060607110f0109090504230c0a031e02 78
    0x34101926000074801d1039464080d03d41005404803041560301490703087c141d11150800d071080d221203400e002070000c1c0340c100110380920054000613845480812076100868000642100d5240309450401c071440421012503038501071482005d0103130780030150700640d00340c4461086400321500d108685c1881c00a00c00601a211541c010149a0150030010031596030301d4000c61000f008450000c0150341000e000060b281c107014003c580f6000c3c0c0b1111445d981f42c0b0f0307036012100100442c189855107401e00103c0700740940320454058808606151010984009001c502c60140289440f010720845001005503210b45004011403d215034603480001c1ca80000d0110841e8500709102400100f42000048903240c4000350090f030040200340b0540000601b20400300d1043c8000711500640c01c40d2500049849070a01c0d00207240341406c001c280404c0140174071403007114443d01040c04610074100d4640d1a030325201c0d000840d90007102070b013081011500c400d0b505412240c0d40714441c5d50f84a2960042011 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 74956395 1250 74955145 74955163
    0x910120509010b01080709060c020d0f080a0c03020d110a170d090609021906080711071203050d0b0103020a0e1512040b0906010b070f1e060c030e1b0307030b18 70
    0x1c5a51524400c850a40e488400540c0c0310003035041000b1418103000d0b008016103a9240c009000700c0020714002d05102c143c248480d10035600c051216540d00a44a00502051130390a0450140c410300c440260726501400c1d03e9030349100044020840b103c100c0d200c601071404000354480c2411000c202d0b50f42e240e604d49c0100215140125800728181c1c8440c414004215a10940c019030040d0b20360302408400d078464802900180c2a1070940003040c1c049030024200121a444100120419180a000c240d0003d0103000e80c410386544c1000340c203142400643c2644118681c4000040e0310200c407400030310303006403039042104002035107030305043c2103251503940c2c100c1c03d480580304188140c01b00686584100801c5014040007407010381000b200b035030366080d20407031480024040c15891540b10412400317076200d032034015001038051081003900500500280f00080040f021805003214010311004580381c603841c0d400d00903008041a0345152035007881d0f0300c40030b020740518650303000d204a4403034000c02600c09 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 74957645 1250 74956395 74956411
    0x60c01020403020f06030708131a15010f03050601020c0d0302010b0a09140703020405060d020702010e220b09010302100e0315040602090909062403030403061104141509101205 77
    0xc0e80714214010484509484200d5500c103403000c0080043e42a40b0000e22500028130340c540d6113560b1003030701d00f824000e0001140144851f00c200c081240c244140c2d0050118203a0a0301e5100100001d480e04800780c5804841c0d5070f000d60306c000d01c510460700b098003030214254000c0c03000045003035032400064090035450748130700700326519041c1403410382a2346210560010b0b8107080852805141c4400300300303030f401610100034038154003050700025640031320b103107c130004c40c02003002c4403841d0140ca8100508103000c04207400c00740f800101411a0602075281816030350002c0c00c941e10b440d01d20504450100ca083e080e035030540034072240d030329000e1000c810442c02503102d140003607164040001407226000c002000c408150384950140064603102c540309490400e45014a50405580e14011070f2862240d9440184005e24100e006011880320310050010b40d4440c81350074032128598420451107100b4883c4203602020b04003c511114941050a401402c1e168282100264564407800d000c460701283d503a2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 74958895 1250 74957645 74957647
    0x61510170708060109081507092106091703090a05010e010e060109050c041a040513020901051206120a080904062403020c07050a06030911060415030f02190917030f030c090a0302060c0102 82
    0x881241c209d182c0b0805410380318018070320241b8040d0f4241400c01c108a000d8a0b243e552103a1a060240a500703160004480789415a0313241003680c1c905648a444440c152071070352030509065a42d803410301602d110010b90b80001e000036424903201000802021b0200d42e4512001c02c070001c1c49883c02c008042c02d00703181e1502542c64501e400240326561400c010440c04051041000841c01e030303040000c0c1c8440c0000c28001e00100e965410108484502002820241e4803e1070000820445140010803562100769410720106a4907012846d940e04450402c0c110000c0c400488085a44a5806000000386040844000e41d80d81d10105104032000c1c0c20250001e40c40c1c21341001480200344080c1031950007034891600e1320b07191500c3c1c002c1011400910208054070b900c145502c800b101d405446c1580c10702d00341c0551504030100701030000107040c03040740c0c10309555550040070fa0300040141c038600c0000d601c1d90751440e0713980002c621041c2d0103641c54031350280403000c0c048050303160305000c1c112203170300c8030001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 74960145 1250 74958895 74958901
    0x6150c0304120f05010516140c0c04060b09151608070611030c070308070c12030b010c1e030f1b0b191401081b13050709080615101707080601090815 65
    0xe42d09440340240180407180550074000d0380f440c0c8c0012074034011030448400366141c01c3c1240c00681440d9240a0182d446810200d000c10304003c450014908140c08641e01e0507402c150f0b030800d0ba0107000e01800e035107000781c6c0ca40e08540454420001031009a10030300c40054001c0b800b0f041d903c02c1e5001039540c02112103001c00d183c01055003101741c194004105003882e1003501301d25558040c00c0701c80c603501c0004158550390180c0c0c19900441420728015402194500c00c01c680001d8080241014002031300080c6111103a0030115000f011034590406506e00300803c0c07241c0c2500e80e00d52800380581642054035200c4081c07000c1020500c07905c4d0500381c0104c001282e81d45403030411803802202425000f5400008440b00c0016903e070340e014940c01c0220346000c2816512654150350317610175540701d5034403405840208000a036144c0f1480d4400c0104891111103003044481c2103400941442101a000c03c0b04000308642c20b004001030b0303a20880c149050010983c4170900c0b0380c240b0a0802d5921010b407910130074 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 74961395 1250 74960145 74960153
    0x905060d1505242211030a0207020406061404030605071e02010f0c210e07050a06030507080703050112030806060c030a18050d0314030c270f03030306150c0304120f 72
    0x5060100c3e40c018a0b40d584018101c0084e914052505100083c2404402400c121343e00036044003c0e0f99030300149080e140c0c034200d100030020751302011080b84203d16001c3c02180c40c80c01385d000301059000284d045805c20342161b40d5200105400780c8100e00703003c0300c81c1c0c642e50b070440c0540150700420303401d07070000c80c03009454440501900d01d44240481401490407184e40359440202036460203000b0728201080f5951454841d50601d049900001d80012880d4400308441c0e0305604194020202581c3d0b5050f1341c1e95419044044440c28010302d41d18204502900d400300e1f10035080c864106600601c440c1c43d046010751200c0c0303107520541d80c030000303d182d90340c00807000101080408010901503a440c0c3c0c0d11012680d0049c00d1800d400300300d800f2400044007281c850070703203542a2450300e02950f00400200e01060720a148402d5014480d070301c00e18001c1e0140000d41000b106032030180601030300f684005a0741d5040510541c2001c11001d220340b0062000058000e4403611600601c0d000b0040d00c000c0303903083d041c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 74962645 1250 74961395 74961421
    0x20c011406010e010c02180702060910050402060405060a03141302040b040b06120c0705011118010207060e010c1401061202100203070f1103160f0918020a0905060d1505 74
    0x4501122090304410464641d800119000e8031803402d29221110321514400203240e610a10344449403c4541c1d800c02c407606800050f0540108405011144040303110142e09055071422a40203412060501c400c1001d418030704013074545d1110b0b604012800400405400d6007110742110071019140701546480c095052a100d401c0d604c5105590600c00454408003058540c8212401107040c440708000080c290441c031015500b91b1540040284568441c558107403450740c00048525122030113000120401e0343c0000380c000200c4009480d400340641c00e00c00103456a48520009840e480030040b0202c6030300c2d03028468980507140c80d81e1141c00c203c0300f6005000c1d0001007004c00c0029588100016004590028a410443c55200c1c007a40e2110a020001c2400c0503028240b0b44030100c1402c5011840040c1d101918064a04850302080102e0301c00789101d95180c40307058040c2d080b00c1d000506004c40d00154001e503a000e40046d020f07542c149803640d94180c00521200d51108541d03510402e01042004003d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 74963895 1250 74962645 74962661
    0xd0f05040309051314011710020d09061b08010312020f120406030c050418090204021c14060105071703180307060b010801050a031e020102070503010603110a1707120c05040f020c01 79
    0x80c84c00c0102c0c59041240403100c85d818000e1f0440c11101d105042c00c220340410034400c0043d02c49009545598580c03100c0806061000008c503922030401304000200001031541c503d0a0341a90f56003003580e440d5859540440d0b0026040e80e086004040042d11003440c01c001007525548100300d020743c0d031460701c08000e01300d60341c0c1b9103c42d0400c40100010806d01c4c51196454041000d807140000d114946032000400a00c01c1c800c00c0420900450131140160f80f0320360111210f1301509064080c9641c070030300112114815207a000701600004040000e00c034071920b018581c80b10300d4801008802040a0b03d0b03501d9908100d20442d80240c13501c0201c405561303c4003045004100c25a40c034040b05081d542c54240518480007685c02e02e81841c107852003507a208000b602d006041c098001c01c4800d1302c0e4185901074100c1496002c2c0600b9400c1400686e0f42d01000e1070784007404061b4041c05159081510314554070740c2d2440c0c103480103d4490400700b80d554072449450400d61964400690b10070701140c100f400d4072080 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 74965145 1250 74963895 74963929
    0x3110303070f12030207060e0a0b0714120c09040203040c080106081504080304031808010f270209190c0309060c03060501090506130801090803090f06040f06020d0f0504030905 77
    0x40c4090700005540b10500010710341c0c48030307400b4080003044100300c00034059050041c00a40c03c00c03842011162004c500d841000703004e020010385a6585a50a03103070700c0c0c05a8200e803815402080907040340c0940b50700240c0c201e0030309607425141410350310014060383c10584007500c01070540300c01008503100c24420341004240c14005810300000112000300c002000034009480d0800010024041520691100c00228040d12012060369195501e060091501c00d40b000d10091902c00b041000201c0f061028482409a10103100318040c56070074809102c202524a10007082c0307a02503403105584074002e4140c0b0580a584c009410926401d2000548040c18080b9051518001c01801300c0c1c1da002405200f0356005403034040c7d5604400043c140c0e4000241d0209109500e451000010001c1500003180036004000464100030b09084803035460740070035140201b18441c00f101980c0003078880c0d0082c08068400040000e507640740343e130000c420303190708480c100c0001344034200a001031f240c03c00403800c0311a84 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 74966395 1250 74965145 74965147
    0x1080a0f020903150f01123201060915090209030606010c0f050a0501051603090b060603060f0402030103081e0a08060405190903020a03020111040602030913020c03040e0f06040c02060a0905010b0604080703110303 93
    0x4907221244203404101d2a8203143d6405500041c01c000d44074074040901230510001c10240e50354100090003022544220014503c92204c0000c00c407200d402aa88070000040260045885078001035031940c405036000c440462020241002083d000d02004032818021070000c90a0f10303116a10328103241400c0e0542050500d04a080c5c03006c61b142082580d4000c0050303030801e66907195880050180c9a88551003075000d800000007104004018000d0071745076519010f11031400000821169003406041c842e80000350402e00000e2081c0b4140e04895040740c00800d00141010003a58810191101c0340400c0e40540d21a01c045003c2550901c0340a01c104004001c060405003801d42c003e480744078690b0428810b1005034000e105030f0206604a44107004002e00316640d440d035a808407159541e0494100801c1c1e02c0e10000240107007003d008217170410001c2d070702070146942d603a090302c0010010103000303690703640d1b03210b04031551501c07484000c00103002c505008015162a6117060207c403c640c25800b402600 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 74967645 1250 74966395 74966429
    0x8070c061e0c02060f18090a090816020402130b1b030307020a02121c081e04080409150506040803090901090b01090b1e0f12090c01080a0f020903150f01 67
    0x40e10075107018540c551480c009402e00712900000b0407034001d00c025966100c00024240200c4003001120344d840c8942520340d0340241e95402c580070222100d2075006401d24404001854040d0081c00810418500c002c2005050402e00060085034641d150070018044c0d100003242e24040300810b0400b181480444001c1d4030310310f00003200075121150b40500a004410071080440c1141c014000c0c21402801c4003103030351b0400302c2a50020204102a039a0506100214182c41341c4070315910380311403090740c21072890342c94a481c2072010802000d485844040c5c2d001c010001240c1561480c1c020401401003400941d00c4034110010443c0c18807040e07020030786140c6020000d06d52640c004014408450428084a45800c45001220b0344c0045003c0e00340110000020342034491907880c805451400d100881c0c82196585142075165121855540c41c2e01003521840000c034480040d41003421410b100a0002d07080400003000b0034038007213074030702d002284942c000100490f537005a41700900524200d618022021 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 74968895 1250 74967645 74967677
    0x90501051815010f02011e1d0303090705010c0f050a031d0303030402030d111006060c061a03120a0e0604030f05120a050702090a06120b0415060602120903070506030408070c06 77
    0x412040d8803414000c0314813a0380703a030314001e40c4200414446102d88800010b00075014000030100300c031f012840400f814a002640b07510003c16207101c0c1104400800ea40c0f0b050030010744081c01009403c03100500d04403017200000354207128041d8170b01e12030703201c04404108200c184203040a880e02240d000340e00034020040541c0d000150402071080e02c0c10a00030700c0c860036030800d00b481070042402c98140e0406200090541d0b009150f401018040d8004102c22107084100c9134107040306002069140d4080001012200c2901d001407880c4d01107030800c152801074101c0482c000e41c1043d803007500d80703042c21503400c418054144400f50288402c0c0e8401413401040788400b4209009004008e800384150744009202c1c490541c1c45103010342030b6843c49500842013850304000601e4110b600312000501012145456940b501905040d1000da401500909202840b40412600310b0180160301d4858007000040c0394070340c40002e5000c0c038040d009072071340d40c07207141803403040c01229521036400c101ca0010100c03021 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 74970145 1250 74968895 74968921
    0x302060105150403121106060a120201080702030c0106060503060312030405191a010305010b030106170304030b04150e03040303090510091230030501080307080307050a110102040905010518 83
    0x1441e02118848404140c0c18142c0a4600541d0030082c02803500500c21402250000b6010000507408400c6500940d40d00b001c1c0f00c00700b4050b1160340e40c02c10b200002d600c0150b00a01e0b50560004492040300c0c1020408654039085d40c40950011021500c004103010b540d003002d02c0b52924084c100d02c6160700d103061540c0e995613502907003004d11494000503900b200403c88000030504031020030b80c9406100d96140d080590081c02401e96442c440c1d03181840004860700903035144042500040040c42c2401d14603103550b41c003000c00810459460554080b220011040b62280070b5008404031700858885040d03180c0a0500c02640e0040e62282006000910360180c1c002500820b51385100c019444040303141c80c00c4403009107406810440b440c072451440e02c501c1091400f018054210382d43c14411640d03503001c0c40b0745a114480024104010400c00220300034001c600a040401162514010b018110030b4024226000f5410103a50207854400410003440d086000e6038102070080e94240341401c10900082103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 74971395 1250 74970145 74970149
    0xc0f0f03040302030c120301050103051e070e03030d110a090902190c0201051614101107080a020f0a030503040b0603010203060d030813140601050a0b0a05030a1d16080601080a03020601 81
    0x22500000002410940b01303200740c3e940c080c602412280c0300203a03111401c100350001d00610b4002071820b03001504008010510b0345103040c5015000c541c50b2180c10040361030408d5110b03125014841082021089042e074410ba041064003451900e88400c540310000f000c0e00c41070307445422014014010000a6109180d00c111141d0183c00c066100e01a6031006a0b814040c14590541400b62080c8510a11038041000c2200d0b14401c41600c8108150816100484051000038036000105000400c00114442c1c001c1081c0021070045412401a031061a40f07880f40d040c1c001c070001000401480f04208244c00790980240301100203504600c3c0480c0400d4120700b0218015040003003c00114001c1045035904014080d0071007200030000039040c000c42e5a400b000e10400d801040d0540000401d9201e1400342d4040501541d5058a15120319400f07002a10348114400241551035102c010003030010080c0714089504d080503402d04500c0d1419040c2410300590104026401103256140083d0f804141241 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 74972645 1250 74971395 74971417
    0x206010e150a08160f05150d020f04031203140f06010503060d030e04090302010e0f06040f060b061b0a030f0905010212030a0605120703060501060e09040303020d0e01051006080c0f 79
    0x10010180100042c00c41c44103a0007000140600c0294072180b01c07503036041d10251440c1c01080541d00b0740d180184507900507920800c8420f02018414105902c0e0707680c004084000d11051035034141622925003904c0e1400700c2c904880400d6461a1040d410708450544c507500110101c0050759071b03d098400608035101c02406103200c3c640c10440301c400c00d4019001c0520380310020340204201d08451802900912040844c02600c0c1b01d800e04d40004032a00140080c880d0b40d0107000b80f1902e220ba5074030341000e400d0392071013541d208600703012030042020000200c4098505180080c210b500190501612179014820325504022412074144150303600010307010030403d0080080c0b0398a9032600c008500800c101d0300500d500070201c2407040c120110000d220303002c3d240524410416030b6a10760050305c0000e184810300e900b0200441c001404207000c1d03806040511025140030440c071402c1145542110011600c44400f9034602c1828044103502460310740d070241d0310020007032400760f03401000d030300030301580b0744080d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 74973895 1250 74972645 74972671
    0x8030910030b010309290a0501050303160807080307030615030504050c240f040611010e0a0b07030914030315120a0605060d050601081b0d11060310120c05100206010e 73
    0xe80d0340c1c0d100e61701c804280c5030010421001c1c03200400d4800744807106100c8400e501d200030800301d2512200391140d50b0480c0c900400440c0307804500e80c0301601a450000301034a00c2901408910007241080e00110720841c2c2d81da60009040d424000310741025412001c21400b058139100030800040c0340041c0158540301d0803514400044031400641848142070070004a030542c001c119602c40d00b101c074000d04180c40d0303d62912194030364400c2945080f00d000003d0170a03103522802a00011800046c206900320980740790109950006440b40c2d6000c1048583c94009540000300b0403142956100100f10600021552101180740c40c004660380c4080c040c202809035030f91a0301044d250342c3c40aa60f880090f070f00401b52a050340c0d503840c406495011000c0e4404041910702664141c6103401019544510b500102c3c408442c0117030001e004540d08000d2002c040c0d06403030f900100d045001030307001103c61486080311803811403c00f0b080c024508080c00c404c80540d031145005005034803465420b46e84c0200d002c5940 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 74975145 1250 74973895 74973911
    0x6040f171c111e1620010318030f03050c0405040207030c1b060c06020a051c0b042304030e1c0b010f0902030f0103060e0a0f0506070f09080c01080405010204170607090803091003 78
    0x3c21082c00400100021300242908002107000010306811794826201040901e6032081500301c0180301c408020005051012262503c0b8000c0d44015000144058058105620346001c90300301c0e801400150041400b4008040c108203400d405450254200030254480c149490070140c485150218020001d0303402040a188281c0b10380305440764401c00a009007140f0444104600092010722403040c02142005084000c424401100c00000c103c0d1030003060300341d584c81d1421a1740041d036102141c1e008008107508444451b01d06040c0005600a040c40c0c0555450700030704401d218010b6000c1c09909005100b0080e02400d030325011030440c0c1e04080045401c1d03001803650b906007100f8130310081c11903001d00300620038494000348840c8120f60549031070713883c00600c00081d1548000351280d420540d00800e080d001301c0d4401c0c0d01081e08281b10b08009424551110034650701c8503410000c0103016482541040b001c039078001040c0004041d11400f0f107141c20404070210340070700c05180c03a4130281a121100d17 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 74976395 1250 74975145 74975167
    0xc0f05060a110c0603070c1101050301030308070e030c091f1707060f03060f0e0103030e09090325080304030e01022b050313050729090306040f171c111e 67
    0x90340380c1c83d04010f120b5562440c0201016001001030b4130155039013001104030f284154040c0086905032501611490482d5440c0d210440303410100c55512901030041e00b000180c603444104019001c0c442c01380501035841e10f10005105ea404041c1d00110301665004141280e6a00c0820f1940564410303140840c85034250240c00d60241031258450402d006038010000340e42e002041f01c0358140e9119a441030711201004080004c07014081e078140c05240c10410a07180b03520741104e003e0f04980783c0360f2400d003400d030015200e44045410481d000da002c01d041044c640302540c0e0504c000707103680c0c90581d5070002d901082c0071214010b07200c208004043c043c00001103210f0420089250320001e5019003100c00850f00d94a40410000d80000442e005541210b02c0d0400d840050098034114940600102101c0c0e40301d4a4000440001d0501940d00c080c101c040c030481d007481d0754000e2140071920888070102207040c00c40202159900c1d441ca103080441880310540000000c0c4021450500c080c40d055190b1a410714 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 74977645 1250 74976395 74976403
    0xf030314040b0a0504030204060602031c181b060e0a0b0a03052502010618060e0c030403200d0f080705031f050a030b0f060904051903030603060c05070c0f05060a11 72
    0x1411810b940412034043c0503900000420a8a01c06d41301442000c4e0fa07490160b07900c2c01451510035441080262075410030040d903000c4032140110ba0480100d001407501c6018284c0700d00d42454010780e9000c08140410b0340c010414508010066605001140c94041d8446081c01a20720709000c040e00e420104000c0301c952818480500780d100107100758440862400b038000e04251040c0d400310310b800c81c1d201c0818034040c840d14044800c00044c860389680d800411009030707440100110140300508a4a500c0076103814016032012007508000c2034484040768018200001841c012030802c0520010414003950000030350360019100500c00090918480d800807443c0c9040d086950070000300034002082c403009903400c030300481802da250080c90319030f501444500310080324090481d5000303102d035100f916200000c08118500078600001d00649a507500000d0303c1141d2007400000784041a03807030500110021080051140003403c584484c41d1202182990140003d20014040d8480b0305d40000d0350244 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 74978895 1250 74977645 74977649
    0x601020c06251e060605030f0a02040906141f12030906030504030e040c02010b0a1509051003020c0106090504020909010b0907050a050d0e060709120305040306020f280e0306010f03031404 82
    0x90764000051481034000c0c60303002c0f401409441441c180b01000681d0708012409004054107100030b08000c50440c1c0a020150911920403241140e4400c211410b09050100b040d02943c4c101901000c8038510540030001d4800540160b0b2503501c03200388903800a5000041c1204444c001d00f00464990f546042c1650042c100e011480e400ca41002d0034000c41301d5040d4040f080018080b0f5007200d0a6444004111031060b500d00040b000c0f5444040078041d600d4030048007012600585030152600500240c0075080d0b50750b43c0e204480864456043c44114038009481c10351000414008119406a000c00240e0303000002d44144140400000ea0a030740611403401c6401038103007000e003401400349020f130345d80d503c500444e1600d002940c080404034404103065401c0411580513038849080605540f0380344000e5001c00640305030054200b00030303500d1b42e80400c800c40d01400000500c182d005d041d40c401810700386030004a03d200c0d40040005104240035802c401041c1c3e40c0621f002c00503e1004110b145280c451341d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 74980145 1250 74978895 74978903
    0x105040507050d0e0102130602070302060f030c0c030c0a030e060903062205030726040e0a0c030204090c18080d09090b0102070305120c010c050309100e0c040903030f050601020c0625 80
    0x441d04d0016084070540040800203006a00e44444035507441c0200e89038481ca0000130341c0158200400000b000a040103180c000301e803000700910b032280f010300851440e44498030714109604034006410906400841d40d0305007881c01d841c030500d8240c1c0040004d80702d000c000c20b2468099200b50317240d140928000241c9a0300d581c00b0044a81d50426804c10b0940d6214803030700541e01101180c00c1c0251007080005860071210410108101c2d51941909140076012020314130b8101a0700b4030000030398000d10b00403a43d07171b5803103030311145617204010500c0b114421160300683c80c55400b828a40000950000c40007040b940749140000fa9400030f400100d0078080c04d580040c4c614829004a20305400c0d200307000303080134031a15000300700c1c84443e15001e4030640800c072071080054001d6440720f10494060341080c8040b106003416261203d0301c40c0d00145c11981c0d40641075001070343d5041c03210301c003840314880c00d90042024001440424a0880001c40328440c103004032000104103003007203400c400405110640d541e44 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 74981395 1250 74980145 74980151
    0x1c051303080301181533080610030b101209120503071707081503101509110f0f16020d0614070e0a05010f09080a050a02190501080105040507050d 64
    0x103242802a0705801c28080c1c3e12008414400c448105007882c456043c0e031450b10207985d0000c074a00141020141c2c0071004801c1e4007240340e0400d03607034440c0c210980240e5503415243c2e6800303402c00318113210b52491610401c0701490314280d945806940e4601295001e00d40c00d00d4443c2c404006031a19101410899600401c400c6d07507022030314001504840510b20559440e80e8405803400100448500c0c51019030740600820031050208110f044c07401c1c0c0e00140b00780081d08072010200040d0021301150f40040c00c010020500c110103000e4800180640c054082d10200524180455210302e0034191043d05083c00b076520340002c03000d201e9640361400e007a4054000748034000021380350600d003014240702d48100600090100001c0c106900501d15440d0070341e0041c0450000c40c0c01c140054035080c3c058448101441406400011200780411104d0380092280c0042c1421440714030500ca21498107030081c2d144202050428081e0b40d900441250440b0300466000c201515140f10035281351040100ea18250f070f003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 74982645 1250 74981395 74981399
    0x40b0402070303020a0f140301030b0a0b12010b010207080313090207021203030c04090f09050c010e01020c121606020304060c0201031808032e0e0f04060b030d0f0e040204081c0513 79
    0x2415a0141c01643c01c03a4984003011441c46c6001c5900c101100300c1165445030500050010802e01c1e1411035101410030380000d03455064100182c0c0c22071210f5175601c00c681d100c2c03c5071461541c0c10710549000380740102c01141444034003141c10300704504a000b40f110740c50380441e10034203642d1282c0404140541c040f09595680c2002c50300d01641e80d002d4011222210305104200c0f440201c14400c030041303250042d02412104190200440c1c000048c105814114840c03c29003810703640e500c40c1342403a000da42c1c80003022040300e0708090607010201507000c107040d5042401300b0002d058101030840c00c010303030900e0001141c9440049000000d2407101c4013a14180c4040108425050b103a203141c000c0080690b1a500c8509171038100c100c0400850003000541105403020440e00d440d2100a1f5030014803550001c50195248030100f0700d4030307a1000c203040c00943c0c1c1c10448040785401c94606100c4601c2500d05600e0141045000e940c1d07002540031401221101c0140036000a10840c01c0d125020540d03408502c3e115 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 74983895 1250 74982645 74982647
    0xb06150409050a060506090603060906010e03030c0304030203010b060903190602190e03070b040b090904050f120a120603030906183c0e0f090c100306060206060a080714040b04020703 80
    0x1200f210340c82006450007401243c1c1d0b16042003036a4070480b00810311840e41d540c00c0d09000c080c0c00c001d0704081c10b00441504068643e50188098908024250020364807140381d170040509403014105080c0c0220002c03c9450055100840c20000c241c44142c200344002c4540d140000003441682d61020606283e043d1404c1040e42c07011005460b46401c908584000c0e8441458241500c907038410043d1883e010401000389040890301c240d4090b0051094402c4d05c04400301650804509284400c485440060380d0b04045821114441d0040f021250802c080c0d4295500904a683c0500400d0180701c0300c9426862000c1e5000b00500103400400d01d03100500e2303008003c5000c8266080032010165004070b8200405d242041500030484a0a6200f03910720748555880700d5220002170078080c0640202d0031288a0f5440303601c2829050480c66800040780703490000001d08003a806444284130380110241040850700004000c0d081d00c65002d000300342c48041000050080c1503c0b465260040d0010422600781 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 74985145 1250 74983895 74983901
    0xc0c03060603020f0306270304051003090b09010902010203070206071112070602071e1509120309030b0f160f020a0b0429090712020409022124040b06150409 69
    0x8903c2a92807034400c0c1c60001c04c05846210444611000005c548980304015210303601682101d010a03041d41c0c5090344070000300715048030a01e0003002094846000408201700c0c0000640c1c0286141e000704240c0f209540003d4880c85440000f078842c000101e906010320104d10440c59a250005010341d1282c100d050f000c948844180c030968002d801980000292081c0701d800c120b02080030151803200032401d2008995004841080714001c0003100c2d903000c81e0350b4080c0c0007170451042c000d485010515103185004141510000c1603c0da40003420414001c610b1100d950143c007400c0c0c40e040c40b070001055140c04a181c650380e404040c00116982c41400305200c0f1440000e086000c24290080320380403019245818010250348008441c0d10489080004031160329102d460310384014008603162906400084090100e040c0e1030f140040402010680484100011007081070055403039984001220f01c503c840c00130082c0041c100010500c0010044c0d2307141032007141c004c0720b1140020344950b101c81c2c2070402 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 74986395 1250 74985145 74985149
    0x309010f200c04051e01030f0501060803030a09060b040605031902030102091c050f010b0603010308070305090d120207050a050a140a090507020a05010e03030f01090f09080a0e0411091f0c0c030606 86
    0x20761402d00498401c0403031500e500170000130000709110f0380e40703135555941c1c44101c0b1010a803015541c034280810813401c2413008600820b038503003010030020501d0410008071642550320910807460428100025103021a0800f40d295100350300100f1804540003213030183c4901d049240d4013490b01d240e8075043c04400700d00d08040782e024100b2255245e00340c0703000034200c0718400711403544110180700404c00112242d00070828280710380740c154207060740304000c0703a1080c0740c070703c000c403418204500c42d00b035219410000c110080c1000c9480b85c1c8140e103041c012804d010030314010304100c170107001c0200c4800d03140c15164800511010004000c03038a4104002519001484800c0350b255080c48880115481c0000c01c1c0c074040c455920101509074a081e103088018241c40100000c59515160a00007103440000500a070000984a04c82040d504000b0401260042140d00d100356005105c80ba03041e0300e61039610b1a41d0300041202c0c10100c10007a500340c80a4004800003000f0342542c1c0d00110420000f5040f03801 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 74987645 1250 74986395 74986399
    0x11404021b1f060905010302030705060a0908060708040201120b1302090604080a0303050115030903080609090a050a1203150305030703050309030d02070c140904020d02011d1305010806070c050309010f200c 90
    0x115250704c60b020801510800e1002a501d644080010712440c6400001815003848038101007965596170070515040c29021140003020500302d00400c8150750704070100400d940072101c0304002c06440c607400501d215506400885e14180d01060400040d107440c021100645040c50072540f20596a02d0300034083c0000340114050788840c0000d50000c24041c1c0100c140540e41910340074419500d04007888211080100201164459121190003180c414441020018025981480303400e030700810240c2664809800d1551401020604001182021003500c00d0700e6410f1800503542d171164102c052950242c0e04807074008610002da20001c011079502d04c001141c083c48140307144550380208200d0380c01c1007100e01a41001c005041d1340010b6210302004000120500c80780d1340c1d503204410114244031803007d039911034581d603a0010f201d10b08040002681c002d150f841d180c0c40100c0d03280e4403241c880c0501d01040e41807003010418503041b02c0c022042c1060660044103140151201c02060560718035091040b64 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 74988895 1250 74987645 74987651
    0x2703030105030c03060415050a0207120f08060d0309030b150306010602010b031501050105090f03100c0306090509120a05090a090e0303100f080a020d150504031d0108011404021b1f 79
    0xa00c1c40c180443c41ca4841c9820600c0c1c40280c07031000c280c7e00c000c2c25005102c45030701c507420061580000e054810303040410030305030390b040d130750008860024100b410003801042c0701e045000481800254041804d10503254031401031452070300e8010045d40304800e400c10359541801500c0c00403c140e82d056105040c07c520440c22904203a44103c01d02d400b0440038011240021810004044c903420401404510340c0b1000e0120380f088015558a2822917002c0031103000042d4407100204074a05203801070540202c83e203001b03080c07055481311034040d040c03041c0460b10342031201c082089034036030303640c0c206200040894002c1800030013001590240c03294030860b00400080a104404143e44600c03284c2c4009951401c1e00400d9111103e03001c0000740c80010b10200e81c801c3c502112601001c1d00d80c00f410f4011880b0341c689480c00012085c02d48500da1074129414100041d00700100003a4003410b81ca1054210140e50041c0d4590fa041c07a07906884d0407002420700140300d000d5608405d000e19132a007000c000c07001d078010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 74990145 1250 74988895 74988913
    0x80f0a0506150a060c02180703090512030609071d03070306020a1d030d0507060902060c160603020306030d0c0510060609060f0903080f1308060108010c0f05071208270303010503 78
    0x1031600c08002e4400a900514204418442e141c0240744800e841030005008501d10344115580e1800c20b42c007103c00000094450004100b00301c420031200240c03210b811250b500b580350900c045a00324000030281e20070042e4580c040903044013440b104d2483c0c030601070f0a0300c20030b60b102d0030008081d42c0289104400101441420800545a45030200314000001c0103000d201e064500100e950b41c00c0800d0590f0f5003559214000f0059454800400080e80c1c810041c09640380d20420301d2200905550004085c0742c010010020746a0f00410b2944079040c6504113030f4240c1c04241001e41c6040c4c014030003001c0043c602680801c040e504408104201e5030300e5170395070b00c1940e1021000c0710b8200b07481c40300421658040c40110200c1c070001c8003400030a4003e40c40030410a5850703051500d00b03003080e0302200704c0d0f075075030020580b600b0360183d41000d0301c40e281e041051a1071110703a250070004004980500c10820b0100c081090328801c0000f5405544008101c83d09a40d9008005a1282e0081c45041c3c4a07118043d18 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 74991395 1250 74990145 74990161
    0x50c03040b13262205011707090b0d06030b040614060a030f170705030d0506010905041a010c03021e1b040504031e05040504050103080a03060b040f05010c050304080f0a0506 76
    0x40501050f030000480b000c2c40c20902414102c2c140905041050301c03030070303c46a0000c0c8202c03841c0011402c00c118505002c903240c0400905408040c681c410307c02106a402c1000083c0c11003100000c5a5111500c15511480c1e240544014041c80e04000c088100500612040c0129500308101d0401c000a05445036256002080f0800d452840001c0160b12004564408500c0c084218035201811084861600b451171340c1c5d590840c7c1c45000000c1032955504140a010b50307000000c200901000d8030104501c0303180c4959490002940704507241000301e1440002d0401d40700307000310300050b40800e40010000380f0144246490309088101c8034541d0f1948900000145058001d560056800d81c680284040e820f01c00c0d40088904164041c0a00c0710070000003443d501e0b44e02c10603000354020745245413688101ea20090680b912170b03100940c820400e01051140a5540c039011048a1090070120320004003890300c00d0641c0519400501c4902590004140065010428480c03080c860001d403080b940daa206 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 74992645 1250 74991395 74991421
    0xd0308060a0e1308030a140106050301140a0b1c0b0418030e100504211506090c0c0b070c020a030b040602070302251809060c110d0311030c0319050c03040b 68
    0x100d1a5000c01c10306400000b1412440055421203046c001c0454051f14041a2030264002a4015400190000010045d0900707290110980d400d040300d0440045240001c1c0c800f441c05840603d060b001c811110010b0103240d0741d400480c0310180544240901c245504003003801c040010030560104401030744407806458030800d401d802070400d4032070b94141810030142030000080c40003140c80d0032680d0b0702d1060101b0403401d4241007012400c1408206141051803071415a43d01d07003601c00903c0300d520310038400a610000d405601c5005450800030001c0b0500000e440c08e02c00341d002400d40310a140c28041844059002000760398083e4080741d0117203000c00c80c0c200d40e01e965451a07002c0007905840c1442003000c00b00420302e64500131040403c1c0700300d4540b100c40881c1e854400c802c0c0400d000302860a4481c00038809042c4070301c00da0900700502e56070b829200101e07100080a03002d403000004000ba00070304a01c038a40c280c100351804104514540541101031562040d5016140d21700031701d0000300901c48440d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 74993895 1250 74992645 74992651
    0x9060302090d0f0507170102030103140d02101512050f010b0604030c0306110c030c011a0406080304090203270718021c0e071d06040501080601060203160302010b0d0308060a0e 77
    0x500b20b1520038050792125800300412920407205405003070000281e844650000c600d000b02070800050352035156180c030116000300341806a1550300301c0e000d0b40c850603401064400f8000a140004a01001a03403011000e400b901e40241005449130070900041c02000206c803030040701039000130403809545004016141c06036100c01020380c84031410030300000b20075400101c0d1520041c00103d042220422440381503420800f54401a44e44d940304130599810307035012a03194520159010031030740342854007040c1c40c0d11560240d12002030300000807400600311000118005104403411241180c40c403010240c83d20301034420215071600e101d2102c1c220307283c0c600c00c654044845200400b02055a40040c502070615419100414098200001102c004d505900d842030b0042107013404441c40c11740708110840da4103030000d01007980120014410240c00008442030040c0c0c40d802c80c454105203140803400740c90590103840e080b0711808288010540c00040c0740e80a29800c48440c0200d42e2210285040c004c021 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 74995145 1250 74993895 74993899
    0xc0304261015050402030a0e07090510030303151a030a0f020a050301140a0e090307060e0c010c15020f0a0818010c05040b1b190213060305060f07030e0f0309010906030209 75
    0x580a040c0085569001407902d600070b2070210810390399003000408980045485900ca90780b00d1294400001040c824080079084102c0200704c14208080440d0700d824007400002c007407643d640b07004880008406068401403280540380ca0020001811056140c0c000303070340070b804050601000c00c0701e0320784500a44240e2807141c0e50742d85c156880d000c0252004055003006a4011010450105040c184446501d11a90588004560351046440d0090131640d03092401f20a41c0c0000c0501c0005a038048100040c840d080702100d1054074151150400078030642005540482000400060160300005003521036000c0452490f10725001c000c105080c1d8800c103030b0000014004110601c40304801c3c070080c0030080c1d125040d0740c00c80340c20071440310f01d17004801004041210f850111002103142c070551880031400d980006002403455580c602d87d0303c0c00c002c0c009100303e10801000500840c800d41c01601131002102c21144419505141c5645a5021159080c0014029200442c0da103011740200c402c45100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 74996395 1250 74995145 74995153
    0x60f0d090c051e01022a03070602060915060307120302150703090b2401050c0102040f030602070c0503030406020a03260f070810080303190204030b0c2503120e01110c030426 76
    0x12550b403e01c2e03c050400c0040d0081a003070b002e4a10140c504100c4032001c9d110f540c008250f070781080c4401d41e241c80c60140c0d2480403080110100809624040340310070031580348600d0101044004c0c0b5044e4200300e5060408003210707002d00d08200b40140d044c1c02014500740600380b2401517440d80503161b107030704101d0080840d0750300c0d82083c1c030000c95100c0c40041550450f1000010704140c3c44440100d00a14107900585c0e2081d0003055110078001720308481c5000304811402140b80c2403410b0006500e6051020740035051244000854043d8115460402c030900701c102e034100680e2070100012290074005590410000e40a0000900681d1918141005176955071000b54210381d10000d2160700c81c100d1080040c0740d240c00b400004006500c034a440c9000e0040780340c03a261100d000318040c0d070803a24030180c1915502c0c0031080000c04242c1100b01116106440480401c038201d071241d60034098003104030090384900700014600c0b603116020001d4025a0850807001d0605450051030000201d2078180408031600 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 74997645 1250 74996395 74996413
    0x3020909040320010207052506120c050f04150809010605030717010608030a09140301060b0706050402031608010c090509060105030f0403270305010b030d0905060f0d090c051e0102 79
    0x3010341e150381c100f0801410f5840e00740a20b900f1180c01d98004031821502a40719000182c14070700c01c8000840811400310040e5902032070040d005003124409582e02040a6540e0b09074039030540309104441315603108114155690340d03540f0110030000141c2080100240ba800081161340c00103024113800c8600040040030720380d003004040984165100c098401540da548000540208180003600e124140d5440e1000c00c03526080310355002c3c054800250740310380d240210034010300741c581c01990700e2113400c060009429a10361000c0b9103450704041020311100170006000900c084150001307444880c241c0c0d6245902d9960b8014041c0964068a9076400304805000042034050011982507000b0301a01d41805404130030590f907540003400c01c085442c01144c84400740144402401201e2141c0419402403207503c8181324018070018003402007910a030341c00030b5150505c5074007006840c001c01e2941d2007000b40655903e0102c4d00c8002c81d10580b1300410060b100410f080181c2900c50022403010f80180c841c2d20 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 74998895 1250 74997645 74997647
    0xb0f09031009030e0306011e06050c0c090a02030118020c060a0c0c0b070509010906051801050901121a030601080325020a03050a060905010b031b04050901110f030402010e01030209090403 82
    0x24010145450301441803640548410955005400c2064060388138101442c01e0314040c1360403c44140c003c1c4501c108080214445104800d40101c2110601e04e003081d11926022003c40c01c00300300da40c0c4c1c550700641ca4410310102040590043d0704a030503605901c3c0138045160021000d84c019515016065003024000400c42c61080d00301c041100e002c4d00d071024912026a03034002c03d1440a445a0380021700100d01c4548550f00b248503480502110304100703003405e1188044000c2040d242640c5410404080b44401c00399000716070401c502c2c50700f04bd05020180c5101200020502e562043d079102c1c0c440c0000018503100301000300e81d991900901c600391074141d01c0030305000900b0443c6080b40c0041000c0c02c0000400c4c0b05010b03c072400c5214000228410165003001820b6920405495210f80c006076141c0e03150a1b42c0d0303500880140420fa070086503603641c9604040c01081c0000d1100480305000800e0303070358203c0000045200e00c1c400d0720750000c8000c000d0011001ca00411040b50307001010680480c1c00310b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 75000002 1107 74998895 74998897
    0x60c080705180d080c0f010207020f0108011d060d0609030201022206121508011104080105070216050913120201062103080103200604030b04110a0b0f 66
    0x10101c40c40d0482885815402c4000d2041c02c020b0403a80401894000340c1d001e0f40e204d00143e51500c0840c81c80b00703010b9800340300304a03c902010007000d81c1c81e42c01515640e0582d150300030a164031000740404001c000901408159100c1440000c2d100012010701950425900ca40e002503101c0060704000401c41c0440d0f404504080b82041c001e11501d9400201407201c0d4501400c04604981c40b000507010705072301900100155406c1510002c0c0d1507100000030012100b9581c003c00050b500d20100726203da07a200c1ca00110110301e44410465450030940483d044000c00614501c01c0790700f940d40da800005150002d00c05070f510343d1002c125800c0348081551200c1d49041045007080203558000344035920500004001c0116500b8021060b481c5460107100c0c1c11000e00300e40d9840e512070034098035801040300c1c102e130890142054000b55082054a01c002c9411a03a002401e0400000494480b = true := by decide +kernel

theorem cover : BRFrame.Cov 74820145 75000002 := by
  have h0 := BRFrame.cov_init 74820145
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74820145 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 74820145 ≤ n) (h2 : n < 75000002) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
