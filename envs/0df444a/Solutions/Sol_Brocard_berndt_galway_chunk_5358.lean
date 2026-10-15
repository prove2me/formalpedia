-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5358
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:36:21.088383+00:00
-- url     : https://prove2.me/submissions/6c8d2c19-26b4-4f08-a09b-a7b9dfa42d0a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 963489208 ≤ n < 963669064 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 963490458 1250 963489208 963489227
    0x30d0509070e041e0f030513050102031602040b1207080a060e060115082a0703090518060910080a230a0c05040b0111010c23030609150d0515070f 64
    0x702c01c080e0b03450710303264010503403c4880e080c2d000d4012801003401044003c04400c3e80c1034441e0b5540e5603207240b03480e40000c805d40e407500b0490441d001006811014201507803e0109a90111400101008030708001a0900096003101d1124060400b0016031020082411100d90340520018401d04280d40140380d200c220900510038850004a101a0300c00d108144540d0b000c40f08513441c8000c8240c150b000c6483c44807000074284840350018503101050380c01146100107140c02d607081d40001c2c20140100328599002006503004801c41c0001a4003004e6125981000b40150000c0d910b00300143d0401021000d010310003110014441c50900d0b0300180002062504a40c1084000101900f000c00b000060203d003105141000000f00310400c2c40b01007849400c00c140351a0312005100401c140da03c00040110005400030400d06000300002c6031148040c4580c003981c1703100422100c0c010900002c890721440354010b000c501c61484800c0813500e80305503060240e03500e030316245091842400c04848460300c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 963491708 1250 963490458 963490469
    0xd140403021e370c060f0503060a17120706090605092409010603021201140606120109020906211803071707080915040e061206160e0a08030d050907 65
    0x30042882d8085105036407402540c621000c5142c0008144401c1a0741c803d0300040e0a80e15042414410005540c116440c10307107004582c2000750070351500c100050381c0c95102d44200e10a5101800081c4410002031040c0d0120540101d5545e85407102c13814600000c2c88508001c0300c44520b0580401c0c0c0a01c00007644201d004048503006d05500030408641484140280118071f2941d01e070040400165229449510307018016000090203004132060740d0071000e40034110a01071001004865003140841c070809040d02d040340380142e990701110002c80ca0134404c400314584083c2c04030005000440f8400340d0280a04826003d041040c0402c41040303449220380d4034001d14242e00094100006c0d04420054024103010b03c2401c0e0900951901060800b01540b03190030b801000040c00f4040358000080f8907801c00030688032a44000380c490301140d0303a00c1c4090005000800c03102000d601491080f42c070a103c020b00540070401d101e41c2c4001260b40c07038000c0782109410034107142c0015006100021494112903 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 963492958 1250 963491708 963491713
    0x4030507090516030903090b0a030e06101a03040f080f09030c010509300d050307090f050f090a061e17010b0d080708070c1202040e1209150d140403021e 67
    0x500701c0c00c0079802845e4071a805c8003400322802001403a850b0395400341010700c0c116103010030140f0280c021a424040001c2c5642d0002042403024440e40704104101c07100c0840b5003900d259652514141000704d6100c1800041404134000303014105d418030070001c0e00b05000705030b08503020008140019940340c0101c800c0c4d00e4109140c03104516944002083d2001951701d000004c0d03035081442200c440c14105180480c0011402c00405e0050300c0c0d1744048030400401c01c82c2004600f990401000075030904c4000b000b50301c81ca001e9804291503005a50060006202c03280180c0003624106081201c103051512600e0341d040042616200748801c1809030000b01d1070000e046846203d850380d44c04010340c002d42c0090380c244609004000010f1174041445e00a04000843c040e24554648100800d84100c1103c0503a550008003818800b81000d0301030b00c449a808480c0007443c01400c100c22281d030b01072600418021810160441c4141c4002c41c20940128080c6e4241c41d5607001328501030f0f000c2420030030010040d6 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 963494208 1250 963492958 963492991
    0x606011d0409210302040512070623091002010605010e0901030c060c0503120f0103170703200a06060e011a0c15060402040905100f1e090c02010e0a08040305070905 72
    0x2880e0550040c2e003007500c039050f1142201081c80d82d440f80300680000c0c000100350f00040900c414503083c400c1d8444841c4c004010180036090980090000303252103801c40b180d00428440000c45450001650000c01029105c01450b4617034220007406440b0500ca582c0c00b003400401140c101e400d00c4c8072242e06a94220302e1480c4003e10302241100c0c0080d92240070b41301800700307102c805505084896118021240b03c190b031000c0d075045062100c00170b030107a07012294418003009058006500407000c4c0e28000c0e048415490340545004c101c508040b20b0280c02000980340240100d1420681580e95058422200300c00c3c22085da14010b4001c24070683c882894164030440310a195041207846603030740900b000d030002d400e10703a4803081202552029207082005e0440f00d41c0074000341d1b202c511404014030200380f010941c4845190846900300c10b81c010f141c801900e550000c881c42c2c0c000d4001c1004442d107513049035601403540c140317034440d80c01600048490340101000028690b800d4080c1da0301510030002c02c036450 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 963495458 1250 963494208 963494267
    0x30e0a11040b060c0a0b0705070209060904020109090903201911040207020a03060207110901061403060316081e010203060105030a0b0f03010204060c110a0305070501080a0b130e060601 81
    0x86040c0580056025440b80d001c21800d80300c103800b400c07226503060010b01a911071843c040315443d00003002c00003040b04c103000c5040560307134241c0c0903600001300b61100b041035140c500040300c0c0011241c10015400e41820101e00802d0b5001d108500382c5008920341c58404000150b040da215514140c2c4490402e641120340c1d4007040000d0030304000c03004020401441c0421507408200d41c00341070380c41550300c55030210348281888000c4900c44115401141c40000c558100100504841d82d100318039072003241c0c01701c00600903031010002c0904010700d0014a003000c560f82c400c070594502d480303002c2001048081102603c0154140281d80c051841611240d0540d5116007108000b000f8be54410703580001500e01270712164400384010401303440c0f1541c48400b6000301c0e007003081c5500361100449001741c440d20010000300c1c0b000318040054031024a0002c0c05031312410f4000c000340c90008589603000c10100b03e030304450061580604404048407054481c039a40e010015200c174011070082c240e0418417000868903 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 963496708 1250 963495458 963495473
    0x203070b0a1b1505071403010b0d09020415081002070b06091f090b190506070605040309091b17060f060f040e0103110306010e07050f09041103090601090507030e0a 72
    0x40600107803800304212914146080b2001d0307200b0405450700144045440c040c4001c0380601c070361180c0075041400c00e610202170202024401442084030310350002c22104a148415046408030b240c0060040c0624442c425041c00c1c1c20b2424400e4691a1007003080400901e107640c029a03c08039000b0840914950300ca805010f40c128000344800581c1d92184888000f03890700d03443c40d50252441000c0010304c100e0013030034004880111026005031440081b401c003d103940787c00445031901d60100c0c1c0413406032101d107400c0c0e56029454004044440c10078200c2501915009806d01e841c101503601e40c146d620112000c100306860076100c20340c2042020300000751a041010080291005446000c4d00d041d80e6940c0c0d4003800c41080c0c2084444034450505182c10b071804000e05d03405840c0b9101004480d050100c0047c04a110341089110740c1c03500822190b505a60b290300020010620002072a52880c0c840030a64840c00240a002041e03490403000c035140710700c40d210b446c8030031031101c1c014801500240c8810341c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 963497958 1250 963496708 963496717
    0x405070816030c0e060c070509130f020d02010e1e040f020301060e2103040807170d0215040f060509010903030507140405040e1608100b0f150309011103310203070b 72
    0x50071300c40a824244901d07180e040082071051101000b90a140382001d041001d03441d0080c1c0305400d04061254003a000c40c251081200300a98101c82c00c1e10341541a1006807401d001d486d0282d40c0c001010980c01404002c00b0814480e1807800701c1d805c0020312828007000c8101d01083c025000011068201d0403901d05114080001c148010b0112540d280c0c80b00004030b18540c0310750001c41e0399401c80001048011140c1d8203803100c2c00c00700e402400e00c500383c040c00255181d0501d0719194a0009141c085000d0103411060031900d903801c107600780030f640341240816010f841c2041c0c00f100040c1c40c020005088910030883e1f4011002000a440d00d03103845c05003040083d00340004110a280204040422001010003401c00140142c8002c1c00101107151441022140030080c544e010769150315080942d42d03600c0d01c0400c582690700020740e880303482e01c4084074018020009100c02c202c4000080c4400c088004030742d8404002000307031520292020404818100c482e000c070003501a808450300f4000c03001040040c1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 963499208 1250 963497958 963497981
    0x6092a030b060405130c230306010303081603090501020a0f0809010b030d030902060c060412020d0e300607030f1d0303220503031306060918110604091109040507081603 74
    0x44440d00f040d481b0096120a0359109004000090100014240f40d81c240309415010840140c00c4a6146031806807500f1001054050000304210004c0c10a90191784501a5950040000c5449080402002d422440218120700100303000700009851480e05004a101e119400750180401103061581540900709a40c2c0480c0c0c030210502024081382010003070513120720300810b41c50b10002c000c8400a801d0040d000c201204100c9196409085600c03803c42c81c015511142d00780c00b0086000280301d88450244583c80e07203041c06804288043e41ea407540200390702a0041c52700300412152a00e0034082c2c814140c07010b07481500248002089041000107198400a484071000840c0b206690f031141958030849240a10311881c104410a0002c5440342c40e001e880060f1080001c400c21512020454028600c01484541d030050492001e4030360130240c60080c409400240424440c0502141e610f412145e01c2c6800f952602001548481c8100b02a9005404e0a0750350070981500b05012005011403660342e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 963500458 1250 963499208 963499231
    0xb09150a2c0910060e0118080607090825260d020607020105010f0605070f060e0d02011a0f06040306150302130905120a2a06092a030b060405 62
    0xd0a05104103401001c050071080c5008880e55140004110040402030003511002d900c0c0082804403581100300d6400d50002424502401464011129000300f242c3d002013642c2c0c00340a051041a6800c1041001520b8058007981c60740070381c1090180110641c8090100c2d0180c01801c1001a0181034106ca40c010005001c040b0303200702c2d8805140c1ca00b100d1080a000140d0110f42000800e60307080c07103024050011840303010101d600d000c1d001030150185100150482000d001c0c844208080d55102c03002c00c0c0f030303010b0035503070603135240600a8000c0c09114450b00f103004404400c603032036281017004811a0000207142c181001e0551311410b000303081412010f40140034504000c000b44e60b840482080c0c945102c000410700c80d4581c5021410183c400500358010641031110001c0d80d80c0100b21500f1029544840f0310722000c420710801d40c6031107090300140c6031620f0040100c0034089800c820403800e88200c88101c07003d0060003140941d000302c600c0040c0c03a840f079100107c0c2d8145060b0704000c1e00442d021300c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 963501708 1250 963500458 963500477
    0x50c120d0b121b091803030705040e090a08040303081504180201170906071b06110c0114011401030b030a080a03060f0b0c0a0303051e1501120b0906010c021903080a0305010b09150a 79
    0x1046c42e542c400e40310080494800708040020001c1c1104c0d40764028051030103040c0010031652400c4140c0518040103052015600020ba5441148044200c102d80c0060040c82000341003030a103110301581030420390005080300c00c80c1c1036018a84401501a041090041841e40e96065040380d80d00c400a55a01080340100c0c841000709909015101e0b60039141030a403591500088022400c464001154100130402400100511561000d09014a42c428280410302400000c0007a06224104000901b1500045200c1020a916510038025204203944245225031144a00c150b180514844610241e02c803521210000e8401e0700102d8126614010490340c046000d000c410a0703e0703040326181800400c81c505079400b50703480840f00012442d40c01080041041c400041001402c00920103414021990349a004644510f400303048281b01c2324129804880e00c03807a2506c0903a02c8441d12200007402e2400204040704d107801220980b0030300502501c4844020307080b156543d080b4909e1034003031205032003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 963502958 1250 963501708 963501751
    0x1e0a1103040f1404090f0b06040e010603080714160510030e06190507030603031b0305070b07030f1a030604031409030304170709060b0a050c120d0b121b09 68
    0x40d10180540748803142d41c00d82004554a064109415800d100d02d04105080300401c1c900c000f21446950004040411a91038802040190842c03091f2840c540d07180c00030020900600700b0240070301134411401180f440c0b804507100c9984e40b811801014003408818420400e902e050102404107034560300b0081281c1490302200e90500313102300e516500c140c1c810412080480350a12601e07074000541e040402004e81183c4001b4554601228094011100d4143c800140b42c0141c2c1a5050160b000002000ca8600814018040c040b014550007005052440740aa00b01582d8000000d407040074009144c0c540d0b0700d840072100221455806c6941650400180440b5282400104040c2000441001203200300f40b500340c1ca4019140e0000907118589441405100070100484100c00542e103803564443c4402401681400380c06040c1d8030000301c00066544081e001c58009075107100c0c1c204e500054411030aa15140c6882c3e0034041e0429103080d80000f40d0403450403454564000003021040c0c0c00d0300e54001b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 963504208 1250 963502958 963502963
    0x90102150901150b0307120c0212090630060d02010c060218060c01021e031e04060b09010323010c0206130302070e0a0506090109021327061401141e0a11 67
    0x1900704c02e090a8000080201c410740101090741c80402c20001080080c2038254020749801c150310312200245000500f03500c1c140c6e2040b050b5039040300f0005500a1848101040000c000e801c1e29081300d00d0442034000501030710b40365070340c1e15055406850b010391102450380ca143c001e5120034443c0e0403181c41202048030320341303c3c40090b00304a00e1150005a039401c10034050213904140500800600100b0400c100021065059a8460103c0040170115903281c5140c0030002d8501c940801d070300700160200020901003110a04400c026030142441004481c40c1d41007400e03501d5044942c030242e0302580103c2d50300c10402c01400c8a450191046d11086501c8031030390998842c1c207641854502d502c9105004151a182200d83d00605000d5811454824400041c03155035a59108100c140201e02c405c0144ca080b4212800c82903001c0e0031020004141c9405072078140c540341000e01800108440402c0b280c019011085882d00b4065001141840c0018030111103140d0120600c8001c0004030181080c0c010401c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 963505458 1250 963504208 963504251
    0x203151b0f13030308070e0d1208040311060c1b0a020a0b0306010521040615060906050a0c0203032110031109091903080f0c0a08060405041407081b0402090102150901 73
    0xc1d90705c00085d400d000340c000342942c5130703c509603100e103980e4400540040e0b603507052500d99071030728100680650b0b5036040603540036201d0b40349075010307020345004c0001c40c541e0000180071a070284420f0388031260781c0204d0075590382400803000703402131203000090004c0900400030b0f6911402c145801440c18100c000b65400209210300d0306652060300341c051108002c0280142ca4900d0700802140c590a86407910042803d81035114800500100003079602c51588540e250b030000c5038024040f0703940c49003030040070f500313a451107651030b0b01c0c80200c44040750120001440f040b0031290040c0700c04807100030242c00c0210501024041e07140e80d100c1c60920000711050f42e808010018040d8488503040e140030001c4510001c40140b4580003079400300505a001608030301c0c066000801a01d0025890390385180c40c4180621341008100c25211f5140002001100000d84598a03e4859448284540e6503810301c410f0303000e2986541e0240e00900700780f020030b0b080500070940c0440068008140700540820000b40c2e88003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 963506708 1250 963505458 963505463
    0x41a0301061e0506030c120406090f05030304110a05012102090904151802060a0c020102070305060c0c100e0a0f081e090f0108010f1202041e06030203151b0f1303 71
    0x81048180075100b0520200320001d1406840c40b0b807540c54054030005c0c00748070344103102030700d0001c2002207030602c8070a40c06200d142d6401405d8040c9045141401a81c98008940444400c0022a48503a5509101070910100e80068480c0100007e2074040c150140420100c9100e0141e801e1000103411754400329140d005a00800800c201d00c1c0045581c1070a41d440b03007000d0480315600c5450500107072140c2081b280c04000030700c0d000300c100015100413410400146d1003d4500c1c0f03e18000d00080301c000e80010008900d100e0202c8900d07100040d010001c6c4e82ca00e070049070164000d01104008103c13041f0304954420f02c60440d141c507103a01c142003004140659848215984404190045c1a0815110141c1800c0090030810103542c9404414203a80455002d10111441c0e65000303001103481d103400601c499000d041e41c00c802004600c0d2094014031a42c401a4840e204000f00e000d4000d0700c00d070049000b80061050004014071a5a540c0059404a403190030440000c1140d050403141000440d03000c1c61 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 963507958 1250 963506708 963506729
    0x1511030d05010b1c111c2d2d05060604120803011d0f010522020301091406120304090b0a050907171b0702101106130308010e060906041a030106 63
    0x41c004024031035081e600040000300c0c0c0d0718018200c1c05c1900c504080c3d8801c1404074540d104c0c404182440c040190410004191800e001075868040392040c4040103005407980940802032401c12040700580010f0708007000c40148440360621410010942141c0c0d03010704003a1032940f406580b400b00896424491600b9181e83e44080b0040c030140d4420741e0341d42080b0510a01c03c04440c1408008804122810702c11684500044032840f403c4e0300d10303400b150240c034003644800c44d200e40e5200304400241545208014141c1114000684c441c036299401041141e581c1e80114141400c00d140c407030084c0f0034008050380c044600e000005059545e00704080c41a40c05554520000341c01100302d001070f4401034105d0420f01d125403500c2014822060a446009130120f90f40c4500003011901580e03008100c9440304041e018500c00c02c1358181040302008104d0703202c1d42d241320f000e81c0d80360b0742001d40301016128170343d004a00101040f40c52515030002c0d40da001d0b070603032610340c42000703840040d0868101c2e034000807105 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 963509208 1250 963507958 963507967
    0xc120a03020c070b091c1b03050a1203020a08010314151905010501050405030c06030c130b070506070e0d0b0403030e01020a0e04060504150608090a02060703050c0f071511030d05010b 80
    0x165420b00c0200b0080101e1131070242041004c0300050015000c0d594040844a501d003848030a01c06e161480c00c06a40c80418409105505ca00b1704603111040500305550144010410f402814403a00c203c070464003056031802c0240e4210784d00e034101442e0340303e55210144200d0010040c140c1c5607510560184800d103d1503e000c2c01c00e80d201c0c2d01500c3d0144c2c400313070520000380410002501c01040315115031714111802c1c0d5980d52102c07603030031f41801400b04118180c2c0c0444004035141c0300c4079005295680c01a0112010755490f90130455003d510041c0141e0840401030100000a9000d90381c00e030054032a00b80031035401c034070420307440c00ca0300003c1005c00000c4518118400341e0a251040501411781a1800d2048034034905d480b0110390030a100d80d40c10040c0304c0c00011510b6405101d4200310680c0103001507510029803c005219070003450411540c2e01801c00801c0e0501c0000410408441a030b0101120b45112406c2c10780d805c40691a03000c280e070204119101d001911391203200d029200310440b82d03444 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 963510458 1250 963509208 963509227
    0x230909071d1801051641130b03061c1109040f1218050307030b0705090a0b0711011b0b01061b05010501180606050315040c030b1903260f0c120a0302 65
    0x12101d00b041140086c040141c8016004601c0703a1400308500e0350849041e8030f200351000e01d803180c42801040610300e080c1e4a40850301c50810341c021070143d42c2c11211070581c42018940f1000402c08610010701c0e4000408600382141401d51038141c2c080c1c011813101d410004243c507024040b1342c110143c0303c0003401500e00300e070004180307003082000340c03c0c16802440c0c01030550b0740b00c240c0c1ca039000c1c0201c0d061140116500e83d00b41d48810700c1d800685407150722217880b269603241c030411034100006580e020844100c0c40701d4510300000c100c40040b903001044c1103416480c04806407580140040e00c440302007501d50b0340c800480c1d4240a02c0c0d0007801000300c581c0389511040204400c07a21f25030000020454100140440c8004102792460300010407500054500000b010940090504291043e0000c00c2280744000452040746d944084a001c0c00d00b12240d100d9040700540e20700b8282c2c01c0912240c0040c440080d0b482c10000140c48800001d40880700b0415103200d4044c2c564100071402c00c0043e0700002e10042 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 963511708 1250 963510458 963510467
    0x1a220602060702030c07051c1b0608150303091509040608060609150306010b0307020304150c0c05011e030b0d021c0510090c030813230909071d18010516 67
    0xa00100300c2c0f0255007050b07902582036480304d07403500c602c61050220780114000c45250b1b0b244400d05580c0a028541220b6011442210501c010302c944d401041e004400a9522030250740c61122030200203000c0e614150140c420000c0440000c0002c081d018400e1000034400e860710301c85d50006d40342800082c06130340703000410031183c550002c00710f00d42c4000340c519410017524001030b03180c1592030220700e41ea100d5449400407403841c02640c7c8036820b040c00c607141e0000c4454118040305021030140c84428903240d11500195074010b160988139205030440d2180d00341080c801ea0100721700b045c1c002d001480100180d000203900e007007281a01c1d00c2010a004100042000030029401261080c02c800d0011683c03645480030103403141d10010740100000511610902c1d9103400c0032014101039442d1580400940054045044c04054403c0c050200107002c502c0040d00015001e0440311040c080400d080311009040c44075960140622001e01001c2c124420032103000e01a4510900300c40d400c43c94a10343c050070060 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 963512958 1250 963511708 963511711
    0x31c0605040b0a0312211a18071404171e01090f02100509041a0414091c12050406150501050c120a14031602071a041a22060206 56
    0xe10030780c90030030304030082c0e1202405081169040160341540c418109810b0710440b520300300041c007030600780c0d11139081042c00354048032000d0510004c51400342e0035041030013140e509408444a130480c1000000c0c0c8040e11076103051041418800545090230399850310010b9422207070030100e0b403c5d007085202c030958404982101d0401c4801d00020b2004080548441030742c2c3c01d1480b8007074081c000d00003805000500400803920b40d4800500100901c2d4200b03104808145111090107204d1400c1460160f48c0c448800703526802480700c4006002d400320400001ca000d11803001d03824003031040d0342d400d00450916506c41d082c441e9000d0080421003003510903601500290340d4118174144503040c403400d105e038200007400c3c2c2d00756012082645c1e03640c404400c0030b540241c41203102c408404000000c010b1240c84003800800e514005030215100641c84803e10b40c101c00041c0760034008804103000c1000b07904201105442408008103d5600d440d03045e00c10f80b98008449818464140d2200104201c0541d0400045 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 963514208 1250 963512958 963512969
    0x50f07090b030105010e0409080d0c18030203190215280906020d0804050705120309030c040606050d0c030b0405131106130b0903010f0c0818030f030f09010e031c06 72
    0x2044440d007004800d4030140018040c00b8100a481c004241c4d40341c86580c88440e4954008052a4a07130b1aa020200080c04c07200d840607000030f4012104600c40c8186440070401d07658001c01411007440c1c81d042d030304c845030042e41090343d2005602041459140100e80240b000f40c04040c1000c4600464580d0440314040174441d42e4204000750b40c2c1000881c1c1c0c04210103030480b100b490035000d5a02c1ea0b0030a28130700045500415405900e458500400d984004000d203c01e01b0141c081e5800d00503a6010081151007612a4101050b000c0002c61061b09166116848211071030900140c01c09885012604480d02102e45c415001c7d071004150041c42007166002451150859084d4030700700c0c96280c81c1050150b82c0c42007003003490380400e6036649540c3c290456080743c2c1002400f00114080144014454442034409200c111440102c10103654400f100f01c2d81c2805100e852141b95031992030350861003070b000420040d080d551f50b40c02070b0030101c4280018265100032103110709070503480389009000c88002d90b211 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 963515458 1250 963514208 963514217
    0x4240501121b090614133f02040b060a090501050708040e130b0a0506150c010b090a02130f140108250f1701181e0f020d0f0507120e03040803070501050f07 68
    0x1031080307004181e803019151107001100c0d0702007007c2c04400950a0520700740c0303142140e071a9101807045c0c1070a00041103500807541403015442c04024841148101030b10900040c4010806208030b50044c0f00610200d44102c442c580340960300c00c010b01440005550380303c03040100440c5d4000384816401c003141c0100c0045070030407141c145440011595070048030104961b040c0485c0e841840c0c0002e500c28520440c028121050300d290107045440294000c010002c000140a0004990810600141410764169811042c0d0444032800103440c9036400030b040c4480e02103800060b0700e00180320803030703600604500c1d10b984641d0440917130b000e014003c0038254400d403000310b40c00410082d248090400702d2038220071380009140f03560112050881d01003a0f01d004001e41050710b440c00c00c201aa0061008019051040100026010012040da0b4041e256040000c441302286800c0c440241c1c0154204440c0c282240c0ca01070f90b80032060b0654010310401d48460f5580c00400c03480d02100001c46901c20000c0c0350 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 963516708 1250 963515458 963515467
    0x11030a0f0c08161515030b060402040305030f0a020d050c0a08030406061511010b010f020a23030315010905090c22051302040e0108030c1209061606050604240501121b090614 76
    0x2001c1720b40200e507100140204042c00b01046682c1c5456044038065600315094a5076108001005019a1310201c01c00d001846015904241c0a02c103c080e12695032214010300300c032504030384442e090703600003610580d1000e0740d0f10000601900d42d40410240c80c1c02e07940b16135000000384403106007140e103018400ea0600c900e80540c15452540804d0038107255500c45640341002e0030142001d03002e100e42508007000e5200010500001a420102c0d030312954800340e07a9001c4443d215024802402c0042d10703e43d6014a041c04002c113410000042c02814001000020700ca040c0d9074000290120441c043d5480d400340c4c00201800380713040304459180540041e41c019441c007614004a00d40e42d004040c048020f007840031841030010b641790001c49681100488907242c18980c01d04240d00240001d5480600c03030f45ca0022861820b15000603810100c84d0341169900d00c4620b4040151400700e654031140d598180da40720b14411009282c0c401a00802c0955100e000150401d10046e106140d01c1c0e600d034040b181d0034403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 963517958 1250 963516708 963516731
    0x509120a030519051608090a30090b0f0a0212030c09090603010e0c09070c0203030703030516030c200a080708070b1506190507050a06020d06050111030a0f0c081615 72
    0x5100005d1728114640fa4003260b5806444030308104410a0040c403004200311001200801804401e031400d050300155100076140203c291a410141d01c90814180d005101941e843c1d101c44000e40610586070040d608510030300722407600650b004a44c85014608003240a601c103040081529a214005070020480840300108545da20103441c85074500c900c1910002030b45a0b4880c0140c01c441d05c1d400fa04072a00e9440314580600a030004894000e070810b400c04245090314032030302807107401100549488038a040749040341c403490300940382d0320744048c4151007038040002c46100042c500a8040d490160329046246004819a0b4001d0400c0310070805500e00400c0c0341c5d440c0c20071519a2004101800b130700d0401c0c0203084e140c50051400203403590055900020038410141c000300545d81900700c042143c1525540103448407014480258080e500038040e80315001d004041c000d400720100e0400040e502c0440e074640c03070310364098058a10075000a0140000b040b07810b5a1640400001e80002d108144107034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 963519208 1250 963517958 963517981
    0x10080a0b0f061206010b0a120506090a0225110111030a0e04021b010905072402060a180c080c040506040e2d0a0b01360509120a03051905 60
    0x500001d051400d0440400e44996501050026004109050714265a07603070010700704c1074201103d803001190b8010f41160401e0018440c0b588555030040030325030980c8070510242d000b5003120034500110340d10072800500305224000a5450345203d40703418680300b542d15000411a00c20548040d580d40c0c401e1000700304590700118110700d4010180c1b00183c892094891190071082c42c0c41c5015a154070300141502030040100e03a01058a81c01c45e00c0008400f8581201c44018402c0c13035002c001078000c0700200b06a4041a0000007001000030031842c00c1010341d44400c1c8450903554441c1c0c510342d00031450b10289040c01c0c01200c0e4000e0088070104004800d5002c0a0703160320445040101c90750729944811b02100c00084912a000541d80448041550f0380c80d107190f00900038003502d00c00b0043c0002c820482c2e072400c2c0c018458002d80e001c03081103501e0060090b5001d080040d04a5001c0e002c0d0040c041d01c0c00b0914005450342d00e2142e980810141410306052214080e0000a14451400d110810407402c2c1c18 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 963520458 1250 963519208 963519211
    0x1401020a060b010203040302270c160f0c05061b0d050301030f030e13152d170c0613050f03010e06071d0402120103120504030c0608062710080a0b 64
    0x40404920070480500413810340c820703504029404000300b8040845840030300b60601c0d127000c1c2c026502c0420f844a405040940c0110b0360301c80340700690910f0386400155849075444005200d40c0344144c01c02e4460b40003481e5500054290f42c0215201004040d02c80301c20010f1070240a01420042d145505645a0b04405a06e000c1c0280c20302060200c01c810311f86404503217454070900904100001d841000c01c41c000b030b045c40d210341e001007906403014000b1041912121f031a003061000c000e640480c40c142e1080b100a000c0b210760049801400c4482500341c445c00001c01126542d100c5182c4481d0800c400c10280041c100b070031600036172602c041884403450014400d500070009040c0010107204107640b5400c5000303ca0340c6540c20500208a0810100000e00085d06132803050031080d40070145050100c41d10300491101818072155010f080104600850445402900c00341c0300312080c403555070742005039000740800071101560085c1040402a1818a804c0140c000c410241143d0b40d81602d410a08580 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 963521708 1250 963520458 963520463
    0xa02010c1b03081308090901090b030106090b130e191a0c1306110a0602042309040f0f021203030403020d090605120a0507030b090408030613110a0e012003131401020a 73
    0xc8130311641050003c0e04060b11104200107051440c50340c0c5441c981e8010342400301003a8020740c01e1080104001400c4d0088064262000d420072181d143e15001d0500070b000f81c1220005640609010402401d00e13020000800ba4000d00300d4248815010182c01c40e0301c9001040a81c40000502c110b107110406101610101c5185203024010895460052400e0101c030b01c000a0059200180c0021070f1200b009124104107072603422543d0f500e008809029000300201c800030700d080c0c551102c03000010f400c0c007099540349001500d00621004100f03201441d5500c19a026005a40310101410205600010b608080c040b07602d061410f02d0b0440070101c440c001c000d07201107400b946800000d180544694004401168018000025402d250401d11945d0307100303440942c0102403000002820244030b0160849980c0c1e101161842c00354488421107c101050940c0e1381001101666202e01441c64180c496150f085040516511131a101182d850318125a010341504004840040f0950ba00454440d00b101d4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 963522958 1250 963521708 963521731
    0x305040b15010f08100f03141c1b050a0c03060f0b15090915030706170702160303180305060a020a03051003020a1806230f12030906130b0a02010c1b0308 67
    0x44500174051100b500781e0300207048620b2102d90020a100d4241ca41d1000c9404807016104c0c00025400b0500c0c031149008080c0b00400e011405080010341030020007100507004034203844980c8841d40d140146964541e00650f034050700c40d00d840b403130740c0128070807e09510000c50b03981c091408103800c1d80780e00d1b000b4418801e02c14804c0c00001281d020483d0310311401c46030b0060680d14125207401e00a81030150004816240003807a4001510860000403001100c0600604d0074510506c0c6035812240c851401d48450315400c4412000000520200a45030091140c03040160700d600c1a071200400f201c40080820100350314002e003c20150b11103501e40c0702503801c0b05034002c2e10003e005002c1005002c00340e00050540f44505041880d40401159400344848111206841c0400040401c001c0d191008100c28443d04108030000243c90501c008080d00524480e00c00a000e07600c20441c40345401c1140c400025075160820f410000e0307400703108211000383c10420400309038416240208180c038028040600d00713 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 963524208 1250 963522958 963522961
    0x10807030c081513021909060503010509011a0c100f0f0b090402010f02241501020a0b07180317040f0b0f040b18120c0a1a09060a031401060305040b15010f08 69
    0x4d0f119420950f044500079401555100044c0045d84842d402104000000031100c2d02c004c210288170310210303412920001c0c440303807080c0d0810b15101c1c485083e0800101c103101003000030581a00c020b021401240d16040700001d410400090b541301914080150503240a05d80704080c0d202d590b4010116420940a180c01c6402103e210420383c80c00c88100c00407402c884030203540c40c41d02e50128103028031a22892642c0e206080340c80d001039a5503040240300405160302c8500007074090380308130418840c2c0c4e48403810084ea000e55a03101c035a80c03940b40010f010018480020140a081d80240005004100044c400d603d0306e0500c0d4405100e60040d8040c0d003880d2071000078540405806200d007a860004010b0451800041302d46c40c03682d0740c80011003914002d006501002881c0351401c0c000403041c0c080c0c10060b03850450904100105940a481d040003415694150701319000101d401e880d0103000c450300c0c0040c403402c1504048841301c40040036807102c10b43c4d4809201721a42d101d5142180d9020350300b801107a5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 963525458 1250 963524208 963524251
    0x3171f0b0c070e0f0108100504080d0b03120c0709050709050a061d0604080f0d03020313150608010507020a03090e06060f28120f0b03031909091a010807030c08 70
    0x101070480d48691001c0b40c040303042c0403d6200455a05048410000864601c107c0015240c010380e030781180c0c0648101d134207002c8040404400c1d000140c6694004064610050010759220056004001000407940c81544180314219492107019000821800c1801e039940c9407000080703c41803180601010007403000004140c1210075209050100401000283c40702d48600c0842d0f83c0d0b59069480103cbc51040022460085019108a074042e100354ada540000d500d0588070010b02c00a2440c00c00c900554030000054021001c1c03160714000d0300e49074040c040407011030500500c80e80a640000303840b09211801e00003e6a200001c07103c203180c0c2c80d0340c4103031214680c2c1c1042c1c041a2110f880c02c420200c0ca504603010095100c1007032403c12440d039104001c0c803551040198200ca8103039180e950160300070028030303a080981e00d00002c00c04419140c142d542d9070b254403444050350100c00c803100c1c15464400b00f89820350b030400030941d8080c005140c10001c4440d41c1c1d400070815080508842c0400c041503c2c074216 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 963526708 1250 963525458 963525463
    0x5010e06070b0c0c0f03070f020102010c0e031b0112050703060302090c03150409030512010f0501230a0305060604081b01120e0604200411040806163903171f0b0c 71
    0x1c5d08244130082da62142010b082160800d2040d402c124015417038510360300c0403c1d004121803000c0410190007400000002d8207140c01000110799014180318982d0f0b4100510706040c003600344101e0142e5004030b580c1d440c2d41705103e0300390009004080050b0090040004074441104d04000c420b0301120042081646400e040e10103200710701c0c0d541d403a40c01000000c107042640200e40000c541e004e81e03075011055400018042e0301d114442122085101c1000582c201c107100b074028642001d0000c1c0b94924155031403940500d4040d10140f200c0c1c04016a01d0b24100c1e40d80c2150219000c4810400306101d101034910070546c07a408010700081401d0807450000c0d041c4250784414a40034030000d8420060000e111404100301c0d08548100029881180b000641c101c0c041d44840b00300c402941c550036803054002c00b10080c440e2240c100c0203103003150342c007100034540e201641d110010341c02619501040560800320600080000340090030142200f2a01c07209007030005400c408952619086c0c54952800540260 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 963527958 1250 963526708 963526723
    0x50715180503030f011806062705130506040b09060f010c0c08070f0f090e101e0207210e0f0108040c080706050a0908010b09010b131e05010e06070b0c0c 67
    0x92081c40044100441c0c02d5a02c524241665981c0e1403202001d41c81804c031401340c1f04540642400a0304c002c03007640900b40c0c03940e0000c80c1c0d40038040503000e0158590004c039410468181b0710100440d1107000707000287c10f15100303d203250300f822382d95204c0d035103016004100d684100a100c1c80c104082c100050003031003a2710030041c001d0400c90084d184801d030f49000300e42840009019801e00c500050000007940d03d9148100113403c000700000e0001150400c40000023401c6106503d0450b034580045c0f0548821588000c01001d84180b00c03200034018403201e00e0641300e0307a104801c000c0c0003503546044c41c0c95848030051b61a040c0246001d902c241c0d07491506a1700820140e004181da8440c03c0700102304540c0100103000c006280c0c0d55501581980d600903582a1010b0800254120560388014049102c03d01d000705202c004040c152107500d41c0d11240d080c090380202d0045a542c51805406200960b405007080001901c115012400c042c5151904030800d01e0261181410050005041d03240da0000c1c090036 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 963529208 1250 963527958 963527963
    0x9010806030a080c0a030801080a17030c04080a20040b031009031710031a07050307050901020a0b01170d091409060a080a230f100209010903021c021005071518 70
    0x21a00d45039854a42c6585805c101001c4002c0782c00c2030008580400c0000f03403070003041d401007594080c0d06100c007130806456102800300403225208100202e000102004541c81051203041c1c01c02e0381203d810f000303810000c109130704244518180001d043c1e80d0b40d000a80718034024140c41000404c441c00b441c1c141c0d0140c00704001000d0454420080241211448138007000300e034021550b184d0351072110240e880e5101011642e0801040e0140b002c181418400c1c00500700700075060040b6050524243c4406084c014240e000314201141108440c910364800e0041c072503501114200b034115a4200982c0140301d08040e242c0701d014815140025000e5503803525044000e080710004d176052042030781085c1061400d00100340c2060b1640310a565000c3c2c0d00007542d1040301686402034102c0081050301d95010754040d1402c40e042044032032000c805650782c40700032104d60582d292002d84101003441800107503040010300000b0b01206200c0e0502281c0c20381c80c000c00c202111100083d4104030128032071145d00005002 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 963530458 1250 963529208 963529223
    0xf03020912071a0c0604120c330603050c0d30030b01090e070804080d021c1503170703031b0206090115120b060a0302120604030315050609010806030a 66
    0x845607880380c0452400290350040b44044500300c18142d04079031a00c1001e41c0f2072800ea02500004000c1800811022600c0555241003140d0303a940d5283d905d50000555444009041d2000c0719007903000e200c8039402c210514911040c081d02c0c0c510b0b02c0d8076450704020079000d0b0140604243e4941001918201881d800c025950010154039418500a5050210800301c10110b40340a00c1c8044940c0a0040320040741c400c855501410b980340c00c422104400050001c540404045c41001c401c00000e0001c0d220320800030710480f036180041c0b884002600d4422510856000c000c210a1002c41c040f0109441d0b010b41c6401c4c401d54070038a61904500620065503030109040c3c2d1a1411a0340c5039010a45500641d100310003400b42c110b00c00074070b00801c8042d108207108031002c1d40b0410005080da4020725400340c4c0c001c01d4103070919501c0d00481e00c4c0800b03209001055070400810041096090710900404203040400146441c0c00c08000c10030502c180c031744043c180a010b0000a80c1c959040080010285d4008403 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 963531708 1250 963530458 963530479
    0x60b300108030d0b030c1521010623190c050a06060b0d05090f03090f120708011b0f050d0509010b12012f0706051806070e0901091b0f030209 62
    0x6426241e8101103c5401c01c241000c43d02d001c3c3d13190000321141ca4400090960030004514482c002c51a07200120150003e6407030b0300610030060210340e81500030041d82c0c55941e01001c50300400341068070f001540c0703000084140248401c03400014245d100518007030400c0d0420b110f06060092518041001c0204190308000c1d02040c10000c090281840305807079003083c085502e071418038030b480d41441900c003000c80e402440b41100070300d00850605881c0c039002d4001d4000c45a002c00312402c04440390800326a6a44034852450300d640000320216000170344c0e2030910464069040010319a1003424001c514054840c0042100a4000c1d0300003030743c85030700070101c0422040707160505002e000351032001e2062642501e151500013680440d03030301090800781d185d0341c6840105e554880c014000940b030320f5504080c600070910781c06003c016003401440c1d13a8444640c0401c0f20402c102030054160071070043c007807d1003c2c00304030b16180d48840814045504091040110044046001b0b006007c0c820350702c240d4100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 963532958 1250 963531708 963531719
    0x703230613030f3b090f09070f030530070317010609030206040b030c07020d05030d050709030302060f0601050c010617010f23150d120909060b3001 65
    0x1625542501d00c6070329100c1c1d441c560350900b95242e4903c2014461074941d20034180781c481114070100c480e20181c0c10710a0002d01c134481c0c042603d180045074030120f048555000d100c1e80d10410403401006291a134144802142141c0d25292115906410039045410000150402189415500d000c04024401036138231003000b03080040440c01071171300040d84110703004004a17600c0d100e442c62100303494000c1d20140c41d003807626111404540c002440301c000004203010300f8005903104001c005640d400340008585070301ca2500000c0846c0c0c1e01400e02000d004002c20204000798000c40d50300e0b808030702d040c160042a520000103856510038000300c084154646907004c52881d0608000d07075900480c01c0002c0100d016070f02d4642040310100000c1038041808500f00c40403030a14044140e5003c0540c00305c00b80e91005020100d100c25184500444131000c003044c1c0c180b60580e009003403500070501a14244800d61600800c3ea00a00c5142c90700255500c1d8158030a0309219036104100c08511600c0c40c003105076130f660 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 963534208 1250 963532958 963532981
    0x60a05152115041422021215010311010804030e0405040609080a030903140c120705030412060504052a010e0d23160302010503070f0e03010f06090c0206010807032306 73
    0x7400700d00d02ca10326100b02138500c45003081000d0721070401c50040810010000e1694410600c5a0030120ba00c6003140b0304c0400202801d002d100d00380ea40f103a5842d69603506529102d101d00151401003410800e002007000040b9034001064050503409890014090703e445c00c00324003412140314003070074009001414010050b030560020003840e00035583c0f807032106181c1141d072285210308002a0a1a40110000940b001e0000c00400000d407152040300d15007a55501e444403100310300c03c000d40310180e891041000744001803007000f401036010b00c0700810200c000ca04210348880450095810480c03424603080315602e6044840481c1c2780c0004200e800758007505074458900400c4484a20a03000340201d04c0d032404108408801a02c0c1d058403051b0966645140441d200000c081590040100d241405000780c3ca083c4129000004069400b240160401d00e8034000e59249008420031544110010081d0100c0032a083e01640c0c1d122640042d03001d0b144d07441101e03900c800602c0e200c00d80100c806210b2941c0d0380 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 963535458 1250 963534208 963534241
    0x60c020a0e041b180c0201090206030a0c05040e0c0a090b07150507052511030303010605030a0c09090207111905030a0f02030f0303090a03020607141206040f020c0601030b060a051521 80
    0x813020140401d40c0f100d54220f090f02d5103501e0080d00301d0403d0000c540d007102c83e0742004506071300d20b1030050b013001d580f201040054074040d00c9120301c607180080c0340351145074010341030400ba040d00d0030903500c2c003400c540e9940705650511708084411543c401c04115010b12980403610b880c0c0900c6101811500c40c1c000c029114541e1500c2110884503031681c1610a040210982e070480703825855150541d41e0b584010303406060201000c80c108440c092021500860900c00307442074502400a054070001000d00f800910342413014140101a4081000c01082d42c00090407103003075078407091000c10b511480c0b02182c580b81281041300c1842c04044104440c040c400035a4a0f840c5010780e0860385941c4032041d00340c0300302c0c402d00f0b170718440744c001040a445c6c0090100b022580100e4040e20004400105181d1401243c000380c40c4c03807015401c80b0004000348560602155000901241d144543e13078501030000700304507488900d442201c400441c014040403444040b4039841704801d80000395610300558521081100d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 963536708 1250 963535458 963535499
    0x12110909160804080703020715020f0c03010e03040b180d05060a0b01030b0d0615180608100b0306040f03090506030a06180b0f0d0501020c03130f060c020a0e041b 71
    0x80400001e05000c0c401404122810040c0c03210112503e49441c0d07002140d01128040d4150303c00c80100290400c4050311124170241264040c0c00400002c040c21818004a25145846603040080ca561210004011641201c0011a140341e40385080c16001c032081c0c01c802001a07018901102220501c04041034251298012a00411600800d000150211014190740b150001c6158406400240140d40400d4000420120305140943c2c0c8040302d16240704440390401c4a21b840c0e600030015028204031a00100740100410301c800203901c03002c00d80d141c0300180041c0022009440300e070140340c0911816006420050202a50780c60118080c2020384030501c05c90401c91406080c072502561a0f2040d06081140101182d40302c0040e202017180c01c420b036890584246d503081250400b0b09804000800303c001d1030901c11281c0a19040ca880340784a03083c6d00000034404e101000200507526800c407841900d207250300d400d40c9d40d00c850070141804242c5024980140380201320105000166800d41100c2d0700b03 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 963537958 1250 963536708 963536719
    0x1508060108190f1a070e010f0203271f0e090105010813082209050402010f1409090408090310060e10120204020c0102160c08070b0f070f0201121109 65
    0x90703035680d1481d601c04070980a4502c581518103160300081c1d4151481000c180646003084562525120415504006580010106400c1884078000d560003450048290302e460002e1824032031400340a1180920205003080528002c80f6150303803075a00d135031118104448908043e20315040b91400905858203804c5210b11856052000245942c8180c12083c8104280e1007004840b0080b070351504065048400704107a000480c251005d002000904502c008140c2c4910114803800d0900000d001300129030000d00800540d0001d01616040c3c2d9411601c03601030a450980c11680c960402400602480c4040c0f1351500a000242d0319010190b0003110583e5010b60980c0c20070b403201002c05070a5200c5100c0c03400d2603034046000700054a402d5018019107405031001504e48014601c0e8800031814005c02292170f030700c1c010380502680300200403000181001c001c0f030900e07084003510300c0485030060000040980d03062100e05004c40e44101e00084803130f41c0341d90f0148080c116040301201c0b107420200c035550146 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 963539208 1250 963537958 963537961
    0x60108070b040605120604290f0d0803042907050901020c0a050a060c06060f0f03171615110328050708011a0c030f07050c01080103050c0d0c0801150806 67
    0x9800700030807242114180e480752480c00790070828a01902c0001070019500543d108040c020030003107044800c03050f202002c500b00401c100401000754462400e000170f0302610103907801c200080d0015003200c2e00241c0101140040c000b00c0c03601c51325580c0d080c80400c04002c0c075441c01e2200141d000720141c115007100360260744451001c4000d11a00309401e00c14a0380c4103031400410410030f4001c1d113190300814042d07400070503a240c5610184c4110b099aa0000039161300520040042c0005400358821890f03640c0744582c079200e13040c1c070111034250700c0d81000b81029a1142c2420403280e4180c0c01042c03400b90640700e8903201e191208100050300300c00842417540b01300890941c982071a2510507244940e1098840300e80c182d003888100c08041481e0f0541001b01401001424160f19003000a00205642d4158569640706103180541c24465800380003030505c1008001813000500106841c108050103403541c0c240301009040c050b601c118a43c4c4280d005500e0070368152a403501001010064400c3e0408444030b6 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 963540458 1250 963539208 963539219
    0xa1101020c0f1518030727020c072d032006070c090b0d08030c031801020c0709020a1205010e100806070206190e01020a0810120803060f0301061706010807 68
    0x7815502c900003603010310000b6000d21503048030009000c0741c0341e00329452168000c104004ca40f8022041e0802000c40c5000c4030500360019000e51200120300c030400d01036041a008600c0107036190254040c01c400c100b41d035034a0700803648503600c160350300c110700039010405039549091440343d440d100d441e524081c3e40c01c070111090700c3c2401812518103d900c500141c1c03185280c421040300400020742e1059021102000a10106488101843c081c01c1c1000849980c0c0c14644541d0301e14008480c3c0314402e03640144092000c030345010468504880300324101581d207000d02101211843c18140810707000e07a00c0c1c54004154441421011031080e40241014840340351101d020b00c0e9150070449020340143c0c0b00400168482d801c940340649505000500816102410759000d408e83e088910510005107102c030400407040059850200144540640d298400c062030726480f0030382c48000c0116001e03103410340c0340b4040c40e2002d5001c00f004049420200060315002d901031601c8100070320542010b8480c2482c0441c5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 963541708 1250 963540458 963540469
    0x60306051e0907020a050d1d04091a10050319120e0a0b070f150507030c181406071e03020c0102010c050a11120307030b03150103030e060d0e0a1101020c 67
    0x5607070000303001044210303400d401c1004080780140030104501404100e4800150200080b4440c4100d58540c0c40d14001060845418a2401485d00740701e54140321a00c004500e035a6848814900001d01c642140c0d0384000c1400342c0030170240d202d160544a0000c51824601089004007103030391140c20fa00c0c1d06030b0490074040740c0c5a18204040341d4090307100030080140b680c25100900300b062042c2904041c4a015460b1024440750f0010359213441a00ea9041100185e418810410341c54024241810343d114014122661000e03140501070f034840280d240c1059956408007030741c0381d4070f03403014500204031020b0806044805820b0350031000b5101d89420030035950300600444425100035640c0301c0c1004980d08048403102c0e0000c124410501035000328403400041c82005500ca0f154944020404012507818585403009201501d024203620800500c0001e9020650214843e0112040c68403a078540da082d400404544a52403c1442401e040c4810001d42e48501c82c0902426001c4d540c88042403000d001 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 963542958 1250 963541708 963541729
    0x15051809010506031306090209181608060c07020d0203030c2103041e020607390509010603020c070e0112060506090621010b13021317120d091b06030605 67
    0x3c0e8003541c01d00001c0e0100c0700c420201d100300350080a02089070241e0740c010464200b4181c40c085070703042180d5541001d4140402c5031010010701d028080e00818908400c0e03949500d400ba082200003036000684800755076800d9040804140c000381582d503034010a00b00940e0700c803c0400036811848076140202d840303405540c00c0e0b07803043d030300b007000c00840480b001c5015280315100b2104130b82c0701d0418400a00454411000d05020300d0800400d07c400c4c807040c100c060051528120400f00350703854510309001070345801210a045a11504000d40c030346d0119804641000d50a0704404000714000e0000103074250b50500e100000745c040e00003003060ba15800c0500c90441d200300d43e0980c200c05080c0340c900e14031603031014545518081c0b02c000611081c029002645081400031001d51154011540014010703605c504d00005196003490500071020b0840c3c04ca0311180d050107600e41d031241c0803a4004c40003640d40c00810196038400007854101c40f8020218150004a01030440007a1800e107011489007408080035 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 963544208 1250 963542958 963542969
    0xa0506040609030204020904111602010201050c341202160e070818070819020405060405040f080d02040513090b0903090a05040b240c16060503011e1505180901 70
    0xe2440b14156001d00011303600500340b450f001603440031703e20342c0001600c0c05810011120280001403003080e00009003500c0026001c403040400400030010300c800c041004600003070090802031080420012002ea2882e101c0d20081c01750100101094411a80401d20b628485144413880c1d6034652281d665a00001c02141c8400110305100c0c0454407216804e00d50381c10400e80c50b000c13603140540703c1044508140c401b00c810407002c20514603000451038240281c980c0440190f45c104450b1403e0f444000d1051314010000d01480400210f030582c915a90f0111809488054100204500125054001000e12034170990344810320b50042402e119010040b03440084009007950310907410301c0108002020609510303a070011843d09045002c00c60224a03581c03d00c000c610864583c2c3d020840c0c00e08000100301744c00704c0041c40348010f110650b0440240c0f4190b40c04040c0d46110116184980c0081144640001c0c51240c1c0e440000c0d4280d5911500070714540e81c1001580c140c0d05042001d02079440c0c1c007030054 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 963545458 1250 963544208 963544217
    0x703020301030822030804091d03210703091b0602010c080f0601030b130f061511150a180506102102040504031202040e0103060c020609100506030c0a140a05060406 72
    0x80c44144c08a07080e4900c041448600c1ea42482a5659030743c4480f5070083c1d00001213991a21a0404000d41040829011201c1c0001031860420100401e607002001101d1000c02051980f02141c41603100303600840b00a9400000c403580c41030390402c5100809501d2081d10010b40c04c0c00040d1500394456214240a4104940014165110030006502070100e01ea2100d0304003080150800300d03120a0300890390401901d410010b1034500707041d001003a0090f000400400d000c0e101c0000343d0412030001e003c080d000c44400148546403a8019083e02428001c20007100e11039007450008103001001c03800f180110f89000c503981500daa03400303500415607840f880001210890341210000750510307801040e8001e01c01d1418031417400031001c01000f207802c150031400f4051400340041c400c001443c402e9030f4030f04000b40000d02083c6045081c02e5a900d070310044811059840d140410102e0700c00f042205130511000b00088401d0b034841ca10501494039110700c0703d01c144040e080000d0142842c4e030840d13040d100309954 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 963546708 1250 963545458 963545467
    0x307030509130b0a0b22090b0f0901030b060d0204020712020c100c0314130b0304120e01082401050f0a02010218011403160207090612030207050603090a0b0606220e07030203010308 79
    0x546400d401c11100700500c10b103610821b41d9880c0045d1b8415014090305000018104802c0c414445d600c2d03000001140114903040041c00824090034540d68440c004a9508102c0c0045101107406070007a0b2030020f011420000540c10f030940c000c01c40d0341c48914107a501b040c0c00c0d1003203d4100c41d020444000900801c03c0782c00488140080c1e58001c0c0406100d002c1c7c05200c0e65501e0219152981c411181543c8005104610f40c0416901501c40ba039070301001d107003488843c18100e000b4488005010100e08034079551403527a10050b40994155980711031000010354807a9010840640030f075010f0300400e204003040c50041c540941c003a0188998040d00341c8070035825a40d8410440c42c80503c05c841d100300358495803c002910319010701841c00500188514a0030b405040d2070060701d44000c682040f441344ca0107008200e0070501c0041c2025500c2d4008032103000503161078010800c0c91048200d10504800c103540b0000440c0c140551480444010001824155842c8403080701240428000100021420403 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 963547958 1250 963546708 963546719
    0x2040204031a1803161b12050f070803090a091e0507030b0405010515030c03040609080a0504030311071415070c0306020901110a0503090d0519030e040b010e060f0310080307030509130b0a 82
    0x880d01e0a81420300b50940d0141c0d40c98041d1f0008182036004112a80e900000042c45101805d01c46d9000a00e0442c0041d4100010b01e000107102804600440d464550f555410018030748111041c00192540c0c581d0030030260418003070082c0076000256071240241e00f400000100c5081c0150500c03035502c607100c165411600c0c0e08082c03400944c07000d44103840c05030302c9001900c049521140141640308003915042d0b40c1d5031030346c80c002c1d00609038031031100c1c2190840f01d0204a400745418200c904500225083c59640e1414401e602460043c2480500000d60140000c02080744a45c024000c41c0b400b40c0754014401402d99507556202825500108030f0f030828841c10440341460203c4188543c450010f0b070f112081c5a44075203850b4a2000c00039000500c500c4052021401d140c8a1500d440c0740030300c9c2255020358050701041c182d1103180c10601c02e814001000940c1c0b20709008000020708001c60680b0307561041414028607541058400b1489081c19042c06808181c03180303e59500d41c14040c0c0914801d03841d00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 963549208 1250 963547958 963547973
    0x150501022e0b1206010801091e02010909021b010e100b0a1805060a030f03090f060c0803011707210c0918060f0b0d0b1608040c1202040204031a180316 66
    0xb40c0141d0811a0700b424040e00c040148140383c0a04483e0340000b82c0120742e41010301401952010b100d4034480b400880b20007607644480380d002a540103640141e500d001c1303030030f4506010380345203400c035469403802140d07120141c3c011400c1d001440010300d050200183d81420820f80020314031402500c40340000e80c44409014030381115901140c01400d4814030345e940c0d29502c03c1c88603107180440000b43c2418061000140d011120000b0f411a0300e8a0244800b041d43c4808140c1b00600402040270403489089a070760108100c6a005401c0d0399259414228004608038498052a80c1c1110f18213a04900443c07000c0c513500c9240200222461400490240c68892034020980100c1e05140d00303403103c0c0c00111503100c01001519071885400031780e01c140341590003580180c102680200410950405000c00700e07842003d80c4064908650201002e4a01840000d00901c9943d00c018440b20348894500308584007500014454964501e4444402c0c2c06140a03c0d2a48130b9010800942c84404641c6800300d20207 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 963550458 1250 963549208 963549221
    0x1b05030601140321030f01090605030a080d2304060c0816050a030b041d01050108060903031807030c0905160309031e03060503030c061807080c0919150501022e 70
    0x1038251004c254845402e80c001410840c60100d29540c0003040c4445494401521801003440701c00810080381050300280d16132070700c1c241c043c04480c0c022a01040c202c089905c004801100c9259102419607882d81141003003104071030590700701d89800780003281503020380c0d4610300c1010856a40f1a041d21000000c1c3c0c4c143c2c0004020703c08040d034900e0040c5081c1c803188586840c071309128010003010702c102400e65007520300503089803c0582180c805c1c4049404004292a04958403042d41048040324511a0340342440c660700c00f07014103407803460000e1009a2648070303034091072141c1002080d0080b083c9064094940843d0b0040006003000c0c40b0030306850301125801d070407000034600400d000e41d8920000e480e40d0450090101550000002d01071413a8221081c400e4041960001d400d0301351810840750788401044480900520b600d000041c0940e46c0300c8004181c0b050f01c00000c10264040309543e898407421801545d0140c40b4041407148803c1c00740b40d2800c0c25000010b03d00c10342080c49103c55003d41071 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 963551708 1250 963550458 963550499
    0x61d06122401140a0e04051008070506070c091e0906060e090d1403070c1a01080106232b03020d021212061002030c060403020c0114030112030311091207031b05030601 73
    0x2217005440110740e1140241c6020300600042c1318582410440581e051805030b07448507101da003041200f076000a030607044c1e09040380c085200000c0c4958450400301165404094000c0c1400d141c9040203080105542c4181c05550206416081c1582c0340c5d001c05a6070440a800c50000c0b0b8600d9802c8400ca01c42d1f04c1c01160701c00624a480b4442040c45d80e6065a69440c00903203604090741d02c1c0040c08104400d02c1181e0080240c04094907507617035034040040c4248107d4000710f00507075880180e82c0305069810031485200d00c601c0d1407145510079a007070082d110788005082c40c0050140b007140c518000094420740350f242243c062a040113440320802c00c00001508001d071402e5000a1000b1020540c0c00e2103c12311960007034010385030044000000401000c200308407442000d0301800103001d1100e40b420440843c55041c00c00141000300819151240d000312030704241d0001400141514100011a01d502120f1252202c60a0140180d0580206c000175004254143d845080100484184009900350102 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 963552958 1250 963551708 963551717
    0x5030609071b0305041409010510050d0b09151e010504050f0a270c090b1c1d030a110601031e240b011710061d06122401140a 55
    0x19521002031007440782d6440141c001c100003150800600080005c0e0348810385084806c0f0402e0740c1840009001d6400780380e14401049000720f04c2c007100d16000c3e0b1000c2507402005048407000c0c50890f04494000440803900c0340611400150703e400b021090380140b107034510507101d250400d410081800b580d03c0d00340b003007503521040201c000180c0c040d042c201002021422085400c010210041d50b000303840c00d8011240c10012408800c110b2030304e00703500b55244031031018034050030082000d101c140548002109041082003110021840050000013007000e0f41c01074403046051094401110b480d030000f4880500000340c1009060f03460103e19502c0104207214480421802c880b601d501340300350b150300c400501d0b0745580300b64100e09580c00c2004140d6890102c00828510f141491181c18801d4492051100f84040c3d003040c00c2c0c0800c01e04101d41c007000c1e40900301d20b848108500304005240340c2961004014604007036200103441c100178600c21141d0f01038464000301c100113803030301c01964440c0f1900010403 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 963554208 1250 963552958 963552977
    0x90c0f020a022b120e030f07030b0414010f0c18060c020d020907020a060531050c100507020411251a1012030804020111030c07090f060f060801031704060503060907 72
    0x1000c140113880c545032203590b9032940703021074814145800b01c201e004420643c0481010400034031010180e0703502c81d60050050300b4803112485424050552600c080c0c00c4141069101c0b00e030725901081e0444103032040e00b47d40030420b955000540d800400c080b0080c0d0800208114040581030011035190029503070b104031500300c4d0b0251142d00869905542208213901c90000203241c9440c21040d07181d410320503c80000003411f0503a00d180d07880340f2600b070b06402041c0c010410301b0f149000d0410750b00a036030040c0c420b225281440441440c2c5034401407460f681d207095580780072602c201c004440070601c0c0d80140030000c0b150020b440d80602d550014403850032100c0c00f0303602140c510303207519018180318442d803292a42c13410184000b41181d03810340e1881c186a0700601592122440c002040030403109107090028465a61001103c09080c2c1d54211030300301701c00c5103800030300c16a0050b11a03048078010075154070340360b420a550070364600ca00d100e00030000c0c4080c00071400a2030421007481d000a84d508190101 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 963555458 1250 963554208 963554213
    0x20709110f1803010f0b09040f050c1905030d03020c07060e0406121a15180612010518070806040321061a0c0c040621080c0106090c0f020a022b 63
    0x81ea80038004045110a030902e000a550030f00b40189056001c080e0b0b010f1107051401c001240c2e1a010080c4042c0c420009403903000c09106007440b07180078901014051104210300240401120320076807041c40d001c1d1184000d180c400c984a4070030b482c00c0c40000000340410a141800489801d51a000d00d2603229503200c1e4001070003008a504518075502c01c1003071030310015008080b40c0c0500b0008262100182d032f0700071400e070aa03941340708222090028071075000c600c0d2120000b013950710304c0f00e064a401d2507280005006840000406059030068000b00300e49c502601c2d00101920307204240d42c0100407501c1040d4100400181e840c6d51400054000c5002440903034400302030580c1200980e0400204000055400d4494000d2100d144542402d403018801e07689800d000036190107620800301006000c0e01c1c0550208a0380b80c0c111107451445000034001513403180452001801c40c211a00302081d411103040d400c45002013800c41a0710740040c14800170320700c02441d000310300e2001090b01420003800250341c0c00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 963556708 1250 963555458 963555487
    0x41e08031303030f0c0803062e08010f080d0e040504020303070501060b0901031a090423011410080f100c020a0b0f1503030408030a0f0e031911040c02070911 69
    0x4101000c0014051078900c0c40c1405408400803682c407404100d00a00c411001c68117140440c3d07008902560803002c0030550840000c0c26043c0c01500310744001c09120b0701043c580d8080e00ea80c0c140c500c074140c5500d05a0b520200c5640e101400001d031004520345034003440360b5140030341c4100e5016002a060342e29120145c0c0e14642114180e4101c601155004a075903502940c0c54415694010b0420042c80c101a85e280d001440500300140010850764a000c036009000502c80701c13890f200300382d010003070040c4114041140503600342140c3e114040c540d0010001070800300000c01c0c80442818a02920000c16420901c078007401804a2407410b5101e001c0d204000078180e01036061042c1c1099400079914189010180026810a210b80b03120b41c1c000d201c103120b400320100440300c62914074141804025003480050f91904920588582d06010b6110524040041040d807032405900c1042840203007032200c3c0402c4200c0e95042e01280041e886488103000c926000d5102c92950892218107604040c150140d8a1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 963557958 1250 963556708 963556717
    0x1404080105090f011b020a0209040819091404180b18030c030c10052404060e070206041a011a07051203010b0d1503032f0303090109050708060705041e0803 68
    0x2e0142d00603214850003110038450752500503040d151032208107807011002035443e103070b040c0081e200d81203180105d42001412412155583c540110f020401c0040c12005029003079248508010582c181072141700320300d464410011055420031341415425507a4a540700301010081140300d5916165410444e0f018041020b405440307aa000110b071784040140e095800c02030410000b5490508010034003c0d00d20203000d003485046649254140c901088a001074080c101b0343e0300242941c1503d10a002c07165a010607414031590003100b48a17547d0a016180340710004007441035459031612001850884503801e8024485580600103c5110703103800041c02403c1c0e8000e83c07040b080318400145441c03071485140501c800c03d912112030642600d01d55107010381401846000034081c10103400403011a01c41903089180d01f41040b07401c4989a240031062a40242540941a201c2d485010340010300c50740700060880c2f04d14410303a82e1500382450500c071003000c99040220605044085031000c0743c01c803c20400f50 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 963559208 1250 963557958 963557971
    0x114010201290f03030a05040b0a020114040b060111120d02070201090e0f0f0702061b091f091a0c0a030c02150a0203030103031103031e0901060b0c0307061410061404080105 76
    0x1000403204210010480400c110b021341c0050068480706604182540d00301c52744900c86c0c941e121700440049005103103d0001e010b000900d0018401407006c0c103001c80d4410725080c1c0b5055540840112816528079070041c0d401907400c0d0400044005504640107081c800f4810304080c031007152120002a50070100b20340c244007100c2c140e02001071190003013841c1c03600009940084c0c52941040880280906414045070800d4000010800c12039120031030342c5282c0d003401c851140a0480420130003825880715200301042c624051643c0c0c0301c11783c0c03000122000007102d04004c3c40c4440250342e050b107094882000070b0341c0c4580c9082140e18207400d42402000241c865501640d940d6055141c00303040045050700c4003005500074010803941c115011186007241d100154014a1550351200c158054103098011807904c1001183c082c1440030004050200544255010700c108181c2c240410101d020407a00d00b082858600b03c02c01c45503000d16a00b4040f10801c0d108503207002d4070740b082e040c2514003d8414 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 963560458 1250 963559208 963559271
    0x1e09200406030807210f1b0c090f0b04061d1306140f0a06120b0721061d151c030e091e011707061803020d08071e0b0114010201 56
    0x161114141462091700303110364038140f021794070a4403500202210100100c5461100d200001c00d010b000028011600400e80d4040034003038003034890518806070803100d1000c7c1c000c0b81001d801244280484402d405001d011200d0460b099841c1d2080c1c07000080c440c0c00650b0140d583e9209c100c09100e031540c8662090015501d64002414409a0304003250115408000d14411048440c1e000405c1d02000e150003900703900e070603001c0c10062010054540d010703010006400d03151960000300b0390519160042c08418690040c0c0c101ea4442201840020800100507803202d05900c400c0c0174001c40040304602e03540a45400c0010000c0719001c0703400f80740269090900800c107c82c4405403400590300310b5000d800c5c02c84150418409070103a890b551242402000140082400c41d000f058001e07108440c01150001e101980207055401c02c100e542c1e024030402da9007000f02144142c0e031600140310102140380c2c0b100c200f5120340c0c60b2419000d80403142161840c119502c4000c1e40d00914105461a8034100f0040003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 963561708 1250 963560458 963560483
    0xf0d11040f061e0503010b07022b05011505030a02120a02091003120c020102060c0d09050601031202070e010609120f0209010905150117040f050708101e09200406030807 74
    0x4002c0c0030310b010700c010300e800c020303003100c3e460203c07030303000007543c0c115140715a582e0348810040c4005222452001e507100e51400002c00703030081c00e10241000d4418140544000c0100900d904c9005920301c106019090b0154001400c1100605007810f170440c040c02c4881c00e68011182e0f90380000d0540a09540c40c0803800d040c00418818098907030315401d0300829509100401225a0780044e4840038028044c43c032090010404921121007a0410003601350701406803030361903840e80b4103000c0b405212071034180103109144001c030300e20140c580c50702e040c0c40d482d0f16500d1801d460070025551040807114122000c03940071162000503100e2104c3d171801ba03c07041030045558a044140703014511000c0f01c40c10b040044d80300702d4001111311541c2c0385e0b4215030080e01ca401998200e0406510384107080d4002030072403145070028000f003031042c0d100300700300e10f03d628030011038610002e020385c00e8a0300c048003e852510807030411600c2d07030040500450b01c00c41c00f60001c10b1076079803516002c9060f041000140c848402440 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 963562958 1250 963561708 963561719
    0xf010c1a1315090f15060f080d020609072111221808041205250603110307050d050919030201060918050a060b060702121509120f0d11040f 61
    0x402c140740b80c581000b04101034402500c8669080c41d5014024118036110507942140541641004010b0701002c44610910346c0d039030440da659102d030001304d000103018140129070012070203c1c100c01115100604035180c0119480d91701c00a440800084071644010140114507484002c101000b108220001e00e214000070032005050340c27610818403103021801d01480c4005018001520161802d510501d811242d10f440c0c01490b01ca000e40200f555010703081d000040d40141c82e40d81d00142c401507541840b440d0742c0e200c01c0d200c850105941c010041395041c440002c0b0301c1381070340c00158840c10700003c0741d50340c4140341e000c003100945180b07081c5d00503515240284040040350007103611002d02c11610361a60022a10346544070442088014200e0b1f489200c0c2803010b5644400703441d0120f400400c0b80d813440b400307402d480c2d0fa10000c1064a001c58440a00092010103001c505070059070f026043d09441e00a00f02644021036209020850300d0f142d450a0f10f910049440001e04080d10f003500b00c40c0f0174903040c42c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 963564208 1250 963562958 963562973
    0xf0e060a06030e070b180a170705030706081518090d17040507060f0509060f0705150705190c0503030a02090109080f1f1d0622020f010c1a13 62
    0x150070a0041c581416000440d040d8000ba54900300e030202c4104644404140c0805500e6070136108205600881e4020302141c234454410840081554000c229080196a136045c5901d443c0644500710103c0c034148005100740c412070108440f0070700000c0504803581c0004410382c0300740106807004002036104407150105a5001440146845150001492185840d645156440301607006510400a0629000d21014040e509580700550300508803601d07411601c0724080150007186081c0c031184a90040304a25200e584c041074003d203060f42d10a071804031500e10340f0320312190b00b01c41c01042010398014400464024005140902e26118000da698030f032620004290b420140c02403049604507070b0802c0c806020001e614403001c003000c8503078074605000b01c44540052a01145111110000c1b810b4101d0341600401c0c25481600014101c60000d10441030300d11140d440840c00940080700b080001c401d56000d09000503540740300788040c41c12200300803500000747ca0b096507000c26940e480782255080041d907 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 963565458 1250 963564208 963564229
    0x80711040903030f060816051504090204090b090703021c0506030304090e010501090b01092313140a0c0908030409020c0109151e2705120a080406060e01030302060c030703060f0e06 79
    0x41e0740080c01c1c0411200c51010440001d4488c0d940304d0001d080300104200700e000183e9000b0b01000c0d00440d00c0b240d9070282c060142981c0b40080d4410201e004c001031080b4040e2084d103100015801542440f144a40074090041a000e401954184814000040c0c2c2d12114050303134012070600310001c01c0552401c00340c80180d413410300b034050501001c035405000c0100c619111850060041041c2000c508882001c02d010b8480300b13142d82c45050514895480e5810740c001c1441c040e0080c0c1008000701041c0401c2124040c0080c007865900350404c0000f04100848e0b0380241c051055440d000103070380310079507589141c122100030200c00003175210065001311030660030324a000198181d40c00d21650080ca22801400c99600007014503200144a0800a103c0e040000c4840307007a50000203030f0740e00034549028282e410100c9040b01c3e00c0307041c1800840c4413010380c00414100c0707502d50001c0400f502c40b500100c03100e406c000d00c50010180e480ca0009001040c00e690400145502101094141080c4c42030103040c000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 963566708 1250 963565458 963565469
    0x20c0c0a051804020a0b1902070602060c090d020303090406120b0a02090a2309090f0c03030f07030503042d1e021509010306090c081006020604050703080711040903030f06 75
    0x108000400c02500e407051690350300c0b180319072a40c0c00c0d99164400070340341c070300031b40c0000c40b031160007240c0380941201c40e001d800036140700b540071206a20780d1100101d035039240403900b42a540c007041c0405000c81c1490b4044426080c4001c003501e00704035182021404072402c1ea03202100059440c10080240411928142d4011100140a41c0741000c000086908200c0f01e2082010707549103200100b10f000e0104503a011192030003028842e80341821445d00380d076094070064280e16030003820103400d0545000811206000b60440303915050a6058900350303045c1e0001031080c1c2c1c0003501200e0340d401a001d900c09248100203058003201c4004410705055201e04a0348042143e410106003004015960320100d244070003104449540d6288200d10040f0007400329a0300025500e410122841901900045200c2c420b640030211004d00d15a40c1400300d0b600c00701a0340103001604035a20600c00b2801500061514038040c1c40f000311101c40313400108080341c80d010401d50009560340c1d84010704071000c0c0546001080b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 963567958 1250 963566708 963566719
    0x18091b1a0304050f01051006031d06040809010216031a06060705150a0b120a050d02030304030801050613050603100e06060901140a0e1e0414010605070609081c020c0c 73
    0x1420305140c00c200851248040c055014007000040411004000804241c0600c600034001410156421107034024203020307010100b0709168481d0114008400e580114410b1607001b801c80361540d1b180c0031040c1d0f01000ca41c9045010794409a00034104401c1c144000398811120440d902c0e410301000340d035118006c1d0041c1c0c0b00f20700401c29100407640002c1e0404407d0201045818591550b01c040c038000c100912840d50800d400c008010b010140104014400c0c501a1054070b840c600e04400881c0c0300c0c401210001d010500c0100140841e0070410003501480c100506d40070b01040c4c031500040d140d50422102c48116018440e41801800c89000d4071680046080d143d0300d040200c01400178000844074140c040580e4004100c07602c0980c8113072040140000c020349008009101071600007408c524541d86c03a802223041c100354113100c0b00a5071000b41220101c1c1c2d50075080011030b40c5c42c400600501c01080e00c9804092280b2101c0004800c100b01c2c51608a02006946480264480f4182140111401e2194 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 963569208 1250 963567958 963568013
    0x80c0607120f030f0906021b192a0b0306030115081b0a05150403061a09060909070306150918080f1c02040603020c1603032003041809 59
    0xc0d848100507842031019051400e504051500b04a0081000c500c400c042d060515084805100c419802416128444c00043c129884280d0b4650707540e00d10600c606170580d06884162000c51001c02e07113111000c41e440305101c008040001c4c49480041b045c0c2094900c51000810302180c0d2609206102d40e010010240559151074075540369154200f220407040041d200f50090707542c9a5a2101c0200a4200202030003005070741001c1004080d04540802c54a141c038083c001412a0500340c4141c4010307100411420503580c0307500901081d4a000740000042d0300c07805c10044001261800390403000c000825030401c1c810700c1c2c541400c0546803850880030b08201c1c0281d140b00460654000c8510000d0428801d990710040710705c0050301c10346294400c0e400244003060100d15550b254005015a8040740102c4003111801400c00c0240e011a100017004500111500e503101c0c082c0611440039006100c0540741000d555402c181d0f100e601140740440c04036a00d190300c004002001c0c110b1480c0c00c1c0306000382e0016 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 963570458 1250 963569208 963569213
    0x203030324100f0f270f060806060a030c02010e0f061e011401140d060b0702090109140a111201180e03030903030c090a030204020d0605030f1b04020a02120c07080c0607 74
    0x10103078207049882045656121340e0354480c00340c4200c00942411142c040110384580312200001c299074021903550f0719031050009031a0384615850f6003d4540100703501d1901600c10380a400034241c0c02e0070310007595240c2400c000340d504107100b0ba44012a90700050007251800301c15003da650140e04030326a0a001900045c0076040341003401044112081c2000707a0b0142d00400141c24902915550307218035030a080340030540341241805481414420b50311000e840e42c0791008842076a400c01c0c89070204443c2c2d00e00007140c401090b000400201195826589000c0305c0031134200031031409811400c0404020107042100c1c02c124800c01c500500c481020f5070860415640c41790302c03444007821036207400e40003050b400400e9035410704000c000d40d4014011540c030020511080003801c0c0c03134030030305200b80100c502c0200c0806005c0b6032a14102c11401c8602c12504e501c41c00c000081d0802c00a40c02107105400c1140035940c000e00040074002c070f0060042041625010126140140ca515040e0254006001a400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 963571708 1250 963570458 963570467
    0xb130c0804060b1216050301050703090f0b0a0e0d050c101401120501111801030c050f0913020714031b011a04051b030c090f060f0304021c020303032410 67
    0x1040342e800071000c40c20071020400a04101680700d054010343c0038048800f034031810a1003080b011520b0540c001d001581c6c2d40b00d000e80454034048005480716040c2030380d140000340401e0300c045c0e0055a8041c0029021140125103103032500307951044011030710009030703044034080800c008201c0c031400c124207002090300401102c8403a88184144000f0960549075a02041020b41210300103801c1ca00580ba15803070194281503000e01d90841c89404680b45c0000207041a12810445644605890460385442030b07200c10b100b01000940b05881104c2d509011600010701580220960040c5c45002907854280702001342030a19040948140180e14000040118551038880d0400c10070040f0b5000070f56684220a00b1589035401d1451903070050004200810140b0004c00f4100444043d10072800f81c181e600d007444114480c488800c0311510041c00018014544a0b50301c03841502c030542d81c0c84680c01281d010910750b41080d5482c0203204028141e851038030306901d14200341180d080341c044101c2d0703464520207003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 963572958 1250 963571708 963571711
    0x9060315080c090a0e01141e01060f0c050114070903021801050a1205010f0e03041505040b090409050a0501140f0610120f0b0d06090c0501090303021506150d0b130c08 73
    0x3070190b0803c8001800c8041c850b80511755000f800002400b041d0f085009000d4802011a44040c00424000d041003400e140800301505a43c0c09407250009284100c5041c1d41941ba00340040316159207c0c0c900300c0308405070100c2d0301e000300c0c2a40c6600f004a81548104400c2d42e10708032040c8030b102e0155004000c00c1d55003884110484500d402922100c0c1c00600b0300c0d5000d000340b189621110b42c00d200c03004d99400e90001c000c200701c80704070003410410b10400a04880921a03803007020900d801c244098402e0f40740690095038014410001ca44107000f560341d42e5030075180160f100303a441e4807540c810000c2c401d00444e4004d41c011401c4410070300c1c10145c054054524001b00c135105c40703d0741d501e090012080302d6590000c8170241c00180001c202000c2c5140650207402e0200046460f03030404840080c00d94081c00350441965407603005002e20308403031039507040c0c0d00000624403580512202283e9401c0d1020030010414081035141c0420307860500028081c480c1400a04000a43e00d88000701d00000c0d401200706 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 963574208 1250 963572958 963572983
    0x50a0c06020708160b01030b060a0e2e06050304051b0d060923010e071208030403050a0201060504061205070f0b0d15080610080f060f070318120906031508 68
    0x5842d0100c41c2800120380c051030407601c284610650240303041c01082e000d054101da1180c012142c85513202c206008a4441501c9465003008008010807507110000c04400a001001c242c1c50100955820065941070400c0e8014404100e001040c001445814841428003140540d040c2c040d424510340452003604a2080103042d071503403641c281c2e0030417010505807605c9090b40300c008a100c0070220003d83c001c0085001d0040184502d1070b0001c0c00c102d401c95413400045e041044581595240d03181034515a02c40031902003103540e250004921540c1d14030036034018210045c00c11104a081c1d1030031519229482c0c21030600c11404440c00c20009881200700ca890210a20010500c0d08000203a02030f11320060700103480d43d020b01c80404c55a10302031001c0c0c2e41210b8a2000301c07511600042805030f101c40c81a9490802d09104000207125503000340c0048100c1c1c1c8a00c905090344100a460303001181c0c404100a1001403660107081101d00d40c140101c030710014003c505550b42c18a00440260380e210303c240c09 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 963575458 1250 963574208 963574211
    0x9060c030f0f140f0a110705010504031202010b0306040809130615030e010b03060f0f010902090907050c0c0a080615151222080d060e04021011161e06050a0c06 70
    0x2c40c4851055200c41003202243c19000e80390403ca22600301c094100d4980400000c803000000384d445400040c2841c11101d0684131280b4007415600c0e0b10004148907a845010342d900c40941007900c1d10f08201030791087d402030100d95102c4841c0420000c0540361460840941c9050240500501103440c48144041c0800c2c140050501c030003003401400340c1035610304c5036410b00940040101012010043c180300711048009041c4d2a070b05d07030030044200e000341440c1c030b50000c5980e400074115078061001884401d82e03103402c0b1340c0315030210700020740c0d07400031030704900c00940069082c800140361a01024080c0c0001711841c25540c0324614403541c46000300605010504403d03804680d41802842c00c1c054149941280c0c00b28965040c1000481540a4601741034000d2501d1000910144280851401254010702100103044007540c221030600010b8150482d40c000c407032380d00342030042c9400f80d20010314600818034940105103c880e08810312070780c040e0301400740030041d000c4101c0e4000c242d0466164080c50 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 963576708 1250 963575458 963575477
    0xb041b0503061201050a1a1e0118150c03020609150c0f0c030705010c090902070f060b0102010605061821071a040f0305060f0a2d0b04090c0609060c030f 67
    0xd00f072900d402d070030b00155440d010a1001111013070b08207440840080103254840400c0005100c0424075142c0514400d2030254001d1100d5840359039420720a45c1c08100740b080d680c1d11030350303855081288200c505010450a012000416405001c0e06601c21400005808114603924200c42800b100a0050b8241c000010300c11590f10450425280004c1c1000100da485d40b1462a000b8000c061203280e04000c655a03940004400c0391500841d1803503a8460036403400740c00e46035124409004071090643c150b548691010400b929500701070302001500c1d0107000a0200d4440900105030800030541d04184c413140c440a4603d0030000350101250711902d200d034500e08407030b6a107484c14022904080c0e00c24007408000024040c000500d54001c03440d8882049442d10303030107480c108850441e0300c0c88070300c520f180003602550043c60405926a03c8046804a81c8507500400141281c488003c12200b402034a2420700c100d07a4020200e0010b000d540c01c0c40f080802c0c07152009004110001290750400001d01e4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 963577958 1250 963576708 963576721
    0x120a0c0b190809210406110c0618010c02150d050a1406060a03060e0c12060f1f12090b1b0708041a1b1015120b0c0714010603060b041b0503 61
    0x80c180310220303440d415a012149144080740d000b8404c5034009940c1d441f10050250000c9044022078800403c064a45010580c0e010064002e41c40036505000130b07149610050703100e0940c1047c2854940501c0f581d902511810441144c802400c1c031140ba510b000351406ca64000b184003240c10000c101c4060391034000e0644102c0c00b03007980c1d4118190344400b04040c0000111544003402c001d10003000c80481c5541d414051100030941e08000320340c0301e0703000400300070300480122000441402600c3c2031010b1401d00c841c50015076a8016084031107121000800c4140303822250f03030000003501400b031145072050710386991805001e2801600740843c48884a100a000b03440125040c420408604d400300710042880c20307444c1c0c10429000d40c070305401c0c001c080960880d091001411380b4030110700144808100d45801c02180d074000c000c851440360801031034001c295280074842c08440e4800010620354110710740b0006a0390178490060003107041c66600058003040c148a014100d00342d00d040c5480c0d66a2a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 963579208 1250 963577958 963577963
    0xc0a030c021c060203061e22060905090d0e01021f0506040912081f030b220807080a12020f0304020d1b0801052e09020711120a0c0b190809 61
    0x34a2040c0184000002c41002c1024507006144039001c2110b0034064100010880b0b000321601c4200554081c0ba003840c5914120800300c0c0180100b209144000380e810b13210500c04088a40540f0f03651107a500c1403000d549250b50292181d000c0202c20f02c0540b80d5142c0b68020314aa88034149000c80501e81c032000050840d0f00d55500c01410203421094072040c0e00ea10b1074000e401503100361100d00070b109152060b8003204102d8140401120b61002007045036958032146034040a0007044c8081c0c1c500101d02441c00461140d9015041c1540030750300a03680c940092038060480d0f101e00705018410750060002d803170f07500d4200b4241c036030103601981c0350300074100745150500403007002d54004884030318203010202c0d41000c15480140303c2c044000011000b400394403001c00c0700740c0c45895030808030000040280b000d028203030040c10b4154810600a40399003940c9000418013030040f480d00e2042d0f840b0191b44010300941c008130740010501c3c20801490880000d800d00b240d041d01c04035010500a204012505843c0d08 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 963580458 1250 963579208 963579229
    0xd05072a02100504050d030e180403080406060605031e0907031b0e0a06030f080a1215030c080c0a0312050c060711010b040c0f032a020d0f03020a0f0804020d060507030c0210020c0a030c02 82
    0x303540d03e00c030a0f0b12b000c2c60054000031083d10141c030306134542400861000d029104a9001c0c3c221001c00d92a003851a980290511030000d091400e140210340300000004d98031156002188281501c8281c00341c00c114002c0e0440d840101f00400050400710104003003102201031340740c00ca400c00c1c076030380c0ea480200c00c00340c8941c82c21103070581c80646409403600070010780b81890800d803882644060011940c8070002980c030007030060713151303800110414100300290200195191170036490605604040514110340d003007400885610010031411030007040e040000384220750200d407040350200410071080c0001051480c4042070441030683e110148c1c400303000140100c6104007640c0099010003d01140700940b00d05200c03070b01c83d01040300d800320b00b50258000d000f40c4442e94810382d07548800c4520000c04a030002006841643c20170b0100070168003003000ca008152040c042e070b0310b0102d044c2422410007498004044450001103106106d0000c00341d0011030303104610360b01407400a410311054000103101464 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 963581708 1250 963580458 963580489
    0x109020906092214190b1602100c17160c1709041b0e090f0a0207020f03011404030f050f030a0507110307030c1b0b0d05072a02100504050d030e 63
    0x2401c3c0300100400056120180d8a00c0404007580c04c1c0034650710000f04600e401c01070007040d4403051400074a1081c2d01d44d04200e4080014030490764400980105902101c0103d624400000c7c5410480c089100301a20145d130406465000900140c48080e802000300b40e0000000b00345042e01714000c002c0d120100251004060000c0040001100710903084201c15409440440071825610200c1418900a90042e1240c004a640298a6a00c2c00c0841000358404c0c2002c0f80d01c480e4607811446a901c0911411010881120344019241418100a0060728400c8040820400b00301302c824004a40a010399801c181100c40110341a1110803054407405c100f1100c00c0302d54400407581d2002d041d40801d0407401d047c0a007001c0b03142c01d01c2d200d1001200c410075010701d21110804001c091200d80103a4400da51189051030401101420012081c40c040d1110340e070090710f51000801302e01540f4103050424000500c5d400c18614240c0b030000816680f2540c2540941404984010043c8986844801805015 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 963582958 1250 963581708 963581761
    0xb0a0b01091a03160201051b0d0f0e0606090606090109140a170d080601031104180905011e24050910030b0c0307020114090606060d090b0a1d010902090609 68
    0x19402c0c1540c405504101c0d511100d0b201414010b4241c180180300c1c0074060240c04a066169a03460b440e4080c407980902c450f8000d05503100900d2100340c1c600e110b82c2c0a00ca140d0340141c42503040c09010002c0260000e000184900b170108050380726a03030000d207200122500340001401c4c490500300020414400303a0300c40f5484d80140a900240800301140c10b45648095840d40c03100ba0311403000440444000000188400408020070302006080f40020961000211008908040d491390341d02c0c02e560554406a082c0d0741d80c8003016240742868002c186201c0150940582c82c06020305a09842c0d290b540b0070b00b4003698a850206003101c9100340100007841d00809058172074240041c908840f580112252801546042400b9080309202e600d0b6500603403100f03006011036143c060400055500c01141e511035660b941600800040301c8000c0c480c400d00341c0f504006000745040b0107a0400c0e800c899419402a403414910900583d6540c100341d030040da090b900c02120703598a01207102441310021811681340f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 963584208 1250 963582958 963582989
    0x3151e0b0d021207180b250605010503010b12031605030f0a081b13090b04141302041409101e090f03140405130b220f0501060c0b0a0b0109 61
    0x10841c2d8000f020b00d6600070b2003071001035481000840305c9007014444401d00750082502089000391810140c905098020102c251240c00281200d80e840214501200c0c416200c0004010a1400707200e4400300d44020713586404043d4282c402700341c40f8860340d00c51070416001c40f1280c400f030260030425220502003460000390340760710503c3d02400a03242120005084ac4041210303010b00001d4006490482d40109000546181072a030800040c0001154054109a03a4010a45400321890308903004103019080c3c12207041e4180144002c1d5030810100711b044110180078002001000182000c07050f4948400241e921144200a1a91017505d030b03c600d500c6091100c80b40c2031141c01029108034910a45800307244108244090615000310b2042991007103080c910102400c9168001c50348079080100307030074440345900c451444080c000309000c0900c5a503981683c1101d5003207109803805405c4504007403810404603505d10150315001031166541c2601e82c60304001690150101901a101101080405 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 963585458 1250 963584208 963584227
    0x40e2d040507090c05070b07110d200d0918090602030403050a0f0e100c1406010816080105010b0403030507020a0302040509012909040b0403120c05090306060103151e0b 74
    0x800a0540d0140c940380900000080c02444074413942546070380c03549885040c0f09590b243c100465030010584428040c03681c4171402c03070040510104241c965261251181900c00042c01102581c070303200003680560200c2550061990800700e9081200e000d5070310803410030000d10304100a000031100051846002000340420150090003400c2113010a58400c03801c001480000c0341e0a80301d900c00d0503045400002c40c00d034000c0c403a4102c14081030007060900c48408500c07684511b00300f0264001c0c4120342080300c4030790748124880c000100801d8480c00030301088d410001a031540c0c0c8140d00c001030501c0400036080c42103441d4000c00e000110380041c001c201900d000ca2100340030744029a490441c42c0080000644d130040c1900304400b414402902080329030f07865030348210890001800640c140500e9050043c0f02a0080c0904d41299907030b59220b03900d40340da0100745480c14901500c010b040c507040c1401c01680104051440c0c04448c02d1141d40d2140c1428a031000c0011040f035081b41221307580000b0040305 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 963586708 1250 963585458 963585541
    0x60302030103110a150309050f06010602070503060c1c05090a0606060e1207081015240f080f04020f04020c030d090b18030a08040c15030c180803040e 66
    0x40728010251218149000d20404c071021405002d4807040c0c01240444907a8603200c2d90010403036034031070310446410500480034a0714003034003680100010b178403540d024496800d0500000c2d030001544170401d418094290350341c1d0b10110b40c1803440300e0403030340e2200001d84c5600c00300039640c00280c20020030068a074035004028059024031000c58000c01003a10244038541e80094400704482e881005400502c51380901080600700b40c0020021191165002207004042402111542e403a02c0303510302111408100040c0c030050030300011401344071039201040b4070001c1c075130721340340e8056411036224004000540000d80280120542c2c10030342c0c48041121076200000ba842030019600500300c80e0302569400f40030625030221460595800c1e0402d1004c0881580282000d682041c46589404c0c0f4035511082d402807811001c81d400380002c0d03212000d0404607074102080b0b08169450fa01191582401d103240c480e03403445184215110508140c4c000740c88003205414006124907e0b45070b1a008041d040400305 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 963587958 1250 963586708 963586711
    0x206030a0c1d06030a02090607080307030204180524030f0d1206080a0c06031109040c0c030801140604050d0501020c070821071707022209031403010303050f130801020406030203 78
    0x4a1400d801110b422900b42c2d269540c1d4000c010b080c01e203590b039866040e00c06508041506034000c0d00c140211070001e01d0300c002640c8549015500103071a145040e9043c2c1c101c0d55102ca0484000d407408084c080d62003401c52800ca0a01c1c00c8900b400381480c0d004000c41e1601104540b001903030b01441600c80d0f4103c1c0c0c0056415a403000500c024825a51100c051079140e840c4107100070039442002c1c1040004500a802411500c2500b10186042c5000b17500440d00750703218500f1020000e540d20342c02ca1b04064104080030301410080301d000903001154008542c244c03145006480c842c1100c159588104503094040b00c0e20310354444141d0b41c0d1959a40c030003c1d82c0318204040565803540008401e8400c4d8005026560084e400410020031805082d050410681c040402660010301c1207024a0320140c0c007040d00c1c9403401100c08009845199400c0c014111006090f00c41a1004104010004246d01406442c1103505440415981d400c612200c18403100700390303119038015400480d00048841c0c26601a6 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 963589208 1250 963587958 963587981
    0x91201020d0c180f06080a09020303040306091b050303030a0f0e0f2a01021e151f0501110a06020c1513030305220615031703071e1704030c0206030a 65
    0x20030b1015102c0e03020800303c0d9640c0501400903900c880308203e018400c2c810f49410a844010000f1146599000700307007998802e400c04d0720368580b034070300d0171040001c1c1003503100d035090f013040540d0340d507500340303030003c0d4503440041d103520507154494209219104256100c0117801030410101d0b11412040b50b5a0307501d03404280540d42609012659810080b400040c8001c0d5100b8140e010b08018600300d0019007042c1a01000ba01003449041d0340b0031030600c00138407040c0c081c051741c5d0741007003400d0b44004000c03ca8000c941c00c40d038100b010008040b1103894001035000c1c0328661090b8003680301d0040305140c1d40380c5030141a03102004000700d03040c003500c50402911148190702075541030110b544d41c0c24201da0720030800805941c1602c11a40010007003007142d0300030022407000420b00d824083ea25217400c0d82030020801d455005031000010f0000e45270300304800e4500a50444000d1400290142019191501c40041303c0000c85501c4001404c1622031101c41c1d1050ba4010195900c0c1d0400408041c001c2041c0044c2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 963590458 1250 963589208 963589217
    0xa050a390914040f020d0f06020c0c040609020a120504080910080a150806060409050c10030209040b0406061d0d060504140705010212040621020f0712091802091201020d0c 75
    0x204402d545600d8460f980120201c2c80540e026801d10100500048040e65240c80c116003401c000750050005040c1c0340c40200050841516940c00c1000b2515542d010100c840d20401080040075000051030002411031280000d40d41d03214200340794070340315400a00d6440842080207804403038001f01e9103030003828400e2080040110402c05400101a680280c1c00b00f41d00203030002e4001e00d415046415007a2081d010f0364150440840450a0a801040c2c041d020a4011842c418242000e1042c9035207480200c0d0305000782440c183c806400a00700020306c2d80d603c0020305602030076071035113042050300561203101044180742c83e08000d0a4010140400800da025135171001842d50320011303041d0168181d000741c02d032900303107421025243c8114884210a51128441141080c1c0c0001d1010b1f02d0013111000f070703440d0390780080d00d000307440c00c2d0304601c030a000e00040e14403d01444001440c0703a41500005803005a403881002c000039103882d000c40e201c5c90650300002d00c80300e010255812268015010761074 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 963591708 1250 963590458 963590471
    0x30b060a0e0109330503210f1b0a03050d0507080f0a0f091505220309050d081c1d012901051204081207020a050a3909 52
    0x100000c00d2900d00c681204414988010b215a00c00c41d80703d2001ca0100412801c0b02c1d0f11103c1c50103041c00030810008a5050255030308010b141000d00515840d0f04034034840c034000700d00c132113080300190103191201348062a020412200d141c0840d038640201e112110221990704039145070007841c552080e0421840c0720f00305004600b0441c028890307d030050100440504444d40c404071124014105984030b03c2c00152201c6000020510202140b0840d0404180209480c07a00250002801e5440350303510a00708030607081030340400d1303110103c00c05031441140c500840d81d5543c00c000c1c40c43e02500418032001d2040b000050081d00c240d03803207401030000140080d2101100f110140d4220340c04cc50030300e1060b440d1090160b40c40b070000c0010841d0700205040c024100b0540309001c0140700703001c440480300f60000040207811541204041684442c5a100800c0d106455a0ba0f0b00d403601040f40b4002d0038000c14034940c9000343d1042c00c64141c4001c00840a030f040014110303c0340c50078905403240200d050700d0050f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 963592958 1250 963591708 963591721
    0x20403061a0108150609150a030608060f010b0a09150c030e0a0b07020d0804030b0403021011040b2a0f0304050f042c0c04020403060b090718060c051606020304030b 72
    0x903080c1207050503191142c05954581c000c0b140d00381803462550340000c00b00200112a603c0c09000f41c0100c440028541c0c03103200d103880c0036084070915045544d49a010348100810782c500b00b860340341555000c2c11141d0715070020100545580d5010b80020880550440340c41036000ea200070851507050080d9248034078582003006205030100c15005a0011a03820490000907041105400103854071500c071041c94540e680d200c50b100007105942c214010f0b08840b400c4041170600d070141c0040d029044004502d454031340340440401d84142c02400f080c8026641d041400a142c5440c8140300c5241601992118030080901c00d40300e5000f4041c0720b11a6910314403014243c01c040c42290345132802c070b1100f4066010a1446c000401c1703244850703541d0500c90f00040042d26180c50010b0001035111b4000403807900034000c204039410070010480b504100d180024030100058034200709048404600f0036000d0030405e4200207003080504001c291500c0c03e078007400a0915070010080040300c0c0a10400f050a07103400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 963594208 1250 963592958 963592991
    0x1a090c070c0f141513170105010f050d060f0603320601141228110301140112080d02030f0610050906070206030c0d0615020d0c200102030d05090102040306 68
    0x180114103c1c140c0030b45140401e81441810890500c60a5001c58104036600044a0407404540c004648500c02001880300240f03090080f04c2c0981500c140b61300030b240c00e120105254400036580030300f00070313202c00d4841d9894449502c088055038200c02c8901c0c0d110382050407007540652802e100c040300c50001680c00c141040106906042c2c55484030400581045041003290303154080303240351070a0284c803003030000a00303810f40c9289400003c00103648480a141c20580c0700d051b1110b0030305020342d040945100b07000d0070b8586da041c1900e40002d08000034602d40d0410b80072038010400c001003810700c004140031600c1c50701a02c40e4410107089400d111100c100f414119224003c640160b508034000344020f000602e000d1001c0c590080a080456042540e5002e010054070034583c4003180b003001600401054a0b414080f601400e1090700301001d40e511299034215030761746001c50050104092020380a0f040c0c1c03003070003210f4035154441000d01140c14007040c001d000303501a20007110014030f8000301d514900030a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 963595458 1250 963594208 963594239
    0xd120f020a020310020f040b0406090608070305191a061812070f06031d011b032f030a180308010f05101215080a0305270d03031a090c070c 61
    0x9405020005800c4006901071b40100704c1e2a021020280400701c0c4a4805601400007032007266505075040c3d182080240c4201c00c0a0709042c10107052004002c2c0c64000c00e5081001030400520008644504151a042092002207901e600c908002882c82c4110071824401160220441b44056234410801c9000daa807585480355074138605030b44004001440c043e030310410300a4558041c0c0d5150700701118001c0d00f142d00c010310412104400030402c030111585480344c0c102e490780a0800c420030700c8002000702c0000352401c0607000700640000c0002d4a0090580102d000f82c90707907041c1c24a07080c140d441c010301145824082d960300e8000c040c0c0c0001382d900d480d040c0400841010f841e40c004031003040b0700d54401b520f03e8001240410342c6c040c4001502039810450b01f0324040c0070b503980a485a03801d06550b841c1e201d0b03801d454164542680f0f00e42005954400700c0a401e50350604000808180942c00c00034000ea150400c0c83d4000c0d8003001700b2070f4080501e001050340e1880341d0054200306e510f030300c00742000881 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 963596708 1250 963595458 963595463
    0x306010e0c03100e0f0406060902040b0706090c0905011706072604170a02010b0a050a050f100e0406060906030c02071a070c030b1303090f060203270d120f020a 70
    0x42100218480c68000c000540c0c010720f085500300c412a4803011861350b140c0084e200c0082d0010440c04010a10006201754030140140084c103501c4c15250500d40ca825028645010b0300305541c80114508000036001d20b4001040305010a00040d81d60324921000c40010141010042c0600800a0402031050b005050440c0701c109850312500b100c540c0e8400e41000c010000c440b03808644032070b28407407034100d4080e1074070075003560000c00c00802081c01d01030302d20b000d60300a6020701a0107100b800196110000703208031090985100d403040b08422001c4407010880c0144c150010300c5c0220110740c035940a10304c50140d0310a03071400d0000b0040307040304a0380d0b019507106803c00002c03841034220440d8013460062504d24003501100310045e4483d02c5d4099095000e541d1520380c031358104a001e0405400c024204c004103180031070515000d2404070013945921516622040c400440d00400c402da00d290b105140c3c00c28409800c14030030380041c0c94400001d0f002c80c52810040b9800200485101c2c2c40007400100c0b042e03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 963597958 1250 963596708 963596729
    0x302061302060f030a0b0414070e091b031f0e011406160b181b030705010804030e06031e0702010b01110a1106030924010306050c0a02060402191a090f030601 69
    0x2015643d10250b035410140c21210619150408450b003030b543c41c0180c15482440198554032410300c03041c050f003461116401d2501a804840400c404a17003001c603645400208003a51680d283c0d45c250916040c0d44120615402509501c0350100d980e01c041c2d96854140d44511442014646c01316041102d035008840c1900360440020180b0f4001981f40010181c00001201c2c01107510907144814604080c1e2080c0304040340c503446040100b1903d0f081148500130325085c2014400703414103480090040b869050351718003545002001c1212540565010003a04680c1110202107042c0b4860080c00b030030700301880500043c041c040e592064a0042006458a54080701c0d50f40d20007002c1e01840096040204011b0290144401450004050340f030366680901c0c0d0a100d0b1180c540c110b25041c400c0b160041c01100300c005050003080c03000341c0c00080e0b1079041901100c10702500c0b4a4149a84828150754000009145502c03a0b002c0300c05550002400c12004200c80c405940088002030554a03c000d106600c02c54 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 963599208 1250 963597958 963597967
    0x1507110a020d080f04090209040b010f0516030207180c080105010203041d0a0b090711151302010e041104080a05121201030b040623060f01020c0105030c0a020f19030206130206 77
    0x1890400062030041d88a1180c032401c0c4400c00c000c084054000740c1c801e01c0c1b003540006410219280134800c03464540c1003400c04c20031441d41d801c030003409802112000000002c0240303450050600800c004c90080ca80c4403101588041e01e00c2c0c132a0042c1060911140100c1e0100c1d0012803a98008010b4805503004c2c9290384600d10704108540501c404080c110800c0155500217090640c0c81e400241072281d0ac00f500d8807041d074429420380300d24000201c00c240d00380d030002e00141b0044010310600d50803c41e409103003002c00c40d501080058004c240d91014440900c00004000070b00c9100440d040c24024068410b80f91031180076903242140344a412034100e003032010170f070048c00020302d0400151741080c0039074030000754001341c4ca5000d1841544140001d668010001c1005500e1801c582120701051080c07026042300400c0b200042c000f4080684114110000810500202e40c400c1001c0c034100c0c041d1008480180400340e030702408000c000030303068005020f20000110300c030840f070003c400160303400742403549007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 963600458 1250 963599208 963599213
    0x13050606240d0908070c05030d0c050a02100e0d0308090c04150608090a2411070218090a0b011d0c0406050301030f0309120321140a051302060c1507110a 67
    0x80e41c1c00b0b0b000101806548410341c001080c08000038000b058424800f02c2c0801d814002007601d080100012401008006c1500c03d001840114000c10800e6041d14444c50001c0c200c817003910a0002940401e42104c84041d15500f403540c071245850140f02404156114000305000b0300064a0840004004825014504000040c4500311a030380c4220b401d0b081d500d0003038403139407485030714990461b0070401d146c0c5818144038400d0f0035201d0655804014801c0320300d8200103074042112034040c01e05000840e00c482000948000c020f109000344180c0c005104004d56840b0344040c1c2825512142d03e0a40e201a400014840f219500485069a02603280e40d81103030f2a5648040c40f145150104508000d192a80003d80c101303003154004480d0301c02d845d000e482c0c401016a5040c0c41c0c01d243c2e003d20801d414a02c41c001e000078020f02c0e858022a0260340441d50340e9882188112102a80310b000b900040c0001d8a048040d03000300348069000320140c482c1d50a6203402004a43c10305c4000c00c2100356401c00d2010000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 963601708 1250 963600458 963600529
    0x1d190e0604170f030f0f060d110915030a08070605060109030201020a1e1e03170105010e06070f1a072d0f1205090705032a060705011413050606 63
    0x1045401e041403e107040401c8403010a00e0f0010b86520000d98082000d100070885200001ca034407480640e0b08200b00d10051300d601220f28010b03007010b4041c40107034000c5201800360403800d604071076001d0212102d030300180ca8030748000d903c013aa040e2069071030318011684541c451240042100e4050340144000803040e02c90907036600b15803094880c83c0c060207507074070300203508429603000c07109054038100b02440301d50030b01a15402c0640010401131110324010711190f80c04c010072008954064800d16103441c1e15180075446580c409201411110080440c003404803030100c800c0c0d101e520251b030358102d19550780c1082c0084900c1c8108401090049021640700319205101c0c2e0400010585014000100c3c5a84020111103090740d20440c3c0f500802000d1249040410050f95036880300d042c0000403010400c0c035980410104000148944070005949040c000250028000000c00c05525900e41c00c00b101d81500d071380902442120540181030014003140b9100c0313544100b070035000c59100344210340c1524600 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 963602958 1250 963601708 963601733
    0x2f12060105100c063303080d18080d0b01090b070305091309061e06321f03020d0b1c020123160c050603101505041d190e0604 55
    0x402c002c4031000c0c0b02180c140d0080a140c02107128000a40200c241700030f5100080c491030b080050f1403c4034080000405d40012242e40d100074160016011507200801000700c12441030182ca41e203404241c04000082c80e600086109000b42c8411039495916603417600769020f00c50029021440621100e60681002005140c0048044900061244c0ea5580300c1c81114560000001204000103010244c207403070b8811403001d0400b00c2c0d1004540d034090040558507040d0b501c00f00f80c40803180b0310043e03401e8035885101718940c140d08070000c45001029400078001e41020b48010060750820543d4110740c10b000c2d03040d600b07101807014100280e088580040d95020000144086225811040c40f0785040540c0043c11110380c680991301c98041f813604000313a000209412803072140c0020001d100141c0d06420240c4200ca00501c105010800d0360350043d00d807805598003140c00b100b200c8003034540c0c0d00c054802285c4034000d440140480d4441c0d65900b18112040440030b228550302c17000215001c1101c050b0200f = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 963604208 1250 963602958 963602989
    0xf0d0203040513020702060705070602010f1a27070507020f100807080c0906040305240709170712060b01020601060e06120a06080d0809070e07050403080d092f12060105 74
    0x54034091712603001c50401e5002d03000c142e0740e5070481c00f000e01108d5170a0151050880480070184005508000b07040c00380c1c0030050206115485185078040d4007101240724050350303510500103e000d071800a0000e8070a40c0800740c101d1142d5100080405075103002030001340302d000170f5654040035586414003584c4105000d071010140844c1030051440039500c02c0001c0000d075120340d001d090b59403255588210010f0200c0a03000e81d0440b240b0801c41102e920065600840e403041b80d200c809588000502800c0a6441d040b4141d594010343c4140b080c040580c000756600e080030307401c0f1445070781e035100e0444841000001c2e041d0710074804c00801c03407901c59010b0415000800141c0005141e0b41c1c1d50101c614090048100001080c00b04d000c0044030031050205000070a000d001d00340d404c4c035201e44020221f100c0d0b804024010903000c100c4805285680c0d02c00d401643d848030300b20020404c0449000719000c002045441c86000a11039145103003000000301884c010400000c00c01079003060100301c01e904081020 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 963605458 1250 963604208 963604211
    0xa110705190504050a1b0f05040e040b071106070e1002070510030623010e06161401020d1a0a060c02130906020403060f020a090302010305091501170f0d0203040513 72
    0x40361669405848050308a080d0740000141c0d490320302444151040181035201e1381e450410b0000f000c4084001154219546d460100d1013241c0380501694140a90380003503586044042c104800c10802a503407078010300003900d498103200c0c084900355556407012030b203203400540000954602810030b0340c1c103d510f0303030024010360711819119408241001c08400f0000006601c4040400c400710254076844950b440c002115903039019800000307044030005084032401144009904003407401a41d280034401c0d035000a06031600d60007228200e01175007003080c254040741e2404900c480c00480381803400c1c41c0ca00000d02018403c1d40381003410703940e070607c10b4003c0e82c004d02043d062555480d1548210300c10103114800c01600d440c11400d060040302c410603229000c0368410018100b400360004d82200403280e0901e808140380d5143e02e4038a00700380c603502c0380d04424490100085603a205090400408581270700c125200302e02082a605d03610400c0040b01d4016800400040c0710f942080e060250190118650 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 963606708 1250 963605458 963605473
    0xc05060d1d0105010611030a210f050412030f06030515151201060e0109020a0c1b081006092703030e1f150e06031515060415140f0a11 59
    0x39084808110781007410165990340050281c29001040301841510b2200194145240d1010160510155920103050500f11079050f50084010383c0041250b407a80600c240715504040c68000d4058060312482408203090601039100207009102e003000b00d903004401001414243d004440c80c134140505900d61580480c0b19060840e01c0d0740446614000d030b9040001095454400c4040781c540041c0c00c2150030794010003101104680c80503007103d41030741000650385540798054420151143d1580031400b54010b029800884040c1580b200c2c5c1141e001101c00e000740c01c501e416495048441d8108419450040c0b1080c1c0c0101e8801c1c0c2c000300281e24044100d6210310243c170860148001010905450151130b01d002e140314a0800b0781c040000c0181e1441c8070b40a0030160002a11856030351300d002c4d03116a58800091134401202c56108115034041c2c003803561035884000080034030998005180111708111000a0034207444401c0780c80046011060505111803404112081001c1803e522000d210381e10 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 963607958 1250 963606708 963606731
    0x10090509031e0304050f060705250c06122a0f0311070b0403020f0109110f0607080705060103020a0b0702100c02061201090e01110712211103070e0d0c05060d 69
    0x40c2c800418251084000380c4071310303162070001c3c600b0000d800782c019640c100c1000c1c09045508202942ea1038810940b82c81d00c0c0003991079101040000300500030301030552801c030018810307030880c00b5450742c103401d03200c14055425500c150032425071311040500b100e0800e644e00e140d0114400d184a0000602a03d008076070050b03210020301c20b0307410888c0b081e50303a6520790b0240002c0640400a096214581d0030007401410317900d03150780c0060421103204600400d04002d10a0305940c9007401c4400c0c40b580810f0721501d80e401810819603602c070901007240960340c0202d000c10032100300001d4405031940104030414000e41510304842044045c081240c101e803042c050040d40070311074103009019116904c00028032108441102d405d48110315907034000d4407010400c4501103080d05107418140e490505108a800082c0e4030b200c100e000300f15200020b203d2600c1e81504c0e488079204000d50040c401992862000c400e5201008401d40c0f420304005c007240d100c01d808004c0d50074410050001041d41c1e080c0082c4894040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 963609208 1250 963607958 963607987
    0x90612040302010b10020d0c12050424090605070f021c02090f070f111e240a11040e040201080c13060801030b090a15050c04030f060f060506031009050903 68
    0x191030407030250f51509101c411a05103841141940302182c402011700c1c4070009005810b01400c424050311207948614030400035405070f400c41d4010700e002200041c07251049c802c00c8000041c0e404904000649c240400592644124207440e02103410110b4859225942e508102c100400440c44c1d4132102d0300d014240000d030ba02c2c0c540483c840c0d0741c055200c08142c42c00000c001d142c0c0b40304104940074809250428800510001100004000d4081c921080e010780805502c0c50610070b510140b050490f403e400881010001c241c850041c10b01030003d06c54040646140c00e9540514003581c810034548800041c05584070300800b64002041c580741c0342c603003041950700580107090b40c0c0101d4041050200100104902001f0840c3d04c52924070192200407625039859500910380c03202c08900319100d201158045e80c403038007114001e680c00100110001c8540c5000400340c860801031082c44c901d810400036071401c00b2011a40300f4651209000c0020781840618002090b01600410f00c81c84188001640701e81030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 963610458 1250 963609208 963609211
    0xc10060e0705160c0b130906081f09020a030807061b0f05130302120c0901050628050d050f01140409021c0305190503091207200103020d11031b0c0d0302090612 70
    0x21740c1d4220307514460300c028050003903020b9001401c07003031400404028101300425840b51520841c2500c0d0904192506110054424100048e600102445c0d0010412920000402d0035901c180e00a120300f05000030060303024950740001c0408101c034034132141c40052042c1d0041020061048483c1b640035140d4000c6100312007145410340745503015506105107441d10f0703410140140000c4484915116401000d88034510458150001e4821002d11301c2d00450b00510a0700c0c61040181030802c41d6241c51401c800c0f81c01c4e02840fa440303480174070441c0c03d00a405e0501640c6090340c0c01030103c0707242e810040a110381c070601d403040607000c029040c0003810803103640114000044156684058880c14500807040c1414040d004245900d1010015180010903d0f00e8019440b801c001018118054600c0142e000c0d10400c148502424503000c00c0b0a82242120040e500071080340904030403905003240c485905105420168100b80d012080410b51180310350010412031001900b41400c201140e2400c6020040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 963611708 1250 963610458 963610469
    0x60308041802032205071e15020607020a0b060411040f0918050604030302091507060e0d0320090307050d06140c040e0a090c050d05030c10060e0705160c 67
    0x400040c108070603001070100000e640c008603011851803c2c0785503101044030030707403200142c4154131180c03840901400f440140d0080558000d00f02c410b10180580003024079a5002d20082c42280085148000c0d10000e911413080345a50001c3c00e12200d2511404075242c0003e181541c03098031019601080d95040010340001c020000c0d808084a017088103810503200561a88150109810070342408540001100c503082030301030400580c1d90402d440421190521104050740035030002a44800700030b019440f00d081c00401400391050402d007500d085095030500306400501d4010320500b03920010549008180c0020f0007004c840c2817aa4410200ba4030030f010610a84900b6034801507030b42210070000f840e40c1d01120301c8075401d18041c141442016540300c090030f188001a0340f402040204004800c51f1005050010104804551503282c91a540d500c8190303054803600409520700ca40c0c0c6041c1c01010180c400c4941003592070b9a81d1b040840b41604460030380004411503041600c013040c01886900c01400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 963612958 1250 963611708 963611723
    0x90402150a020307051207020303180d020a14030f0d021005130f050d080a091203050613150303180303020c1002032802150702100f0f020307051308010506011b150603 73
    0x1c2e0405d113050410b448003803100110b04001000051754040b0841e8035010202161a4130340200303001184030321a40c4403000307410001840010540d150250107050f60b0300400c804841c0b0134a41281d107130351100d00929992015074001c10031000d500c00590061540507400255074080d801341d6803a500c1c1e560010b00800d0b90207800180842c042c0942c00b40c180359001010f41c1082c05940415a100758100a214641d0750030155144003040140e65000d011401902e00400b042c04040c00398002080b07818041d01c421008605104c0105400e0804c0200a2007180d402d030300075000340300014081c801c5204441c40684114002001403030a0041031300480404101c24108003e14a580000003900d04113501007071700c81008000301000340350340e470001ea0704681c040360301c5010038028106400d030405086c00e59441e0000324008002c02c20215401000b8054008121805081c040d950703a510764203c54040e03070001d00040c070303054400d450491890301d03c0c10200d01c6012650a00101e20080a08550a03604202d8244 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 963614208 1250 963612958 963612967
    0x209010801290a020115230a0e0f31110102061b0a03110412060b180f040c120f141614030c0a090e1603020f090402150a0203 55
    0x6580c001409030151a48280b0304034810380303004900c8602d003468059030103031000000c0c010500600c01e40000034081e860a030000320003600d801601741c249000008210140040c00c64000d02e91601e42001011600146420710b92900c0398101d00c008a0030007000c0030b074124084100307102a000300d03000c1c17044104001c640a0100468038a048035581d2000746001d07045620201c00c0c0001d11720007421040244a5401c2c0f0950360300c0b0001020760250070b0700c0200d410714210200d0b0000b84520904141c3c08844e03c240343c20032501113560100800c0d0001259111603600c1003c0001d0488c85402e020103402034010358014800315603410b1000c03100c510004d41107414800111010f02002030305401080450186400340020000a18070405840c2c200e2080c00491a165114083e41c4d480510020000d0304000d080351040c0c54032610f504c8050500281c40050500c1000c00c0c3c2c12a020070890102e05580d0b00500312104010014100404132502900a0342c6c40100c40c2c0326103d2040d0480d00611082216401541e200c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 963615458 1250 963614208 963614227
    0x60b0f0d0f050123061905060409062903010b0f16050c01030f020c0c0105030a020d0c021b04061511070906080f0c0d030f231803010c0f1d0f0306040602 67
    0x35258191000f00582026684000400180d01360007540041c00b5100500c280411842d282d80101c5290311040d00100005004030341c041080e0400d0094402a4074101c0c00c40c003118085000e00e0b201c01c10382d20f030f0190040c001844424110401802e8203114000780305d04282000b040388220402c1c041007150300d41d000d00911551542c040c003c0d105189a000821804d0124110b81c0c0ca03110703202140c4681c1004000400140f02d980c090341500d07415802c540302003060b404c441601960b140082c4060700e1f8082c12450188009240c6806000c2c00d8400951510074008280e440c00d030342c011101c00c8641c0c41c0d40281140803601c1c003180d100d0400284400c000500884040d000258204080803d03218000c04403440c444000c42e4010742450700d80302c0b0a241c11580d004044074031000c041002c980a5001d000c00068030551a21480801d07100c0f601c007203000700b06034840c4400564040c040100d40001062445000701d40407000449141700c00c080107080d604e440944000042c1c14664110380858855601140f000007 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 963616708 1250 963615458 963615461
    0x3200a05010213081e07090921090f0b0c0c0409080c0a08090a08070b22230108010602010b010801060f110a0c030618050307062705010c020f0307030c060b0f0d0f0501 73
    0x460b03031704000c0f0b4a4900705111552503d070f480b60b00034015a251602122801c000f044a181c3c080e0f00306518403034a82d494040001040700c04e6511414150004003440892560360100c05c4900002c1100c00624024104506110140501002c01d445189007481a40382000c0240507100f485445001d0166031410030f4410041c1140c4550001e4000e540040d100380036024400044402d940d508144070403490032024180602072205030054070a2514059061154840f01400101c0c012000d8848640780d85c0c842c0822400c0328000d0a00e50300040174007004101c0b43d0300036040c9400d88003031860408280181b07d00d40c3e0340b400d00b4047c421205000146000c1041c401e2a100d15140390320b000450649001003612801d58034041ea10010344442d541d840000428008203140009000c2e07140249903104246052082c02405225a02005409120201100c1081c04401c0311760700d540c16140e030700007907000b0b84440d0b00501050034125049685400c030082035968092505003002c1c400c0380b0b0084c88848514090f070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 963617958 1250 963616708 963616723
    0x3051b0c0a0f0302090f10080304060207050102060a1404021002100212060411070f1b091d1e030f030c09030106150f0503010515070302010902060d090605060d03200a0501021308 78
    0x120711042550b01480142d592480582d000101d65224141c1ca1301e90303180c3c40c494074030030764001107491000150020b8440e4004c208442210400d03001d44540f0703a912a110350964030340c51a0014034694103400603005140a0713051a10505c070b903104032104140071164002c00c0703034008a085045100800200301d2305190601414101c1d200c403040d1542021042d40e02c1001c0c10101e6080204048a04a043c116009500320b80000414032540148215030308140c1c2028190051081c94031140690407854103900c5994a1426a0240781c0c1d009524200c0c100f0800c4030f85800150250a5411040180c0c0d0210382c0c0034000c01c8054466a20200041c001c000d90140c8485000400942400700c180010441a51411b10011002c070003c800035035601380d40d00c0d080740149111a0001e50009012441030504110799004106080c400c0f0300800490301c90340704118400c5110f1400400058400518041a420f101407040041e0341c0403007182c2641120b03a94a41c00d82c1c00640f01c96000a02810042000b480d041110b030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 963619208 1250 963617958 963617969
    0xb04020c0109380c07020a1202040f09080f070f021e01121b0e010c0611210402030c0609180403051207031506110a0b0c04050108012304050403051b0c0a 67
    0x282601507143c12200d400d4100b4201850200e41110005140544e4040c204c0d411198020035401502e5114014482c2000300040f00340c0c025850710880d6402004103105040038260842185400c2901d8110b05070605c0c0d1003004115004481c1031004401038444000303a0f10b42401442040c460000ca510004045610884403141aa400c6c482c60302c1e05283d403180c030000081141d01e4064004003104006880300b098101c0000c044a1400c0c544014402185014058500b4070000003040a20031460040302d000c020303203020750f06402450100d107052030070100914000401030301c1d800c401407105070070310a11102240c3c00d0703010410000314540e160303e801d800030b076021515050030000100c2203d000420b40a0601034681401080a400c140c0001c04205c10303042d0680c4020900c2191500030402e6001c0e4000341b00d90b40c01701d1140400862240c81030080d1481801c2c920104641506842c1d04110140c40080c0003039041c45420007410000741e0304058100341002184006090805495050000c6e21840e42d028 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 963620458 1250 963619208 963619253
    0x10e06060703081302150a120e030a09050405090f03220f0e07110f0a0f1205090607060c0509090a090201090806090a111504120c09090f02060d0b04020c0109 69
    0xd01c0300003a00508819088108181e16504114003440443c00100d01c101105940700c078089406000c055000c4446481507114102c00d00070000100803165483c06695410000705d54850000c4c03106d0300700f56109584c0880070508841c140c0d0700c08c04060381960b105000344009508000422088005202c0b44c010042c80e00c1c16448140501d820302040c80b01e079000d8400000c00100022101041c030040041c032010100941c103032400e407034651800701c0800348607110449a841140010540040c0100d00344e40c94005e02504092030b160306662420014800d10300d1501c2480020300400a05da280e50f48000d200b490b40321800130701980b450001500111080d407250007603074000b404110602e035000c180e200c0b58035408207814050f20302c00000079510503903491481c02d034500041400140e4140d501907207099580141c00c4420300c15112005a401d5686031407029144207039500c115401800c01d200140482c0c4550800014840302160006080c2d074418103403001d0707031780d11000c4102c00d0144035900c1c4048400b09409 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 963621708 1250 963620458 963620467
    0x30703030e01050306040623130507020a15061224060602031c0902090f0f0f01050a0302091e10150806090a150e070503150315040b0709180203010e0606 67
    0x24018025074406044904104010003c130b1890f4483d504032401500e840022100c4040c50041c0700225842c814402c1032181e0080420640080c01d44c0c4922402415281e01800c0410010340380c05603c07000c1c8001d800071240d5120700004022110303203502407120744201d40090400400307011079407068501e0345031441d115140c1902000802e8002080303940e030354844d42c84d040c981c02209560a008002d01c0901a4111105c1e00400c0722143d44401c00e40d21840c03110f21126402d49a000c3c4c0b070031014900740109a04114109018000340c5042050203a100404c50001c0c2010480c20070010380030981130300e040b540e00303070712400034070901c030340d000c0215281d414900d003031000307860400002080140060a0790b84c00390740e0788031205842400c0490f03030740251141d04010a504e0401035801052a0b0007140e48880749001280709415030718010581441024180c2c01c10121611251110940803c0c007411780c1050100141d03000a140c2d8201ca82d048242140410068403585002e0342d01510389001400244900800c11 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 963622958 1250 963621708 963621713
    0x70309060f02070614120108010e0601121220010c0f080109020f03180a020d05030405040c09081e0c04060305010902100804020a23062a070803182106070905030703 72
    0x1100002c560003880c00c54000e002c1c0c80322500389881131303200c56650094102c0c0007262310329054000c8008035070b0600455205a0340c840e40c501070903700c24002002e1021024840c805a4030885040700740d221440d510f00346400300358503002c4c00c507201d040450003c50b40150b54442069085248072f80100124a0700798a00101c90b118038140b40710003064400d20300b0400000840340c10f001c202240e1800d07405400107011507030905109560340c0180c89568030580c1481c0c54848034a01c81c40781d0a088a0f01e00c00200481e13a40b240a4102110b0018603841591044400250a954950058800543c0580000a000c0b56140107020110340c0d40700020080c0201c034001d1000686801e0309440454601d81c2c0056403400500010f10501ca2480256075881040440d0358018402c000e8406807864005012004040e04102440b9890b85c4082c400c120194100380144215005100340c2603800c2d04004000f0700c1051070780200d1006943e00b0034250405640041c04100242d500180090b02424049005050080ca580d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 963624208 1250 963622958 963622963
    0xe10060e0f1504030f0c0905010605120403030903030e190302070801020a0f0c050a0209100e0a0908090d02010905030102070503190509060307050a0c0f0321020309070b0307170c070309060f02 84
    0x4050601034000050b030101401003400a4a01a691100c0d5040c2e41c403103641044280d40c0c0580c010b03d02c00501d40800051054010000c4a8140c00040858422a074654800f03070028805a18158141610749084c1804407100340118a021080d034070320314642c1d03562414003d140c06416000320049030710400550b07410310b40000f65860b400c0c10500d4800c0395540d07941b8085041454200000b5005040341041c4500969044061000d840300340130703211829941c0d04105d1042e141203043c003601e400d4003080006450b040114450007200e0060404071034065903000442d0880e032148905559640010400c095450b088841d00d6602031064a0b000342003a8007403000680a22000d4900c005001000418110050017804410b8045400c0310312400c40030b44c181009070406212464921452440c0401d02d40340d0344451003aa030041c80b00a000f4030042d03080c0201c81d803c55001400d504244480c40c2d03480503505400d1840c4501c10328070031016a0b110040307450f010300700d44210741100d414410300d40c40c40148030307070f00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 963625458 1250 963624208 963624229
    0x1e01092a0e0109140a0b0a050f0102030903030c0c03151b0a03060b0714250e060301150611070506030702100c14070b190203070203030a020a180e10060e 67
    0x14030640d098240900220049418070740c42440c260192000006040050341d000c50704500c080080c0c1c440d10307904c00032588101e441038052142d2010a00c4001c6c40a0304000d0001d804d41a0103004032841c140402c00024919000f660030501e0303507484038194059608003441900b541d8000b44100b20542e04100c64a020b01c1a4011002c2410740300104034010b190f4401e410001c01400b04120302030713031010f080c2005c000000a0400041440c481c004580380703843c0404404402e00c00c21100c4960500b4144200909600400340010381c0c15900c620b0401c002589030038042d4000d142c140c94545d42c40d11003208841c14410181d00603442104140304101c0e003141c0100356140080008800080d4803030451000392684d20f0319107400e81c07039801d010072484e0411602441081c050b81111600e00a012260030008050703100481c3c0400041c2c0060000c565000141d4018040880143c00d0030301c6500209401c07403981e0345c0031b82d02c1070945801103c01c1c0501c0110080d41c1c04090039061401440c202132060108055040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 963626708 1250 963625458 963625493
    0xf010b10080702011103010e0f0105030f0a06110d062408060a050f0d0b0108011401050f01141e0703030b040b120c0105090d0501050901020a17010509150609090106021e0109 76
    0x34144002002d09200794400d00e4990311310750586444e56150744681d03000a40444502000200c0c01c800401c4c2443c0c0010048103164405008000060311503503407001500e080480a20321050a10000701c134150a0300076500506440801c0e10000368680b28191181c4840c9078011051055480603c2080e0300c0d0b00030074405031007054990b10b2400c1000070128801d0400001d000e0102c584800c0042882501908001d048000b00f254200080e41c1310020030001c03556218100d804104680300c0016245800c0016100b03403125440c200001110345200400f0f55403000d202107000a5a0f000406510314040c4202d43c2d54080035076001c2da0b6030300030307040e01a17403080c1004449040c0800416058165910b10b84a50301c582d0707114009001c07600302814828080e41250002300d011401c80c1c00d000c62030184504400341241d000034440391994642c4d0b042090580541ba0f072060304241c2c208a600c200d030311000301280c001c0140d41e00400c403000400400c4902c0d0320a40c0d40c0e0311800d905180c0040c0116459441200300e001 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 963627958 1250 963626708 963626717
    0xa1e0f090b0a090b1b1608010c050906070b100b070c090f021306140906160308061206061005090613171f05070302041a190e0102101a0307170f010b10 66
    0x8000da00c1c52171040181001d200500c1780041d02180e4800d1054000c0072210064001d020324a6145400d60706070041441140c2c2080e4240b090344040342c801d240040d0003200d0141c100440544039455103003079910580b0190b800c8001c0d42010032502c4141e20400352107450080c3e00714180415910f400c0d115054a22034201000072154070039004d03d10785012540b0fa824014202c45c1e031504501d818030b00c4440803c2e01900423419860010720141001c10070b07444403584c2007018184e16600c240411015000003e440300420409200c044060b40b1307143c0c01801441c02178800040354919200c080c9400d034030200c81903200364200e60030981e071081ca140f9030140c2c243d012210109281c1d0300c0d000220001c0c0103540c44000344050400e1100900780f09480207000e0303408078070b446102203040c810054890380c41030460940142d0012503400002c01c8940e2007070300c0482e18802c0300b5040448040000c1e1400007113800444440a01c2c041c21462a8030030010b5404001405000f8400d5007410b000040e041c150405500c030521 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 963629208 1250 963627958 963627967
    0x31e020f060a1e0f110c0f0c0f060d180602031806100b070b040f060606050309010f0c0804020909010906050907050a0e06010c02060c1006030b06010e090f0a020a1e0f090b0a090b 78
    0x5032140e03088550150926590b02e501c07400e07006d0300c881d5110300b80e0300205958000c105010406040c080200001006c0161880e49001116001c420041c00010200c1c40400d00000c0076000061090000354040d04244807080c036041046a001c504004c8050300704070840003402801c0001110b4541540d541a0308080e402d1003d95032810504c00101020400612152501101250310380d080405540140ba003000200301100c20741c2010300480c0c82e44294440800c42c124005001480d20302c0119922840ea4400800c5201c5150f541a040ea03030140d5010001d038100d4031080c0010b0601f403055600802800209140c030341444400a071a610040c64083d002d203500080c0701086102c10030021035600507540b0200320072030f41e13030500c0384600400f501e03141d00091030040a940c86181c0009821f020317005021880c2071640b20030014034000d42c050042d00f02804049414071403843c4074011070044001c4207450b81c80641005d064018a540e09581000680650a01c000c0c0811580f00300c2d50401d450781031801513502c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 963630458 1250 963629208 963629231
    0x6160f03020f0c100e0d03110d0504060f0c1d010305011508100e0f061224180f0703032303150406120f05100603050c0d031e020f060a1e 60
    0xa10034440024268400c2e40c0702c6044c070450719070000c040b84a003001613602900d000d8038100c003611044d40008640c0350082c02660300d5403e003a03003e280c00510416000500820030348022040d22400642900403074904080849030400b20034400d0005202441c080180350b040035001100018986050002c2000e4440040d0440c402c84820700060404100005c48516082c505020b8002d0100d5143c1c4c0070f031080750142280701d4000140c1c5030040128820204602007608001040c03002d0003000040d41c0740604081001607a000d0000340d410843e200d0240c620b440c11824082d110641c070101300309603c4445154014408080700070741e0b8210680580081e1980e0980002078080c01458020a40180712b0781710042c10410070405103e10184501d00b65900e800a4a0007882124003901c006450754120645030001c030303c0c0c0351b14142c100503c2070405048410611840e0458041503010b81c2001d64414114038121a0342001101d903c48048401400041b0910603802c90510224145d10070164540544480 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 963631708 1250 963630458 963630487
    0x102071514030103110a0b0c0309150919033005030604020f040803030421050409090f0816050f010c09260105070c030305060f0a03080a0c080304030c0506160f0302 72
    0x56100361041e0941e00c0e56140e0609107900a03c0707040903403040c451070000140440c0010241d07608101c0c828007450030490702c1014450310b42c01c00410b45078001010000c10000759034601c00d84182a28884408010a046182004c900826840b026104401d20301e00019170000d00c0c03601c071604000078640b2b19121b44443c004074000c1d00070442290080300b00403070081801c0c00004059885a1b006880c0001104c80c0302404201c282804524800010010402440508007035000202c1c20f52280c0c000250b01c0041c0e0315010400c0c0c1045894210b45551801d03103205001c420030a598090401c00000c2210111441c0040c24a00c1c981c8910070146160204241080304034442d138189840341c41e4000d0006241161000b001c03d034902004502191034000032440310305040380d180305034800281070240010b05503200c0360f045800408440040144502c00040014004406140076501c01d13200c411f60070345103140c403606001c400bc01200341500090300104100c0e508c058010900b022605006a644070300c54085807 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 963632958 1250 963631708 963631727
    0xf04170f010513030f0c080306011d0405090102130f0f030b090a0b2e080613050f0d051305012c0406051206070807050711100c0f06052401020715 64
    0x30200d500c2c140070003401803400e00885600c01d01c40c0c1e6800d9480a030f015001e0701ea0580303120001d420030405000103111540200303070000408242800341000d01a00c6800070301035590490b0840d0b50b9075000b180c080306080342600c441c1d01030803046000515850501a038400b034984184405040040d91801103071030071030184103103460260403150314007551400c442c40d16112803110b030311105508680c80300d00ca035400800111308140c4e200c2101030711a5842c2c5605038118024503e8003991103000700c11034501c185004102e0480816016203515032141d0301303c49d10301c1b5501160380c0040e041c400c903600606100e40111804002105480c0194140f48443c10b020500900c410b800c855040814282500c00070400090058458882c039510110b00342d513a00c01c1140da44c040c07003900901e50200c0d651941420300d0310a4120982914628216000c102d16480b14140c2c00d2042000b0703a1344035612003d11404c01c240700c1c13030310102181100000d00005142c0c00003d60310035840c4100340d00c0200100104402601c03445014 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 963634208 1250 963632958 963632983
    0xe15040b18010c09170309010c0b0405030c07180b0d0b0a0e032502100f020d0302030a1803030906060506040f031e0f0b09060906010302130c020703020406060c06110f0417 75
    0x801c06014a100003500031030700c90003102010040515101c100b8000041147e10b0450180c0d81c3d0407400045a4680d121010040d00440d0760303000510017826159420442c54004281c00660520541c1d40520310310104d80354000d00347d004650080103180403884405099800800c0b00314006044101003220600f1070241e200c6140700790314100010480003c440d414602154003c81c4c8100381d62a003040180d422445d12000b09d000f41c3c00c034441c0f801c881d41c020340c05035074800c5004002007030b6440309120701415a015881c00b1004642e9403205502441040d11441014240640c0c40610381410011170414108151000428949034000c542e1680314841d0149002560301c112a11b01140f00351401c162350400844100c0c105200d05000204003002c0040d02c0c80c100ca4004d80201d900000211f0910043c040a0142c0c03c06e5205040b40003005031510320a58000700071035912060521103074541641907079108112124070841c10b12046c01421040d03011913003103d0690041c82100b8128403007540c01c101840c03408 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 963635458 1250 963634208 963634211
    0x1602010207050406060315090c2f0105010e250e0411040803070c0314150a05070c0c08031e1305040e1006151707080402310608010e15040b1801 63
    0x501d10382c05400c144103030707900205c0c041f512a880d1840303135049440350440c1c200025000250600c06914004050a90122204004e80c03c00483d035501c90030b40303c00f030307000c10004d0220000b0400b40c05210020702d009040c2000c42c041080500082c000c02e81c112400d441c0b4441d45d581d00c244080342c25010200c030020200070064035100c00c90b9040c40307003a0481c9840142c43c0c43c0d080c1403910000000c0410500c1040030040203208160b112404d080c002050006c080d4000c0c088011181c002140c0c0d40502c1c14014103609004603503500d00c0091142e403550480d8001c40051030148084070060801241040984006070b40004c4c194000b10110391800030004170f10007500f03241100c086510ba4400111507012591031320f9551100307030600b81d00003041504075940800540c0e510042001854446040791100f00c08942c440408009040d11384528515501d13041d1205039a00c0c000c1203502028041e0030076840406015160000080c61071410002c40100000c01c00d090107800540040d400103c0e501801044400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 963636708 1250 963635458 963635471
    0x60c0f10050106020c10080c090a0302220c0c050312090111070c0608010501170f0603030409020c060610090317090319060b0a0b03090307030530010e090a0816020102070504 76
    0x8400c001440d081c015600140140b468812150804806680c2060300700d40c1c0d05455070f514520956025000300f1540c9621805001000025981e21120000c0c03240da00e1459820790045000001c0c201c07001c40f480d54082c454900d0750000031901c0441510803a041c0003807139254640c2c3e000071090040c6180d031113115a02a0104076802441803d04650054403407a45502d00c0c82d0f40c072000107654032031610100c1d0714141d050b500040c0d510200031154035045a00507048038101901d501d080405d03601315410300032890b802402080307000c0ca41a46440049400b40c00c20821b8903055860314184c08a032104650b60348600010300c1103003920200501050594200b078108140c1d8076514140002c1c042c0c0e180400d20a951868021400000d0a812203014050b07500083d803504034a581c003691190440d0600d00203c1c00d8420404542d00840c14609640800c440c0e04201258100f001e80983c5503009000a02103a1120103608002002001101e16000c04135101100c1071600c1c2c40100d10b080c101e600065049401c150 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 963637958 1250 963636708 963636733
    0x10207050d08010603060801060f0605090d0b0118050f06090408130506030f01080d080c1b07051513060e030304061d04090b01080d110d0c140f06040308160e060c0f 72
    0x14110b038180c80c0700303a5080c02610b81c0c81a91a00b84c0b509e50107001070b9000c2c3d80030200b0a66000320001c0406410180102c04d000c402a00c4803482c05009a000a44a14170311407024106080c52241030380c048014480d0344118206900802c0024100400c014078411000800a218601604008008110040c501070780c902c0c050507010590442803044041a00ca003d01814180b80039480a0f40701d0000703404968140700d1807030b020651540d180c180245030341c0680d540114503a1100146407154540703005189598031004591040007000951190b410003000b521101c6650340c0c0401203d0844011b46040250505940050070b0034810b6a01200d51051402020104022869031468100c60300b0200b581e1501104401c180c5130503042c0101005250801c5241c542c1d11030003201d2006006004030600142d289101c9140781c03804460f071118169580c042c0c020801007561100c00d640d4410400322081c440700320021805401c0301c524054441c46000302007a007420a2404002101040c150310b802c0b01c1d4500200c1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 963639208 1250 963637958 963637967
    0x230109020a030614031f060521060907060815060d180c0602030703050316050918010312030911090c2502182202041d01051906050d14010207050d 64
    0x9210303400100b0704002000914082d003100c21050240050003034030b21030a06006c94512542c00c204030080c83c07583c9003408126a10ba03a40c9081c040085040202120290301e0100d61812100924034686944400d40500810764000d0210741c2041c100f003c0703001c945080c00001035160150003001c0100600e8404ad0000d6018901c0210003d540107807240d6019130741703c02c0200c1c0c49124018016020502c1000413a00b05160344080907100c245c0c034680182049903840002d610101020026011222150014414000a00321114402520f07040410002402d955410f112804103400b492060094400203598105264221407540303603d041030021b406040c03064400405a2201c05034060550070118032003c031030b17032038215001d82028200d000f050301e410300f00e00d0051005034000300c1c1c0080d15107544000f034aa41c0d0481d201181400c4001080c2460409200f1031050030035032000100c14100002000b254035020140c82c21143c01070005425134003010031182c0603229468004200d88100c0200100d6a6840b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 963640458 1250 963639208 963639217
    0xc100c23070b01090b0d0308100f030507080601050402071a070207030c080f06090a0302061b040312120e010c08220b0a06061d030d0f1e050c0d05030907060323010902 73
    0xb18503500080e41c0342c2c01160300301c03801070b4a001e0304100c15404001c0441e015032045a407041c0c0c001d10a441035500e17039241c0c00c10380c4500d6004461541c8202010300c1030050a011035805040196000c50a105e207a40711002d08140d01e00d50340e040c1020040c040f84c1e21501c24403181e0051030300100301c070102c00e584e412102e5852500031607448031070080d1030105450000110395000060780650083c5695190b200022004010311011004000010007000002074a5111100702c05209502c88003207084481c155402514902e0100c0304240e494406c21400d525000040281c002c900e1824901c1c0c1a11112034441e034090351400c001e03203004400010403081d0a00d0b9084070f815190b0f15900c4502c61140d0b0f940554884d0242c04080d640b64000d00b00003012148612440d9004c86000e1038128a8500050f8018141e00c40c40d950b035100003000003d80c211512010843d0500e031100a103070440c0fa52414104a40d16004c0c41d000c0d00c010940c403440004d182c409119450300d40e4548803a4506032550b03440d00041d000f54007 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 963641708 1250 963640458 963640463
    0x210110f07080c040504330e0304060906180b0c12070602090406170307030503063c0d20030a080a03050106031401180b041823030c100c2307 62
    0x1032100900d4903013410b0040c01d0260780d000b001c15410b00d00880d0f207501c5404c0108401c1840580d6404200728900b0907020708000511050701640e036850030040010880900c0c0d80003102800b404000d180010800c0d05400011a1000502c041e201c1104036803550520010b03868170050300c00042600e0090241c5680180140781e0304480030010140e48241151607003070480040003094000303114160200780110011607014600504419070ba14400b04402e41c04203007040181a0384010007005562212107800071103038580101c0702090031903542d03940c202c0050440104030300c2c1da14804045901d9518100840001c2541c0400c10988489900d2401001808244a41c600103401c0c2002001000d240e259034a0580e030020080b828598610000d01004e4204094101c0d0000c2d6503c0b2103100281038107240940303481c03152000310080c5032001424038150b441001c517441a5007080140884402c40000c0c3d01010f809119004500118078a2050b540c50704444600d8a0079008010314000c0070843c180100721091 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 963642958 1250 963641708 963641713
    0x10f0c1e0b010f060f0203040605030c0913020d050705161b05030d02030315010e0108060409021207080c1e0315131209050112110306041104170309011b0f0210110f0708 74
    0x1a5254021a20b01c5c19400d10900136820412040c008603114100950f80440203491240c034000c0702704003151401841003000c1100660104103070002c1c40681c0600760300034040385041d50401031079400206955070900e000408030f01081442d0030620001403510002440024155502e280210304040d40303170f85c41101c50305000400508245002c0d03000d01e04a034121101030b51100c04558641e02480000c1c209154166442044491041400c0303004200c0a0003a000540c060b281c2c0181003c1401405807160755030001c4903405000146454500040e442c00c4044031104840e46a1603459112103042035108010323041600b03180f802081c480d044520f0400b155004c1c0d84c2c5060801e04110b650084071000020340ba115107041000c152246095000903061010903038210345410b580c0c0c1e090b060544c98801c080500c81d040441c14020968100d9841c0074072100462022000c0445c40c2d4810380c4005003064001d00c10034010103800350940c03044921401c01100f100489400c002d07142d0f00c450303039030150380b18441c00e62 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 963644208 1250 963642958 963642989
    0x110316080906010f140102010207020a080313270902011b260c1b0f1207030b0603030403080a030f06170705030d050a05071e0b0403030b0306070e010f0c1e0b01 70
    0x1e00c000200741e41240c0c00c01d1a662889424040d10001c0d1050406000d0304647d000d000000150782d44003110710080c07034204021995096400310f2a489029558030420200a80c2102282c0103600c1c01040301d03030f5903212603000400030881d1005a0b20b0016250900140e07449400c0c60354104076080c002105800d8204c292481401c00c00c0401703804510401250900642101c2600702c511140066428a040001046501d200c4010000f281103444941261a2554003041c010014407144401c5e0a8112200360040d40c94142191204009481002182d101300340e82c130303802000d001081e41c0c086070250642e41c40410111030740880180d954003c41c060103200b40241005040d80f10b0040044034000076643d150103081100d2070300d554080c0d0302c0388100900e10781260100080010704294035144118425140004d00456030000e062030880c1c014103920900540c9039040d0002d03a040ba482c0e0000000d281381c00b070401400c0e490800916003c3c0c514007559030200b8420241081444550340e41030f41d20305480003104 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 963645458 1250 963644208 963644221
    0x1504050a02031512033007020d0207210f0303090302011104380a09060e010905211203190b0306060105070b090f0a2010120b0411031608 60
    0x202c0c442903c00c16082e50b20304201c07000394100300e111041d841216070240c07420aa030309140030b0300084201c550600300a0000a82c607840411800c5a03039000750540c030050811b01c020f218060350301c032094014000580180c0a0071031105038081002e241481d44544108040c80f118039025000c0c1841034001c602550030079800040b00c0c1d0031034040e41c0c05c4a20415174200300c540805001040340382a013603402d0204070070015980f00314580c1c40007031032802007650340c00c035060b403070010001d000900c102e11403410011820400c01075540d80c501c101e00307903c000e450140c000904401c50039140000b046031602084401200708001c0b0807a001c00c2100c402080b07901130010b80b00150405d030711840c00300c0f203050100d14280410008071b0605d50b40b20b54850900b0080355040b41c8500d0690b403030810301c80c00403108014556140c0710003080c900b402d48551007040d5000b10300c00c207079014098030750211450303ca002160b5500601c10155103d410100e07590407101c140ca9a00c0c240110140d070700d00040780c4010b02291110000c1210b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 963646708 1250 963645458 963645461
    0x3040524130b0c101a010c030215090c03100c02060f190903030b0109080a0b131401050f190b0a090c09030206031f080703110d1a070f0305010f0b0f0307090e1504050a 73
    0x140d0121000e07442d0912007010045d1110201c07d10264214815568060560382549607540c2c004d220480003800b455541404052030032040716107218000b8100459818401c0c0c0004245800281d4004400707415030301c8502d45c141c03902e05214455070a505100c004414941c06074464400802d0a98603c0d69258461091964a0120381001031805500c2c000250000e80c00c01c0421403003c0c80b03215070415207411190510b003902e10542d00c80c8100c85082090001c2208801300110300554840000d00c600c10300f003800903000714502e100d181d0b0030704d0b1203010320780c0c000d8418007201024641c020310302074503030406c00c482e0170044c0c50740c1c01c504012010400c00400c06c0d410005044080b039600c04c0c40c04446c80c00e2542170104078005010300b102c3d010034ac8402c480018440241e0f0501c00d4010703590b010b07001510800020203449040e480302d0741c0c80100740002e12020707002e4012103031800240001c0c41d0366070b01c400908440003a030350341c0000c0d2800104c04c184401e95000c00d04a00b40d5200440e400d0206444490a040 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 963647958 1250 963646708 963646721
    0x23010f0501051f02070b030a140103120806100807080429040203010b0303042607091d0d1b0f080405090408041a0a080402040f090b190e03040524130b0c10 68
    0x409613019845c20008450514000e640c0086c1000010400001c1c503100b07a80300700780a800484071400a43d04004070f05901c00c64032503122a0440740780c040e1015011010300f0410006d00a07108020090001034180f01201088070030301c510540d03c0d80401d010b00300060b8000702c2c0c02d1390224840e50801034441c03070914000041c0c8003030355503d111442d9107a1046001e4001d07a444140328042c00c0c0512000058100b80c00e220780d00c00044e500c1c20100d10100f50702c0d00c0d1070620f4410389805e001c0c400c2c5c0125060041c0810520503414030340c85001402c07200e040d401c00090600980d440141e105501034104420001d0500181045500d04050071030512041d400d88001e5010f03500300000001e00c602c1c0004c0140c5425001200300728046500000c43d0303071094480d418215800c50740b003188001080b07c1000f84907400d2103000c680884920195080601740400152840c4401003003a2a50098101c184818142c1500700d54500c105032a40021050b600c054286c10340d0806500a00035024003900da03021101c6070701852 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 963649208 1250 963647958 963648019
    0x7030c1212050a02070e01030b04420906060f0f1a0901030c0c061a03100204080604060b03251401030203070918140114030606010f080423010f050105 66
    0x1802a4045150300715800c2c0c0000c1d0b150f104520480a000542c0e82d44d03400064060740c0501c0d4000180d20301400d090841000100a0701c50020079041220b1005000d99000f0801c0c80159510290510034000400701030510400007814980c68403130001155611848581c0071038514401d03000280b9600c1162101021044105a5006c901000f10042541c0300e68001d03010201070f42403210714000140c5078501251921014000c00e40301d00c90701c0541500d01000100306070090114198900380c282840b07152100c0300980f0050205483d21600105664141301414507406114403a040c2e028403600c01c0120340d40d01d0310803010a5445408155150b52190003113a105480c5510389000c2a403401c1b9003503101c0d02d10146017040f2076944190b1548020360041d0410300904100c03040341d0190b0b440c1d400701030415501604d41814482d500f03022050481d00580301c194440d41180349643d640c18180b41100b24104406d92103c8070307501c0c19034101d4070345a00d903200d541641d07801e031080c40720f82020480f00007507400000c030b00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 963650458 1250 963649208 963649223
    0x4020f03150609061206070c0519050717030c0a06054303020f0c070f082d0c06030901020a0206152b0204090c060e090f160c050f07030c12 61
    0x2c600342480e65081e504120040c0c8088013481c1c04105d0182400c106403001000240309018000600508100300240c1c14103246807103040d00f1803545c4043c0d90f0a002d00ca04481c2d00c140d4450217200740300a0040c0d0b4001010003090741c640004620b45800103200849440c2a00c4143da40940d401a402c007240c21181100c0030103101c4c5642160024014080e9100550010140c0800844401e80b149030064001d80d10f1040080001900b01203c030b00b5046403540204071503520108003040e41e4090168102036000703101000050000800445030300307008402c0381d802d800080c00801d0060640055000702005d050903400c1d114030b40c89821240d410a0b05044070300d54402c8945034040e4243e1440b419860035008820001c1c11888015030215090303503070b019005e46550f4004078081001c19040503c0000d050001c440b0b003445850080c465101c0100d000d07206003030f2203100b031040c80c020b03601032039041602d950020100c03a2103500e80c1c050356585e02c14a000c11503000046503000209005c00301501c030340003548800d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 963651708 1250 963650458 963650461
    0x61710060516170c060a1107080703020705040c050403020f0d20010315080102031902090d03080402011b050705210309091009060303050a0813020d06022a030304020f0315 75
    0x50403900e9401500c40194084040c10402c000a25680c1c01c9000c0c40c00c2d4030880603110f0600c0b07080141001e01c020040150281451910071018142c5c100701c030542d40d40702040b00d03100d0601d0300b070492600882d43c111603001031402240c440b1240d002006841164070031103400ca407e182d07120a0040c030418801c00100304140c00c4840400030f9194007100c2d40500c40c103140014412009513a2039440d001030740e004000c80c0e503002092108030314800c101310f0f03400a4006000c0d4030344074140001c1218520011405810880c161011804580c0700d01849a41d02460811410b0000721b10b00382951944e845201d8640f1444500c0d01406240c07140a03000c801344145180654100441c82c021f11111450042c00d00002c0400b06002151a801e584280005140a030743c400c1c0e02e800900801400080c2d01405404001c0c4111168600683c0c961030700d840125071105c009616090455040203040c90600c03c82d032440d0940b02c1e149000720b40004090f5200780d000b120310521068009043c15220703c0100881c0d501d0004000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 963652958 1250 963651708 963651719
    0x190306050f03030c150c0f19080f2503020405121e0705060f071403160b1825090c0e0a0b0304020312070203120a030c020d090f140604030c0f061710 65
    0x30415405489514202c0c6080200130b02c00c411544820001910780c00300c0c1c98003064239584490000c0c4d1016948010601c0c1d4208034454043c0404031001914000c601d000d14800500d201e03030143c40007010060412096644044035094407000c004803075214079500300d00c103104d804000141100403140003600d401e140084040880000341d100c1d03c0d003520050410a05086212000c0000302036825100707160b013000802515000e1003210001d8208000703445c4440c00b08400b4000483c003120016400c041c142d1912440c14807141d02c0340459800325010528088405a8054101e90400441082154003e07200c544813000d03a10035010507903010750154003030034440f100010728a0040019900080846002d010f0002c04003500e60b00036155000026114503444540703e0301080304541c01e800f40e00b010240b41c0d0504a80290300c0c40700384500090140900011a80380e05c80404580c0a1600b02644500158031000640d0481200c0d100d03202c002204514400c1e1181c040c3c100850203110300e100c1d140c403a1890031 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 963654208 1250 963652958 963652993
    0x20405061b121216090e070809010e0f07080c091605132718050c0d0f0f051c050f03161725020712080f190306050f03030c 54
    0x107500c20a514030a60345034440110042028000c540c2008203902118500702665000d560401599481401700d8120280501416070300215400b008a03d0301d00040e42e6900a040c2c0502614014544036015a01184401d528003146140640c6c0020080b00c00b64400041400a9200102d640e8105c20111006c0e40030b62510030350090101000b85202d0408071030b101c152440940c1001440340901880074680d81d40005e0305805103a065100400c2f5100701c44c0d0003502c445031104961034005100d4404074440c40e00300000c01604600054000c8018510100e0700d242c02552001c68801780202c200c01070140c482e80900c40c100b02c400e090840c01d83c103030441d218010703000381102804640b10700307119490300f030020f20004c400000c500c07407e100041e070070907844001d00065800744480c0440e411900040024881c18415805248005510201c3c0035a2607a00c1807850886001d2240002c03800045c1c50743c0e030740320f07268190441c400341d900c21106480c00480d4107040680d07900c105940400c030380d00f060b48072002e04d0046 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 963655458 1250 963654208 963654247
    0xa0b0108300f0c150901060306231b0d180209011707061227060c052701030905060405010b011b1505060f0a1e0906030503032d091f02040506 62
    0x303002225400c901002141603028000c81760031050340e650305400c10920000307001d00d1842e40088040c11001104422809031710712001819052491000550601d9031306000040307503074003580c54004000c042c12070740b800d41011551141c1a4030070b9600000100b01900701401066a000e2240000c1030f00c9803500d00705072a0404007054120f859a03480d030602c4620242c07070029810003144155803c001c9101c4d4501882114881a00b4000308641072200c1041a42e0429680040c2000701c48205480c13002c910040b4081c155180c00140310340540028442000415082441b4941d401d0700d60a1541ea010b0268120301d0305000f4014181452408a60641c500c4c0da9010343e40140010f0074400c4045088400700301c54a545500204120f00e042c10b40415580407070081c000544440c19003801140e1035511050350b03a0102802c0d01c04440d20141a209040c100000301e1541c00c3e030f624030950444d107000d41c1402d40720200361a1400040a84543c85110340041e0f1003200c060300d00041c00b05003030000070103099108103117 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 963656708 1250 963655458 963655477
    0xa0c060b01090e040305030a0e0105090c090a0f11030703050601140d150b2b0b01022109031c110c010914030102070b180f0f030a0e030a0b0108300f 65
    0x49002c008102c000c0e030010b44a00c20340c000e80302c841d075a0500002c2041162606403209505074940400c0c40600d000c0400c114000c548100ca10120716140c480340a0024484807450209072442c4c4120144055030000245100700d40e030341c80030092540c03907000543d0002d0b103800c103814480208100d801c0100850f980001c2466040d000844000d980348c004e107541d5944a6000714568280807a0041c00440c07020001e440080e2500e58140f00303442203000080d5460300510850610700b01d00082c0000da803410003081e42d840e40703070040860395445800c516511151000011480c00914420f80e0110f81d40400191081c014a040c0c0d6500c0a103450801482d114680d101042d542c195001c000300c00202d10080109401194000d04c01d0203601c502c80e02e607502d001400c0540007080c1c1c004c041188524000803003520015546401e140c40030f1501600000e080049020009284902c6200045882d52001940084510380701d603e6143d40c461a0200741440044080d02d0305480d1340800030010b00c00314180c050320b03c140 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 963657958 1250 963656708 963656717
    0x60518010b07121b030822020303370503041211060403361403121801110d02010504060f1107020402090607020d11030d090605090f010905060d1506050a0c060b01 71
    0xd4180440800c03c4c02c100b00f80c000402c1d07601070240d40042e481c10340c50800c48440c40e00d44081d51660100e920307400307606c800c100d0341400031030f429040300d0800d5043d00003000740e0401503c4240850001801a07042a1000d4400c903a0301a41124524010b64844c1d07141581d0742e006202c40d0b0b0312a074040340d01e42210f0f50f8103101054000c060448102c402d002c0040d50185c800c03140c8051030b00304106003c15010380025135100b6408807040030400c083c42c00c1115040030002c10180503180441d00180c414401840c0f200125100d44002d07c0c1d001c07603040d80014042c0d40302d450309010b0005082d50007015140c054030380c3d00412030104507110051610780d0003000da405020f420503060030200c0c0c0004e01090301180d801e890940e2400320150040c0b400707102c000c2d030481c0f131030a0055000741883c0005165001e1458258001c0103c24001061030703001e58080c1005007801840716640d04820980100604070390852141090908030f00465054080c0f0183d4442800f00ea4440c0500921342c1c42d0b06010381a2400c1450522 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 963659208 1250 963657958 963657977
    0xc120c0d0b09151909230109260301031205070c0312080615090d1509030f02010c020313140111070b07030207050306221a0a140906010e130503090303070501060518010b0712 76
    0x41c06160340c590103400341c100001081c0e40f003412700c0d02c01480100403000321595200b200001c0b020030401500e056035001550002e03100c3c40d07104180e44ad8810441702401c040b0300c230b2500004000b00e00d0000d0801c01400e82e54031032151128414481044861481802d01c0b40c800d0022000e00c1c10b00880c0c5498440c040d0300d41d0700c0c000d8100c82c00d0a0403100020b0b003c3c2c001074451111908550b8090240d00502802d92004615004002488010450f00c1d40100c01c42c208020040c14456849840010300396007800b41990b1500350381c2c1c111040d6590041c40f00b1005805094030020b01480d000c43e00720700c203000c90703540840100f5103c8078007444120108800c540081b084525801140840c05103280303c2d0011400000d48921030303c0c221010400c00821620742039000e000144050f682c440c1181d5001443e4840c0503c0f00c0c0b03802d1800604600840100d135805100220700c130b0081c03200c150042c03002c035001900c0b260f021100c890160703a11940c00b40940308a403c2c0c00c1018400090300c2c44400c1d00c185007245000c0145 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 963660458 1250 963659208 963659243
    0x301140a0b07210503040809040b010314012601060e0a1d1209040b060c0a020108100302221103070921020907090e0c04080c120c0d0b09151909 63
    0xea41141c802540c840345010511a2501281c14000c003d2460a00f4032508510b0690758188683c410b103807026000b84d458286a41035640a034010f41e0420104040440c010b42c1c659140b00320710011004804c003030070a010005084203006200e1281034810054005280340e490410804c0601801c4c000742c904103522842c81c0c04d03114001e000703000203a130001c06803695a4003e5070820040c2c0b610340b46000e1103141c1c00c10103003070381400004082a2a13542070030134595550b2000400311a40742146c0c8081d40008100f02091030700b184c01141c86200c60a180b40810120019501c1445c281c04116042804112400400d1044028110a48618500119600c28499180d9001c182c4c008020b84041e40400e0800c0002d015421030346407a00d80c0b00498810b01400d00d031a00308041d9890113940303003450164422103a00466035a0910924035940000b410b551401e80b12880c4c1100d8ac5801101c1c41c8003140510010219010a4015054000c80c08200f110300034456a114020080c010710a046401c2075080c41400709 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 963661708 1250 963660458 963660479
    0xa1a04082a100f0c020105160f050d2a0501151404060605131707080102072a051302030a14010824010b03040f03050705061503010c090b0301140a 64
    0x850044000520010036000180640074210001070144a142448406242ca0364040518204000d040c0f070500b50011840c00160307428401c2840704002c011040e80000103100704884420003c51050341240c0d0004081c00303080740c03481d1181c145140b03c5030600d07030701504e0f80103004620408103004000024208012944040c41038405501645a1040710800c0c5000c07031626101c0c002c020425414050303d0031000c40846c501011850050703109480140c101c0068a501c01c01c0404080c2030500d000315551060350800c0c01403c0b803012000100381c4420450080b80050101060084610141055194010300c12841c000307500020700b07940801c1d9403035140342030902c01001031600800804010304249240080e000700c040030345540c1c103140010744ea03004109003500c18044a03400394000b6404511445145000c0301c282c41407000180142c030882041c0320b0309803080922108243c90440080001140001e0192001d4283d41305650303d08205000403c4010f41c03110300b40c0d01e20351004180140c059241c010906 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 963662958 1250 963661708 963661723
    0xf03100608060a14040e03070c0902120a0209010c0809040e0d0906120213120c0b0d1506020606030a0b15090c040905180d12091a04020306010b07020a1a0408 69
    0x550002446020084941c201c50501d400c4441660700d58055410625964401040603068900070713a903411003510040024415225141e0344400140001e0ba600c01c2c40c81d01079045121022089581c500c0403071b5640c0e6043c801c54112000684504040040545692800b90048481250003035150a50700310104030034048005001016102c80d0000b03410403030018030300103d414100320100d10420018413810200c85c01c54080340c14070650039214038024504a50060381640c0540300d8143c0100304100402525000a0500d86441d2034a1220f40d64402003241c0d6220107690142e010303082002c2d04008151241e0400343c1c480c4168520b0600920301201040c0342c44000c07506100240c0010409002c0404140079840e0020856003901c511524001c02081c1c4034003800c180c010038410b01403d4011811a243c011a808503000000040c15442c1c0c9414040035201c1150124440d0190a002280301e4502a00340c41510790040c003a800342c20305100414201c200440002081d505080c8000034080b50100310304d1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 963664208 1250 963662958 963662971
    0xc06020c06090d0504060c0b0901230702100203060d1502040b04090906060504060509010909150513020306010b16020d0212010207120e010e010f051612020a1703040f030c080f03 78
    0x34401842d001442d02d042400100303c0d542046420001004156480801c4400d803503000000604191920b14445004050044944d10350b2252065604035031040381e00d03600d108250703e40948010180d100f031140120700c03084a045902c140c494020501054000160b0208030f08600e9005141c162180d003c0000d541265100503403058a600c040300030000e460084400400056600380310075420100040c0c80c10b070f0140200c524560f41d80c600d800603c041c100a45c80c0d0040040e02c2003200d07084c0039043c0c030b21004504c0b4042e4060b101e05400010f00a50320b400711040b8140c11620b403410040300e40d08000d40000840700603a80281c03140d00c100015a02840140001485441140c900c0c5083e400e010b04502c0781e6001240c14450300511507017580c0d810860b812601900c2d841c0156036901c1c00000c401e80020740798006000011040e185110147e000a00351a0040c01100c0001d03514240356404112880100c0780281241c0a006041700000d01500012800c0c44c41021f8180c180b4000b80c0c201d40f0950422900c5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 963665458 1250 963664208 963664213
    0x70f12330f0b0f03120301031227080d1107151101050106030b180c181f050c070816270f060501090801050610080714130806070f17070c06020c 63
    0xd03000343c41c243c0e081c1006000c060300900b410f2034500c2c0c4240d4082c08140300c0036102c11410b1510b00a610312400c03808043c15580245501043c864010400c501c104501170001140b203100001c1003c5c41c028804940c1c214480401801000d0400d0111102403030540c0c070102c180301010600c1c40096030203000d00360103014942c0d4000b0f502e0908404004250f42140d0b450840c4a40182c14084080000f40c01c4545130340e000050307040c3d10120740010403a2900c60401440c150f200500800da402c961090080c82d403d21204c040301e034059156007681e500d81c1c034070f804983d18010000000300040c08011186255600c0021100e42c0291045c4032498141e03001d1145006001c0d030f45400030700c01980c01c44102c1000e015000c008000d145000808160000d02c401d003084240648600003405240c1f0511915006a00207510b15840314000000200085658002c800381c82c09858000340315980304000b8101440b2080c0d5880002c110100740c035024620b0f008c0d00c44c1040003101c2c2d03015404070b01980010310f802d0050800 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 963666708 1250 963665458 963665471
    0x606120c0904061805091213030204380a05011d19080f01020c010f18110f0618100c1a1510181e0b09130509070f12330f 53
    0xf01c034103203042e2010710281d6040c1400402c0103a00504020009d8950582e0000b40601702d92b080480c17052a82c45070451300f20103a14800154049060024203003040c150380407080701d42c883d4019280b1400d01c1c0080c202c05c00e441b8098032814a4504c2080c200c0e030900a54200c1c40707603100c0701c41c141001c4205c1e025990301da40001d215400d5440074401c201e45000082000c0003451350240e114030303c1c49500040605050092880400d0656a80020b0600d0070402403e00b0fa80740c05a0388a19602030007003085600c41d01b6400c0070300d03c3c080e01075a075030300400d0303803091034043c6180845550b5140f12501130b001190a0701d0003687d100043e01e450405031842507207500c1358426104c49240a49600c0100d400a400c1c1c15900720342c0d00c00c051018101041179941d0014181d07120030401010682c4000c000d801c000c400c5051800380900304602151030416901b948108410b0f0a0302c0703050007010f20b00c10030002010a035041c440e060914960305c031115000041f80209149016040b500003007545c0002c621001d5041e503402 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 963667958 1250 963666708 963666721
    0x17070318121e0c030503031f060e0607150218030601080309010c0305132c090d0e1003020d02030c070317040b01050411070212060106030e0c0f040209120a050c090606120c0904061805 80
    0x240e0007108c51a4080d02d001107a41060340040c03030070f44643e0040340610703030204000040024003903030130b06042c00b80b0740c1c115152540d00d182d0b00340c45500e1282a1303000e0700514001188801c8080704540c0e03140c5042c0c440c400b40d080c0da07075400c81313555010340140c0100c1825800041904c5d84000c1000f00c115074400350024144400a402d007801d0700c0040d003400000d5000035100e20a654201d6402010b25600f207844640f200a010300c260064441c061220018620000c104484016028064250305000b03a80c0c24038550700840048c0c190107000d64010381403500441c010000c616060b04244c2240260480c1e4a080c0521580440c180389400c00300d10000d40c000c0001480b4266061160880e250062001028041c1035034000c00c0d1075004120031180185d0700012989459200e0000c88602c14a038a8100c41e0804c1140c07c000c0d45603007010713241c5481180f400d0045407191030180c00f540c00300146010b06040685030340b0300d151116800451b620707801c29113902c0006102c42802c40c603400d61000c090303004107040c50080c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 963669064 1106 963667958 963667981
    0x90c06030a09030e09040b06151b0703060e030a0c0803060609100801050f1e040506210f0705040615050901030917070318121e0c03050303 61
    0x10700860070300d5507106000706402580c030844540503d03410000c0802041c3c9000d070164058002086251424040303103800d9000d124405880e204a09400c2000e0500140c1d103010650000cbc0e00400600c20540144400c1c1d808520145260030002078000e00802c8181c00003800ca030300d01000141c581e0711080c040301c2070f201c00200300f9640001900c50040c1405001d00582c2d01860b4071050740e101e1400c2c40800d6541031054403000114600410082c00001c08004103001d0b403210126440d101d07900d842000114160f41d107400038002002200c00ca5516021081d44100c3c00350b890010b04005801c07005011030340ba0301884c0340050349c5d4019840100c000e020174a2001e030001280341e21495850400c03500810500c3c0c07190301d803080f260070b4207151a01241104c1c8070314500e80713030050244000101c2080b04080010164285485048919200d00806829940044a1641c400814041581c094 = true := by decide +kernel

theorem cover : BRFrame.Cov 963489208 963669064 := by
  have h0 := BRFrame.cov_init 963489208
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963489208 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 963489208 ≤ n) (h2 : n < 963669064) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
