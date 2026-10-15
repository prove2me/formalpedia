-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5438
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:52:13.470985+00:00
-- url     : https://prove2.me/submissions/51f8c3fd-51f2-4ac7-b062-450fe71f2c3c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 977877697 ≤ n < 978057553 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 977878947 1250 977877697 977877701
    0xe0109170a0203070620010b01020712060b030102030a1a0a030803011401020c090709150807020304061b02030f100b0405090a021203070b072105090d1d040203160801290d 75
    0xa01c1d402404844810782e481c4401030403011401c80d1a501c22003108941a071280040c0550900d43c03905a0040c1011070510980141d1a4880003080318060355400c24429180c60a00145104500140c00050700d000060080741c09a2803c407e140e102d031400032801e0000400703020907241540c081203140d10b002205100140d1401c02d400d102e1a50000104040017509a40a00400c05942000151391018117020005607030148040d603007000960030034482441441d01c42c00310b564440380d002d80302c0403802d40140c01003418003003002008140341c2c0056918040b0382c01c40d4025444071407810380b8200041d2803c1c14080b502c800020a00078824080c580b183c26203210208251a20706d5001090b0b4a003e04190f0006000f109421040c9408002d06510401e5a0f00b818031a103446800500c0180152003000d25040312180c0c5c1003280c0550600e80481010300a0705d032440030318441c1110000c6111807150190010700f9603c0141e000c0c0c00001c0341480300b2200d11140d1603118008951145a480c4c903803140f4001400 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 977880197 1250 977878947 977878963
    0x10807020d08070f03180c03020406050607172b140108030a050403080d15080a050d08090a0b061f09090615091a0403080c1e010204050f120a0b01080d0f0e010917 71
    0x160042004003e86c00c2c404040c0c9040100c0e031086604000e003a84e070b8002e0106c240608880500401102004903003090b1070000180f502c4001c401c1c3c000c81c4c80c11142526028007103040c0041184a40c1c401054039060a0a0380c400e016103051401142041c4000b40020114416400014090b20000c00c1c40c42034074509411500c0c01c228803600d004003940e12440714960324186194244c03100e00c14040b00782e10042c0105001d500460b402c9024141c0c2010a4a0365481c21002a210680019031990500740d0013088040e800d00c140341c50b40c0c1e221105c500e4842d600341680d81c3c2e0f4002e211f155461100a000c0580c010100e80100c8081900c01c03603e000c036282d090b61140c0a56440034140c83c0002643d09212074010400c04084101c411414505641c0c0d060414200c0c0600d008054002481d070f0701d0343d0003918101c1030001c2c503034004104030b45040c00d01d5a5030740b100840a90002c203170756105c2508440031942007490f020b20030b06180303860f10391948000b0000300f4404003440b400618188074a4010003036034041c80090 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 977881447 1250 977880197 977880221
    0xa031a03062e0e1e060603060a051c050102031e060a0f061206030501020f040503012003071110090b01030b07050c0c0423010b0a1d060304110d0c0f05010807020d08070f03 75
    0x103142d0324013040d55200c41e0110390314019070000d03100c00041031850074400782c0380a03480280c000d9810904210500c941c4000c0c080504015801100d41030000980034001907204548115480610138a84149041d8080f000350440384a6801c803002400b45441c0304100e842281c2c044d25141203078901d03500f01c2400034081c64001601035400011040385202c240002001103a009034003c2005020926442c804201c5090b40025032040c108003140c2c1207032080000507681d0002030140c0d8124804172060900b00c9200002c112030040c1d90100400920600003403c503803200136803c060346007422184c20b02c0c1e00c982400032068401d9940d41032006c00700c901d130346120b030101281c2d1111034020350710394021200d203410400b400c200090918408240d02c0080e15221078501c0b40250101d401c40d00e03245d413031414410003611641e030007130141040080410800b007502c00041c000c05400d4003c090626000510030b4400a00309070641d40616404d510310b550002d80300303074012403610741224007400d045022006858650155 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 977882697 1250 977881447 977881469
    0x60d0207020a0315141312031e18030f020d0c0b2706160306030c030b150a06030b03162102011412090114070c030e0a0302060a031a03062e 61
    0x1440403101c254440040400501088429581c1b4008104482c40e075040c00207019203003110007110309038001c1e0400c07459803442d544000030305401e00005004942040301041c07903049400c030b4080701341a0403a1100d0901213291000e03202c101211035001d454201b00840007090303643d882d00011030300c1c13501380441000c500c4404421051815241d400715540c881c10746140c03a81018001c1c2078a0294000c0c494141103d40c1f08a007a4086491911090301960000342102c42803a056910043d0307554510807c4400f40c28280c074005061000e003002d052a00032003404030504106c60001c14081e0280a00119030030520b0600c00c4606c02c0b4243c40100c03403940e94404c7c003242c3c889001c04c002030460084280c4611034171041000704003a40c906091002e0000c0f099030040b0120303032018420713004248a880c13001b182074005466403409550320743c0440d00302d520400721000040d90b1444086841c1582034011a100d4070120010400d9050812603210143c010a0040310a03207545402d50315100e902300321482c018450340f062 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 977883947 1250 977882697 977882723
    0x60e01050102030a301d300c070b0a020609070b0915090d080307201203070804030207050310020306040b0a03020105030a02130f24080708011208310602030405060d0207020a03 77
    0x20301b004a400034600840034020b143c07039102400341094422442c1c0b030482d8009103400e80140d07203000751540f0000806460f8010080086400640c601c0104560303000795005025503d41020030310b0401d40c05d034101d501002c0d030800002c042561a051010710035070062603907135078035248100011000c1e6441100200b04120100421648a8000359509a4810800c0b00d600805100460140d15a05110754904041d1400d00114040502c200c036182e901c144a401155501515800042c1c03a0081c03124810465035000810003640d4182030084000c405404d5424001041c1540d00103801400300906407080650301040044048201c035040400508200102941c8203856071001260400d50b0a0b114410320300d44030404400354802c228541c81002d069442d044242d00b050408215540b00e070710280c0f000102841008007440c1c0c810250101030304e01d46a081160302240600b0a400c002c1a0311507810b540051004100c0c03922088115600c0c100a6900169180b1349440003d0746070403290000b0b4501a04029 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 977885197 1250 977883947 977883971
    0x20306011704121d030a0605190e07060923130b060712032f07020105040305030a020709060f030b010323101e061202041a1003060e01050102030a30 65
    0x2c0f40190315146558558203600301d01c003a01001c0b919038001c00c1e016402501c4840204085070700082c0c11000090080020000c030540c0782d002c5e94444590340c8140d8001000030004c13140c22400d050300414140c1c18004c9a00304403c0314002400e03080300814060562103c9440500030103078400c40d1040401000143c0b100380d40d083c048460f5903808015008640f07400c0104d00315210076545403481c0d1031205000c03440c4070324024450182e5046100c0480c14018140b2004c4002a401d2000e882c08860a9005101e8140340000e101c0070748010303070300038103040640707071420b00200b03540603420360660b0303040301e01c401903900100034554104a00c1c0280b00c0f680c4c096260421041200b90300500305402081144407801c0381803921030f0b0200c8440d48181100324072640c0441006003416041036807242d00f54542d419096420b080821603000c1c04e04c2c49400020303541c01041c098290072400b01c2e805440d081c4011400c01d402d031040a460b00030750320202c6030510b003000c40d00614100d0011640c0e40b140030300f00050040c406500 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 977886447 1250 977885197 977885213
    0x312051911030f1302090a0e03120f2e12111c060e0c0f010e010306030b0c0c06010f080a0201110a05011503020301050a0e100b04270b07081306020306011704 69
    0x500c50702c910f6001840881d500965107404041d5030b81e001082815180c8414004900910400d00ca84540340410b0042d000020300d024103251180d00021030b40d96141c585084080140c102000c028a2010304554032518658566044241902c040c1181c10340b0b176a8880c03d050000c50a0498a541d0000820041140c4c1364150030100020314480e00092101c001e524880070380f5064248041c580011440c01c03050712561140300c9000540c00f040c100041c0341901d80e126a60801c008851a607000d010004a42c1e6001100304442801020b60035400445103041c10041c03a11000350040190400030081d1013030310350301814003420040640c031000030024841807070005529040c40b407100742d02c00d5103000e000840d410070300c0c001c0c2d1621000c00390241002904108605008014800c180354000d992032441301c0140d40341c1c2c10a80012040d80482c40741e105110301d0901d601084c010880410000300c8828040600b00b852504078815510480140c0c0301d544240040301c24807880410011805a00e02c14403003440042 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 977887697 1250 977886447 977886451
    0x9020304030e010f0318033b130b0d08090312120a0c3b04050408030a150b03040209040317160207090c0c0605040204060b030702010605010912031205191103 69
    0x381c0702d8125010003284d044c2c044a618115240c0d850034140030100010388242c54507960108030400d4011f10100c0d2188501d04032182081404e00e40d4170f4001d01e400c0b00c0c82e0500f55030240c450350130001d00c13284d40c010000c2001e40d15a000024054080842c1c2411682d6040c02424481e0466415440d01c1d401080104611399a0070f5811400c0189465004041c1f140b2a104d154010003420819240800c070f44400031802001844600e203c1c07509064000b20640c0d100d00411703010324020034071185c403800c201121108a502c901a45070300380801260401c1080c81c04030503039a020750100c4000d02c407036035203046c01e0301c0c0303900d010400e048901600404c01c102580c07629410b24080c0c280e0350031200c12607100c1c0d0350182200c02202e1410041140030303d5081c0092120b4218503806440500085000ca548c0c0c0100101c680042e00c001d000360f51503100c24065560f2182540009020300300349807070031680544000d0604422064403000e800e44510018100c1c0c480d42c003c090034158020820407003000009c568401c55001 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 977888947 1250 977887697 977887699
    0x309010c0f031112150d030909050f0405120702060d060602034302280e090102091809010b190602070801110f0703090f09020703080f0f0106110709020304030e 70
    0x60700c0d40c1c002890b22074442e841d10141e540081600c1c00320004091440408010041041c1d5001101949041d44441d055012018482c1e00c407240050700f099560800d490008280528007440b140400000c10000140c071103d01d402a91303082d64489460020860702d100704209544094101400020910340c000b000b0002051420200f0910b8040e050101003588607404440395003840c500c0103e4040c07186c20b100020054401031201c1e04440c280c04071121134991218a0140c0b0181d43c1070100183da611904081c1d1205d24480214602144400060011444040c80c459102c0310f00001550703605c8250710501600c0b600801840180c2e0540c140d0100410860266a0044c0a410703000900214140500b1021802e03485900741011032a1425640981194101f9400c0016509000400d24400a10140a002c04840c00340c0da605107401d01610000020304401d1588541d50100515a4411241141540c0940c0f07020301d506070303121301610710704103483e0400c03100c0501c0041400101600b02404000d0650 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 977890197 1250 977888947 977888957
    0x130f030c12020f1213240f0c020d03050f0904110a0f0206010803030711031e0d06050f01090e06030a05010e0d14040b0d18080a0903063b0307080309010c 67
    0x40500d812030b100d02410040b403946500c51a1003212119010000d00242c0b50200c2040c40c415689001d0b550b294140c0403800114080c5030b446d200c0341103034090107200c960311403800c01c64084603c0364046800e50b8071480c00a801c2100114242140d07940d0002141c044000040060140b00c506c215121025404084800d020408901c04081c0740390001c25008d0488210718051810741c1d8400100b5602034034002030418550004101e000850404a00194503540f000003583d43c4400102640f84c08840180d000103121f0350082190140603033f0300682da0429541031401c0031405885500100c0d00d00340d807071a001000c550a1849000030300d10001008190710400b50742d400a0801d1032401c02e0b04034440c0780921440135504101c0d4040212440c0c1150a012200700301054080c82c95031540742c0b543c0c010511132070004180b0801081070150600070344c0d20114240c0070444800120101c0e000c0f54401c4a18820041c2400d100711644008051058400340350700015070958900d001683e4600070a00c0d4423202010031 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 977891447 1250 977890197 977890223
    0x9041a0111010e060a181e0201020115080d030c111002090f0a030305070f030c0206040b1806130e0c0403080417060f04020907110a062405060c060f130f030c 69
    0x107401400740102000c03600002d08400e840705050903025280100c40a03200604202101d8000341c00602c0d1398001c0c2d0000044080804510700c0024207460030b20304850f11030490070b10103109012020449614109544c1000204103a40e080309603400900700c00c0c05040e42c011920020100300d2a60010607071008202c4640d81d1048003182000f00c4a08035000160001d64240800c4000404d02180485400d01905295090009585c0002d5807507001d60000800b1035030200701200302140b00c080d42c0c0c620450844603142003941400c0143ca6010151085424001401d03000c56003112500c400ca90240d904102010f98035030301d8031030304101501410b954001c036114801c001000e40210201030390050754000c050010a0b00c035604119503e896a8800031340701e0040304c2c00c8000003119445210081200903a81d410b80c5001e1038040e805846d0103a02050141ca020002501c42c0ca0003c00d00642c0140219113140c10394032440481e682c0504d0b0440020b04800340701c6604014190001c0180c50070f20f2060521040c81 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 977892697 1250 977891447 977891477
    0xf0c111203010605040e04061401030f02010219030203091005280912020d02040e0102160c080714090c0c100f0501090501140f24070f12020a0302070b07030509041a01 73
    0x10384003d01c100400900103201c05d1140138070200c66a60014020000400e9000446410458445082c1d0044800d071000b030035108110b50b0140701000000c0b00310f140788683d40520340c90294817880b40c0c007030051240c000203600740503650055081da6801e07061014080200001031224403207601c424202d480101b0503c103000182003044c2210f8055443d03001d007248a18102c2c2c1e600303120160090480c4c070b80055409000c442c2c81e4420300c4c07000d04e0801e80a00350040348149010302040c00c02d2510b1b080020030f0f903009031840d410b036181c555402d13400001c00c07050b1070703a24070a0320703420703810142102e031000b0711030341006003829104065801903410b03202c18a01c2081240d07a1001c1810b480111003036103941050300403a0384907403440c107040c40f00c5030309a1907510803400070003902a14540303a00c855003c071009041d107040e50061050b02114800300004030300082000400d251070207035845480d807180c484044400101e141c200342c465000e0390302e00000a003081c061408514240b55031310341c43c14121800118408224148 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 977893947 1250 977892697 977892733
    0x1050c071a092416020a3203071d040c0e09060a110301060c020f0307050d05060f060306090307060b03030910050a08070e061204080f03090604110105031e0403030f0c11 74
    0x40c41c0280440c0c10315000c48980e804c604405400c0081c0d07030100d6594030006040c070440d10f59940c0c080740380743c0303202041c0c0d80e440e0104984641c0300308083c06a40400001d00c003250030307000104040c910001072403049a8030351624102d0b0030351a4100d9800c020441080c070021a00000e442809030200120a10030000e041c190340e041c90000b440340300001542000c8800242c28001c0201c1c503010300c06003c0c0c0d102641c0352000305421045000702200d0790b501610801c02c48040080070366030018011806404681050003070b450f038034001c1c40800342415589a44040d01c9980410445840e0072000c0c00c41d0450814552000e4440c0e0400100301011852080009412505c510010482c00000030b21880c245891980c5500c00707408014000c8031000401c100044580c55100090340c81082d006004008034602490300058146c15500114140304051050146040061b54075613401f180c100003140155a80e800e0840180c040d910310300d03d12901e4000f50031400740d4841c128680800f807a80454a0341c00001c185040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 977895197 1250 977893947 977893999
    0x60d08040504094103030f06060c010b13060501021605130f0905030c0102040816051804050a0b010602011a010503011a28090501082401050c071a09 65
    0x11441042206000901c1e00c0da101803412405200142020303440000f1035500c004e070f210040148050b07007451040300c1d4034403a400c0a403c0e0400e24060f50540c10070440c0a418100060300302071054002094231042601d0940c80f001558000600107900b800340748009000601160090fa8010f00030b20381517480c210300340c030701c08001c80d40060055a4440406030b040707801089201d02550f142c0c3c1d2580c0c4084003080c800c10160001c1e0782c0031000141e82c5e07031901018500d0050410052a111400b2030020400303541c40c06440300e0004210146481c0540c1d9628005060030041f02009101d95912400403880b03a5056004104203844090140c800000c5940103441c18002481740c004108550b803154540081e022018080820b100c9010f244030800c60f400e02c0085810400c965400140c00c58002c00096901989682c0c104041300c0240342e00f50b5a08507506504a1180b40c0a418080b00164054005200f000007074000d02692030704c44908803405d40c1114442e484a1041c501c1400320f28182107032b44010a419035 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 977896447 1250 977895197 977895203
    0xb03122d030f0c130308040f08060f01080714010e09130c05041104090e030f04030b100f0303020a023604020405070f0f210f0213140d030513050303040b07030305060d 73
    0x38600750307150700c9911519440b00342c13200180e1024080004c000b030305500c05072005d00015208a5142410b040803a032805070001c108481c0350343d40d280100508007000c01c12400340d4502121806102d155840180d582c40c09800000307400c040780004100c000a00070306c828451a100d0000d40c1007566036175080205460180300101c3d2261010132081201da5400c0d409030340c03112061801c4d01d0512616030500e0840303070807030761081e031703c1072004810000b49a00860984001c0c0c480f02082032621415518020343e2000101c000901401030050303503481207800f4188031401100c031142c07410881a0600d4040300031030015a022800b0300d0600c00480c41c141c3c0109041c0c030700411140d907444243c8051020840c2d0503221102110b4554001402e401a961000e00401c07030a8211b94a0250303030780788a101c4034010154594003021060281c2018204d19649098041840c1030f05450010303181d00382c04038244c80170800ca40c030160f0b05110005001910f4040400600451402903c00300300d26915031040c0300750f03018021801 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 977897697 1250 977896447 977896471
    0x170903041406030402130c08090c0904030504360b03010f0b060f07030c0c03030c1a090c04110d150f0b0a0c151b08100609080601090b03122d03 63
    0x10039403418100b02656002c0e000a0809030b0700550300840760b0845a0798041c403800526140b08110011508000240007104180d801c0740c118940354500401d030340268001c0c8400c4090303160341900d080441000b8152020b21810700901701c80f0a00c12810005d104c00b02d4a6402542406c03c10b074100c003114482c21000300b8014149074507141c5d6070f03075034030b03001da84904021014440d000d00142d0204101905000c06140300c2d403600303c0442c08500b407881c0c00f0000701e0000c001202d01102080703030031900412040505070055070042418039183d510b404c10f80c01000c3c4400344151900b4020880c20081420250858030306044070b021490322181c1960203481201e51840200d042c511030a0700040c0301e00c0004031a0340314481c00040380042506103032018000316001400013101c1e00140a4150390030844040103056a0a10b441031510385071100b510340c42c05201d58001207545103117141e400d440600c070242e2440743c144100b558030450006402004404050f040c1e408400d001101c1040010900c12a401800040c1c50 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 977898947 1250 977897697 977897729
    0x20f0c030703020d030333180504032309090907060315030b0f0a0f02070609140a0b01030206160503121009060b07020f0310060608090d080f0a020a03061517090304 72
    0x2040e4058500780400ea031040b0f0f0041884903050042140310f40c030210070521405113162808d80446800c0821a1a0110907850302081c0000a900072005149019105a040d00044000020180540a00c2c8090f42e0404126800c20400f372801041200654101c0e0704c08001021054a0051580c0c030319000041c82c1035805c20124800c0344a55a009030701c0181c905001c1903450514100d0426170304424803c4555503100c5069200b0001091701040c41400920002e080c8403045407603180c0320745010f2101078014540011102003528400c0c506050f120f410000b100e84d41d0b9940061000d4003581254a9840c4220160012995014038014072088236074001c580d600301f00c5140c08001d4080d03000c8030743c50b515104e044211030300700b6024060f26004240340d413500c2c1014030f03210390070301e040090240440040042270b1040068155004540e40d0b0000002d000c010385808980740700390001c0015800400740c44005003565910300d80d0010140e4a20b4800c0540c0300c41075143e00b5145a03890045d0f002d02c4d4404940c041c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 977900197 1250 977898947 977898953
    0x7030b040f02070308070210110a14070c030515060303030f071115072d050307050f090405010f060f020d02250905011205060c0c060c030a140106020f0c030703020d 72
    0x44000a64010320014451428500c424120f074403c0400300c021039a041e0402000c0d40e010710042001d0386512a003801070b60f90b203020a825901c40c1a41042c180107200904245c807400f0390041d104195800f00001110944a0410301d030350341c0043c1060b00601c045d070000102503040201c141c03800b40401c0c41c6598249d0700d070340c501170300c80314000310810000d445500314141001030f00c2e50302107001d006140c032461150300c14020302c2078100c1c3c1a032443c0c5107590034045a0014899000e01241c2d070003540c0d403a0403a1901841c40c00140248038006042c1d03400f5091500200300500707090000c204880e002e4071044660101d21006907107a602444c0c030f803409070300054007a49001d01150350f0001200d188600510380b00703446000ca4800c41d030007038114082144c1028060400c01600f0010903401100340342026086c00d07690760469642e004001e00360040c1c0703480840842c1689446820058070502d60b440005400d40e1200747c0259900350300f0644142c98420040c0004c50f07400c000c503020082c1c0e600038143c0002d62a242d1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 977901447 1250 977900197 977900201
    0x50c0a091e0c0e030a0308010810020405030309091e160e0f030a0803070504171b031b014406120c040908120412030c050a0c0204090c08031b01110301030302060703 72
    0x1c1100c909110f040314a0030010f59040c8070050f01640b003904d401c00c0d55410400350350300d020303800f50341d1041d4148100710078401071340c4c0041901c6400c003003200c0c0c5c4403040e40d41d401d40120b42c441d0b011104489800c2c403000c0c0030151a404203000c184d074001d0b656888504507440200541041003c500507090b422a5100308080b650550081d54407800074182585042d0f0b9501205000e10349003166940c040e003040e200c0f0105580360108490a4030b04c11402841451148101c541c401d0052541c06414010707104c500d01c0700070829040004140c6403140c03003c000c1c01d05034002215001c841141c01000e1a0703444001860615203000ca44490414a0000709070030b5400100303020091603080c0007502c1c241014806460140c0d5800e400e01e1003144a07056444c0b100036940c170050f0555103000010824010f05000d0300c040315a010841100141c2c0403900803d40b0310482c140b01c80c444003243c020103001d00000500450800c04414003100c100c14000013040141d142640000d8280000e0000130300581102c000704147c40d10035 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 977902697 1250 977901447 977901461
    0xf0301140a270e1b1201061805071202071a24010c050a0c080d02010507030501320901120203070503070b09091b04270c050f07030912050c0a091e 64
    0x701d40029120800c2c0551a14000e4408501c201d050013401d50000d4600384510541c0701040140002d01410342003070400c1c0341c0036540103201c0b540d242d0b9800004500f2072140d03a48040342094102c0c00c542c0e0b0502d030300384071890540020b10603001d08003590100d40d03121016585125480c41c030b0440f0080058400e0011a01c0114048060310b46125083e8000e0101d1251141c2100820540c4020401084040d0029094a400a000b41e06041c40c11300100905100019a400707503ca03100a0b03030a050002891030300c490514580c405030400e605000208002c24a4020003d24034022000c59402c0307542c813010140d4480c0503004004e689003041c01000598106640c1403034012901440144440601038500300540c0c00030f40c000c4050341100d426080d03070514103c25003108049421000e1003400600100a40140300c0d0705041c2200c848002070030000e1502c10b414440152000e4440b01c5150440c40c00c1c15035651b8101206e01d4820034030344c0700002d0641841d21888041c096580b0342e541d10001c801406100405071 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 977903947 1250 977902697 977902769
    0xa1b0c0c0b0708130e2e03030c05010e0d050d0e0610050d1707060902011d28050d0507051c0b060411120403080906100f170f030f0301140a 61
    0x400e2100d20080100c5401c4113002e404080c081d50841d02c1d100400e080b40076944c510000d41d110420030079058a080c05610001940d0b0142810083c5a07072a1070083d0040802003042c002d140185107200311010b170300c40c00402d01c2c45031551041c0444002101c01320b4681070140ca0b000e5081c0f04800e03041115041030036400d131141e4020707021108812140c50b00f8003007681c0103034400c54006075a00d10708000c560300709249003580c060880d0b040b0001c0d95801d0124040d421030040040d02d00d409168042007144644074510041c0c0300c0500b0000781c50400c1e2070019503d1442d80510351007180b0075186050b140d01c0440d40a14519040041240913480b003000380300007402504510800302d6410406103000026000101c0d00492003552080141d00c5d00e05196410040068035100000c401050108001e030b4096440409844841702061800a81c002c0c0e441d280c40440800c0711131a0001086e0240c14807183c4001d503040324540d29503800d02d00c03c3c010170800c0740000c90140c103500c008503c0d10200007468000c03030742c81c074502 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 977905197 1250 977903947 977903963
    0x1014040b0f060a0504093209160602030441040f02220905060d0b18060412030b010305010501050f030411041a0f100206041b05090a1b0c0c0b07 63
    0x21000200384668403500f85000030440000d401c2020b20b2031845144005440342c41d90000c0c0c00d81c204803501c07030122080d04511070010789501260041c0814030040d0411b15070304402c0c00c02c2640d1003002948a0b0010302c2101010152241c10282804104095410103500001c0700b00c086401354000940700072030300300c0198200e5900c01d01e10111843c40d01c018541307024400003003a4500e01011884100845a80000240031f0501d010f0042a445190304c9800f4103038008a030726030729680d100500408000c012140342c06442020240020710041c00c00060a00c406035400f8080d01200c0350054044e1282881101c2c00500f08010800c0c011a801c4051500503110b40c0392330318145030490000303090303031010401980024500014600586440829048a50000c0c1c0e40507010a1504038060740b90b51000380003400e1841c94252100050461400000180100070002002814580300c55402040182e0402c5550716619a20750101d42c061080300508070344c8031040000d46070401500c43e020360440700d01110900c1d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 977906447 1250 977905197 977905219
    0x60a0e010c1b0f090c0c0203070b0d091707050f1b01032c071d0f1b0d0e0c180f0403140421050c01090803390105010503061014040b 58
    0x21004101c035500500183c0000ca100c9418030100c075041710b4040b04010180103901520400503180440d020084605000b4032035100c0b40040d0344800a0300580c0b800800310090345082e0004203048602411100340500100c030080480e01462540c1c884035202200c0b02031b41d003070070710030850342c403d07040b04142002428a1030540c00e84ea52030541c080404911310405604179070014801c000e00c0084201c810401990b08600d541040b04610030040d50280c5007044901150403205e1a0600910031907000440c0d1b400b00300008902c03504281d455101c10001c140c8074242162481407156000c05115010310b074100c044802640b5503540588000700504441014054140400540544a40f400c0e480c1d001d880d800a10150340e00d80303003d40c1040103148800c3c1c144442c22401307000044001040e219400f00d11240c0e103041800310002e4034203502c1d8917002022128114108000480010b4108504032001981180d0040c0c0710388d8400d00703004102c0d00400408000c40e0220052910300754201090380c0e640540065004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 977907697 1250 977906447 977906483
    0x1803180112090c05280b0a0905090109060e070825111f15240207030b0a02120705031e060a0b0403050706020705152d1602010e060a0e010c 61
    0x1482d009907098880703407000c840800c41414402500303043d042580da048100c0c1103c101c442001001d40b4055841d10007404103d0700d03401c90040355040c0103490000d108640960350b030f4001c040034140700c0c0101103501b2410344c08541a10b005e041914080c1c50b52445c40d0600c6500810310b502e402c1d000c4135400040120048040038181400c5c891400c0034819010500d07040a00c000c1810240d4002c0d8154110032480c41904006400c0314403130354004200b40b580441c00485006108038035140c01504041d00f440010410300085900d0b40c0d00a10402c80107039080029583c481c503095956020849072203050051680c403908112840c8040503030300c07000040000c980c9075212410307800b0720382054000311500d41c0404000d1000c0c6404010300001004112000d45401003406030145080c00f51010045590f248246400c0048648050001e150180801296182d2079008050704820302950070580c0491001c4076195a182010b07021645440c05548aa042a5925800444408000c1103048d10f500c000f1490340907903 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 977908947 1250 977907697 977907701
    0x606081603140109061b18050d030f09051c05100c080a0b040e0a03091e060c11130f1505180105060a110303151c030f11031b03070b1803180112 63
    0x41c110400c1000c681c001e82d0340010b0101198080c0307c0d4003040c58660308020983e1200b80192040ba4036180103000700e4007200c402d64680c0c00c0c9410040d801201003003440441c010010800c2c040d10b0088040f0f555001104030703010100ca105801c03840000300d220000404c03120940e080000c041c02c01410014181d502c4210031400c00c03c50340011000580394003000c01c01200350b08010150201d050b503c42d04801e10340303680645180c45908005103141c0c0001480617080e41d034804101c040440c200d4041c002408548000c50040581202000d0341005181000c20760b4200170104101428441a64544d941d082904001c070381d03089803005d4401c02c41d42800d044540700003400514003c090a84042d0002050384040000b84a20a90b400304003801021140d00402d41c0000b5111460340310341055002d030070017a42d40b1030840c4102d0f9048d0780e00c810f4600e0890048007000000342201030142003d8ac4060301c0702c2d0020808220b141e1100c0c01564414080085060040c04000158450504055140ba400342c1e5005003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 977910197 1250 977908947 977908961
    0xc0204270b040501050f190c110d1205010602210304110a12030909091101080702030d0c0207090510081515040c0e0f0a050307210b090a060608160314010906 69
    0x2031441401c420701041000c2409896007180c8140d107441c803140b0340600d00c000101c0c0c0c6442d414036001c0e20351355200081401906114200222001034541b198030a140c058191000c0c2c500e000c02c06841c000000408c0340c070215503000500350441100340d10324030780041c0c54211b81001c0c200b50390a140c9882c91000c1c1c0c0c1d45051140000b011440c01c1243c1503600b41c100942200c085501081b007050a003180b440011742d40d0000100380c0c25090818122940741d0b188100d00e14040d58283c90101c614011842c0070305a0001010003c5490308001030140b941c49444440c0c0c001207521403400703a0340c808440317000b003808410314481e880a141128182c041800400007401d031a16503210318042903192403141c1e024203120941420a18050743c04c9050b280c940004030b691003005200c0c840034995200350811894a490b54030441c950380205000c0b0f1641803550581e40c40f050740d8039044809524140300010820804038001c011008118031260f40940703181c450101c004942d1042c3c0c0c203035540c1c81c03105000050041c8241c80b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 977911447 1250 977910197 977910203
    0x1309020c0a0506010806040b0a0c0c060f021e0406081b0d1b0807090311040903020316050d2007050105070501020c06070905010e060c0d0311130e04030f08070c020427 73
    0x40311045603801c2003410f0a10680010350203410010810010803041c01c00d8076003051040c580021301351901d000442d1081c41a40000f0002400c0040155034600d03141c01808000c1006400501d06402600001c00c081c841c510600c008070b0540c40000700900260001c41984140e0f0310092403908a41e158450111038400010100040070285d0410809a001c40103d83c0101141014416541903448000d0691180707500f4502c1039841c0c3c4410401c00d0710900589107600483d031200401944075140c80c0d038940040f20f50318400903d41842c0744152661202590568412000140c1129400c0100440d80c55100d1403007910190f400b005955501c01c4100314003441036500c0e41d103a490203030408c0001844180d20307850040c4910814007524401440200d8a9a0708070700a0400045402158030710001c2400380d15403810112000301c1000440300c424010442c41581719a4602d803508440c1041075031281c400703880910020300420002001805d0070f40c085a9458a146d074000c408009110b43c044e201c144ca03240031 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 977912697 1250 977911447 977911453
    0x307031406010e03070b090d0b041a131e021507060515061201090c0903080403080c060a05010819050f0f03070c0b0403020d080904140a0c11011a061309020c 69
    0x58104000305080381500204246859031680c2e04000000c0da03503102c05d00800c26251070000340c0400603910030340c091400c0f0380d10103486000f03031400742040000700d2500601e110741502b4460014006010a20441428550110302d00d09080340c092032502c00f00b01070040890704031061020301c0341111200c03000350001c1c5214441c0410b01d46021800705407030b07030301e180d004034000d15042c08210902c0038106803d9040d03502240b07001900300c100d514200c401180320760028250201c0002d0200c2803005c40d10081174124164812a031213a00c581065a040351001d1007038100540044410f0404443e42c480d00c000240c0c011401c035691660201c8101e4140114181109015440084c64000700280c0e014500d000380141078840381010710310380100781026540c84c40209040b20019070598140da40d0380c40740042c4100d0314448051485d010b00d4200052070a098140003248807141442c0200105000e64885518481c0d9000e005820800a00a10b500328004035500c074881c8100c049042c4540e4405003600c49412030003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 977913947 1250 977912697 977912711
    0x2304020307060e010f030203060f040204170607140a0e12161403060405073f150606050f0d06051002070e07080114150904062402010506030d08040c0b030703 69
    0x10103141c010503030701071001d110304038071144120780c0c1090041c03190f0398040c1405079072603031401e002171024a007401c1c80350f41c05480810042404101e100c07510320560200300c01c9401c2c03611082c5042e1107681c0144034004203800100049150181701e0b443c4440805406040300071105406040e090608481ea80e040344000c64518041049402e0140c07a8280d0040c20b40c090201401c054480c19290105405070803022917000e000c84540b00314280701410142c101d18004460700e1049070781103080b9050700c48240c0346015003800c41602074038140b00e000f007213400340d0310b8041c60040c402100d131150f504204071000c075040c2d0762a800100d40e1200c0d0317a034034071000d440d5000e060361904040480d6090080900310000b0030844100510001600c1151020384480446124500c210100010340f014032581486603007141c10004d0004100750b07000c3c078030015100744101c080a0b002100808130f00320390040724555850f60100518080301c070300407403401e40c01c2070061041c40407103030312040c60081a60003910041c00007695011 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 977915197 1250 977913947 977913949
    0x12011401020106270c18030b071101020a1e05120a0c0f020a03080c09041d0106080d0c021c021f050304060c031b03111e0c070503012d230402 62
    0x20401025100d1816203a4006480e0340c0308013a00280044401d044039540d41080da5004d02510451100304401d5020010141c3c4902e0582e4403101c007a6800c2d004600000c07501c1c64075003c18001d85101c0c2c10f80d5569607658205a413880d840302007210714514184030041110026059111907180c3c4a0411407201048140380d20100400101c0385400403411500080c00050000368003c6100760803c41c400300180c2c40c0c07420900000d00900b000440c8841d995503c052100000c401134021000b220710342c0d01582c3c1030b050040d1055a030708640da140251700c1003402c00f141c0c03104060349141020381e60020b0300400200c042e01d0681412981050701007004501c010041008100143c02509410802c80c0b409009040740c8916042d40e004a4030006014562103203910130181350031405444d01d0010554029090881030301142c18558007060f0703c03808a00800401207003070706050140780060124010301203180300703445006150b00009840c041008a46035a0b07a20300011501300020180d80c2c10050319900d07810030384 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 977916447 1250 977915197 977915201
    0x80c0d11030411060c060c0c1207030e01111f11070606030c0f09090807080a020a1b09051506271908061303080610110f0109150207020d17120114010201 67
    0x10301c3c0d208550801200c5080c0102181458008216054040d01c07070b10302d440d15a08040c4d18180401c4a91404505c6034240b41d4000c1d401d2410703440c00e07252002e03c4003054801907107406000f240710880c5841c0b990400600001580300024060000d0301250800200b691204281c41c180d0340195040c5c20304000511506101c403011800800310300d40300304598485592460301d05d0080100c050301204002c6030741d0800a00912038200c0541e8041c500d981a07101c4905840c0d5595181e01652048624010000d1a811922102e20008100013848039003040c1d810b400e002c1210002c01c5004d0181341e030b0752900e604c00c0d40703c07401c46c1071038140841144c0c00c9403401c00c035180c2e10b4020300030940d40b0382505803101180401e810840e4250040b40683d100d448521724070038107a07845028904056094800d401040800040c1940a00380302c0e4030034840070525202400783c00c002c1c0e0180c070202030340c0840070b282140c0c005076000c090800c101c3c450318407041c1043c41d07080d020401180d0980c03000e040d01c020b11060440c15a828 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 977917697 1250 977916447 977916473
    0x303050a0f02240a02070b04030305010812030402031c0212040909030e0108040c050f03010b0d061a180c03041a1008010f11041401032702010201060509070f080c0d110304 75
    0x82c801403600c0b002c100664410b100d004040a030554000d900400e1001c003a5030111194140c10a0040384607080618004000308024031600400d0300407070800341d00b400b01600490340a190020003c00140204d002d074202070300034040c510000c1d4892011070a6000c804840948024017500c1400a50201203041c05070841004042071810400200c04000000710311020002c10358605690b06603c1d2200803000c070b40140211035420f6409a120714060302002941e401101c82c00300030850841268507034101b40030143d41656400319240075800b000904181840028650050180c40080c8010612803e60886031105903654450545200030600071140c0074001ca18002c6070407581002202d0103000c040780d840c06940114503119125010b001000e070300c00d400c40f80066800c500ca41e00000204c0c003001c1d6250742c51910890140d4201000041d0901d031000903903200c1c8519803201e0700740381e403d00c10441d07132004014501d00c0410b8040c400780711801d989100f003300030418040e98503640c1c102800c040e00000a0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 977918947 1250 977917697 977917727
    0x1302180f22090b1e0a05070908030c06060f0a0515030a0b0a06181719020f030115031401180212150a290d1511030c030604051b1605070509010303050a 66
    0x10004100480b1003040344c40c594001420240020f081e11200d00456a001b1154052a80c91102090000c2400300129085001b40000c83d0704d0850b41c06010140f20a40c1325500c18141d020201d4004580c0425900700156800021b107080000d255554000003518540c0c160040f400040000700040040c03503058882001800d50345a40800c01c40070058296a222821809400c408003009096000c43d107030b000a10f4514003004009011840c1c048603220440321a500c0140c0ba5001541052a030410061041240021000544000f800003035001e101d054007000c80c246507284140000303ca002c26941e01c000e40502031540d0b001c540003070354042d441401c40d42198440e24503c40c0d190342889542d07a00c003448022a52061500d0101c2115008190040041d0b01c4600070410000007000b500301444c1c801184549011541001241c44244003e002d900b91a004111783c541c0070000c105900e0510106150114825070807516656100c0c1d011504030403007a0703c101d002c29004100819000d402c55003840003a00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 977920197 1250 977918947 977918971
    0x30507080f01060f020f0105070806190501090e04151a040b12061f09050c1201091404111203070b010801050c0a0f03021803011a1302180f22090b 64
    0x10300c81d412056450040c4680002c0c090f00c0c403102c40d1001d00078000c000c0c0301ea283d007000b04010301e00324002401c440c100b05c8419215074040400c04001404407509081650010303902c0340391a40c00c201001100d200c0241064585502100004800c9162785c0691001d010030b0b41001c41c07581a80100b88802d036011005a284604408030805e1b101800018141d60b100c58000041103408020b01c0b8550f506842580105041c80d04140c2002171008242c401001c100b45500c440e02c0c1c6e1680d030303603217050200e030481d05440c258440d809000c039010807208541b440f000c0d600240307814880020b160069280d98010041115600d0109004101c2d081080c40b0340c561207050702000929000000380003d0228041020000074194046504071124134410060402c5150140082112100c1118000111000420020722034510469914400003050003a508960070490b0900c071800c002100b0002c2c00c0c10f290f43c0701c40d0090051100d0b030280a9650310051200000d54100040c40e0059080603034540600400340c908102e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 977921447 1250 977920197 977920201
    0xf0a0b030d0e150429070b130302060a0b03030d0e0f10050a0605090402090406090609021003020c1e070506090424030605060607110d020114040b0c10090f020d11060a0503010603050708 81
    0x1201d100810000105110017a00c07840340c0310107011050300031580301070301c0b080321607040026044090b000d10400314083e07001c42e200e960300c40c81d6182c15580d1045c40700f078168206000a001e042d081790840104401102c1c20342d600142100c03c22480c1900d01041072000540321010300c002c1c000e980c820a80588002c1c1c617070314818500b940103c1d40031040a803004200d42d40c0d0343c042c1e40600c45035900c0340100980c0100702d0800e20005401c000c1c040c0d0440000c400d2980920008042c0d180003084405000d915078001601030350307280c0800c12640e9005261056040b40e00c0e551002c40d60780d43c90081507401096080746020241c11070401c0c04c2100d030002e0481d40103030004c002c0305012905560b6410300803132003290b0301405002140300407116400c1c0d8550b05c8202d1803010801242c0703129040c0142803105a14811514152191010f00007903c07804d510140422042015040160a11018035000e0900845a103030300ea00d551070201d102513015401400c00101d0100060100c20784c14040d45070040150700d4058414 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 977922697 1250 977921447 977921459
    0x123010303050a0c050a050d0c060f0605091311040c032003190f0e060c040504181208090708030f0310060815040f090c1205060f040503030f0a0b030d0e1504 69
    0x1903c00c002c0030f4800d12520107260b030100b100402003c01202d60240980d2404981000301400d000750109040b01c0c1541095209002108284a1a8125100181800f440e600e41b4110307003094445010040e00d510209400317404c415141c070b0240c082e019066507000200c20110348007a0b82c4a1551300046071070a6404c00a000c0380c0d000e80c1520300030300104100006880c403594580e2000400003020503443d01d004007000c000301070207100040c104a41080e0340c2440602001722050b0381c074015102d00140210351291072004582e01c9001c400d5800303d0018100c2d000b25860301a2103245401c12980d0f40350070500041000310a4000e01c1e0050300600c1c25003040483c0b03003030800414031590703082084603004640e03402c24401c2414030394110440305500030382d0014000307480f2405924005581a13040d1514440c0384046044208940300c0c491145410001442c10340d100c005641120000140651065645a1020300d109940900072011032907026120520001800000d025560700065945124100b00303010402c50 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 977923947 1250 977922697 977922707
    0x3070209151923060d090b190e122d04060f08090d0c0606050406080f07080c0102070905101805070e03010b0f09061212071506030f030503270123010303 67
    0x1080c0f00741c0c01c1188004074a00007040c51400340300400b24050b4149900d410074402a040321718010400070310701d81c01090800603e0400e1761048110210356500c0003600ca084800c40b5405402149018100b13503000c101400701e140700748408101c0300203600c0000181007284941040c41c000316024035080c11103040c5059200d0a40f1000b100450000340030505400c0c80c100310940e8001405800014410031110342c0726014176603110500da0359014244148200031560000001d05160f1104e4142e0082460908102801000e000041d00b100401401c5400c04500b0200880b80422440c4031160f0000b5540f400c107070020006c0d030510f0304450182c0d151900040080d103815203003920200d010341ea510342a03116800461841c03945081700210703500448150001000844000f0503920b8052040000741c5900c2200180071505948401044c001107080c6090000b0b00070030186501020b492070366140300c40c0d0681c0f004d9000e6038000480407141d568001d8840446250b41c00a1240268580c21072090f40c1581d802401d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 977925197 1250 977923947 977923979
    0xc0103060f0e072304030308132607080d0b010e0906061815070b040506070509090601030c0c05060709052404171002070302070603060803031302040509030702091519 73
    0x81020a201c0000e06a18083c4d5801c80c1d1810600d40c00200001002000c03100c641c20034002240064a1400822510901000840d1029400c40349020312952800300c5a80e08401c114025071000800744041e46c0405c8170b4102810100d01c901102041c02c55600d40014145489440300c507200d91074410901441da02e41c0c00c20b60f076403100f20030000004070040400062400c850b4650f81c00034810001116070412591081d003a0081e4440d00817030b0351685500c48296074034081c10101942000d6802c00044166102c1e8001811086241c180074504540b0b40d02c41c0c43c10032034200da43d06e01003100c2080800160a180f40d03540000000800e01c7c40442c0701c0c041d84000c040c4660b1040c03011032401c001040500b0b01017440000da0802d03502004542c0c880c02450082c0d251600d0744511070201c2c1c504100000c1c03691011084034071505081e2301044940340550700304002488081c000c01110f1100340281c10040e16058605130284034200c41243d00c112080e030030400c60308a880d181445042c40030a003003000b50f443e00f160035 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 977926447 1250 977925197 977925209
    0x390616020111120408071d07020c0d06090f0b0906130803040f0804050a090b0a06030e03121021060c020d0c15140a0506040c0e0f010302090307090203180c0103060f 72
    0x80301c00200b03482c11071402c4200e00d52546031480014001a140c0c40010388401114811000c411465141d88407280031143d0407900c03040980c119499541c030307514020118042ca2403140000043d2001c0c02d465010048003030010484544210700144404550b04102042d40302d400c0d0643c24413000e40030341d144425400050002465484414420300c01c0104c414155000f600b40506214402c1c0c2d603a03070440c0003410046903010701886200d100400d2280c440d0180003843e90003d001903240174034a62142008000c0108420f45942c6040c002240418807100d00b00000800342e401108000e106081c140c08a54440013600155401000f400c11900d40200009080a402c4858914405101c002c410b0251140744030030320503109030804002c074030301e11a40914050107040d0340410125049078029621205c1d91060070703520081289030f1086640c0310b600200342400000d401d4580441e501c030003d4017680c20030b442502580c40844001074800c601041105001d01c42482c0900c8070514104000b079040ba00d5002d09 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 977927697 1250 977926447 977926457
    0x70e0105012019030801060908030f0a0e01090801020c030901090b040e010b0a020c040609050f0a14060d0f06090308061212040e06010c12110f01150b09033906160201 73
    0x310b2415005000c0404030005012000e14910700514008250329400d000e0503012800103100800d00010000540719503180060341c00385015201001501c00d1444c00700c1003410407030118400b01e040042800586440444c060040d500c407413459002409944168100c901d100f0402d210803c07070784250b0814241140c0a4864003a03940101d140d04900300404154407a030020304244001400c01c03000d9019a104541c0000079850a844d0342c031145080e00d2000694400841e00800410b28504c0c0c82400f284401d445140c01103c508103176030740c0340251440000c0030750100d40c1040400800e4204280c0102c0c084443c1809000c4030750281d114007200f401240500c00d2020404c00000c2c510707034041d41a050100b40c1103041c0b0725400c0390500300140071420119034807000c3d0082e5000070302c0b40700c014054a0b5a01e1080410b503d030160a00b5065612500000103041e40b611410040895100501042c0b030f02000501e800c400c11941b000111400d914100c0c40518040c120801c40408440029445001c11a50901c0c03c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 977928947 1250 977927697 977927747
    0xd0f090515101e1e0f1e06020d02070e060109051f0206071b0312060b271804080c010912030e0d11061f2c070305100608190905030903070e010501 64
    0x3400048013030f80214130809400c92022078894000106100d8102d0b6081101c00c1d402e4070741004a0302c60550340c03d448096441503038148000305075122400c0d840b0006140410f411030b903490000b6140e4212342c01d03450068030101203500c205a410300c006588480369042900300104081070340040c4a041500c050704028156040882820903508450300a05000b03102546442650070b03001189200040000710340c0600724000c0e6181d041403842111486c801800e010500e0303030b541c3c58032000d5910101a0340c2240d580c5c0c82e115800900312551039011074240c1d55001500385d002c2141a40303001552030005080c0f040d00d80f070806220300c1c001041640103c05618010340380c50f2914a82c28a08142d4001005c1c5503100000981c500d841c1724001c100014209120744240d45814009404540e03054941e0f0541c0340038010203110b0940901502c64210041074095030040c2c0422511404460310030700c086034150400100c00d41545810000d21000c0c140b400300360100755140c0350000e412a0342140035002c2809032098 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 977930197 1250 977928947 977928989
    0x307020307020a06020f010b01080c090409140321010815061201151404110304032c220c0306180c0c0204090b1e040201050d0f090515101e 61
    0x41d40d400d65805820400c3c03240d113402019407100c02c00c4c008803c0962130403081400c1980b007030003824011000b808907282380030403000600000d001c213941c0c19a01030241000740030407080100020700c16002c1080301103501103001050704011380c0c01030344020002c0d44005200114003610751005500544103d501ca120314000005250250401e4040200c51252070240000c10703040340980c0c81c0300d40104480c1000368118011a43d84117000030360b1302070001070b4842d00d00b0310b11034030a60702660201a03601d854076540401c000004c0781015080c0c0d00c681900c2d5218042507400c50725019180d1b0350300c44c6050a000700c4d8206403128030440034071184556000e4a9450540c00180920020030714142c010300103018801d010705101d8200001070300e0940c220007a02000b140030490040d0b1440c0160740c16500c0c240342003032404005016210117075080c202d05958001807000140c0412141011300512030360051540381808690080960f0366000e22074058a07100070514131a2654110b2064600c0700010f00e0780040703208 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 977931447 1250 977930197 977930203
    0x20313121b090f0c09180b18040606050103051617180709020a1701030b1f090c030506100e0f0d060b131a040b0d0210050c121909061202030702 63
    0x810038007000101c05004900300341290003000c01144103540900400c10384000844015401e0300c40c15078404202000e050744180c8580213011610002030403a0346101113000d1054040741e00351004c6035415541c010030040c6c7d5800d4051a81d204580300c2d00c0010625040740c000e0400e000c0d034020404080e000b440002c00d882c043c00150741500041c0400c65215640300e15911009510000300c80020560444141101020501125050340d911401540058844500072494044a041001649944200d0205905a0074814401e0700103141d900828242071840034442083d007000b040e03000304040700303600c2000750301c81c0080c0414001040e194102441c626003021402800c50028441d030001c040180c00c4c6058000c1d410800c0b0011000918a612042000421044409000c40d0750340040c07081203120054901650958003504081c140b4500d01102c400380c030b5080540c24003110881c05008a555100340c0a024100d82d003092850404145103400c2c80380190030703045c403803041c6811180c00000003540d5510034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 977932697 1250 977931447 977931473
    0x1511092202070b150603011a07060609050c0a03050a02040b07021c02040c0f030608010b0d0204090507050303030112060e01020a20070b03070314090c0114220e09070602031312 77
    0x1000c4110b48507855071521041250081c2d44102d45006034440b000307858a450001c480c103c41e225030000200180078192001c40e40c224203c00e507213140e55640006188641750080d170b48501c410204141da600742244000d02180d0000c5c010780161481800709114582942e412140704a8045403c0c803411880343c2009180c4900c54800250400d041c07081d600071081c3c000d40f507210b0000c4991000d119181c1c451400600703e89002012545c49081112a2005810160701013610b80c1c4c000c1040c0c80b5a10b4507840440e25580c0280c1c01182c00030391080602013804510b01c1071421040b047c0001f903107000002c0c80d00905031616200e03001c2413258111a02007000800700441c40080841d940070944a1810f2040a801060b20071044518401c0f030600162002c070021030600e407504016103450100c1201e04a00e040d02d03400440750500e82810347d0300b103202e500d640c034403a0340d00804071000c00c10582d203414481e0340d050990f01d92204080d503006110814000c1c0039982c9400545d0016101615051507a0400c240c900740c032 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 977933947 1250 977932697 977932759
    0x5090f071b1101051b121903050720010f050c03010810050c0a0513030c0e0f01090506012f0609010c0e030303190b060d050403030501031b0303020619061e03151109 72
    0x41c6c100404404401c22018144030b19000c040b821401ca400c040075070a81d0021a54100010344485582406030310000d591914024010000505444040d5a800c101ca0044d04c50140104001c00104800c1c0f604001d480b80b200c00030719060005042115250005000399005c1009110001c990200400e0060900300021078000010b090360903a1050b44440031002500c403102442d450000100300307104c89005460180d00181d4130255500c141c0b140040c82032141c19070300014801c12907e00d41034980c04000c000d0080d25030000000300090301b00006080c1265100d80a0f000f0b400030300801031010010300303010b00700382a43e03800420051034900004200e48909202403880914000a00c01450780c0b55000324140c9100e00040801551134507618940282584002030040e40060001451003406c1c60035007001e101d4840300400c03101d448100c009000d804200e4442d01e507a25510303040046c4070122070681070070b00202000300410800e150f1840b800d441003100040c012220402c100107250032070f14444900c040 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 977935197 1250 977933947 977933953
    0x30601030804030606141003050601090801090302060f010f050112020d0908040e0411041b0c020f06040b0705010c0503101203201e06101e05090f071b1101051b 70
    0xe10380c076007449150400d010076100c1c84c0c50141c0224503461000c40000c19900000c003c00c400901d203410440140400a0010341040102c820000f000b400074080c100c03901d03106e500604014a0101a5502210b405a10080d21a18210000c2045903000000868868408040540d40b03a044100f00406041100700003000a640020001841c0140310b031124002d80c0f1850b910000240410100300990f000400c00200148a590f80e180c03a43e0b0048280001c034502c013600d007040842044002901c0368215038020420320000080b4241085028880e00d214003240c3d00f03200741541084012040c203942070303000d002303d402c000d03507503201c00e050088520340e90007002c1e540142510700200300c8558844880d003000e4000d4404400080050343c030003094007485204d4921001c841c85140020f11022500345088010307460360a40b001144a40300d4950252061100302102c03d418180740c00c009060641ca42610610800302750100400242d080102840300f01d804d18005444280114025540c0e102c04107480420b44 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 977936447 1250 977935197 977935199
    0x40b040506100f440f1807080a080a0f080f040303020d0e01060b0a030606030b063004061a0603040b0a110c0f2d0d0c140d090e070c03050f0f09030601 66
    0x160b00490290703000b04040003070703400580e01301d05100c0c6136540a071050b42e2103244400000f800214580c02c0d00300710174940d000b11507105a07200705140c2002094101620750b42000583e4480035074106a808a181d5070626108a143c03422807004e1849860182000b0308040d0009019501c1589641200004400703020082100940c2c9802e051899030040c10600042030400b14005a640d00078862605003400240541d8548072200c040348032403890803152041c1070440030000c110015158851248a00d201d00c60024145135251524040d181300041c481c0d00c81e480c1041004005508288a030f6004140da84000c00d0094400030404014010940350030348a100340f61160141e18400280483c0d07198001240361030807410100e44034815400341500f00806e40c04135480d095450310070301b07000c00ca140c090780c00c5400881440c82030a060442a5090354001660a4411310452040090454002c00c1505107041c203682c0d40c0c0d40242050044186078904d00c80081640c2c00c000c000082103a144000040030b4407440c0d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 977937697 1250 977936447 977936507
    0x316080d0510030b01090e120a02011b05030f0a0b0d1b181b0309020604061b02060d150b03101e080a20040c14070204140901020405040b040506100f 65
    0x2c40c0ca0b6102c1039501ca11000000581c0224074491b81210792290009042e00e1400c1404100c415030050001908665032441c000759075140b032050220080075141d07206940d9042c406400760940310040d191004452428411042030381d141d10004068070f41c0000c1800741401108403031100c81000b5404071031820881d805403101d82e1210b5124400668400c010341c2041c1c00000821404c985074000000d4106000704401d02c1035900a04020000d0060b400003802100320540c041201c0d40c00550300d005074a0307201c040700e801709094890101c014007400c440c05802c501d007030850380983c0d00c0c0f14411009400e64050103000c0c40c0b8034540004020308801c00881758400c005107804520203048543d01c41c1900c0014984032440e00d094094074443c4905aa038200300c03c01c081c000514140d00070f0204031b0b0b0007a9640c0c4230100c0ba41402001c0d610501b40349000584481c07403c000c0c070044d01d0b10b0385000b910841c90130b0100038036a034408059840103092031411540c100074030442501c6441d48251381c4011206c0322880c0c82c2d15 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 977938947 1250 977937697 977937721
    0x14040902030f0a0c120b010513060f0f1401030515040e0f010504050304030b0c130303140714030d0605040209060a032c06100602060f0708060625030305100303020316080d05 76
    0x9480c1c82a151350614580d10300803a072400a40440041140d0001001044280703000a10b41c4c22850340c0d8140058440c2e900e4070f081c1c14014031913006840b201d108a4080101c00c2e103601c000c15841000f801e046c0f1240c42c1207001034004200340140701f1303c91a40c600c01030020980c20445c520480c2c040d080200302506142c01c2443e0343c0d4101d40310484d03003803407080002241420b01109079000a522149000c900506503a8140d0749601041c00300c245030b00c0306009900110301a415424207401940000d180c1d52129500b1200545d202c540165029600400156201d6265041100e6080046107000107002d0b198158550031010480c00c1115481c1c0204030306502c401c00403030782c14090100d18801a990940e1000203a031a440c0840d04902c5a01c0f441c0001100c0d1801070400715071100004042038581030710f03040b03034101d2011a003422140d40401f41440d0300400d40c151044e03580264217290304501325407660350000d5076446210f01c075a103003441e42e08100080050110942d070660009200500040c070701140c40ba10 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 977940197 1250 977938947 977938963
    0x90b0d0218101202180d0c031221050601020a0b0406020301051c05030702010c020a18151d070c0c0b0705030d0f051026030c030c1605060414040902030f 67
    0x11401d0400a4041841c00d0140400d04000940300c4440c04901c200596000790024611003504030071000c60014141c1e03551229488092040589603900c50440c01c11002c0da0f815180d4107000d0114010001808403a0010024048191040b0114585c0c0c0c9a00040342045070001000b00482c0002c02400704105158001c0c1d81030b0760301541e52018180c950001c04038800f901086c0581650020040300b00036511404018500324005080b01040e01da580c00014240048407032a500416691b00e804200400d05c40380020080940002d0031502d8400384c0c8440304402e0000c0d09000610007031100603002c119510906038010030400c0e03c07a0391a483c20341400b940701d90144920320851441e1a048508040103441598064100002c000305154141090400c00e40c002c01014031500e1018004840c1e024802c20040c5050b2012030040c0d5144c000d440450340ca030000c4228105000d00300f940060000341c60b010203903012554000610080b0030b0100b030100d0014640030002a40500807002140c08001000402c85 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 977941447 1250 977940197 977940217
    0x91e0c09010b07050c06030601142a070306110702090f0a0f0908033301050c0a0210020a0203150f06010804020f0409060b1e0603070c14011814010507080105040c090b0d02 75
    0x5a861803145c1c1080780030312048694030b0104200c03502c80c881230f2200101818200030b240c108810014458111518210750f16180054203500204091007040702a001d503920000e168094a42454902d9002032209800244401c2e807242101d0000741c0c001c021070704a80140000300b60304105090160418400d40d41c01100c0c0c035484515456090415240b02400d06401c005a545400100c450518011100307a80030311005c0c0c91520031412140c02684c4c584a13503d00b0030341603800500d6071620b10f00c185400c0c0b00456980118107021402045041045032108960205003480d1400c160341e0350340f0010301840b22201c10240c03c0b41c907200a41e4100f00590f8450b9a84805c200ca122900c11129402413042c1c5499020540d00200140045075849000c0c0940070003075807250041810400c48a03034001d0856046640d03000034081e90f6016081408101502d1030103a1540100911084c81d00d0343340917221030010b1080030b00456486105000140c4280c451102030000c0c0c45e0496601e410034003144010f9007180e0308003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 977942697 1250 977941447 977941453
    0xa032007030302070c06410313020306070c0b06090402120d170a0207020a09020a090b07060c0e06030f041104021c02221a030402030106050d1203060905091e0c09010b0705 75
    0x171403c0c4c1d0003050490000702840312004140184e00300e5000e80d199900220030351f80c0c80380b0340000710300c4400c0c0d0000c0d51017010100c0304034010140354010540343c40c01c081e0036401401252908000480c0c071484035281d0165084d10038030819115880030a49110a01510111030301603c5103500f8869030040a05040b03c004401089a686030500c05104038450004000e43c8080810810040c526507500649060059414800c20803940c03030200300101c0d40003181c220741480d03403070301c00b00005604a600d119100c00140d5009095207070032a1032500d035900150016091407504110800150741d82d03012200900179441568400207616042e0380082e40026802000d0100740ca80c1c468002401d803c0b5500864000c2000940840c90341441043c0303030303440908180e8165488000200301500e48090482905100e48006550540d1106005088440d242c210409040c1060300344100b4a10000c0d01c5800f00c0310300b40910000100030640f062800d01616029500070020f4000000c000f0440806080000d002e001a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 977943947 1250 977942697 977942699
    0x603060c0901121d0708071d0f07050723150c0f120703090503070f0b0f040203100b06040302151e0406020624040524150a032007030302070c 62
    0x480e4580212201c481c0040c40010700310922511680140d00e64101c40600302c0504041c4210070740c10951503810514181e400411b0401100480207803050181421003030039209410b2046072a40115000f0300080c041100100b081424080f500159003450b000042280041c000304045e090b48448550404020310706a072350010f1500e0305000103c8a0701078404441034034000c40341c8135181020001070054002c0556540c15480010010030080802c3c038041c054640482c14580341c0041c036108020040c841c8900781c80148001030b10300042d801e2a100c00d55001041e250b9407070022130f41d24010369101950244c01c40e0b0406030f05003e80c40040c401c9901c44080d08400780c0760383c0000200b5100754410000141d000500248000810b120010301c180c00000c4640121032500c4002002c0d20303410340c3d000c24074014100d131199041900c3c20f05642d4a940558001403488849529a901d50080d010110706050304c603903503d20607240103562003c44c40480505240c4402e080d040c0200290800c040440d565040004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 977945197 1250 977943947 977943961
    0xd0b0603011811042d05070918051b07020108010303080a02120103080c12040807150c060c0e0f0a030308040611040e1e13050c1e040204140312090d1e0206030c03060306 74
    0xf042c0440c5c456600c1d4040e182c01402d10100c1c000d080080c41c40003089004240070031220001200369080f41d8400b84046203d0030031482109201c1d40f54801003440c00010400e400040c2d8000384007504403501402c2c40042075030742d0301250001c0c1c0304082440c40000d6040001008116801c0c1c06855003406e410102c8010001100300208a403059010341c0e500b95000740c10070081204140d0f1880c1c585616880d0805581500d0751f00d1601b551107803aa048041080200c1410311030074210701101800d1000c4850b80e0702c81c0d00e07544014104101c00b0341f000d00079580305c0c2c0088030f098000c07a048038018418500100d1076454503048140703004c07800584000b8030300d02e040d000c83d400c40e00400507020890f4000000d012440300790810442854010f4546030380300c2e802d601041c107080e51944042c1c40100100c030801c204440b000d03820541000b00d44020000212014081110ba03030712121000f00d012030b0711030550990240c2c00d0f02c4601041c07854840081d484500003040001d80e01d10740000e180186425021101d464480f5a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 977946447 1250 977945197 977945231
    0xb07140606010302160f23010b010f0201060b040b0c03090607031206140f0118091d060a0e0a0318050a06030204050906101d011e030510080601050d0b060301181104 72
    0x2c01042c024030400061402048002852000b8070340305031107400900e81210045100080d022505401fa6552002100010b50f000000000d00781d00307500c001c012440c100000e003401030245009411006001041e0055001d008004131091180c00500a6807580c0d845d00e0010403801e002c1000c0208075040003000120f0110a10b10500000c500800b12203a01c00c2207030045489040071030500302034540b071031000600d0411303620940c5c20349516803982444d205808401a482c0183c0585070a103030901e441c00c140c43c010b2001c16014910390b4940340074600306490014962040700e6175044180d0029030710000044540c0c042d40203004452042e10100840c0c0d864070304001c298843d0031214170100c3c06501c164010032203075020030641000c05040c002d02d240a0000c01c1c0e11021859003040000c03950340e0082c00f607483d4402548600900d4450300a00d0103605090214078040c1d00c400000b40700c880003401281c0199001c1d004a1100c02002845441005080c140748001e82c1702c40c1c20081c0aa80341440e581c18040c418 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 977947697 1250 977946447 977946457
    0x60619080319180b1b031e03061801080709060e060120030f0c06091c050d020318190c06030b01080c09010207030206030a020a1707170c040b07140606010302 69
    0x81005181000030751590740030a45040800b54003005249480c1c01880e00d0100c00c054050603007441410380f00c0780c071051709035042d03811600102c01c21380c01400522101d442400b96240c2008801112075202d0701e440340841c4c1481da43c540d00b180305000700e20005c190301c0303030010710401203c1c101031082c090b466507640d001d01c44010a803841400509000c643c000582c8035840480072400105e412607103042c0d40b0f6103c0e00c6142d00b0900242032203800c0003003442004001002280c0b11211028281003030701c01c0d4040c01070054855415081c41941c0c000c00040e080198110120207100101c000740c6649200c59403d0f103940d8000303c4001c4941808225000c17404520030f100b02c075040901030b16441840d4843c4925012a44c0013081101d04621488401000503214200503500443d0041d10140c4c99201d5600044d054400741140d007034114021004120b82503500600c501b1b030320002980c010040d030320341007003c0d9110711990b00207404001001030150100004846ca103000c2c030040d03400ba00c410741c441c140110103078810 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 977948947 1250 977947697 977947709
    0x3050f100b0307030c0207050409030201060906080d0206280e030a020607030203130212210408010522060e1606050c060a0506010e09090307020a0e0a0b0909100e100608060619 77
    0xd100180703c6034002e6010321840c0101c1e00449900640d01c000103016104e50000403801030f5180c0720b0801580078540503103c0030700350f014058540030340c0c0390a0003559a50010007500c92901c10810400310402950050b10007650100f4052100701c0310400d14607aa0360104900b0f000510450300050185031080c42a43d024500030469940701032250b03001c0120b080c40d0210441614058511200d180c0010803030080c04031131803684c0b002e8860340341001f83c030300715403004100841e0040c0040703c0e0218540090503040d070055100c1800200b20403030983c0c61f40f900c0100640c0081c2031015100102e1803a80010142c0742201c80702c2c00300c4000341d650300a91815184140c41c0300303021a80c80110000d091070903500760395102041c0c1044a08101458000400031a0594080401208680b0501003000098040e41282413000e54134010b1604203041015030311308030503407074030050340d500c0c001c004061205000101505034059030501c4020340300c908035600e071001900e00c14859801d511030984004070305255241240c0b2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 977950197 1250 977948947 977948969
    0xa060e01051207080d03060f121104020c030c0f0c041508120307180f140102030304260403051b0307330e06070b06010305220f1a0703050f10 62
    0x4602420301c04500000b4181482c1400b8100000c40c4005003080840c5131900c8641d000300381a4034000c07990301500301a81120304100070701d0201d100814036005803030291040c1990010703a1510064480c1c1e045000e1540e0301c0700c6c1401004d1900c00c020303000046116403101d0480e410411200a25110200350903148512280d641001014514140d600005540e20805505003000052044045000c801041d03400c002c0c00012104418807006507400c0c04a4030803002800110310f1170806031102484c250140300700000020328840c41400801036002582e000716070110481c0c140d040c41d1032080400c1d60f5071034603e0f802481811400580e16101074003079100d07220000209131a0381100340b14030754008126684002800340070110801252505001014042c0c01403800d40001e050500c00102036400c00740076840016441c207881c02d901400c04401c9500c02e5405081b45d54609000c2ca460504143d07008150028081c0820801190f0341d01504400c4c8a144c0d540c210015039951503101811100040c00f600c14100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 977951447 1250 977950197 977950199
    0x1f05150a0312091706091b0105030402190b070b040b07050918060a031e1205030c0f0711090103240203040f320d030f110702450a060e01 60
    0x1a00c003821109201603d1030715500f41521865562030000c074504010000390700510030002c4140060040104014010300c2822010074100c0000340306000180010380700c0c8004d044c40d07000c0302c95508921001080b4440225842e031170182015001301d07000321002ea501c495100005440c02d4461b5003111203080d0000c020342100000b080c251528000024102a0000d201c083c010021400403c113542e900d024200c0c42843e041000d00d08640502005500501405024002d21400346d161105440038500c04100c0b49440e08800d050495800d4025500150451138150020040c043c001d644800a4000c1918442441e080c2440050803440100d5014010181414040c000510145030103462040840b402c443c0002c002c160916050900d8400548140c1c019187c01804503098000c002d4039069100d01009900c0442030100c0c002d203d0803000901c200b5016210b40c4c90220388166501e8802810140c9039005104403600c0f005001c00760020441405881000462154a41c003961081e580120103540705130b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 977952697 1250 977951447 977951453
    0x110c0604030c050a02090a0f150303050a0f032702031501030c03020409141006081506150c0a0c060504090b06070507090b0105160c03020f0d03021207141f05150a03 72
    0x120702142e822100360260805200150341c0300340080340562a424000240e1030741407501c481c00c440e1810401d200d80080c0c94802c001180d044030507500c51001c60304040101504c01c003400c80003002a0800380801d011300b200e00268200c41d91204400131882941202d054801d140304008000b98244002098902038800074001801d19810401a26200f400034810a0703102c600054107291070f00b03041d001051751b00c0c401002144402c001c20025145000c800701d40f2403d1803000300e171001c0d5a83c9070780646090006180047c16200300418054281c00c80c015407541600c490004101e0b91092044012150801203640c819103400c504441445078050002c0070f80da4604103042015280c41d40070746040c0102880228580c0d0807400c003145090348600078806109056204008103204081d50700750007204c00c200703800002030300010008016040001ca0325208c20080c580700801302241c03803004403540142c0100000f442442c001d40e0205c1104a24144240e5803444094103c01c2031520095a10640d03414040000c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 977953947 1250 977952697 977952707
    0x120405101b0f030507081b061003050c09090c09070906021612030f020717030408010c08070f0e03071701050a270206090a0b0f36010e04141504110c060403 68
    0x60500c04d05009091044544030b81c2100d1b000504444604030050024003010b00e01842016403101c0c1c5080994030060954890796503456068001038062620803000c10207549d0b04102607000301c0070082c14141d07907240071a0024060a00362007588054030032081042c9465031481e0a04c2c0035215070b54820070580141da00c0c200e401c0d01c1d100340c1031070550007503800114100310114005d0312002480c41c015603480d483c1c0074102c0d003120b0138000c205003000551420b104890b9403140b4000c0c5181524904000280718840c00242441d81c02d0748015007295200000c841e0310503040d0051442141c0404003041440281140002c00c01122021480c00182c40e00300358005241010203045410340180148200b1070311520304404070390044980c02c144d43c5001c9848848010100b2401c01c0c0e00321142c500e120024441000740080c81c0801d01080d0503c1158004151140c56a90004054505603000640030b4100030038800d01d440850210355020740d0809106008000100b8100da4404005900a000715902c0c1e4404a81c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 977955197 1250 977953947 977953973
    0x70308071e0323091b040b0f061305090a1d0a23070305010f02030907140a030206070609050703111c0b0a0525020304060909200c0304030203120405101b 67
    0x142020310030141a00443c036400401d206540802c010280c0c0d000790b241d01c1c00258800d079a064400c904240072144c0c03a80303801c6060b01201100386e03002610b0340c1c070f450980403079020b650700b00503003243e10078042104145841d007200c070310052800e040360110014008515115642602c0c003500f032150b101f0001841e03080700c429034080b0151010540b400241c83e50748150a55403d1030b0780410881c1c01000303009110109110060003070544005d240f07200b14140010901d0030f41d2603c4080d1182c88081003910138000d65070803002000b94410309640c980e80d16031800501490b620603078036000c0e641d1108008640f41107000010445a000500440c06640c0c03004520041c0c100109100401ca03649003100c1c5a11071201c109a40018403a0007940c0c41c1da052000041004800d0340c0007410480c03c0c500150f101158404200c074003803200c048429550380407603614910350300c03d41c3d0000b901031103001702545406040d00c02500c1500c0048030780000c00929039900312203d6405029440c2031071680000030001512083c6452 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 977956447 1250 977955197 977955221
    0x50604020702030c10110a0804030302060903131406070f0b1506071e080f0f090310060b072310020c0c0306040302072c150a171b06041208070308071e03 67
    0x6c080017082000d5414444094011108124041401e000b05078061010680c080f403110010340c2020940340390358010747c46520030780b1b5070030007010815031a5840e8a0129581c59810031b03c1003103556400c0c0340101c2c040d5011140b9121094110400307490600e0700b8012942e0071600010a0080610120038282c0c0301c0503c510202c4050b40304000780c0305103845900141c00c00c050171485258560640718203050800c0703401001c012200d4039000c0140203040c50002034070126600300b840064401d2003c41c6c080922140701c0d02c1065148917801c21802c1200b80c03a002440c2c440c0040040d034410030042d37010b040c0e841c2c0064070014056000080f0620444401c0380e665a01004920007185401c04505003072020070381c05444080a141481555a8060030b100200300010090184150190690002c02c030f07072148a0580c58840c0c0d80b020810b8005590b480f942554090401c104802c01c0100062a1041c1c050b0b2200d001180401d0140001804080c0115003c100440101e40015000d10403650100c0c01404603141039 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 977957697 1250 977956447 977956457
    0x1051c061505040e150903040321020708030c030c0709180201140d050a0e060f01080c060904060f0902070309080c06160503190f14131205101e050604020702030c10 72
    0x2d03141d51035000e04940c0801100c0a800e03520f40d82141104810340090004080e80e1041100b0000a03004e0f4801100108080d0100f83e40003a194408a08081c0b641e030040030684404038155500700307404001000c0031990305084401c45035a903181441a1032505003900d0006882c104201c0c00b40d4050348200a1b0b001a107405039107401403404c1410216134050301c0500381555503c0c6071120000c41040b0315904241c0c003009401c869031410072090b581b4208402020b0143c200824018200d4407150050b0014110000c4d92402c560740b200e10860007900f080100f60300154400300c000500d804041100c0102071300c050040c52410500c908444699642c41a00b20350a100c2080000b080c1401045030107220780b100e80e14005074030f0403044000d29034400c1a55540950104004c80840109a80415001c0b24202d61000101c0401c80c1041030a010501c1e050030742250510411000f511034803152000c030380c0a002d03820080360301d80c901400304030b00032044001c0d00756000740381504807850611010900e041052030700c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 977958947 1250 977957697 977957699
    0x150406150f021501090209010906020a0b150d06020d020910050f2a031b01050a020405010e1002010e03040b07020a061d130204080a11030c03061e0703110313060501051c0615 76
    0x3c41401c800c0036403218000390f45c0424000a1f42da4840b280e0b100900441c8000c5c2a40005929104103a8202910104800341180f04642c0380d23840380c803003c5241541050701152156052407040b0040d501600009224901c040c0140a00030b011344281c40c4ca80220880030350420340610b00743c14201e01c000e501c4a0780120480f56400e55208100010301e45c08041c642d24002e0001c54600d00303801c1d18009040c01c641140180004d10007664860454160000c007141d1085800c800020180d0041207a811b24024500001801151030317214400100070942c4242c4031b0b010503541e2914110781c3c00003000c25180c05c5150391001c00329145810954900c192101c86401803034203a0310030340d044c54001040411030305104001440000d43c034090190b045c0d00d20003900548241c1c03030450050400352010f80b907111040080000451000e5200b648452302c144c880d40042540c0b03040980c0c055941c00110002142d0b030904140000c00c16040207603601218103120400403007081c005950b030a018000e812034490203c00f07800b00c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 977960197 1250 977958947 977958973
    0x306050703060f14011706030a0201050d020c0723010504150c1505150108010506120105010507030e041d0d032913050705071a040503030a02160218150406150f02 71
    0x50b100005104c082c0d40b03900411035070f000161244da40c01043e440f4110801041254580b808501a03208130340c240381c0150348200b0214594000d015030700c000c0100380311340240800d49104d0b03c520340490022404c015651641e0300401101d8502c201d0140124446003054401d40346030081d080c0d4044584110000c01c203086161a528003160021035049031101d555603495490707542c1040300f40340904410fa65451600c50000381d603100c5800c042c0f2860381000b900280d24405d0500c50018002d0141004000b4000005429104292800800800d00e0140a41c0d410388103410300074402c01c806003090806480080c100500c100da104001444459000309040c8041800745146226079889007a507038031816110100c90410310080b200c0c1c00044800a0480300501020803000010b980e070211101c0d0015984440e020480301d6a1501e6000003500300c11004201c02040038101c00b5a880340d200c28032072044c0d0488a500b003005442c2184240090b0751650124800703d103120300000d40c06c80c40140111400c1d420514 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 977961447 1250 977960197 977960219
    0xa051e0a0b150a05010e0d03300902040f0c0e10141b07060c08220b0c0a030e0a0f0b130b0f0c060c0405061602011e0903060c0216030605070306 63
    0x580c0d02480c0c040320b07486004545810015140509400e180820018003403402040b10354503010005420300082002c0c041c10420700c10a800c02d1606440c0c10940c0c4621039030001e001808110380c08a11980c20312803d43d00300109403088000f150f545559100c12240c0380e0051100000155503280100300d10b060641001900300001040b00c040d080108440e10706004400a00745150307074100300c042042074020711012408840a07180a003480040c09510303094a81c00840e00c1c0070385076000c0981d060012602d003041c46e00c00b0610300c10980c02030b10381e04849011201042000c607806d00695109a80744082440a2007816000d0980c4115200e45020103d8840c80c00c10601d8114115080459000207200a004182407000c0b94110803100309850038a420b140000713416020301c8044400d2250180284c00a680c490696591054040744be10024452145802001040d00d07001c1552001e0a2000b444143e901c00034045a2443c0c00300d070b40b074140a04581c0c90b40007408000e4025410951960000301e11448a8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 977962697 1250 977961447 977961451
    0x6040f0903110c010c051023010801140a05060102030409090f0c030b0a1a0f060c16060905150c12220e07080709030213020a05070f0605180a051e0a0b 66
    0x207600d400007188000d1660503e40082442820b0400ca11001c03400005400050303528081190b102c4085440e0f0017180b11404a2244818580001141d42000241440040d0b020448840136124004000d070b9903c80c0d0807007580d1003515080d005034000c0101b0060201ca6500140c00144507118a80d440c10f80303911444030205041c0c100380c541c0540c01d418400400c050744144094a41a0309540b4011001c0c90005441c082980c13000c203000340000140041d040e181400111000c06100300c20a8042392a000010026842c40c01458003518980003184c495009403401d4851103c4403034001c0c20000200b5611000c2e03a0848158014071079107080380760032071401503110174014121100b8801030a04d0070000c001c013600c00142244080c0f0074010303002d101684944c3c250128080b1803020141c0d0756486108110341e10720480c0c0002d00000440040c040030072250380c104900500f81240c224240f41c840e10001501d5103110480184a070b070290f0500018841e428041c00c80000228040d40c10b40340090305c03022020755003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 977963947 1250 977962697 977962703
    0x2b0b01030b060102100c0f0804030c06060b0406030e1f0b030f010e060a1a0906091e0a0603030816080609070e0d05010504060509070f092c031207140901030506040f09 73
    0x79250801c03046503810045820304a003000824031085683c95400b030600c42a06504034200800800002d00341070090885084945d030201003002250764440007010355030428082c1100007401d210b440c40f41004000342141c0002000550043c0544030b401005005004611010f81c0501449903030000d803a0003841455103041290026007460b03e08202004101c1b04080c101129902c42540c201029071a000d0786141e012000303a0780030310f03141c40d0040803960a800c0c0780404084121654204074a01e0080d400c004110b921944400b60652602e9142d50428840801d0b1200002c0c10a40000d00d103140c1620595000b5840d814014030031001e50004c94949844d031b141c1669140e44420900040212a10805a002443d400600038035030402e64a81e8689000d4440c40b05881d032103580c3c488242028494600c06144844200c0141855215600e03869030405415000d00c4140b48002441550241c180512490303010b00649140c40e10150054008003009010300d0340041d07860072807000132001449880c1010780 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 977965197 1250 977963947 977963963
    0x1a031b0f0415031514040b1303110d110d08010605190e09010b090f0102030f0702040f0b030f06070201050604061508042a090b0d08091e030d09081b2b0b0103 69
    0x130844074010998003200c00f50170b01c000c0c8040810010800801e0000d070008540741c42180b0b203d04d01c1c1001c45806820804660082c01a007142c1103415401c600e04c4440801840c0549a101420141c01d6030544800d2040401141c0c04100714a00303c6483c0c4d1a4200148083c01d150540d645148041030b842d86098100740f80c041400584030300030340351580602e83c0b1f801092005518021900c05010480d00031590021701407a1900780c0030003100000c1d0000840780c000038007110660704500c40781ca0b9031359400b581c40e20059464440810310500300341c028042a584a100d240d036aa00107608200d4008000401c06d0f0b59690443c814615440f0700306d188108841c07014501443d0040c00d00c1020402c0ba114003420910071580f400c00c44000038940c405413092440c085803d4069000c082c8401e0b1074030582850b4480c1d060049410380d041c9650801054000e66003c40111040450142c03c0301c03400c40c100c00300b541e6000c12030311142680803441c0014103481c1c5c0c3c24615814480c4070281d4604c00302c2142078004070b407188 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 977966447 1250 977965197 977965223
    0x6010902072001051b0a02090a150f05030606060d18060c0f0201061409090a05100645020405060c010506280605030411060c011a031b0f041503 63
    0x3020281800c080001000040c0d40c1c10b1a055001034414480e04500500b2900c105003c0c01084109102e020071350f80d00613080f5180391400c4100b03031000b00045602d0501401446030007240d0182815912380680e01e0180042400341c90300000c2010302e0300050122502e4545801181840a07034101e03801c46460b10035070340410071042c8010041c050840748000d040031a07140240820a01004500d450600740c2d0541d000001910b0f040c44d01c80c20700c00110b4000d4074510454000b03101c3d0500da6480082142c0c0c0704101c4005030b03800112400769900d8107d94042c00d1005200543c94403d082d81001444425038800051074596103c0204405801ca8112460540d41d11420456a41040559030000c801400e010030b5586e10742c02d52415850806000f0740d410048084001010030072508120072000b80001d0401d512500d601d200103001e03007001880e5501c2500c03044003800b454180040c5120780081c0e20b008185162843c4001d100d17040000c2c0d00080c4d84540c680200440c1407a84040d448061800303680901e400c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 977967697 1250 977966447 977966453
    0x30204090302100e0c090a15151806051c0b12070609080d0201020705030f0705030f07060b04240501030b03030d0608060a060f0608010b0325052104030215090f0601090207 75
    0xc9220004400c0140c02c002410245c03540c0782c04034154407207581080010000ca041c4402422982d80c0e400881c07400501820036405150001c28440c0c003c0101c2d21001a00d90b1150783c112240d01611481d01300c40d07039160301c6041c0c844184e5008400c580c0c1300900a012948007001d101460b00140d50701500c0030413a66a0140280ca4040c8400b044e6280741c1d000a40c500300503030b5a040d41e02e10682a1840040d440480c904082007003c1c01210048580c100b0700685510303860134120010940c105602d8416407a09210780c4000f90905401c0146001c0715849190715481c001c0150b01a014040aa56042c00300704203000c1166560711030071001c0c0207004000d0a441c5003002840045481c10341010482040e146c504100c00c680c0700d03c155040d54035070100d05440751600d09010050801004c2c400510000e1030794072000781c5500401074108240c42030540118418010040d075816a0280c2e4080d0068018100100e60700c0003409007150020255801c0702e22040701d108055050403020b810480149400107a000700f8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 977968947 1250 977967697 977967701
    0xb0c0703020705030d090e1b0d0f0c02070f1e080303090d092108091306030803190519020a0c050304061d0301050906160215100608090f0a031803020409030210 70
    0x1500c1c3c2a401080e1044120300b01600040140c42407414070501000042c08100410b1003110200c541007030129102c0084c0d00512016054880102d90500d203003407849e15409100080c810708035160080604090350400007910305415400c100865020003140000800540800040d442925800e019245410180380b00614070985944400110107002141880c0452548071402043d0391005540d90380d60010b401240522500101e945409403610100000b8002c80d01c00851289200e120158a8005000b9014040f16403e440b801505881c48410502118240d801401e503500039092070301c0c0c1071000d580c40d54a10b6009402c03038800104c860010201c1036085194400751510110024400c13481c180d82040c0d81d412009082e8164002070790002c0d12410700a10065414150f10a4405a030f80380844103010070b03080703034480c40f4000f590850004499801c040368000300d01c5d980c140a00350070700345504d04480c030308040100ca01c0035240c503520010040c1c2d41d42c403903106803d210313070041e0403c00f80303003c40c15003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 977970197 1250 977968947 977968949
    0xf0f041e1d030c0d1d0904060e0f0109050307060509120414010305130503030601030519090b101a0313030e040608010e060601050a14161239140a0b0c07030207 70
    0x5007960092200c0324401c0c0c0c0116003070050100c5883e01740c01a00e11441042c06000d20496441d4108040e44240402d024207034010030615861082103801c4a030302030141074201e500d05034026265402c02d0022900203901da411003900840c203141206d56011108103c1102d650180e4007800505c25404481c04455805009131a0710134030900380c1054110141c0c4810707481e840010030a40c100b6982c2c4002030560b203404040307035001c92200740c02003100e140203150410b41e4600980b4a058100c0b50118005580b0584044032265038403e40440c2b41036445401306400e81c00341c41d101c21800d101c082c94590149850710f200d41e00c000d11000c000890700ca000c0c4601d0504005004c0d0000b8100319042140c1c0c5841a0092a10700140b444015000c6d550341032092203034024034091100800760b1455450821405600c8a0300c0124a03810580c103000b44000d40c040d07140407828a041d00724024001280d000042400c146051080e450441e0654904440c0d954948850540c101c80400c442d0b04007084513420700d50b04001200c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 977971447 1250 977970197 977970251
    0x709050108010b0f04050703200a020105091c080a0605030a060506010e010e032d100b09010905040312020d0e1507110604150e030705060112061a0f0f041e 68
    0x2c40569404003044c240d18485800a0056468401043d1414030a038059a0700705407400000480310004c0e0360706e605e180d204040f0b042c01903080101140032840c0c00b050754500ca000d6000003244281c0d6171303d8180c410410003030410b43c68503920303075000481d5102402020342180c07207500d002072a031404c2000940311b0a10503030181d041082210341540e1076280003402c0110f0009a1041c000308074a01c03a900706200340e01c0a00075006024050000c02c0407043c0d500815403249007121903d0840c2c0c0c848216608494084a0150014140c0383c9103151034400d60b4000c10496441c1840410119009402c043c1781500c0d1003e512030103001c03c07042203030196002c000c2003030b641f2005001c0c1c5200d0070552205580c0b1540e00d40501c1c45940e4504280002c8001042116040303544002525034569541e4494000e86401c484152403a0b4107003006042e41e41508004649084001010000c000e044070092001c61480000b101d174010741d90700f40708240d12606450b5040f0340100080b020a503840c12210700c02649440c00307102 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 977972697 1250 977971447 977971451
    0x71205100f020901020c0f0310020705010e070e0910050711060702060108070602010911130b1005030703050a050f0f1b04090515010804080301030f1b0b0a180b04180e0d02070905010801 81
    0x18030803a81d01060402c11b440d41200c090400c41c600702d00183c101440c2483d0010110300c002480402c003c4d064001c0404501c4040950368a990b580c8900c2c4180c0b581105c500d8070301d4000d000000c50f00205903214039009411403030a2154005141449403503d01c1c2511a807015901c0744004224031a0200705241c0985542e100a20522440d40d0700c00000c03103050140184212100c0b2101c82298601e41d224014901c030042c560020068404006003150340207403100e01c0002c1c00c1c90002100d92500d405814051100f40c001c01c1141e903a80c100b4010011006025201000c61801030306a000043d10042d02c00f43c07081070300006140c1040c407162a00204a000198140a00c8004010216200000340c0381142c2d00000c404240070340d540b410315484041d0b0030300c510785000d42c5131000c1044844c0780040c00d030501d2551201100400c0001d41300f403223201144540c00081c44108414088050104540714900d070580e0070210300759048503005401e0450a90711000103900c90340c82040500c00500400c0c0c010034042000f = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 977973947 1250 977972697 977972707
    0xf16050105100506071e05010c0f081e0a0b03150108010c12062d0b0a0305010513151503020c060702060610030c1b030c120801080c0603010503190203071205100f02 72
    0x824131a0007800e0000d40320f003410660303007480b010002c0c110b81c001d0b0303500034020005039a481101034820300560482000051010340000e600f14081c2044030641c40480c80c0541e041d03034418074021301034811640b0703a81c2c06000e120150702024001c420707000d020304007881c00820645403119004040851074002140344a040c90420030105580c5500c030303004105101c103050805404c94081020070420350344600003d0700d001404802c945d41c5036000c1c5040c0e0f1401c0b142800440309035042403007030356a00c81551100e010341e00c004118848501c220349802104904000d41441a11003107141803500440b8040056041031081003130620300402d8206606480341001c0151000f8404002c000c0c1003424616410340c01e2000c11070080c5070182012801c21a841010140c84905003a4010140724080c403804100e445400c0111b18186848070590381a990058018810404202c00300f44c0c0240040c0d4041e07805010714480441c90400c0000903c80c45401980107001c2158419503030011100c054001c4482c45105200f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 977975197 1250 977973947 977973949
    0x516080f040605090a0f0b0a0b0303090307060807030b0a15260114151b100902090a020304081201090b01020c090601201c090e0108070e01030b0c0f160501051005 71
    0x1922504690003800c00901c42d503402401034071700b44e0b64070805084840384001040030050524582d0b84100d14001040c030920040406156480c0518a20340703a064000c848140600c03031280440030350040151070049000320301107010841685094000c038440114550329010300a80040d154402c903090500341401d041c41c10f02c0c03044400c00c018020100c00e00113813100d06605903100c4005c500c00c20004595203503134400c4020040c25107440e09000c02c541e401140000b07145100c8611441d001c1540240880002e030307561180c00c4009600080086074403150920a10f1214440003604601a00f141c01001640340700c0d580c0064900244081801c0c440d4050900300105a41d10200c0040c000750f080e2444100e6440c05000e4604111302119580200030300d114110100e03e03801b1340d82801712484c824180141c1e907220580c0c592184444d015194800054100400001c1d52141c0569030100350201080e00700a512460b94140e940002a03500d980c1c10018129001e0010078403d1030b8014210b0f25015000382e217020 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 977976447 1250 977975197 977975221
    0x6031c02071a03010b0706020906190e01180605090d150903080703050a060f0e520f0f02032a0c0901030b0a0f0605030708070e180307200a09051608 65
    0x401b00070000c0c1e80106412203d40c075080b082c1c40c06a000c0d4189070001062000008116020b0742c041c460018030340d2001861009002068032096440710340d201440c0400c0301c002d209401f000300b0000c603190101280b1034020114503100d4800c5c07003031181c0d0fa4861709041001e001800c2d0f50000d000345c40e41d94500380040040b170f1802d03083d0701c044480d4030344e24502c6030791001e840a8000a41d01242d10203071700d6400d00c2c480292003511003031011001a01d18079820700e661500d50709080c45800400000300c3d00209040c800c5c90300540306521100c89a00c11689040c1c1804401101110400b070092411030845800c41d030040d0f0140903000020b02d05a50320080ba44c5035448400022001900c40e0b005c40c5e9540101c03a2241c68560840303400345c1406021255181e659915081d5918000c1c4a09242e5410003c049405403270351400146401601c00001c6041600c291540403038020122195581c45003c0b4001e503101e41c1b24402040f0060824850002d2685010307a60f03903500c0c103807481403502005007042c204400440c0f40303 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 977977697 1250 977976447 977976457
    0xc08070f0501260a0c03140405070515031005150f0a03050402040f0c12021b0601181d030a1d040e0114090d051213050f010c090510020d030506031c02071a03010b 71
    0x101202061101c5c40180942c02411006100d02c51403407018100001d1110000d451400c95800380ca08001102000102f240c207400199628180825080d40400c1145403000103c0466440440114030b0702c00307448418a042d512140040d40460b4031001040151b150611401d50022a60a810701980e024040000d0403420001c104021240d40400e0070645006143c920492896142c02240c03082c0d40c41c2c1440400e1a40c0a0010032660350414989070a01c01030841d00c11368140444006508010708032000382d40c24000581d9801804e0b4002c00307000350355038503800342915100c0e02c0e100006003024402920048044004c10300416548850380b00e0141540c418103d409280705403da80c40140c8131040030030b2008040c440040c00c28404c0e094085801301e030651102100c0d14503516640b860640c3c1d41c003801b020b03021084074900581c0000e540500500d0103034200d03581c02100201500c0382d0380c40c04182240e407586011100c4005038014001405100720740c01e000f21549400355109400e562401a40242078819 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 977978947 1250 977977697 977977711
    0x10b010f0302071122290a060914040b04141e06060405040e070b0307090e0915042901080a1109060f100201090f0807022d0103090c08070f050126 64
    0xc588a4601400d00c03138000b151700d011841028080700804217001420801525425421a5070f01d2000c50303414030b800c05d5004100c80381a2102018145490a44da22103d03120200d140c11036181e5460280540e142d210b8422501c1c0504910740c00e9040260704a843c51404284481c3c5c3c00300500140011540e6180c181e07421550202c6001c90f1202d000b4111030f050460640c480a1907940100900c00001d40281012054940e4980351182698410f13002395501c4246980001c9001c0c540740124022603c15003400461041c0c4c280c0040c40c00c10f20b100760f44041e46c401d9001e110790b5000403c0c04402c10106409509920708102c0e1001950300b23040000401050100d110341e4071079060440e600302c42034000e4002c402c90075080030710b40d00c0c090560b0a0050660744580c008900c6000c211b1041ca021440039003000410401c001500010b44881c840190700421381c00d0015554601c041d100051074600810040c00980204101c005e035041c6403000140a06c42140141100d0100c5014030003200302648842c5940031003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 977980197 1250 977978947 977978959
    0x90b0d020705010e06011806120303020306120a080d0e0106080312070908030a02031c0903122d0f0e030a0f03020313080a0801060206010b0708030411180108010b010f03020711 77
    0x501604844000d11440100400c69420300b4482d5030b14100115031141210368008000c5900d076040f411260032151940102d001e2480001c2041011901c45c2d0302560f440070010b0701000c890f00341114607629020824400b20b501b440d0004079031201c041103009920b062030407040248000c0c1d00f48490282c490003180c1c028030010b0092000614135502c911101c0000780100790070741e599100480c000035144d070700482112603a0070340003180d0154071419116112400e500342d642c000382c042c04c140013040a0600b10866060900d40e410030794200420100d5600c00000101000061407800c0100b00411b40321102006806500107004009001da00309808006500f810b2800580c1c0e5074400b031840b01e020b40141c00103025448080380c05421213821101182c16203181c1c0e02212070300da0361145042001c0c400d80800803c409010b2004c100002d0a0702c54110408400400d03c0c0003404520714400c072410000d9006c8009607464610042c041d50b04482d5601d0030000614040d40350071059116002d07181103c0880500404c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 977981447 1250 977980197 977980207
    0xb101e08030f090a170307020307060914010f0e0301020d14060901031707051f1409030406050a1b0f0b070f050906042c0a0e2a10050f03100e0a0c090b 66
    0x756071007082c18041c100c2c280c3d080405d000f4160050760f89400040089000744a41c21300410300e540540b40d1001110004402c1d6403660407100011585080d0303a150460074410305040c1300350a6074080c00501160800d1400020302c0c61500039080c0c2c80c1102c040d0550780140c0c4540c0040c00810714132113141c11580001d0010759510405887d166181117040c032f01c0014201444e000d5251800000c0e04240301c40c1c0600301c9280d525488a1070519201d116510a10300400c1c01080602d4280b03014010b420085003403440d9040b0f20344119210050349004640c000c90340c51040c0e2040050403070b0841c0d8111a4407149141c110309080300c15000c52140d2065014040f2003420388250400001c2d0600281c003034403c0b00d20a5801e050401000c500040c0c040f41c10314840d5070184010020200b4040703c0c4078481040400b9802d0002d43d000414841d80000510303103881004002c00c0a9028840184015405a509450540c2815107802c2c1d552049250290121020b6070500118150180d4407003800419135140c0c00d90990741e1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 977982697 1250 977981447 977981449
    0x1207030311030f0612150411132c0102090a0803040e130201050904051513060603060e101e08030f0405092d06010225060f1115060a030b101e08030f09 66
    0x886c154000f100c00030840d4100001c210700e408402c542100280c400d04510780604810100b61021102d560800340c18050740c095903d17400410f45c81218100000041c6884458000710705541c0c61604403078002d500c005010400918074500039a07000000a10260400c0c8680c1e00081581c80b070000400d205a444901040041c030307450f0b42400c81640300500042200e0581d28500001e80075512660010902d00200040d00c02500f01140e886008100042d807202406d06141100d0300040c04824004e080c601040801e45490800c0240f01f100132507100262520300d8403040100f40744000748481042070480908000c0c00092015070b403145181c45410701000e40d10080100e1800702103090810040810701141d01c40200581c0c00903064070324903562011a034080c0c0c00c1c00da500e95801c810603442d0707a0205010340e000740c0e010341200da00a0b0004203000c0c003480e9a9113030b0261801c0c0c10340d2000c417980c450610070400707000f4001803401d440708500d55041c03030740b4130340b4038002d40f240120741d600206ea0f60300107071070211 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 977983947 1250 977982697 977982703
    0x1e070f03020c0a0f0212010608030720030a080315040b0f01030b1309064502011e050c060714070204051803040806160c0c180e1207030311030f0612 65
    0x101c03203202c0d021980d880708941040d903e0300700d648000341e02079444813201e401200418003c3c0400ea503004c1000b1894209035540c2e98103c000c8000c8100582c0d500c039041e200b810399051103500e248501410005840303060407200801c60a100450701481149441030840710354071404441c0449050134200001c10108070404038042c1d82054000c0e400a0746418101c20401a03543e20448083c50f4260301d40350540d0800300d0700b15021100c4e4142caa010040100486106800141034040540c4107240620040382030210310706082400342039410200340080350705441d811042114550001051900c484c490060b00075100881c030441c48064000c940310000030b101c07a07080c038100d10000803100301121f80d900c0d9904c031425124a000d80d042e5040200910350032000303502c100f4a0100325a000404003401c649421030986841180d40c41c10800252120600f08004405200059a90106078003142e9121014a4014111807441c0d072540c99100080c01400206180c00f45d02550082050318061a20906003541e40c1c030f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 977985197 1250 977983947 977983957
    0x905060328090c030807060e12030702012a1b0c0306020c10020301050a06050c01090f201516050709050118050a022106040605271e070f0302 62
    0x1421220020038492081d03030301c48105003001000003010500200c071050850039100740c510003810030103984038280003282c16400105078103131240100141000c60442024288140ca5059181101012041041482c3c0a00880100010180230018049400545000d121200d0703c01e46c3c00700b00000c400903d907031042c2a01c0032000ca4000c0418110300c1d0b80c0f882c0900181d84018000131a41c0030b801c0864100c1000d6009580c10f954004000310942d5080400860700e5800943c4a1070305507480340040400708004003040260240a0f030200c0c0c0340180008181d10441040c408010f0140300004e5000c4c400000030b00039213002036002c0e0034900a82d111414814940ec000e60003036421103143ca400058000e010380d404540884040c1da0600481d503a00350312104a000340c0d4048034001d031143c90a042c40d1046074510540c042401080081d0464584000c04c0b50342d2a00700424aa50790b07021404031113041b4408032a0b40c802c2c035024012440c901045840c0c108244050482d40c01d110b010320720070110a02940541e0303 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 977986447 1250 977985197 977985199
    0x61a10020303061503090a1e140714010c02040b060d0903030e1f15030210020f01200d09021f0903060f090f030806030106180207020f0102061006110a080a08090f0a0f120905 76
    0xf140c40c91340000e2009222048c5000b03c0f50400400d402040d000d0012444004a800d40c5480d101403d03901c0005641c100d0780c14004a074440da41d00e41c4401142c0d100030103000b82141488002802e4190351401408940103040c21001940c05028000e81c40c41c01a844041d19800400001c507802a0794105566524400e4000943c8074404013200607a103580018405910680038009010701082e01070310702c410503210ba00d1003031840400c001825010001d50400c003c001e20140c164010010315501e030f040a20100f080e0b10002805108040090198600030003a4150245204100601070344d540c1300d451000da000000c05100c2003800040080d5801c0d0310120003420800d4580541544020b4890000c0d401144200e2064003c47e18109403544001107481c8200c0e90b1040c640c038524100f101c143c40d07141211424001c10310501d405a0300003102c420152240200540703411019040403403040e428918001405050395000c01c0804011418511400303904581241003400d00300e641100443e080e4106802107 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 977987697 1250 977986447 977986463
    0x5250c0e070810050d0b0114130c170f06060306091f030b0f0a060308040501140d110a1101020c070605030601030b1002030c10060b0d02090d061a10020303061503090a 73
    0x41c01c41e4001003072034456800c1400748600740341c0b103004110220740358480142c280c090020040c4440c07014003552200441008002500c00c1c190301141d0020303280d480103030100281400c4008524020355070090f64003d21003000d2034a19150900c0401c07580c1c080148064492103101c80410b502660074051149851302456640001c0c60b00e0741800c681c0d01e2010f0303070034280400d0144002203a24906101d0481a01e5110000f0351516280c4001110500880c00d07640209a10030083d6440e200c03124407501180b000041c2d0090303214808100041d0001244066202e4164010840d020007040301058401c2950120300708651207494600040300284100745815800220b8682c0c51981c2c681c0010150038407480100c100c4069015000242e41903031034070700c9480b4400700c05021807405440142c01034281c400001d0700214011025499580581b081c049901408009580b815891428203d1710018018028001503165062000101c0c07032103034100341d840051791008004180c40b01024403400bd802c1d9048810 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 977988947 1250 977987697 977987701
    0x1b05161a0f160f140106032001090501031a2d010207060c20030604050604050d0f140d0e06070801050a0902310506040308030f010504060317030c040e042105250c0e 72
    0x54020302c0c04d404180c0c1c0b000c80e08c58007ca4580075030800e85e4060303981a52000f18081c034040054008d003210a400b01d900c01a91030801041d900c070006200d05180d50b1071501104812400b0a40b4a040b010090a604641154005202868000c039103c2d0403517070b0001101c2c1e84980100f924480c1000603010140c2d25029100520007403041c001121801140500203884920f0650101130300c248035080320300800705115854034024010908080c000c00c20041c0004222901d1300b00b07080341000011291a0041455000107020a0614010030009441b000c03104514140805043d0369020700155112403da1075809150384a006c1048507100050002130107a40e152a100e25005c0603e400071203a00312400c9001c00001100d00e068003035002240e0700540c4403111395a0510300d507412540b0080401140780c4007004005007812110001d580320b68010700301804d032500d4401c64158492102c62102e4108201840000003a61103c114005405401c0751020b0013000c541c58020342110300303a8030a038441302ca0001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 977990197 1250 977988947 977988983
    0x3011514040e07090905013203030301080f100203011d060f040e01020d1505150f191110060b09120709020a05071707121b05161a0f160f 60
    0x240e000c1c3c2000d84581041035190b10f9101c04444d0240300c2d010282c40034a240a4401484803078060070b901c03401c00301c4260540044042891940281c1c41400c10394000060074008c010b007841036004207900f2490079441d44d4500400015484a0400c1c1d003164060404d0101e09284c2d2140030703415113641c0140c0305011341d51940a00034000d4000f034490071419800c0c103201501c489070f0b00d008031040d1070008190350341402540c2c0302c1110725001104079180c00c00e810481c0c59105200d11104400c81c15095440a04c000c921113001420001524160741c1140d04120080c001240c01c882035891020044e680307155039416901c4664a4519194070190100344000340c8104541e60010080c40024015a03115a0080c0c0503400310010b4401c0c0078000e41b01014543c4400c0482d4400c04410103580020900303082840b60079101c182c00e003034080c0c459010380b00c283d01041120390048444070134000c03001c240e21820151441503c010078800e854401c0d04d0003031000510400c0015580744500c206820040e011409143d803d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 977991447 1250 977990197 977990219
    0xd0e03090a03230111040605090a0b070602040302010f0e011d030a0b0907060e0a03151a27150a0e0a060806010324020a051c0e0102210903040302060301151404 70
    0x1c10b40002544003182d0a5183c02814042c11115400800d08549840c1c03520808890b40c0c2c01c20075406501c814002000103601d5010009818801d01442005039030310f14620014050300c00e2901c4090038444580c90f54140d42c0c0e080204840d80c100382100f510031800450000905002e008000113040c40b82c98800d0001000000a04074255481034440c4400b2071000300800000c2280ca1000425000500c542c1c0941d008403604000c0e90801c4501e00890811030a0000843c00d848102101c51701c240c68000300590b454803000c6441d001482074030f01c001e004046a003c00c80b9030455004861409460402003008095954065801081424243c43e4696142d10301034403103c441c081c01007016059002400f920310b102d4400c0f41d40b6040c0c1901d42c5450300ba446010903010700380013035501801a42c3c440e1441a42102800100a125021410441c8d075014251200b02a03240c043c00c0e060059209010a100585038107080341d054800b50307504141010794031582100c6a0b40b090517604d42641000c900003450704186 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 977992697 1250 977991447 977991473
    0x91810021b0c03010509031c1404060b210d080402060c1e060f070c020d0303060f1e0e0f060909250303030b030606130207262d0d0e03090a03 62
    0x404142d80e0011050360426090b00c80541d001c40c01034204010280e00c681a0515465403001038010124502103400e0b140900c00d03804480a4030b0f542c1c2c84126044640c03519240c50b101c0300c00000127a21b00c440146900c140c1d1032580041c0d003000e114031040850107554804c002d8031001001e08017200c030341c55031801c00140c005410120b1011a4403581020a0006203101d400327a1050714280c0d910074001041e5000c100100303584034401d5043c10b030b80d400080368000141021700b001d8107441d1072000c200c0d60000c1440c49880003550146c5c461080344010700c0301d50252f800810350420f80444800381a5162840f8041c1841000541103030800d060010f03403030030071024160160850f4000e80301007061000000a254480b0800c40ea41ca50001c0b0301b5084c001d90300308581c080c00c210740c004d0144966141014000404c0369000504d80790703101402041c1c0e00c03809070031024050080d1070b0190003403052111246880782c9a00905241145103600c4510000344510100281e0352401d1000f40300d05c4101c1c0e500e040c003000784040 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 977993947 1250 977992697 977992747
    0x210902100801050d08070201051908060a060221071b060806010f02150f090c12010b0a080d050d1a03030d0903030c020a030c060c02030705030c060f070801030209181002 74
    0x4421440e0301410025048810281c102c00089445035100340582d484014100e040c03102c113002c0040c5000c090b650b084982815611000400c1c1002c10400405071615400b0008660004003843d100d881003400e440100c24009012a49038805072403c0300003a05c2c403840d41c0100c44614000010310642c464115406000c0a880b40742e82e98103e0a0100e07100c04010b05841e044142e00c00c082020040301001d00c036031044880d0240c4d2040f10501001900140342d10404e11060ba45600301c00e025841d1036028400240090002412400c2e40818068281d0146e03021440c007450340c6206000081c0300a90740752048401c0201602d550308181da401900401000c00141c00103071624070701402d41030000910341c4566405031070350494548565100005003010201d03420841c0014000c00002450802c00b4006640100001c0c0c4010302e0150000d141c008002801501040517040c010070168450a82d69600851300c48800c849440c0799007540b61801940180100103140300007108101010034104004040340 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 977995197 1250 977993947 977993959
    0x9031203021216050304140c150702040f1e24170f030a1202030a090b0708090606040902010c06200c0a0204110a020613051204030b0a0c1d010f210902 66
    0x128449000d15566048200401144c800c102081c0410428070807881000396500031a1060b124020114802038900c1d07a91510030741001c14210114070702400780c00542103081c0c07010400d00b80400382900c244d482c5010303c405038a0b61001d450301c2c00030360742003090040003d40d46000c004540d03032603100c0742040c0c04100359091402010040f1000c410003000b19401c03040107075074400b912444d9201e0000294006444141e045541d00c064034000b0707407000f403100d102c2c190988900740039240c0340707608070708107100182882c1c4034030314000e11440181c0e00000090030058100b0301c001812000640100d078400030865805502507804925400d4130200025021883e034400d9800384010011015200081d0281d031485201580100c4006000714105082c4040d801d4050011640700003841c1800804d02d03400741c0c1054404840d05030412143c00c0300c030b0140350b400e40c045140c0f824080c1c14288007502241f091340071543c10018500c0040500b00e1103800007501300458541c044a40045a55004d070081002074000c074000c0c8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 977996447 1250 977995197 977995201
    0x306010f0c021e0315090a0c081615020f101b050315060a1202030a09030f0804050703061505060c060403091706010504020702040f09111c03090b0307090312030212 72
    0x288204010301140d640a441ca424200b00c010466400082c07510f51075405115035a0b0000048852144442c0207110f45005000103040034100300450781130070b07003150f0769a078040300f0745482c07070f0340d503640700f40100e84010f08405407400b4141c0c01282072079003440311541c2030300c110500e030700e140c0b24640d20030b440400d14051440010440007500b940e503404116144070140c0d440c41072484981c102a0000c0901352484e1030100318040340c0600400032608151040e01030f440d510a0b45108040d0840120030100d101424105040d14041d501c050340c9818902000701107580f104154103454404011100c041d00005292584555040001554820741203138143e00044d20070740001005103007003030743d1a6042150005032107a80e09040c144400395201c007a040340c1283d980e05a2910848061258070240b52080b40d0f041035800c440c07400c00c0101e9480001030414842501200c40020390460f01d420202d80d0381111907030300c0b40c1d2002c0007581c081d5800c0e800504103200343c002c911041079256004084010721000c084040d0307 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 977997697 1250 977996447 977996477
    0x60a0314070806162705060406031509090816060e0a0303020d11072a092d0c050a0e06070c0308130f35010c050705010b0306090c0120030f030601 64
    0x10800c84d6120301c010a00d50174040304062134060f00c800c81007031186820500196500c0102d601a4015840400003d83c0c401c8820b90603812002140001e2000c10340c18000880d444e22110301d14860112201d480d0f0b440382290008111254000c50b0301711022400b500e099582038280030b40a5480103c84d00d00040c5404aa0000700040c1c5e419106160341081100c01e188205003115098071441114041080040c1140000c1070100d41c02650050b000b040c800c0d42407010031740f40403079092600501c203404050a083c0304401d00d5600c0010344184540750700e4a141c0320580c500101310217114450018064412144011090000c0c45008041c5c0a48041040c80c00c990b440c143c050212a0030f000d40e02c003c80250f8140c0a241c8801e00d10380c10800101e03034120002901c03082c821801c450652020501103040800d402080c81000e1083e000541016030140040707181c05103070961691607600301c00341440800421034040d00e0b00303c2800340307551079400c08a80d0781d015940c0703d030649900b0840f469400100407a50140c00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 977998947 1250 977997697 977997721
    0x16050c03010c08011a0c070306020c15240a12080423063103110102010f09020a090e0a0f0606170f120f12010b070c050604031505060a0314070806 64
    0xb403460799503a401103a420411104000081e0700d10000700100306004003c140c030001d000f08402180f2034403005a075001805901800c001200c80e10040b41081c040403c0b45003c13030302e4895400850110b01403110f56607890005a2102c0e10f0741c00107580f002d8040501c0701000500f4000348280ca9254005c040e1900105100c0750180ca6946031450700480280030708c6134034101c40e020074245110140c1540c4203441414018116a14455009403030414004001e400913507028031a12000200d48841402400d5007a004202001c00600c21a00e0056481000c2d0041050511202c0032540c3d000000c01c1c20b0703030b0f81d07806c003c8050b1080e8041c11088000d40e031140f0040010015403821040c2424015090600d01c162074418150045416034034011400c02c03815840d90085c908580c023030052603040580f0b0705c3d0b2505017040c180b1016081203000e58010081807020540c1c502210092400e6000082116510300001c141d01c1c80c51035200401c0002100071156500c3d0021844e0401c0e074510404903882640e070525030044e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 978000197 1250 977998947 977998961
    0xc0601050a08100903030b0d03390209040303060315060305060105040209011b0507150914030102090a09150b0301060c0b071b0201140c151f060e09090109060216050c0301 75
    0x242da03031001d807a000b043c001541002900d45d0103420700103261113000b000328448a00c128800c034000340d4003082484013845131401804d0341031002d07180c080c0d0050907060101048825110064840e4035071900207010140b29801510146a0049554881404042501016006a0004940c540904400032a550030b00d80300f0385c1e4190702c1c141e64a03a0300e0040c40510015030320707418006907000e0188100108002039a07030012400d400301741d0780310310050703103089030f00790f0203030302c1c1c00d04080c270a034010040e088141e07484040d0300c010b9030759808002403c00340c004c00c0c0a0304141c10f503100015201d000b000006009410ac40d0300d030a407900030308400e0010358420200f154480c3c44143c0030110000e40c0144500554440e000203d2000341000700d0620f04000300f10111b1521900c1c41c01100341c4585541000240b412201c1017844012070035200710300160402c84050300a668081e401c0c0e014820045c002003e00f08250031010400381c022000310b503544100010707a101c40300340c05400e40c0c0c00e124240c1200075030b003070500c5141 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 978001447 1250 978000197 978000209
    0x20f04151403010e0402030a120905090108030301083d0c1b05030315010507021c03021207030e09040515040b2a030705070212150618240d06050c0c0601050a 69
    0x1c0c2c656030900c1d801c030702082d00c0176000743d80602c50181b20741c000504501d5240c0c6080c4017600c070082c550b85050200700c40c1d414160021205900140300402403c500059100310007210302c0d90328007001c17124107583d04103a40f140c007202c0c41e6002c2c040a0fa500c1743c1010340c418030260100e036640079150340c4405c10b07202171807640b030300001c1440d4000c000086007000c00040c50000e006c030514095140c485550001030f9001d07480040040b10000b2003882004140d010800d10140028950199081000390703200031740580b4078a60705501075100f100000c5c0811030107021040d04141440007076800b40c00d040c00d00900389441101c0300004d94910b00c50004c0002060b00d000422030019040c0b142c5540e40700e610071607107030f00208402c030f800820301c01103c0301090781844080941c030141780d840c440a00e8500100944c0003050182161101c2034a014400e00004220001c0020000c0380e903c07242000c2c0c5000071441d1100308150140583d4907000c18000703403984010003443d4038420202141c00d2a601d0300c0400000e184144225 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 978002697 1250 978001447 978001487
    0x30c121f1b0f0f050a0509130c1e08040f1103011a0a050105040b0301090b0126070f0f02060f10150915020111030a0e03040b04060215180309090a0f020f0415 69
    0x140f0103841c804e200401260b41c041c0382603801c00b03140c0740110303944619035200001c2150326081e180c024694000c407805c80080c60381e4000032002d0030034a0041e0038080064009401c000c01001c550742070003060441d440312500007034020800d0000880540c03050000003a00d8511424a0490000e619882a001e80c1c0544090410103440c0da40f0f0008400f005202e813607503050510542c01e01e441c1e00003000700d001e03071052192003006074445c1ca0504001401301e030700c41041710288108400e5a6141c980e00040e0340790300503041c031070384021511a0040c900145000794400505c81c0c1c1907510300704030190310070340c40c000b242d58510698144c4240000264280e90f002c50240e2550311080c00000c8a41e442a00841c3c2030980d03500a0364903058403401c0507007a503400b0750003070805070b8040c0080f4507030350704462480c580c8101020807070b02d00445200c071401e40324032940b20030501c180000000716003040c00303a50000350440c2d81840115038031400310a40c09a180c0080c881d8501a042c008410242c8038010590300311200580149 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 978003947 1250 978002697 978002717
    0x10f05090c030d030b0a030611040f050922240c02070b0304171c05010f030b0a0b01350103030906081e04060c0203160c0807090b030c121f1b0f 63
    0xb0460040c241725040c650300c04642c8800002280080c482d203000584800c00742c03a0340e9414110074030004211548814000c0400c20200101e1880c030098600009142c8800740c80e13480807030300f000310f1090b80c401d20803507030103c0c51592604840681c3c2d1180e8071602e480d07000e86600683d91640300b410b0707000464001c1d0080b545042840d010052900080c00c4010400e0903140d0b40d100a0302154040b95401d8110100c03112401c101401800340102c200c40d03105c4c14138030b014404407042000003040c80d81c100e0900b1140b103c40d01141c8884040106443c0e03c03003a2100d520a1081d84c0d2410000e107090ba0a2040d0000b10340e80e9070200300c84464041c00c44035100c013001c00001483c0c5a50ba41c0751300800c06000c14000714003083c400303c03801105000c80707034601c0717400b550100c0046030074290483c1c2403c0c201da0021404e1441c1820088160300d020842034082c410840300c00902c41d04512405040070486040c901c1e85611601802d199203200707502003400702e00080020000812086404e80c0e49110601c0404003180d02044 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 978005197 1250 978003947 978003973
    0x1305030a02100e01020304090204230d050a0803100803030a140903070309032907120606030e070b09041107030f0e0a36182913050a020d05010f05090c03 67
    0x803e40200340d1040c81201d10b0190b0341e035006002c0381c005400598161914000305458941d600c20700103032288040f5950410041a5504c9a0782c3d49501680204108800310000342419400c100d0180244a01400d6a5403440c0c090318407801407440003401013889040001251250500100303841c0240d5050b100c807030166046486e040c01c6c5011102c48024440c00010b240c07810055400152070050f1001e480d8603602c1c2c01c1041c1c0c0d8100369035140c0c0042d000c161a1590f84c202d070319400103102d022164044405a5210034000102d4041e005442b8160381290b40028142e08040d44200d03c0400e0000300e60b211403040d0800002c00a000307030f161046004c00d1403414000c1c0d400708800500200e00c508030103002e8510b44140c24040d01502c00803080000c1804448640d002400343c10889041080940d92021950300f90421100141100261001c20314041e0b5450442c2040409c01c0500f02141e0000c00415145600b80340c842d010b040c003190000400b50030b00c80801c40d0100700041d42c04420200a01510032020816 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 978006447 1250 978005197 978005207
    0x43080727020f1605030d020406031b08101a0c030703050301092007060e0a12020a02240a05070c0e10090b090103020603061201140a060e07021b09070c0c08031305030a0210 75
    0xf61050380c45000c108000d0500c810503100500040c59952008070700d0a118043d90280260031440080610500c0010000440440c800080c280d4400c00382e8600400c0d40201c22820358003d540d00c1000500c000640c0005040d04000554100d0f014468140036402c1c2611220b10005200407000c2c0b102c800c14400e0400280981d0044800098001c084411180a42d19000f00502c00060100c001d6000014101c0540c200340c1807002c15040c000180c1c20006d10401c1610380c107885120303e031108120011824030b0400003c4000c210041006104031411414480b0728580504200d01c1009019884c0c25000358060400a41c014100c0360005c006a05541d240340c1442040e221200c1140ba0a540e82e21210301c0e030b0040700d8030b80c07801a07401c2c00001940f83e0410401140703506028000d40d040d54004c0403005a1401504212079140340152030100d034035160f1501c01e40314001800c000408100c1000008a80c1510010240a82000e440806007101e50764000349522210010740207034000c0c1003100031b0b02450f0b0041e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 978007697 1250 978006447 978006487
    0x108070e0f04021206010b0d0e07051c021201050709151818140a0f05011a030105210105040f06060518010b09030f0a0b070243080727020f 61
    0x3d400303402c44c1d82c41c0050700e900300202604071a003d80c1c030118101c012040359100d03c0c004580b900b002884214104000240c0c003024600d401400881030004101c00c54541010410605071000f000b8050390070f00d56006000c440650003055001c1580100c140041c0b8800e100303e001201c20301e184282e4070341c24400083c5090309501044100c140e160718030301800c04445442184581180c1c08002070114500c40428196101a40f004844c406003210300000283d2550449044402c115450440c1c0d108001401203013006640561041e54640002c000903c09903c44442c03031180f140208006250311801000003030520154050f81d42d0030910018040200c00c04020301c0c0c1c01100030304880000b412110b40c5032610001c01c000f224610460000d00800a40402181a1071190317440c00240403c0e4807a042108500051403400541039240c1607036520a12122a00002d80b500341c041c4d55a0300e4560290841c40418000d100b151251465042d41780d46030240b0070340700b65080010402d86019103180d00e902c419490 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 978008947 1250 978007697 978007699
    0x1e05070b1f0b04030302011418030a030507170411100f090611071a0c12040e060123030c1b3904090b09010c0810090c0224010e0108070e0f0402 63
    0x1c149404a2207182090140c0000c520070390000c61b9449040c03120b003200403c05019001d1888011014944000000c000d07a10806403e00e00012240d603a440100d80c40b000001030140005000c81c04c0c8014004c007698070104980c0280c48030941800c800004450380c421400d0064001107a8201c01c2c0062803251040960062159080317544194071a00d40e401846030100c4008902440001c01ca80e100c041400103100411507036040d175003094030740842210703184030041050f410042240c11504604103284051800f1030b01102c603ca440b07141c1112020142d500c000d1403104c00c1c1c21a40c500c040310150001e030b002c03144203008244030303402a60803e141c03c0d0030700805003034050700c2d00409a02c1030a441d54464011458012103c10750b00342031102c2c8031400c480720780c1020010843d65904208001c3d24800d000c1c800c5035000c500026013202c1c5050201d040050000303002d00348110405020b400c0103642080c09042c1c0e24906040806a41ea03018515580c00d100d02c41c00b0a400e08000c0060b401c0510043e620f40c1c4540 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 978010197 1250 978008947 978009001
    0xb0a0f230916020f03032a090303040302012703110301060e1005101101020a0909050a0c0c1b12080409050705070515180d0c530403031e05070b 63
    0x85203204d000e0942e0811503002e521400f201301d030001094405160807000c1071240c000b840c507004a0002003a141d1043c0e00019046c4031a03404002000342410700c6412030b0050030351440890545a143c20300d1840c40460f000340c442c3d801c0220114503264207021050007644c04c1c039890b0700030300d103041f081c8a50107231aa24490103012071550200c0c0210b000303000919507801c19079500e1681ca42008580c104894024041c4c0e06041c0c540b20103454015000104c111084d1340003404800324185400d18602400e85c1a0840001180c04440007000c00c00f1440141c0107492103030a05002554450408403080d020301030018000e0350000302250b95114680145d260410204103103040078140210405150219074400d84c400a4104039284081c850300d82c0500103000c2481c0708a911900c071103c40310080b1032640d0100c07007902848200d44910408000b0007014003102c98090180c5aa60368200504803a00c49a1a02c88100740f912090134424400e8048641c91640308409130540e03140c40340864040d1000e07441803d6018 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 978011447 1250 978010197 978010213
    0x3211b050f0609060709062a080903100501180504021507030e1807120e03040e0c070f05030c0601091b08130606090209030c0f01050403150b0a0f23091602 68
    0xc40244242e034410a150001401c060504c00d40c01010070383d1950111b01040403443c080392103520810110045603c010301820116021820071941520400e100258144100314190300c90310030a8000034101c58901400440b00e81c04d010200e4262a03040700c0081d0310500b41050701c0390080354180a400d6060003841e00225014808020501080311103580509003480c07402041001c9030300003c199010200c4003800c0c8400e0328501c25980c0e41c0d000c0e034059050340d41c0d42100024800b0900c1d2003510001038100301e400b42441c0d41c504180c5d0712903001d4009102c0600400f0008103610015004410101c8004d012210840c042c1050440b040320000e020740c485c021441c5041d901080b100e0007624040c2c030300d10900507500c2440c001018a4682c0b1100c80f00c1c01114280348540f0583c7e0442c0644048036040081903040701060f401d00c0000b41101d96082d41d1040052300045118800307107041c501500d51810310350624054038004800e880840c111155840b150040001c1c1c0c440031f01200199081c006070048a20300 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 978012697 1250 978011447 978011473
    0xe0406060b0a03020c0c100f050c150a020a0f0c0c170307050109030801080d0c051005071b03091a090a06050a0e0603011715010305073501050103211b05 67
    0x142e00100c22540000e40120700b01c8800002403201c0504100211904203550058101c040c1c18050040d5604040c4000070540002d11031050004840c0d5000c00b4030706a2080c80d00041c0d01c002904085401030004401000d01a94240034112644003960012103004c500d9182080c40c0045e000d441c034001040d0300040c000c24000603801d0068007035091180c4c032039410960500c02114a070151094000741003201d811350034004100042224107103060325070004102c0f599003400580b652a4001c01d2100d1100f81d041d120002e140e4403400901c2521485500c109114072080400b1140d40030f282a116800411940f08021140c020030080c101d4000504010104030748d05c0c00040d0300364000740d1200e1001c150880340d000c05551b0600c0024030303903404100320000c60350450f11220398804190049120090720710051803c0400e141204024448041c1e203410f00209002020a02902080c401282da0b82200c40b402d1280c441c804900c00c400700c09558603034201102d040010034a109581409560500074941c00d8400 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 978013947 1250 978012697 978012719
    0x61110020703030e0d08090c04140a180c09060303020106060e1021110403050f03071e05100507032004140906040905031908060307060c020105030402012a110a0803040e040606 77
    0x51421039107030041c151611100560620844a100e240700314600580903021078010220300780c101107900d400103030390320900500c53352004030540040c0c0703503e0460000246465440c0c0101060302d1096000380501e50f5100800d8800c81000744c49103500034100c140018040f403041844e08c201a446030348088034502c080708a5411110b51396807803804030000040c184180503040260441d2428268009c625000b400c2d00d50344007800001c030385021041d10750018102440010804054400c081040c1004541440c0d500a4010081440105882c42c0c520f503150910346943d030166800c403081038040080c2126085c0030040030050040c09607605c1655060b24030702050040010b4235003003004032001450b840b081d9901920001c4c000300031502c80d80c0150404d1041030fa1251200f0750039582801c2c407503100e8a6601c012703100681414248000c4615014040b0003c0340c0703500b40190614001da1851501e40303540000d00104100b9070284000b5075200708030030070403410003144450b0b002e4051940060b030a6294258294 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 978015197 1250 978013947 978013963
    0x150d0b040e0d0207080309151305150a03051303021c031d060f010f050a0302010c05030705011b14030420030312160305150d12050d0e100501061110020703030e 70
    0x541907109079a41c0b0a42030301004408040c2c01402c00843c00c140f5480000f510b01d4409403d0300105c01004900702505118090352603000d400020401c41c05011141106134603034000000200000342000003140c04110a0701c0c500c100d858160340640fa00d0340c403243e0000700f901e4104107203400301a80d071160b40320764113107455030b5085440c41040904128109080a0002014181c11841e51204030b810b04100315912350087c01e048a5081c01d15618220080c20b11601354081c074130000d4402d5003455000203c000725a084041d1107089900c0c0c4005a00032808007001d10300040744c004100c5040909400c01841c030354a501c641400c00203044900e00b009200100d5501c00741900c0440d1030700c00310f84480c5280750701805001d40c44400e00021500c0a030101000500c19112103c02a180b491401d0302480c2c241d1182040f40c00b5524551024030a410144003626994a032070b903041c40e00145000000302c0c15510605921a4180305075000344a1009040d00602c0254408441141855030380c0d00c0d01c1c0c507600d0007800f07210 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 978016447 1250 978015197 978015221
    0x1506030f10020705010c1809050606160b07031802060711212802100e0609030106060c05060c030f040311160e0907170a150b041b091202150d0b04 64
    0x150721503d00f4a4040d09480b4041c1010301070001c2000c83c2400000707445282012102c03141d4001c540c6464107004216280b140b0042031096103162203500302400070401941e4081d036001d40e0200800c80c0c1100c941c0082c00c030008802175000c2820000b20000c1410311a1125084400610340d80040c9060702c005114501e00b04c3c8071001da6041650060100d0204181440c105070703014003241140000c60b80010fa040c01008115001c0c029026414446519070344d017610001003000c0d0080090700c2c1c8580c000f50188640710f000300e07a40c0c403443e0001650b440e03d08007038900803201e12660240b90780301da0381c0940b1501802c03030610f4010f01ca4402d0136812104011403140080200c0d8200514030b00b0144415402c0c0045a0000d606030541203203074012181002030401d0f00b45070042c0881c201c4404400c0c40101500d034078482c0c07983c06805d2410600c4c00e52070b8100c0d1a0004410354991800065860251149008450502952000302540700c42080d0074080010440024180c0001038a4103d04e400501191103c40300720b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 978017697 1250 978016447 978016451
    0x3010c020f0106050f0105030f25020c04050606070b010b03040503090a120209070f0f303602061b010c021e12040311060d020f07060b010807021506030f10 68
    0x9801c228801e00c10702024002c156095665501032000282451001404000c111103682000035400315a0300e9807850440101d11094040c1c031a10360000f035441c130381040a144207525040119140317181040071030300382c40d030320900491190703180441c2985203400c010b0003075519000c00c10000e41d0340d540d4108144040e041e0811070a4485002d03006010386c00e400102507106015014203844d02040e0820100c802900503458601d0400404d842084400f09071801c1c409040e51400c0d200c02004020b640043c41d514001070840040000451130881c40d2034034584440a6200481100e0805820071100816030916807105030212814010030440c2154030340708440005804c5150204030300025501e40c0e500c00c1e850a001442d48030f0342105103c0e2588104d00c001005080180f4440a0581f1003405813610000d0260046449810045034208035a1241c1802c540b101e160030402d14031980030303203401da010356041e034020010510162021189aa00a841c09a0600c5201c801c5c00319400e04002c0c182085500400c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 978018947 1250 978017697 978017713
    0x61205160f0c0b0415050105031b1009050306010801240e07030f020f030403080601082406090301110310050f09281b03150e0c070b25031508010b21070503010c02 71
    0x340d204441b0107811051180e003241d1180e169020a80c548001141c0c4c0440303420244880411003039500304090303806142c250040d48000500c8240640c0020428802d000480003030b1892145003008025490244004d082544008101700c00d1081d8000f046409811030010b01d410340d13070800740803940c108403070403000121120100203072946c1c0040455042941803600c401001d40c0024101d07942c0500240c16405400003082c0c0ca15a950250001c4120030000344880c0e03502d09010340400046802801070a00407410100602c1c1c50342440d01030705100314245400343d01c580c03555800406400c405805600031054a50340c6001d030040306c0641ca0945c41907942c0b40040e0402ca0300d5000c1c14800c030240c2c45580c440302080c0400c0800301c410801c40b00304c0d80d80aa941d40d61651552898000c540844050f8000030a0b881058601c4582550084d906591521384c00629166620403060030313100c0032450301d03401c22800d072000d044000c0e44041c00c1358004d180606860302d4507216008a4215844c94602e000140d0100300303 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 978020197 1250 978018947 978018983
    0xf03030f05130f17070501030e0c120c0d0b070809160e04020f15130b210726060909060907090f0f15030213020309120a1116061205160f0c0b04 63
    0x200305c030300814080c2020b01c40e829010740255100c80c80d000c1040d014805000b1008000da80a10004d0707100d0500801120202e2250308020000f502c0c100c5800d400b1410340c1c008100070340e06c0022a00c160048030640c0303032081402c04c1104c50b0b11001c00340c412600b140c90480b05500c40d944050005101120b501803180d118800c1c100602d072951aa540070360441a010000001040d4074401096036003515038051030070689a00320111400b86030301a488140e04000608503281c24090f070b801c24001c17901102c900c050741c2c440e422841e0302ea00c4d080d180c07010765602640302000242a01d030450303902c1841d102d400091f0300c0c014011150075500e4114100410410651b030500861500c100c03d4500e0703030f070080300450640c03502d01c21856460341c58680c21043d0b0b51000ca0044240c0b84a1512048010f015a0a0b11030700300400c440c103580d4001c0c1d0f0082201082528443d1101e0740a00d115451003064640d903070111440f8001e6080e5101a4441d07490b101300903502c402c0c03101256031000c0d5940900c0c402c0b1003114040411030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 978021447 1250 978020197 978020203
    0x1a12210c0c01110601030305130b0d2903070e09070e0f01060f0f0509010804080c0d030c031a03070509100b0720010e01080a270b01080105010f03030f05130f17 70
    0x101200b4180000e0080c0d40c5a0a000022901d0540341c0c54100381e81d445420340031034010341034290700081541a00003801c1c40c002d0b44a170841003003030f0750f00c1380902da400d4036402c101c52101e95034005003509a404004c041200070070b0b6074044d6400c081d25600b900c2040352204a5401c030070008460b80e540189041004000c040e5220b41c100b010560a440c00020689240790024200d11030300101ca4100600c0b0b0004c035080c0181b043c21294010b24940880e00104100f503801b80141c10b440c585c0304040b070314203845025107103a070159100407500020054020541000204908414040c1c00380d60411540b010125080c01c98100800030740380104110200d0411481c000e002c1802e021054904000c2345007c801500c0e60461046a0428005440820501c2c10304065440c0ba6505040d002c001b0f126241d0703240203200c4001c003141c3c142c42c1140d0080c40a6a20742c114880290003501c0028000341000010000340340c4074101400c01c480c2c6809107140030958461003045903c3c4a46c1005480c2c5005060301074183d5010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 978022697 1250 978021447 978021463
    0x30b10110d0507031d031903020105040218090703060203180a2402181c06051e0109140f040c0527090604020a060509040b06120106121a12210c 63
    0x5442d010380340c64565580201103503c00b8056901c2401c20268003940340d82e042c0301c1300300403c188000004040d170300c5080082c060300003a10300b81d0140010702c0d202c2d1b00044c10b480c040c500c50902d400c000c0040d14995074580e402988000c04504420b03a5010404112103820700110117018019001105103070300040015400030bc58000041d40148104995404903c000c0c6240e56a0001120640f100b4103062039504590902c0c500014206403419082080071140d100301d40d100c001c1c0070107102e5010b81c0c940030064201c45440c0f84401c0d9048001c000160280208441a94000d1040100c200c4036076840700031900b45240c0d102d2184c10240201c030040841e40100803d1644483d014005101c01d0074070790042021500c0d41d00445040190000381040303140c03900e41090a01c1c190240c00150f450b407075109600b03080c1c1c1080c042d98000581c0845119051209800743c0c4401c02e061900360102d18a203401086802c602c41031504940340030b00700e105a4501c00c859403116500115060007542c8100c07612500b8104594 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 978023947 1250 978022697 978022723
    0x1091a1608120901060e040305071b090f0c090f030b06060d06060e1c0b07050c01060e01030501060f080a0308062101020a1701151205070318050322050f040903030b1011 74
    0x90305500304694009400b03151f802907050700b400d96480ba0242030046051a196080103800044101c002400707503015400700e00640450903081205e40c649071011107800304507100c0c03d031024000740c1042c00400c40207a015900410300526031850b000e0540011001e8589035800800425584280b02c14607041c4442595690690085200c41c82c035219034500f0b942820241c81070781080b80100d1009003446d0b0940c0701e24040e00d8010f0b060310482d070b92460218040d011901481c2040f140044001910440002da02e0750416030540360108a540c80500744242071b80000f110390901a8502440002c40d070303003880180101401541e840b2a880100400100503540683c000c242212452140d00c900d5607101801d0070811850123408a0760341c940c0f500481c0502560000c01c400426500e005030700b085800001002c0044554110500300319164a03030001110080c85401d070004007a4032101007900d05a07015800d120310900300021185081c5000c505140d030052040408610b1105100d80703000400c004594015030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 978025197 1250 978023947 978023951
    0x1c110402040b070b0601030b03011503060c050c100207020411030403031a09190510350606060d020904090b190f0c20120304030e0f0f01091a1608120901 67
    0x114050042e0007611942402800c0c4ca1011004240960710070381181039843d400900134400c91174840001e40706200b01d0302c0126106490000d0960301c060148041e1500100e084000e802d07a02c580c00c080c4d5010b513200703d0081383d06c0f50307846101c400500c81900166018501940d00060981d98095a10700e04040c48031401b8030402d440c104000d0000d00104c8403079105035488a011600740c0302c5a01101103043c05420001d41914121103208644e041032114281c2800d402c07512841d01c4d0f1100000e03903100d18058400c0c5401c100100a0500082c0544e00204441400078000083c50140c0740c551140404d03040d6215602802c1c0030286545004460041d800c1c4583c01c2074007007080b800d102001a01800507141a00200180c16038440403c0303406000b000b4100422024844d9640791a1030010326125045200318401c0303040030300d160700c58184075050740781c101c0e010b071a040b110505145d600c59a1140300d0340b034044000820130140340c900b030420300c1070801c2c0b512a811f160b85800740d642a010030400014041d96440e8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 978026447 1250 978025197 978025199
    0xf0201060305390f010c0501020c0d0201020a1d18091006180b0402040f050d141b120c0a17031b0303040b01060c080f0901170f04020907020f0303241c11040204 70
    0x750f1410044d90300d1040c00d081003442c404007440d003940a030090111420f51406140366450003907406400400c5640e0a42e55040d20000c0700204091900485c1c402d4650003400c1c9036814224030f040c408006810455030811607040300e440904482c01e44010385c21a42c10300360b00c7c11616400e40003e0040342c10035482203800f54100350918440260a86240c4a02e40c480d4245041c820180b01030071280305100c41c00d0a040c0d56110300c0f5074040270040c4d9051032006004110300056a0004500802c0711404040d00405403002c40345071218902051052300b0000405000c10415440754102100c3e4800c903030140320340510780760701c1c2a0030306e140200d8050f44800705010085c007500c030005080e08201d44240f840c0e4911951524540d0300100c0e40d1100b1840d006010a14803801d0140d501d1041d9030052103a407080b19024040d0351020822600d518610101143c107500510205804503040104000e074440f032aa010740340e0b80039800020389a054806411400d00940c0803480003482403020b06000011000e44d4154506 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 978027697 1250 978026447 978026449
    0x3110601170604200604030c03051002030606160309080a0f0b010909051c0c021c12030c0e15070812070e01090b031f03050607050a0e030a0b070f020106030539 70
    0x1018001c10044c010b0600d0142c842079680b22958480700007801a168a4480d41c9928080040185900003601c0c1d1380300302009212608040e0084900c030b5400941560305004904a02c103a02a100c0101101403020303111b004964904c0c1000010049406000b06e02800c80713181c01c140351700c0d02043c1c220b013002900703101c03032800890300010315542c211800308410340f19120b6880003103d880e40960002035002e41c0842c1041c0e82c0c0c5070305040c080030381405005440c84100c03644209908803025261802d020a0411094030418a005500c9202c1071b18035613903e502e04001503540e0412030340480b001c040d408420b1000d02c01c240382c1c0101d00b110f00c80001e0070082c0c049800c0c1034204401d07010040010f550940040c1e0080394001c0104903a1004540c4002151131340d050507200a070154100c05420400101e10b072018008070f10380010b000c880d49800180c128442d40b5220707030031a2401ca80e0040d000941d92252000400901c0800250340d444116410b00900780089078000752200c2070080d6200f4048146880c12505 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 978028947 1250 978027697 978027703
    0x160e0a060509120f03041203020c0f130e01240611070b03011401271d0c030403110a0519030801150905090a0618140c0a0c1104060e040311060117 64
    0x602c00d04495900081c0c001415503440d0134840c1c00e4245050201180004840c40c002c000351025a100f9000d07100010100d9007882a010210749100c0e51040b4400d014164000c01c540c401c100240600d4004130f18000300307403a0001700c20b4403116003180401800e8401c0085030360009510034555081c1e03020f002140c1c40c081100d20180410701405184148001c4080c0d001d80c0145000c5240300401041c1280c4d00c4080505000c0c214464403915150055007941d00c0c00007039a084070309118000c2e8503a80c5055840d640c17411a8154611001c803d61440340c9400040458400c0290208202c4400217a00000400d464010014207041e4080c180700440b1003403500355103402c407101c41c096401c240d0b400003040c0c3d540143c100c0500415403081854030345003074141402c000250040c0341c41c0c020704511007485866402041409226600482c800075440c83c2158000501c0007450380394a0b81c0003000400c03d962180b01901c0200010f54040b03021810042d44116500410f00c525401410910500b13030380c0c0c4026007c0151 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 978030197 1250 978028947 978028957
    0x1020d05011e122d140a060b010c080409050403050403020d050718022106031f050a180b13150507030b0f010f2304030c0b0408010b0306060d062003160e0a0605 70
    0x30f01c0d0001e02c0c0b004513000398030103030140c01500050090701d00a82590060748811031240c058034901c0c145580c032103507540291160000198040d0a403171074186003103101402000050012400c01c0402c003c00400350740d840f9142c00c03415000d440036040e541e14120480f101d1000c0304030850000e50060080320100305200400c86078903024500c0078501c550350f0741e002a0070718103480b132420b240d802d40706150800354586074046407103000361a0007000610b42905410710043c00041e8000e1030b1b820000006a812000001011381061048000c01070307020549600c201520301c1284c030940060b03a141710301000d41c500301d64903240a480030300b080402060600c100600c02400d100d64031030407240c02550310351503040c50001c9070000c54125140052040e00c90107009a598040d10401880b036080c01c007020500e1030f02065440c00307038100500d07240f2102c5840d516840a0003806194840780700c1850401a03903400c40d84002e61250348000102000031440311405060110302c01c009501503d0700a0091060b2500181250 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 978031447 1250 978030197 978030233
    0x80f0601120902040b04021305031905120a030f090311060a090b0a09022b03020609030a02030301090b012021040e0705030c19050304020a0b191101020d05011e12 71
    0x4030318490700340003240c041e000b03c2586940041c4001908c0d50170f02100031604094036403c5041d52000c0c00c0003005002c140d00e010002a00c2504004101c4040d10208030041000e000142808183d039940300300391004079a0092025008120303620b06400030250103204655000501c41000c10240700561546403d4000c01411900b0003691500351030250750320300f03003010104c41a074880b842d0749a000c5020f0410103203842c50100c02501c106408680c0d50302000c401c0d5450402c2e6580150b0a6a103804005005003c1040c400707070600c0002d400c1800700b200d030f00c42d040321441024001801c40e10303034140d859150b8115407001000d44013400d001c18090560701c045003580108031490326689988034600f02294510500b01600e00b03980004883c00c02e51500440030f07602c0f4038000c50310b8805e1a0765612400b04079200c0c88540358a0b101b00c0c0c00700324034024000c014402400719401c0005081000070402082145d20a80007190030116541c0ca05070043c144401581c06408101039a002c0c2810643c0e54002d40d40341c900c821 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 978032697 1250 978031447 978031451
    0xf0f13030f05040b162f100e040e010606020d05071a04020a0b070b0114010804320304090e010c02370210030b0a0509130f21050406080f060112 63
    0x894101d882141580d000d070800001c0349680740414661501d074882c00440490b0040c1d891000c00c0045a1440c4640c95074140c00f91113543c0b450118010000413005203901c407000c2c003d2480c88003403651290701c509440c241241c0000514503051900292812010700e40300410007000700310366170008010b5504804a580e18440c082415122840040c0e0300500c0e94002815880313020a40406010403560200d049690b0340011603040d4140800458042c0c0c02140c02504001040d013030610f02c06c0b01c034441c5c1d40a85119990b040c1d140000c210500e81940d210f81d1220f82000d448540380d40d8280400e100b420500a814001030003803a150b0714806c00136109261032208100512440341c1080071410502d040030b1a8010118540e401007480090020440009140e000c1c4024910110716400c040301d415000310f440c4810706810046540d940c15a003a43c404045802c50020200120100c442d40c0c1d461042000548a440e111802c0180061004100410301401110405d05001c02c0380d070080040c0d4031000c0e0b90500 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 978033947 1250 978032697 978032717
    0x307090e031608071a010e070c020d0606060207081006081c02010207020a030b0703050f09060c0a090914041703150402090d0c090b1005120601180806040503030f0f1303 74
    0x1200e0450040e00c1510400da1500d6006004000c0d4030300080c10710702d1242c03040e000802004600302900545c00d00070383e000d82807041c1c04900c410b4000d507105074403984000c0c0344200504d801d58412080c1c0c0c3c101c0d40a0b41c09070b48203d0341401010824808540e0111000c90100809880d0601c0d040ea1481c1d86030861004000002030703090312500c01e40458034526001742c41140020390b649001c0302c1401d41110381e000020b14107000b00d10020341a1100303501075070701a8000c058a889400d4000c440f40e01c05502e40c001d010327011000184031b00c1d081c010001c030b00688140100e800d15050401c01410060403000c801602c008008200c0039480251040040103001d85006841d44065000300703100400c1d17400050310f410307000000025210081d80004081c10801d5502a0000d44003100981d101e011f1074501c030a10320484070003d200303035109104000c0440c40036002081420f035181d00040c02c020b410b94041d03a258100100300000582340d8610203820600c1c0c03241840451811a0700c1275038010710301703000500300494018 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 978035197 1250 978033947 978033971
    0x20307150c08120f071d130b0d05030901030c091a0904090b1609090c17090106030804060f0822030c141e0f0601030b0a052a07140c030709 61
    0x80801481c0e88491a01e90f1204080100a900d4000f190315007602c00c101d0002400403481a032054800c0284401c413407207a13007001010440e540380700030003100c1401d036607000380d82c0345540d40702ca130300100350090780910b035960145400103007560030460702a024040b94400030003a0020b01c1e8094069801c003082002d032104082c0000502528182c10080d00c016400d00130700010b804100d181080e80c201035210b0b2242542e8030030b4104141d8490158040c04101c001700030495071100742813407070b9000d41d814000054980d02d0b51340d680940c3d046a002400003514550014951a401085454101c0302130708030640c980004148003c514034406400600700701c400884c80e001c020703e07981103151a50105040c1c6441117802246454229241440242148035030342d40c4481012021402e01e060300d402c41050303601030303071070040785409000060310401042c8048841500c08011074101c200596010303a00246e13603000c0301d082550312100325075071803400c68029065104150350000781c0707030080303860103070002c2511083c5107 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 978036447 1250 978035197 978035207
    0x506030d0503040f0f1a010e07021e01060f030f03080606130504020a0207090c1107090c08060d080c0102030c0d0c021c0c050a080316080a450c06110a02030715 70
    0x4d0b0000789001911511130381000166402008402c0f990076039841d40740e82c1c0b40c90002c4402d00640d89c00c8003580200703011403405440e0030000f0050044c0003001140c0542e50754800c203a00844e030b5000341c0754160030b4528402019401001c00340c0055089440c00c0c10031000d5000045070322501c0c40f400e0300c0b130b80c0e002a684441900a0011200078541c41104014901d5142e4002c0c07c02c82c5112001721843c043c1c25804989400c05208075560b403134180c1da0f01902c0d9611001800355141c440e00058410f403d06100700d404031032003400158881e944103603000342c441030b514000300300382c8404004640654000e00c83c0c9540e003030214601c07040031111314944a03900b4002420038904108103100090300d8200d00000b040740906010b800305140e407505968846c81071350b42c00852011640c20b4030300c0c49507101040044004080b80f2048908409032858a900c04207a41c07901c040c1d00310b0344401d104036004007100381c00300405c41c2c00441d1440240c1c440c9000e045921096030019844101c180541200c80312121000d20105200b4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 978037697 1250 978036447 978036473
    0xe090127150c03061502010e0606010e1f05070c122a08330405100c121b1b08040b030a06080f0f061503150c1606060510030506030d050304 61
    0x5107400700507000030714000401400d19409002950155500281d0101e8070510030144400041005095991904401140c3e800e03000880107508c00c400c048105003820b1003442140740114580c0314181c0d9917600d403801903201c11283d48085003e4401e2040c4901045881d507a806040e4010140c00c0405004102807076440e04a0340c2200c4d0b46e17886111010518a8074410303401c030309901c000890b04042d10b00d000d920544904102e4008201d90001c1190051000755034001c1585000b20b0700b002d01081d00c1000e458001c4400c240c031400c06c9a108079002965060308841c0d1008000e42d01125240c1005858444100710310843c443e941c050400040010b80f8400d196011001800071030081d103040107484100d0994818a1054661140c0248400300765a00e1911003a0040d102010300076255240ca022451095010001d1484c070101c441000000300f130085191301091b400d4896803000840604003000d222a003c1d0440c180d605040c079040a0003000d540c0051088002c1c0c820349041c9550f541ca52800414a0b040 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 978038947 1250 978037697 978037733
    0xa0e0c18061b01050105152104030302041a090a0f050a0308070507090204030c0e240402071419030e100c12030b040f060306051b03130c030f0501060e090127 69
    0x58080030b4220507106400150403a102110507110714904180703021114810703668404040034648201980400c1c1384118254031602a040040c189540c42d15a800350810801140d03024040000d0403054078584011817501500b040c003110081c50741020049030215a16000141441401048000c00c100d000c0007000080c1c00800c509545a99491a001c50482e61a01800c07540815203800203030b2190f80e02c804400541c43d00003082004402c403030244002540100c105880c00100011709951184080002c0e40f02040845807603085410581001060071004903952441002c10103484640d803030384032446004d038640201c100300c0310314101d4405a0040c01c4410071142c10070b05000c1f01543c200e800c0e03030284080701e0140f0b005000554800700030744400c50b007003c1040c546e0f181c01e002250390144034904034007003944204000100e5546940f541072603010201e00440b02a0345070b850a2200d9640401c6160304100100001c1c44030383e011000480715000414a101c030301d646035500d0203003400310003030100000c054 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 978040197 1250 978038947 978038977
    0x919063e0a0201120b010207170a0507060e010f020f0d051321030314190c020307050618070e010609031101050d18050c01050906090f06070b150a0e0c1806 68
    0x2681800c20744030403180a041c1e012030f0440d031034122000c445000307542030540141d010301400d130305006074002d2040140a40034154420b01e020900050410400c0b58051315080c0c0790007140c503030040001881d1003106000c0b402150058003030903109110001d5000b440003c1d509229444165403120011300310640c0e88542c2143d8030140c4607403c50f00206006040c540d0280d40e09100d8001032442c506003501c0300365443e81413604030000c4407541d01c000398000d20309007500d841900e19107041d5403070702468954140d90240305500c41918106140008120180041410040030083c1d58582007000c0c201d1007807840060701166601040001d541e12801c00c4604075205907804019204a1540d4841320340400c001c100d48500c1920451031080d070250342a0341040300b00820061030700e1080c90900402280c04040141c0220081c420040001c0072450394511801840034129002c110130010010306882d103502034507030000a00d0611844a0005c000c90300358450303100101c0714017066100400c030703a0b21840c80c4440b607000e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 978041447 1250 978040197 978040307
    0x6051e18160b030741040902040905060906010212071103010615020a03020c01030501270b04090803090d0e01050307081314030a031a0306070818060408091906 70
    0x20b0200514010501960745119458141d1109008520810081e50000100282c2e9429080d8110400c0c1a82c040030b0301254203181d91910040180d070803a4104480c1141c8420800c0540d00f000010550b000381c0910003846180803410500300148070321607021b4403205402ca00e560b40c6031401d420800082c00102900507038241511030094036024814412001801640f174020300c11342c480e010710348c141c0e90321000741c0d41c00381122540140642552031030041c904d0303102c43d000c903a503940e02e1150040b004c0c090250300750b503403905a12040c14002c0243c084001d0002815085035140d81c03280980b54440418101004152a25030705250302c5010060000d00b010f10781c15642c7c2c0d040704088058410420f0b00c1d21f0038452002982000c0000100d030140c4241c041d80020001502c651180440039080640e02c0f0740c2c41400c20b988081d00d402d2030400c49013980d906200060403e000d04203156015615240fa0616803546400c0080081407101c5026141a003910400070241e20080124040840c0b1b01003a03442102c12 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 978042697 1250 978041447 978041459
    0x1090803130f38010506031303140301090615021204051c06050c090a0e0c31080105010608010e04050a171b15100312030c03060314070306051e1816 65
    0x90000f070100c601000030b040ba080050441c40d0700a0340c3c1680c0c0c0c001c004508507946e040e8064138031510003a0036020000a002c5a440120780b020082d03010304858403001c20342c682410f80080e81a912811403108652118084506e41d50764001a941036403012940d8080b000801c0740c1c04030382c001c10041c0140100d0702c5e06050183e108512001400305080650340d088000380c3e02c84450050000494a101d170001082007845071260284800e21580c3d540e45100303901e007000105107000032045a800c206200d0f9901c400502541740c200c0c000d1401007240e0015a082807502da51030369120809010014201c2c0740c4201400c03500e0300a0700595120300e031004181408000a03402d21035952800c4804544485c00c400c021903400301649454409407030700019510a8004000b1086004004181c40740c803c055440f140400004c8180141c1007503046114000c140c420306605101c42100c0300603140701c048030310204d0a0460303034201c030000a500c0344108215041b400e80d8040030324203254034455807a0340c10a505d4004519 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 978043947 1250 978042697 978042743
    0x6060a030e01140a05130b0a1d030d020c0106151b08092709010e0604030c110429190b070c0509010b0a03050a0504020904110a0803030907080f01090803130f 69
    0xc60810b00006011a0300e41e11401004140c1a80002d0f001441c002c0010f48444015040320101011640101c0480150740c6050ac0c03c68000306840981650000f803500002d40e406d01504020f41468131a09072114180c09001d00362407098038401c080d8017000380c03541c001e11405a050300c1103000042e011003d0b41924030f031400091000005007a40a0540c403000c6800c40c1c205210301c1c41250182e4000780302130703210b03900c0a031075104c85c0301000c031000301c034822400e80d06480314001e0304030303410400403c203544c02e100c6030300040c4850070060880e00415103200c48010b0712503810b0000d02128844039000da9158042d041104804109410098005074440700002e55480203000038000d00b00e0303039602000180c0350f04002c00180c0740f00342c50195000e8040800720f0046007200d4003000c40600028030704480a9075540355181560030864900043c0d130005203041200440c24031426403410070b000002c0050401c03582e103080e2280005800b032030141001c681c0f540c04019880700400c0b03009801000d150321070b507104503220803 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 978045197 1250 978043947 978043951
    0x3030d020705060c040308070212031603090503060619060e0609060408071a0f0904050a0e070e010f0503160e0403020712080301030c050603040c09020a12090b090d080f06060a030e0114 81
    0x42e5511850300000c528031584c0054806070390303024600c02d28000413174080103c04c5e840301d01002e045000c10041c0c01b0750524034045611507540311351076000c101c614100c1054108400208840d0240f41c0711724108101d80006005c090030344509080c4112914076200120300c45002e0001d134140c00110002d408503130301400080107000c80b00c405a0b8000c0341003000e041036209000329006aa5460001e0004542c1d5140079002203901c0504004c00081140d032a2514034a031810781c1d4416114024007000510100329550001409003c0680090141d400c2032866501001d85902c86c2072808101400030604040c03080c01840d004140200303c05c084100c003801c2c200d649034001e1000710f540c4e90580e54005014100f01c1c00340c0348507d81101242980714074000f41c0002a601011202d010800700004002c9d0f0395505120780a0854002e420100c0d0340e20300f080d80d003464041c12a684030f007406090b03c20414a4811018000d03442101075407416120100c452081d000382038030001c020403035420100d080501d4242d403c6114 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 978046447 1250 978045197 978045203
    0x2d080f04030c051504120f0803131502130320030a03030c0f1d0907110a11030c0a0807060c02061903020315010905031005060324040309080d080412030b03030d0207 72
    0x70b440c8030790380c0c820040c000000d0201051405001c0c002004140d00354020032400c51f0090030845c07146080e42e46c1e0840c15070300c202c0d034003201705501e941780c03074248140c0c0306001e070b5841e010410451034560798400517401c0120702d00c802880d405031642401c010480071f180c0031090010207011a1f10103411454050301901460f58010300094041c1d9500802a12507000820980da0028149040302c1d03401c4140b00600d84024200014041c07000703480c034501881040304440a500070782100a610000c1010582890f600104940c0718102588050281c401c001c2030b1403007119a1406c0828400c86c03244080340d902e00035290300070506620740c980e040d0b0142d00340d001144520080c4410401030301000c070055800300c01034000c80c2c1c1c04da480030f980783e4450b014660040c1d400a0700241101e030f051070786113540d11108050b180003185080c81c4c0c0e028841016000a42480500f10003405450b114100e040010b01e0108010406049000203500e84600303640aa072007602c45000241c20340340e5480310501c80c58046d50141c1411 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 978047697 1250 978046447 978046463
    0x80f0a1119080703050c0a120e04050a0515060a120c081503011b050a030b060304052b1d0103090b0f01230a1a0c06010e10122d080f0403 60
    0xc085250701c146480350609600400803030070001c044e201207030300303400c00b801c1c00c01c02d48107028060020805154003c0000d00c3d4998a00300da01d400101440180c60016020720507940c2030205200914191440d10a8290750a80c2c5c031540301c2142da00220b90811403c5100d8500c60714100645541d5540096864840e28550303216448030b0300040281802c84c0c01140c0003c828484031400c070204a0712600c01080f010017070b4500890040100c00008840303034000d44048460f81d01c011980a00750201d27032003a40118000c00d11a401d44c07a42d200000d008083c06c50070055100e400100c41c120580c0c020380c0444102900301c007091245180109108612020a00420054120544204140c0e1200c0203580342d508030017904000340345103405222142c500c142007861500d5801404014003200c0204109030081407c2440c0603824201218840104d03d030b160412407141030b41e040e008020540c00ba034481d100040c0d2118100100c0c5140c4250b115042442400410780240021030705503c0c210100504241c0c3d004200c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 978048947 1250 978047697 978047713
    0x2a070e0606031006140705011d070807230d1b0503160f05060903150703090c090b090601081801090503070c080105060d06020a052b15061704080f0a11 66
    0x80100d02d00003181d0b00940e80c40ca090341030090622400489050590801510b81011310a03501c20303003507401b20b03d05078950005026040210710350400c510002049500c01610b9481d04080c0010000c1c0d96200400302044002e001c030321510307200d8101d4003001d2508910880c2d000504000d08078011540ca200d100c3c402e21135140c2140312015030b004040112a401500c1d8203506103403e09103c507607001840f503150b06006051a810f441c125038061940b04680d1660001000150703071404040703101d0503130080041c0e14030308800d14903980c56000c4402d40003c42401c0c03069032940c0c0d1622004000520303510889855003000d905500700640080502016032040c18403220250700c1e00351250890713204840312507018585801c5040444d06540c0241003440750341c60140d1034010003c1d14104d54101140f258004295008001c100c0302506201d111801c0307a80c066581c210600d07244000704940c0d002158201c21015a002240400c0121412180d0024100140c030f52250310300b800c081e2030802e107500002a18051004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 978050197 1250 978048947 978048949
    0xe0a0b0708010b0d091103190b0a09120c0c03050d0906030b24310303020f060f0601030b01050909070c02030f0a080f03060123030a0b0901080a082a070e06 68
    0x141d030b81650f542d0743c9040d00701000a00d800024064950056407066051611900313039403001d1220541c0360070406040c001550140c54024981d0740020807030b2400c185031a859500080c4c1a80c019040c5121038a0480c000c0d4440e410b000000e400b031a4001007240c03280320514030b070403604030b0400d100707d07449600c0400c402025201031107400d0079460910a04c118000854001004102024255801d0f040c4180d0581019026909032040700980060b444551200300030020140d04201003803c2c1100d410190180b400c3c503400461500700080c100380d0505403654513642c0309900c184d040e1001c1c8540145011258105080d01424411018009a029010301298142e06e48000285011550b0340503031250b00c1d00e440051300c000700fa08090489810001380380302e40208441d59018002d08021001d114541d03a040603500c08044401182049010b11804001086a001c0122354000200c0d0040c07102e0703660b044070000d80c4c3c1c20841c0303113000d40c81c440c0e0000b07180246c444e40004450054480c104a01c491071745400b4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 978051447 1250 978050197 978050207
    0x6160c1e0b031b0f0309060a182409081206152b020409020c010b12010e07050603070203090a140a060509061602010905042901050f0a0e0a03060e0a0b07 67
    0x30141c1400100c04001181180f68040c03051030b20a240a004a420b02c600490b07841800d52082c2c03100c000d154080317800d100001c02d842c81007003030610640c820000034040d559102d690b0106c540d0442c501c410032208103603c004219401804174160f000820a9031038103414143c5440c00410340e0514014200c14203410904094102224408503008891403425100c030344814292002000013442056003e1000141d5104e0724000b4040300000c076800411800340d40c005010062880305244003442c0e0522000c8280d10501080300020380e5004d843c895540e5131130050582c614401e082c0031680184180000099818005000307900303445046508240450b0340d07040846032400350105642d030007182008542103c80750000c0d6038001c1381c81030519900c0e281e65800040c0444030404910b0512800b80035080312601300502d00e075040c9001c2400e2070390416540e46440340c010301031440c50301c0c14070000345122000c50b602d086400b4010f560102090202c0b401010b9401c0d29a044c80e2001c03035500c40010049a03c56001e1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 978052697 1250 978051447 978051449
    0x30c0b1305070e0a0f0207110114091005070204061a070c0b0a050901051309110705060c0403050c09040501110a0504060e1221071a1e04020109090b06160c1e 69
    0x700100411070515004000d961000b030440303240b0310b603244003020440c42c2e41d0015182e41402240c0c2c08950a60703440024110710300780600b0450b154006c0103c0c0510f076a506490000c840c00e01e181c0540c4a11396840460001c204580000325412403100c1c143d0901ca21a000400000d40f0482a00040b944c1d02c1120344818000c000c050030202d43c042c0301004495205030003038211440da020003000044c1d540d80d030321000c40388000c0c1c370102d440a0001c3c1640900004204854010f9001d203812482c02d072030342d10b520b0340b1001005815031040c80d0500208050003000d401540544042104080d59446c40d01000342c050b5105200d024041080b11403c070046140815645140800780c1e0302031300340c100666005851249603030616105a80d0144104000703d00c02103480c2c0500680c1c1442c3c40d1440c1046507040302142c08850044001c03411080070000181da100c1c8034041242c1802c100800e8816080002801a000380e040c1c0c500f044601001010902000320a0780381115201c010180f580062030300300018034030072 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 978053947 1250 978052697 978052703
    0x80d1805010c02062b020c0c031209041d060c1201050906090406200d060305010e06010f0b030a0204120b0402090c09010203070b06010203190c020316180b040b030a030c0b13 76
    0xb00001e01009400c2010080001216410641030260034440604401c56200420080e12550104080d5030141d0104a45000704908800500301306001c00180e140604c5100d441901a54880c0e031240d003550b51031414016062489020b80e1118a4040c0d440340480e00202017504050300030348000143c5003030412038280200300c06402440c8682d0740e80c03601f40140100d6151081901001c141c0c01d807200b031828020700b041001300003001c00c09a2540c14a0350944100300b6280c042e507009280100000d295444501013200c041c1c5080c1c0345c0301e564000101c4001c1c01258041e0309070081108600040200c0c000340c1c144194030842d40c1510320f0312030041840040c05100010f6015078000c10620021131001c41c40d8981c070050500c11031785003080b0407070b41560f0042c1c070864107004941c1c2e01041c241145824010003000c5131001105184040c541b09100340c101464200710140c1c2036584081c1c20702501d81e900019403d05000d41100c10400851600421081d14034106032070b80000400411811b140032034010f040260 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 978055197 1250 978053947 978053957
    0x80c090114130c09050d030e0411090d0f03031425030209010e09091e0d02010c030c0504120f02120c12060412110f1605031903020d0e0103090c080d180501 68
    0xa1005148005040c0c0400310410300c074518500245d195902c0c03146006a922076611000300381c50180c00c0c00140e59090950004401c030a0010240f661030301c516a03884140c12203002805541c45090950007045000007858036003a010040210b010f00c06e182c0e02421075440800f9030b01c1900540c03000c074200d0043c142c1c014001480c40c0e16238412498002190344c1c014914030140d848022140520400d0b0300c0d048035980d9aa5004100d103100e8558081c40b400100d800ca0341421304c002a031030341d4010b1007441075008407040842c0d500c41c18000e206103684501c40c0d86034003030710030f0790240800b65483d40c0c3c0303410340500c80d0b10030707088a00180c24485003c20b0041c0600d0b071081b1600c0240381616410b4403118128408620284655950307400030b00410800510040841420b60701071038101340c01d243c10060030420042002e07406080050000f83d0019100e100c100c000d142c03c8000c203271240300480291124800190440c2c00090011030440b0001c03913005049083c40e00c3e400c05240d8250328920040e0300390b20403d40452 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 978056447 1250 978055197 978055219
    0x6020c010c0c08030a03150608040236010f0906050d0f110d060c030f06050612041103030d0609020d0c140a0806131814151b0c07080c090114 62
    0x3502441d0041d180911031501e000c0d000382c9446070545107410000703241c000a80c84840c0e500e40c50301314400c4180030703001504e0300000602e8075030042624500791003242020105e650a82580e42c92003104000d02c00313945452801169607540c0390460703550740c503802450909071401000141501d8104000c02c2d61701d80c41944280202416106c500c030314240501c00ae504183d0180500e00000c1c003611464106c1061628000f40519035951040201c580c40d41205000c0d81c010842c03011441504054154881e42c002c2503080481d80c0a40400d0541c09100c3c1340c04281401d001d400704070340150f03402510458401031400c20402d4940f01c0d04540658002030f9a00c6000410408080c8440c0f04070842a0300072000b501c4025450740c00e02e106421500b550100c1680c0005020000c0304000701039410b0340c0320360340d4800204219030000c03002201c90b04019003042c0c000220300c121108002c0f0901c0540c0d010200d440140c0c7d440729a01c1b400350351144500c00c00c0920480744000086032010070040d03030341d00c2858007a150509007 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 978057553 1106 978056447 978056449
    0x190b0103050601081305012315040510140103110c01021209120a08130203070f0602100c14090a08030d0f05130b0601080403031104060e03150106020c 66
    0xd8101424032440f6a0711140181c2c00400210900000440a180c294010b018032101c0300705c281c03c80040c00c3e060501d03008100740b09405070030401040400360010403049620403501400c4034002d020040c480d58403080b1392001c90140605000501c0344011400d418940c20524080745107030740001d0300c1d40700741110042054000540000500d541c01004400e920a40101303003440341007008080c0050401850f42c0300341e01080f0380140681c2d912b00d40711810007060303500c2c1d8000d03500503100e41c0000e1400e14450b803094a8101c9819aa000e4101c0c24210100700703070fa84400700c0580d0040361801d0101b20140700384001c00040060480000d5401d81010b40c0100340c0720010000c0f513204083d80411400308102820003036000e0000d1034903c0f038956851400b03500030124503403078410b040300100c0c000c1003494101e81d002d84043d800700c00715048901118011181d41d01c0c2400340b0801600031903075084c11 = true := by decide +kernel

theorem cover : BRFrame.Cov 977877697 978057553 := by
  have h0 := BRFrame.cov_init 977877697
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977877697 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 977877697 ≤ n) (h2 : n < 978057553) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
