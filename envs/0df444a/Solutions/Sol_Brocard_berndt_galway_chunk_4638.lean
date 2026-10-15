-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4638
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:15:40.815579+00:00
-- url     : https://prove2.me/submissions/ff463607-b4d1-4225-a789-01f3751d7c15

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 833992805 ≤ n < 834172661 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 833994055 1250 833992805 833992829
    0xf02010f0c0e0108090c060702120703051c08010f0b2713060303030b040e0c0d2906091f060e01051201120b15210a1b08011113060513 59
    0x120000c0e42c0309810380904082665812a96118103103200c2d1143d8a8051241c0c124108012600150a0005c0700ca0416009601250b55850380d0791580c1d8200002040345010020500580c0c5044980c00190300d4050202040c02800d030343d25001d080700d954030500d0340360302c0c1c0070706529860f402d03000014880c1c41b55504050701c0010b107140c107582494002c00c55400200e0101380707000c88001b014102489038804042d103e4000348900442c80081092a102100040315010030076203140708100120942034440c46c43c2041001c036503040003000c1014400005040b201e038248500e01c4c0c0ca245c42e8140310f41c0e00440740c0c203080082440c0c3c074010040344c50b48030340c0000d01c09000a0078000240d940c90395148a2315980910303103140d01d40e114101001c81c040c80e10703011180d0212180a61a1461100440914003142d84904481c03045100d9a66a4400f403080c6110300c0c2004860070040183c2c91003805580610841505003d2404111602495495025001c1c00007000b101240e202c0c07416181d0f01c0c005019041c0c929502d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 833995305 1250 833994055 833994071
    0x60b130e070801061d061507060507081e180a140f070f0b090906010c02090a1407030608190201180e06040f0c2709020c0604050c0d050304060f02010f 66
    0x14014148025109580740700e40400003501400600c1000c0695151172035a0202c12a8241958104100606680e40c4802034175400400003100000030f264841c0701e40c1e00450325290585016099020007080301d131200103044450502c0201030741246a019180b810450030b50a03100407540d1a10555440080905001d60b07035452900c8000900805220b4003032044a10040d00e511140c03207206181d204203141e4400502c10b803000762070480100b950000301071500d420b003615650005000f20900345e40300f172442c07581e6140c0340c1840c40c04910b106038030180500701401810f140c40041ca0740c454140058031140d0080da03040c0c004582c4502404021402d80703058044050740c5034000c181c034041040c0d603050b2050340b400384108200036450007680300806442c0c6405021104c40e800c1002c600e50b02c81007804040700c14000c0403c04045600c0500000f66104000380031170b10707052400924041c81854030500c40d00c0e400903070740e0005078000126002d485842c41d24004418803008281d015000702410340c628a030030490a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 833996555 1250 833995305 833995339
    0x1208011a1e090315010306052a0a0e0d03030c0e041104060c15020a02240403080c0306030a050f010906180209060112320a2013030c030305030f070201020c0a0b04060b 73
    0x70b145c103890044100b000a621451403810038aa4201d10030100d000d40030b00b5818042c0482005040a060703641030000b01c405807440040c41c1c00158010850200f80c0e15440034508a601c40c41c47d01c04500c0c140d8080026410001c401030160040d8850041005115a42d8008000000a9100129410100554682c004d0440117074580744411641c02000c42500c1007085102d0101c240c0e81d01403034058079204900e44a015464485503c0148201d4062280c400c2c140c0c0090410403c049512250b9000003130696290300d000410b440c8200489900c03883c40b050203c0141e6646205a50402024240203042d01110a40c2402800d54034200c003000030b2000c0324110845e07000100408442e0f010700b82406850350b80703951a00444140740d038030107440e001c280154100799928400030480c000c0a80803c400c03043e42c0303960300c102d100030b9904200c0020300080140102c0003002054641c01140500095060140c1e40c540b60369a6420b400000d440c00040f503000c6001e00c41580e020411105004c0e00348003e150312080 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 833997805 1250 833996555 833996593
    0x10902030414031c09030507050703030503100b1c0c1b080403110d030206070f090f240207081911030d031a010c0b04020907050f04031208011a1e0903 66
    0x107050341c01002d0070030161454140402242d02c2008841c00006103c0840b0258070300501c0b25610842c2800401c00a03503010400c104019001544266541c9a607890240300703103035a071491980002c1220f0420302807036101000d050b101d00301c4445200d400003040015280c3c111400049002441542c02c940c0b02100c0c24880008001e105a03401841000d0400c400842807001e8414482c4014005801807004076801d80c2c13140300c40080035030003881c08200361500c82020300c500b00c0150380074102144908640701d00d07044a200c00c0d219200f0ba58000307050082d14100384544c0341c07050981d5881c429458840c3c81c504120b0741d4940c02c0d50100c000744c12030764601403a41000c2c0050540140306040f0181100004243e5842100e041403420703401001800207860b0380c1d080c8100103c016000c9000e0160a2114070b1190045001600055002d0b06105108142e401c1300600f0009040e0400342c0c50400704201c200200b6100380480c0e015a02880c11030208407009030707200d260b0b0302954801c1e030f501d4000c01000c0d07024500065 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 833999055 1250 833997805 833997811
    0xa2c030403060b2b080f0a270b0a03150b040b03040b1510031505041515030c08160e0301060f050a0807050f060d06030209040f1b03111905060301090203 67
    0x391003080840708407000c00c9a5a14440005030820b03071400c0b400f01300400303100400405540b0504e5618100020121510a1a084002c00e1030004c0c503a10000615081d680d49501244c130072081240c8c04050400d400c140c0e2612800104205168841d50200710000c4c60964640042c42c031400708585860300c0d02c010b07680c0d980c0b05580a071507030a603c80216454403003104402c854000c0c01000364580f005002c00a602900020508868101c0a68400a199240d034003076a10040450348155a58505140c5003800e1404003407061130030980b4108110003201c1d002a0715039041140c4407401a800034110000715401064064095019424070310000f80340c00110500d031081d50b03c200c41102881c2c3d21610100d0f6034004600c915540190107210040c01c0303081180c024510115000b0010a00d203440360040f480f42c00081d10100d0368000c000e6049401d0004c44c5a40c4160820018480e048151540e11003007200c0e100780c00d016200c0c00f0842c2e4040c01500f40d503c0756900a05014203150b4896035142461f0300203401c21 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 834000305 1250 833999055 833999063
    0x41101080702010b01050a0e010c0f03030617010c08130807051507091a0f090315072d090603020307111c08060904080304110f040f0b10090303080a2c030403 69
    0x260119030704500600440200c0c06041e900c060415100f400b0454125003410601410701801c6114000424440f940c090780702402030710007150755858040c00c0240300301c611040c0040c0d640b40c80400300d0f9540e0311141198018180b2502040358816504006410b8401c12000a06a206820b90415590380d1515007a1080c4895251848441c2d0380e1400d9841c0b100005000c0e20700060204010810001300602814024002074200c0741e481c0040150060b22031425034040010451820346151025140d0200c81000c030004500c030b0b015000c2214021780300700281e014040a06030007000040c00d00e4070801803030b008102e9160850786120b2007640329000a1044180d141c0016142c0750006d41c540c240b2000701805144d00c490b0341d500c0e555903600d5031203801d2070249001c1c0e8440b40c1c40c014900c07180c0c2e480c0248091130350300041c0000d00582210410074021030005441c000d1100e91181040402e0700075124a6020f01d6012004c0740c0300300388a047c40000030107841d2910040000b0041402c400800002400c29a441 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 834001555 1250 834000305 834000317
    0x2704020a081506090703060312020109060f0608060612011514120d050d0906020403020406090506040b121002070c1e031401021c1814030d110309030301151205041101 73
    0x1507a01c1030391140840014842c0070301d0000e01058603414110003990340315650b807400064160301e81d40c0f18180703404110700100040c0e44481400b014840c05100d9481c0541594030200b00d5146051080c40d202d5400824491003450038a00f040310b03c0c0303000e40003203007118488581800034503100c04202c0354012b107a048450142c4e414400c400d10701c100000d191184401c0684405080440040e0070f42c014085020045501c00e400b070000200580f40c0e405110050007140c03e000c030b00313450b110040c0030454128641c0d05204850320511803c442030b0125100f6840c542c401c0016030b40d110a81001a0035441503840ba00f82155004d0703064489241c070081600c21b03a407281d40c56420500000281b41d00f81d00542090340c140d5109158000f00840c526440f8403001da1803c02a01051900d036152070250002a0f004441142c0000850700c900398164030501c0341c50382c0c02c070824600b0b5040c0f001ca51540e9000500491103070040c00380b0600c15081c003d40541100b400b070b044003440149481c0c0303021104114080505804118 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 834002805 1250 834001555 834001559
    0x18030d02011d0714060313150b031c0509010302070807020d1202062511100f061701050c090603070908031602210a11010c23060c0f04060e2704020a 65
    0xe0049407010131540c140706200036010040d41085100d500180c096070800700c0007118400020042920102d0701000c0141c001200450707c2c0a05040031080088150100000305145902d59005020748400500a190060320740029103003824951003000000b80d800440503500a04000500d140503004a2255090302d02c00d44034101d200e001c8050a10507000d00540d04c407401d901c024031039030b81040c0c85e8a00c44100c494a03290031019404444502641500094480206000113103030b03c038a5440d50b92100c00200311038900945078805600484078110302c110b0001021420b4a442444114090400001a20b586a0500c40d0328084020004400c07406810f02e5180746002003c18003d18100d4032400014080d05440380e80c03000c01803641c1a442d1410321001c81c5014000c54000d108040110090780c001080c0d90380f6414500b440d085005246400202081080d407a48180074400d4900b1500c80e8282110010b9521000807030400400c6481940902c60201c40c2c55401c1200c010700d0301039402500e9010180d5 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 834004055 1250 834002805 834002861
    0x506010314040c05130b190501020d090803220f0e06090105010305070c020d0303180305030f01051f030905070b18090106110c0f0d0605010b04140418020618030d0201 73
    0x1081118083c140c42c1e100141040182812a9a07001c040c44601c80001c1c0c0c03031841d81c00070341819200725203640c45040942c0d05100c25601001081412020780c03c00302c0f59640f80c10621592441104c010300c1c1d04003c1d020b1600c01c000d0402e00154007902c0c585051095994aa850308207088904850081c4140078100001401c1d500a21550f402003400c1d0b0307603a1940c402c1c01d03000d0000f0541d034070300c040b420143d6450043d48a54100685200e42c140300340e0700c2555a09001944050750501a08510b2081811099801041006035401c40340455a0b00b408241c1034204c6c03c0c80c0d400d0003035590103401c1500d40018107045642400303000d4203010b40221b440280590f21800112035100000d404c9941aa02100d031441440c07400c0d2100b41e18078a00140101c03045401c5540b050103948c020b0f801114552001700d418010040c07034640004c1c038004195001c10442d1182d00120206400850300a07011380d400007607210b50b4680c2183c1902003000050300304c4504440340c0100074028020010001203640d01c401384038417a1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 834005305 1250 834004055 834004091
    0x501021207021614010804020316230a0605041802040b0a0528091703040b070f02010906110a0308090f120d151202042a090f0b12010608060402090402070605060103 72
    0x65085080301340d44103000040103694040340500180da01d072062481100410440d141c4540180c8600d8807030041c2c5000394881d000040c02c10343c99441c0700315902c0c0c4080c81541d6010040c1e5041b50800c00d02440c40303043d02c01d103030300084c0304542008058010000301c00381e005401030010f000406880f035200e0381203419880780d0902c000180c02480700040080400300061809010304511b010211429640b40070b54500800e8000c1d406103500311246d40060722404c00b50b6801000d1140104003605100036244202c41480303465600c000300c0201030200142c082149004100840782540b145482140c10f0b032003125201a032103410642070803805604082c880700e03201d06041e0084044a0070303001c000c00452410750800c405040b50920040d1014089060032840c03802d058003044261100347c5602c24141c1c00d041007406081c0442c0c0288012030000c10504a000f03109200c3e41d41100c0841c604980580c50b076400042c041d101d80c207403d0354407a00100b01c113411301035144d0095008407426241088081c2c5142c1c504144 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 834006555 1250 834005305 834005309
    0x90108010b1014040513050612030708070209041103100603060c090b1c0b0901150e180a24030308101418060a05040e0102180103051302060705070305010212070216 72
    0x40303402d900e00d6019050261090607401026003441c0c3d82440d407654003040302c036101c008440743e81c183c80b6424411981041c1401c0c511514122028515249198640c0307040c910030924001c0c0147c0ba203500003414030420345015084203000030240da6080702803440701e90142c00a80419190545800d41c1029003500601d042c1003201c114000b1641020b1350b4808100b0200d04601d417004106d611000441810390b0380c1005c090180c201010803c4203001d40d0040103142c07401205005000d0310b07100000d006141070825085038840380070ba40209030680005160000500003840e40d80d00440e9044010007010f8012070790078481c01c2a840524146e0b5950300e011880a50388a040b031b90400c03150401c1507007800e03560001c0d5a0100000d45080a402d03030f105d0109084540d080c0305009140d5020640300419456100200c0c2c011100342380030702c00360420f00c14038409ea600e2510024807070080010124204030302401105c0045400000854440010480710441a18119011401400f400c081c0c480001c007182400c1c82 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 834007805 1250 834006555 834006559
    0x2070f060219050c0405270a0b01090e07080d02010902011701060c14070b0712020d0c0c151106040b010608010b040f0b07080903161a070f06020306061902030702090108010b 76
    0x840264181e40e900681d607010410b550900600e140d981a41d1590f0040c1800382c65422060003102a134003060141f548584159151240c2060304440302217400c0c0341d902030648068540c005a960196440c40c0d01e0b0041a030f0245155009401c400711f2b085070194800c926050003a222003c402914014254120100340100070120303032102038400106004040340005422440b007262100c0703427590541c0021781c200c7c0508441404c0d04400301b801c1c265051003a44400d05507801d05c4142480595516404211540600c4400708201d03a00c1c214494410f207411030820b52041c017500d44505150402c804505424010403000c00c03203240000489003655030483d81103401c100400d90740a418464081001d0384401c005444800b001e1142900f161f4040c41001d40d0b2580e0036010007402490700303e0701200c2000100a0031a4440c0612100d0081011350241d4100142d00081c010399966618000038220300420340c1c188548060426040486a000001031038400d00032240602d40e682d03102c400e0b80c02d980c0b80c900304036 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 834009055 1250 834007805 834007813
    0xb0405060d1e2a080102090312090d0611030a0c0203071e030903080a0207080106170303130606080706080109140402010c020f04020c1204030c090203040203031e040b12040302070f0602 81
    0x400700c0e070302c2c20442d181c052505804000c00c4145803510a520300030141003616203440c40400d0052104200820002041a00e009608000188000989070020006020070403403000600181564418290b2240246d010300b0410010b4405880c064807900111095072403185414a407201c128000000e0b900e1280e800101e015914001c55504402078220420880a12103569004030005a041c0040c2c070140074954003c000351b41c40c0101c80d5003555829840740d111760304074644c0000c03201e0003c000c50b580b00d6604c0c1035007800982d981c82c000004124680c03244410f030054542c049103865001c40868120741211005010b150451600003080081c1039500034081106e40704000010b08100c40c40215500000384014107204048030000d0a0030307100001a4110000000d080c0100900380000b040501101e40c411400c510300351303000c41d907a0300c00c440c181c101410003071140c100d0441c03502c4c1c01c03140074004582d0740d9911521405d140c01c1e1900c5040e80d0440150160700800300390300c1d0b030a0195404132510741c0c0c010 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 834010305 1250 834009055 834009079
    0x70503041406070c170c061605071401142514121207031a041b14040b090105160609060605040b0f031b0325052e0f0c170c010b040506 59
    0x12172944c1e0860704c06907405000c0c13050132545a5503500c01402554030200c10340100c4507130b240740880c00c144039900705040c507070155602109180d9101d400300001c2400c49100e036136103400c107481700190500710f540000152405155100c0030081140039604096002008960022400c442da416942c010720061408203000c1c100000c04503807094004800303007980c07a0203d2099101d40e00215007610380c202e2500380c00d84150920685040c1c0c3c0403045140d403000082c002801c260074140d030612148551041541041030104040b4401665450510009507108404102c5950f1504d407481c0646030743c1c480d40b84913a14046418659040070601468102802005421484d0582c180c0010000d00a980e17140c16100303404d4920120f0b07500d207c0c619800340b603842104540e1480d1004004146001c04501c0900300134160307007000c0c00030201c01d400f0910030240c00c100c82c801e12448002c0f9615a10744502a202060000b0902c080b10718101c0100460310b001070090010203800b0b002e1005a80341502c100303821074501d43c16 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 834011555 1250 834010305 834010319
    0xc060e060109271e15060e16030209090f040c0e0907050a12050a020915030a0602041a0c06070807050c1f0b01030b09040803060301020f1b0118110d0611070503041406070c 75
    0x10280c13113030301c183d0361809044610614241250b850303400c8455262601424000c9075071a2065210480320149006c0d8603000d1441c01181248101503e0605100084400309040107030303c180701c034040c0081c0b107100b07000d034505074030503035a1040346200c2c0078051a90030b14003203064420b074039460907810303040402020042003c0c0d081c00189030004050f03c42000c00407071328003400c2c0d405210311710145000709000341c0c0750382c00c0005080c0516800401c0d5464000c2c2004a82c1901e10041500c0e5841506800c00c280240c0c0e030001c0c151500d01c60600c171140075002d028003c0b0101c0c0c19811040040c20500c030710402000755030300700540458510040044e44441e191000a0019000074011584500041e0002d8180141c0e54603000300c3d90411034010301c0d1f4901400092810003024442c00104502420384d074074070031155448407110101e14076402e0f4041c02c0725265031020301c101c5030050b5620008031030410382d455200e400c2441d200c1d00725008078502080040c0d440d03030b40344c9861410b0301c00c100c0c2c03c505054078007807070004 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 834012805 1250 834011555 834011603
    0xe0a0e0f060111011a04051806070c151b080a020f090f0a090929040804050f010309120513140906010c05010b030a140d020703120c060e06010927 64
    0x1003401e042200045940c003c0f00c3e0207018000c000308481459007121a2840200700544800408009001c403000050071035200c40020040d4000c801800c4c422807200503070070001d051a00785a400d191060415810b014186040101c04511101595a040c955180c0aa01509902c140e46110242c290140300002c0350b498205010981010020030121116a03116544001c0e918038039001d85d4010b810403000003100c858a9424044102105d104940c9850103544130803003070245002d140c3c01000140c034644400c0c0d0103940080c20a640168100c00003500f5548014450780c44003107840300d40300e940c0c60001641240402d400c40700c2c001c000c050720903c1e0307620401140e080e01ea60300d040da81076494003407200c420b0b02c0900004034003a00413500c0744c00000225032545c0c07425018140c004210741c80300b4001c10100701e0070701c194040308003036290140c03481c0b88505103100540400031000005008030000007440340241ea01c1800c40405010110140c0005069071078511200e22030060301c83ca08003414000d0b0550842 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 834014055 1250 834012805 834012811
    0xf0b0a050f190927030206010b0307050904060e07020c030303040c050603130602190e3a02090a0e0c010c051207080412030908010b1c080c03070f030f0e0a0e0f 70
    0x38000b540075071081001c40122240a07070001c03880715030f0b50101c0300307010180b05007044c505038203103508034140001940d00075a5490148201c0c1586030f0080040749c061031241d0125480e1b0880204180b08442e15100c40441c244000c0d1401d2015215404600800e410301105807446a40c000303c40726640791501c014002242d000034549910100311907a841b000a80c244003406109a40d161f903846466412030000d40304440045110f407040d02c000504212940c14800d204500341040e5080050245402c00c07126400714030420000e60180c00d5034200192000c941d03024695008083d0700700d9038000007800041d2600c40e0180c0c0094910342061400225103900b801c001c0c04203502c2035443c07615082d030b00c1440d0b41a16910500440025512650402a42c00b09014079490755400720ba03450300c1102c0b54a060302c1c0420100304010100800410850103401d0280701741e07041c19820400c00e64240c2d565240c01041038142514000210f030010002d001141070448002c2c013640d141c0c02c1003400759154802c2c01c0881d51401 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 834015305 1250 834014055 834014059
    0x5060606030c07140a0b07030e0c01030f0b1210050a15030b04031713020102010e0615040b0409020927070506120a1121090d0207030803040602040902031003060f0b0a050f 75
    0xc02c00c2c0800a8104d88610b44651841c0c070280060386220300d4111100040a400700007014140800391751008004109191031181c2401c000850700550322059000c4c0425090050703011011803480f8050312804036a402441940d039008101c5956414a00700c11102c80f0009002d00015400c0240002082080c42a400c42d00a007044081c013030b0740c0340b00ca2107140000c0316040120025a1800307030455809000d18404000c950010342030902e002d403c000c00105503800801d1181e500ea2000007090b032940d52000c2003150f005016208a807a241207000a840400300e40ca48404400114080142c034001c0360035000d0b030700c0c010711141c58000e9070710082c001080c0141492945590707074050314405405100040030300c5130703d0800920310b41501b81d801d100040c50040c403016031078100d46112154a507010502c0710540f6841100315489848a00340680280030315008000d007148004144048040c4548407181102c2c41594180704000300d11300700100307551070f0790b00f6990001c211003010300072440c200242c10426000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 834016555 1250 834015305 834015307
    0x1203041b03050604060e060a0b09060f01110304081606050309070504020702060c0a030324030c03030503100f091407051806160203010f0b01020c0d080f1303020301150f060c05060606030c 82
    0x50340c480906002050380c003280c01e142d40d04c800d010342c038800b41329080e884800d42404100027500d07000803900f00d81e0024181ca100b49a00400795225078012030a134080704000200303c9881d81d8540902c11fa0790380400c0030781e180c000881000081c4a91003a011a4481e0f40e0241c00351001d6071915007400040c0d088007400300c0c0e010360300b8082c1e40c00701031040101d4180540640d4012840d100c0d001e500c0d078038015442c441e158844a8214050011800540507642242d80c10300d441c1d5070381e548094602441e01107582040d00d40281c80100080c0a004c0341c1c001000d80d040f034012441c1141c888030020ba60500c1038502803884803181c0d101207040c80c60800080c0190740341c0f24901c60707903040c81940042c1c2143c4420b0070842c19243d4a40d03141310996410044042114002d44503410712802c2d548800c1018084d20308100f4070b281c0c00082c101d0b252982e192048004640c090000e00c10780701c021000d40c0d08070b522030041c20220010b02e0342c0040e68600c10303114035151642090207442241c54010510005500c01003240c4100c0f05c0c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 834017805 1250 834016555 834016559
    0x22a040b06040e1303091205191b032604050d0f031b14061608131e03020f0c0301200306030c0d140d021f05060d02210f1203041b 57
    0x103c840c04610a1112a4080c1e0552402c0d00e0068110120354100c00041c4000030b080303a00140c0e000669030071038508080250798001062074040d40c00c5292803102000c0381800ba40000400041042e48109140c3e036500c0f411032251419031800740790103241b040651103e00c0001400204812120b41390460f8005c0c98002902c9190703008400080900580c00c460302c614102e0341c8450014144566604040002001080540e0100700201100409003c403c0d004800301c0441b0104000800100301c00c40341c0d02940450104e41c1c0c2400783d103901710482c200745280140c114002c917502d01882140d120701d00d0203561480d28800030648003466000142125014030402c082c0c1c1585a540101880c1458820490403407204801480320742440079000c3c1c060155408207050243c09400902e1903100e60071060350019050ba10031000500c1e1010103c4081e40240c01c00000b00400f0038644640d0000080c6c100840300740f400c81c130303910543c1e8002c0f0729080c410312041440403500140e8850721880e8041c80718030004200903 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 834019055 1250 834017805 834017819
    0x803071106120105240310090b0d0b1f03050a0b040b0603121b010621030f020705011e05270a0f0f150c080a0207180209130506060c030c060601022a040b0604 69
    0x84c0c001d1f983d0140e0010b5402042000c500e180c01404d21805064030715209024050340c1c0c0f5044808040c1040b00c07a4101c0d50407502c2401104c8055400841e003082c2103982040e164200103494000a41c7c040e0340e4000c1c0a0700144040c01d001440d20381403a80031003201c1c0b07055100200300c030414001010f20700c0303155200d072800075180c07000781d820041400350101e203258503242c03030302c2c010704039004d001c0038041990842002027040c0da80104011a080200c00b80c406805400214110f641c0c1c0b04080b00d40d404502c2c0141600c1c00d1106054880311046400d4585252403902c03011083c4900d041446030340017151549006003c9844092252507070543c5500701103007000543d81c0c6407401c540043c607020300140d0040b2030400010795250301d5110304514440007145030400100c04100d4510000e14411008c644440120300d407038640d141100c05901c6000c02b500e8030381c42ea880c005134465100751001c07801881a241100341200c0081e1103400c602d5403800142807520b030b242c014000541066050641e01000c1844001407034 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 834020305 1250 834019055 834019057
    0x17060d1106041a030628032d140609010603081b33010b04140409030203090d060f050f221a090c010206011401020703080708090a080307110612010524 66
    0x2d0081d0f05481d04c9151280c1441120154600908210503651820310000d000b43c00101050340d0304002c030a208180c818403080390103a82e030700924100c800e4003030001d030600100020301203200d13012106840b92602c50412050070f803070781400082e14000c41000003400c01030074031000c420001e0118003a00c3c407240c2032144e003480090f2161a411941080d46202103042c1c81c000f0785c8503001d019640e29441c102070402603c900410786051401c4d008580e1b51083c141850300070001e941c601000180380e01000302e0540380c818084d003a19090300090f20700b00800304d82d03180200c6240c07600c5614801da00220109500d2074410300010003031029604079514030304128600703042e440c041d4072070b84800c401840400340b08000245880416848846c916203c94400c9101d60707400b180042c05c680c1c00a1021b600c4110300c1c140301ca414400c8221490f408545c00e000007030800c4000c0050310f42103014111300c0041d2420181131260900c103203d8020910522035005201928004801c51144007070001074810110b4042910845 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 834021555 1250 834020305 834020339
    0xf07110904031d011e0c140d11010f05010317030a02120403050403140c0a09020c0f011a18010e042d0b1503011b030903120c030b0117060d110604 64
    0xb865420881c03100c800d20240c07480800d6820728200d01d00e00d00a174060740318040101c9103001040f0021032a00113010300c1c050044028500c840039600c200c0c40c01600908a806401c110040d01e500f0107508401d42050761090314103c03900710f9034206000c0c0c4403200030445580000c1807200216800d104030340d0b0203045800c042d0b110301e1003038940699035415030400510b0910f14510401090b8042c541880407501c40c509002d080f00c0d607490b00982c5601c1c901a0460401091415230000e961070070031481c19448491044007c100f000703464410008071500c3c040c0310401030900842081030550404603000603404064600050300700c604036106414550b83c3c1106450680b1419109091802d080c0403540720302c416a500d41c030001b10001c01156059500c416031102d2850303808410305030340780704070740070f1500503c0303100d040f2400c2680401c1403070342146000d0014000e050b00140019078200c410b1140c18148210365002d003100909401a6000d00d540f9000707210700304648076400000c14080080c0c1009000d1a00034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 834022805 1250 834021555 834021557
    0xe2505040e07030204050a0509190e2b18030f030f170406050a1107230304050907020721080d0c030b10080a0b01020102040e0f1e070c05070b030702030f0711090403 72
    0xc1c5c0d03949468104100c3d1002508054800c449500a0141040e5900d107070108000c400300010544000843c41e540c1080d01c0c10400d14080a040f400c0c0502000030300c44100c0301c60003561a02c40b40c40d450b2024001d9003201c0390100030b085403103494040002c2401498284070308131040c03400e00f20320000481d42e41503003d001d54040350919120700c02c0c020036295902520002c101c002c600c45052024903104c200e0300070151001c0d04407406c012015103c0850040c022075010f018064100c942034100703084001e540f460181b241c143c0501002504060400307913500ca00b591141c1120086060003072a486440c01402e11007008400c0c1542c0f407142c084c840c0c0314104085211461515041c0c4d040c90109004800c2d16085240c2d00e0440e4810007051000303410b821100c940120880c2c102203820303580d2004414240b600018610310f12420350b02005035440c0c0c810f00001655200e401500c6041d591100d00c8482d07800156410340140c3c00500c904221003041c80042c160140c0501401010040c2160124003140819a8140c1c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 834024055 1250 834022805 834022807
    0x30c041203112e0207060212100303080106020c210a140a0b10120b090124140a0b092205070f110a02030a02010f110d02060a060e2505040e070302 64
    0x1899542c051148680228800503c0d4a5035411a03854840304249000c00c2041e10707074080349040038880c031035045d00d2450030445d5605c10710b42484a05200f0801551008400050b241400450502d2010402580f03c0101515607417141b0b40c0049400b030360802c0e41e0400034940c4151258180462481c140c00284d001c0701d00c0190010b00c000e4107080941800c000c0580c0609a0110341c10094900d00540300d06c4483d42150310581a6203030481c2d2036024040800c4042600220440b0074079647c145601c42004a803020310550721051074850500030100d0f10380c4558800341d407080c0196000360a18410b403041500c190b10308140000449102034080b59401d460400014181208400761550003801c0d2508181041d0000d12010a0301d0780040e9440c0c0108074028100815a0174a18080d07020f480c400142504030030239190114031018000b03560701070407902017092038140b000019074000e40c244054043e4100007001c01000c460a89900407401d41c0204000421804010006e10310912104460040340c40307076409 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 834025305 1250 834024055 834024077
    0x13090b0c1305010509060703030507092c06040c090509060d050102181203040f0909060b100806040c0c020d3008091c0507021e030703061b02150c030c041203 69
    0x50105481e580202c0e0501c5000c10030071115995410980701444d0b414030f80400d041e90b40030003c0324011225808415400c1c15090303103a20080411031303030302c001803e241c3e80002c0c0d81e951a001c00c825944400c154801240d5881c0d0700740018244200e00300e031b0081e000781a40000c1d84141d80c1740f40c22a406501c2141e038001941c00030b19554600b0300700c0c800200d800200154200b6061100c52030041000303124400519503148244010440c150700140f07441500141407290503070032842d0141c1010403c940180c80b072351419007000ca07214090b400e06c5010a4001d064404104595510182e40c4030050000003880403154900c400c0c130311421031604140211030f1303844d03210a08003c041541750080d6a04c01d0302e50b400250001c1e00e12254800180d5410980450f5018000441450182c15003207868185036014084d0328804002c4c0079064006003408840c501d00c0250b550003d04080781c490a80e041405d482ea060031010440083c691405540c118032034501640c0760a80d902c0300000040c5000208070302160500f119 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 834026555 1250 834025305 834025327
    0x110a0e040b0d33110c011401140120030406021501080303250c021c0212010207020303040b07060608161d07020606040c02010609090b10061106040213090b0c 69
    0x507401c54040240c46000400515644943c09806410340c400d00c1e4070355403100c54107200310598051880b0440c0d401d08001c0c4074103c2c0c1c1d8844241c1e2107130084d54100d46c00c140340c1040d262407100c402030484643d0b10803001c544c1c2c00840111441c00310205e07019040f0703d60380b0b5a02c08850b424801080201943d400910290820343e9a0301100035050380420040e410600403c01c8500d40c072210704009100a49064540600b5488142c03003171040d94038042d40040b4090303440240b00d03400c1d04070110341d64000c0760424000396500228900381c0c070030040000e40580080c0070811007600c02d200501000b522604000c2840ca4a80300601e20745000c090605014220084c42088143c8070402282c840700000b040c0514540b40c140c601964401c0c0181803940910795403194400c501c1d100303611500c05044009001d12100496003017114042800303440e240f4684074001c0e4000303a098040c0d00005620402ca6004c0e02440d66960200016441080b8061030703810307210300180c00018000c0754814410248040210380715580c3c0c00b0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 834027805 1250 834026555 834026561
    0xb03011d011d030f04050906011806120e160504111b01020a1115010e19050a0207020a05030a1a041a07120c0c080f0a09122a05061c110a0e04 62
    0x92882e805070004c100303005804180ba82250103032503041c0c4602c046611000012141040c0e4007690b80f044801a100c0072525603404001c08408801c0000144a12540d054106864a1004541e0a5a0380c0446010059810650040125907211000c2c41e4204240c1501e00080c18840e050010520b0b540000e050781500d40140d56240f201c44002c000300821480700004041680c3e0600410401518030000609142c0d1000030491280306a403e0503c07050508100000282d084038004071300c5081c80140104203418001303a0b00032215000889a00c40c10b00d181c10717681300d04c3c1c03020384180e903001c00c03120ac10314000440c803003c1405040d40380e450749502082040080210b41e41c1c03043c4d00080240b40d9600b880444c0303c1e003058801c01900a4082d07655006042d2054980300310075801012444600340a88040c80407184148800185440318240001242d94003c0d40e904100e01a2551022040c0855003d110306e0b00040340d05c03a01c51110000302c000c2d210702d80b5492a003120f005040003517080e201c501c5141c201380c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 834029055 1250 834027805 834027851
    0x903011107020d0b040204020c03040303030e25090c05070c03200402031014190f08100c0906030903020111040f05030705100c0b0a0924050f060a05040b03011d01 71
    0x11040c20304200e52a0b00080355110240000f40c03100d440e0784041800d641d56036048500341360900048035501da5991a000e805849020b40d00300d194020001e410402841d20322084800004881c582100c9900340780c400c10003000c000b0284010000b00303000c10030010b1a0249840081c500501a003000d4002d110845820606100d0032903004d46d0045c014480c00803188640746c0203581101c083c1c00c2070f000190340030031220909423030302c40144904100b00007050300300684104c0c19204c1c1c0308240c0785070124079418201030300c00064a06000074840881080454442e03801071140794841c1c400800c24254510341c1c03110a40182d040000c000c80c0e44d6004015903d81000100c0c000c0c0402d0380e2230001d4445161000d00320b60b1141102070040c3c64003500141c2d110071254081602c1e180d01c0820341c05041580880c2000038403005114001d840d1503d00441c0d5107082c10007410703100740e00080c82d0504043c01c001c1808041c024a04d05036403d90b407903299507a102200781c113489240c2204400001040400000c075100000381e05 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 834030305 1250 834029055 834029081
    0x603060510182106090303020919031a07120f05180f030a0c141203100806090a021504050405150406060801180c1101020a0f02060106090602031804021905090301 71
    0x142d070207501d10612807000c00d01200e01a542840881c1461181d0301028001c00c40001c01440c90282590209a011307406814014401d540645490700c8000301082408410b02000e48081100c05200b200269010350311035110403d40307001c540700810f000c03a071b01c19103c8026000526a85a204100d401000c0004200b8602c03100001041080744112061383c5a2003072109001c100046944454203100c402d507416408100601704480c10081c0307850362050140c0080e40c010844240c680400116407000243c03040c0503052000141c8590301c41c0354200140c3c80c42c040680038040b907040c400010325503a1881030504c100c0c0c1c41c0301e20020848000c0108822103045400c1b02080c4001e45005020440c041102803500b5521040d00040c41c405101c01903c52081040031301220351300005106250030749c484d1031555580c00ca03400311400c5988030001a581c049482c002c420040c3d0047c030415441d010185269207201c0f070044c2c40140b4198005002c80c04140b94980440085400010b2003e0141024841c2c40369004d46 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 834031555 1250 834030305 834030317
    0x10c020c1503150409021827030313020a080717010e0102120a090503160303090c06050a0c0209220305071e0c03020f0102010b090114040b09060d0212160603060510 72
    0x46029200070341c080a8101c640e01030907001c0c1039031140c41e0b40e40001d43c5941c008054004095580d52410b4514001712655800192841e1001c0301c4045090600c1d00001041c0019600319a40c60b541e2414514800c84140c1e80b0141c402c0700090031000c20300c505000b50154000d0008101c1080d072110b400d45004806054160f8410000808601c42c01c030600c1e034219160306400700c0c000403a4104a4030b1409a5060220710980d902844002c040e059481402c0d034520600480741c102d42d6038117050b98503002c2c0150311404504000c0e11000140707031019009a1102100e1150b00011818464001750f040b9000000c9002c03c100045d04000c4c052802a0000c007182060040280c0b40c1c1b00b9511002254218403000b07004a20f26004088180c3c000e40200700000005007a0360025a59020043c10360780081c00c91900171490445d00708880e0421100041c0b0940300178100c0f224801d400c4d030910580c4030300201e294185000300400079803032460701c4510318014a21aa00030032842c0c04d0500304802400008a5a070074802 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 834032805 1250 834031555 834031579
    0x60c0d030b09100608040503041a03090c040e0d21020a0e3a2f01090e040206030f040305121905070c0f080f040b0403321b01050705010c02010c020c 65
    0x20b4980c0d0f00009032419450044002c1e00c90346013051550040d41c0000044901c0c100c1190781c04462407018601c00c4c1c8005017210414001c1c40c003808100c0340601c3d02c072416034100d048080c007824000d040d0020041d650205107080c00038030401400490b00074001501c0080d0f1460000b000501c0c0200300f0200c941c51100340b41e8200310060030110421301d00d014184127200c000640000c1070000c0c1c014103215101e04200340c08480380e00030117101001000810101d01250340190041002d12842090a100700e80c040c2c0001c1c51034a542c1180b030900e08004004504009041240119100100c065903000e84465405051504c034042214016104024441e208011603c00d0003001320380c120401000d15500a50901e65422611b02888010310954200c40c40d9a2400200081006004090b14461000002900c002c0e05698100495800103034a402c0349580e05c519401080301303031454140384041a0504140d80fa00788503550701ca095400503411440907075500d404c0c0030b0500345c041c05940c1c805c2c00c0842e92010b2442c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 834034055 1250 834032805 834032821
    0x6030106120506121608010c0905090c07051204030305030f0105100503040b070e0316090b031c030e100e03070312051e13050106031b060302090112150302060c0d030b09 74
    0x602901d4801c400252904042003141e00e490900c00060200c2109441e003584020380d009840342482c1c8a922000d40c60030142d4a10a48201d0070601a110010b003021040d881c3c0c0700d541c41c0c035900440000d82c0c0d10702071500315010a001d018018402144a43c45543e01c0786401000d151524005911242c01008000390304050543d10600701c80d4803e9000341c610003242c60f51541240c00700d0181a1580c0c05200764444407068045040f040412103081160030f0146006090a050315281e91201e100802c0e503400d00505500d40c001c5d00044900f003c21412074030010000351205040e0750b0081d01e8140300780c10000b2504240340e80005c0e084000c1d180090240000e080038002d90a148100281205403600e4400108550390201c10f054403e040c0c12900902a9507203d091048074960600024100c0e00600c1400040c00c2d8000d0003610821072050b107031240c8000c2c107664008040c101602511264280c00040440180c0d16140a00b9140c004180101052000210050100c400c24030803140300b40030b2842001891 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 834035305 1250 834034055 834034067
    0x180b09010906110c04050108010f0609090317040302030c1002041d0f13050f0a05034b091e04061703031519091b1d120c15041406030106 60
    0x4038034625041c0303181070761203e010b03041c26800401c4540c400e05020000801c0541504646a10501980104182641c5442920840c3e10899009002c100005501d8280300440861142e0207806070041d40c1c5804075940e40c481c249030044501e00250340d804039042c040340c641c3c100405400d181d825443c0c0147e0a00a065090781c1000818500c41c034418007407000c1c1002801c0c0841000205d10000f210b26820040c6070440e00e903000784050301c03110807030381c490290061906c58140c580a0746500e2024038032500344000c14501d480000ca4101c072900c0801c400c0d40151078a05c02e048650a140d403540c1506201c80e01000309540250344a10415060b0342c80c040110800802180d411020901c1040d40c4001c4020210301030000d1f0104480003400c1064001a01c0031060308030280c4020601c3e07100c15a030700100c50035030b42c08100c038180039818003159030058030a0900840300034521031040201d03280085914001604460f20707001c2550704071004070f410045a04850644049040704a40060556060800042a03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 834036555 1250 834035305 834035309
    0x3301b0c060b03240f09030a05070f060e060f04050106090207082d07050d17071b03020304080a260a020d051305091e070504120b0a0f020406180b090109 67
    0x95555800d440100c6907410882e81c940400c4080415500c0142000700703030320010382181e952a69517401c00019401250200454105112035158141446038a40b603590044080c40c404030b40c015902d0003082c0300288100506032081c0c2e9510035405e032078503007072426900b5078481d58044412140180314550024001c0d1007580c0030010444c0d101001c1c0e0000043c42203c1c41d02e0201c44580141000a001090100c0403c400300103446680310138450342c0c88116989003c003c215401c20011704207240b0f4140702c0e0b980340c240c091072502a10459080980352000e15007880a010b00407103039036001504415141e280c42c421000301c41880300c6160309001c20302d540070307444903007040d084810003000241814296860b480c940b0701a000c0a030035480d40e89080346c59103010400041140d001e18024000003500e080c4a4400c450036154024003e449040003907132101c416038030190140f1541e076211313454808000c4451001c0d00007004141e8606004a41c000e01041c00030a882d00041c01a01080042c004166040301c04101 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 834037805 1250 834036555 834036563
    0x21b06070201080405070906080f07060c030c0b070306051e01090f0e040308090a150203070206150a09021c022d041a070f0f080d0b030106140d03301b0c 67
    0xc0340e44901c5d0a90810b460358005c4001c06180040103e220080003d409071105409002c5030145600c030441a602d00604103001000070702d40b400c11b10f00080411600c15048000b500700800c0b0b45440300c00040d018980d0003140c0b50884a440d2a00c071166911242c483e000b04191085032a13103904103035541c100d0000082c4082c0c1030044160225910741020010819015000010003060301005c0e00c1d404c01079403068440c00300600c207023030100c1c004005003207c6010400c1c0c02841c809280d4a0515180c029401c4103803031200c544d004070750410b000070729400107101e049040850f00815401000980c4030440603c0307110061007205210912008805031700e0441100c514001c5141c6130300051030481c218101c0c098009000003920417a000800034070310007030003041140341814800d2214000c1810300300e40c01d034410800c1c3d005000b4007400d494103040641c0d88403140a4a000361030110000000000e00a80381060090740da21500c556016840d00e115088801351201d200d504210b8030100300034001041914050 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 834039055 1250 834037805 834037817
    0x15051305041703090a030905220c020102070f08030a052401181503050709092003060d0209150301110403112e050301030210090b040905090316060c021b06070201 71
    0x240a0108107202080003862030350b040c0d90b0b24500f40e4045a00c540b40c4071001c80c049145050041820310346660024600d810706400c40e280900c0034540302001e0401040e00500750356003004080003254052990019031401140035139a03c1c20844418400c44134020240f02c0d001581c011345420003040a240c036000030000f481d0011008a982c0404110a440c640c084211401340c0103074041c0e0a901754000038429102c6459015880e41d0319400340045d2407400e1400c4048081012a016410401e0b81c055a0001c002804036003840880381e0120b60412802e83c1c940d8907514400003052051301d400d0003400e41c80100452088d09207843e5982e28860a8a5000305a11882c2000e01c2c000d2901da804624020714484643daa400340c0d6910714001e00716a000780020f038059000c40b03043d80c030b040b8060074900046854603a00d2918162410b80e1960081001810342600390004100d24001030020341c04030294203000d110006000b00114001a140c87c40d202e808910006583c0d806840ca0703564801590070041d02800d100e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 834040305 1250 834039055 834039061
    0x6120b0c250302280204050c090105040303030f0603061d011808180102011e060806130812070509032415091303030209030a0c0501020d03270503090a1815051305 71
    0x3039040204049a540f00411003124091000c42c0713081c81c0403080c0340266420090354481411040c01403003001b5405000c500104170030400a4402ea1000350201c1c10b0071400242a43c43c0e50784c807010f83c0d82490303e410b5200c10f942c0450310041403e00c80c1c800103003200444401111055621018140543d004ca1003408060030a00283d99000707402c82c5d4010102d4a0703004c40103000d00e0444000912003801002180d00c12100050040c40620b034800d82e000350080c0080d81000030002d50000e81c140014981c00801c4014092020f01f500c0803c84a02118810030710301035140b40c44049880d40b02001054551050f18030500100070f51a10036400c1e1f00f10b411107910748031306071030390400f41e002e0f03c036248486400d813203071200ea2000c0c40342014440040c1d070800d07401e95000c027071404011002d581080d001200e846903d030b8041c20050707a01d0450742d842c0701d204100356400d0001c054002151507180d9400400302c403901070242da80c18107403441062210302451108061503400d0202161045800030003c000703441d030303030008 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 834041555 1250 834040305 834040307
    0x10b070510180b0a061401080907090b2d040b180c0f0c031b06100305060115201608010c0e0402030a0b0306011401021014070305100906120b0c2503 65
    0x215160342508030301c1e01401418882c01d100b00502103881160003005841241e0411b543c46915214042d60980c0f005100d01411700b00b2920084c07075208001523010308108031b4a0b007010b650244442004c21542080c0300d00c2d00d504070601080d14020281c1c1c038400e6246450f43ca141d00140882140c0140c1c0d02c2c0049078607000d940c04c429500d84291505081c1c01d100c0410061144180030110703000081818054403025100e444c01c0b00c0110100e800300406035001500140009445481d001a40b611903103800540e00108452982c24403541300f49040e6507030809080c0301c07140c402401000c4010100c00c4000c10800c0302e000e2000304000200445544141d0700040403c450010542105044041c014207a915a5a40c0c100342d54130a845d0708086400350040c001a40074400b11841804500040200641c009507903c020450061400414681084100b0400070602c003000340300d14005000c48a100b000c08203003a007007803a5a0000201220a4018100000341c0703010f240b040b00c20000003540081025040c15131034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 834042805 1250 834041555 834041591
    0x90c090705390703060f0b04060b0403030e18160e0901140d0203100507021b0a060906050c0a20090a0e031b0a1208040605060a08061801181406010b070510 68
    0x12402c50207102d028004014030040394412400b90040e40d02c108140700040c010b000a03124644141002030105000c1007003c20301603400e8a42c4a8001880029120034520704c40c64880e10a5a121440d11000140074600eaa00714038007a80703c16040354201c80030340c075140e014640c070410480c00e50701a5950400000854608000d00c1c80740120354281404149054103000355518a02c8258144401204030103c4203400c210346008190741413503403180c03a0142441000c3d41c051b80002c00b11102072040d411500c0205083c030140680005194210300d454210138000c00007944806040c03010250728112801e2003446002086072400d4440b5600120000c081800e40380c1003554a05000d480c103044003840e00c0d001a03100000c144103502c034000400003502e03154103010b0524041e010346116584010041580d210f0210010f20000c8045070002c108961540310100020082400444081c501002c04a0546070140300e06409054118a42c9081c45203075210280e9407031500100d04401d0769508115008102d6101c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 834044055 1250 834042805 834042907
    0x412030c05121609060504030f020603190e1c020c03190807210f0815010806060913020a092c0406020c0604030f0e15030f1509090c090705 61
    0x80802c4000c0c1c905111004804980d050010b80054546400428014095401e0711f095941261071404180c03116803c0c0131180d400505101b0900307025203080c0c10a0a0240100f54084902d18094011060991448040222070022913029504062025403032902c0001d5520114400407000c030282214504044600f48299503000c2d00060002c3c006080f04104621f6609442c0c5107035a0740b84041b4190401112082d00036503042c50b0078089241c1100b4107600c00d2603440e821000040000b850030f010880007c80c107880301e075048802d0030b4000c01d208490b20b4100d81088018401d2076001c450002c0118040144498688000221880d14030b01003005e000c2154103071a41400542c04560076410f0500300540384034a91441000001c501282c100598280288403005a1030341a001a003543c4660352401c110780c06c000c1003104071201111214001c2d03034440c903c0700c3c00b914081000e400b002d44044140550300e10018a0b20f0244801048604012000c6208000701081c070040c95100d486108000302c1c08488141c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 834045305 1250 834044055 834044077
    0xf0313061803090608070906050d0c1101061d180703081c0c110105070905030d030f02071721010e0726071d0901050102070522020d020910080412030c05 67
    0x20301072510405801002c0d580031307070b0115210965580d0381c41c9800c80f48031003240201400900140242034800c2003e41101d80710000300d040503520203400c442203908442103584900c0341103418881040c4114001d0850607081891100d0300804202d18107499940c8900720710004068110024031010b0041c2040b100c1a407601204100380441e062122008010f80102c40e84001654a00000b1a4040e802404c040c412103401801900c840b1581400550041c125140301002c110780801070034000521a031881440b62104603042c0351607940355001c02c1510120031002c1080055110014400c088042410030751011716032a0036a1100c00d400300b80b000802c1740d80c1140100b0080401844112600002c05070b9100c0680400b001595a2803070170400301c07020038070505d405030700401307424011414003649030320a40002c10350b40700340c076180016004103c0e4000c0c0c00c284800c2d03501003904206840c0801c860b6003d40000d1a02111b82c3c00d02d911051010142d8603070303102c14180d5512280c1c04c03460040f0251420147d00c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 834046555 1250 834045305 834045341
    0x40e1503060a0902030d02010c140901090b0f0a0215010303140319050f090f0601031a071407050123150405060102012409180309031e05011a03010b060f031306 70
    0x22012120b4003038a40c00310201c0c030a0080c81700717401d43c0c544140310b0004070044c65a40d44405812852105c07038560b21001c0d40e40e041010414006c1102c0c000e4800808420380ac041e082c0303030784540b00c640081c101051082c1c0a00100f5040e401000405e60003000c10301800d1f0070140740e13980c0e6115000b01741d014200c031141c0ea03003400c1d003810104a00620303180c070b82e1803160b02c5900039070b0104094001e0b2141c942c20700340001000d031455811210892141a04080c0d072010032810501401c0d1600c0d03280300080d8003c1401100e03d0303074641446c5000a00441010140d95100a240f006141015a0921107c620070680d6a019664810010300d15a100750454001c00c1e40460110507505801c900d401000d042c10700882011320305002c004845c290035800c070180e400d0341582e40d0004c0581140c0d25151b868104520f02c0c44040d18a8180c01f01080e002c0c0303d0b80e00356040c1c0c0300507507000034100401d044c00d41d0640072005100380d0046c0202c0d00c03a440b641084070b5108500e680441d81c100303540d103094401003021091081032065 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 834047805 1250 834046555 834046561
    0x70f02060c09010c200f0d0201090e100e040b07030c08071e3e0609030a03090203010b0a06021c0509060a080c12161209150905072d090b0303040e150306 67
    0xb89602d44c5c0c0c1c6600c106981c0b80103442c0013030040c001100392080c4001d0020319800307001c201c05082010710300d80004c0e102c0f031800c404683c0c1d00d41c254440d0301c05031303015a0704102c51421703c00515050710800e4418640b0b41031500f40ca240c50403000d460001d03403000d81d2421081403151516a5846405455090050a2030803410703903030400040c0200d000c0104a40401020320b8040006e00d0310001000c501c01c00c0224001c601d000003885088000d0602804226019903c1e4000e002c180e545400c92030024000507070081014203054200c0c154a280c08940d40c078207001040000101a4607408100d071000324141c100740c81c42d074803684010119481041401d02604201809000400c000e000322203104040d2079690304035012900b5076031401c403104450000e1080c107a00044a0402040317811200b0558015410f50310042c0d80e580c801d20140c241401c220380012005440c2ca0302c001c2d014640c6001030a41c500042042c1a080b1000c02c0d9684228016400c040d4517110020340740200c1d040044130740d034001400b80d9110b42 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 834049055 1250 834047805 834047843
    0xf05010e07081b0f22060b18190605130806011202010f0807080103110d0605070e0316030803011a0409020c070f1202030703030e0114041706070f02060c09010c 70
    0x1c01c26000765007590041000710301c031107024804140003460004040710b00a02c001c604200c11707072024080f5841c0e1218101c040c16014401e5216810080c00100410740d910701c1509101c8408102d041d030b02c640710303c03010b82c0c2402840c690307100c04105580c01814420343e20a61203102b840058115403012a072842600004200d04400e0303a501c8504c14400c0c0c031090ba4588100c602503417100c10445102e00010008801000400c868908060a90601410307624100429071522400d0302c104540c46404590300ea9461161410b00b004003542c80d4103030958040d50281151b4a134400c52006101c0c0c41142c035a0321748841ca401001754119402814640c07011941d40303030340a020a03211800d501c5440c001901ca0b02000035440603001c07030000a558000d02401d8401c1c02c60390700b51100031564504504004450303d4218600c20800e0041000e41701d9405014014402d45401504e441c500420035002c0080554000f066542c0015105402031503070801c0e551a403c1160040314038420000001d810341c09041234840d842 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 834050305 1250 834049055 834049063
    0x13090f050706080c07030f0c05160305100903050f0d0b03030406120f020f070b0405010f110301030506090a021e06120a020318030f090904020a03080a12050708070e06070f05010e 78
    0x1944103806841403240d40d402c003a10100c0c0101c46840110108000500c0000d01c02c0b03c0814114242d420141c41c0b51445032115860a8200e8103a401440032112061060003410051108c140030008010700c0b00d160295002043d502801034a1902c1d90004034007000c0012058000c10042d4001801303ca0315195a014000d00c41e00721103090070002032504101011094a90003201c01540c1100812813030107101d541e410140b114024415943c65598401c585074042d0b01e0301036884210500c43c580c54881d41103080040c2060782c047d1002246612404c01040180c881128061125031071340c004040d401004000b04569200e0341c1e90454200d402c00007009a46007965010710700410031340f0a010b22030203010410350f680344140703031000702c00e83d00600c82d0f54981e1400303903069940171b0310240c1440909651f0380c0c0c03403901d40e41046150b200031400000207940181550711a5a601c076043d444e0000c15400c1c1404007801c803520301940d450041c41c000441d030091101900c074134580302e81d001000704440b026952885031a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 834051555 1250 834050305 834050333
    0x40f0525020a08030c13090507050406020705240d02040e0705040e13210521071805060f0705010b1801080c010206040b1824040312291309 61
    0x310041810503000d19100090000056900540242c55900c1d018600e00154002d882c1c2004805003042010800e000c1e6802003d000c4c08050321816112824180b0203030030b01c000390b0049400f41c0b148000100000da20f000c42c3c0c0e03015245408403146d0302c61045401001900c100d40140403039000f410140208190721000400480c0c0e0043e030564280e0319110ba03100240c1c05500030103402c1c2610707000303201c0304d4001d2072050444243c010f0400500d44030104030708081e0740802d02411000c4030313403003170030845c00c15000204503d2440e5516200e51802d418000041c4c150b006006d540c68415101156031403c0000941c071552032142d000386002c6245603640ca000d6800c032400d0040d1196405051541c41030b550001a80500640c3d018101e000f4564030b024401c8600704a5240d60401d81c0b00e441009080728507072503992600406001c4605d01c03d0305c2d0030b04015041c2203140668000341c0c0c1c5002c249614100ca803807840ea0b206850079410b41c030f0903003000c40040c00c0c3c02c0c45280c0000c2da452501c003c04041042845c000303d4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 834052805 1250 834051555 834051601
    0x2040f0509070c03020c010e1206040b0108060c0c071a0f2a1203011e0e09010b0901151d0402190206270d05070f241113050f040f05 58
    0x340b960380c641e044481a144440060260340301552507025907001e072801c80c0b040308002d40380c582aa42c854540a24240c02500d040e644a14680014030007200c050010b0380c0d20034400189103240070b503056826540d800c41e920503090f03150440140942110f1100003103564100d00c1c0e40d205600d03408412124000240c0131701c47c01c01118600b0700c1030541c60301c002c54903040303008821021500390f07880c0100540c40320802d0459150483c032455404160b04810560050058402100001c0c08113108824480c600c070b4103802003940c0040c0d030020224000c0c0c3c0031050006072003240c41c0c0100c410303540d8000b18020b40556081c02c903030200079451818446a0001e04507114450310300d01005a210002079401c441d01000c0c6441e401038111280c2c41d20340a00a07030003049254810450b40c0b50854036515440c01c0c0b15207203034000c1d80100341c00085401c1009c841c01351080081001c1c2c0800e240000d00300301907021402c81c0c40388a00462034640300a20907641c0d6480050251450794007400700d4034105414162a03071880b403a0305 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 834054055 1250 834052805 834052819
    0x320090a06030b181e04140105100f061116080f060c161e0204060608010510030c020c040b040b0d08130b031603110705010905070f08060f130c030602040f05 69
    0x681648280102200f0b80c0c8041d011401c5150054240c40c0d02c43d0380208520f00920700001c9411148035000b000c0c51045d8060300d80d1540c8099200d0201703003542d40c00750400300d81c012004414400c94596015403c01c03640c01e4200300d1404100398086a007020102040c0b00400907040c0700000c3c01102c0400c85a950449400c103980140c0d45010800455006558110322409412000000020395801c0c83c0003400c188070444084407440c1358001b0b02620829080880003c1000b4010082070a048031b400e02c603603140b0f00341440405d94841000750355059400c0080d02ca5070304d4400440c0d10b030311698483d04000c500a0300c1560186614200300105034060f8101515109a03103400042907a40041645d00406845041d600c112030500000c030040c004591125210000800181d0001002442441d801a1180014004041c0b9140c0107001c00c41d1658005111504010200318410003008169036008002c46451f040e1b07030466040c60000090190402017500d44002030210390f4140f001c40f0700741200d808440413 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 834055305 1250 834054055 834054059
    0x1170a06060f0201051005240d0c1706030a0b06120304030b010501111b010f0504170705040e0a020904021201020c06190f1e110d0f0207051005070c120320090a 70
    0x3ca0885104884440c00c5455030a4103000070702e400c0401104806200c140d800b80200441c1e02d540580d13000c10324001c8260b507100c1e400024241c1000e60340660380241e002150309481c01c070000c241c8440705c1c250010589080500010301968a01c42e112903540784480442c3e4603203850745041007800400380036107800b01c1c504403500580007100050a00c5140100c1803004280900c040055a0600c082c00d501418400d085c00701107080c1c50000060510b00071a203000f4840c0a14040070300007217810b100080400b0740c0000c1590005602c0308a14207401c0360b4141e0b000003940b0304510b8560300902406941c0038050141500b801109452102d6044072002d002d0b4040003854050b4090008990307400e00060305200621001c00c003440c1c0258480450346d40004c80d41c524240c0080902021121a00100d001c810340c085210024448200300106802521031020000350a2550010340910700d5a81c1c02090940b8090022558a01c40d820a0340103400300001e9481c0b251354518208500c1d00301d440140e008038085000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 834056555 1250 834055305 834055307
    0x5030d09140114040f080313060c0c0c09021306050c0c040510170a11010e1f030c121401030b10030c121209060905010c02030a05100b130212060f01170a06060f 70
    0x180d0f5005a6100001c030b2a1281281d5810819420003041d4801416880c400c02011a0380da00401e410100d1030343c0c1e001403002d402c0c90f180030340e07960b1a000343d030140d481840307c0c1180c1d20512000e00b007a0ba4090500c262120149140f0342e04e04100c105405801c03a00702414031880e019440d04d1003045d1600c494800c1449800000f040d50fa900c509071010780b258901d4040d42d02154011014941c420b0006000c407917031a20345442518840000ca0314540c0080d40c0c2e03018201840340e201ca01c64031b1110140700b040c064056821401a008241030001074119104030300401e141c3c02145030311200440d0310a01c40039071030ba83c50400c01501420000c056520b800300254a1241c148115946016034075107482d200030840c00c0400444014036011002c0760144908200a00801d07400c01c0b0315002282070f40f02c08100d0000003024400c02a14400403184614018000284c0000034071903603c1d03010304241c40801c85002c00100403201500c00c803032088841d60075241400499407254003c601650000d0702e5107929030b100400 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 834057805 1250 834056555 834056591
    0x6060f021902040e030903340b0a0e060c0118021305090604080d140a062103140304060207080711010305060102070308120c0f0a120c1d040905030d091401 68
    0x8030140712900c54564940c0146000e41c0040510043c1d0001c6908000f42040480c0ca40801c2d02842c0800000e060003202540c00c800a5018a100c42502100101d900d002c420068a00a03401c01005100c1c05903e1400b0381e4a4250075169a07002c080002c1c0b112103000220380d069080d5000741a07000f09422200380740c0350119030203401c3c014208680101039030b542e1a140d11000c0d0700442d80107035007551610441c0c403401c681c51401d28000c1c2c40c3e2400c0095950b01e020000082a06114404c5e00c500c030b00011301038046900f106030070006611f882001981e81d070315890000c00034800c203000180301d0800800d030241842034001030814003c90a88003081380307481d481c00681e9190818480109100010004804160f400c0e0300101d801004480c9241d0511600c01c0040005c0d8002c60300c1d02000410021241111179001d00854002c88480d0404401d2031070088001c82400d044003140c14000c903214a04281004000c004890a00c003840b10300300b0003100350f4500400d404040e100c0d00d200070740c01c001c4000040300d8600 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 834059055 1250 834057805 834057823
    0x70605031302120c030a061d010e030f030717090604060510050a120c0302042a090b0d0905070504020429030f06090709181b0305010f1703041806060f02 67
    0x1003a841d210022903080103010901c6003054091806010030320002c1c1e480400010324554441d00011810140150250882d9151401810b903507a04068100ea0012004421561035400c41800b00c0e0341d035a950442039504994240940307a9a2000d9010000003040102d0a5405588500340511080d00c462510340c161800c2c45c0111036000d230f04c81c001042101c10201c940110031f4401c07028128070b2541d94000404a0703000c0c2030040c2c20400700220403246404003c080020000840c2003030b090050410000409601440820414003036890030410240300e4100002d20042c14002c01c150358403502d81071044c00303407043c145960348d0500c007074080520b45104040c00d0340d2046040350042c5180355609410840605070203040001030002202c404036900100c44003080c0c50704107a03400410081e03650803044a0942103010301c401010f07e0440144000002c1c3c0700c07044100c1e803a40300f1700900410180c0c2042e045100720b034490052288420348801d801103a60300b2240482e00e040e107a8a0004c96408802e03600d80c9860 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 834060305 1250 834059055 834059071
    0x3080d0e1612030314070201090b0915070813170409060905040b0604022d18030a030207051e0409060f0e030a080c0f040902070c080d0903030903060f110703030b0307060503 76
    0x10388010b001c0707880e0181820802e0b90080c81c0124103030711090b143c51420501035500e500140d4482941b030f400d2281942c005501b240304440100020300e403e9030413a01c5160301801030000c001c0d90f0b1012907400031144c1c0f100d81500c7d42200c01582c02c0a0302401c01c50080e071051084140c1c060921000003400f0250340b08452049400c0325000f203c40d564401000300130750224203030640301e4600c208401c0c0d40c400d803241c003c075014082c42800ca80d41c400f0301e1141143c0c60340011001c0c2c460f07400380340e450000913804034031078045801c2a80c5002468021241e00c0c800d01408100180c0c02920703101c0d40318203000c0144c10032059038000d440100160765487d0300b000d03243d10030702c03020201003880b0300b01141004c2c20b200010008441803001560400740ca030f4450031f040c3d030b10008054070381400c42d0304140b20b58242402540030b10750316800e085110b1884c40e03601905c00ea0700341c807002d401c041da82c1c1544800e021458200d02d04240c5950005c55030307a403a40c40e001c0d0081c1900003401d4007034851f205c0b01003403c81c011000c9130300034248 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 834061555 1250 834060305 834060343
    0x61410060513050d08041d0a06050406050f0906031c022103100b0c070e15030c03010522020301090821090d090e04021816020c031c0804110a03080d0e 66
    0x41200780a019070142900700c2d00140200000260310f216800070340556410b10211f50380d603007450084a0251005074200700e1080d40340541c1048650b60300ea1b0000c0f04101d09841043d0181d4810000a091038404040e10b800d0140c2c0100f04007812b6130115120340c40d920071030600387c240182c066151940b40021104601c0003046c980082c0045600c0f0b10140c4002c074000700072146090b4503000300720021b040540f03a6202d00600d904080d00186010302900090103401c0e0000c00451425641c07a01001e44031061071005400905031a505540302900710510413908000000e50705c0c0c800c00c0311800c0085d02001c100c0036400182020881300103002c5085016046260303115541e0a04008100b4a81c0c0c40240c0101d03801640c43d0070388070b0300d07840141d80d841c401e0b0ba03414002c04007a030714100040e05080305002d40130300c213420003002442003824030a0160b600c4009843d2960840d5228a07091140c03459410085910050303030b40b000410040d420005000061204406215800301440c130503942d031103001015111461 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 834062805 1250 834061555 834061559
    0x11010b010e01052b091505040c0501050903031306050306100e090403121d030c0709150b16080304060b120a0201140c010b0d050a0b0708090d050313061410060513 71
    0xc0303d00043d01242103c244a01410f103443c0701e000e8038500c0c550403840c80c85601c4140a8091020381c05260f4910315800c07400780010314240c3c0d98095907c1c107901a8038144400841d92480c40d0300e041056541e04043c0c014008406620303a240600340e0f8000300c0ea003a1140f0100e0702408a100d10956000d0030210000c0c10344483c035290781d601a58443d124001c403a02c99661a211090756000004000765244a40005150744503019246c090801c2155000f80c3c070783c542440310442c0303500c8038540ca15040312020240a0f4451030011055582c610800c4400f4240000100620041c40981d60001c6078411040300d00e102a070150301c0000f40ca6420b14040a07020442c1b081d0304030002e01c1101c0041c26041031000c00010b910020900103032020918010a898980c843e03c001c600300010407090f2030b00503a19091101052410302d909907624020380140d5010044003201080081c0000f4542d502241d5001e081402100850038440c208000308445001c084a492040022403501800485503c0203208a08180c214 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 834064055 1250 834062805 834062807
    0xa0b0405040b10050702220c1e090501020601030611070503031e0a06030305030a0e16060503151c24061409150a06210c05130503010b061c0f0e01090311010b010e01 72
    0x401403868150703a20307c42d0b43c0004524561182800262090321030b00c04001c000108100b070031943c0f50300320003071182a0071300b4440c036a00065542c1c11217500030004103200c80c4040c150364090042920003005448044144442c00d018841b20641240010700500603540c0c55418050a13190b140c8800f0b4080780f420000300d0846000354202c00e9824030321104465051000380020110500240c0c8136200084001c000c1c003000d4003800158229078002102d00c0b1641e08114502001104043d0000500202c44440380c8039051741c0f48002d003009500707050340030001c0503a01d5140d0501c54400c02009031080400200140544001e41a1003001e0080039040044031030601c90244c07034001c40103008190b88400b01d5611403140c403640c010b20b410316071213a41c0c0980f15851140d41038110403140e08514440d034102280300074640c889106803140e000c0240292950164052a0780000f00034844480328001c1c200b41c0356881e004015004080100d10960340c1c010015042003180c0d00f02c428401c00c03140000e180190b0b0312595 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 834065305 1250 834064055 834064069
    0x302030c1204020a0e2d070f0c0c0b030115020610240e060c0102040e070e10030b1c0305041401080906161103040e0403090b120105010f020304050a0b0405040b10050702 74
    0x2241c03004d03090400d00c40e152034148048072030846e424491503000010491070721105940c2d83c070b044141c00380040c021381040f02c00031300143e40c0144030b4020070449091003010f21103804212802003241d0520580d403540c680d81a0103610480d04d02d4180903109000118a240d11828074000488900c5d9261500426000281604150251107544200710504d248a106540e51000420182003201e0006954601d883c0c44a50f03089001014101400500d84100e40d140d140c201e0011035016007807a000420b950740d0000200300e400b01440e00d400d03074490030401008049d0081e00400035240b100810f55003003004038004450303a910860340759440350401404119010070620f00c00c00800058244001409414031059255410a80c000103000a82100340001e058104880700080e2010203569890b20904c01c1c6440c10025041c0314442c10815051a0b030050b0600c20b0040ea0060030005102c2801e04d03a89039010060780c0c00031700480d8412454401c6040051811082030704003066107880315070624000d90200205 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 834066555 1250 834065305 834065311
    0xe0f060d02070501060906030c081209190e07090911040f1205240a060b0903030a0f0e04060e090c040e060103080906090d0b090c030304050120030f040807090b010302030c12 76
    0x940340c1c080c0850350003c2c10a02525015140804002a41e81d03c0d50070301d22201c0d1174940c0b0000c0c4940084041004050060049800544043d03420a1000e0b81d03014480c41103020b2030b800b20000c4c0a00c0c106002c1450351000c030040444425a1090003a4401203a0090451003903201d40948286810740c1000440341e6084a0100300e80a0001d44a00e0068127610303103d5505800c4044042c410b002d0100f00908900d0701c01c0f04064441242ca070b50400341280046075403841501b48090500c00d055565108803803044126442e00c0700c028205001c103940da026051800902601c28591900811103040002e003014801d2841302c18080c1300034400381e40b0795101c072070660303200301c1c40300b41c0081c001c0024004944807004009461885005600003500d0142e078000c0c00c14182001843c07007900204820403643c1c0c0d00005d003a9404c040a0509002d040080b5040c51540c0304240d1616116000880c00094101d004241d56040714200350041c809c00380c0e4800118203e1204840c01070000105100c1c0800c28241c80e0b0141e54 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 834067805 1250 834066555 834066577
    0x816020c040e03040f03140601090b0a0e04020a081e2401030b0a090507030f02030c09191a030106030f050d082208090a030b0601120908090111031209031201060e0f06 73
    0x204d029160299040120550381066600c9080008600d0240300100700550040240980402c25180c502c00000c004040602c2240b20105030704010138150350300d28045000030404141154000b00d4840c2080000d00d1900084880c64012105440070f00741c41601003011600e0481c02101942c0e00710303030b10603082c00005840c6a40b03007550307000100000781c01000100040d40c0500710140d14004580704052a020321054510f000312010402d025480c022880b4141d07200f00002c20111b151481c5a000040000f011540107a00d07608040d400810310014000404038503000e482518a41a02c000003a50f5228064840000e0100840003100240701505c0320010550320905d6020b107404131013030000740340d07200c1c50b00b0999030710600e20144002c2e50b8000481c00305001c282d0708140600001e949900e00140110039400b4148049801d0981c440b120910480d8000b040c21120101241442c41d2500d950b40c22030a014980a0010300003c100c00d4010390603040c089000401d400f8113032010074140039103130704201b400007 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 834069055 1250 834067805 834067807
    0xa0b0d050915040804150318060b010c021e040506090f04031803150f0506010929090303160201080a09050a0f05032b0609020901093308070816020c040e03 68
    0x3800d00b400d007041803405030380642c48484e00c0b00d01340300c070041c00d13104d0710f0030301501713140c9040c002c10762010741c03141d191401603001800003442a40d5600141d0f03000b000070000a500c0704038000400e103544001c07404030f0f0b52807009940400c80e681e07404052000048d03041da05808042d41c05400100000c3c8929558010200c0f035103c810100355980c1d88140c002113006268070040368a444e0246000403444c881d06920180c00d10300303544880d00e0700803c6640c41c080c9445481d40644224803051106110400300d1b040400b0180880380d540700315055603202c22070755a5089002884600110350441000d001c0c0a030b01c0b03a0090702800300202159242d10031850f096000300c826000500c544420004000c060700c60030300941e80d4010151440940010840c0c0460300500c1003940306025a843c2031368000307881000c0e039203100000e034502d01c642c217032250002d4405c80e2000c1412040d8229080140d40c0031480c0e5000e03840941b0703004082d485000300d10344004020104000146d100d60f0310100316181680204c1c0c014900c807800c2e2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 834070305 1250 834069055 834069073
    0x151306050a020904020c010506240714010603120804112d0f06030717100308160602040f060504061106010501020606060a031404051e0d0203030c1810030e0c0a0b0d0509 74
    0x403401780c2e044000c17405070b030ba550b0301c003081070904061529640c0c94a007852628030341c0c41540c1070300c1c0d2103000c0c03800d018055848000841111410035482607010355040800c5014aa6005034014560070003250100c4180c50003d40d07080107400c0000342815014001c0060b0344525540144000030320101402c3c0396803220914082e91801e803102c200950007550f0303d030780341c088400d9034000102d00214090503641c1c06140910040000c145800103070760006105800d46207001c941d504050020303029a4100c8860300041001c001001c072703003010090085030010303241c0c1d44000c0803812505458000900c5000c0c0540c01800000e4071034540030f0001d1441c0c100a04000860046050014040c0e603011030f400c844136800700c4042e4254000c010303401c1140000c0d200041003da10302000081d1640009461207454900219074840da80e2040481d45c0110f0802800300c13003007480a00401001350030f0f4546a842d03580103144070405a4101441600195004043d069180c550103000c0d50300108002022035107907000e11f94403 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 834071555 1250 834070305 834070309
    0x131107140d020c0d0b04030309050a06060b030610212c0109060e030301030f03081e0f061c030507170c10090605010501031a01030903020705030f0f151306050a0209 72
    0x1100010900180061280700190040a07191000d15a6035a100381440440b030000520b0780001154026032503c0c000c61080301c9454554500160f24500170041030410070003051442030003024504c54281100c440c00e4203102180140c0d00105a8250940d207100c10f1807400c950b03516240c000c51840366549104594000c0c1d004842c01001405a9000f419651a84900428800700380200c03400c80c0128000307540355502d141c0d00c1080c00801c1c0240201402207d400141d900c640c208000b449849148001c600c9525208440e0800380e00d003142e201e0b01c110030b07050b011000001c085640708000d0f0340c580c5807039150844680b80c100080e00110101c24000c04104122030600c0e00511841e5103001c0711010104c1d00e940985400700c2a22016003060b03041518007038141d200100042c0800c074105c4030030700f00010010228107013242000d08a0300f000d501882000c0c290341800744001040c03242240c06009652050030403400c1440f010805a9401c4102c2c66680c020402040e200d40c4955007107220b1000042c504400c105c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 834072805 1250 834071555 834071573
    0x15150303040b091008220f200a0603112505121809220501060905010b0d0f1505010f1b08210402090c0c07050603160914131107 56
    0x21449903003001145400c841c0c00c003400c0c0c140e1100e40340c5c100801185031151108040c10201204045106008000703d0240582d009070340e0031040e00141002902500004200000d020311a071240c040c0c01e0120001841503c281702d90050a02c8401e00580303080c116903481d000c0c11111070501c2d4890550800500001030302040341c810880e030207690301a143c000107143d07400c0e16820403d61a004c2ca2540040018420421000200d402c15000751251000c03c50f003441c81c010f00c11600b02010ba18500400420741c4040130000e0080c1c85131510007440310021804184c01a80d000d9a176840140d105104107200540c00b400070040141b001e840d0445854515000d254110b803903041041e100440d0003d1000001c034a600d4408001c08802c8800700741500380383d4003003403060b800103107210030021000c07034010416081848803400400380149125220305090f00000850312819003880013046000c1c400040c07210030490300c0c40c14000b00912010400000801240c0604038903144110000340c00c00026001583c849 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 834074055 1250 834072805 834072809
    0x1050d05040605011707051035011503090209041211010c08270705010e0f0603010b030925121e0302070608011a030c0c0a050d0e0114070201021515030304 68
    0x90b000314a5500d0715882e40e10408114850540b05c0d0082c1105000c5901c03100c840e2500502907240001c8200c0103880032913040c08100000c1d001400c08065071103804050498036a069881050200c2100c05000030160104c8a203050025000303c4182d000402282034043c81c003101500c1d506161888010940d034050841e002242c4500202d1210000d200030500308191403008007040d400c01c01220300140c0740403540c41c10b90f4482d89040106a42190790582c69544484e100e009029003880c2d10703940c50780c24440580d00110780c40c1032070b84508151110203101d07002d060140b41e030342c04440d9040d00341000194410801d0240342030b50107818070000c40d03a021012032301580e40b2a019a000e4400a410504010702440d010384c08103030050b901031380b40400c900ca4101280d070000d1800c510183da0307095079008207050540680740502580103000c41603107a283c10a4006460035400d0742c40410840022016031200c1c0a01c000207401640096240b034071940170b000c84542c114841e10200f009000010000a207554825 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 834075305 1250 834074055 834074063
    0x70c0f0606060212030906130c0503101a060a0813291e2205120f130b031e04170c07030606081b09040813030f030f03090b06010c0201050d0504 63
    0x4420401c41554184139660082880311906859800d0801074144d8413030001d4803002d0206c0e41101003030200711164100c0720081c00050150f6000151105100b0010100c1164030348a940300003440d480c40d85020800c80ba05001282c0380d4020545032003180f42606002c03400100d495450f403000302083c500c5a409015540448004016080d1030803c0c0400b640c0314415808500c0c00c4210000c2c07051002c030340300280500c0300e130041998403510000c0c1003c51405003000300000540f4000511045075103081001440000092a00031000580c0d80702414103030310085500d891076403500c0b4400000000c0480c0d203207030000d01540c4030301c0305d400085486000507846044102c6281d07100100400420a4901448008105000c00740640b45420f0810005038414080e01600c10180c150010302000071607020390b5650080b5140081e031864491070155100f9142d640203a01083c0b00c0d00d800351861f4400d000b0894069403042e11840c0075103d2a0056801d02d2039400c00b00d0500100340a401a140c803a4441c842c45076020b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 834076555 1250 834075305 834075311
    0x1005031207050f0d090b13031a04022d1519020d120504020d020d1a1306051f0b0d1d0d0801050a0308040612022106090a0213030803070c0f06 62
    0x1482c1c21443c0089800341e042181c3c01c0100c0e025038080e000391031081101c1c0e0139112960340300d54a81518100030410740000f030100b260381440111405400a055104a1080e221000f51102e9415450b281d4140b100c200b2400202180769105142081c1d40d0b081118005c41401700c3c01e000e400b100c0c0008070025000c1220060740510027024a0541c1f10000042d55055008104001d08203900810b241f043c034064084c0c06440c1841c126004c0050100c034140d26041c0c419001d45403801c05241101e0404480202910154140b0001c120070503400c01c60b400718022280030f07807001d9a00c1c0c04100b03e910380000c61901c012503900d09074042c11101600124240a0780d9402a203100724a500005d0509107040e00498014400fa80c0c0900000307007407004403422b48501c0d0612011811041c1c04400280c071941046c1d080c040d40485070204c0888580100e036009400407904a440d0356075400001040740140c003003040d00c01ca5418001c00c0805d071003d00454009005150080e0382c80d1803500ca103501c1e142050001c23100315503 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 834077805 1250 834076555 834076567
    0xa050607061e02040308030a0b010908241005060a0e040204050618031b060a08060a030f0b09210d050915010b0c0706030207020d1e060e030912030702030a030810050312 74
    0x424802c03440c00700c10301200c00718145410740d252601c1501008122004c032075900c4402c501c0aa0046d150440103103442c004a41c82825450710300035103085110341c506210b10305440420a5080031a03144010f442000e00010300b0070030450801c071001c0d010300035500e8000c0c0e400c010124550300c1e00d00007010264900ca003003e00402213001413501d0910414070318000e2800f030800346115903031072100311080a0394500c0d1001c1c40b0744a12001078050741c81588000c0040c080ca414840410103110600c85c410241d1400391103100301c07101019206545202d030052080c040070050410200c140760700ca5904a00340204881c605045030f00030315400e001c02c0c0c0200510000104550f200c041017080716101524a5203810340c100310360340d0701262928603c000d0062242032010602410502050400c0000580240301440b9103180310140b140c0300c0c0d000407141802041c4180e00184610301c00411241c44540c040c00400220b2090788003101c0e0b0040260283c1150040c0c0c80001030a036800308101d14850f2850244a0780e900 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 834079055 1250 834077805 834077831
    0xe160e190b13170303012610060312110708060711011524020a0f060207060212180c0108091e070b040807151b02060d0e060a05011a1c0b0a05060706 65
    0x1020240081e50307164130400062242690708104114104c003a0304401c0e800d43e50742c00d0701c00e00740801d01602c0364001e45406000401e101da1500c00360741c0f420042d11003581a0340c0030448113480308018042c1036556404080400c0190b481520001300e00c01c034000000405401180d0f401c01850559804460080000282c440e0314000429076401840858002000c12182c103544900001010310f41c0030301000d5020481c5000e2210350340450300da0720503c0014500c00c1c54954210310303080044010001080c810060680c1c40d950103010050b014680e080000e22924036503010300e407843c0f040458007400342d00410b000010380c904080d000d400503040034006410043c0c10f140104190003c02020201000070958048101640d043c001c4e00402d9015100e01381c0ea04040d0000c4000740414841000d201c1c41140c0821508036031a602c001c0c161810070008111a45400c11840d002d4080c062a48805201110010442c0300d000e600000c540d0701c0281c90a00c1a9a4420010701a60131912040d5070603a03c4143d05100e00c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 834080305 1250 834079055 834079079
    0x618091509032b0e030313060b060a270e0a090516030206092b0f050606151801020705130c0311042106020405030f070e160e190b13 58
    0x1c55900c1008504101508154000000c005803040c40c000382d000001550f41c448580180e01c490b04000708680d56400c0440415a03444030b42c100c165445031415007412818504030080740d4528643c1da0301d001a003155a002d81202c7d5540c0c520b0a1010004007100080700891204200d100349020a80041c0c004400e091150030413006482111070700101000510040c1d4644007642d0100c4401c1e00e0002c0d401b58050b80c40b1090303800c04803400d81203c00700d064410411108140441643e8070901c103403200307501c46105203c0c0301c615078810340d600343c10705001074281c0c183c24a64070b150070b00d41481202c5085907100085922500344185149045884040e012225030b01401411503070000c542c4018074141c5044e807001c042030300301c818401001c0d460004d803030207001450f0180ca002d084018182c07003452a0494940e6610280d03031041000c5a04000000303111083e1790070902c4202c1101d134460740303540881c0303000b04905007040a250480d5480d80802c0461500f0b20b58021340154004007040585503400c0095111365 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 834081555 1250 834080305 834080311
    0x918170c010e0601061b1104060b0a180e0f15040c080103031808030a050d060306020a090f0f0323010f0e0c030c1210020c120d0501030c050d0506040b06180915 70
    0x560303071010004100c02c0f07501024424021503070b1004c2080e41c00d150700d02480184403070301c20075920a003002000320f2b150840c9002481c10040039190451000000420309140400324421070124500703400000320701e45004080030f0340c0110340c58901542982440001000c8903540c00c2900d000821000050007007680200c0c545008240b010209621140f501004603641c3c49075118000c00c1010120302880e4115440d048680510b070b12000654aa82c4a42e900a01c4943c1a1003403143c89162420001280440044c4640c1a00d40240b490311088500c0241606c9024051078032180540d03071900c0f600542c0c03000c2d10410031145102c00c00b40c5004103000e820145000c590400e02c920841030349440c008242c2e0001180600031428800240e01c0751030706000c60f41088032007644450b440000142c0c40010354110380c00b1034181c81c860306880303c1301ca0315503091291031803000d1001044d036804600030902003a4000182607000e1001000001920700c40b00b031040d184807058074000c0c000e40c0302050740e00c1904041418198 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 834082805 1250 834081555 834081581
    0xf12080a0b09040b0402120703050604080d06050a03120c03050f2101052704031701090f0f23060411040b0c0c04020a0f111c020a030e01090f0918170c01 67
    0x1940f420aa1101031030400041c000034404c4400d00941c08010100303111400065030003800b070384e205140c01d042920345a40040c40410030586082004601c40c9000542001a65040b51184601844051080d030305081c0c818003d405010041c04800d00c8052020000c103003a400009400e108848414114907640b281038001c24403c07084003400f41e981c04080f0554607101c4200000d68030168440b4181554543d030622045403240851400100d610f400e40d400041c0503080b0820108002000d41540d14201c92064030300c001d501c0040c400d9000054001c4501d280c200000400004001070103000b0440e03160710a038000d02c0d4000012500c40c014103000d000e11107401e0300c191810740c81c1800c2050000e0441201001c0842803050780d041c0742481880c1007140c070580001c01c0c03140c00c2e88101c250001070740d030700b03e1500100c0000e404508188a154403428510084030005000b00384102d00b40019200a004614030a0506034500302d6240d002c510078050050710441103004246e41c0e6500d4030111400e48040100d01c1c4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 834084055 1250 834082805 834082819
    0x90501050601052d070b0c04081c050a0809100e160f0b031611070e0412020109030801051c050118020a090b030a08071b030c090f0b09040f0f12080a0b 66
    0x2d103440e40340440301c02e00d140140e1102c50f241c1134412131449650050540152407400003504001551003040020000d82c2c403030310700325100d5080c0300020146035036103903281c0d8000850902013800e05d08d005140c21074002c2003800546840450140100f001c8594402600d20654042031310f022016400d060407001030b0140d0300c01c400b102d034200800d0307009c18807015001e046d0309603400840512151140000740080c0707100c2d030700765083c141d034a0100d20300c500003d440c1699400520f03140444c02038014425088059855202c810841e881c080400c0406990704000c00b04120040070a4000508288030b9540805c2c403c08011684580e240180400c103545500003120451412500c2178050303030005851000580c1c040d10035540d0755618500021185d034013031244900080d80d480007000700210555040284d42d07441101300450f0100c10758100a40c1d1101205039006500c0102107804039007003454400e440c1d8040c03615070b0100c610039076038240c81074000406140003609000500110810a0250104030301085400d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 834085305 1250 834084055 834084067
    0x706030e0c0a05010f1715010e090423030c0102040e010e1605030604020307051b0c0f0102190213110d02040312031b030b030712110f090412050d06120609050105060105 74
    0x803074200d082c030740240b07818421069a452405d40c07040d0ba0840d10451301c101d41610504007054036040140c085501c00d4045403002455184608195219500c541d4200071a504d09405260b8140c0003c64146002040380c00100618186082d0900040c801030612032990001c9615100302820800d5000d4481010b00c40f0a410607d00340f90702c2010390703400481c102c900598a032903018003136800c0d21424043d01368104450109403034000011070300140d07000041d42c6044102c10f0107001240c41d048a98000820000885090f101504005050383c02c03940e0070704400a00011111205e00f199003045001d0421a600003c06100704205c940c1c02803505c1100e03003801d210300c18000c4002212440701c418a031040595076510b110042e0780070001c0c0703401044962130100901c48542440322800780510742c00ca000d16600d100740702e51070401d002c0c074900c101d0300803500084440ca4000c0444080c1d20686001d4906a12804081010303ca03100340f035400103100300f0002510a0361403902c03070b007940d400400300380c188401488a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 834086555 1250 834085305 834085309
    0x150a1503080403060f150602250506070303050a0b04181a100605161212050c090123041e05090f09030904021308072606010302150702210706030e0c 65
    0x549007504d43c040760100380d06991401c80c0004280c08466000b0300348403607030300048007500881c1d541c1075650303007400e0b075600c00c00341185a5000d0740c018070415401a204200803400b0038860380c401c83c2c00040c00c0c20040780f04810040090306070f85a043c1080341034030025603e14108210325516010720005204140640c6c035041100e0b081584003885090248075001030300000c1d191440c1003007824968022140740025071605401002caa401a55048103d440c1c000422802d11408042e5005828142d407200702c0d140d00c1c0250400391003072107110056681d0b014007020a05081d504071400842d0303200d021134426a17181c01d04021181601500407114000041d0070b20469a00c0401120b1940c0301c196070141c1d070740a2003170764035040d07219641c020a12070050500102c0d228001500102810350101205150030b8043c070140c584030102071100a40c00b103400b09200402100030b001404c1c4080c0000c1020a4002d2011500c2d001004501500582c0d50090a8144030464151283c010100c2c0240020209500c002c40 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 834087805 1250 834086555 834086557
    0x60e0406090e0f0d1128020d0c1a040e01120309031502211006050a1205091b0111071a0409020a020a0201020d09030b010e0a11072f06070b0a0b03150a150308 69
    0x12040a2012409800124003446c41c2905014958003a12000050b2694200b01010701814001c0400c00c044d010039205082584d101501c060760015028180542d00c1c000342485a00c0b05040c040b01030202e4854000b01140104d200c034200c01e0400c500c00b50f5100300941c1404401e0400184560b19007208009101c07203186c5490360a41912603504001c2d40c0c880d0280340035101d00200c004513180709401c10b010840354000110b00117091000607201d811220030307841c0054802c100f10f125001056032058208001c50303032a072011415408007010801e4903240c1c84401440907a800398203103101603405200b0190071942d040040d1220f03031844e0729100c100c45003940d0b1b40c4022040c061203588a1680818085001c0200aa20494000c41c801030320994400b2186070603402419072480700c150100f9810b50101c44002c425114141c07100c1d0052200d4070b4885959100d000d07510000e400d03100d80590303506501e280740e10b08009060301e000c03054240315020b191041c1880183c4d201625011051448500c0400c00aa8184 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 834089055 1250 834087805 834087823
    0x3030f05090a02120f0d0e030708030406210f06060f2a060b0a050a030b0907080303100b0715050106050717040506030c0c1c05180301090c060e0406090e0f0d11 70
    0x490a0703404400313000c0d6291810700200035603042170190240c1d094840780c200c030150740c00038000d6003030342d01e481c0d910b0a40903100c0c01588103103000b01e400c5100850b848103400020404003500000300184004c5c52211403002c803030140c0c00c103201141708102c96540030fa0304104141c02d814a4201100260248034102414011520000070507407a00c3e144000041d54413105140082d203c050640c5400c20355906004040c41810340d6175443d940138054002c101e0b07850110072030b4401c070404e40d20040390a1900d0006e620a900540094a0a080c96150082e00e90610700a59008004075990304da06c4000ca030030201c86201c003191400351036840c00c01041005403140001c0d02c0d8000c0e500e20507103403107544000503182451051280160000100c0c611031140e99003100c05815141c841c03441413451703008131109041c01c0711030241c400341000c03003040070170003216100701200396142c1c40181001c19000d80d41d41c64402914440140d581c0b483d0806042d4511109080000d840c000c81c080c0342040d50180c902c40019210603040d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 834090305 1250 834089055 834089059
    0xf0b0c0d0b0f031f0209090c0a1205040507050f030a06060803180604180509030408030c0114060306090703240207050a210921140c0406140102070b0307021f0903030f05090a02 77
    0x31031803043e00c81c4c1d0640d0549a003054040c115680c24a0326140502d22503104410980205100051046100e4400c0c424a80300381d0b808001010400e0030301003046a07401001d1070b07907036041c403880c082e12001986900a070001800307100010364480448032080118080c018100038005c1c44188010070000702900460034401340c01840c00181070b07e03203e264034154031481d00642c906100000c2c10401c82d03001503010b011030789654010341900782c6982d0304050712400151440805031348451030620210310740c144912602001d61000341d001a41c1114080281e8008c008143caa03030304109440c1040c05400040140c1d8500640c103d004100e0941c400500007d172303240165110a0103170310a00045039207604a08803110342020f880c8083d00d1100a2580c0d640b41031804040c003072400d00300001002c1e0408480c8500d1100305030081c122460a01c4060b0b0082d8100034010000c611030b50b00c0e50744811940b4030100d40f035003c03214804101000c0c036040203015540602e1080c081d170380c42d00781041642c1401140b510107403a41 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 834091555 1250 834090305 834090343
    0x50a140310030b040b04020901120201050a322703100209041806290f011101090b01081c021f020703030b1216080c0a120f0b0c0d0b0f03 60
    0x144101c0e10039040a1904000c1011403601c0900c0b060004110b022803040784216640412a03072242c100b280c21000c40040207010480c244100b050f2030707000b0201c02d00c001102069004060400300e5004451010300361102c0407001000030a50404001a0303c040700744000b13040f480c10111200b0000c07035078903000444d01d1000680d003c9103090f115541c2c1c3d0420080d06801c50f0043d040304401d81003030302c001d0038950b01c8070011410320181c4410522103503a0b4406128002801c80311b80d5030000005564103480405042410b550702d03040c04c000501d405050724040c00c0d02400508a24118101042d070101c1e842d010501591301c00c00400100d2503800204040d01460b9005c0562603503201d00d400d50103018142142c03548011000e9501c002c0510000340e501c2c440c81840d42c850f40300c540e0758201c0c0340ca582c941d408a503080b1141400a0089003161905102254400c012481ca1406c10b03483c5c0d801800401c0e10110101c50000030031014141050080450303150044403130600c1900d161000a0b83d9000c0f00000c44000c0038 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 834092805 1250 834091555 834091561
    0xe13051b0f0c030d0203070f09060207061409090f040b0106020c150a02030d0504060c0e0409080403080a11031314060309060a0506060403050f0102040618080304050904080702040e07080d050a1403 86
    0x8071101901c00c110002001ca036150038040c40801c4c06500211020310000c0d4a02d80030318071081c8902080d100700d4400e07030003419500c0d0a0000460700b80f00c1000d00300041050400c2541e940d80c84900343c0078401e004e40328020025003051300e0030b0012a0302c1a4400c204640c4100e0441403071b5555020790b80301c06101500450303a20260050b09900318010440c140b071945180100704802c0c0401a000007981000301c1e520314840c001c8090400c02211170f1b01e140600031800c1404140005150a4001d00707203442c040c2440c0b1200e54a0002041c0740d0361041580040e000032004e400c02500c0780308580381d07032070a00495006041d4a410000d85d0741c1c8940c0100440304107900d80c40030a0850311980d0840340555084410354a000300c002c41c6903400307503101d840303000700140304800c0b2a40c9005d51169041c8c01d80d54180003440c5420f113046c041001420700500192101d8000b00200f400607a2181b00c1c415000d0600c401510905141061280c201822a01c1c0c07c02404070030407045d0380b0380d0f9101912200004c104d20900307850751 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 834094055 1250 834092805 834092827
    0x2030a0f030605040e070905010b1602040209010509091302090604020307020a030f030b0a0e100b07020d030f02071d0411123c10050705340804060e13051b 68
    0x10181c0c0f14035041460b00d5060201d148011807070f075040c2c3e60185410701c60741c1da176114020010310461108441846900704901c00600c0c203500141400d030300c1450180e003002c1500d40014030089054403482821400003206004504001817002c3e80308400b00d404500754680500080e4840710114801000c11100c0b800046030300c0e003e81e100d015020b00140082e84281e8607083c1c0520a92000d0f0b030386404005213400e00080d00c003621001c0f1400694090450000800955030660b06100ca00181c00150300856502203800241d5a5120700304c01c0e48200c00003240d007400c1c10185a0010040b0403540107403c4903000e941f0607039000500c0c00600c40480704a07800c0200007a8140440c030704001c0c440303410010610445021890024441100314078840c0108003580340d981e010745d868803c540c08400c2c03082c0f016a1409510100f0b40d0582c2c2110111000d0901801c03c56481c1e8085500903048080032902c00d100581850404443c544148040e175401042682014944030030310f052445c58000c1c2d0b1500004000641c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 834095305 1250 834094055 834094061
    0x60906050706150b1308011b080a110703051c05060618030f01140402210d14091003200f090f1f0305060111010533060c0a0303110a02030a0f03 63
    0x5410b8a07483c081c043e075103601e15440143d0001d42d618440c040b000001180c140300c1031068400c5d501c0340c075814000341d90240e4425240590f009129400301666092a01c00750010303040200f01c06031003652455503a0850f912152495400151540341c91881c0c1020040da540b42e0030100e402010305010028403050301000000c1c54441014000550b650030080c00c51100e50b8038061850060f8030031124080c80c2c0449034404c00c2e1a000124045589921840020b20310074040d06540ca03200184410007450408400045440e07030740090030781d20020750303981000c3d1592803d94010700020300044031840c2c030f48100610a10014054040c1d000c0c4915003810404019a03155040103142a0b5403041c241080e0400500107002444202c96881c0828101600e1300380c00c03107041c4141c0303124100080444411101003442440041400d6400c00d881d80a0b40100c0c440030f5136284007412005540c2070042044200701d1a00805590844002c040669801c1c0301c102000c075008004d40301a0501840d19400c0030045800071009 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 834096555 1250 834095305 834095321
    0x20d0e07031b12120507020d1a0a060807080a06020d060e0c09030114070c0308150a030b01050423041101090902181203180d08040e01080f01110301060906050706 71
    0x10311940900000300001c0c42c0c41606210400c2c000b11080d142d40340715483d900b80d00b14100a000280401011401c6130140c000707080d0f0940058a24410401c0360380d6560303061084c10202c070781c41d01c908000300814211203008010150006d103001d812400c3c6446400b5030b8400c1d80140050805070045401d00144000d0360102000300f2040134842c601d81805241c2000690210003928040d500b05505100708010f2914068001c2106699034415143c2948040b5040d0901034010b40d4092403140c120000d907961482c0c86006035010310410402c80d4907203003c100803903011011404c61821000001803618000018103580107422842c030090a100201c01242d0507039042c1c1008500910104440d1101c0910b17014040900d002520a49400c082d4203032800da980c09420014070b415250b1940e800c21f903080c454841040341d440307103a0080c1000d4442c441d1640080f002d820140450b03100c540c0400c1e9102c400d014060b04800e040c440940b86504108000380340811342d001d59000d20000003040d4003041803d0f800002 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 834097805 1250 834096555 834096581
    0x2010b010903150b09010f360509010603051c030e0706021203070c08040b1918090905010b130c020d0c11091e0411240702040b061e0901030507020d0c0303020d 70
    0x4006e60b101d41500c4003030308880c05260000048113480310042c00c1c2c04684841280c041c990018100400c5601100c0038050040c0000316035500c40c600080016403c201070141c1100600002e40c4070703181c030700f001400c0b5107540460714840e62100c5010407100390041000d2900200307019940e40d0703980d80c418080d21500070070140100010720020b800100f07080f0041c09840b00001d9110104d0840400441c1103500d98443c86541201d01540d080404c0711aa0580c0042c42592140001150020b191000107204190400341c1000103602c42d10040000da5040c01244900826402c2030221200d141d01d9100c12940d00500582c040ca4907a0082803400005900704101d103800001103012501d454a8110400011400c3c101e00801c0b0200f0aa208450080c005008030000a008541000d1980c0c0230803015080d11484503810490402500c1400714a1030740300ca1201e88043e01082c3e4403100b1380300040c12190000c0004046401c200d5003d103200c1c2d88111814a41a09450007503240d81c3d240303601d000282500c8450b90 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 834099055 1250 834097805 834097819
    0x2071209290a0509220c12050405070905150901030c1401020f030a0f050705030307030b030606121b0604080d0c0b0609070c03140f0a0908011506080415060e0a020c07050102010b010903150b 83
    0x401e1250b90307007115580c0c00482c0d40741f517080c051940060045d16001e450040c100e42120720305000040c81580600d80c0802c24019140780c2411440120b02c2a14081c2c20a5455074a115402d0108107150346000a04403001c1c401410300c60001040903840c2d00810b00003d0812040b141400422445101591800c40d0000c090740c0e0f0300d040910f0050028000314203014024002d500006480b4909048540b00010342403024107000f0082c40a00d401e26413028806613070045080c000807810300740070040396000308010749500c88400c1039410303c0940d001d0003e080f548150304150030000315660004a69440651608201b01054607910070000075008000203811003420204108402030350100c0b0450407104c01100030006da6410460102440d9280d014240100c7c1660000c0b41c001254101c4811400c1101c18000401c1070316401c8107400117406480400905401051a48107044144000300040a0900013001620210b500280080341507100290202504c003408d4030116083d44c01c20058208002c0c028 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 834100305 1250 834099055 834099109
    0xf03070201231003060b04020c071e05060304020d02060306120123010e071e0302210a051006020705010f030b03060f070212031009090602071209290a0509 68
    0x81c0240700c01210000c40390300b06198090700948031a05203000300401c02c01d40124604513180c4c0030241c070b443c0b400d01c0e0b0056400c01034158000d030140038a038094007410303003150200b0b010000c4e91120f200580d003000344104800c1084c040169a00c00c542400e02da41500c550380c5950302d01000035030320080c01c200c07000b05500300104035000c501d0000c5c0c808103168990343d2102d4280d0f202d8074000c800b07044c00c50320040400c602990200a010900c15119881000b600d005458200c180545110b11403000f49106818140e40c010700081c00c0c3c507401890b500511251400c54403c1c5808002503942105100f000d06200512100c070000314425005044000c0014040321801d0400b11b94215842d00100d90b0703280103015800d0100800c1c00440100c0c0d0048000503c81c1c0d40391030404030120300802140400b01c42e011b50030010103001400080c0000c41d40d000f552605c03a460351400030f0000d0450350301c82046650583c0c1806c90081109040e01ba901c14003000e02c0c0c216180c450100109d000c1c0130715a002d0000d12404060a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 834101555 1250 834100305 834100307
    0x10c0212010507020d080402030a060b0a0b0408060a11090f01120603020d0f02040c05040e060f0112050f01061b171b030f0c010f0606020d180b0a050d06081f110f0307 73
    0x1083c050880d582c03c4901583c1d0030314040b5848442960000d6040d0403094a04010600c0c40e003110b000000c00600c0c98403803036a6100c0d07400c0c00c1c2d44154080c0312039070401e0b41040b0100005101c0c1c900800a10220286007040703001c001440c15500c4804035050003080d00d80030013540d0350b580c0140059680034099103500e04443c103210700307942602c130400c84c401c80c1440300341d2081c0d520403005c1d1021a000d8046210885e2102402c1107400348100c0c3e1282d0400c00004644414203109001c0c3d1401101202c60701e507030650600034020a040c2d8480d80054100342485d854000043e01c10070020b242d290a51401610750344108040550303001800c03500c0c0e0381403102283c100301c2c8102d180020815440004020005a1030030041c280c191a4a81320310000350300300780c084151283c0902c0401d54900004510540001c1e1101c51040c0d96800c40b0300b8280005070702240710162004503100710700241034103000901c20188136507480ca410319554004150b0844d103070020020301c0c1c0804410340d010a0389100a0a840c0d14000c08 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 834102805 1250 834101555 834101561
    0x6160e182404020a0e090105042c0307121d0613170717030a180e0a02090103060f12150509030702010f09030804030b0604050f07020d11120301090c08101d0402010c021201 75
    0x505c9110b076503100000246d070700c1c1c14892000c0c2c80043d80703902c00c101049600e4541d0231203040c0c0242407950004005000000f103a00480304603404031600ca11407240540380c919042d1a0403040058001c1c00c080240c1901e90a011112000301d0708100980c810150501442604110882d800340407a808481c0e60051a940c01002a02c2c58220958600210391312540174a607803580c080c401e4001e841c1c90b09001c1810b1420640003049001c070103060119200b80d841c20403040e090380e00e51041e801c6c41d05204c088400c0200c0360404408000e41c1c0340047c403413401c10703e40058480c418480d00a0500010240411010780100491030013540c102c61301c2c036110b44d560b0900a500e0394044500310b104520300400a000c04000203801405102d040e401040c0b4a80c01e114252a03200b2003d43c684d1803480b40c004404060401c0400650182990703001c08642907201040180182c2c90151842d00713200c42d10300c800e100101118174100b000a142d031040301129262400181d0380d2001144001c0c1d0007484440c0c00c0306d40560150 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 834104055 1250 834102805 834102827
    0x81602031b01021b03090a050f0f13060617010515030711160f05011110020c070806190e1c051308061003031409010806130e06160e182404020a 63
    0x8154036a5a141074413143c903881030204081c0d018801820030f1005041c4041c9810a000001e03103481e070140d024200207050000140c26101c040760720b4130350a0012a40c000701c40c450541b5030f080d0303030740346541804005040d154420030100080d00010000940e003511070380d40307a89602140d0703040e650140203880c101607a170500b5006d0030000e00041e603000625544107010904650b10214064140d541c0d241a014010354856046420b0700e100f03400000c28450002d00ca45405246008018028008680d90324003d98001d500084455001002240d04010040300307262210b09007450501e6031641782c0e240c0c2c40762280c8103401900b030f607105081c00c1120798121500020700350ba0082d01c03462841c0e50754082c818102d202340780c0d40a00040081c40441e80600703001c600600a0150b01501207020707080107821a240280c01c40b91025483c4902e20340716850b541040c4046042c00c0c06035004440c082c83c030144401c0034a0050600405806441080050768035a144a42e060040090065554810510300188032741501 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 834105305 1250 834104055 834104077
    0x7080406020124061d041b02010b04050604050624041223030a020712050a02030d080a05070306030308070507050c0619272912040b09060403081602031b0102 69
    0x6079080c040740341c0303440000f0103c541e5941c804000090008084020803081e074003441d0000c1c2c40300100d1484450744610002e0b45134031540000340903202c0e01c0400040e560040d0515003d81c1c60a400c0c448181c0790309490800b2000380071494442400c0510300c81242c0c1c40386602c000c4951500d0141d000400c41601300703800c1400c40508000b0940007a41e4403a607220301c2100c1c2c2c3c00016a2101404100840d80c00e41443c41280c001ca003a00e0b150300722038000ca4105150000d2920004600c00200a00080244101500b0041902d0104500d504540d0081c04c4201c000d0149000e110b0007150342030800c1400c00140c3d116080c09003802c0d48855015800c01141c400d4100343e10042512041c2504030142203505804820b09002171540c04a0726040d201d0860884c4000d07803104000c12a141c02d40400044401008412a00b2a440134945403600b410010148081c0461909400081c14040402d0b840000315070080300c40c1c00c040091103c500400c3e07107140300d118180350381c03922602d410300919003065001d0b007002142c0d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 834106555 1250 834105305 834105341
    0x70206030c0c010b0a140f03010207120203090307090c08040b22050f010b01021903180e150f06070f15020d051806060909070b0a05090d06150617060d0503070804060201 74
    0x451304100007160755004901030802621034201081c500b00c1107001480310003400041ca01061a260f03400c01a403e4a502d001507800002c840116080802642d402005650070800031000c3c55107008282010250015051501150200e240c0e003920048424090611000700003415066180503602d485400030081215440c01c483c402c1ea650010803104e0459400142000d4011415541902c600e2110031104009010388c510104030700000102680c0101110243c035418940c2500410001c4000b442107a13000320410f002c41000180e410215000c91580f1010845015074440340c5400203010310420700300030718100170602104001c5107110049031020300050352050768510081c402c40030350580c0c03070b61a540d004103010403404030498082c10306d00c0c40b9450f00d03918140c40400052894000810140c5a0582d2581c070121030703040403c03407000240042e0500860206c3c0d140d000322085003006010f07500035840150020f042040c2801142c003a00c0d80300081c95100e42d26800003e0007408480404014041 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 834107805 1250 834106555 834106571
    0xf14070f090902070305041715130605070e090a0f020d110d0e011112090109080a0305090705120c1c020904080406080601021c0c02130f0b040617061605070206030c0c01 74
    0xb2070084448440c0c0544556103030500d072a415600941104984401e240500e0009071403162404040b5405080e196503100c401d9045030604601716400501404144900c21440b031110f52030345049654810140500014255003880c02c46c0c004c0e2080700e010650180c900301c00400e558040001920030102c0c804d00402c841c1401a21103800c94039001d000c1184d10300180b10080c403e01d00c0080c46a4002c47e406c0c000b18064807142c0d1088a02d400810b00400401d0703c500030030007454000c1060a0040504480c0c040410340d042440a885465140040c1e00540c04222245070142400981018150f07000e0030100203481d190424140c0e6400600a030800113401501081081d0710001d000242241d0803000d01d140c3c03a007110000e80d856244210f0482c2c00a880c4103400741c1501c028401d030b0704140c80a41e0089500070b000801c003c04c5a40c140c008030a41c2c00164104951031130700083c40b551000500030601454012840103031107601807144025400800002081130040a0b4005440f82c280303040020302c0012 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 834109055 1250 834107805 834107819
    0xc0106090b040b0f0d0c081c030f1a061810180902090f040903120f0501061818050705070507060512060f151c0222060c03120f14070f09 60
    0xc0c08000c003155002400c2c411640c11407824201402146100c3c1c411002401c0e87d80401c0d03410124400103006224620315084e0403815014003a603803103600b11140030080d641c62041e419080813410b4021a0107400d0200d0f210402024004c1800340e0710200801600403440e08010080100c00340c0360600d90030034441c1c40001002c415500945202c1d64005040405041004040c040200201d08090302008240101800d0001a922520340d0000146070081501c0d0304258000e4050400c130391890307103152125a410809200030a1112034141e4508402190f0394079410800c070f400b40100c4401500500640f10700248440c0c00078014110405020000c40e120350314601044603595504001c00d40001200c0c000c082a003011100503d42d0a003141f80c0c3c03440b90101d0001540480e041850710320803005502d000b906800440004080040c9410316100411000d1079900034003201c000303455200c150307495064202c141c406940143e010000c00b100d43c0c1c07040c1d207403184c00182054501440b45000c60544080407030f4607 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 834110305 1250 834109055 834109061
    0x160501020706020d3c09140a23040608073003020a0b060105130923071709070e0a050a05070e060405010513080609071509051c0312020c0106090b04 65
    0x508042d884000c0d409800000000c651180c4034290148100000042218170080150340061070b2500e42e01c1c60103250070592824442901240440e00ca00c0c0400300c03c128141099108118204561200200200050000c00c01400040e00800503d0091400106002c41c4c03c01c4000341007980350941003100307011819401d0b0041011480030b80180c005910500201d4501e071051604020189096442d29409051080c000340f1150400304600b611101e0594192805202d00c0d400ca1900e42c800d1030090400c8030001e80446490300b916003002d0040000150b00000500035440107001c001d081640c503240241e07031480141821258031408510f82804129000e00c00c155035004690050029840c10b404c102c011764994109c8c140201c00300e690200e002c41e0b102002d10525014848042c010010241000e446040c208030003044c00c020001101020400f0340d42c2d004402c0c0190010364580d081c038504078201103554010702114081d800f4000103401e01601d1055001404891021400704469000c030700821040d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 834111555 1250 834110305 834110323
    0x110d0e0a110d02010e01110c0a0602150a020901091503020403170a02160e07050d0b0301060b0408101506031a0904050c010e0105070b1807150302091c0507060f090816050102070602 79
    0x141c501507010166500500f280e0380712001107000c0301d0141e075440c00050750380d427480d402040050700501000d504110a440c845900110050810f40c01d1002480c0028156012445413681d445600b150380c800180c003e82c111805141c0091a2281101580940c1c800560103500540014400d007044440038182c1c0701c01200549036a1059502c640e00c900000300c8054221070a0541b80d2662690f10f901107076424070a00000b405034440080d03c540c40c1c10845820300c6010b000007000107041241405250200070791610a940903800c0015072100041d80c0d41c2056991404003d80061948007400180440000e0303c900c1031000340d0711000c421200c04011161400303403102c01481d0140007404284d8503202d082403200c104031202d048441541da2501e5007a1090310714900d42001c01c2d400505400642030590b020601d00541312400c50609906503603843e600c071000c1c46150200100070345440441031050203104010312405040303440b08441102003540070000341c400c076400762084100005806002140001d9 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 834112805 1250 834111555 834111557
    0x12020a060804030e094b280209190503190201170402031603060b010909021215060c070305030d0e010528060f0e0604060801021c110d0e0a110d0201 65
    0x10410f60542805000c500150040d401c40c0484c468240c1d445101510180c04c5443d8181e90321a05404c1ca040305d6480144000b00d46c0780c0c42140000c1104500f0b00b21070032847d000c4071540440318913800c190141c2c02401810301c540d606c204200c500401103202e407890710094031021400d0380c1501ca0210403104030381140210090116252000013204100e03110707942c4e076020f400a400d4403034428000726441e1140e01c00e5081114840d5035040ca41ca200d50f400640000034080c4200704500e00031002c1c40b501c0325104000d002c0381c16580c03c4611410192103500070740b03e00c50821801c41d940140c42c1c0c5030a80d00d0b504600c007194151880d100101c8545007050050350b000b03450607181c0d010100740ca100a9010722511101d0300314142d450700c00000d203110311071084800400d44c456030070405007002c000700310654074190b029846076801401030440900d0f2000d106100300303400510000c0ca0303a4200b001d0740c036503015080c2c01a0a6070302d0074032821541600030903219101c510407e1a00440c8803140c0c2004100500900068 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 834114055 1250 834112805 834112817
    0x603100e0604020c060906040507151202030a1509271a04030225030b060117060d11030a030f11160b030a09211805150a050c03030112020a06080403 65
    0x2046000d0250380c2040d00600054a0450404109482c120081d03c2400b0558420b03800c01040c4a01481548050910242909200440c40b40b0003440900303624a81e0200030340c00030100703150131003641c040103c0c40030045110300b2203543c0d00b50181c003e2514a24100c4401030340d5842c1e8103220752030307140c0011103070303100403079000c01400007601041009008004070294480c0c40314048031000024040d0302000c4001a0f4026800d085280030312070300368007038441410b100058403104400884140340365800402034606040b040303058140f0440300701400e4051074040c0210b281040c2031540c800700c1e8010454150301c44005807181401102e076112424460742103075840281c01409480d000b00c1c000c54110030700309004030b020704c866181c014220ba03900048681d120300142c04802144e03045008140310017404142012080d280801048000d4045094041000e00004050340894040c00c10b48001c001004110382d120342e1226040c102100f40384005074801d20090500082c9284101c58039803282c1e605030340e03032 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 834115305 1250 834114055 834114059
    0x22806022b0c080d0501170303072a02060309010c0201051012021324051903110d03031b03020c07050604081f1b08042607080d110d0207020f060310 65
    0x80007444500c40d9584080140710860100480c10040140580610440e80001c065150000c19681a01c003420150300d560014010050f01781e41148800c80695500b45004180e00c030301c040d0302100000d02d400000d50105010003841a0142d0540c1b00308820216900200000d850f0102d2010540b00184201140581c803084035000506200051005201090401050030360601c158154004005803030860034001c4030100300010728242c0108988800c42c1114814030790304503140c0200700c1410345aa94000c080b641c401c181010b200c0e81c0030004590101501c19951303104020000c0103540100b031140c1c0c40384104040410117291004c100d03000c54154500030310000a00c400c0b540c1e054000d68450b48c44099403541034544518440b41d400c010314640781d880003176a2406d40f400d1070074a11020310010001e040c00c625403150802ea5400ca8014a07044100a5115200148504040c00c2403c03561031103070b100450301d000c008e103981e0080c03c2818401c648110410300c01009200c12400101c0d0388000d490069441 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 834116555 1250 834115305 834115363
    0xb010c05071707030804170717030412020d0b10082407030c0e03010507030b090c0c030a0c1104110a170708130807020303040e010302130b0f010305090a02280602 71
    0x2c0c0d01480c0c02d03500c103030384010b60b4030341340c644480c2c0080c0e00000400b10546c1010150120a000c500060401321003c04507500b61207100d20b42d03a00440c041c1d001829400b040d80300640d40c03a191010b44699020a00084900d00100e40a8042c440d5200c1d441c0144074020607518200d0384052032003e146a03030000414544e075492411030190180480c40400c5c02040102908141c03020f01600d44116090f031008600b1030040014080c1c41d003001440c00c0280c49060040040400012040f0340b03032500b551621284606150070000741041c1002041a0701a191524580c141c00d510b5004e482404000e40f0750030303808815009040d158440403030b0b0f244000f0360f111000440c0204170345108460540983c0c1c4407400c1c51641d0340860325650064000040121420004004524100c45004258844e0500902c2011118008518088410601e0a051544640c00900088420000017040300e4005040c41220340e80500c6424400310358007944410a9942180407a503540006242c25050b02d1110a0040400c00d00305 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 834117805 1250 834116555 834116579
    0x130207030c0b221212060810110c0601090501060e0f0306010e0903220801061d01030303091e0303050910060806010902070503041521060308030a0b150c060a0b010c0507 74
    0x100d202e903040300b03401e000d48000300503c1c51048110f01c035049440c40503665050103000100e464101d03800040c1450300074003003540041200c0e85055084940400d01c9822041c009101d4051811001128420b070800040e104007a508041d040f581c0c039440d08031080c03a1030011b01904843d003610168050340448010003901d003080380d400398403981c0d00c02940c0c140078200383c009241c0382018450704a40380f69110240044642889000000d007400c2440040344c40320141070341980d0300148005424036a555011030140658207506480000701c104556041a0705441c0150041c24166030282191080d000081c400000921030f04040e41c00800003001c00e40e180c41650000b23036101c1c20382141c2c680000e2100003100d40b05451248803c4031192580c0700e03201ca0300003000c1c032160324034442c200c00b103800c0807420004507060804417600200f003403c000c1340b0548030368045a012200c513810805078000004500102d1381d8041140c50007000090350a0102e03204c03032001140c001d415554054682d030050740082000c069809 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 834119055 1250 834117805 834117811
    0x1052e08090f0a030e03070501080415091704080a1416090f02132403050609040638120109020315100b130303020c1009060c0201030213090b130207030c0b 68
    0x60110ba6070900b0304030301e060500c1208a4110040b0700480c000d403035a80380501c00f88010b80000e00c1c02140c1842c054030740c030101d00c90f89440c4500c101e5840c074074001401040c607e0810001440c07040c40d41e4443d030b2080074981c5e95011800655201c00c0c024902c441190300800e154203465550001400c200f800d0102c004000d01c1d40106031079113254204600b500c480003204410000704003894200360294a21403e0603820b0048035110b80c00c05d80340400304040c40da50f884485400540047c2c00081164100c03144a002c0904440604106e0691070380d5100ea0003003036109202c4150066450001102594016070f0a0b01d18070207000b036040e00310203090301c4400a100d02c20b83d031217801071034441c800d00d82e21044140558040140d011440411060500c14141c040012079040303c401e492104142d240c1c0000180328240070302071a02081240705800081d6031080c0c051341c5184820509000c102c0b99909480e40042c600100054043d59090003100c45000e028402d440000343c241e00d0303c4130025140d640b0244503030b50003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 834120305 1250 834119055 834119071
    0xa11122502040501060f1806021c0201020c0105180f0a0b010e190f0f1b0f050334091e1202041b020f1908040b0306040b061201052e08 59
    0x62a03a40150307a03180a21402000d440d2240030742d050610070014660744142030110103c01100c2010005103a002407401800a50a502e585040c602c0d40d174228003910600040400300d6081c0717002d119607110314a45c68010324078007108030b414284036000c00c90b4907080c075240042c0408154a00402401d081c0ca10384035480703151034086d902c0400804403500f0440e04c0d03e002c0e070206942d079885070310311a00c0ea6109403d04219520368a0f5080c81c03c68000401c540b103002071400c2004004404119000100f031422030910b00b144081803841040c038415508188040203100d400110358039000110f044628081d03400034420b20028454107401d110800702584900c640490f000341c0e5542d9480303501c1d110359100c020304407000e41c0074106c8140301500003854001030225190552000082c0c030000201c080048400b101c62080b18241c032a0b035450b00043c002c04441080030340155002825242000c200c43c81c450603182e04946030151205003041c40030a40b03103112a00c040015004091410300781c02041c0380b550201003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 834121555 1250 834120305 834120367
    0x11120f1207140307120305060906030606010c0203030904090f051e030703051e161703150123030f0106021204030c030602091527030a11190e07050a1112 67
    0x119442c51860342d40820b0050700c0c440700e4842002c0750b00343d16010ba00d8000300115002c0c6814106800080d80f02c1c440640881d060080b486450021520f0610a592040320014020086400300d820700000840d40c01e8001c035018020286141c6450140038610701c4100d0b0f109004604081d683d07036098682d40d1003c60b5075200ca4001e442003071816580c06009240c420304051100500c01d04600e45010212425182a062140c0030302c1004007042c02c040a41480400c01d10780024615800014401ca02c00311003c038a40d0301d0400820881c2d500d00d0f007244c46040710102d0b1308868450350902c0c0d00c480280201c1c040100b030210603010402c0400d5543d00641703000c840c02000e2421000c0a2034102409900030380c80c040c070b00401d211404a80d42c0030007070441d104900070740142c05c0c08001030780c9160f0f50a280d0041c081c03082c0b400461646020440ea10b4450240c81000000106e07801e0140014245030003186c9803800140f464250030316440c0d408200a2000c406040d400c40c24403241c0300114443d185414151030715844 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 834122805 1250 834121555 834121583
    0x610030b0613140c190806100311070c060f080112080f03180141180a080a0201020d0b01020313270f06090b1905060a05090d11120f1207 60
    0x580103008038041d000301e0312100da80318034030051440d4040070755111106011b0070030304116041d00d840318a400c0c5426149400220544110003000540c010000054904892842c0100300d1640102c070603416101d594a61210310f070ba03a440b2244d2501041003000b404081c0c14070070201d007407507004065500500700801a00404029242c09401c607036071020400b0440700c004e00c51800d10b4140c4a43e0340c1500c0440584d01d4a50303207c0401c440c2502c40003520b1648580b1070301d20f1450120f0f00c04d00407004941c0e440303000143e4545001000a005c3e400c030740405601d65103024841c170820360001013100c411207008401e0314540c43c54548100c1408145a00304408480c0e10540185003d00354400d90b109402c46845c000f80c22804c04948204072841c0420359405849078442c0849103490303481d2080d01701c480c00c540d1980c1d0b5039800e58080340c2c01c0c09070015041d00500800e4050003004910322514091070011346a0007050300140507070503560205d20340408915003100aa00300300000440c010156607024940c900c4d00d503031b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 834124055 1250 834122805 834122831
    0xa0c030f03111b04050703201303021503100b0a0c110a0815090f011104120204270b060618090c040305070303020609060703020702060f09150f07050610030b0613 71
    0x3d481d00b84102c1e03403e0100340807030069103401d2007907640010b000e00d001c00100300058041418180070607403040141d02c01080190201c4810200100550317806080c08600320014000900c183d0015610350034021b40d820404100c4841043c241da4a00100341d854551014454846a05550011200503040304500001145031441002114540c13126256642e81528000e8404d0381050500c0103d168140d04102180c40082512b00079241650341c08400025504030f180700140040204282968071200b50b0ba0070030711101c41c500d8008040c03034000d04a0303800715a620410408688140d009245400448810001ea641804540c240d80201a400c0061038107440740c4490b8034020050f0b0003180160b204004208001d4014040d80d50130400d24101507007000040c3d8001500d034024040101401310001c07a11504a40d03902100d01c41c0c07900803408040c0d80700388030300b41041d1561040000780c07214032030709000c40c440003406051001140d401000d9500035807640003c0107150f803c40042c084009842d144000001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 834125305 1250 834124055 834124063
    0x905030307020a020103060e01080723090406090203150c0426060f060117010803040312021006060306050f0a0311060c030c01060603090213051009050c040801020f030709080a0c030f0311 82
    0xd207000780c0080000b2481403000409407030407900100d200030001c0c4010003440c88005004029140340150310074050101112030360590205440c040d60000100041c0700038400b40381c1c0002800d034005d40039243c004c841550100210002a00c030748811010801c000c0081000c1d6021503003c09050381c21a20600003620005d916004081c2c07520312801065000b070004035a0840c00c400c4102d4603445240726298034007440c060300c03400351388030150003201448403440c0e1092085c07101c407900100d8079500308201c9481e8240200100800c0c0a420b000e00301100c41090309184c1440301ca4112a40a001e0b010000005001d0080c42c0c0c03c0048400300c507100520508020748000e00811010b000d10b0740c2c00103002c2e4114010008140310b0080c607440e40740d1511040c0501c10421501e000107642602102003620344519128545610545c0c1c401341495101181440c1c4039a0b00000550046100e643d410181d140c07644501900d41c210004018410b40c2640420000154a1608406510700070f050442e0f00d00610f50b0f0345410 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 834126555 1250 834125305 834125311
    0x180e2b0f031407110c062808010b0706050a14130c0828030311030103050309030613031b080c010f06180209013c0809060c160b04080d020c060106030b06090f06070609050303 76
    0x71301d85480f9804500c1c803880b4034843d00b1f0f03189249000324440d4503205100322148107000015012640711000140c520b1f055410a05641c1e0795880c84044515010502165180c2e44034002c4424400f07a42c00043c04060000d054207442c40c000d42c400900100600c0326008030f200c4450102d051540b192645442c08072404080c500a500580c05980e592032440c04250418030024500f101000618203810046540701d9844100345101d0380c030803071100307404e400c0824160048210300d40483d802c0071408844960550418000c6812a04d5811382d25004030314081d0581c0101c881d258006907280a840140144e02340c1100070030301d4041283d40e11855100c044401c01c40c2081c140c0c0c00410001c400384080100108501d076440a8a402d906042501e0502400501080d00c00050b0040c40b8200202c0d05000110707045400c004c1800074110b650301d40c031020300c0b500c94100340305810210749405145070050802c02c0859400301e0b80108401c641003004002c106150700410f9040e034220382e0354011040020300c10070043d40 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 834127805 1250 834126555 834126577
    0x606050604060f092120130b01020c030d0f1b020d21032c1002071a01080105090601050105030a150602030904060f180e2b0f031407110c06 61
    0x2460f00400201400300a110707401840c8980b024895445020920395a858000b64060700785100018005011090b80303224100300390380500040c0c00741a034030314a03502040d0b4055084c1c00b540c0c4805481c1040544803003d805044010039185101200f0f824403442200350080340b5400c06216403000c9401081da9001002021140e001c005014100e91100200500303110b50340c07514040c0400742d81480001c1800c1441c0a82012011134114101400c0c0742c00c4c4110303111a458560119107882d51414045001007450f4a2103910500f05000424400c006010305841024080000d0640380d18040044406a0004201c1c000e400d03510071700242c28000c00001040106100e5006580300d01c42c400c10007007202c3c0d850f80948442e04040508202407008015000c030700e20180800098103894a2890354285910740d00000c01e4407640000007206030001001100c40300c800c03030380c0340e0700007014440e8280d003116070b0300d40d0900040808500051180b480b0301c041441a604804c15100503400e501c000c40d1040d0800b01d0001 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 834129055 1250 834127805 834127817
    0x3030a050a05060409020d061e0e0304060305010501110304030b1008031b0712020d1118070801060806010f17090709060b0414030307200301110304030807080130060605060406 77
    0x4041d019240c060540c200c8411030f02040807443e5035000400040e035841c0e00070702d420f446074100c0744c40817038540410b0308410001c00c00740141c00080b42c10036100d6000f8090305002c246414000700700c9500c42c602d07420042c0004801145003d066403030300400404003c00e60862891264000b1402050034000741140030307404010010104a803031103550901240340c0141c50701d00050640d1a0141c0c0c2c5040000c40c101d500134004904005c040780100e445244688907802e8001030004c1449821544180080e04851055a40c001b89440709401106c0005c0c0040c40080091260b00c150124803040760400c50308411904120380c8500e0340c8411242c103540035644a5074100e8400b00b400c01825125030124203c3c0d11084002c0c501d08402503492090323007120003100d41c41075004030078070000c9600c09501c200c2a200d03154205a407240303401e280040c5454005c8440000040802c4000262050442502c40081d140800800300000078800d44a60b09180050252040c5881d00c40011b8940c0320f0000038070143c4955507401c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 834130305 1250 834129055 834129061
    0x71505100308181e100e040b06040305160f0f0e06130e070810151503090c030b04110312030606070219030807031709070614091513170a02040b01090803030a05 70
    0x100e0381c6640800c8402e0130044030644c103030160340d9401124010103c182032503004032809501080c02006680d09236904180001004412300c2000034402d024004c130400f207070a000c1e0f19941c0f00784034803480e84a030388040c010602e0240010750110501d9a0b001d50050981052880700b001d13540107881031118814140d8200780018005c0703100901ca80d0410501d44482403118000ca00b80c1441c8821052160801c103a20404c00c086409109030807084e01183c204098208040e20f80c140182408015101201d525401219100e076508010658442540d540000e107805d41e034843e002d00c0401da10a48040342e01a0b5041d0110004000d00d034600c0e0042c40c01003104545902e050306e00644111600d820185c03017010b42034100148268001510420344000d80340c00c0340b130032a4000903e41c8a00450301003681c0a01d0305150084095480009000c01d082c0d1781744610b040c0c580e00c0701c0050140320801810b1031540c005c0c400c904090305040c0c221451150061410310f500c15990b0103c40c0c11364105968840d82e4039200d0040c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 834131555 1250 834130305 834130309
    0x230d080f0d09140120090904150c0314070c0308070302090f04050f04050f0a120e040204031509110d02010c11120a0602090a0501110c091f0807030204050c07150510030818 75
    0x280f541003045c01c2e2a062000303150152001c9503400340642e00c41c412000d020018080200d08141c0c101343e110721000600500288800142c003800350080c001c6400316a210000d440d4504c41c4800100c3d141e01615101055128240d08601035403000798041d400c0b48051403041402d8403981f041c14480c2c904c55401c0107050600b031a10340e00303064009c0070442071540300010316004203488002001d0408024185514040c1850001c07130080e01455102401811041508643c540e80503085008500d1080c10f042c01c40d10940303010400448003ea0000e0b000402030b40e03000c0700040d850740502d100ea00c8000c00c1d8805c0c650310040d1861074101300c01402c950054001c10640e8a074180f0030303903d9000d068242090b0292030380c040c040c903a4139000408124816490310002c54082c55484600b2544100d01c2d038803990300d0545940445c0c4c2d5440d854030080303001d40d1a240c0018007201509041d80d80460344031214140d4000d003412a000540300183c1003490401a401c0000001161400101034079500402000c4140811200b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 834132805 1250 834131555 834131561
    0x270102030c1614120717010f140907060333030501110d0e0c0105120709030b090a02031c0503060d1e060f0c0309080f0a1707050301230d080f0d091401 66
    0x940f00c1c0c014408484103c002c80340116901d03050710100c9094406040081d1549405009000c4406050600c0d0002100c1003518090400703200e50b20200840f0f0a03503036242000ca00701c0d004500091100000407502d10380c6060030102812445003018110f0388456120344425007100e003000300c40c6150450000392602e41504900405050415440142c10036560203400a0f03c1e83c4140c2948540b40500100018100c038010290180a150046030140c0e03103180c03c001d00c96560300c070300c00164030911540c61a0944a04c100078406260b26481e0f4034142151156001c0c00404c81203641e044030350191400921480c401000021004a4000c0360046099840381039010700301e802c402c860004150034103456070003054004044403c00700052284590b200702c141011581c20035140e40d0180b2042404042c0400030358000081c5041c1c0f90301e00d0141c0e2207906450f50143d84848031181da1030300010031040100114261300040c007221025110034070319158405000b80202c60700c0140c2140c8602101e03990401c004000d00c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 834134055 1250 834132805 834132839
    0x1080106051f0801050f01110706030506041a15090a03081611010e0a0b0d0609050103080712020a0c1806080307050a0309140904110301060b030c030604050c270102030c16 75
    0x1000b10034484414000400310705050050714002c2c0701c0b10b00c450206900c200741403044203401500795202c1070b8542100501801080d80c8403485a410042680721000c2111100c2d51206002814241d50b42c1c2c001d42c8054203a0404d100c1d15600185118002002c10b91150082c1002d50615043c480460117500d0001c4c10080308034002410000a85816403007500c944503070f00d0580303161071509611402c03001c2d00100034007d80c2c0c1040a07000d0909000004100400b405001141d00c14428043c0b001015031040f0382d07803014031802510400340110104205c019110900e84090120040400c0003515890840d1440e80012021120f9502012040c0705140d44146c40d003001d000c2090b040c0805040ea180010b0428034080c0016141612a140e41034280c0e609610650041440f01c4089459242408070622550821207080780181d0410002480d820509000c68802402d1400079003401c61300c40c0004c031116508500010305500c010403203d0f10b04c1c4002c02100441541c800d400503059810321a2490081c5450 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 834135305 1250 834134055 834134089
    0x20c071203023f0f0c010b0f040b0d0b090319050703030e1f2403031e0504030f14011d0703051216030f12020d0203180a03120903020c090108010605 65
    0x80c000c03002d4281c0141c10b825030202100071a1003441041201801c48a1040c0c290325008200300203001032401c076040d0801c116251f011500d910000010400340005e1329007100d4250745c400860104000000e03d8108281d0704103d0503003c481c1000485042110b90016211040300800c0011681c04201a414003a14444d07040340c40180c4694962900e00640d2410141100f9a2141d2100c06200100300b41c210104c88210031094904072043d03070303414082d200e0710907146001d8046202d6140441010301907000c4608a0b41d026048180c40081c5403105040b082058111070302c0395490f90980e1240c1e03040c40321034208024000c0043e003041882d61802524141c102c81b042c0701da00c030050040c9480f2841c0e4400400d1100d070507041ca813242014416044420500d41b02c0303001310306840030030203101c403100603409180708940303110801ca001080003d445a607102d40b90342c02800102c0d01402c80c039600310160499940c3e02c1c42401190301a42080000440c03c2000740c00149480e075585500b08001d103040b4005418058031 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 834136555 1250 834135305 834135343
    0x70f0e070201090b070c03170a0606090b0f030a050411220608010b030606060a02030f130303090501170408090604030b090607091a0316140d0f0f0e03090d0501020c07120302 76
    0x565aa40c00721070010130603030038440c1040e8400281401608c901c520100301d000d1002d054501802090000c0c8600d000d0040003410302c80740403a0181ca41c0c000c40c0c404841c040001c0e401e594422007107001808000b00b00311044100903410400715103502c1c20405610301c280d5140d10940a0000d030800441d2501d0780450156810b1071000c031030300d8070080303400c2d5000801603c000c0c0c0c1d16003076400c0030391851203032403c3c3d40e1001600144200c566002008000c080e0f1348246e071040040d642e1100115401c0040c541705000318000b00c0b000c81c00103442c0000406000034090101420244d40c1e8890140c0c2078421900000260040020001003d51041c0c0f40b40250170716036403c62410b10500152505070000805d040d5900d9018003e5201c11405050440d0300d5034041c02e1708540d20408021291f0107480203905021410341001c80b005010320f80d80c064003c2d040e118500460410035520208000f009603003a040c0e0305035500b008480c0200205006a00251450705030361110312006c1d00d030007494404810444500414 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 834137805 1250 834136555 834136571
    0xa021b0406031a0705130e040b07050405030d030e010f06030311060f01060815040b0a0915050105030c2502090f1b190804030215070e01020c1e09040602070203070f0e070201 76
    0x15100d0004410043c200d0300607000d950b112001d84251081200c0050103000710f41000401c01d1550541070b100d5072040c84000e8180d01e41440541d40350141d40150790707140d080840b01d000490f03c20b0f4071006003004010004035500882458243c00c4510343d030020b90009034920340a1580550400c002e5801080e40b40c14041c00b589041d078010914000688544900c18007469903d201d6600d1740c10010400400409602c0b1040d510b8842a00a0882c0710300100b18200c2e1007030000e19903001380141c3e8403e00c00c030058149000405030017199a00189042d4608004002000c080941c035142c0f4000d100740c1c1e00b004641440d080900c4d0405024984a806a43c8c400040240c1030040e20089030400144003a410f015026484601c0c040e800c0032030044c602103079000c805c0704114000798030416401034150280c0a03901c401860340107108070b0784401d10040090300300980c0c5400d001c0c1042c04940d548203008810040c2014555030000c1e052444580c000c098003682003105001c8103d40748a031580048041c002004015 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 834139055 1250 834137805 834137813
    0x215031612021c0905010c0801030507180e031602010908010603020d0f03030b1509041401031208090a15050103030f08161209080412051608060f0c0409020a021b040603 74
    0x180214224604100240035400c0c151026901550342c0340100e4110750450805070711501c0002c00c41204145d400358241224000020701807501079060f81d0304075006e020018200000403154080035404054910b9491007140c0c803200f414030244c0001380c21110403100182060000410b00c0e602c42c1c1000b0f006924101c02000140c3d01d03820107404c001d40c80990000f000903d41010340c000d0030400d141e0f940054407075007065100d42c02d01c0000c0050381011981080b01c60080103e00904603002d00004007940e41e110226500079008080c96071f03103c550390f0f00f16266402c0302d07640d08403050451012401040e441d400180105a00080c050055403598038280f11249805400c0c90440b000124100d4207004504d0085005080c50740c100150f810b401145d4130b030f0303503030b559a40e18148002002e5050300c442c000e003607080f2040c0009080500895124000505041d05e03403100d68056400080c00c0813403684d0b400c100004918100c2d001071b2801000c02e40143c103824120719451400300948003d550703c6546840c03000d000007 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 834140305 1250 834139055 834139081
    0x406020307031b02060706060f140607200a0906060e06030910090809150310060507080a0806010504050a030614090c152203050a050c030a020108130c0e070c021503 72
    0xa5415140c030b440c41c540d04008902080e9190f00d0060b4010724001181d205100d5240c11103011a030062902c1c2c010140d50718000004400700e03150b850f43c408010401000894600001083c210760100607400f000280000016a80300795540400010350b201c035000c00ca00b98115004500ca1002654203034a140f8080015035150010740220100c010f07035466612007806510000da40c26170a02602000d17030905529221300150b001100c6030703103d543c44100301050a030703c1a000d9540181d8403030310003410320b0a002d0003501d0600000740348a040010502c8002195030321000c01100a6015110024481c800b060344454143c500421180595100c0c510300c0c00700f5115035510740c100300c180c000300c03645580340700f18468511018004100c58107011b00d94040705000c001b04003000b01911620844030228100d00900d43c5581c3e550340080e0210f0104c10001e034500726200000c000051240481c030606036124951002401030035240d5100186030a02403070114100340901c105810480009079003146440c0d8444940 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 834141555 1250 834140305 834140317
    0x8150a030c0905180d02070e01080d05040b0703030f0c08060f180a1a0d0501060e010e0606070b07021006141201020408030409020715060e06010e04020c0c01050a0215010f0302090c04060203 83
    0x3941e6a800c0060302c8402989480c030f0030382d9030310826036003800c5e441c4c400256a4413050240701000e40074100001a1040f001403400388281d02d903151682010b113800e1004080303402c00c44003074061513120070094040c10403520a01e444d091a43c1c6400d440390504005021500b10303580306046c09120241954000c030101140d03119030181d10740c0c8011500c0c0c80c80c800b180d41048200003105402c4040070031040204541074010005890002007010f900c0ea03614841c44141000c10f071040c5420a00230012034010031000552035030f01c510540116004140307800501012109540d2081c1e0160141164803512031a01b40000703194220340b08025424182400c1c00103440e4491031041c15240da500041c49401c10400318a540e03501a030640782080001d81d80c01d0000729203a801c40d0301f180060900c40e49591240380503c01d95001216000c01051000203504c01556980d20a03800e00c801c0d071142d01c203c020610103005c40140603003c141600850345183d44180f01c0c030018013601c0c03922204001c0c032007440800d90000c25a95 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 834142805 1250 834141555 834141569
    0xb10020c04050a180b04060b0105131806120b040605130b0109050403020a020910050321030403031a0607050c040f36060f1a01080105100503060f040c08150a030c 71
    0x140b15214070740c40900805a10b03101d040c500d40e03c50300302c1c1e06101403e0743c464801ca002d501c1c244104240c0800445140c46a914018400e941903a000c0c000a442c1c400d200c0c008003003803140012410b8444040d24200900d1140c00c031547e0311741c002040108040b50045640040344050784a80300480f90b50b906400d500c050142503106a61070f00040d062510070010b00458a030003802101d118101117280e4480c1006a001c0c072402071040c25612403000c10b00ea41341659004944038102c2c11600d61382e03800c8020b030403450301909419041c000c0c0401d40d99607090040ca2060b21400c0103010050443c1d040c0001d48805001060307440c2d280400e03041029007620841d0024103410750003c001010742007104003801d01c403034001801080c07515207071021740070307050b800958071356400c0407000c00896480700110b41114003401215004104864600c2ca0140184051a00403400030140e00d000e030ba03194081000c4507461030220300028202814000d4215803034026205c0408103481010005040d48c840b00803585451040403 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 834144055 1250 834142805 834142811
    0x292a01060b09061c090c03140c01210603020411120f0c07020d06091a011e06020304060309020604030b090c090a061a160204060b041703040f060e120a060603060b10020c04 75
    0x600e1548242007003411805000e04100305d01311090800d400701391002d01045415038050381c100541144001a8400c080b081651a103100344801501100f03082a980059440076403104000f0005903a24014003120800b041511902c81501c00c440110005024040340c0d8101a040c040c00b000c24030050803503050540581d91442440814a802c000130074002c00060002c060004140d6503500d10fa00f40a8100c2d03520b6525071200b130340045085001404140b10341e2000d030344104820041c69010307820022940c0d0005003103e041c156039407104007615000300c80d8200d8031307040320140b00350038507100c542941c220a486e41d041045500b401d00e2014030762049002040c01d003001041900c0751407203e188213400d036a40508180507103581c1d00a840d05076005400398600c10504c20a00a000c00b2000084c4c44c04c5541910496484500c0c141040e81c11040d000e85040e000904402c8201c0141e108012a06016214440000d022440c3d800c1490803900c628048910072a5510542c0c20280c0c0c3c005104e51580c02c04072000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 834145305 1250 834144055 834144067
    0x618160f0303050f040f121106090306150a0e0405030a1b0510021c0c0804061805060f0703090c060e03070b03090c1201061a0711030c0a292a01060b0906 67
    0x1180900981d4880c6400403207080007c500850000c001080c100e201c0e08030840d880a401c0200946030084841031074055210340000b035040140c01d44110381c6141d02400b811030054450949076220341085034280c4255000040e4001c4240c2e0240c6e0500040304206980c0c8104d4665680c0d15489011011001404c9500403131442184421403000700e0903491b0f40391040090500c0d10001400d0110101d6099408503c0c0c00f14421080d4803491720040661f0f40700015000642d00c14205044039007005c1d0800080643d240e5200001a81f5400c8250180c0420b444180e5580341030020540340105540011844817824000d0100e40030000480142a80084035503810120700d0342803d5005001c141d008030300591461140e4820b85080d00002e0a8640c0501c229443d0070940d4000c1c16074581d0703180c14045d0044107e58042005aa94403000c62100c400607410405000c1c14809200040e0001061854110b041201c400490000e004040c1c0c85600707540d00030301c61070346001c4010310107000f0460180d0050341c0003d96 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 834146555 1250 834145305 834145327
    0xb0309160602010b04050c1603120207020405010608010806012c3103140a08010605030a0b041a040e0c010e040c030b0a030f1211100c110618160f030305 67
    0x2814028404441108400e15500d4000074081c000c442c0c20380d40a01c1c070700008500010a60b00884004641c01c248640b03648003165000c8407403040301742c6400c80181e420b000038401640c460051600800c0340e9030702d0450760350410b9211800c1200c103900a4242e0101520380901c1a000340039454880c000070950088030303035602008007650700e40c460300400449c0f01060121303041c10001c0c84812501400b030b9498152559680c2800c00c0c10740308180125021808400c0104801480783e0015640f00314a20380c01b2505242c200b000c03606603988400c4c102803080d031403000c024181c103242c03164540441c16030b03008010341110840080c140ba114007008034040c6d5100c1600d10a81802134201e08070441c0040c10f0b00301056681c1c203094030403281c010400c07244a5400b20403152031911404518842d00c45c3e82c0b005e4402c0181c000088001440a03103200c0040c00000c13144900c1806c418080c480c85902101c0842454140380c0f80d00608121f010708024402010144040c0825400403010a081d664142005540caa80d9044 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 834147805 1250 834146555 834146563
    0x60d120c060c2109080f030714040806040308161d01180e060f100f0e1305070f0e012115050310020405090a0225080c030c0109020901060212040b0309 66
    0x4409448182400001582c82e0790202095410703040c085030406283d400a188002501c0d8a0000505005001c1c0544802c09040200454001d207181c2007802d54080380070411903680c0c215501082c0d50350007030780400040c9500010659448264921b0074020001030083c094048240360410118032842540c01712406c0c0d0041c0070054003040c0c0c1c11260f184035507aa5440e80507051040f01c01601480119081c040c0504003031502400070491078031110b0000ca80766a040b5400d4681c2d0050692140748801c0e60200142c95120704c9000350090f64034184803075080c034005001303010711121032410800d2080007504a035080d0f000780d2441140004c80032488200c0c40d4000c1c8030b1f020040c0c000546c180291041001c3c0d80c07030340e0760050044031001d40d6001426a02c1e440310804034050f071030210700c2c105440c7e0029808850000c1140c2e0074688101e07941420458000d00e00f516603000303400e020140f43e660b01c0c5030505501e4201040d41c0141524401040f58406804500f2031a0103140300340e4510075008404070f02805030500c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 834149055 1250 834147805 834147827
    0xf211e0c121918020316080d0c06020d0603080717210a09050106080d110c1f02120417060c0915030702070b0a05041d15010f09120609020108070206060d12 68
    0xb8040e149070701550301203091550f44120302c81d11503510003c41c80040d1000700c100312484072014260804040c001076038040230001080300c440c5d42c00c1205074042e0880c4d10450010303500800702c25403100b030140b801000030080302d00c0c28840c0403010300000c00c011006085915003421101f4000c1a01e03155080414040c04c60721b0401417995003048004141ba48000550621804903603480502410010018603200c40c00c83c00c8054114038110b045e40039040c1100111680c0807440d104650701c034a0300406001180c1c000c0d400a21440f14058031413840203008000c203d400061001c10140340868200006001d04404408102590804000a550740d4024000304009068080c6840d68500064000801a900c280110035184140b40c142003c2e00e04400d400c180300340c1c1908226910010b48000541d20308a107c035510007000840000402d0341ea0808140410042c8207601c08284001c02d84005003030144020058002c66001c0001c00801b0b80e680f00c80c0c0c08825400c0149a240d0103035080b0116030f40c001032 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 834150305 1250 834149055 834149101
    0x906150f0d03090b0d020c0d0305011a072406260a3e1f020706110705030109060606030b19030b040201030f091a010f0f0b0f211e0c12 59
    0x40384141180170643c008081c507010035030039511410300545040d01181c5007802200c21500d100a041c9a91181d82001015558010f03800c0a03001a500018013184041e202003000c0142d4842c0010000e5070a14200c10400742500148a08400c60b03204405075148600e4801a0203038218814040da504203a02b5003030034400c20308000740c1e19a840741603201c1d9a10308150700c0c1d44c0502000c0303080014000d6008107003903c4104079030252490515051080302c0c1c2e06d003019191341c00c5015902000402d66800d10804030640e1151802040305440c002d005400c590f80c4400a80c02082c602201800c40c403210b14101c0c099030360207103043d1041d1702c543c001200101604400030190510b0201c0500034030a41c98403c00404181140024140e86c89100c5034080c094988038100140305407901c24401c401192000e00a0040006207050810b1070300c080f00000c1e428540c040c09910080b400611204e29401c0d480121400021a40400c3c141804000180f0174499007024508029000c0041000c00c85d65004c482c8148200e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 834151555 1250 834150305 834150307
    0x503060d0f0206031e0a020405490501060b090603011502100903050324011d240d110301121401090b01091514030c010c1e0b0906150f0d03090b 63
    0x13210080c4030308885a940c02d0041d90f0326170400038100052030b0007110223a030005002110440e80c10961105012400c1a00c0e40c2180b00046680090108921203200e0714440c00700d2301030149829041903400c40f03038903401a94025170200b01c465141d80724403045034111042e81000700074444950740220f0a2545400c401464141404142d00038590b1000185024480480035141e40721030441d0084032844682c0c010742d001c00c0302808050701502c82c540192181d90806085d40c812295410903154078503491854178a616800071641d844401c800380300d41d02c0c00551100e00319256504100404119000418000701007030403850010104000a4110383c04040d1302081011403541c50b850100050005c0c0441c02c02d2824480000054174100001c0074181c81030f0140c003900350301951100445e051184000291400710710818001c464054140c643c20489000e0b514001250030001201d03410208050003042c50010400e0303400c011981ca07420b000b40541c100b220750344640340b007a150540b901501e5a000c6003003410 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 834152805 1250 834151555 834151561
    0x20616050706090303030f050702060117100c2601051302070618030f0e0414010e1e07030605122a0301060f03050102030f07111005041a150112020a0503060d0f020603 73
    0x1403c00b1070403050768402e880510492015030b0000301159421151100107074002d07030040080134000b40d05a9560014001500c40c00030326400300000303981c8aa1080e01c00107110042201c0d100182d404c9081e58400019030a61142d454000025181d4030750085d544001c540c0005caa80c100a05035101c0c0380c446c5030510034407014240509000e0180c05d01821800f001c526460b02080d00c9103014415072540300c0b0018848807940e424005024064130004010f03048021000084580e51851202d20602c01c030742070741c2c020506a040c441030000000c084d6503021000d5004c0c07581d0b1542044507018026200500481103041180030000003800350581d80d010801c400070005011042c444103400840c4180503130130300d505098843c1c142c100c03040600c0c2d1903140c10517000602d0500c0440041e40044e500301c0d01441810402200031003456010f41410345000c16801d05200c20b0174650358008507040040e100f80301c011030505000d034002520300d12004040d140300c1d240c0b004220303040000041c480086150080c1c90030f9103a01d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 834154055 1250 834152805 834152807
    0x30a0e0f09130201080108150112060b13020d0605060918070e0a0e01080607022803032304062405042714010b1e0d0215030709030314040f03020616050706 68
    0x4505182c140c1c002103130140040b507600340025402001c0c0c500001c2c110361680c41d0181070141050030f424121342c0240c441c0320304201503440c842d00c00715130804018016980d01500d001230701120881e500490284200344083c04ad156502e12003902d0850042e9000c079000d9031250002c80e019010b10710501c0e480700c1c5014000c50458686d02d6500d05135140003085501c00d8071003442c1641e5519041803114203011280080f10a04050349200300341c2c01c0d110b41401328030140108140050380425441d50402100060100070601c074181c090185d504600d140d07a01c3d0300321140040070300380040c14000c3c18051900c074002e540d042000d07074a9401401c101d400f04400050308070700d0018008085071100300002c0d82485000c9a40b440c0201d06c50a04190100c04580b401d02140e0900c1b03800141000160303030142c107023225141e0814180c0002e520a200907a0f42c148405c0c11403074060b15810041c0b4594603580800e200501100e02e0b031901240a50343c040720104e403585c401900400708001c05540007040c6000d201000a601 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 834155305 1250 834154055 834154081
    0x50106140a0905010302090414100f0c020c0907090504150510030c1106010501080703110903150a06120b040618050a050114090f121308031309180302030a0e0f09 71
    0x5218112030032080301e0b580d9504801a00c60071301000c0c1d8418201c1000ca00003072541101c440350b0440c4c51007076454024018055008880b040c24002c400c89440e00c062013001503050140f8401088201e4040ca51418000402000e9120754001e69000f030f507a0b524545810040c50300c03018000c1000070803c403c0031310801c40023030103489988100e6012402d03a00b86030200c0100071501a043c1c0304181d4522a50356030301c400031006040000a8034441c6e80c0d0030000078180392014048072042041a80c00340040b400c1c4202a10101c402c10b40c010000650322051b00030001d1f4441d202d05d43c0140e00500b010400c05070b4504c0324020f003030700c24000420a10641154008119040d041815040d9042c4201aa155540c20030582c0325000014034a415400407140c8a001000d5000508143c584d8050003002c540d4a800065145522500280504d41c5002d0000c101c0740900b402005800c031020b1407035034001503860380c0c0696a805030b121010b050090040007205503441b0a1070401ca00600244a611181003a121008030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 834156555 1250 834155305 834155339
    0x804080609060411010309140a0605090d02030a020a0609030216090902030127060e1006060e0925031e0f021b0c0d080c0322081606091809050106 64
    0x296006034000524038480100e40b0611694124030010130409910f0011402400000300449801c4150100d03d21381d000100034240d0154890b8000280c6810400c82d03851400c00d1743c84400045500030400c88442c5540412581c0c1c41a52046000c64510014035060382442d07140041d082d00040c080c100000c4604d0141c0280540751b0003603000700108415000521100401d88440328604198584140c00042c496805019510f044505507442c100340300e80100f05a030540e620000020f980d8003404062440c201074580e030400c800140104881d00d5001c50004510742e659072032000d0503034425821007012000c0644001d0f00f140f0328010050101200c4900c1e00175004515030b4207507806000005a0780f000000b41c1924803810052800382c0c041035641d580d0300f6035400f81b1490703019404284221030034004403950006200c3c02c2120f1012089041c100a14500040e10300340107240c51070300508101e0150000b01800c241e410010032200c4804000b04100007070006a40010b10a40c80c00360f0000d9502c18800c1301d058 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 834157805 1250 834156555 834156569
    0x60c120a02090618010210020309010f11130b030a020f0406091401110715021212011a0315040c020f0d080106120603080a0309020319050312160207051c0804030804 72
    0x248a0325410391200890007041003890300800c08000c20f0a0f0000e00d01e04907540440140704403004940382c96000f00a0780c01c04e803174241040c1e4480c0751b0080c9400310340c002c400ea01c07500030681500380346030aa58419290301d907210740010310358000b010910901080c3c04441111040c80602650361307985407401000051944180641c200300c4192241c003961003488440560f0610a006040303250800c07a0414400c0495069001035103e03e5401c3c8605006e0304000e04209a0584400002580b4010941d140d03007a0b020002e03c0c407402d08000b000b10444103043ca4220349030080d5030004441a064800380d1a084038031140d110a44180711020701c40c968409002410703110365584409072440510440c4040c0c03010703804010940c0e081800001c4049100ba444030079480c0c002070440f00c0741008640101d501c0140050182d0340f41d000040c00700751010039030280c585c000c0000e00c032490410301500c01c02500d6410501903248580e1009600701ca0b81105100801809038101e1a41691160f0b240303401e4100d5071051140b1a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 834159055 1250 834157805 834157837
    0xd121b0c03150203100b0904020409060f0e0c12010e19020c010507030c0504060203091507080a020a05010c1d091b040e010f06081603090c0f03050309090115050405130e060c 76
    0x4507404069000742c1c2d000e00007150030440d175a42040426140c90f0403d484a5030042c0d8207101c000740b8094540101c0009080340c4c1201c114841c20544080042c602c010440c00c03450f8010480c1c41d00250030700484038112101d0000d0402c458541c040c1d02e028829135000035015503030011514500140041d80428011740860314100000c00c0342c0b100a0b200c03030145205100c0035030820b029640d003038140451000b8864190310900d905e000726503640c1005603000300112000582c44405040100b10b003d100c0c4011100c04c1d0304150445a030020814200b8156154486d40140890030106a0542e090310050f1000041e20b641e00b911942c40740c10300c41e5000c2d030902c07407506000100e41001601c1c50080b1107490160342d06026150398003c0c00071064000c2e1400d40c504451000f00c4c3c100004005040200460207148070f0f1014642d10481882044241c002c1a00b04035808402d10f580340c030300c140d00442260200c030000d0b070311890700c05100744a0300001c0030380c0510325075103000340340800c044c0d0001000201200f11003010b0700 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 834160305 1250 834159055 834159083
    0x40c0e070302030603010e3d060e07090902031006050a1206090b0102070e040803130c0302040906050a05090d091406160f1b06231c0b0a140d121b0c03 66
    0x20341d235201a8440650038808d80d6130120307801c034901048600908070a1481140c0c107015509480011075046601c140c030f40024030701c1804012940314401500605103c202942903041c08292022035544078030138103081c46000a2400c0e5140c0c092241000080f070506020002660f48043c1030001d4481d01e80c15600601400303a01103075007000a00242d00850300803071b8031030840d130f1640c100040340c0e4180c42041e144052001000070041e0741d640100d02c462446901d002c206424078840340b41c1619030252804100340c1003011401c1c1d144c0c3d4400713182021140100502c84000d8404070100341180715010000150301800012f83d41841100c3d5510082d051160002d804c1e16540100f0301d00500d07a04d4000d03140011210303070092952001d0030541e00410f0020141c95403030728850200c2d00c0c0c21412a05018503d803511072240402618140c003d0030000d0900d8500c480200c04814001818901c3c1d040004107001d010340d4102800e907208081c4600c07014210209040e01031103e040c415210002444210350244e202d40300 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 834161555 1250 834160305 834160331
    0x906062303010207050a0f030504030506070f0906050a1e03090803131a1501201009021311030103062304151a0108040f0302010209130219091d040c0e07030203060301 73
    0x8030742c4c2050b044406404000010380e1440050051a481034040280034400417000c60002c1c0f201c103024100688858180802080e03018101100c264410800c0c040240304403c5101e07044450300f403112618110034a1034040218054004120028000d0700340315022080208841206030f0014199020700b408581c8002e0350101e107a100507040316a80741181c0080c10704840e6501494040b2815000300100320392401d4203400c8a403800b002444a41d8009031620315801c1035003402d80b07607051344581031103007840f030f21440d0a1040721901c010b00c001441780b569007604900128111a2041e801c00c1484081200c0c0e09090400c0f00a0301e0124080300c11991030644001c04040c040d4940d400d4020041c0c4840685503281d07100d400d40100161010b80541d5000c01c10054103a445024540ca0910448001621150000030680f061200d054044042c00b15100080c450780c0d0712007110104810110140704840d45d114604030700c0720003065110301030071a035030024000b203242c06d0f40244d0722886040d03000b08260082d03051 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 834162805 1250 834161555 834161557
    0x101802071505090d12021b1501090c090509090312010e0f0a140c07020123070606090513020d0606120c08010c020a120c050a0f030816081e060409060623030102 70
    0x20000e2882e8444e800716100c0c1802400d20041d541c40c003200050820002000d20801a0a20020943c10390001e01071040d001642031255405001294010402c142548102030442c40c114059640300d00e005c0c40001d5040d6030308108a841d42c0007240e00c0849296500c055031007030314100380c1e14640c2c01c910010001e000100b551081d9600411150035800054450680b0320b8043d50190030306a04011040031109040c405501c02a00b11301c101c0c1048a03502e600504219003200c84580046040078144000d016150f02e802c0c0ca04400250100e80c0540d62540c58a400c4000f804c0542c4204e2010071480401c03014401c0503400c640c110f43c13440c1c0086c0206099480100d895100f202c40c010709006000300c082c21028441c4410040c4d141c468012148000c0030364880821801e8420390890004200c9010480500615480041c1d000d4040c181300e400360a1135903081119510540c400e00350f03624050b0000345e4a41e1140c0000d99009e40001040201c07170340328203200b01d10120101d040c2040306c1214901c101039090500c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 834164055 1250 834162805 834162811
    0xd0c09080c0303041505090915010e120a030e0d0b010602010c1b030c150b0409110f0109081507200f0f0a1a09070506032526101802071505 61
    0x300903600d03050a000ba00e21003040c00c03100c4c41c0d04206c0180410401c98455440c481d0040e01c003c1102d105648101c8001010039801d02034050080000c01c482e2141c0c104005400d240c40d07030303140c02c0a8050b0051180898011b41003510090604050323040000368054044d400300301032540d0356446800c0b00740ca101906a014150000c0100003400040d0079001056040d6803400001c054450082806141c5070000350654000e09425200741e07203800c1600e0341500d03082407004a200f10a007441c1c550706140200254032000f0307545049000000000010348034600c0b90840c1d115040040d85c0003a0303240145501c42e59500801f8080901d1841a0640c03130032200800561002d6141c5c0c480c088114005140070511060354014002c6916485496404602d44d90340102841c42940d0f0080c000319041d05001c52000c0b182e00c3c41c1e000300184030501c148100d180003c4101440c02c08110000503016443c0d852030400c104401c0d81c00200079003d1203000e003c0c0c05103550004d01c030701800388044000400c00c848444044031070607 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 834165305 1250 834164055 834164059
    0x190302030904201206180603030301120510240608101415030c211909020316060f200718021c0902011d0303030703180203030d0c09080c 60
    0xd0150100c1c61509401c5907489000036400c40948200350314400c80590000040101c0d000010000c00c08030781030080280c031440250f291019600e0600c48080390300c0303120602403000042c20170360303210b02404800c000c1c01c80503207050a400c0021104c1c60b030250303800f840600821900050211070010f48a8840c0c0180760149400d441503501c6245401070042640419025940c2c00840c0021403001606442d4040d6101e2000901c102d5500c0d0b40c1c0e0380c4040c00d1420075200a540f500b21100c02d019041d505182000c42d0444040400035848100d1300010b0302e40041c0c003032906440c0c0c40d443c0c40801c456510110442010442d503c0780b800c040d420303024282844070226285829079100a104000301c0030583c08902007504c0c24800145407074080b5900c8982d0091001c1c2c600350113600d5105500c110750b40a01e414008010146683d101d603062200001d84a120241003e41051b0700d40120280620b1042800c145c0280e0003400c99541d078810317050000142ca003d0fa04070021034140a80003400c80c7c408907010350704241c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 834166555 1250 834165305 834165307
    0x51c0905120c07150503010513110406111c02011b2a080d02030c1e03100506210a090215030103050703300804110a0308030c1608130819030203 63
    0x4588004916400c00c02a5010b603100d007403000078243ca201d100303803103074030b590b5941d125580c0d0b042c801880840c100b03103a15007811a00d006181d0761104101025601500e40c1c0c0c6c902200c032400b010902514000282e0650006545e102d0301c8031a0b110f070151302c0600e00495803603d60007910460013045da0a003090282c5003aa1320036140c001907144610711300d031101562080880d14101080c1c09800c5003282c008441c40f0010203400100c003c950400a48401072030300c95411078524600e081d041008140d15075100c0d8601072040410351002454030384c1e80d501c8401030350402d45034451a01540c0310f0060501080b041e1b002c0c07484000786c1c141903a626000c0728180e80e040801000c2c0345107180e0350780d02900f1101e4110003507480d6003014000b00d0700c0c1126188440001a41c0c0c0e8500c40d0403d42880c000010003005050b106a9400303004000040c840f00540780d01041d41250b2548418080d00c00108c0f603640301c80020015500061948041c00c404002801541d8200341190140070108060316490240103030302901581c4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 834167805 1250 834166555 834166573
    0x30b0c0c100b0406030b0403230f0a0c03021f1401060f020619180302010c0909020306010f12091b030308010e0c032701050106021b0f01171b0703051c0905 68
    0x201c10b400450544001910002e21140d480d1180056a20700340c8084000620600d801f248044031810400b600d220b0400c2075510780b00c1c880301407500510403c0c2c1d084050049140d01d007000e06000744240326024080d1920038a00108001c1184010441070707a020b54010f04000010501903c1507281c0f08400301250002c020079112048401506120139200f0300d5a035882c3c000350743d201044000210b02140c842d40010619601640e40580072084540140382402d105000300401c980c0d0082003058203009a040504040c00e51059034009081e1000020b0a04400100303400e920005603244642142d0090b950703070300b1990300e58440e860348900039a55103040309014030200e02c2c0312031b44108c0b641c4070030728603281b014030448147c11249c2520026030020002d40c101c1003800004601c10302c80320071505070840d03600111200304000171307040045c01c8210a4404442c500014150b6400451000341410f00c1c03012a6215401c034a0300070400c2d8021612541800c3c1010703003400511107280242c10025030f22001800242c5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 834169055 1250 834167805 834167833
    0x100605220b040c0f030b330c0106030503070c140609040b010c0510060602010c05040807030332181c08030c090a1d010b04060203192601030b0c0c 64
    0x240144500c0d4081c0d656401c01086030b0312407140886204058642040007000303100c0180403a8840545240a41c01d01207002e004510310380c81c0001407641922000e0101c041a1110104500809043c80020741ca09107020040c040b0010181054500c03610f58190126100d019070812134148030340050f00100c1c244081c4040b4a0580c024100350f44043c54480c084041c503494003171401e04d4a81c2204121969100c0c2442003960a0050408080c406d04209180030726111295a82e40640c2c40041d00f0040300001300307204106818849a0a454004031610f1501500c0c050008568400e200641990b2141c1c50746081c607040516103409418403288055161096030385034900f880c0e01c000d0100c0c42e82a01000180c031240c0d80c03110340801500000302051a800d0100241c003c0c80801031300300b8480710030103000400c00b885c0e0010403901080000130340038291a5464009030380068a81c52000380c810b1444240b07540400c2000010b40c102d0b8051856500c40d51600c8a03c040d00303114102c10740d44140c1060341035603815 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 834170305 1250 834169055 834169099
    0xb03070302280903020306100e0a020307020a0c081f0e0a0f05190606081005040c1a040b0301080c0118120b130b010605121509150d23100605 62
    0x30042c00070300203001000700c0d0128407001050710384000104034158024001e5040c20800103900800e442c5440782054204000c0b01d0300101c0c010311440c1040c0e000000548000c0c030900000140e41c0c0e10664280c101c0d5241d09155480f00425621803660844102d032405030b00c2410701900e020000d8050180c10a404c060300e59070b200015441c010f861910030300f058100d55041101c179049520b0b01401000455a080020480c28800000c400c801c419003000107100200d101c00c5070380e03011a583c048a0085d44048e02100a0082c06940d0013062075038000700001400131404540ca95070030f0360036039860305414042103080c10180403600500c140100a200b045002500c902c4040381c214400403c1d1a010107455512034018003426041480028404501c407190000300d0080260042440610360010480c80030104440c00001046032034182c000d0f000702031080d29a08012641a6080058424130704034102d144008000d480f080c840e02c51050800c0c0d002018140d12031841070b220300502c0c10302062000709c045400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 834171555 1250 834170305 834170317
    0x1506030117011508100605040c050301050910240813031d030f0d030b01090b1c0902040e0109050106182912010f0b130504050c0603070c021c06150b03070302 69
    0x2640d0703600b4907480c0c54192604000002d0210f13500900708140d0510340013080c1c030000d90005005a042038015031845422000b40c0e0706659054548414941e2000e102c03410b040d802d940040c4003000d401080301741c5441c80c40581e483c6401e0a45804d0240d07100d50000100700c818120003e0002100c100c91600c02050780200300001820040450b003400106482c0c00f0300b8661036003008404a40d680090040360358201c0c0e4614020600e0020460910341030544c003230b25140740c460b050348950b952481c1407021592594032a14100c200030000b040800d0445c90814005d1046008015139000034800c800007406060140c0704003d0081c42d6000100c00d48400359401d00d41c01c0703655082c2e000f0140000c00018010910500350b2000510398003013440021182407281e601e68010910100b94100b100300408101d000030000d47c862400e407003540e40c036640d0f1081122046e5100c00025131061f401005141c0d1028000f402600c480c0c0200320070892089030f68855501c00955206403001060144002201e440c0264082c0c05 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 834172661 1106 834171555 834171599
    0x1c0e0105070c0510140c070501020c0d03021005130213060e06400e1b040212040f1a1810050c040b030c0903030307120515060301 57
    0x95010500943d030051403224140042c142c8070b0140058000f000000320380c0c44103d102001d07a101c0c9840e20449006105404c00b18015141241c1c0690485615030000e02013182d480b04003002510b0028410303d510a55500b500f00580c0314200c0f0a00602100880001c3c80c90924200c213040c0c00303016003810b0040c5130584204c6100c1c40003080a2620038030310f200301c2c00100450a4500d03100d25a0103c40380907181030108a01031254000f0b60300c000000424581d04501d04201c09000c02c81c01407100380d00d90755400c0310104d03012404600c0405619400303601d42c861100340410541c00d818000392407204096001c0402030b04204028040400003001001e0140042e04081401054500660149405d00f490001c04204e010702000101c602c1020060292510ba1514a2010b4415a400010f501f00a0300b406d001400e240c00c040200f410514000b001e55080d0303403d14041d28550520b03a62508 = true := by decide +kernel

theorem cover : BRFrame.Cov 833992805 834172661 := by
  have h0 := BRFrame.cov_init 833992805
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833992805 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 833992805 ≤ n) (h2 : n < 834172661) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
