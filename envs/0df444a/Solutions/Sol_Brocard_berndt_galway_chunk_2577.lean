-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2577
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:07:54.666429+00:00
-- url     : https://prove2.me/submissions/b52f52ba-0523-4cc6-ada7-e076af29c7fa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 463309352 ≤ n < 463489208 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 463310602 1250 463309352 463309361
    0x308091801091a040506012c030a120e0a05010905061c15140303090117040302030d0603060203150409050c150f0d020304050f061e04030c05060f0a060801060b04120c210303 76
    0x8013480349207010300b0b22000e0ba8024480014a1002c0130034030040c00103e006910289560301031320380d010301908604c81c04004c0d2401000080700540c0e15115074511258062040403212030040e240400e0f0900c20a0000d80390150142400800e4400c1c07001c0c00b1401500f03040c098402990b0049030040e03141d50240421490950850280141500118204110000002d013a0142810b0402c09610801d0102e82454070034030456041c0b40703001406011540e500d10741180254021250668110b45000e000855464070340284110150842e00074143c42248504006085030203c61020051070b08005450358078114038090900914203078001038507450315042a030b0405800d5800c0341000e0700b10f03000704a44001d100d841010119000c0240d1603d40d581d9203001d80d00b640700c1000213003691041e1030811030b4900d02e0440c1d20344502800102401041d41e16415a802e99086011710341c0483e40a000900052141070300c03402000740522454054103980c0e81510304500412045640301c050307000d81c08410725826008 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 463311852 1250 463310602 463310651
    0x6020d030227060d0e1b030d0c030302090604030215030906010b281b0b0103051614040f0b0d112e0c0309270c050c0601030809180109 59
    0x8066103000c44102c1d000b4104008a08225050b84012039900c40e25150035081d9162a01030320b408000100794030201a82e510030300d00b80d043c00300418051440882c00c010070203a000c4011503c41c3d22041016540660294008405950700220140000000750351245482c01083d256600c100d507490506241c10750821605810400d0b049004100001501ca10006588142003c402c40760010780543c0034103c420440072a0b01200d5800d44540c41828400051021350403240301e041250304030105001d01c103014000c02d1048045600b00c2d2194000c0e1810241c00100b00113a0b82e4200040300100c8100250a6074482442074031314084062007102207062956203900150844110151041e184142040078559034403d0f100170480f413945207000700760080e00da800c0902409103010035000250000c0180d640030000c3c6504031036044c4995a100309008c0c804907224103840314040d0038181e09585817200d0680c44501ca8a07000100c0000c400c14a40100340050f0103041e03110000310315800e01d6012900341d4002541d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 463313102 1250 463311852 463311857
    0x90516080706050703020c1e01021011041707080d020d09120b010b1305060f0703020c04050103020f0909030c010f0c0f0e0f0d020d060c08071106070f0c0503090d060606020d 76
    0x30300c840400000c803070040b14040c0c9000e503642d52407468201d0509044004007034204555501c0200d00613441120001e140c2020390880b02406000c550307000035214030500301c8604101c204811310040d20b07000721410300301002008035580326540e10050361801c061018190010303040803004098250b84030404100601905004c1880b846450b11038480c1c100d010710400748501d20000e08022001ca518291000801c001440300780c4410701c03980c3c0700701d440d400f16504074010301840c00c040c0410301d01441440e0590780c01815001030003a1040c144214150060402000c0744418015a40424024010b15108800e0080046581c050a140291000b01ca40f0f0303250040c04140d0203101c2c2541c803240c4801031110000c580c035075650240703400850034103400f10101400180c180251181955003200b0002e004071441d5403014041d0380ca0400e007a0319800143d8031313000045c10f1007601140702031107909d840c4641801075046d00d00e8090301000080045400e01e8080703440a803503490400034960140f02000c0d0410090 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 463314352 1250 463313102 463313143
    0x8060426030603120d230603011103010305100504081306020d110d12050717040c051801030503031302270f09030c0c120708120d05070e030307030f031b030905 70
    0xa0380044c4c0c503407a1446580003500b50224116000e22942d411406402884045801c1a80d0807020451101001180c5e4503000e03609041d40b1500d0280c07050700702c0c0c2c1200d402c000581030091003604114082c0c000170f8801d03a1950303000e0121050100842000400802c0c807500203000c0307548840d60151030700144484002d080c0d04441140c150941e0044402c14a0395103613180080ca55881d150103a405027111b062000c0d0071220709040104002e10004008151038007100c0b004d10701d020031000c02103005000d01000707181d504140003240101c21111024010507100424050008404011401c0310707401e2101c1a40c0d00c1907048050140141840c850141c120448401a6281400c0c1d041790302d45c1c807440c0d52142401110010f404404110301809030350081c04410040d43d07111070070084c8110403500003a8110111a25142c04a200c075405a4030810003900050050360034020b031614142c2d00f00041f000304205040d00c4090b0340000d4844641041031500898800250601c450704001e880c064849071480f0140040 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 463315602 1250 463314352 463314361
    0x20d060b010216080a030e2d01180b090a080a051207030509150304020f060306101209060501170c0402090a0306020c01060b04080d0206060d0804030818041a040b10120905070806042603 81
    0x48041910b00c40c4000301e0b0480b42300d10142d0040301c40a0813078040524446440b5404984455000c1c014501c1c18400ca44128403140c95150060701d031a11004002c085911a481c00300003000244044d0100c80d000b814031300e0420f007000300810032244c003201c11840440c07070010070442145071070600140c641609545407030861820001144408910511070024000c01c0b80354184841d959820854070302c1e0b4000130510165035200c4a80038441791154803581240116401c0140070300341482612001540200649e071918a5500c40c40025840704c00c084130325540f42c100c04200d03000d8040041004052034401086107050803080241050380240407203109407641e647e0a40811390724400d0300c0c25030707400c000100c0e07841e06005140140d810401b030540780c02c641007092004803040d01e2241810700080c1920148108040701e000c229607000aa0044008543c0148144101580503070004001c0c51160084480083e103d41046190110032541100c00b544e07010091341010030038040d0f04115600c2d148845045007031 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 463316852 1250 463315602 463315639
    0x11e0503031e0702100e13050f01090c0c02040606181406030708060a030b011202041d07140d060603080316050a172206090507080a020d060b010216080a030e 69
    0x46468071800348280d04180c9030070124036400c80d078440f13a00601e907130f401100c11440a0155610028164400c1c51040e2464812101500809105407141044451142e00f4a0881f000038444214241d0400250010707600050f22184684805001540c5602d20001050107030103000700060b030003d024501070480305804685516050707d800080c5410404001c0d0b880001003804a91217510203400a40d000000044102c1c0404600101c40c0c000e5809006040c80100c0ca071320030301500b4000c086540e01c4448104075001e0f06644224401c1c8008000368021159500d40c030040d500300313800941c0d10050000c240607103170304004102c240700045403c1141c101000c0c9100548000a040064207511250308005042c2c00802602385640c00c3d100e090206107500d01d4204200207050701c0e84115142e00c20312401043e0130000042c2880e61944c000c0484511601030784c3c1d40409460b000b22143e043d072081190184154401e592204041d100c01e200401000b109414020100c900450000313028500100c0d00603e03021 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 463318102 1250 463316852 463316857
    0xc150112020109120f1b060815030a02010c02040e01021803100507080408130308070f020301061a04090905010b060313060501061d06031801022116020a1b050414011e050303 76
    0x180c0c400350444c91a0400e0400a00a022000303005040882c40000d031030303403000380c00e81d010305464481c1d07641002c607984c1c01c42030700310303120060156545907014080c8040158441c42200710114405840420b00c005647d8402d8266040781c05555141c0c46440815101414204282481254095018803d03824800d002a081d4000500701034062280010090100742418275000015a40100403640d01c0d003070b50070510103029030050103e01c0b80d401c0030000500d40340024071101000002d4001d5618251428920368011f04035100700305c49031b54849183e03824903940d502c0130b07500c0351207100700210f440307051071801504862051700b221040c8400c0c04252040e290801c00078174010841078606656903240c0d0101e400c941c04103042050a01d6000155038101044d204035005024100401458402d444075210700005140641c030b903500607171010741c1e584007081c0c2020744a082038072945403500000b52500013040640303040801c10821003a001004018000205500d20b407002d82401c0c519904c1404d03c1e0000340c5170f1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 463319352 1250 463318102 463318109
    0x10030e0c180c0706020702031005180115141c0b010303081012060c05090a03141509030f031f090204180e100f0f02180a1d0103060c0903080c150112020109 68
    0x214045146000c210304e07a411165419001002c0b1651020032100f040301403c000c0740c02e221100c5040003c50b101c540c05004d107001800d00d00310280445410029100c40c1074801600583d88003410346000c50b405031040341e0510b8404e02462034103900e9070450038050510030018180111501040c3d00c100200c00c0b1040425881075800f4002040e02d9203400c8080301c01e80940c41809600036508000081040609c8444ca40740040320710a940c4e5008031001e0071284214110340c5800f958008114104400c8000001150300036005040c0780b6400d141c0038002c08070b1002580151001d980e00150a0048001000c02e42074508002001401440f40b44002c2580b103000c0603511844044c4c1b07a020311046085a1342110220f4109007100310b44406141841c2160344102180c601c0c050b801301c40000c20008070001100d41843c442000b4010306034a90b580301c0d801800c03d03100e13100c104810034401000003140030000700500c0c0406802420181c0c24540d0b258002a41039100045d502c900d482c0c80c00041c0d8204810200300e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 463320602 1250 463319352 463319371
    0x109020304021203132601020a090303090801020903030334030209180c16030e030a05011b0e06070b1b0a030507080718030b1005031603110901031a0403020c10030e0c18 74
    0x421014801c1169441b2550300c02d04010b50010880d0f0011947c4400f040d000c50b8040d0b03581407245960f944001d400c03481148051901900208006000c2e004030019865545840d0a07140b030a040f00310700601e58110303016020000081d00081e02200380c1c50003002c3c60648051200350304640f41441c00f4601c0c0180320f0780c1a100c008514101624040c103024580d90803030100c02509886807040079281507402031a5a84100c0600b003c90010310414a100d100641c6800c1c602815040c5414a6130b1078588035008010250062180c100c0c4c0904000b80d00c640140080c00300e19107010410341042513016043c00d07401000c041c02c100c00030419189822000c070301c06003100c0d00941005419110070694802e003981c640c1003640c0500c108024246d001d04281400c4040320f02507000d024403070f00b6410402c40c02e05000c0c40b002d82195849008180628000d45885070418840d004551521a200d80820340038505080c0c4c1c240070075a02d80da01c06a10700c09011421400908a031819402c030b208512021440c000035241b41300 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 463321852 1250 463320602 463320629
    0x6130b010207030209010609030204050f010f030311160e22081b0115061707260601050d0911030d0c0213110403081c0605010c12030b01090e010902030402120313 71
    0x2241d00902c00000510b40140c42000c441d0303154003003e04294294881280518507002c005007580c4018510641a1041403000e040580e05d151421510001c0f502d42d552014003940c450381000c0d90042800d0402000c3d280b1210030320b40381c1504440c4042c100c6c00320440c11035905868000009841c001240c4002035034901c0f0365000640880d0840c0180300c4001c10159000005d840458040c0e08002c0441d20500c3c0c0f00301281003691000303412034413024001d003c14601e8201031885241c00310154000d540c0288180360850408040c10302030000e6841854003500d400403845000500d07401d003800040b240741d0342070800240c1c8600e00d038003084204d0040080c650089664407030001b80c800010301110700842d040380c030359a1a440c2180360000760180452401600901d0400001011f5024130410304070690003c00b001071501d400740d0154050a080a06581080340740d160101d89400e454900c54060310b0303c01c5005880c0c0c5094030500103044c0442240881301d81c024031564400e80a102a404195000c1d01010301 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 463323102 1250 463321852 463321871
    0xe0a2703120e03041d270a03360806060d21030617030c24070e130f090b220f02060d09030206091006060e0f031c051b060613 55
    0xa042d0b00990b0800e0300441020040040900460765032a4020707031903140d00d2040010700c030400700f400c00b601b40c0b03010110350042e00d0590042030042404250064002075405110707240c0300581649050103142450051100c44000e100d014010080c1c55480001074610001c035000c1f03a04d803030008800d1500e031440c8898403c80301c200910721903002200144041c00c5021030b0b015110540c161a600281140b0085114019141801c00c0d450619560040c484410f800e69907110404100c611034201c1c010181c0250343c140301016032503424803409815000440000440003028582171781e20003800b4040131407143c900750015070143c02410400110a40c000400f043d00e070518408076200b40030b2140ba18150034a414082400d1540104101d803044440d0350640d034100c0c400282c18411100c0340d010f240c0002e00e001300c8140c640d081c104522114880000d0484118108500f89200c0c03522010b004480000c01c0415440301c0403041c540c40c1d001030b002d400301418080ca040c3c0007003403031280301c0c9050280c11070311210b092 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 463324352 1250 463323102 463323131
    0x923040605032b2c01020a02090a0213120302030a0f03110706050601030509121b1c09050a30030c14070602190c0506090a0e0a270312 59
    0xc8024000602a2510f81c1e20b1940d0240078500780030719401c901d2020280c8081d00300c2c41403410207102440c40d00c0340d0081c106101429600c2c00310b180301140c190f2141503404030260356070800d0103200d444003050259448041c2d100e250020314841c0e0104100d2042d4101070310000350081f054424001c0340b0314020340c42c0800d084044018006854000e4019240020300b041801502d401c010322a0200380c07020310040c1c80c2d00381c01c181e03102c03c86031442c9042d42d0b0a1084100418a190844842040b00700c02c5075600d0030f000c015045002e0340d0b0018100803403041041000030703043c0401c10800900c80c20082e1589200001d0000e0a4400101d0510034184000d44100381014043d91104511780e03041000030841d98180700103295209228010000076201d80d403442d03103c4205035046d0f14213081e0b002c504151101d00c0d040c00d00c81d950b0802440d095101607807010205500d025406a0351061001c2240030400103010420404845a42c02c018400d4542e11090800031030b4011f8030106d403681d040440001e10701d141c032420 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 463325602 1250 463324352 463324361
    0xc020109020619140c070f150c14120c0102030405070510020604080a0c0f12021614130e250506040b120c04050a06051b03091f020309040603050616092304 68
    0x119010130000328820b62200c3d80068940d040d291303030f40381244500b030300c8081e0a00312855403d29500041e400b0000040001d1034040c600e8031483c0c0d0f0701c088581203804400300c8906500410144070403070f07502104000500404001381401043c054920129202407508000d46805002b44042c2002070000384c0c440380d2521602282880c1c907041140c00f54005030314541030000460410207400184114000301a210405511410440d01e070304103003c400007107140901180003080361419854658488004c0c0002c681405400c00c404015169082c3d8042c940b0068814003140ba00981c0c0160400c2c8014004048880100c4000c070f440d0341e00d49a5241d03074201d822441c2d84a00e422042d0030140e80100000c842e81c014002d4000702c0c840b552040781c00071f100c1410f19a00d0007492400c682c04080030080c02c8d48104003446280c0038400510640c3d20f4a200000400e0070765040e07920485050384400100b10514044040500aa000300d150150680d03141850b06042020303200c15020000005005680065607280e11 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 463326852 1250 463325602 463325627
    0x903060705090a0509070302030925050d1a010e011508060a0302010c1106270d03090605031f030b07020c0102010501030b01170a0c06051c0509100b0409150c02010c020109020619 78
    0x3985d0442d10300001c3c0240650410794500031207105a601c0800e4105144842130704011058941c282c4251400080240500c030b030300c400307440c6803013090020a0301005550f01c2d01e01800d02009070701d81952601540605c1d40030550b86c0b40080006840038440715076151640c02048903024a0200b034880d4a81c1820708a194a400398247e00c0a00010510341c0c0d084601840324841001d010940e4401180310244919070000e0b003401400158142818815140164080c6801007101d50211421038003c29515002034400c3d041500c0384440718040104690781040310310342c0c8120a10080c052540b4550741e4041501c010301910f0410122200446035001080241071145a00905030282483d40c49170003800e20b9101c0c685021f16a07070b0744460361294010500031036010b0002d030b60007481d9803802200c06000610303e00f07142951150311440d0042c04101c41a007040180c0d45807201c00120f800c960400030342100c0000c0101c9040d039041551050141e580e110a542003980361006c0c6101081039403004440301c421040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 463328102 1250 463326852 463326859
    0x803160e1905014d030c0a020f01050c0c0f13021902060106021c0318140d030b0a031a06030102120c0c01050a38060d0e0607050903060705090a05 64
    0x2944101c00300d2000d04021600c0a0703d03903421040301401c3c130121070003820049251075060b9400c40030400611058040d00f40034a50a00c26407151150401030661380403005169665000c0c402c0001980741044400c0c8005009080251802411000c10742d256045800d1480c07154a1000080300151242c4541400359014044115901c4c5000c10762a003441407010075800041c032038200045607140c000144c1004510f45d8a01100a40001c402d04030041c103000310030287c40c7c202d075000d001c0004201d04406080507075500c3c090703d05030452fa03100a00715000b43d02101d00c0317079007800020404039140c650546030040502c80180140c9e0b90f40c0780420b02902c80c030300b600074018004408024480c0d8a95018203c000c5141c0024009526403014020580f900d0b141c005844022070403440c14000b29224814112462072111000d40c400d030040010925000b2801e0030a140f5201c81c4002c441d0401070140603400909400c185052011000c0444e64a170802003002c8240000010f40d54855680c03110500020080107 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 463329352 1250 463328102 463328119
    0xd020f0a0f0e0a060b070515060109092a1e080a09021c0605130c0b0714070605130b1809100503070306020a02100507080a1104080f0309130203040803160e 68
    0x801c40b011444000710798a40c0354500e0108041900d450103801c580006403c2070081a078414882500080700c1d0014007264148139003210001a85080d5008040e1a11100d908080500f501c586892800c02c40000380c101c100070801410300380015100c04e005000300300f2403410b0940799443c01c50440090543d000065800f145035040302071068240034030042d190344544418440d40d10341881d52207002d204103900030701c903001c40d501c24000e0300260380c05803802c28060303d60400403490b00c503031081c01c10540b504035200007074002500c2071041d100c00d172101005141c22160503180c0540792a0701d4801e05d0500c002103109112090100700d202c0c0c2c16030361850180600409640c000da90b00c3c0340c00c2d802940960321070700140c055105000140c10315071080c21b100b5071680e19400910368500b41400300800c00900c0d468885c81d4207210110f0510b0080221179601c441160045a41d8202042005030401d01c019402e810280100200000500c059054940102d021858996448480c42c1c0039101100c1400e00f243d04000203 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 463330602 1250 463329352 463329359
    0x91805040201120213061d0d1b06050304110919230f06010c020f130e07080601150c0609020a03080a090302090c07080304080a0c051603030e0603060d020f0a0f 70
    0x564045801036200b621240500f02c240b08012059018a80105140448040301004480c0c0a03101c0c01d08400410303250b40d0b8081c0051130000b800064007900130f6030b4014001240c0703800403020305000b0001d02200d05003642580b605541301c202440389000302c1401840740c00b020822030101c8030082d104d9102014006d010044a0401046e03046401020410000c800c400120702c00f2410510b40328020aca0603503c1c01e03913030f000580a0001e03030780680c80074941050120710b03254584501c901c2600e42d1443c058020b40440303481e0100d018609601a040508500d081902e0303c0107140c0c12000c0032605a50180010400d41c1d0140001000c54655602c042d01c01000090307100b512075840820b50080d41d2080b50740b2401134842403060039650150240092180d40100b000c900032032541006842001550320340f5403004421a038480703003000048409840d4210302d030340301401015084407606032684801d460040c2540740030f000264411035207a0000e070050340a61142c3c22981c490034000c0001d821507854004140c1e0780c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 463331852 1250 463330602 463330649
    0x160c03050601090506030c0a0b09011805120a05010f0c0206071404092406031a01050924071509030f030c03060e070c030e030601030b19140a0603050c03070501120b0109 74
    0x10071035a00d44a80200511f550f801e01d40810528184c0d40682ca440781007041600064402000c034004a1040001170040003820366510581400303503040890242582c0400c1785001070964100d1480114041d040c000d520180c903900280c0241d01078060324000d00d00c40f0300402228281c0c0f24607004098494101000c82070240e10030101d100300d50b1150110a070380302c0d6482030100c0231102d07030a0f8480c0e980a0b40340061244d940c4140c0150040503001403c82003034025611205004081848200c0e182d14404a080d40038400310062940d1301440c241828440201079a4000704503031716001e801000d1554481c2d100100070700c01d60002e000390100301190303c10790030292070180110a40d09803c030006825512000d040342008104541200d6000400d20115114543c05100c03120b540c2a91507142a07444110f400a00301030141103024a21045000591a045003080c504001110403414061380c0312041c1004140d9010070150180e0b1148103000404200c3d000040758480025844440b042c2d0107080d070104d5010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 463333102 1250 463331852 463331861
    0x70203070e1602060405031803030d02030a0501030311030c030909090109050a0b1006090b0403030c0219030b040b150f090a060302030f010c02190f11010c0b0a0902010306060c08160c0305060109 85
    0xe40b00a02140d40500c64822a9075002c1100c0041c41504180301a100c4c070030700a1040b141da010003c050f20309103003003600d01900700d81003290f502d40f030709456100402c145038010100c01c03107800920010714034040100225503500e102c0d10b40d0444c050b00e9803000040d0703080401e41c000400590f1000c20b40c0ca00801e6800e1560503003e080d40c0102c1849d45114001905d14020f0751140c08645205046501345031035510306480075011034200743d800100b8518a0344018118620100240d8424001ca0256052504008440c440020b261b04026141544280b64665621101c80d10b81c42c1c04440880c250354401200304003900701c40c0c4c0025014031801d82100440340b010740204141424903402c0310f40501c140300001040c100101e4014103079a102d968103c001c20600d14548003014418103001d2240600c1e937480c00c0301da490864540203219038a2000b00111740c2c1c1402140b00038041c44c68000707050f80c000e440300c403c207106030310320804502c00e040080020820b01c20b080d5002503070000182c849640c1c1d01c8030400040c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 463334352 1250 463333102 463333111
    0xa050607060c02010506180f090724030609110909090c04140a05060d0f120311030703020a02060906060a091e230603031201090b040f0204060e0406050d12080c070203070e 75
    0x65003020009005030804030510187d04c040146406041e03110340200410001021f0140c8030580158080441c07400303001c404100003003450b90805c1407010800c2034003c0c122441c0e81c01603503065043c580b840b900f0003480000d45064090481d508581902e8440741c0c80d103040c00c8001410b030028100800c846180c000360784140d09ca000717204001d202c42e60b10341d010441c80c0664420014915180c110001010804c40005440c9141407800c000902e5400011108480c0d00201c81c40c00009400160030310200e43c1c1400215000503682c8001c102c60b0900e140081c48001d03190140000c084d907615441c1903400c920860358401c2c1c04002d80c00b0045c041100d51440c82820054180081c14241000440e003607080000403034004d4800042907400350390a006c010b902414558850541c002c2e20ad52100d5010002d03032009000800803600c4840140c00b00e1020302c8140d420a07800070b40304401c10410302e00071820b000d00051202410b8034142d141030ba20848460340034040d0f81000ba42501c00c2220104030035121141c414041c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 463335602 1250 463334352 463334357
    0x3060501080d11070501210605041802040c0809030417011104061106091b010305280f1d070b0c160803071703101a0906070510111303110a050607060c 66
    0x607145058002a5201d589111740c0780000c281100c505000c0030521100300f04640c0e5a5000310f41e440d03803440014280c40c15150004c0703891141c4034059003146171506c00c652a110311420041450b00d0700d60f981580b280560302c42c2110200c13000c030140220b4682940310072809a00c907a020354890f600c400c0d00809500004000c80c240b8450a400f00f404840005203081c00111085102041d0000360001140174000c0a07003042c0d100802c603001d02820b91030b070301d15860b103100300c0c80c40c006406c01003401c40c0c1007a9a00b00f01c5900140204903500c0d1540c0e0000f040b5001910300324008680e0724a04150320a180945003c1078510081c10b0550204032110040700810076a0b0080b82140760068424442e102140b00c295a5404040802c0e14200f06600c1c2140c10820510340988469003021800c0d00841c032260b000d484121015002070251165112a40c030640381c001c1407450002d41004008110f44c1850806404081c1c06c3c00c2214000301d0003682d0380401c0c8070203044094080b030f03200c4285103090701c040c00e100c8090001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 463336852 1250 463335602 463335617
    0x3060b010c050c21010c021f18020d081603050c070b0414040506040204080111070b1b0406081f08010207060b0108060307051c080a0206012108040506030a0603060501080d 75
    0x22503100e203201c11401a0404054002000e083c020000d03015052003120600e45011400e10030400001c1c81880c11040403900034258501d01e0001c120081440400a506007a107403030760408d10050b1062882c0550341d816252984108803505000790715001e2014881851441700b044c090401d58030002600c4884c038450b0840b500349890f0340441119003d070740624080c005040481070b0740f6141c40e030011600f10101070b20040c5442d40310903d483c01e4441c6c40e40ca0000704480043c0340303c208242151202e40c80541c1d181100c00b040e69262036005584240e2003000700b0004c01e6004100310070018141480010120401140095038441015000c0d402940007903c00c5440c0105a0200d9401015141e104250040142000302c0c24075041121034528a0500701c04d0000c00322090300002d84100c0108007143c5190006c155641c0741070084010074404039000007400441c4924030001807918020b45050701c4089a525840781d0303400d080c7c00c00400d1180d00c09084242014000240d10102044549154400760703500748 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 463338102 1250 463336852 463336871
    0x812040312051204060b040e101401050625140a0f150504050d050708040b04030b0108121305010e0f0a0b030615090f1c0b04150e0a0c0e100b12010306 66
    0xc4081c001c9260340703d08841c40e500040c002803d030342c0c4192600b08008000042c04004418101d00d480c3c851030704011460307036030301c0c01070f00030b0900c640c0c0140180412a541882c1540185109400310024041a0030070754600c5030ba00104102c604414004292030303c200c03224580c460034445108035011000b9200810b54480c11501203490b405500e12485d0002c0040241d4801d04c0d90031071f8982d100820030303241d0400511000c50740c0705030940104020350060311488001e50600035503d01303180d210b105c0c0c18840d001c1040268401100d003000842207540908140c20108024000b00e9460b10140300200d9014100420104a020b50720010318000c1c501550072700d56184403000408214440c058071103500800b0340b02044001c1c9007000705854152a541e005141c100c0e13140ea680c0c07000c0c030000d0354200d40d080e00c078105c01d566080c4c0c984112143e20080d90014444d05099486905c02c04005009446000300384c90002018250403003010750041900392429aa01c1030f2006035405400000e0000f100c45600340940074 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 463339352 1250 463338102 463338107
    0x20d05090d02060402090702070801051305010b0109060e090c070209042102030c1c0201060b0406050c06100e0a1d03070506060f0102070609060c03090306050c0a080105040e03091302040812040312 86
    0x7140c185410740007014a510340b03800304500581d000b00300004521440700042881d640c2801220b015988100e8400440c0070145032181c20340d414040c081d410480516800c1008a070b201040c1c10404c0d1041e10b0110040e150b00740c40000078403940c80081d400c10044020301041200e03014004c4100400138406609104608000301c0c1c0740d02c80d06287c001c0990100102c070003d400c1c08400700b80e030b031011030000142e455610031185000d40c00550081c0081500400c80c64400e0409220b1241d011080ba00c3c0e00f00b40604100b00740f0710520001d404080017640d91003901e4088100355061280c052210401c0300d85490981c9010303030742c911085401c030340a1986e286104000754000a03201003568107a440341501c1c1810410100c03140b85d00c0e404182c0070004950000404107125200380360048845002844e5150504a8080d00d500c5042c3d000c103006500e001c50740300b1000d03404000e54460b600103c4240d607042c0c400b0b1f03440c1000380c0526002031140e80581d0315040903034034001001b00b04a13840f0700d08581c061030601206 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 463340602 1250 463339352 463339363
    0x909010303172208220f06080603060115050711130902040b031513173403140d0207080d050708150a0b030703150b04080106050a03050307060216080706020d0509 71
    0x12039105a1103d00600000b40c402d40240840c0c100b40c100080c0001e405200101d0000745941c04a50291041e42d030910440340d2040010398000703010340c000d01040d45850005880700031110b9901c0c04108000c601c6404010403400020192200100491b142c6070071341941000038141000c08900c078903d8070843d5042e0782408112240d6100381c2181801c0560759182c1000e66450080904480d20300c0489851985a017841016005d241c03000162480e200d5410301001d44070711062040c0d04108403040c19a040001e078404c061503e681c5040700b01a0b11184030b200b44c0b00203405064001440d41d1000300710030b80410f80315409180b05080c00da54041484d03c40d115040e07024210080c0054208011309403e00402c4204001990042c01d01c2c900001c540400e850910f03e00691500104503d400000d006c00c01d8070801d02640001d0403045a9140c90a803659403201d5a0348030340d01c4024500c81d000300b9180000305461007031245103904000b446035075503a986000740c001c1d4409418000114a4a008103802c1c1800242 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 463341852 1250 463340602 463340641
    0x4050d331401050f10021203070807030e06090616020a02060d0209031e030f092205060906030f1b010509033007050c040510050a030804030501050c12011406090901030317 75
    0x40b4044c1414504140a50040c07200445010f500c610501c0045800e2100003c5210b5140c0d80d840d0300322404c002c00c0c000c00b0fa6400f0a141c100d10303400407060020b954404204590091860901c16400c0146814260700b425401d01c4003961040000c00d90381e000401e56001801090000c03016124003c406412002c1019003040c004800d640c0140030140c01400018000c000d140c034000d00581202c4401d03c010b10710610b1404182c16801e03118004e008031030a208145c5c54000c5c408401400280400b0b1081030796a5600412440708120b180d11114050b9028a040358209040502910242040302c0c0540d0a04a03003c050460701c0619244101040514031040e14101d562110240c014403e00c02c04000c081e200180c07034051001c20b60440016503541b15001c1100840c42070301c0054950707203582855400c580303005083c1c000043c41004802c141c1c410840100f410760b0020b14450721a5600603007c11100e0041895803a0444080d07000402450f4000d0002c00322a80b10400c001516607a15813854141d50a084 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 463343102 1250 463341852 463341859
    0x60b01031b080a090209090c18090c011d030d020d0f02030f0d09170c010e160e070807090905100923060d02040f1109010f020c01020304050d33140105 66
    0x50528800c1e5215560454020191850101c1c44013590340000e104104199650600e65204801618060a002004060046801c180850b6030b01e0b1a007810b50f00d80d842c0d800b103e03040140b100300880144040b0503c507090000d02404036519a4124000a543da0690711031280214020341c0ca201106480002280c4040106041032410a5010000700001c2e01d00180c0c11198451500300707008518001d240540549141100042140d10028225909011f01e0310725503080c0c0c040c2d00c501440441ca502000c640c0020300c81c50201926507980d0001c8684049a400140401c1d00b4031051000c06d400c1140220191603d00311704000268080c20b60038a03143c400c0d80c1c0784542c0c040da0380025101c0d14002211408540c0058004074500c6c44216881080f00d10381b15041d2070912010400001550380100c2c0c0d881440d0707850004089090b0355500103582c0e8022881a5482008499100c408220640315622506c412224509101948444103207109503003904a06100d0361414440b450220000725140e03040361b1020713 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 463344352 1250 463343102 463343141
    0x10f050d080c0a151a06030f01050108061c0b01060e040203100510020a0212060a0b0603090a1502070b0709090f0606080606090301140705030610030c05090906040e0a03020307060b0103 81
    0x15a64501c407900520012a498000e81030050082281c1c0109001d0003000d400300081e4160342800b070380360380754188510a8058103003403040003080381d000714645042d10313000d003002c5c0074a0b41e4070400503825403012100b2032400d08001204c00100001030050301d042c1c0301161a01d2a00a14030001d1008a0008a885140c0e2000c0e03d502003183c0c2c1000e5000540c10766151041d5080a411900885c00a5211400507107181d480346007000780344400c0f841030010708501180c606256082c41748615540b401c1300d10014143c00d03402024a1014561039040310041984554055458501100050200401c0e0702c5500615420020081100d058500c81c00d415100982c58140094841e42c0c144a0650000d142c12600756680c0c50070b200c0000582c0c821b5620401c400d0b0740e426903e24210041c02500464854840d041c54104020030f0180c940140980d860004190707400041980c5030b000240140c800301407041b249000e0090044107040e408002484980c1c0241c1d410b102018400004400710303000303030b5040451032245 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 463345602 1250 463344352 463344379
    0x2060a030b030c030304080f0613151e0515040509160b030606040801051006030c0e060708031003080408010c080129030903040e0c0a020c01030c1e11030a0c020306010f05 75
    0x3030790040301d5024001c1d048034800c0b1004070110346564010740221800c2d60114081d000c950600300000d070303885400b0016a4041c0c400341d58500345685070f4002d01c07000d11601d170402410904902c4504260388102510248140e0034070f64108030454106080030390289003400c00180c04c51301c000448884402a80040076a03a80c504400d0800c5500003420707456008030100310005c2e00950900642d80900c0044540501e15890302c0b802404a416140007101030040c2c80d800c0502503a5000107031528035400a400c02c0d900d903200c01d21001c01000b19000288000d801060100752008158002561600c49403201e04c0966261554108500b55448013282e8112400000800c1340000002968001c41003908a070b00f06074542d43d047c4c3c060311040310903110341c6a0210707107803042c554104503c00345481c0a0070100240788092100400e15844a0402c001f401010032014480f2481030346088048030040050320f46901d1144402882d41907000402e034403034031400300045100c198521414044070001450024034030392 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 463346852 1250 463345602 463345607
    0x190209070c03050705150f01150f030f09021002031b0c090c0c10140604060e0613150801151a0c1c0c0206120703050c04030512071b090516080402060a 66
    0x10400803020801c3c280103c07070000d0001c2154080241e80d10040c24031602e041c100724800160305a11045000c21401e0348100c11300c0d0003441d10054000c0c24038004c41c0b50071071521900c0190480b0314000350812092015551416408005044c0da4174449002c3c0e01c1000044d03001960f100d42c0d442400d40d0000821000c00d0b00c05119030020142240b49209a614034801d00345494100c480c2c00e15101d502c144404104140f61426100c0c000c050301c1c00500145407410b004c1c000c103005100b044200205103070b0303860b0000c6c4ea10141c0508400140300d1000284a41c0114810b8a88400380c1480f40c8205108450108011304043d0000c1d80c100c800008010301c001c1ea4191002400d90745034807192024083d00e48031010150320f94200030311002d100015003180318140788000500715032004040324a9001c00744800c0c80041c40c0850034048540d030481925407580c80b80d0038050702e059880505409082c4561400286070301042e00424820300300382c0b410350001d41e4800e006031000710040318000e511030710400c1106402d60 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 463348102 1250 463346852 463346867
    0x181207050609040b150406090911030f040b04230102040906080606091f0b04090b13050108030a0503090726060f010b03040b13020402031801050619150216030b06010219020907 77
    0x1c401805c0d8100080308001500391548076420810024106980030701c0031340e26600a5218000039001003526515000309542e48411018100a001d1000140401d09000c4041503c41c5c2c1e16481e501622203d511a41e01a0300075801071146171030107800c00500003400040425010300c502d602401c1da0310f0603510080120b201500702101c034680f4a000100c08124656600060006440c000d00c001900304421010005800000b5a0b4018160304107030040c401c910303000c419900c0f2540542030450326a1265141e260418045030481c0e041d0608904ca61021401d01c0320140704480e0102041d5416511843c4403640e0310142409040c2c1a84420008140019150304281e0f03484203031010004141c9007036070f0006080ea80280c0c2d5103081d5118003180031801c04000e00c1440e40000b0100c807d15940f080002001d000d6032064840c1a40912050342d0400d4094024401684004a072681c10744405880786820f951200c42526040d0061240d520405503c130701d9000f141200607001400c45004d50782d040030865002 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 463349352 1250 463348102 463348121
    0x2a0708031b160606031505091b060405041404120302090306040f14010f05100b0c0c010c022b0b09011514010c02120f0607210b120318120705060904 65
    0x564040003400c000d0410080c44403603151044038041003852031030130b00e529020310346c1903007030001842e00c0e06024003c400000c0030050000e40d0411010080030074400503555004592010741c000b03060031085580500c0e4103544a201d0751245110489200029404804a0090001954065108001180100312030001ca078960a10400a54245401215a0a0940b09a20b0f4480c3e42d594a41041c0b15105030228403042c0644540d070f07880c609002c401c484143d80c0d080703034014186c10303c80d0300c1c00d00600703648800c11503507049000c02c200e01d0120861140c040c146500303200000e48003010300d540415801c0106010f5520268a0141d0041d500342c04d0070568042d03603040c0f401081c144959011083c0050310759100c81c00d03201102c03c0c054014011500c029900b4044002c0c031100c02c0052a001c98203d40b070704c81c0d0100c458031100002c00030700110340700089420242403800e409218400070510504004a2050316014500207507051100004040c802a90303504403401015400841800444990f0034035901c400d04a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 463350602 1250 463349352 463349401
    0x30c03140a051f2a1d0105070204020d09020306090a02040b0d020127090e100c050f19090b0d0b0f0108070c170405061201030611132106052a070803 65
    0x1364294101c40c0000e46910520540301c000300250003c00b56a0801c11602c0f1410b9a0b081d0a44407200b5840020514807800800a20450340440c103080f40c6d1189901403201164054101d5000c3c0c00c10301c604c180c2e90908120120700c10383c00c00300c7d942d0940c02c11b000304203c85070b410384900401e100810a0300458120060a00060038546c07140090072000c07070f004005010648402071b00452002600010554148907920402d21070108600c60390140f049045400d000b50008110024054a00b41124590204d90048030365050104160040a90580c440b0301071850446005080b4030700c42c0700549040c18102c0314040440d10030511200403481d00c0600c04046004550101d2034142c640c1c0004045400142a00823480342160043c400c001080c800c3c400100e01c001c200e903040c110100b10107041140217015101010010b2900760000f0751044104c11403845d84601c0611080c03616881300d4072002c12500003c030903403c03442000c0d015410042d013100c0704079400414451941d503e1034260490201010058120b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 463351852 1250 463350602 463350611
    0x26040b04110315180c15070b1b19050405060f09040e0a03140a020a0b040308010e0a0501030f080a0203090a0e090106050d0818062811031305090c0d06030c03140a051f 73
    0x1081e640c0c0c4841e0b40b14403021a07015510391741d83e414078201236000101104c06000d0070405041c3c90018203030a070341801c15049060f001c0b600060704103c3d10340c0101da10060304010041151016039115001404481d002581e0404c40b83c1480c1034900d945544240c0050080740f456605261340c0e180032801010011040d0040711002c103a02c0d9039002484104450960000e08030100501000030002e03049a04186c1611041c4869411511680009070950400601e031000004580140f10b0003032003a110310807001821041c0341c90751070f061140c00c4481102d00c01001d500c1d104020070302d4905124070130111604000814104209092550062510540e116500071004e100ba04002e4265400717809070b256000c8810001c61610b044040e0004400903200700954109000c2c650890054054420842e80100d134110220307103c10002d40340a11940d4112440346d42028008000d214964480307408607403181e00645112129501450380b500f203081002801604103040b0000f054500107a01942301092071400078 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 463353102 1250 463351852 463351873
    0x3051305120703031506080610030f0f0b0411121501090e0910060b070b07030f0204080a06021e070c0306020f090a080c01090902031626040b0411031518 67
    0x145812505079401d080310600003400800c00da414056100418264141e188400e0305051029040f008002d01141c050368849010740da0492181e040f890030640600381c1000120704038035500001c0d1042c88211405070741410f15105007107850a048920b03903008240b55400c41d4a0701c446291802c42841e071554104003c1103c0400d5400da104021801811400c0c01000d00c82d07100b04411042e40d10a0b480546a0ba001307104c41c201240c04038103496400005e5180015040e1401003188000340204e80102c0300360710a0001b241c00300020b65005040300c001450141100016a0711100054232600f1002413802c00050300410001c0e00341d4018080c9480141541c41c00d2402010208106200a034010030302903001b41d255200a5810001c140007506c000c080070362035440c0c2648114030002050b0204e4007080b01d25841c207030b40d0744010918402583c0c418032041140d4182030405100c9600c0c07c0d18203a50079000c1280248148c50002000c0d20b0040c03142646612135030381c004640e0010502c41d615041203005810f2401c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 463354352 1250 463353102 463353113
    0xc10020307080a050105040207080a031503082b180f05070302060d02190e030d0c0c1203050c0d020a0b01120f0204110a02010e03030402031b1801061d04020306090106030513 76
    0xe41c8036044550360030000740340103944007043d1001070303201c2402548100032070000704982030100e5240d4000e074103002c1000740041c0c1d800e0014070903650018000a10100745500e0b504468542d40329288403241c0550103103180081c034181160400c02c482040321407000240d10000d080c82684040450199054602c12641d980100c0d40c40e51198400040195000602e86201d2489950440362045d0b145040c02c4040849404a660345207210a59014400c5a410000800c4043d80580014002070548a8036560013850050000d400422801c040741c0504070307116184130b20000301d41d03442540004100d4107507403800b40e01e02d08825801c0301c1561036030401c110310000750701d507802504038646d81c0c8124580c2c0ca1689000c000d085070405c0c0b54844103600200300b8000035a400144c9152210160322414103403917134103000a600c50855410074050882d459000141c07158100d007074402c0c0f804090300310040900540d010401240300c1103840950100a00005004440c03003540002c2c0d0107140d8550031140004036441c0e0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 463355602 1250 463354352 463354357
    0x7080915090c0406091e0f020d1404050601060807020703030e010e040e06040209060f180603250302010e0405010303050a0e03030c070b131d0403080601020a170904110301050102070504020c1002 85
    0x103401d07154071900040c242e07814588a010000c0046000070010000000310101d044064108006c8019883d40c0c00b00110950365030440d824031401c00c0b401c00070901c03511418840d001013101c00f911180251030000541c0e6020364459441003202e81d0182c501c9a055031b8090703503440d0800d8002410060111717421400c58456204052080859100a29041c50503104001c2c00d000011300315030140400703c5140341c2c55112403c2c6584068410302030000103a0b02e14021900c0d03d0403102802e40c00504c2c10480404901401c0404800d0307130f000382d132a423409107652000e10050b0344081c4801800240d00b0840800994401c01c4a10600360004080c0c070704e48001112060318100c004d801c601610000001d03615191040007441500904420011404000704a0311100816000070b20143c1408507020005d9200da1082c020b0301c0780181d00100b9040751000d40c140031045900590000d40c01280390a8180c1c116007010070690341210340503030003842c1c11810311043c800030f50428100d103045407103040540c03040050540003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 463356852 1250 463355602 463355611
    0x105013e01050901150602033f0a140f15010905090109060e060a0b04060521130302010b09060a170a060203090616031401050d0f050607022d0607080915 67
    0x30910f42400c1880c01d00310340000e260407000d8000c60104005594002c004d40701c1b500c503608100c220302d50045120160220300c083c030010b2120307003940410145200000d1418000c49004808200005400310718034920340080e9000028100b5080020f1211b00014034200c80c001c2c0103240c001d440a039900d01103400ca050030780018440380d4a8074000d0001036102102d0740d511220460788144540e00e809d44a070050300c11405910200080024203d1294541915215556958084d00c001900d016070b800050080c00d040102e0055082014010300f902d07048282900900e4001e060401075468405030681c00c98011120403502d0082c440d640c4007080a9101940c80303410301001802e0686002911043d42d1b00c82400400141413511110101e01e201da0905541590003d99407040d02e03001d03a08250141062525000700710f84aa101003102040e4080780c07040303650324100b419555900c0d04070003581e80c0500b4440303804103552112001070318907840744d1140342e000b010031b40598507030901c03006648541480848 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 463358102 1250 463356852 463356977
    0x161e02070501141c111903150909171c09061d0706050307031d0a0501090c1a0711010905180108150603060411012c0306010608010501 59
    0xda0810040d6000314000d0355010150511624011603151103182d03d41ea055422441540c1c2d600c10031000004103000c655580401c0c0245005c002402c90000b4040c2803000305062401c003030b003040041d48200c1c074041c0640c05ea5000010700502c0380d6210255035240c00000c40e00101c00b0f4000c500441001d0b00f03108001d030860140d08041034031b4041604800400c400384e070700c403190365002c0c01c03040211035481005c0d1390f04900a46404070740000d41c290300301044440e82412646c14001c1c2507202080001c15800b404041d8803840000c502035a40e0301e0382105070b040640300304110305420050140042da800420310103a5405040c001c6e04a0785407004100000c090303400100c03e00d05040300601205101300100c100380301d00f0035490f9100380781000120352142d0f005400103281e0045261900c070207038050407905100d82001c1000c010f51400111005541100101080f0b01a020f41c0d070012a1440c1316880c11030503036106031a100028060f15074010012030300110b186941000d105030304070b408552088506029020301 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 463359352 1250 463358102 463358113
    0x13030809100216060809070e07170a020f04060819060e010e0c040f0611070905070906030b060703080105150910030e0f06010e070f0905040e0f071a03161e02 69
    0x2241482004145203401200b558080c0d03042d5640d07a0101c3d003030703038060314910315201080703480f03012841c0c2ca406e99907040744c1e010301c10100c204854198403101e8a148a0503a007500200f0b17443d00c40401d000ca00c83d61003003200c3c2910401c024408140a40100c90300807864610780110604e81668500441c0c1542d00400c1050700c6450040013207009140100c0d03001808654502e1a017031800d070600d0f10500341d91107100f05010b401c07000044c0e17680b024080100106981c8406100c0c510b007102000304940418003441020903e4004800e809040c2075080d104d84981c10340745d04120b0390905c4204040d82c1c1b0741c00c4008500352000c019400c00d94580c0908036501c808a82c03070100d101c41b000c00e200780c20700784822100702e1f16a01210042000103299403d007a04001542000382c0c04540c1d84404454002d019040550402d00744104003519240010b0440501c0c1c040340c0036102460740f00e4151440d80c0010702d004810301c01040c00801c1c851000e01001548508440c20075151481131040c1c220300c0b00900075440000758014 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 463360602 1250 463359352 463359367
    0x1b0f130305100c082202040b010315080606121506150c032b090510050702011401030c0e070207141905030d03090c080114040b060102010e030309060907060e061c02130308 75
    0x114404c1900318410b8140713001a00d80c0803104815003001d03040040d10598803040c42483ca07074029400030380e00c40c00b840b905180241c0c90b1800140d0f12103050790511300441500301c1c02c00b40c012010911815040a00780c8a04864594900f007007150016080004a0382104000100e82282d0400090a0300d422070850b014042508a80310311402d9110a0303000c10040c1890050f034001800440d0014640030441000182515143c42c12801090010542e1401030b510500110900c89014610021103225106201096a910004a88134405403142d519407041d031282d007403141d2a00703031034442c4d100020300e80c0400c4060b52000041e152010b8240c642000ca07548100c0310341446041c2d02240041c00124009000d032415000310300c094040014400340628802c02d000c921160710039040310b9420903512040700d0300c03400c001e07a113251100000d4881507403920842c280010381d180900c94500d07a10000401d001c0c101032080100d403442181444030f484100e40d0801c44e07442c1c2c2102c81b1015002540c000d004184c0c480a0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 463361852 1250 463360602 463360607
    0xd0609050f101b0915080709080d05070501570815040c02210c0102030f070e04050610050d0618020d1503020607020d0501090501020d02121b0f130305100c 68
    0x3d0006005007008041c5905000807001203084401035502d614050b040380c2d981d45400c0780c1440b1307070b500007004034020410040e840e42d80c001c001e429101e0154000f080520045038400d01421108040240d40c80144e0100410051540310403801c90749484010141e076a980c0090814096407400960020070301c0c52040c4141208803100030030b03030700c90180c0d0204005040c511000e551007800480c2c14002803040912084008080701c1503684040800e4025900c130300340800480c800704412102400000d02600d0140c05034500380c0112402020080c1583e541740c401c120f0122015800030303030900c2100392590800140c1c0c8045e004010802c0c2c45914005031034500004142c42078888034103c42602404c04c00040c405070361740100b2a0107203641141c1115041e03281d85403c9000d0807840e080500b0a510206000441005580060400b40309141b10544181e480017281110348a50070360140384203009000100180f08072100809804040300b1543c0001c0d0b60380d5950600d00000080c4502d4080d8490000018954 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 463363102 1250 463361852 463361891
    0x110724140403030e1608031e0d02030103030e13151701090f0b091509060601230d0506130507200c030313150c031706060d0203092a0d0609050f10 64
    0x1401175040c0d4041d20b044810780e56130040c0740b00c1c00e2410080100e0003501038080000c9400d20b80e41e580c1c044d0746135030b0350381070152082d01e00e04609405502d00100304061001c140c4174145c00e80811240c02003006007040200040308001d281007142035941d03100d500380881d40003c44042ca95101d0200142145811640f81e07083c480c120401010404280c814040759070004074031a44c1c03000082c03801704190480f1140310700c1000b62002030a42459030000d60303c2c3d040c9601d60006440381c00159442d1070749020321078500c01250011107202001864000d4695a10b003294801400d8200062040710460042500080e045a000b01c82440360300302e44503410004142c94801d00886040c59051440d400e40a64802500d40d140c1404200a4113103035000003101551100b0585203000b0340400119180d14040c4000f503518620041070104810250050790101c1580c5030702c00c3c21884003d08102a424015a55030010b4444207800f10b5440c0511640c09410340400c00c1401d44c900025480499800042c0344801d82e203c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 463364352 1250 463363102 463363123
    0x170d020f070303080c0702150a020309010e01081306111306080a0605030c010206070c03021603050a0510020405210c040212010e1006050708090310020406090603110724140403030e 79
    0x107402a100400c00720381c00510450303000c0921900c2c42d07915070a80c030028214061101204041f004c01151458200381c2c0080030f011030035400e032a082500d0401400564007110103c6da1100e800c000301c51980e0024103690852070a0740c190203002c40c140309d020b40580303002001c039401c4140098000b90401c51300303143c10300a0340700403c2e00f078000d8480c10b10000300003519441c004000320240014041e48008041c800c000d04101410b1444e0040d08140d140d1411a844144a40301580c0912070f100701d20b000d00c00613100325000c88400400c0340c041d50603400c0301c2d0348540d455a481c24003a801110300032644c030b46070390008040c160001d480000c484d60500c811100d0008000e03142c442001c4a0780010701145030042c044030400c540014109464400f1140000d04c0c00500d02410f00e40140080340004855801c0200c0c40107496032520240040c0c03c1000300620b13940603400014041c0c2400e0750b642c8040040e42514007880d205900e0022071503100c0c1205140b60a4410340381107000a94034001c0c0001c0510610400c00107 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 463365602 1250 463364352 463364383
    0x70507020f042310030209010b0f090312070b100e01051e0301050a0e0d020303090c0402071e06020307200d050306030a0b271c0f0e09090c0f010c0c030803040c170d02 73
    0x22815500421f100794014011701040220014000e2190328510059030685603000b402c8601000c0301492030040358000b1f950440f02c0210b480e010890100c000043c02e000e6170720610317070712201e0fa203030a08008940a030341c0901d442d240c4840e140710310700b92000c2c0261486402e80326404108400052104d6141c6030b0b0b810b44080c00c40d0000d01c240245d5480228462408a83c01c42e0056201c09042c24401c41d144145400c4c4c505a01d500f014240070845a90080c601c02c0645445914455a6000036840441031032140d400694000800d0002114000c070080c6421040280c1200c81e212016a110404198141d1b51f40c400c4048000c6018516480c406a40300d1038814080603103140300c0c022170007100c102c0e54080e102c4140b112400030b00c2100d500c0340c24000040d0100512003101400d00c45400e5455045040d20240200580c1c0d6644c1e40075401014000c413069409080c40e0441459900c2c4e5100c00d4002030421100205100000600c44401400e00410b454844001e041d5a090701c032307030203450450f0030702c40b0055 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 463366852 1250 463365602 463365631
    0x90c090103030e090c0904050f0a051003020609090c16060605042304060f2301260703060b27060102011d070315020c070f1d0f070507020f0423 63
    0xd0344200e40e0003c07200705a6001a00f51038040c1e60341518000d1846154106140c5030411800c0800505114080d0360304580c1042561208a406904241030b4000a0740000c400c01003203280f414040003d41d03200085400305401c0c81911001585007448010301074601544952081c400f91915104100303000c00c081c800c00c559108030144601d1412070080020b0312040d81c840c004040ca088640040c0407000e07603c081c6440840039007004c0e02c0703191020700a11905141031000710340850f40d04000100c14840c540000c20296195551b040094a0f9a40140390808241c00855851080d00040d103050012009041c107001d180c00c10009085031005c8070821481c01c094070450b80210008114401900e401c44e1040b45802c05003440307032000c1d1107100c024030054031440703c0026100096120103020380d001081401c41c19040b400c950b0b000504240d9501e100c8072351141c0402d40c01405a00101000c1e0b10240898188a030345ca00002c0444452509a02d000441420100d45982c400042603511a440e4480c002 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 463368102 1250 463366852 463366859
    0x207081b01090302011209080a030609050c09010c020607110a12031b240902090a0207120c030512090c12060601111c0e0a08030313020411270a1805090c0901 69
    0x30314034407143c4400707814016000340c80e0300c0c500342d550005140c0f2a0001a019559010000300800503c5248100c2e0b954034544004581c000b182c00c070440e580d05405170368440d10f21030160200545540300d05000ca400c254002180a8941c030340955000041099451181ccc103903000d41005417148111280070418201d01181c0c0700001642c1c901d01d03103010410fa0941c0c031240d0f6588800800113120066005c1c1d8020360183c00c02c440f01344107400802c5100d220381542c00c0100100d88060707800c0c10b44100300034041041840300740405034074a10110b80c0701d210401116403c10360700c00412001031406400070310980114040000a503081884c0501b541e1a0100911046442039814120002c6c6000100e007040360600c064819903880e450160050049a4207407550390408280701d0b1040c81380420200d00031814000d400c800114000140e071140300090602109048902108084140340c0043c015400583d282c408500090106070020321100000f00004035800d0121081e40388c031080c20940b070302c40c006010041c0b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 463369352 1250 463368102 463368107
    0x619080f060d03081b13080703050705100e06030a0b040c030b01031503030507080c0c030f0106030b062b021f030b1c03090605030c190203090906091005060d0603020406060207081b01 80
    0xb9070054001d1503654440140748100460382c030600907802c1640150749804148030b01f010551004a078031035030403541a10754800501401100c45200070010490b0f006421540c1c0c14424001c0d5405203441c02c0c000350000550f00000c044030b02c11250040029035070b40d19a8800d5030148505d10300b0250481420b814140b4603a0010312034070507410002d000160219560401d110f0800050101c003c0003016150041c40c03020300e017030080c9075522080d9400040280400e0450400c10034060118281078501c00c6e2542c081c04d020300658081c0c00080740c00a503203c046551112800075040f40c03101d82582c2c003040b00f1200404102007801000401000f150008030014006a006100141150b1290610549940e15484000050300400d00d00c075640042016074103407410b5022005000da80c00071039440f07100d51524403e020f600481141c62071a283c091420600162a103400903020343c03054013038089400d41d102d6020170180c901d26071241000d03a0065805002c500f170280008050501c02c641c0c403003a00190003000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 463370602 1250 463369352 463369367
    0xb0306160e121c0f0914090402010905090a0b030601090b060a0804031701060509120c0a2904061e1106010b09130c09060315050604140619080f060d03 66
    0x3400621000e903100034030a850b80c0c0051200e81d40c41c0e4043da0440f00100b0000d00b82034191401d0280050500c880e44581180079400708015120388a600f405240400001e00c0503124006d001a8144042c086000540390f860b0142c1d40d02c90145005c0109042440009240c50183d041e003100d000e2178103200010409449400c2a110361030380300d00d001c41050300c55003400d9400d9802242032104940341c00d000450001d801600400c0030040940300040d0641c0a000d086880b400d41c81992503112345040301c02c00501101070f4480d140d00550030741c0046800044030110000b6409640b148003c142850760303404400d48842041d903c24205418490060a021884c15464010500400d46896000300750780c111501d03551004040080c03002c404004d80c040c3c1810180552400e403086000082c104414090124101010701d4202c500180c02c450030581040b007110041c03403800c16102d4001c00700b8861036a04c00c54a42d0000088003840c5c4407070207107003054524040304070360017051280501c0b43d08041d200040c0e40283c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 463371852 1250 463370602 463370641
    0x10321081504090c03120215070503060a1502030c010e010e01050f01030807020d03170a1a010201020c1b180a05060a090c20030405030a0308090d0e06030a020f070609150b0306 77
    0x40c00110700c0f50b01e18007952403418542003d4403072001002c05010031500002c0a192408103809418030302c2c3e0310304e80100d40e584000c4882c0c98004280e540308010350010401103000c03400850040c3c4e82000386501d80c43d07003101c40d030246c006000da45840c5814414082071080540001c00e02404050319070640c0c90b4940c2510850400a010f1074072440c000003454810b030860140708001094161250412040341d0780a080030780c0c9500d0005114041c070710a02d45c014401c54a204600002500d401000d000c64500050304480c40241c00401124441c2c024540300c09a05100d00e501c001c00294600704001400310500142e003018069510b440691128113402642c080b0310948182a07015040d0794101e0340f5030a500480e2300c26601403080c25141000c25400c080c3c1a40b0030340c1c409088801603161080200c9140c100d080e0030a801210400101c4c4004085800a004284200d00c0c1c161601c80b035603880c842150030310403041d2000001d034000c4801e030340c04034000e079000c03958203c000b41030604011019500200c1d4085 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 463373102 1250 463371852 463371859
    0x606040e0a02090a1e06020d1209020f09090d09080d120507030b0a14030606030a0c0b0703023a0903020906040b0f04091406130503030612030d050103210815 69
    0x100151020745181c0403284003c0d8050031101d09242c0c0c13403152071a8001184440142802c1100340852002c0c40010421000f0b24595643d42c0d08460041e490001040c2003801aa042056030050500d19220034403140c2c002d641550003015a1011080010300d011540e400c0348078950000c01c44150007550080343e841100b2000b0200140d591504201030b0700a0000030840ba80000c46d0000018900800501c1682816400d03010340b0500d0703451804040d1146071000e0001c1c82400034546c20300804142402601c1618424011621180c16003480401c4007420400c1c40e10004407403220724010781314500e4502101034a50b0504220f0036003180e000880b0743c41c0007008070380103507070320a0400c15035038940070000700020000c1d204116080c61410000f20b04003d59070510078138851a40420300390b2561190301404682c01201850441c1c407100208529140300440d0190320f44010302000c01000e1b104d100f02c40c0258465100c1d0011381001207448403440e51442110824005420304128802e210382d0545003c040046 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 463374352 1250 463373102 463373129
    0x60e0310020c10141b070b04060e030f040e160305040510050621070f0e2203031b090602010f0c0c06020c07030f061a061c0c1b06020d0507020303060604 67
    0x14915074a0308107149070440c0103600745030030360782804c9400c0d0a06010740a0007112a142280070000740040b40310714403000b41001c21003800100815020390008900141800a40385002c0e0001c00c2400c01e80c026030090303440c400b150340500941c00485c640380c0300d598040303080501030b80c5041d445260f202c807078083c40040c101c0c1c0c40303400064540d0f0303c00141c0e8008101c442540b104c0600010070381d41d5a610345005510f207030503a07000041b80001100440d5481424540340d01c3c480b00a084101801c8040c8011080303080c141c8603440106171041c0c500c0c4250000e0200d690b490352040c509400207003034590440e50100c659140c889030b818081d901a201244041c2c01c03c80250b034468070ac0740194508001580003070100440211090304000e4031f42c0080d4055921004210b044032040f1040101e544102034172220314115070341f259500500345400010150300c090a2461b40f144524480c0408103540410403942c1d240d001651078401003042c418141c02c513180e80300445c250700d00440800c2640c45503000d9029540a907 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 463375602 1250 463374352 463374367
    0x1090e0712080304230106170d0908030319060b0c0a0b070f020c010c02060d0203070207091104060f08060a030503030a140906010b03131e080d0c0c02010e0d0804121b060e031002 78
    0x8003042e03030503001703001e00200003079907071202080002c081ca5001c4146a00039100b070503107143d02c00c00300c08050305c80c410080e41c91601c50010310b5840b000a45403e00c1c0303a80d00d03204000f488405040180003a9030305040546003412192810b001c048000410b0081407005031440341d0007480c0e0000724503880c15403e00388040040024000a0024094110710301b0700a8000800c010002c0d5001c1800421206810020300c07545102a00b08509400385002e1540081c14032111211014401c00300140c1210006e0301d003030a0243c4035155541554000c640a989039516070200400504548456a034050b9401c400707440c0550500b041a000303403001810301d200c0040107a43c04404d006c103003160010409d040844045030352000d850405025002000e0242c007051a058409000c030f4010024a02e90560580d40d5035000c9a15004008592110250698031340100380f2001c201d2032420200d905040d400340510000225480f207400d41c481030560040e03010011030001271049a100041c031003529907000900035172a10740 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 463376852 1250 463375602 463375643
    0x5190905180f33041416121e0209040f06030b1506041203080603160609050108010905100302040f0f0f1413050604032d0c0b07090f090509010209060301090e0712080304 74
    0x601703038400003403264020600c0b021200c0942102e140c2d5a0585680c204414580121000c84a480c84440c10080e19010318001c940310343d9000700340034a0000e100282088040400760121070864108403030311406c036001d0110b800354244215a00c11411140d46107014204481c00c0700301e64150800400340032141022031415541801181d651415051101c980d00d030f0b44150052040100d441018081000301c000418408901d000c0c152003600592100600c4c6c0c0d10319404c0c40001d05100c550603411030381e1008a034803141c100c5c2c010000581056074001c107000d42c46580b1020841009480b00802000380d089032800110302040c4541e200e40c05042c910003018008900002005105031211040b4910050940d103050700a00d044030814001c2c03001d0182691007010644841c2514082e0b0595006410010019040307681c200c10762264065002508000001c0041029504207811400741e058640210101d60603080120340b0041074501f480e0086007986403240c40172840090070180000c03400a80b12088a90b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 463378102 1250 463376852 463376861
    0x80312040f05030f070204110412020d05010e010608011506030603050a150b04020409090b070216230405040302070801050603121c110a02010209040e0d05190905180f3304 75
    0x25044402c3c0e0343e5480180c4d0b01c2c070600d42e2012000300e10032403404910406c6006098107403015034803600403c50807078509408000c05407500d91400c40356503403907010001801d0303c01e004400003099010000308965000300034505880c0340d540c000c1d50400d4070b4228204042440010f494100c4e0350009203080c1c00400110138880505030903003c1e40c1d0894000200083d0001c040d510001415018000e481c100791102107040713803503100783c1030380c40960020803605010b40b040c15001c098070280d4990010010059800206044c1c0710125410f83c0941c00005040200368401e0080c40d07070003072088028240710040c0c00e0071000c041c01232400100a640c801c100b66103075810b09500903510042d681d841d03c1e03107440204000034040c1d4060746c0e0700c50255060420404c0c0016000451120012180d03c440d4203101c1c0200000b50b048050040060400c0414400020592a40c040b0102d88540301c1098000c0d626282d165815030113030103800d0b030306001c0950000c816028100340002e0384100b030740601000b0001a040024000c1c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 463379352 1250 463378102 463378133
    0x1e040c0e07080a150303020726010c0216060f052709042603010b0910170108010c09140d0206030601032018012c0a0305060f0603120408031204 63
    0x90324900030311414075048522284207014020051000702800744031502460341d07500c0000d015900080090008030710b42c400711000355448108003500008080c90003070070b440035111030030050707006044440c01d00148091b0342c1001e000c440c2400d4484582e00040107102e4030804955001080740708281c190340070200c1c0c0f55018074142c002d103447d2141c102402d000c6039080102142c203e0000c01203440030303400c0424400707aa049a00c00c800f0141040f05280c00d000c0c800a8441800003007013024540304180441c620b81303881c0a803800034000100d1429421005d001c42c940c603082405034004030004008141d860304030a10300c907a8190b031216180d8503800011780240090060b213504c00d0100e4804002190f1240d0064812180d130080305640c0361805070b0040d5294142200d080301c501d000704201c0c61241c001000b81b134026500c003600940c02c0a030340352922801e12200703607400f07281e56500703005000e403a1a00b00035130018142c3c04000c541c501482d0040c0d61395280b051a9101d40300311a104001018451492a401ca18 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 463380602 1250 463379352 463379369
    0x509161418070806011e140c07030203070303030203070f2a06060b041716120b1b16020f06090a090e010209030a0b070305010902030f010e1f09060501020f01051e040c 73
    0x15814141c802030f01d0640308a48550000381c8030950403d089140b915050740a10040e11000340d03001d48250001401c0d401025038020b00d104052000005840c20441038004600903640180c903401c150400810003011013901000308a086c51402c03101c00c084008519106403514010001034103640b0740140034107050390290454003c0424000344c8440a618103d5142d403030340d425240160324064070340c94094020f0007015075000c1a4003860307001880030000c0c01d42100540880c26034240f06849886041da0010144060001640d140c500860806016000008800b2203202c0e0420b40d0f1203000c5004200a032144824840d110038144204800030740c100d81e0b8a00c000760a0b00e01b88500c5050403c424001030320f0840000340340a0002521030220300c25607008000c0c20701c505086900c0c04602c1d681c0d615001d004659040d002e034808158405454441e80c0090038442d8011030014a804000390614249481c510f43c00d07418982080702d505c4280460b4403603a10800300060103511241032598007203c0d5504040b1a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 463381852 1250 463380602 463380649
    0x905040207230304050a08030307091a040803070c140102061909020109030b0103050105190501080309010f2d020d020309300a06021312050d1b080d0b010305091614 72
    0xb1080740110080c002d4030303010765440240b43e680d64142d40c0d40380710071120000000c00d110802d2191600e200c08030354140841d12001414292a0481e0f2400d540c4440021201320000309800c00401440708080c92820307609002408507481d090300856000c540320184c1701041c40c0d0b00c0c8402c80071680a5105100a1034104410000380e60b1031b4a4814004c0200365040b0345034624210b0410601001c40c0a0075045c0c98140010758200640440195401400c8451800130310002054a82c4d41c502800360140c0c540c0c80001441e40180d0700d1000c06403c2c400701000c003d045410411000701c031500d801242004807892503500c00200400071140c00c601c00107014494200f0701440040905104098001d00607031070030010260351159491600c880507034003204c0001d015800800e100311103140602d2144660821120150001400c2076485c01d6083e401139601304011552649030340ea46507403602c540d07940480c002008105062841002d98440d8030709101c1c1046000b13407070380628040c0e1030f20f031504e20804102c001c1204 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 463383102 1250 463381852 463381913
    0x2307050d0810031a1f060c0206030a2415020d081b0c06040318150c38010306060902040806040602070f12030c081605121003320d0905040207 62
    0xd44c2813805d5034841500812008031400e540300311180001201c0f41526801c0c5804010344c01d00043d504010018003515030354051582e0300c210982c004544503040020003001883c101456002d000001d41e280c070085510000031410416003001c078054102d186201c504c0148420388143e44504c1c0701c0c0e100d40760140e0040000740802c0540011980c501d08000040d9450a03523110800c02e5036200009000000062840752100041041c5904143c2005070441c81d1500000d20700c190301e0f80000b0541072050f00e240b00c002c010024030582d0b2054802030320341080150b280a02d044007d540e20301c0c016102808195000030054100300381d041c244a04d607075201d034140384039011002d000760081c44c1c20b9003d4404603115000160558103034000c00c0e4030032841ca4840c5420200300804052030041e00a020000d80c014400c004008a514090810042c42c51b6080503e83c00024800d204500500042103072030319440403005580c1283c1009034041a140c0c251001070f110002801c00300c02c2d070203149082040c044070701300580 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 463384352 1250 463383102 463383143
    0xf0406060504081507050f03090a0804060215090607170702031c05150103050405030d0e160b0a09060c02090408030606130612230c03040206040f062307050d081003 72
    0xc1084812a03004e60b040309000d0406820002d80c22110700380020820041c401d488111a4051504440c0e9035044410807030060340c2d100d46d0350380543c000b01c2c013680c4001c40c804101255616070b146d110080d100546100e04040501400002084c04124240c102000000d0000f40c07081050319101c0741c204a04440c82918449850001d001c140c9e01c900c13240e004031000c2481e95029010351805513601c24011071070100d60041d4140100309418215800b40951145c03400c0c02c5480b1040503025090700d0880c10f03641c02842101401da26260b42c0b104040c018000002d00142c1c4c5c0c3c121800381e0003030300a0f01c811368907554200056102e2050300c1d2800c42060f8a004045041540711580e40304504e0b81c0341c0100017002c00f0004240d02d4592080241c00b605086100140d071503480d94010315003091015114a05054a80708400e2002045030401c00c002000100401495924400583d03d819410a08545007440c1d544403181c841404000c008284410782020540802100f10715800031a00712840040091080d25030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 463385602 1250 463384352 463384357
    0x5041112010209150a0903050a0c06270623070506070815060d0902011815080c0304050d0f2007030b010f0f0e0a02041d06090903041505090f04060605 66
    0x814040c008000c0c0d00103868405108640c0c101400408540c16071030400b90f200d6099000285410410015602c0000051002c07c00300500600c980e8042503a94280f030700090a82c1903101c01058031034003802020344038400441c0460700b529128903145c0d4a241825400c4899410001e440b03103200d61002640a050081c04640e9602404643d681d01101e611107500b4074032142c2040483c01c0c3c3c070070020440e10103014115131012100314410f052080c0d8094002c50710385204040b42c0c0c409002e1a0113001c648880c0c60340700c8030302c550024081d00180d00b1400e06454050b514502483c000082c0030442003103002031401818241c1c501201004004621491142c2c01c40d04c41109210854403420058008151001144052815101241001a0300501e4461148074104c0060b1000c00565400c1201241d8600b00720fa218032140070030b1154514a080c4070090000028000f000000940c0050005124003815400c15140401751860030540740c145141c00540000c0b281c0359802e5001d843d002c0009510b58001c400b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 463386852 1250 463385602 463385633
    0x30309060b0108090c0f030a1a041218050f030a02060c0106080f0309030a0201051303151a0a2702120f0108100902030a06020304051603210c0c0302010807120504 71
    0xc06105207140d500064900b00340c04d6803040030076000100015920304084129120280d4000c0440350015a107803200070030491640460740764500c1940400090203041d040603080b80300103107010316450360311240a6522601e5806094070030030840000400caa5010412018400d8005005035664592640701c6402080d203032184045500400e075100385000000b105031510410003802600b1852401d41c01119603a00c0070140f201d6104006c000403010641e0f002d940441d4143c1268001154001103549108200c1c1e81800365214581048003401542c0320740010080c4501d00601240d085011036240401074081d050300d403214503c1a000704408047c0c621611412126075105070b8048080d0058450141d9214501c00707034040e4803405c00d01c40001c280358001e5078030a00810599030150240c010704441341c20644d02c00d480c00c840c0c6c4200c606600d034401101100c580c45034104130b11070350400c7d59100c944008a11000c1c2c1800310800006082902a2585820211641804000503d00751030310000e2040d188070b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 463388102 1250 463386852 463386863
    0x11202030c03010516020c030304050607062c0307060f0e0d05162a05030a110f040615080a050a1a040207111809010510080c0f01030b0d030801080609060c19020c060403030309 77
    0x245607e000341804011201500c0f070240565281840b175403500c2c1c0207003401c0304100c5840303100010b2040c02d10603041d0700d107080c0341c032500042d555565a0f82414010b40d07000103c1020b0643c900000a54941800a1511140211402c1842e11390449410b8a08285441c603400780040d4248403103184125000b13403ea2081d40c9622510f00e41e1a6180d1044c580e6600718110014101a1003400868003440d0000d4a0402008001d0000c0703080c980740c48045002158400d0200b0120b02483c0c280082c0e10402d01595521406200081020740040c00d805e000321103800da0014003442d030000e869000c0c0528012060f6200310b0150116204034610b5144429a2404540c450215442d150124465100c1d0f00c3c28113003118a00d000178001708035584204540007509580440c185952002850b2460f2605101031010f180240c80700d410b03c1d0303d86000c0f2824102e000f0304014403078100404105460034004203032003c03a10039030b053310300019140c44160b10300351039918141d130310841c0454000101030f45508900e09561091 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 463389352 1250 463388102 463388113
    0x403080301170c4e1b0a0e0a0e0a030915020a030e061c15030201030f110f0705011401030f1202060c030105010c05070b22060512011202030c0301051602 67
    0x6203100d40318620f008529900984002c002c051240942640812000c01201c0300010003804c00d0150b41e144840600541034030b04140e00b601034000742400103200e400180e00c0200c0308010414006089501c041c05a2070b4204800c4000ca01b85036a00c0d03101c0120645000100da0100c181824081c28240403481035070b60301000518400702c90380c800320710500156419115030303901e291148100003803500004100781100103071040c00e0040030154007610180304104050710744828290f00005003074039401e5800c5030102e03040055410243c0440c4048885190b0105000342d111700c0300745001070161048966558803510f8a00011084c0030300c0d5028407002d03c0c41013044000a010341d680a984a0750100c81078148000c0c28001000745501600503c5030300c521500544030b1994035504c0d01070711504010001c440400044d0100603102d516018140c0103080a420700a0505c9012100340300f8152050040a0080384548800b408545040040e00030844004000307020524040d200580c5030b02c09001400d0051045 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 463390602 1250 463389352 463389389
    0x17160305031e0f090f0d0c0303030e070501081509090f010515130e0604020909150c071b080604080d0219031413031b0203210304050c040605011d0a0b0403080301 71
    0x801120804040f00b12110b00b031000010030000c00065064503c0d40025070705044200084010310b440010350710a0f18006494580b000c4424941105a0000c0c0d051007400d0302031040b90750b6011810125804115014000d90385c1e0340ca803450500c1c0104031907001c50342c240b03c240080324a010f5542d03600b500c5c0a030740d0002e000c3c040c0c080d8403055414030300c11017081e40c008001040140c100400262350104000d0f08540c00d00c010305034005110207089030000807105000c0f5145003048501c0b680d4420703400f240a8541d0b000c0b41001c0c2503a454140280006118010004100a0190b00e0b901561180d001c0d80000030121581c2c86406009003803203a6100d010810f00d8400100c08080104c49006400d0b0141d0b02c203030413101c050030605248400041c080c1d03418458000c124511210300381d6030281200001c1c10003601ea04003854290710b40a996024140f14904041c4144501e0f42e10030f140f60154481d680c1010395481c070410205508100d01e41041ca0b04540c0000d020080c0040c41c0020340c12a8120042010030700d11 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 463391852 1250 463390602 463390657
    0x12140c01051614031603060513020d0c03021e03060109030c060c0c080715110721110418231b0a0b070809060d0e0618010c11071716030503 61
    0x14000c1d61a00711a6083c00815140300c5c5041c1c9500604045081c00184070340c0702d01c0021380f0f40c81c0c01e144081c3c42580001e0891410001c90080c0743d80860581815400d0803098620f8102e45129101800c2e40c0d10b00c0403000500aa1050182074015031700450940306064480c0c0c001480007401c42000d403000d80302c008000a0a0100203031040440c1c66102005a0720b0910f120100c5004e1825200d42882d8400d042012642a0380b0608041070354803800001c9002200301e140800e41c01c0d2000f00070354459450281aa0306911102c1c01c3c4540095001c3c3c1c00c0140b180340c55440d040d03424179048040485200349000c40450000c0004003044400c402c807561030352140d80d4a10004984078003440200121000d110451941c1041006040b030308160644c0819540d105022003440c203202181d0300d154050321400d17080744904003845130210b02800e6107046581080402c00d400d5403a032540c881c500300341f000303d2598141c241d400c0c1310030162045500400424560f590801690740d41004464100c3ca40766281c01200f01e20 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 463393102 1250 463391852 463391867
    0x109050609160909090c0305030f1c090201020618010f0e06091b150f07050a2303030f0c0d06050604031b06050c0d0e041409070f120c0312140c010516 66
    0x2900b694400c0e0a443c2040346410191019400072150040b0126011000803401d1000d002000407030b5041e41d454011502050039401c0001d51200c08503407900e2140400740c0d90100d00c035a0311602007509200000c01540a241c0104140c01007240250701e002c0391900c806801095441c00b41e01c640080341c225000314660409595103070a000c9901c9150f40d0414110380c8900006000d614001210040c1840f00c5038540710300b8008003000407102d104c00303690300119070510a41c80d90428500310000f1421443c0c40b20740300c841031402808404580e00d0204c2c504850203002e810480252001900e101d885582d280342035481612160b41400c1e0a403821500862141e114401761002c2002c02d80082036400c5e06a00140c0700c000e01035421580143d191001c00c40020900740e11240a8107034003009181440c506010054000d60036001901c1d13400082c420703940410b08c00e050b041f040da500300100f81ca038100761000c1034540124040c00b80102c01400b16024066400640c8070074800c82c4c80c04610204118021000c5a0b40c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 463394352 1250 463393102 463393141
    0xc080c060c07030f0201110609062203120f06080102041d0106030903020709270323040f03020f130c120c0203090108150d05030f04062003041217030109050609 70
    0xb03510444040001c80e0000d650107443d40c2c0181482e140070b1040819244c200001114055100d52003402806201ca0445401c910240d280c2d09024a6102060f6001046c0002600812501c20384507612502c4c00b00803940540003d01844000715074440d51200c62905807011510840c001c10f03489000003a585000c0e000d05051194540e020700001800c080b4004014900f0b8441828a241c0c0c000342c178082c486241c60113a00f002e0198680f1000c8900120002c41000008003290785c4000d07081c0020031812002120090990340e0455600102c0c00c1c0fa0f10200d80383c107032101c20503040c0b14108a4a0344029802513500b20018030a9071081c40448020300059907a4490aa03840d8001220a400281440060964035080010042144481a0b440d8885900d507800135003805007995000242008081c1d044819212001d01c0030100c7d2805a0f58410029120300413881999040d101c0311815004120500c02c2d00e030440c0060a104985030b58580e0f04500c0100800c89003503008403030000110b2100700d00a010303289007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 463395602 1250 463394352 463394377
    0xe060405071a040504150305061b0d0e0a02270a05090c06030a09020909011a01020c060a0807020a0b090a02090c090d030f0507170a0305061e190803070c080c06 70
    0x102842d100c040d280c0030003055940884608140004240e507170391030140070baa9103115850f5000b19070070341c1829410040c019001e020a018000c400c1c00c824400f9805581058580c200001610070b141980388d03092289090000354400c8a801f0176110074030414600d030352103246c0700400018a540754002641110001c1d03406007084d6000038030003141031402000959000502c0c050100360340760107a0108903e0f400640740716510b40d440380000380d064491014041e94001092004110301d50903000440c10900c1184088401c00c1500c800141916000b0024103003801c3e88800c80034442e141c41c0d64081c0d100c0c0070a020803882190000045070b00c040000041d2008a1030081c80700c5000d40d010341c0d007551090b60003000003090cc42c05009020106401c08240b00c2e43e2420010440c1e991000c50b00b0060845900816880c172a010701c0000da0f21030b4107642c50b04003080d4015500f507140704010070720f04224401300c2d910101451000250f050b0130000c15407003030000c54000720101c0307040a207000200401802110940f180 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 463396852 1250 463395602 463395613
    0xf070602070b030c0c010e0a02100c0206190e030715031a060306090709090216140601030309032004060b1e0906121305011b0806010801060e040c020106170a060e060405 74
    0x24285101000f1504580e1880b00c0078644000652001c0c2542c44040e808080f5412581010095080034007085007805903c2c036102140107001e0b40052158080c034041d282508485100c07100c041c43c001d5141c4549010010111182d5640d40c21517141c1040745100c200740000d007840b12044210014a204e440820030041000341140d84c2c42c0103120344950010084420480031500c001810038991000f450b000700c80308410302e800c40c9a41440c644030010040010019400180100046903204d5040340a5a612000d502080f400010109500500300354401c0e41c03062400703400140b00028070000701080201150007280a900002e4203405a0180541603034100200f006640040034400f100158000039000c02080c0012a0340c407000d0856210110260040e0119440500d043c2c3e0001152680300c002481e102500b50f0401000400790045640e56a020b66240c0e405030030864001c0d04080c001e40f41590221504002c0303d60090784d6180151003e5910515003008000704200100340e9511880c1c00000030107 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 463398102 1250 463396852 463396859
    0x30507060905060405061c0c0c05070b0c1f09050d030c030b030a1212150902120a0504030c12170c1b03160f150908030703050c091e0a0b0301080a03020f07060207 71
    0x6c1c65074070a913030003481d6a02007070328041400454458080c0c4025036580b5030441c12814500141b03454008d4114010300300c018425441441800108e900c1141c01826000640c618002e2105010301015540203107140a0340d1521801a1341c59442030035030310034542e02441280c0c520400d06448041380d880c0602510702b8000d09000c1c0e50b0103220f01d184080340b11031001590042030740078540c400301c8a4000941303240e00000c0c60310304100c0c00280c4c5600418840d504210074203050343d0240608926810040290b1000704803420303002d0041c1c5401c0c404c03644004025440d86003007904c400c50b03540b00d4181108103030520080c040301e01100005407000c0c0d200d01549180080fa1640380d42101c0c400300b100c1143da280007c12441308000c2c1ca400703200003451283c00255120f00300700c00003500340d540060030f804000d2003c2c032200082c1d1790b03540b1580c801c0200c0300700180e800c0a051400325581c00c0c09038012003c100c2001000160a50b40044c602d05d403079020390309940000100040e100d0711029184240c1e00180d100035002e0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 463399352 1250 463398102 463398109
    0xb03070e090717100504020d02040e09062809021801290d0b0d12090501020c01052503050c03070f05120f03011e030f05010504150e0d03090507030b10030507060905060405 75
    0x140d0042c840c8129130012030740e240700103010387e0311040b00703102c526030003040410000150044190b0448280c01c0500100c0c034100080110003000c10380584d0304203846101e007446113101c940c884061a078028110003071030740200c19a10303481c2e0b1081c4590164400346208100d0002210004030012182d114003040c50008406034a0002e4990001050b500613008201d42d40010044d206a900845407a1141c041151504002a083c80099408035041c0302c0c08100341461a2022038030280d07031845180d42e0940200c0701c1c5c01e0403603e500440b9414040e5103c00110401800313001d1556001a80c8200115040794a035451808010f001c0d0100c2408034038003d00050001d0310300d41107240c0fa603000c1303016035101060345c035142d01080103400e40068466075980c1c814442401502042d000d00000001400d2110458040480da0358189142c0e88604160b036032150f100811005005800046030007200310750b058104034542400540851004a4140c803036118001200e90082c3e0258003102c400420b60340c101807505c000d1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 463400602 1250 463399352 463399397
    0x30712060e2e0518360f0706050409090615140a140105091507050a080903060a0b010914011106010306051608090601120f12080106030e03040b09041508070b03070e0907 74
    0x110300148000441400300784100c8501001c10030302111704c1603070711001d050a410050501e0480d5000d0700324031001c0c40304c190400c0898040310040b18002561140700c0c1402c1c001450849a4840a0300d81c0840004a40b40710f41100201c0e507200320b590a016a2382c5003694407550030ba6101280c00302c0c0081c0b144180d07d00e0191f03903003600689103468280c42c003691503890508107841f40340101d03a0440c011038103220608040200c1c650010030101c0401c03e08130410006005140c0301d110301c5103441c904014803480c6902c2422031803810b2881c401141c003156120720b030000140c40d003140c0c1d50114061401c8429504d5108910f83e90255884034040d049590070f02c0b041c8008510050000c3d946100001801d00c0081c0140402408644846d60f81540d00e50500c48000c003540c150b83d0f480d0340303558400d020921980e4441d9049601152048400250304d1401c07114041040c44194402700550017039440028824200074021403103400f0940d180c20940f00c3d0a02045032810003565204001400b440110105410811030f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 463401852 1250 463400602 463400611
    0xa0801050f040f021f080f01050d020312030601050c030d051e01181112240d080405040903030e030d0b0f060304050a030309020a120c050301050c0f030712060e2e0518 73
    0x7204440701d842c1c41103400071032045d500600024506904204155070300b612020301405c0300b1500c482d10f0000301c2c0c0019540e4946442103840c0074200102080281c1e00590807940003c4a02d01038a0721000903041800003020100d4840c6102c5c54a288481e140801005529050703907141d202e00f0b5108129000d440005008902250009038010070085100d12000e2130074034031420342444100c03586860360f40061394240460300307803e02a80c011404980040c0b44002614103440d020307200003a10a103542004c40103040c00c00d410032218040020104d51810164014882007001030f0380032003c0c3c2e42c4103428403002d4481101d002c0c0990300041300e01000244079070040400c03140020048406c15807552060000c07203a070300d0f90813241159881410041030800780140f640c00310440030054141540040d90301003130f00c0000c0c211010800d01c00194100c10750135600010261580d4502c2295a281104545078040c0445614440940010031014000301c2c6029561007130304d0024004400302c00c070b00c81a0a010703000140 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 463403102 1250 463401852 463401859
    0xf09080a050a02010609050103140c090c0d1503020a0e0a05091501060318020405011508100e0601110a05010c0e040b040e030a0e0a0503030d022a030f070317090c0a0801050f040f02 79
    0x45c000030380300d41540585402703980651102d17a05040c000000d94582440003180c3c2d4000c011180402842c002d8031801d40d40710001406020801d019401898090160240c0009601810100c8007080c044c0c43c0c410342c00d01c6000d010104011540b52854044d039608080d11241160680240050040c10b110b604404a440b4486010020403e4181d00040584500344c02c440745032205a000700c040c1c03d0303001400ea038000c2062180003840c18100081c0f00a00c55001300143d05000300e01d84e8241e842c0c403082054541143e0020000c00850b544404010054000044c0f064030a0742005100141446c00d84900303402440340000861400b0428002079030120417103a8040d07440806544002020b84050000349410700415500503950f0070f0030601d0251980d042a000740990f00e445007802c1d59401c2c000100e0b1010300c101d41d07a0680303408007440c1c1260b484040c0c03000e141d268028070041c03245400c00041c2d03801d031170003044621414441e256100b40e03023224000c5030040603184d40c03400420045807421000103251400036 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 463404352 1250 463403102 463403111
    0x17031b09042003070e010e030a03140c010203012301032a0c05010203010801050a0516020a030c0804050d050705030f030f190c0b0c0910080106271e03060f09080a050a0201 75
    0x11884242d1601e403200c1c00203110300c030000800055a078007084002a0080074240980301c0c042d1140420340c7c442e1a42c0009081c0b19035111302c0c040b140061826100404d440c0c500956483d81c50f141446040b0003050391044036950b00c11031844c1d03a50f0080c0243c80d8208a40090081140303202c0310000388081d2020000020300030640b954001180083c002940070f410703000c001050509001926401301d5000a000480c000305803940301c00040e82c00304030b501d1020f81500c1d041030f00301841c2c00d0004c41480745501c903541c010039540d80d800030842d012400e0811a90101c094030f52100207040095241e1041600d0071100780747c2002000090b24950000d600c400c055440c200446150907034031440c0110f0280d408840b034400200c1d21106030b2508592109441c045803070089590b51600390050302e12920040c028200241a1800f02a41d80715020801c000b00040c0c02410550181401010384c21049400240c600700c0c1000848002046d00d170040c44170b1039a021003080c0ca0506202d50072540313600009141d02c115502d6 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 463405602 1250 463404352 463404371
    0x190b0c010c0e01030b09040f03110a0c17030903100510050a090e011d0a080708040b04080307060c1b0b060f040c0c0b0906071e030204050a030602040918170a02070503010504080717031b0904 83
    0x82041007040743c814592070001c20700317280d9100054649378801703409550040106202d903032030200b81400e001604002c0419580c07201010b0042010040e00b040340c1280c1c10000014420b6030b0781c2c1298040e003088a0013009000d007410305116042401c5d100c88166584242643c000054011004001c028001c0302c3c120705140d160b101440d00f503441a07001050f1a440840c4840520030307580715070101035230a4200303009240241c60b41d80646070040000070380400124000900d05807521000c120f005140140304001c481004039015140e20300c40c0d081900d040303071100006442c251002800c40e0090b0a25111221040aa030040d0082c20f4440b1140328200340e000e0000088903210128028051482044d0142c1c46030f0610b25020b0403500c1303e007250074883c06d9400c15031000c20929a900c100311a1035000789640c52904110a0740780c05019448181c16602c1d00c0104014002400080c141c0540724102c9407108082600841c0302c42d002c19110682e0600b80700205003045080100240f4184101a0000c20108070 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 463406852 1250 463405602 463405637
    0x1a1005060a0e060d0b1003050f010612023f010803090402090d050105090a140c010e010e04060302031005040506071106070e0114210601140405190b0c010c0e01030b09040f03 76
    0x304906000c0300b0341e1290f10030340761742c0b420640104104a4030701d410005490900c910152010041c0315180034001e8070741003040b00407810340449060092204030f01d05120307080c40c0300802094880d51440380980f1101420418034006e01c00c0a4100c8002c08004c60920401c0c10410000794030000307001d6840f0140714604800190280a600d124000031030140075034a9441c109008400c10400340420a504031070701d00700440c4c0c0c01c070400c54070356102843c01c580140300035004180100b60640000c0d6052180600d650344c82d00d41600001e01c180d116a0030b540c1140c13183d10007956481c0548101880a030040c800240850303115200c121260941407402c4111400d84c8070a11503e6401254100300b01c0309480000e0b003150481d6101755820201c28607017070620801c1151000550300aa02406102e40d80384d2640320404400701c2c41080183c0070121100d81e40d2010402d00703038001c2000c00d24050100b8136216003451198001c0c4501708440c000544a9011030341c4964400a40342040a821000d100c18940c4c0e2058040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 463408102 1250 463406852 463406857
    0xa171209070602010b010e0321130902280203070602130b180a1403121c0203010f0e0709030f0204020307120e070801060b0c0706111207030c1a1005060a0e06 69
    0x1806000890b090550003400d640d11400b05c030381841074080d07071141d0680700007401509072200600351410404200004002c6442803040e254802266075002180c0b01480d0f034000d00f81d0214040401c2420420383c1c2c44141051400014000940c0007840b030344000c18466002401d0041e00c01080c0381a46442d501c1465039508040790314295040c500389000403c0c04c10744908005814000c40100588007c03500203a81c4030f1440d1a00c0000040c0450401703010380020328414002e5040c194290f449613191501005100a03e104410f1050060004201054054030f414000d80390400204420302d10140c0030b02000e580064002020884420ba914009210070322030501c8208602d00a00006071901521a0954006400503510490b0030801c801e00e41000040e01c0d42143c00300c3c01d000240300c40f4810b6960070281c8400d10341800e05000501c00f01010b9000b034225a00601c2400041002c0100300c0f0011500307041101d540c0d101ca42c092406100314500034002d0708807010fa52902086004103031001c1400b54 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 463409352 1250 463408102 463408111
    0x2607050a0c020d12030f0506090a020c0c0a03030c0302070902030f0408090d0c090204050a060318030e0109170303040c0b0a0906030e0118110f1804031b1b081002040303020a1712 78
    0x480740c07071a0704c103296916018541440449410501070350600c1030001c0c0550707c02420b18198240e00040d690b0003840284403840c030040d0000c0000030320303039588e040c042c000b2400084118014041c0710f8001c6003140c003520950b40521558407041080341d4071540e903640b0306c0d071150003456031241d1904042c4c40001e880d12003400181c070006501503101c51038101030088840c411b41201d0281804e01c003419034000260000d624127143c051800c1040d0034405001601c200300030760081c454000f030442c81c40c051104008015405070748610803107082503640e0a141c04650103401c02e20f10004140c8081001520700c25000300c9403841b007103000080c0b4002441c0520800b00c00b19001103070f504e0701c1c81015445906d0030400c001c000b0b181c1903032203507110503040c00410140e600040c0010284125002c24240115030300e4100b41d6440c1e0710140c62103043c8503099a0000c015010300c80c00744544650120001c1d07040050081d24110780e4540c00070120300c04150354034cc002a200ba0754542070220309003c85400c4a0740c40d54594040e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 463410602 1250 463409352 463409363
    0x5070201170a09060b180a0f0219020a030210060501021f0f0e1534170c07060b0a1206110919061d090a0504052b2607050a0c020d 57
    0x741e0322850704c84161125010140e05c5865441b1524101070f808006a07035003c9800d40b0006000103016500900030b00030034000c100d0b180803141000101035000115500e1036402602240c10881d000c3d08501e0aa42d01c500407940141c000788415028a41602900c20390812003040210714113030030029480445200d040c02c1282c40c1c0c0b20b4103900340024191000c143e0803001c12080d011200c074000f0607002c62881840c00015a034068400c207501c146228285c10190603103006d54075a041e052018041c021038104107411340d070351843e1058660491514030000422541c40c04c0b200180c200341a15240000e00c0b03840200138171704ac0104001d20881c2d6402950002082461a0030400c640c1409402424030708100c16030740810302c4140b00854103545130380b01e481d44000d144101040d50344d40c1e481c21908280302c1e41d690796010403130b480c2000c0540c00035501d18504049681d54032844240e0721145c2103d50111140e900c2c141450780c902149000d4030420042c10b0082090800460b900c00c26400704401740800041601c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 463411852 1250 463410602 463410611
    0xc0f2d0204150f03080a020a020d08270310020c1203010603050103051606020c151e0301060f2c0d05030a0503010e012403320a05070f0e0105070201170a 67
    0xc515042c070901d07901c2c0c071200c070340c00c000a0f00300040143c90200c14040600001008101c041e50130344208005141d495016140c20f0b00c00c0341c2860310025a0b00600080f0b5002031b0002500d801c0b011540d809500b104000070000d1070001210011140254408503ca0f01d15004040c0c0d503070040c20815005500901c61072343e00149940c5142403490030301d500324003c820b1007a030130b01003001410350000d405030f003a0310112105034030144c2e50b12004a0318440d10048171481d00d507035203d0b8450b081228001e541241d101e91243c000c0c41494643c03c540c0108e0020440703450500020001805921a10b00d450304090043c010808040c9107440c0e081c55604158400b40005e8800030040c019180232690050052001004060f1898451040f64020601410010042540e00d480d84031011680c00848a03000e00e01445e0490505000ae04201200700201e501c0c10040c0d04203400314642c548600b0314645100d44656031000012501e800444d11070f030141005038100100c171241d8054030f02800c84014021026a000000c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 463413102 1250 463411852 463411943
    0xb03010525081003200d03020c011116090c03022106040b0d05031c021e0702040b010504150c05150a050f07020706020c0409050a050a2405070c0f 64
    0x2101c004484058a08019110061005640008071044182c2c2d034021481030104021403480c20800c00352585095004030200c3e00403003030540102d05440722440a0b80c0c0c19004689024070f040c1d40c0c29046010380302520f41c104080102c500781c3d0b88428100d0340b091030003524041124500684032001c0c255a4040c0d101e140080c4030031403a2a1040e2815104c054614040b140c0b031a8450340d07260300650300851130603013989440c0482c040c11941202e0586811002103490300c80c5211070f00b50746403c61300040740540e140001c1a0710039801001900c08644085d81d8105090508074400c0f9920003090384215118450b03007401050070010484442d10070b0341e840c10f002529140c900712031585c5103400b80202040d500100707020302410f540072407802c415030320507540461856041e14095280908260000e0090701541088404000b110030383c82d0211444988103074031228450284108440c415030300c0a02142256500c6000a1008042d083c66980940796442051502c010004c011284aa1080c0100b00382c622101 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 463414352 1250 463413102 463413151
    0xb0123130f060b0c0f19020f0d05030a0210050606040812070804031e05210405041503020307030b060a080102040602060f06010c020a090204060f0315030305090310020a02102307120b030105 83
    0x1c164a0141000303100c640351502c18140718000780c05000c8d02030b000130701d030340d865540702c003044008915403101c120f0740d68010740c080007510b03810709028040100d030822001c56101c1c50030760103441c260740344a4041c246001c0074440103120b61780700c00011102c10006000c004040342ca2000800c500ea6642c8034140c600e00c6452a00a0518207858544400101041041902200790500743d030305403a41510000384451540b0030713101c05400310741c0c8001d60502c50710501104014080c601f5034040d52040d900e009841b522004020300340c0c000c80c0078a40041c3c3c8100000345441c4c410001d80741c1c0040c418107111960309140c1d000309104400540003e200150005400c0044503407245820000c00200d150801001c9401c0040301d481001c544009001c00801045c12076681e581800f0301c0e90b4132440302004654501e030000010752075840207042040c01610300b41592210603500d54415003d1008514401c1040c1d46415080d290580c1072840445110398824000100e61070911419020305554049076008081da1041c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 463415602 1250 463414352 463414363
    0x5010f20031c02120406051008010216050607020703120e130c020d021207050604082506050405060c0712081f030b040b150604030b04030309061103040b0123130f060b0c 74
    0x76030302e803501c1001007207038410341a4903440c0c2040c0d11010109468450194001008172203801c121000d510003e91107442074490a212080300d8415070a4603d25983c000050740c440000b440041e00e800102c2d4100360791a841000542c0640b04000e00460503081e1518400c4101e414402964025900030301c40612100e804100c00c801390340da0054040d01e080d25590710310780c0703c00010344002e2204202045a96142c05442405c014040c400c06490111440034101100640010344003641c1a0003454042108481c14204030b424203904000c151030084035800044a18040017000304a03c0d800006607a120220f01c0b071400300045000f03003280074035800c240c241061242e5000d041d0040141e040e80c80101503480c2d14081c0c3d01140d0300015100565903d50030300b94090489110002c20b2145003040c00c7c285886041e000e140124082c0c0a2a0a03582c4c03911006440b25030368890450b400001300011044c103103030162200030705a0920402041d50070b66401914142c5c1c80540080a4512010800c1c0700707464008c100 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 463416852 1250 463415602 463415647
    0x7020615010f0c02042003160e18090c04110c0c040c0804080a030915051905061e06040317041502010501140103090503190f2705010f2003 61
    0x520100206039a00182440ca5030550304001d220501c5009070555507244d0009481805100044403486681d4000314525072040b540f5807130404080d0780e840411b40c450781500f528440c2c064070f0020b16065101c0d900d042e44030014000d8219225100b1030420544450044056a5108020f0b1507220080380c2d120b035090504c5004454003407031400010180d0700f580f1490340d580064220f50716503543c0740ca24100f10007030400340b2001341921040c5122510108801d602080c40f65101c68003403d0445407020070201901c10075517001da4002d402054940b207195545a00c00c240c00c5004000b0361030103a0303a07516480e2240c40c0802481940301d000ca010007810080c80c940c02c840514610003004203604025a2a120b10a54800d540c1019950900f80d01044402c000b182c1c5480582039103410204403076100100081d005606140005e04440300000000324071050001300802d500072641152402c0c07500440725020000421000c110ba03907110200c071444122403001d490000c0002445d96036400045000c020190b151 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 463418102 1250 463416852 463416871
    0x1c060b040b010c0b01030611160c051008271608060702150415050703060806150a1d0f0c090d052512170408030f070224030718030b090303070206 64
    0x31000c3c0003a091071005410751f80d2040b40050800b840090240e01c0740030314079224080110341c101700010300c600c0c408400c003194002c4840429141e0120011a0b0301a4140d89034803010700c201405290152004546440c01d5034000c0888061014001c1c0d481d2a140d0395500000c101e0f04a030302130242c03090781440b00c0d03100c01b004c0c003030000340c681056903030741c038464001e120f14450b03840d5200041820305100f9080f25008003281c0046138950300f8a0b02d1617410004000f6105445074820a000203100002801102d09801502c1c00f101341c15901c50b0f101045440006151103610201003002d42082d640b2898200c40440c040c00c0208114502500c1040345540381c003003126030300c4000030f00030001151030204640119600124042c829245030300fa0f40c0e440d0040f03401a800c18000826500d0000304448003034011580221a0303015202c500d103210048007030201d0201c00d03098104100041f15903006658a40799090041d5011090030380c2e80d250f81110740c0080c4c804120580000050002c92503040040a40028008 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 463419352 1250 463418102 463418117
    0x2306040c020d080a0c120504060e0c03011503020d060b060406090e0601021902011b12030e0c0a05010807110c04110c0f1f0c0504080a050a0212071a0304021c060b040b01 74
    0x502c0c0292504a0040825401c25100d20b2504266845251502044500104140000d050a2406002400303e0007040c1103648100d80700c00446203014080e4501c1040281191400a030035602070000c101c00802c4141ca40f1500d8400d0a102526590020402403445954100150f410001d05008040c4081e080d1811035100c0d84140c81c594100058180c0b11540c24204084220058402ca40940f502e540014254903200c0d081450b80325010b811030141c82c4a01002e41d085c3c0c000070700406c410358185004060004010a0009a1060055402288a042c100112039140b14540d0018055401d00348000d101c030790020940f100440010058100340d03c01c098050440141c40d20004c500d18002080c0a4600d19241c0c400d02500350700038000c0700d01510100c030170784100c62850f0801d0355460307001003000c07406102d60401e10803614030007090f0142a80c5941c80d480401c07556014041030306030000351090303038041e82000214504a040c012207440b00c1d80301700c2002c1058115070b42040b04440200313035900c3c10320900 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 463420602 1250 463419352 463419373
    0x5011509020c120d0e0f06090c0a030c0504050c0c121e0702130b0a05031e060c0c1908120a06140d0b180109050a0c090c0309051e012306040c02 63
    0x1061072a19503030b0110450703440309104140c0034040c05481e01040b417a0300a1552001c107100c1c0c081065481028043d04450a1301c0c804d4050141c00d4030640300162032100c192405001e0352800e900b00603001103040c108c160070070303020001060805070781844038154400e00140840c20b50140070210022031a014656a0500240e9004500c02603800410900d00740c2d42d60505030080e65940300260040d04002e8200c8420b0101581100503c0d030081c80300000520500380040c4002e52480101d030420070f10400509100049110900c16480d0100c0c0e040394494007d00000c044240b06507121340c8900c2c1e0500010a000f0b152522489600713640074041070162243c00e1400e000704000414041d0452140c034a4000c0d14010000c000f0b00400e0900743c020624040c260076a8144011041060280c03580802c0400a49106120a90451700000b03001861a001000f08800000140c060700c0340c0c200081002240c1000e245401c0c0c43c50348102010300b44900034200500415042c18441c0500c14280c900003070140845 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 463421852 1250 463420602 463420627
    0xc14030c060132011b031d04020406090e06130f020319180807050f01060305060403030609090c030f030e03031303050c030a0b0f0a09060c05120f04080a030b0607020d0501150902 78
    0x1c2d00707141004070011501002070280d108031101c0e40342d801749010000400c000d9117402454500b602a1a07640e40801c4000100f82c2d00d0f241c42110b00300c5030f50b611249401c82c98400508884503000300215403144000215000c60300b05405200c503100c400302030050341c0345071034540d03098801110000407a40368902500c01d448012905450510582c01c0f10b5280d1321100d942c44c00c1c5280840e10544c0b8021542040e000100b00000014214010b500c2030724280b0210392521200d0302103513000c103805488140e003c002000401c61000385005010302074504a80f0545218021914580c08064124800151741c00c0400a0040a21103a45030070341c114094201d80b00d142e240e0044422001d42032032015031011000c10711f0440c5079807101114070340c000c40900c02014440340103802c03900a112005241e1750994006400c0c4030503824040c1c400e69002c410582010400c040460007070001ca075503070750400d004014140242c0d80e8002c0100030144100d001043e036044042d11074013200310560044034068018420301c01040b4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 463423102 1250 463421852 463421909
    0x6010b0f07020a090204080105180604020a090b01050d060f0810140408160c03081207080702100b010903020a030605010311190524130e07111c0c14030c0601 69
    0x80c4400045a1101a00d00000700310f0b104a910480d261440014005101c6506401003841400e01404c60709020401c0001d081d1030344012a4000d5200c0c200d450700b0312503100d06600c86040804c040c5009814034080381c881c03a04442d0241c000c2c000c090f100340c100b008608010001b0340500c60040c507062144103141130050840d00c2d00a00010304030380020070a902d03041d00c502c901c02580760b048824150003507602c0c1020036242e80b0a89030b04105445c03100004528900440259028070610781c01065140800306902008208401e181c504005025200201503034a041e5000041c5002d01400911545185044403500003050b035454000c060500c40c2404d14880aa120741c126001078540c001c00c4c02e034a00d03681302441c014160001c07500c04040703220000009200504020b44000d4807a138402c0f5282e407a000d503581d500600c03103610b5952004208070000f01c16001c000e03842c40f0031400c044580c400ca03561503108032000302c1d1050409500c01300b02e0400f240c01c200001d5005203100140d614055010305440c940c141d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 463424352 1250 463423102 463423117
    0x2a03020a380c0c060a060312051215040e01020417060f09070905191b0f030b060409090501090f081305190915050303160317060346021206010b 63
    0x50740c00500e4200e50441141c2d00d2640001c19901d4a141c5074810300001d250300d010507998003240c0c6041c0e0803068003030740403600e000220b12500b41b15581d4800301c0c0d01d10210307004003981c0c0203915240196050341c024000340c0702400c2841d104d40000003104142c240790010060a00784100108414002010702c08540e0600f43c601da000e000c1031954954401c03549525a0302c03840303284d251a01010000492940f48015585c030016980d00601d031403218412001e580c0b881d00c501d07030701c034600b048104011146540b000081c14854000030030903102c00c0c1c581000b440c10124051f10f142a0004030030401c2d541c14031321400942812668210301d0500c1e081c848494a515004100e60700e50760340080d8000680d2025560010540101100d569508032900500b01d0300301e1002c22801701c0c158140c82810700303100400d10b42c403c0c1c0000c2c000f40509840560b443c00c01c80c201140c98044200e036109000c4061074071005c10071141034040004282d20074580705102a400105941c90030580205005000c20318050080b01e000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 463425602 1250 463424352 463424453
    0x21c0b0f0108041b03120c200603130302070806010f051503090a0305210a06060306080f03070201051e040902120708060d170d05040b070e03070f05012a03020a 70
    0x1a20004c40c901030b901241e81c3c101130426105281e9918615501c409010f444503c00e030094081c08030840c09014125008046580c1e2104062000400e4080c0d00101074844074024811640d43310b507038414860500d80e0030303044541881020441800f00b03081c603c41c07041c0740d000c000b51214614a000b04065490780c034a0540141041400501d050050f009100e2480e52007003d00c047d95500d0404c010a00e009207e584224070200742400c4000a400f035000c03803054465060a001b035071503c046940115417640c424521500d6002ca07100301048402c1e8208040d2010704044100140d036101403ca60030b00340e44000b800324040060b80d2081160607152400b805c0c2c0b220b68014981a250b11003006d0404c42e038060440d00200b460b18020400c07041c080071209090090000d5100e100d612000c40c401d054076403020340200230000342e2181081005520807030403105202030310418035140e0040103101100001c8510382c10b40050340b28003808001d100084c2c0090005540720303042c0d102d046648010a02c1010031180c0c04494 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 463426852 1250 463425602 463425623
    0x90c13060e0f2a040512070803130f0e0402010e2101090503090a0807060801060806030717061905011818061b080f01030305040905040c09021c0b0f010804 68
    0x25420494021034040d100340c4198160301c0ca400042e004884008071540100c800c0c16001a140018400031074811848159003182d103440e0a04040c400c400100c142501058400d42c400090440001e1000d014200c0b8901e480024140ca0b05001e0f411810380c9070401c80711009810103110041c2e03040354040c80056815140003014201c11900340d046c02400f840071b4a6103500340f400100c2001000300041c0888442151a83c58207501e40c0b566550f03a9220340241c3d408500c2e40001400002c0c0a80d0105034400002012125510f4440c172200902d59851941c0b40d01550118085c405d01030200380c80c1b03001c2d003a11410204203946c503003200d9070600802a4040e64483c0d5030dd1000114490640c1e40c640340f8150014428003444a11100d811750078030078481d0000c001f4008001244621b15445131417412290150b5400c1d060a06103038006c6c00820014000f143c4000c0c0c07030780c1d00040c1544e01d030001e0945843c40c031a802400884030030586081c2d4209401b4184104950000710700540c2e003008aa54019401002c40301 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 463428102 1250 463426852 463426879
    0x501050f01261305060c070b060d05010908070c0e070309020619090302120601030b09030c030d1d010e1006060c0203100b0120011a190b0a140c010b030c0603090c 71
    0x1110461030302e1105410440e1003003081240b10fa00b0a1191030b580c0310710110760341603860804400c2940150b01c80188181145800300340c10b485c0c69158030b40d00a01400000030790f00100d40d142840b69000d400122485030f02014100300d200f0304906650391105440c24148121000c960010b2824072950303810212590613420103081c002d00c1240201c02442d4040d080d0700c4100b24180345d03a03944001c01d02c8102c034200c817241300061403400d0100c141c1d00303000307900d400840c10311081204030000f0301441b940b03d0a203460f41004102140c00d0034092441c10440c0c3c1c1020f0000304801814801c20b80c0e440d40c0044051100400e40c5000607100003400d003480501c2400002980400725004843c130320785114803031031680000012415010f02c10f510200c2c0e03c0c0c0c4c10110841400b00c0001c14805148460f2001f40c1200c45218400c112282d541030092a00000074900a40f9980980c011016181c001d40b104407070aa541c0c60090030142000c101c2041c442108448107030440c581007a5856580a0080d0418040c00c641c42440 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 463429352 1250 463428102 463428137
    0x80705030903040e1005242b0c0e0306280b01052713061404090809040204030c050a12080301060f02010902040c08100905010f030204110c0a120f02010501050f01 71
    0xc401034155910904d8907803d142c2400f10000c1c41034014a0703c03a098180541c01a14280f00549008500010380d079030600060100d0703d02402070f0010300220407404c40c40d1100c00030701d080c07203401c0401c450b13500d481e45c2034594842818641100244240d02c881d8040001200001d84800103618030703011000081103010044d00100d03017a0041031600590203c0140b205c2141c0c94400c0401c04010a055800018158040a620050300d20610030b03202e0700e80d603440e8024414149a00f040300c006010f00c0703616240070360740004030303049900c02d50080d08c452008960a100c58940400c0703e03c001c14180c001c20b106100d10303031606c0600c2d10041c0b0030030b0240a04280c3c00da502a000790400f0b0162030300241308214504806d000901203a0040b11040c180000c2850007181414007407240c90b0603120400104a0424116030030302005043c2c46c083c9101c054024813044603601020031812207858801d213a03662200481400140c84c90031280342000070345e41020010301840e21071003d00310180c0800d280c0300e5850305001243c13 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 463430602 1250 463429352 463429357
    0x3040503150402030c090112050c150702040e15011205120322051009030809010c23090d06020f0703080c2104062003070207050a0e0601050903070e070f08130201080705030903 77
    0x113140c00484600000400d0350161848c0500700e400b440c2500e6035542d5103c00c00010718407000c200074031502c0520880002d42416400841024030481c12210307800510440030175141c40c2680410004201040300c20200035003071006d4402103611403900b42c21410005000d0f1058100200152035012440c0c0c1c0c84420302c0360801c403d00d074040042104100480103402d005006070412911280550709201100c000c45d44078041c91480d01181d0032014013187c4c0858061035060307000386440c80c2e10032400507400004c40d40340d10040a24014000c1043c0d1341c0c0c0058500078068007001484c1b52000da2050206d205003510480d4410300c1c602540441140c10398842c03424000034800c030b003a400c107503240103040d030007072844000025401209075401b00c50001e0f550741c040218161450060b071204100c1d8402041045d4010405440c6a44000741605c8c149034941d444000c1c3c40508540c020002020703010200b1641d0340004000b6007100c82c2024a0459400c590006009024003401090400400000003840641c06109 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 463431852 1250 463430602 463430623
    0xa031101050d0c0509180402010915030e030c1b06030121030c05030c0c013b01031407080f360304050411070203070e24010c06020a0c140304050315040203 68
    0xc0402580a64990084c0f2035000641d00300e0203010560781802d19800b010141900c501d605954a004150901030041803041041011000b4141c0f5045117460b145401d001400d0701000035801050721611350003a26585482c1050414052034040006106402103030070303103040444000c651565824068981114111020700000c1c14a00021440d5040c0540c00f2900302e001b000c0036618800c40340000c606815840d011041000d002000882c0007802c00d40019401c0030210b82d050400044003400e441806940c10000c8622000140c058810841c03820382c1240f0450700500104408401e0300344140642c03401824020003107818113000c903400603011004200306d401510002d00b090240220500c203d072120f4120005c00ca11900a905020810b0079007507a00910444190310703444585803030039051004c0001d908244a041103840e00b03a146c00329040e80028120384180c1d40d0759150a0340f0b9818201c1d180401c3d540312190a810802081165580004500001c1ca506140d904101c2d2201e02c00a40780681001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 463433102 1250 463431852 463431877
    0x9070e042003150a1b11031e070f03050d06061d04020d09080c03040e090d08011a130b09180402090a020c030c07090c020607020f1203150a15020f03090a03110105 71
    0x18100050501c064002841d00b154203c0c6078814140c5d440401c3d20001190030440403143d000307000701d03500e110500c1945115182e2691005280c40055112601781c0c4010354400c1e00415800100100030078042e1240320010003051800c10404102c8400614440f146409214400c40c1c022810011011242d030246900035804185caaa5600ca05040d450300c0b50018456000080b8a00c000036164200c04617104482da58207a644014582c200004a107040b02d000d20088003043e030900c05841500001004030003e414a021025110b124007410841101070344a1000e1405907034006010040c0c075440d0110340c0146c00c0600150f01c03101503900071461402400700c42910340c42a0302d000144e4140b240d12880c01c8004070350030344e28583d949160685c0e68030000d0001d50442e500c42100400101135610155030841914005411102d4280c00000d180f0ba801c0d03000181c600490086c12001da0340c04010004400342c200c4055403c0c0560480054682d425503c00585000340580c00c00119a12032012104503141d0300d03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 463434352 1250 463433102 463433143
    0x7060209061b0d020c0a0b0708031e090615011e03050613090c0e01080d0905060306121e011506091502032106090a110703030c180303020609070e042003 67
    0x2599983c0d030f1905900321100c098040c0582094a0307040160b10b44051341c03041d014051600740d01d543e480000f50300003040d200320202e640f1004408920200b900901a10480004040702c0c1070010b5840324681003c9501414410001040407108400a003e003594602c3d40c10b0018255441c3c2001c0b80340c41e0162070900c54071903d46080c1100f0004a00c10002c141d511100103900c05a89a000d02d5a903440f980010001181961000b041181f409070000e42e03100c000503090007912004030405a01e0100d0b82c1c1c608144043d052030341009854003d100d048140d0b44041c1042c0d101c01d1400300301601442e114041d030f5075081d0b0300760b58000b01030740204210380549240f0a005101c4a149031115002c0c1d4000f0740e25940703c0d149400220b404d440890044140d520004208a40b420341c0c650750950003020302c0356800062000341c0801c0c48642c05911114401140a500900fa081c50104286410308031a50407052590464406100c08122018100604000250040c0345180c2211002a1409101c03140c00800d40a00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 463435602 1250 463434352 463434397
    0x180b04230f150a0e07180204030b0a0903021005160c0c030b0108240411010e0a0503010204090f1811060a02101b08070305010303210f020310030311120706020906 71
    0x20b08403480d109181044081c90303c40071841429942518000d0100754010340301805200d0800c0c05180011140074001450079a1381e940c0c0000c03020003102c410140300c0d0354180c80c00502d0b03011f0141c2c40061404250400c083d127040900c1c1c10241071144400002c002c0084200c070200003500c00c9420203180c001d0003101a039030f07560381180c2d03480c1c4c9500c00780c40194420f8a01900d54070200601580030700d0b40b10707490540303442c0700c640112203030109051000d620014404002809071000e10041c0080c052119000c0345a681400c1071205331681400c00940c4240c40300b083c07d000c00e81c0c0707582c0c1d0030020000b00d034100c2c0d0303500606104a05c2c1051680103019002e2030001004030051060301e143c1e5801e00c45848070000d55450340001e130101d800900c40070300403e5822080c891840740b815500d292210000c0e40000e0540c00214107a02240c2044521a03c00c0a43c01810710515801102d40080b2030003000040190702e400300200c030101c0c003407042e00030f0000c2d4010554049170b035510b9080d42c0c103d182501c50407104810 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 463436852 1250 463435602 463435633
    0x30e0708060702072306030402030a0f080d15050906060c100c0503040201080c1c0b040e070f082842050a0908090f0102120c03090103180b0423 63
    0x141e41c0d9501502c110200000d11072011103a4049403081d1542400c200d45d070302001c0c04250340c0700400480e818096900c00c10001600b1800c001c40343d42c0030b06816603c036000140008102c5041101c0145414104031040042d1f40e120044a94845c0003902c60701c1c1c4600d00d0000b43c81c40d240c1114144180342c2d040c6298101c1461f4008051840b41c0c0c000d82c0c51030307000d4541d070070442ca0a1050080c031250865074003000340c0c20841181c0069034200340240002038007924800d802c0d401d000e095004603060103d41c03d41001381c00d40400a00c042a0040c0031700d01000305e0b14060384010901c1d0b021000b058092074045034000c006141d0401c0320800140200b95404003100d03080800440002d03036042d500246040c000c40d01c0540b8910034400710300c0c0e000c0c0d000f51600d070400d41040403d11a07002114114880c0d50068075081c04004003a000000c4d052008580320b40070203002400751100d42003071401a0650048050201e108500b03695006500031543d40f64050500302c40840d10382481501400034820f0003041e011009 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 463438102 1250 463436852 463436863
    0x2803150902091806040b07110d0909060602030a08011802090d03030e0d021c0302030a020405220e01020f1818131703040c0605250309060215040819030e0708 69
    0x501c00c42c1c1201a50340d030800c3c0b0710449110401502d072140d0011001070000b50041c0b00c00c5802130420308201030008600031800b85003040c0303e0311200010704000c0c4c08009400380d07401468082c00f024000303181003960440005040e0003051040c012084140c00151203c3c60312541100c0940002924240038000710b41800303005807a070b200c01802c840c46203040c0d015005101141110258006507480c3c032070700c2c00e030140480180d0005464240c0f19a0f003000009810b603141c0350b00091540c13000e003040da00c0458400c40307139007141c1311403c003000241d00420588007444000d408481c00c5c043d0524000428040305e0b0301180568070509450007400d8007070f4040c0441c19040700700100040d4482d54a5494924180040300082d0009480045c8250303142c82d02402441d0061010342420390403125241e13000d10451508806c0d55110b5035007580452210321060104a90503c61000d003044192000702c90750600d07503a8040d080c841c14912521001c1000e6402d500148660000c50700c6482900454013403035140c640d0280c845 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 463439352 1250 463438102 463438121
    0x8041118071106040302060705090102010b0d031e090b030103021c02090f150a180c020f070f0e1501020a1e060905010f0b011706150405041418010605280315 69
    0x1c2c0c81d80720031030340c142c2000801c00c0c80f0751743c1035000e004182c848020690310394010001c81e81c190354980080d0741203911000030103804a8042c0c0d42c1e0322030a856640307060040034440354581d010402c0c0d640e414070076000080102c070f044070750541d000711403031040c80081c851021501c80003c0d03100c0203202c14050280fa48003c1140151701201d4a101d1881c02d900400102c10010321880464003158452007801050a41c06141c1205290041d070307241040303070350b40e00313013044290f400641c1c200c600000b040c4070340140e95100691100d052006220301c11b14440000c0e42d18260500001c0c4841150b0032250a202e40700c007810440503034800300c04d0100704a00c2c50700c03d000c1d0107803200c0c80d0f440511300102c141d11584a80c6556103814001071100b50151503071b03800d0081c0c001d2040107228400c01c0402001409490f00c2c410b01c02d040103100b01c20000c2c0c2c1805102802d95411800010100760b04080040c015942c0740404101c0ca4100884002e84500d11448044290a200c0c0d102601e07000c5c90118410101c10727507802c9101c0c00c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 463440602 1250 463439352 463439357
    0x312050c1e0708010903120b0409120314010911030402091005030706020703050c10080f04080f0307021501050102031318150b070c090908030f0403020c13090c0b0c030a0804111807 79
    0x1001c1d03c4503a5035080320303a00103002d00094058a54020821115440143c4142000d8008211400c564592418640c20768a01000180e41d94030151507842003601c000e40035080c05c3c2404d0054540b0440882018000500080c0c800c0c2d0614000c16040c40d8000d40c42d80080c407000e0162210036560b25006034580700948015500ca0190740244540c1d450b040840400c0c03184107448981080e01c5210660351081c1c0000c008a80d00c1400b0480f4803a54610314014500c10002c035801407034080a140614040c1c100183c2c07003c0d0545d8400d20183c00741c0d0700344149078400d0314500400507101c2c5680340089005002c605c1c40100303203c1e5603904045a104480b50043c000316004801c0700908541c3c074424102290204080a0702d010000c0c03005c2680b101c0c1842000350040d000344111003184d0394400024800720140c0710000d40031a61240c0003000c00811500000080030a091940c2c1401e0f00c0440180d00d0380b01d1200c40d034080014010000341041104040c8220814018002611510182c402405802000d8400201 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 463441852 1250 463440602 463440613
    0x901030912051309111902010915051e0105150d1e060305071401050412230d030e06040503090d0804080a060506011e0c0b10080109050303011a04030c0312050c1e 71
    0x31452414040e58013031762144006540340440300d0303c60040560749031407103008554a802c0d402001c1001c03085002c174041c0c6440c03030000303550400076010380c00190110100d03d03c413800c0800400403555080c5900402e03604003506543d485454503d450300074204100802181070803024440b04100c02c1c1d03070104050380d02c0740c8129803030710ba101c0c07070064005401c00c48010300054082005101000e20494084041c43c4034507168424880c010f04280c080c035800c003518060641c0326805409803d0b0f4507003e86030741c1240d143d000d007002c0e040a483d855204c0c40380701087c03401600160207181c200481e51084800500944043d2400380c1410b29102003e04002e07500707a0300007000d0145050032380500700030310b4202442588071040324004581e00d10842800081c0080d0b0f05801c50702c40042c403040280900ca4041d4410809150360390b0401000799100107848021407102281400141300142820b5904e00c2034079000500c00030820855030301201d55201d03175024401c040c00390507104441504800b4900c0603084031802a1038 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 463443102 1250 463441852 463441859
    0x60e1006090e0c011106011e090f0b030d0c080f090a0302061209010b01080601170c09030d03022203021302030c0d0603050d0e0603091509010603051c0e060405100509010309120513 79
    0x11540100c445d0700203c20b4200b4170040158440a0b01c0c6182100c0f20071207440d41595494045004a41e00394110145481d10b071001002e0601e01405107440a0070a030410110480144d160150b1703030300035544605050768001642c5981543c03200c82000c000c1d44e0042c0343c10b50300c0110042c0824041c105440c86c007015800d10b80d0700d02866002c1ca008230301c545010385d10400148801c00f400200184068001c0d0b0070201c1c01c01900e20a0b46081c082c0702440046502c015944609200c1c002804416030440b005030110420010300041e56010385841008145807005078480d1500c1c07501000c54880c005c0440e604c0d600d0140c00004000c800300f5405183c6020351240b00c07404401070203001840c40f0840700c0a03910341221f940004040c2d03190000342e401401c081c00000e20b494403503031010301e400e80100607a030502021260011400c1c3d808803a00348048000d0310030b61b0615180c10081000341356002c824070140034010440c00c9c0a648aa80050a002c1e04461040c0007000180d10140c202d501c44405040911401540070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 463444352 1250 463443102 463443107
    0xe1f060803070b0402011d12010c120c05120c04050a03060e0d0216061421180f07030201081e0106080106020d0905090103021909050a1508060f04060e1006090e0c01 72
    0x160516030300010b102c40f8642c1d49500440d145c0c4468800e1640004001207000d0058035030141c07080307010002c031000160300141c0420241c00c0444501c510f002060900d000c3c000780ca548041a15494010094003034510f8440a1100c0c0450080c5d4020356008242180000305201e080c0d0000740c946241c140c03c2c0c07003800b4403951080380ca6443c0800d00361180e142102040140c00d12400c4092110002c1c001c20314180300007612507000413030340d0684801c40c2c0c02c3c0c031a051000c1c15803004d001c201c0c40d4000e1001014400030038406107481c0d03500d51101a050119060000b03030914081ca941c10740309441d800005000e581c640354086e000f207000b8002c0700010700c0756541c0c19a005002e829200c0a5420080c240c9104d170386180d08104c02c808250120180d80d810000d00010601418080d19006920304070303011400103128480d1181c0000e803a0b02c4003405600c1142401081d8007640c100a40180d04484086000062110a80e18118080310f180882c41d103462400108440507500080d0052407100903907014034030380c4004 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 463445602 1250 463444352 463444357
    0x60b0a060f0c081b03190f050301180c090506211003020d02060a020f0a0c1a250201031b0e040f02070816061401120501050703020a050a0e040e1f060803 67
    0x181c1c1c081062415581d002c56000000381c64080192000d000300509025031a600796040001c2d80d40100170010003d005440c0c00c132042c48842a0b46207402403c0d907241400c001400803500c086c56400c142d07140c08184071a80702e01c41190113044064015940c901802a049400800c00240c9054009409002c1070001c121081c4040071641c00a040445000e182d800700007141e40005401ca0952048203c0f14500100c20300074040e099004a104410700c91a250f07821425a001c00001d0192000030001c2071074992401c0001c1d0585065405412070003802c40c801070340102103000c1c4e9401504540b04010074200d602c41050700004d03806843c28030110401003035401c240e01408a004106d20824042400606500740b61445154090030002c40c0711000518000d40030842030300302c0d0380b2031807260b208841031040c240561904006039280441c42d10314002d030f00900c40d00a07240c0720010019204482c40c503580d00d980101441d0071800c001d031140401d25a51051400303010410340e80c0708070b0603ca000513116401005 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 463446852 1250 463445602 463445627
    0x60103090b01120b06100c0b060406271112010303080601020a0605101a09060306060a0329040e0d022814010605010f030203040206040b0705010212010b0322210219060b0a06 76
    0x1d0700d6000d000d048c0d0741d070940150021303c200d40007503443e0303000907041c084000c1590f245041c06080814600420703044000703490004601d00003003c0c0812050605071040c03003400f4116605458500c92540390040100d00304013101002515943c00c04090201216034250100202c8513005404100f00180391078115460007000c2107a6070000d01800011391504003400100300c0000d1074500029a0b1603a13241040021000840700380b88828000819521400c20f0303c505103c500040d0001c0c4035518000e10000c1d070301c0d6010000080d50f40d444010307030050130031546164501650700241c052407515000049034001c006622500340050059004c174410345010b8801c6070b000e0f54014150525040c10035000c172045900101d02101c007590300308074120300c4070100d0045134040c020000e40595241051707845000040764903501803902205180e41c0c180001c20b0080c0442113a60b0220504400ea42d40e01c2080c0d04281c3d00c040c01c00d080000c030042c0701c402c10500794040e09005104071644450030b91521000c842103241c1d000f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 463448102 1250 463446852 463446857
    0x16020c120703060203100b070303061d040c061412040501092112020f091e04150f1e0f0e0601031d210906040e010302030c030f0a030503060103090b01120b0610 70
    0x2241400403034940c1d0021503004001b00c550001950352210090881e900001702580000d51303d42007884800c40c02007101d04a080b29003600500d03804d1a80b87c2009400c0c0600c10303141070041d200f8070240440b0f80c4d00c055a031590011000c1412510b01400c04602828686000b1110401044260551a400c0b640d14018803a40e0755504501140c42811400096000f10054000c550050000010a81d01c146e420b190507840c545a0180c2415204203200aa440c0da02071a804807010200510460200c5800881119803e02c00c4c2502c001105004c024007100a80011040059900d03001c103400c88d204100c640110002ea030304000700303610b6010301c01111101d0b219a030340d2034002080b0704035202c1740320082e5001c035441d91049602c0c00340342e50005955a8403d40c8010b20040010004000750710303050107903407a24601640a4080544000c91058542c07006180c020280034001c0085881a4400d030300c01ca17515584100704c1c40031545c65038131151041000281c1203a0100b141c1c2d00042c01401c00241204002c04641c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 463449352 1250 463448102 463448113
    0x30606170a1b0e0405030909010801060b0f07080408070b03041101030b0f010f030f02030702070303170121140601090e0d0201060e0a0c020313090902121204030204020d0f0516020c12 80
    0x10780d500c4451090202c000780d11250180d00215500c41d114896500442c03080000319551241c010500200c030070160701003019640761103000c000c444000011200340603440509160b8502942c680100607000340c0d0003085142c81100804501903182000460045003e0495907242d80982401103003919181e2000940198050030070032090350051001e402c01c01302c030f42000300b441b44000359400100e8000300c0321100103034450102001415009030140c0a040c6900003901d00030f606001c0300010340c1000c13800350132030046945484028405a40405140340d04240c0c00d4500d956500c1a0200103800044c6149000c2c0c080d400881904500500c1510102d50152904c2d03622a034800002800070300c4142c12581c1540010840200341ca6804892000074040d0f42800280c480c00c940140008417003500206000e0307a014018081b40d41e030009069030700b2264121005039503240320b94602405448210000d500f5141001c0520501e030140c0040d039907a90303855034200c40803180708904200004811702e0720400f02c0d4015 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 463450602 1250 463449352 463449373
    0xc0c15020c101805061f05180c03040819090311040e060106031a04140106030c08090a1104090f030c140a021e120a03030e0c01080103050d11012403060617 68
    0x120741110b00c240c070205850140c03c5a107925101d04003042107620345001d28405100c2c4110308040140c00010341815103811f000030759050324014901001034403440780d201c1c0c0880000c042042c07000851724070180300040c942850315400c03806072440a180c08100c038401c034603e407588880e0a0510900300c0f00d5603d00700500640e464004150014007102e100c10203d00d44141d840d0449445501600078200d110039510b806640c580031000307003101c083c2e00d02501045080820710640040000e0008802a0480c60101d01041014001801040303440e000a246440b04003055041c103030095107054069008803001003945040356404c0751101c0c40b00c81c00070741c044403921250702d0542d100041080c9050001c0c1c59000b651101c400749500d007000c0d81d802200000d469032214a604c2c4420f006800d07020f282801c00740c0b0326504540d00c445d12201b4400c810360070828110403a1251710001d420031654050032000c452240740d40c50404039250f80f6240410355225040040001d03c02c0c0789004444282a00c0e0000343c10300e010b0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 463451852 1250 463450602 463450633
    0x6030c0c030c080d09030c12020606011403090321060f010503130f02040b09010e1f03020904030f0e120a0605160806060f0408061312020f120c0307060c0c15020c 71
    0x82d0000140d5000300c05201881240790390f07200f94503034030b8026202c00a000200789460406440a00078070402c54101d481400100d91704400520340380003d001c021030310380d130341c2c540d441e0302e140180c43c42e02104042d035135640021380b88500020b501a15094817448120703210740700192101d03c0140d030150119280c0c400030703001080c8948502c3c0000381c40144082000601000044c064034000e811424444100078140200302a1183c800d90414104200002c40d191441d00050803a920060028080c0035180d42c9600c100e900c200c1e0380c50302202c001030049a10b0384402c001169541e801c100b04030b50491400740402d010408240080c1d80c100309a40c0c1e24480c032340d20755061048036040203145c490346160600c03020502c000284001d6101c0e42c4c2c4401e0342580360246080030341c51503c0c074189500954002400202c00b040300416611808440402002d070344000c290300c05461881168006013000389881041d803a11644040c1c842c01c210f000b0499180c0240700d01c11080101c0c8504200310b856913000c00e90b044c42402 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 463453102 1250 463451852 463451867
    0xb0703020c01060b4b07030509090405030a03140903252a05010c02100813020310140106080c07110f1f0909110315030c030f0c04050106030c0c03 64
    0x20303034400202d41d890b031310f480c46026900910b05001d01c44181d075010018851000a003440c1c060340d42081051400c48858240701c0e1500c0d008841c0700d0f1050001200c030141800b03001211007011020f0603c82003494642409600da42102001c280000d04003030809402c042d074003e0507801420035002440c60255014030750485040c0c8402181780c06040360030700c130b00480c024003148a81001408441448a403800006411101a1b500620306018001c586d81001d40c44001c2541e807240c1c000d08041540d0345800c0744180c078424841b40c00940c54032070070117483c0741c0e452a604880340d2180c00045641460340c071107001791001071040700e41ba00c0040c020b104100101d1045401040c01103009420101040071000c01b00720b9862858030600030001d244144078400386d5100c80c110009058001040040b15007081c281000d9100107807100c2d0000701450800e201680c1c05200861002500404a41f040000300e4299504c0ccc45555916034411481d04000290039402405001c4200c901ca503101020300748a03a43c1500d084 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 463454352 1250 463453102 463453117
    0x120105131409010204030210031a01120e030c01020702130e0a0303050c1e1801030501060504270c0908060c03010e0c03090a0203030a03020909130f1217240d0b070302 73
    0x340e10381e581d0198040607095658003644442c400507956a045005014841c14142455420103103030030300b041c9000140c400c003028003080034a4800b0042c0e512540b080050a4003825200d41800001040300c0e02c00c005500816002e4802d441c005a10201c1c903504c4000c84901091225241d04155114000207109500c1070783e200301880c0d4820704101035080401d48008003c1c42041d071042002502d00c0e907110000103c11201a4246014003c945c101710b0001d0440c0503500c41d44820344402c50714211400446509111101ca40803020829440d240340e004000034294820941c06004242c0030a0300c444400e0101c03410b856125010344032a8680c0f948107900e9600084c5203411074003030700100c580141c0d002e000800c0030600c10b40d00580c603100e001080210440014081e080f020003040041e400154060b04956078540d0800104c3c0c0c40108582810b462032514a020071888030b06410810a000384001d141c800300d601000040c0c100b8a44180511401002d1501c0c060041e8010600140fa482c1c031a4000782200d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 463455602 1250 463454352 463454389
    0x3041a03071704030801051e0a05011409040c0c1a04170d0b220b010504080a0201140f0f04090e0105071d0609040603261305060912060406050f0c120105 67
    0x200d8650b0104441400020303034003100052560f034010061880c00c808d81c8220401403413040c55850b104440011096040c80c407c45040c088060754054a020401e030554a01e0b01340540103202c402c0e000c0304001c01e11154103c04854014080d604414001c07103010b8000d201c1e40d400340382c8100405441840c0000c40c0c01082c00c901d0440d40311100c600541d102c3c10320350044552500307041603d000c103440d80c04069400200b1482d0401c01c06100412040e0703000500e11841940a0034039070b4100c800107107800c14512031200c2d428403a040c0052541c500900c90002401150b2840301c04000d4461042400c070b0030b980c402d40d080800103c0b80c1c1d48121175070154880b22200140d004201c14940118080170501b41e0303e85a005440805040c0d1454610000d82108907002180d00410310b46420001080c1003110301030360150038003584020402000549410b00a004511581801c8440d13610703191078a00040c000c110740500c00303100e04002190445400d4403d58401c44040300040500e03a090009224454600d00b01c030000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 463456852 1250 463455602 463455617
    0x1a07050315060928061d0607030504050a120302010b0a0605090f011b05100515090a020d0f0e011b1805040f090605070903030905030718091704141203041a0307 70
    0x440f956050f15407180d806001e600900d075502045440d01d250112a40138001b8481440c541d030a85a980a1009101c03e5044400940b80e00b0360b030400701d0310703401a500820f8010071401408168401e00507118500703d482035000303000d030803050001e10104c1c41181c071444011070401e0003100c0c402c5c601010f400d4002d180c1807400d0b400e40c82035500d62140301c0c07480c0c3d40240c0d482e811030303041340c03910848a0180541c06400580c038071143c0558100480c03000017000b404a00b000342d02050380b8003048410380098120599586c0140150700d03001c06028000c0160b0382d00610320840c0c803540c9020260007041007010344002d290001d0f820500d00700500000d0005071244c12026582c40b408107000034280c1c407440e80540400ea072681401d500f10b1501820039072140d0040d501c80c0d81310407820083e0b807256070701c408d00e1160304400114512401c1c3c070749540b22500c289200e841d1802e0114004c81c0d202501500c074209200c0131241e1040b4509041e50250310780c401e6014002c000b00841e0140003422003124019500550070785466403 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 463458102 1250 463456852 463456867
    0x111091c170903061e041b0f0f06180f1502030f07060b010206130f02010c03210506030c0a0509130c090519050c18130f050f041a0705031506 62
    0x51288140c0d203181d20801d801240040c6141010003245902010035404c02c40064114280d2190402004000070100d0320164482c2c1481c01d5000c1c0400020409040440300290b16180c03c03400b02402400f481c0000740c5131003e500313402482906180111782201c600724030510306040641068140840034141580700811041c4074000300f40b4000c1814500808000984920800c00281404c1018180c41c010248800c0443d0210350315220340c8046590900f04440b845140d840d00307480c0034401c02412007101c0064402914041d03455048280300e01d108500b9a510710b0f50a100700102d801507405a9600190303000009203000c010074544002d0b803801403604082050751044050203594045601c041c0c0d00315010f030708040710754442c00340a4000c0002ca4640381008100030304001480014000c051046102809000d1100000d500044820340d81400610591400b45514481c0d000207030b9084a104144206007a041c0c0e045821071070080c0115640c10340f0b9505c60559035050300d03e1b203446140d446178007080b01d074 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 463459352 1250 463458102 463458113
    0x6080601080a1101170a0c03060509070216060c0c1403030f0703031b0905100e01030e070801052512020706180f1a070e010305040c03121e020111091c 66
    0x6030081c0554002056403204900c0c000000000d1403100d00d0510002c040c40209044c0620039a5501c12801900007031b4400c0e40c080100d0103010181d20154110402c84e050056944d07001c620b15803680401d0010720889990307140116210002224090240450210b0521005c0440f51a54400910050031030f403d025401600d2030180d07100000072030109030395480003e1010124284249040b249050000f9450720b840f0100301020116481501000803989441c0c0c1c00d0380c000d81c4124080c4030503a04542c904c80e1106c0382903009040503600400141e20840300e410042d03031100b0f81807094000903942ca5030140c4000d81640c0294104440844500b0344440c0c2642c0c10f05400404801c40502802c0391980340d000c2410444969050305c078480101c48805d900300000660800303103001c0300300c3e420b1070009419038843c00c06251040351900002d00c00c1401400c034401043e84181c0a5050021034107040502022111043c4e080341e0004072031407002d03c01406103899034035081c1045154040010b01d2008640322030350301c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 463460602 1250 463459352 463459363
    0x4060b0f03090d050f3c070203150606160807050303040c140a0501081504020403020303030406060501120b0907200f10140108071a1c09060e0606090a020d0608 70
    0xa22946040441000000e0b142000103800004107820301601d441d0030800013801c0e5124070041d0303001e00030f0a80c040d106140e003011015110001108558080c00c05046092001e0b0303030003207070b050344213100d8052035802003900c481401e4080c0c94014030f07003880c0001002c08148545240201500c18640900650000c1801800158801c503c2020601d160600301482d80d403590fa2b4000340345014585042080c40281d810103901500a010805518260385000c80020040d2049810081d054003011092004000c541c0e0000070540340d090b2561007582c004c01d00d200048070782083d212680f000700d40c40840d1041d8000c0e90020041d25001d052500b2860b4801c0c80b561406918001008282e0700c162314990440d001807041c000c005880c40c48101555160130025a07444020b8000e240c842d102c602804a4014190000c9074410404e00490850300078400d28401c000b405902002d81e405420a42c2c2840d6203000414058031030400140143c1244d00c5000444009401c11030014020995807003001c5400303d8200407 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 463461852 1250 463460602 463460617
    0x4141e041d2b02060730090b07080c03090a03120207081602030c061e0f04180506011209032106050a1205120313060b061606050a0606080702190204060b 67
    0x14101c2c1209606a1615403005400150303008540204060212140e800104003610145001600400b290f4000b5190740d54146c0c0301400703c5062a08102c0e0040100d00113070244192a90b4980c5040f0b0360b5180c41400302840111400744403a001084010002401540403032620046c001005003804841d07691030069600c4614002c80d4000080f0f0304000f14a07040001e405c07680025190541046504200c511900104440f0000b00e003501180c40c0d0007000c1c03150181c81c000c10714541500110b074180c05685000f00000c1d680e42d8009203540c1181e003161401400307440101da5250341c03468003484a12172440352900221500c0c050854550b0800212603690202c2d2801a02d4449034200500c2e030b840c0342142ca40440d0001900005000b48104103e5040c02201240842d800490201341c541c00180022802d01c0b80360b88e035100c1c000816102c5e1003448201da00a034410341020340100907072b541b207030019200400e0844030b07580168841000500485a1444c07503410842c40035002007040f585866915441780c1023000c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 463463102 1250 463461852 463461883
    0x1090602160203071e12020d02210d02070b0d051f080f100b03070312030e0303010f08010e0f030d0207060b090a022701080c031801050702010204141e041d 68
    0x4618809502d401c3c01038200070b00c201444d0088145c004010110000c13041d00c84ca00c1d80c0b03851001c403801991100008410100c0d030090803500003d0b01c030740e0f444002e01e40c400100c005602c201a40d0305945800002c01038103450884003000d04180191a010010704401481800380c100003454000c10419132810140242070018090a21000b104107491300c0e04a0040f0b20300000303402e2882c0003809071800f14080c03061343e400c9490540301414000066001d810501c900200740c0c0b00c000300014a041d526607014080c0c0310745c80020302201941007100d0750764850105c00403a168004111403402d014043c3e0042c143c1c80e01c14480480c89456140c001807070440304071400c10076030342c000841c1e54002e2400c0904840440c503440541c6d120703001d5880020641007000386060142d401c0040800c10116080d0103040d14081c2c41f1000303005070315290300024080e4101e07201c0c801c0041d0340420b50070141c2c50700010300b840c000180300100c030241418804020192045010f44890801c4402140c20540414000d41d03200802c0b00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 463464352 1250 463463102 463463137
    0xe1828120e010f080f040b04050a0c03121202030f06060d110408010c0e030d020c101b0c150201020c0a02211203060a05010e060d0b030c060a090905180d03090501090602 74
    0x24005084110a50b8280e02001404d07001c2104090412801c81d4109401001211a940c0c45103001e500e49005c0c0c0c030b40504950384190f400010881c0d5040075a105001642d00c100036111382e40000810303808203031380840030701039420006441d80c1800c2024060307584800f40b010500503419480c43e0211382c81074011421503519070351180c521541103a042601030703005500906607400d450030300a4035802c02c0306645105da50707042400c00c0514171582c0e2400301d40054115001840c2000d15090406207030a1103600141009440542401c600610941e22010011005003030100c55650030441c1c8042884004140c0e02600d1074490400c0c1d108000140101405c15401a03a0341860000c002140d18241e101904000d500c61032006187c03906010b07251a0052000041860b1113080002810160300300c004540200000c80d8030700c2c1c00340e84061840c00303c031004641003140d0f032603540c44030b010904038959000c001e90011108a0b00303070307100e0707400b801c80b55004100014140300c20342d80d00d4082c0d038032400701c440c07118866 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 463465602 1250 463464352 463464377
    0x1309230f010b2d010507020406060804061d0d0e0604150206070210020304080d0b040605120a030305061905010f031107241a06070f02041103010e182812 67
    0x920036a2100e1000711064028050109110f4540c1e0046a42e0050711072010b8035281a10f9024805880078a42d0081041c0025070711403400070034500c001c80703095840d00c0c10800e10f211a605800012280a010280a0565280c5c014005c0e607024180400c0d458028408100004610100e00350b586044003440d40503003070030708101900900e000d856103250400c041c410005d1000043c19081182c0f10001030030004251818a90002002000c1a078031040e0054001c00c01d1015400c000308540301514070a072010001c80e151201030100f034044241030794a400381c42003000e01066000e50309a1240701e03114900490b050b8451101c03d44140c020410403984c1d68183c00c0d409a108042c0d002c42404203404d404200308007541c0c85100c1d00f80f64000c0040a00441c400180c841c14480e564441441440e0098001d00000c4180c3c0b00040c02c0303034405d214480191043e42e020403d03070341441950708448000107001740805280f0300300c140100d117161440542502d044000e00b00c009a000c0d4904401d84c10203490710400d2200 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 463466852 1250 463465602 463465633
    0xc06030e160605090f04090b07120e0610030305130f0b1209031318061d06030d0f0c0b0604140a0f0b0f0303041a13030804081b130923 59
    0x40020381c6a52241d00c5210034031401c0d600c201a1841c1d64401c0311603101e2481c15002007001805075407409805082200104403029411800c4020746207003160f820406045112002e5445800503a0502e4a20141e9142000481d104e9130250620b05281c0501c6071480e0703942e0a6035280d00c1c945a0081d03c1140000c1045900120003903a11584041081d028510704054004c0c5010341c0c900318002c4024648001d86a881c174504283c1c042c002411801d0007150f00c802c0302c44c10480c03010a04852581c42840341000071900c1c113124900c2110320142680743d400b032042160745c400e0001c840c000c1885c1d4200d82d8441d880e0110302c50580019000c0c01c920240050300850300d0940d01e013564102e00700b05d80108501001c000d1759407170020480d4203c600100105580214402c201e0804e441303025402103400c41d542e0004801c2c000c0100040c022520140200e031600307074204040b0329001403c0922103034403465480075403150141076004102e59502c2440390384000110201020900b5a00944030328080d0f002032144400681d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 463468102 1250 463466852 463466863
    0x315061b01092d0f06021318061401020d080a140705190908031611030303070f021006030c05040f0608190209090f0618070911030712051501050f070c06030e 69
    0x4000c6045051a20402c40c0064001d070004040280144c02c0741c28103005000c0c10398107640c03485020900104642d6980c03e02500c680d42240d4050060720320307000000a00c000312101410a0000c1130b0040c02d554031a5450696034010010481e6514a448000c1c554045042491341407042404c0d494050f12900003120a081c02c1d0030800c1440d060200c064414050004004107030391541451645802a03840280b600442680e140c1d441c1c203415200c080b09002005800141001e803d2185508880480e09611803076010345e4520b100c040c216000f040814410b5003400c1d04801c0b040c107000f400128020355100c8299207841081d82020a1003000301c4000740442c0b4005c0002d94001a10714018924091000715194850101610742001100191102e00c0c84078001d1020304010b0195150400508450107a409110b5008a80010024044408041c0d5001803445054002c000d00e07a0000401c0386050015142d1b41d0041c40c040c80040014003c2000007100014103001030841a0780100301b4500c0020201c0c50700 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 463469352 1250 463468102 463468133
    0xa06050a0e06040b0a0207030c0203120c210405040c02010b0a0f050f010201140a051003290903031504110904051e01080a0305030a050705040806040b18070b0315061b0109 75
    0x19000b0505010100e10491038090b0000b41150b401640c41c001841c0a0701c40301800302e0001e406000d8500c8041d10041050301501005500c0000ea80f00ca8151911941700b8000201c01540e800c041800280103904107a444500c01d81070300d000010f031a007207580015504000704e60020588031403246040c8094102440c2e400d002d45404e00080c0101c2c8185001900b031103900034440c1c1d0980356a9400194080c9580a005004540060031052102e1038040f41107441c5401c60300c90301030380e0304045c00b250303040300004200d82c4114010800301c11402c0c2c20108020142a111426a02188090000c036860f1360340d80c0300d01e5000b098407007410b041200c0982942e0107510b02c16401560b00390801401c00307000c01e4010f411a07a01c907015a50005055840c058252100d000ba90800c0d660307481000c4c10041045581d00c078540c0200d03900e14004d601000040202c0d90345010741c0c000d6582034107052002c2048070448004090703020310001c0825040610042541003500084103005c81103a448501e10400c1c003c40d001e42c14540c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 463470602 1250 463469352 463469381
    0x12020106030804090f14010605070b07090501080601082e08010606052b060b03070e0109050901180e120c0703060b090f06060912011a0a050a0f12030504080a06050a 72
    0x58624588502c200c9002c1c1344030341c10900d501c0c0c407641d183c803800d99403001d510b40e080700c00c1c8200c0c1541c40b2000140590000d0a04940b00503c0c40040740201e80109170080490350142d5841c1c3d0107507186401100c00c0080070341440001568036100b03056540d4415848218031203184240c00d40285455240740c01c2d9600ca611481c1809010840d030390070303d11035030f0210401c42e520130002061200b4100010004000c00c0c6c1c051842c2003004024480d49079440a0103540c049400d82c1ea566100c3d4a402c02c00c403c0b50028881c1c5d07148021010b0900b04000465040313503000a4007013040c0c0b03114048014169070240e006441216503078118081c184200046445641c000c0304090700d4440301c03442c05c0680904400c0001c0c0000c4d01c104004610200e0503074600e2038404202c0c104800911001d0346021000074400840c00b0642d105a60b118404906401e003d40d80d041102ea03884c01e02510b80340341103442c1d40b01c2080e4000a400f042020080440c0103a070400c05091680d102c1c1400081c64a040c05d1120704076109001e22024 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 463471852 1250 463470602 463470611
    0xb03162d0b0417030c070f180c120e010b15040e0f0907050f03102a080402060304060b06280f050a090614090d050304080c01080112030f030e1504120201 67
    0x85004140150b500391240301410081c200500c00c0c9444c034500a820000da0540306441010a9091600c8051000c44092024214041c00700e40c1e441420b9490302c1c1c4118000411164111008801c180c00502d20011ba0390000184216801c001c504418042c0a408104403000a0b04000c02190f0001042c0d01c19a01c084850304c6013005038829440d00f0f0180300f028441c2d0800c51003c21196402d004130600304006240401224454607000d000d54801c260360188029a40001c032031a29001e09041c9100365402024145195a503a90742401401d201d42040e420102c00d00121721150409c40c3c4a0385040890304072070400300c0301c00c0700003803541c02d49500c400100034003880040207081d04440d0300380a880540c18501c80004c2c100100d03400a010386480658000d080c807441005001000c0000c0c010b4501e00d00c1511000012000151080d40080c41040404010414502d01180c803480b0754060180091070041001d0804100c0c492a21f0f030f40700c04115400600400780410000c1d10100094164100d0000f0b10 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 463473102 1250 463471852 463471859
    0x50a0f0203070f03080d09170a030b0a060c0b0606030a11070501090c0f0b1b120d020d050a0e1504030e0a1419060e09060619050301060e0d080d0b03162d 67
    0x6280e0094006c9001459190841c20003000001c806a034148591441c0c619112880c0b014002c2c00340c019041b06034011001e00e40041100c0c0d00c03c4000c003510719000b03401c00c41251034040c02c0c04080d6100030907009001c0d65030080d100280e10507034001c144441c090710000c02e0810460803c855003415561118951030007a000410030240b011003524091340382c00c01603440d440c08200045040602c0000324800c1c50000041c10f4110f803115501410701c20344104420000b0783e0f10054079408481219000031181d41c0100d8400c00b815007003150880e8400d20a141c18800f1181440225142d40410303000b0040c9104543c5880920342021400307080c0c17165180c8080d180003407400501030110325010b09075a000b441c0b4280051180e44581d81181c01040720709040840c1130191420081c400d0300b0a0140c0f030f00042c00003100c140c1da8541026200c5490f5008103e061030300b06555111001040e47c110801c0d00360044011a03104841d0300384000000b0003001c03024031460030220000380b09405a0454195a00740112000e0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 463474352 1250 463473102 463473113
    0x6030f070302070c0b13030c08280c03020415090b011404170712030906020d180b03180d02071508010f030f0c0e160e18040b1003050a0f0203070f03 65
    0x540004050078010781d00e00c1c3c141400148015560803031601e40d580010032100310200c2e8660358044034010284054035589440540e41c9460440e032807071130210351640580c44d4000140700406083d0b4841c044580b425a52035000c18151048102c0054680c01c101d0700c20050605c0c18040c081c000740c82440d00882d01c20520a9a42aa020303a000c1da002000749400710088403503041040c0d0010b040001194840c108691800501644080c001c1c200103002c1d9044010f0100c1c010074060342c6909400751111602c0c0e003080080341d02604010300c4007000c2a030845000300b02c4c010911450308610a65406000c215041140e824400c01c03020742003004001c0700000400c02c03541050380f0707002625407104440030701e00218209034144580c0390b00402e054050320f80c2404140c144041e21641e00f290039403108000c016401040120f89900c58000032040345d020300001e800501191031069102c910800740c0c040c06512a11800c1c60025442401c491b0020410260002e5140401892004000c501880106c6c00d085a691 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 463475602 1250 463474352 463474381
    0x3120c120a05180316050706090e0403180302180402040510180e120a02010c08010f030302060609190e0a0606080706050f0901030212090607110106151b02150c010b0603 74
    0x140c968036540c4003c21208a41009804807002003001100d8840054545903940005c0e00d440071502e13440b49050000b001030042c1410b90490f06501e031000c0c03031a61180c4055422403407603c2c42025245d128000800140d0b6054030b08078042c0c0350400c106403180f07068414002201c101900060308030b802080104030403c140b0f0302d004108655290301052281c881b411261030145d14002e0305428010224a9603031032a4154811059520b60b59903086c80c0c0c0e680e038851820568514000540180c00040020380e4a040c19101c00e80c0010002c0355980b144120010108110b03403c248911140d60090580001070060341d0007220090171032000a403209070300e00440900700d84107504070322240781c03404256104c940c0c3c06031b4150b03500602802c0d0001c040c0d10b80035090a40b180000c031002c41c0440d0200c1240407101c101481188281c41e071070500004078410442099900400101c0d00c612103074000700c00107005860380d4203c0307070380380602c0d4103410b80b52220824031071709443c0c10407103043c0030700700c180100030103040c1e2b2406c1f = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 463476852 1250 463475602 463475611
    0x60f010311040306021912180b090f060a0c11070e0f0c0d111b0a0b07050903010e01020a030608190312020c0a0f050c03010c030504050a03210e03120c12 67
    0x80c001540419585000d20300c0c01140c0c800313400c113131000c910159940c004401c41003100096681d0701c41c40d15402059101142c1c07003104503d20160170382da1004001561140340d547c00c0483c04003104d03440d070419000035180c400d04481c0d02d0403180d150401d044105400c0084c0e540312020040180404504089802c00c2001c4003d000d180150080e4010070a245014401c6400c1200d020b42d090145051402618200b40e000c410b0030540880d0016620684150109407407401e10b40c0503000c41990b880b5100c08881136001654282da140d503803060100200f0200b4030041c899402c860718041420392410410b44d00f80b841000080000c03191707107022400000d601480d104011550b91400580b100d040d48515842c0802d4400020014200320300d44406001000030001d80c0000210000e22002400510807416201c080d5401046507200c10b0b8640c00003405040e10200c84c00b081600e100e0071322058050081543c4141c61030130b040760800111030244040000c0d1307030b030f902501040c442880d040300c5030b031040381c0804000c1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 463478102 1250 463476852 463476857
    0x1e0617060915190c080103020a05010320090103020c07031208010e040503041203120f05011406090109030b060105070b162a12111e07050f010206070509031504030f080c03060f01 78
    0x2c0014501d410029000c00f565001c0c99040001c03481088015168120a010036445040013020000c0d0f198440e0003080c01c100030f1103010090b03c8001d008c0c40c0c4200d401c242c2c141d505058080c805807a46403030170410500250b0007040c030300c0c1000000e5003019080c00030607000034203010740ba0b800300804602c00104507000c0343c10a14003500e0b54203040c00d080700c800b4040e00e10320a8842c01e040c40340040510907040b0794141c8a0145103140c0030718017041041011711a00c0c0320a800310f04080c0301040401c10034083d0960101060600341c0c6498aa0750324070151260845079141000008003000b500c05612140c0307890000700311204216103c156003401c3c1004080403d0042001d0103010300701c11164841d801a180d07038942e1408a0b20100041171020001b40b03031368601c1c0d116910404200003102d01c3d09203e0110200012380141c80151902c44049900e5400045961b07054881da00e01140c2040800d604148210301070b03503540c01c1c003440b1483d0040c00d401029100c16588402842802000e0ba2000410050b07000e090 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 463479352 1250 463478102 463478143
    0xc081b03070b070315210605010b090a1721040306060b03220c18110c0703061506050901110118031115070f11010f0513030206010e0c03041101031e06170609 69
    0x100b259038a06c180c0084000c141c9400d0400000d00205400040c008101d821035000708550b0300c2d540d102400082d500030004050b80001e82009070082d564510f20454030080c40358518194503511020244c402d654440541054008200540c0b85503141d09280c0741f00441341d9401c03c040c59900d82c081d10180078052100c2654032400d025541c0000d81d40107446590240d03184d80c0c1c5692555207203540f40c0205200c1901c0550411054020145a061900c03017559450788460341081240c0d0300441da403000385038005020f59a10f100800302c0703015031200301200b10b1003a502c143c4c0f0400020556402c0000004002184030744c0407040c000003070342000d0084a60b0f041494480390100d014030706580504201240d85058500e44014014030552007080c21000390300a40032941907981e24503580f03c007140201c80610036187d0038404070740011000c04501140c54014900869030f4100c00e000380001410200300c6134400d5070750362000c00c4814a00460b604840030a5409841c0e6860290f4006880320701e66050410b40030b002 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 463480602 1250 463479352 463479389
    0x1203110c0a030c0602070602030f1e07060f0b1e220b09040b07080705120c0f07120c02130902060313031b0c0e0115020a02010c081b03070b070315 64
    0x412400a550100a00c4007007015601e0401080600b040d0103610014041d50002213030260000088038086124580c556140c00740102c3c0d000c40414020850611a000070841c5c035010900c0d83c02032130949900036400080200c403480401c90744240317500d00d09095402405500000765100c0000024000c0444400a206500107244100500101c2c0b222540b160300d00c4244418440fa11071601c0c41840e880d1a06605501c0324a400e136aa030040b450035054468481000612004e252405041d00d021901007641c1000030641d616103840a4002d4004001142c0b5500c8506500d005030300007000c0d403001181044038246035000b29486220041c102d4551205504000040501ca0028a0114500e500f81c0c0c545854561800e480d422141d03104a0a4416045001042c0326280100501c035105054005003410b481c41d60064a11040100d410b48800c2018030145c0c8003203040c030034008a03c0d00c1b100041d50f5541e000b03280c882078184001d05000205458030780020380880303844c500f0600361100000f01035003a941 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 463481852 1250 463480602 463480637
    0x140a060602060f100b130302030f03040e0c220e06131a040e0c03061f05010305070503072d0903062004051509030111030414060906011a070807030e090a061203 70
    0x3e5005c1c1c111010002040428001030503030050659100720b0a90359200d0704100c415540703008902600c26040c150501155002006000900c0358650179544c84440b6102e0b82c0003180428056031081d640000d00c03500308003040c80c1406456042014580c0c04110308004100140c0710f80e55040310450040e5030b074280341005000f0070401c3d000c0d0b201c4018225082c604d04106080b001710750002c00194040c4a5080c0841c1f19802400780e10f204034010380d103217400d503170700d8880894166218100d9002e41c40c910b29a072242a10b6401080b8044155548841440d54034500d801c2c1c4c22644021802c00700e400c03a080044042c00d500030112800ca90003161325002d00304094483d0501032007900c1540da490740c42e10f02e0b140d44120202005d50720450060241d44442d101c0307860800d498a00846201d0f5194004400500075041d02d6401010b000199005147c00e003401561201410750041400b0b4020903a041c1001c10145000c81d040c6030b00c032040402c1031101078a881c088201c6070078642d000800707025610030301d800101e6 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 463483102 1250 463481852 463481881
    0xe06100e011b0f0303060314150f13020a0303110d0201020c07050f030f01090605040209281a090108062215020307140d05090d0f0c020d050703021201140a060602060f 73
    0xb0f820940c01003450901d850301070000c2c440b62004486404614501c20b642110100c0c45207001c824601e80b00f542a900c518091049100c01010990349918a0710107074050703264a0380300340103036100c1d89400c8884074442c00820300d8035590802d408116801041510410000820541e04a40003078802c240d412102c60b00107402c00c0862011081c1c103611b0b00502006219083e00043d015600a8a903500242c84000c0341c0b01414210901c1c40028028105542d8442d010381d5000c034440e08925510714243d40c0c84900012002e07503003a800a012a8021810b0018a0401d0110040030b40003c80071840b2040c1190f4540503c40c040a44070303440b80354040000b076100d03406006e482404107401180c82d5070728615504650000e0500380e0f5560700c80d00c100c03142651801d0044d5000c2403100c40c180c0b90051201d00c0d503401c024100b9900d000c1110640140f040000058844a12880038910000008a4408600445210480f0008184424040c1400300402c015074020a406803c100060303808000e9548050107140c3c1030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 463484352 1250 463483102 463483157
    0x1403040f110f0a3318050103020322020a0b0403051b030a020a060302030a06180f0f020306061e0c15010e070801060f0807020a0203071503060e22050a05010c03060e06100e01 76
    0x301c0c045403040d800c5944003010940d01c10310384139141c61703894a6200440880c00215200002100c200600200703d0700c1861001742140e1004089050480e1281101113064026174800ca41c40d03480411001284803000d04601c0161000782c0041922000a0f000240c0818140c86141e003410340c004082140c2d01d00a4114034040e220b003690f0b80e289000c0c4207203100020079001c5c0d48038040c81e03e02030300c100c0c9d106598021a401008001c1c07540781003068407910752000c101100ba82c00c222500411a001d0800400e0020b0242090700c211084103030761400c8005120340c4401000741041108450040c0009508141480c500c0003191605024965031848181d150150592010b9454410f0741e400052014150b00691145c1e0003c0c1d60030700c0095a035903a2a071924600b03540540d03148160811f84646100d01400c01d01c84540074908075100590b039902d6182c21130f200c070800c40000a440e84010f10082c0b01c0302d840b40343c0002058444080d48100a400100007515041206041003542e00e51110414000d42409014 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 463485602 1250 463484352 463484429
    0x51e071b0803061201140604020901090503060c04050a0e0412080405150f0108010f020304050c120312010e01030b0105060a0e100903050f030a081b0403060b011403040f110f0a 77
    0x40803181d0509590030741040b1452807299907040320b500c4078010113000300c1c1100904540d4034001d944540f010003020350411608141000342c2480005119a0204007490003071140ad04919519420304041c0159003010b90811220311941e00c007800700003000000c031885400c046140c07080c02502e45180041c01d00d000e02002c071015004500c01c1c030264207166580d4604840301326000300310884440c1225004d0b40000c480c0542950490222400c0350b040400011421580c0301050360700d80280b4840d0300414680a07004402d1151021005004000800305440d026000c121645410911460b80c000d25900900490900030310341c00c0e6032446040e01a07601040034580c0101610354006140c1d207c2c550760b030008400600010310160101d001402050407450902014030945890a4210b44600e0050180c00303140c80d0410514210100716541b0460185016071302c1400100c1c00c0c8007090802c500d41c2074a45400602c9005107841c1c0815940c1d40b4000e01040301e00480c0d89003040406c60648204900488032b00c60362 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 463486852 1250 463485602 463485647
    0x60403080703020c1207060c080307050c0f071401051c15172503020a030b07090b0a030e071a0a0c02030a020405130506011a0d02032703040e0a051e07 66
    0x1015004078440c4d90b001415120f5120b05407448102c295208030611520b00807501d01840d410120b8001d0001350b80c01074480c00e105141a10b000c452074505802c5480b1144030350407001d8140203640400c4609007558400340390032400c0c410f00e03043e418240740344192280c072010390356200000b05498042d01840107210880c1100c0700402c59145241d22141c01d0302441080b106c0d5030941e646d84c042d0382e40d6940207894002e0001038060b4215513a00c00080c401600c3c20090003c3c03904009000c1c0c81000c010710b0004010743d40410121140750100c2d280020300e41000d0762100d20503101d200010100010f40e84c0c0e40c80e036440c11001140441c004242045070b0410080e4006080c00100700040d00c00301141c42d8038a10804c21034000b0782ea509038110014000116015a6640070080d000c038981541d0095a00002001d204180110034140303005c0c491415081c01d2006500046010030400d1407441419078410b40905040c4064034014441c0d41d0880c50074002240e4030a120300208800034070070700480ca207100300c00304a800c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 463488102 1250 463486852 463486867
    0x9060509100c0219030212011406090a0e03040909030e01111c0c02090906060a0806090703141f06080f0316030807050f0309011a010e0f100201140c031b04030b04020105070206040308 80
    0x400442c0c00d00059000703e801035000e80c00203005104001c9e462070792402075000d64891030204800550041d0030302501640f1358401d22400d0405200510080c20f00850018210300716181c043c1064000400c154180040480d061801a002082c080d5110031858041c600b65071407460142c49143c13406402a40150b80c210410040300300c00a225809100c04968000300f40c0d17522041c4641e9148200e40741d80c690740101e0410800518604480240722260340c050301d0751180448a03100f08040c511181e0220036859540400000d0003e1106820083d40580a145021010300700344400c810022401000c1001c200001020244034400352100e5901c000c4019541b41415440759020b0b04605003c2841e81d84002181c203c1c940c001da03034001d031380708000d000d00102c1456182040b41c4211040031410940d502c43c0c1040511100d080c034120311540718126000e450381041140c41060100c120320000c1c54034000c10090010440d40e030443d503481030382440c041c4d980310a90b2002c52418021940000d02e51400461180d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 463489208 1106 463488102 463488139
    0xe010b070809150a1d0a0503030f090616080307030f02070209131106160510090b150d140a0212030a090b0f0408061801060609060509100c02 62
    0x40c3c0c11580c1c03441c07240d0254401d6480c040002d020000800044240e684500d505200664160b02c800b42410b0200790760b403080f51300304219450041078001a42c1da032082100c001042030703228840381c029680707010301c1707039030000d9503a900400d00380720003040d50742c003d403007a904c0b0f0b50740050004609840e1801403c0300c2154004080d140341c3c90340500c0314000d49924000700381c40d65400001b2041c1101c01d040c243c2c24801c1c40e20001000c207003000716a42c0031907507409216400c040085541d0300c042c12301c3e100188030702c24040001070140d40100804601c03070700041908000d080c001c3e242c010a403610317000090340720300c00c81200c00007050b441d0704180091390403540541000494611054646a22010b4007481c0060445052081c01d00f40416050090000c1c080c04d0000d001508141d1050780c14804040c02c42d000f500e041602880c0841c20502400c1c0c800c2449900060300a450b04080754402a100b = true := by decide +kernel

theorem cover : BRFrame.Cov 463309352 463489208 := by
  have h0 := BRFrame.cov_init 463309352
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463309352 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 463309352 ≤ n) (h2 : n < 463489208) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
