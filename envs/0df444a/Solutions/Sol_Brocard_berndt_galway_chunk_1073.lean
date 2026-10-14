-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1073
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:07:15.988626+00:00
-- url     : https://prove2.me/submissions/357d2966-614e-43f3-8622-ab55ddc5bec4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 192805755 ≤ n < 192985611 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 192807005 1250 192805755 192805759
    0xc0e09031e0d05250504050d1202010b09090a0302010b06040605030f18190308070e13090302010e060a15080a030909022b0b0a081b0904150603080d0f15210c030606080610030809 78
    0x20f00000d80714400c80c010003640cc0407075440040542445480b0320001880d0305814425002040041c032807104105ca0f074040e500c1500c1c0081e200b0400a01d0114110307450030342080000580040031110440c0031414030036500c1c0110203160342c250300d1806040d4842d040f0f640203503190400448074095000030408890f08480c24050050701c400d00041014400d61002d00300001190660f1800c0c203151b110a406814074011040780040348620101d0704040100e0100e0600e076042c0c0b01c86098514290107040a0740052050647c0441040310f41c00700b00054286060030924402c50010b001b240f07030803c000030121a9000800246c1c042d00d9002003600b100e84203022084d404031105000742c1d440340340c070581341060300f4401c2a00b103052150020400000b10098801700d07a80344404d114035944210707c4000c8a40102030440703086000c01d410003c80b450004011200d01074584400000545900c03007613079134060b5500031078085941c0e98003000302d440c0601c031658200400b2003294041d039240d138461081900440341d07680c0c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 192808255 1250 192807005 192807023
    0x10503060a0b0f070201080108150a090215070b090f0102071703040c0b040609051516110a0b0f13050f01090303030b03010f0e03070c0e09031e0d05250504050d 70
    0x1000d9507607030a1440c00400c0c400c850a541d070880c0340c1c103548080e000340d84201d01180d007040000c0f0391840f0100d18040c56081d04101001c00f980c41030080740140c40360901c103980142100103044100e0903142e0081c2410382c090070f080c03222410040050b5142030740486254410741d00c103120040001d006d294405450515102100c2c0d100c2e103c078104008002c4256200c0301130490009400112076820540d4407007220002c0303a48e00050003a0680312607603480303641003044020194400010008485803d4011254400f622400c40a030f2540424840f95202041c0241044000716000c004103c074400302d8006003000f0307601c070f000c002000d8001900080c450300005081c140c0301d03548072420f5102507102a81907140c001040c0920107802401d1500ca07407200009a840a86031200801d2109a03288424003407110100154a0407001d0032800c50003030f00f81e90070800400002c00c116411031004d800740d10300411100b0f103211440720f0303030211801c070902070b039040b079014000244420442903a83c1644024096088030b010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 192809505 1250 192808255 192808261
    0x160c03030e070f031401050a090b16020a0209070c020306060301020a0f050f0d020a030507081b19050c07031406161d01030902030d11010c0503010b0f0c0717011b030507020c010503 79
    0xc5402c008a54024100c3d4807007606001090008240141861403041ca00070086911442420030030740303000c81405072503c44078030046204041c50440c0c10396001c8007441510020b00b11580017a0702a0810f8130b0242c0019403241c2e040d000d500d17051241c9508500124000c41c60002d4009018010811480004013032147c0400d2078203d01180c08115500d040c0e120404541e02c014003100a4020b00b4255210400542688001000c8042002d4a003101d1448030303800500700309421440090720000c80d03d40c1c1c3c042000500c21070a0008c020009500554802d4113080032100301800c456203419002000004150720400000300141d420850311280c500d4048046100541c00750b006a0181ca0b00c160025090300c102407034109441e5018160100d41000c1000a000c10343c00c0c1c0070111a41e00003030045207105e11041040c003001d036120b03c4c020302e9141c19041c165003030a5a0380b00464078252602c0b440c1025030351601c01d0b083c000604422400b00920a60404101d02e0603d42c500070341c1c4a03c41c42c04181400400004 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 192810755 1250 192809505 192809531
    0x91804021c03050a0311130e0703020409020c010c0e01170411060f0c0c1e030304140d05060106081f03050d0f0e0d080714060f130f060e03090306160c0303 68
    0x98a03604200708120309911901c649002030080e03011004180c002450480920611082001100e83c075840c088108010035083c000d070801c4000c0b002c0d21400c00c0c5682080f0016200300380d4000703070030146415400080d01c0340c980c0034080c15001c940e510503810004041910046070f0218040076401c0764001040c5200349042d40c0100d107082c450100e40201503000880d007060160000036a42e8012141a02d0090f1688c3c2e209980c842c0036004405499410b070003e0009001d46081511840354580d4024017140100d40c00c2d80b80c040c00d24600380c01010018182c40101f10151444852040c07520384000368403540c103803454680780e40704c040402c000000c201c0800f191802d031500c14032140e40c1d0380500410300d1040055901e003030031050344010380071030b9040328250000d2032450010442a2107140003921401d180e585840c0050300242c64040200e50b501600c2c40908003017121449008080301445000b5666650072030300b051f1270001d0082c10307084410f0280b031020385c0d91782d8840e5210803c240e050a02003050307910042 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 192812005 1250 192810755 192810769
    0x708090102190b1b31030c0e040b09071d061f0924020d05130b0a080103020f0907020d03020a110f0319020606060a0f0e0415060906030209180402 64
    0x2082d0036450540e118240c052010041d041800f0345040c0724807180f11010307201210520300810b4402d1203050650400215404205a241c0440d041d41135505918030ba165030340d041c003001003a080300d1502d0306038804000c10084004110340c0c110b02000700030440285012506a4940c1c021020142d028010001040494803440b0002c404901140210055040c5070366008048104a100c0e041c10001d1503078a404602c200e5030303401c50386585217a0103440c17000100f075800c0d2165409003400d19012a50202c000038211403043c0900302c1c40601d80d03200a040e5255004000007c07181c00c5c4189d2150340580c1c00d0022264000464840c4840b00d4103001d603c03089021000c2d100820b0069030540c3e640108103140600e49804401048101080d0f00c0d008292209050102e80d41c5004441054100f2400c01c010340400d070151821840d4288540761000320041c0940100342621b01c0240400c5180064180501c0a2900309107000080d2010345000c5040400740d800082c40003d0200b00300012840020100707044d0f4803989 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 192813255 1250 192812005 192812023
    0xd0c0b13061b050c150615090a09140106030b04020c060601080c070606180c090e070c060209060c0703110f010504140d1407030b0708010612111e031608040203030708090102 76
    0x100d00d0b04420607030080040c1c1280c3c400030040b4240d00541c41101c4084904402d024041c19001c0c2c0500c0c998a91103071140a0b503402415001d070310a055900016a40c00180038075940465410110003035540350000250580e60495074403071003940107111410110b100010020391200c824601042a40c44200440c1400d01c03c5020180405081a00204103002407000c0420501206081044ac4800b010740488181c520390040c2c0f00c3c284010004101514801d40b00d89401c3d174090a40140340010030000101160b105109680d9030f0740156000300117000c5c10000f0510500000e40d810700c28140d624000a06a101e5805500800a084d11046105445200c1e10000c460782c400d8a0800e00e4800300002079076100d01c0c2c4030807600782030200300041c1d816104099150417a40c1c2034490034001c4a8490b240c07409064601c0701e001e000b10701400301d01c61100e6000715181e9000305241100e541c900b0030700c03014803080c40e00300d41480c10710450400b4400144c80c00400c4031b95158000b810140c883c404040101e0400800c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 192814505 1250 192813255 192813281
    0x60405010b0d0b3606030a0201020304030f06060e040f03140306240f030c1308030a1205040302010b0a090905061308040308070f0b0c0a020c0405071b080f0703110d0c0b1306 76
    0x130412400701d0303c41403807808500e811030840380d1010396900f020107907128405d2200074016001404200000303481c4148610102d4840c500115101d5103803c0c680311a00c41c2200d013601c1014144211a0501d41c02100e401a1055882c0c40e0a10f9840c001011610004a812440d82010b00e4400350030802c1e01c00005640c0c405243d004500da0ba410820031904140d00403101c1007280c002040c070f002802800000845003422810b4690500d045c04000c0104010100100141d0555489481454075590340a140c4c0c0007400041400251060440c1820b41c90700c1c40040020002d250780105050114403803200303a408407684402055981d0030075190030044d40113000401004001000148840c001040d4007410b810580c079800c942c082d840c42c43c20032003980c8050710308402103541802110300d042c5101c0440b00440780143c108a02c0c0804001c0c8142c81548039807401d900140180c07821141c44170041c00141d5900c600392811040c00403a80d11044c60081d0040e01007040340c119407805804000842d00f280c0c0c144514 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 192815755 1250 192814505 192814549
    0x3020106030c062a0507060503040813030602030901060f030804050d05070801180b060409020112050606040302090406020d0c05040b0f031b1306080622020705010b1f08060405010b0d0b 81
    0x92407001070416120140921501c06032880c134001c1039100071441041c4030350000300a1198034a031038000c1d62940c0c00038009880c0544100807a149800b06001e600006600c21000180d580c60807407501d03801c450190300b0412060070340c6030042010034024800c2d181030b0740c81141d10098044651411620f810025031200d2125400d144821219043e290a10160315002d400022140c1e9903003400c10046030f07180503000307010441e24002004401c486910180c0c0c040d00152200e8602038807900050000d20040300c040350aa81c00041a02c2030301114011100107020504159081c01d0800c9405840350155510990283c0808000503214110064003e000034000b650f0345559160500300302c400c049182c2c0218004500d240303011a86500f0000355240040e99920a8126081003220242c0065402480140c4040d0b4841000c110107507500c01e051250100b140c2e080c81c07803800c006440544018802820705210307524000040141c52108011200b081c0000c120001d10568a94001070074040121102c035040d81c1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 192817005 1250 192815755 192815759
    0x90105040807030302060a110405011e030209031e010b030a02011d010318080307030c0203030c0405011b06050c21060603130f0c06021006050406050d08030c0715021b0109051903020106030c 83
    0xc1c0201b140d50090040c140e042c84811074001002c81144a903204590000e10102d425090320b40aa06c0303101510000c80c03502524141201c00000d1030011016a41e03184040b0411b1030704102103091140000703020059002d403da031490b5070006807840c40c2c0c403941101d441541a9240400e030f0311030b502285c03111203509a9040e00755030a04088082c1c0c0c100300d900381c011a161900b1036280d0360000054a1042c0407540c00c00c0c0c6800e09200c011501100f1103070640e00014580703460400010154041e040c03060100c176030500c1d110861120030711a1110741d040440010070b0000306100e81768868004490740704d40b50b40e00610940d0028a068801c2c40e0307640030068500014000080b40055010071200301e68041580300348000c80c0c0b1441040101e81803842610790215201440c1e00000c3c010401a541c02078540c00d4182c2403640c03d88604150360703101055850055400a50b15044a4140080500c0c01c0e01401c000c00c10500555511540e9101c0c0103035400100e114441c10004042c0f007500a10042d45e070041010007016 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 192818255 1250 192817005 192817007
    0xf08040b04030f110109031e03050c250603060303080f04140d020c01021204150f090f06052116050d0213090e0601080f060c03040f0503031f05040b150901050408070303 74
    0x2034003504003141c19410658804d94a51b02c0b6040001c29079800000c441d4140c171005c1c16886415011000880c10307c00d041c001912102c10030700600902c01c040c561004c0040780440c0341f0362450042c9400100030325107044020300c0401d901079482c0e0b42c003c005a44004050300d4038103212160502f402c19042c1a44107800d2080701d83c55000c40c0040c0320f0042038003107902d03040d600d45294845001d00e0040b404c51194203901c00c0c0340b0501c141c24a080c02c001c94203040f440c0b81d0300c409507048080303980d4220301c2c0814000642e01c68a20100294010b54030160b2880b141c2509002421804041550480703808002012a140040c0c04456046581c219000d5103048019603403200c1c02d0015040f60060300203d03000d903c000051100300491104210203146000c0c00555031030224030302e5a030f00040c10a503092005206000c00040b800c10046d8001d07031850480c01c40d414802e45124030102402d801c180d0289007094242000d603101c0400d0390590075a010b60054642c2280300c0101c42c02e0143c2c4d4400c001038415548000300345 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 192819505 1250 192818255 192818273
    0x6040801090c18090b0c090111060405010221060d02010e01050f07050610060f350c0310050a0501090e04020427030e010903020127030b0907061d030a0f08040b0403 72
    0xc60004144602d60b19503019200f0807100705a00181c80c034031124000410300508031009090f190b005050840c00c1c0315400864030700e42102242c04980684d40010070410724603503440035034005c05610307202c4c18080c5403140224105889024009040c014889512042c03680210151060b1280720030219403070704100c3c1400c594940c02034580c0c002040a0801c0030607240c0c400c003100c1c1c1c60f407a050348074900303114440c0201e40381500c01c880007a21036140c0c5030052a026001d10a5150044404a00040d144c0c105035200d01450800ca40c4401d00c1140d17207140c00c10181e40c02c640c0e00c804946144072104660307a51400402c000e0141c00360068030721aa1401d006500061b0305000c186064001d41d20500c0d5004540015522102540400b1b800314559810304042030101e056242c91b0700810800c2d14802e1640c1c2c0c2d41e040b00140068552800039002200140a400d42c8181041c842186065a0813001c84c0d0101c04262548284040500000c0c080d22214003071000010807500144614107141d651582c2e281002080 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 192820755 1250 192819505 192819509
    0x209040c050418140304060905060d020f03040605040218060102070b0c0c03031603080a02040e010e06190602071d040b010b0f130810050c0306031e150c1b0312041106040801090c 78
    0xd90305500c000c2804180c1c0000a8500b687e1003900d4030009181000100041500440900c002e52a0200200d4a80140f800b0140d401544201c40c08946402c003441040003010700c0401c422000456041000896030b03002a154040310014204940c2d5514010641411700d82c8495a00707415100000e135140006510001c07818145010f1390f42d900c05625014100c005034410ba1082c55519000d0b00c0041c00040f0040310100c0d00883d000b840125202044c0324404c0d0729410b1603100102507040310104100ca20b8108500301d803425181742e000380c454501540c44d40d414800c180200c0018150100d880c046c0c420f1000111500c1103010341000784d070141c4e04c0c420580d88407500b44034086907604081c0411820b1040c44141c1e80a08801005049600340c0090700a882c101c590100d0521446118540b0030030400c02e140050041101d505802c0d41d5082c040e44d14038040000c0410840c0a92040000f03000360038204070001c0d081036100983e11043e00210300050114003036500104001d518140001080007031020742502 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 192822005 1250 192820755 192820763
    0xc0a060b010c080a03020f0417010603061a03030706090804172a01050307030506041e02040e06090907140118060518040c0c081e07032610030209040c050418 69
    0x1100c8510040110b03195405024000e2000c0d1050019008a6000e50013511140b2600481c050420743e0b640a060304042a155101800741d545010510a00c90f180c0100e00340303100d010140d1042c0b0440741300403c0d50780c0b0030408040c022036550403c0d5010084414100c07030041c1443c40e08608400441c1c0c00441c1c1740c0130201c04105100000000c0140310b095484c02c1c019040e00140c480780d00307580d00c00001380d005e400001c0c002a0f010307a0750440b607092102030400000c400a0f003403d0042c0c8807800d04c1c03144011104007600e040d21540c61f400401c07040250029191054955a100e120003440308440140ea5500100b0301c0240340c49440200414100c0c0c0c480040c0061300d4071254490140d080c484184400c8510003038603400020031280d2450003080300ca400600072505581001d4107544201210051550881c0340101c1c001003040031002107132081c0d4049002c0d505841074040b00136080030002810046058070000b80500e16910005d010700c0310415440c0c00030320002d00144240922100034801503504442d0881d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 192823255 1250 192822005 192822011
    0x1103160206071403011401180609061214071d0d0b04290109020a051209010b0a08010b011e0318081c050f04020613150c020a0b09030d080703110c0a06 66
    0x529002c2c4503400305440a03d4000c0c0c018a181d091540380103608041e0300199040c49583c107208480803400c24010300040809541d11181107092240081c0100a0f4944031120036090140c02d403003510a03003580a0b04201e05040c0400340d051101552601c0d0410000e06582c010100d0b060441030000448081d842603120320300400b031070040d01c4c10700c2c0ca0b4000300754000c1c07241f014060010700482c00180e004011940f281d091a90a000c800e0407603001401e07040b0b9003041c20741d444d1080c0d80e9150800507040009460880000e020501003080024071290032404d440d5000e442844050341464025807200d0302c1551103280300c000182032410503c56591282007190130301e1200311604489041d84d44102801822001c03195074550701c0d25000c200d882d030464081401c1a6204403030000340c00740f141d1440785c000c003002e4444015241d22401007007400c0e2103d40c4a148000410807408405943c0450040007010300c60600311210348400c039048005290030100d0600c1094001081d401014000a0300c3c510144109014 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 192824505 1250 192823255 192823261
    0x103110114030906071107050303070c090b060a050d0c030e1605010e010c0b01121b0e091b0f120304210c05010c1502071a01120219050109050d061103160206 69
    0x1c000c1d9200c111141091a0005404244c2e040d11030b11007112000511000c44943e542c07104006400c0d54000001224010a001d4041042c200c807400b6050f4a20000c8030564209420b030340b001b420785d02c58262411203450759244071104140c06075201036500044042121030802c0c040088020408413801564082400134100900ca9032081c00c0c544186503200d0b1058003141d2070302c105464254201c6c08111001c001c4034807501182c52500d030144006041880912807507040040005007442020b034000e20507481c0f0074001c125140c450500c1d10001c804182c401c03070b82d00f60315100302c40c0c25030040c3d4101408143c02d1a1082d81c0e4008a603007042483da01402c00e280700341d40c0c1d806c01554034510036580100721035541045404641515406041540d02402e40341584c821501e00c0714203170380300c26001044004400c0c1504015800c0c120841148a02c519610410f428104000600184040c1c4151841000952071300010000340e0340001e0720741504545070944904058010114405240c40d50790300600c102000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 192825755 1250 192824505 192824537
    0x21011040503281407030308060d1a0403121e0509010c020a080a110d0503180d051c0e03030a0605090c0403020d020f0d0209090d0f090b1603140301031101 68
    0x80394100c0d08001c0050203a00c00310410022241003029190307604000002c801404a24a01c2074902c01c1ca00e04000780c19510b0035442c028050038805800079000d00ca445105200090000f2205030380720b0f00080d01a082951a0f25007290120014011101020b0421816080c02645074030a40480701640806100319915030041500301d94191410b50016800760f0595408580c07101c0042c05541064a008041c121001c14901e1600b10b42000d81c3e80001d0000003080005280b031000501010f0036400502003205000c10020400d020f030003034010114000d1243c000d4084981c0d44408021280c0c1d100b41ea44914010211000031310080c807841d03029848180008041048034421501641c2c0e0080c5440982e03403003a0280304880c50001c00c0c140d0000200022500966252800d0900c9100700030014954082a481e00074800c0703441400340d0042c48080d00d024085160500265816962001c8201c50452034a0904603003a1001300110f106001d070000010050040540c40d010350004282c85100440821000c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 192827005 1250 192825755 192825757
    0x90b0d060c050a0f0215040201050913061d06010309030f0e030f060c0306010f09031718090a0504110a080307060207110d06020a03060608040b13032a1208040201081906030c06021011 80
    0xc075086c482c94441d40000c005601a40c050120184003418443c24605040043d10440d01241c0000440b151820020178004280e2035001e075004000386018030400d039450303901510680902d540c08051000526050066803010491041c9507940d00f01220902c0c2041404210507910681c0c0c40b42c0051007498802c60011300a140d58801c4035444a400300800004645200054009844d0310350754524904c1c242c00d140e6038208915004017925180003a450800d403a00d94850130940f1030050203040003240400c070302c40340402559065504100c002da619040303458081c240b58036240b207850744400c1c000c8411092008990160100400d191801c209103500c401095881c000f0071280102a99000d100050141c00320100c0c1c0034020380300341060500800b06003074281742c2c2c03003029a0010f90280d180001c48107026a4001b4828100704908000c24241800d0b00000c029801c000d011700700c1811807000c4d203140b071a0136510840c0256006031500804c9500c8420081d114074135070701e0340800b05050445480a00400c04 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 192828255 1250 192827005 192827023
    0x6010e011505070203030f04081b031f0510050d03050406080f01050d110102071a13050f01021207031704080307020f010b210705060d0b03070e0f01090b0d060c050a0f02 74
    0x100c41c0720024204404030340c43c0e400f2100c100e0305400184042d09a0044d4580980301810f410009001c01c00708040001440314101d9034041e2103a8000c0804400d41c00e04950360a80142012030b01080036600d460414034040b2240d4805604000d80d016000c0030f05074171801800c140d40341591550182d071101a031a902082c000c0c0150b50340b1005020701d072000a070450548202515060041d5040741790346039180c2d8401c14001140ea880c0c0803001482e100b0034944040ea480c0038110865643e140b440600300000c0d940d6034160110600e01d48005144424140188091081c034469a1a03020903490149400308243e0001c3da0704101511403026852b102503010b00561589510180c004407d45003000941120003205844040c06401040400704480d11000c000b040f011840b1440440e4010005003410f2511030941d000c0c3c02c04050107001d10007070720040311041c0d04455110101285005c54075001400c0c080c156507008001510342030b040520b06401c040a00182d80450711a0810000e884805036102d40c401c0c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 192829505 1250 192828255 192828269
    0x30303091c0201200307030f050c130806010806070503100305240a090302102007050a03080c0f0f0d021909140a06020a0b0a0204050d080309071a0901030c110d09050306010e01 77
    0x1640440b00364204c200051070340300e286803401040c0e4803580c8100303204480c8184e541d0003e880300042c030000e407030b011901c0c0c4100504064004008a40c5451140303922403038080c181804100d07000012580c0746a40c0325a50010310303003290569114541e401b801c1190012030008225103650800d001441e0f44805109481d0500d07010b80260000750080c82000005200a062601300405014084a00d80d85003001600c2c00a1149008144105a904020308585402000c03080c0000e02004400c40d171860300300c03da689000c0380c04034141d200e2409041000281c00740e1803074240399052150613020403a03400060802102c8090300300c400c10b10040e500b4080301003c140204005a4002e8180600240524038029404048034000500b050b40701c10004550070300c1d0300010f41d110000070003482206031301400141c00910b5042340b4441d00748d84d600c8055280340110201d00741415074410180c42500d0040c290001d02c0d02c40301c0c041e01c407103100002380a0183c500c1d03030007454000e1090b4000460000709080c2c1042c180c3d184 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 192830755 1250 192829505 192829541
    0xc020310020304030e0a06080f04051011030a050a1107060f0b09040b060901090c1d0307210b090604032a1506090b060a020c09040c0b0a030203010503010e0106031205090f030303091c0201 82
    0x27003a10305244810f01a000302c1e0b40d4803170703001400e40413a2580701d07016441d604108c59603030b241020145d11003981c0c8094048550289082814880070711340204940100764040c81c00f20300204007904450041c4600d003125504416a00c08200c100401b00b00e40c11712442040f905201c0030b907202d44102c0e085805c0406440d010626080d45c00c8180c4042c0030411a1025005044502581e10350001d03400b03a203100c160003801c111001d91051304100a504080d9480310300f0000030401c81c0750a48008181413610001c025088000003801038001030040da400b50701d15041000101c000104c03c4d8040e00030070952081031000c41c50003030304030b00790b1038076900720b91310903000341c2c02003c00d02d09003003c101d07002101402c119520000c00100141040e01c290243c0703c0c16002e9100145c4030b600d494241400e5499100e6101c1d0580d24029041c0f0014103090202c0c00c5a0403140f41c610380312030742030002c1145040e4a10f0002e074103110201c100201034070700103110001501240400c2286903c506016400e881155640c4004458 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 192832005 1250 192830755 192830761
    0x120c0b181e2d030d020309010f0201051012031701030c081504200109090c080a18021e040b130b01090b0c0a0201050d090819091d0a09030c020310020304030e0a0608 72
    0x459141c01c912550b40300550038040c1c00d81080000d01d80041d81c180c190140c0c0000c1134100c911741e0406c03c0507028a00c2400244220310b010400210080128080c04c0300c4009100b02144c20325100e000d4002090f0b0080e034584095507181d04140002000500c41c07040a8401c207040c0301a19440346424a000f50342c03092642c12840002c003080c401060b0344807013036030401c000020009120325040c0130360315070028251a4021036041106015068494040d050070101183d8815040140ca03903508103400664940e08440808a54400003009046041e8109034403a0021158502240090784103e400113400d0b00c400304070b0390b0b80344945c10340c2c0d005410070700007240c120320000400755001c0c0d0010840300281c00c800082d400c140b0f40e40e4081ca504402244100790014829080b140c075041103401c409000041d00905142d40c5642008010803401456052030300e40780c00180c0704040c05042421b042a40c010705461070011024a2000250000c03142500011014000d40006084c00d42d4440c0c161a0140e449105a03a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 192833255 1250 192832005 192832039
    0x30a0213090c0e040c03060830120603060105060c0c0f0f0d03030501080d020a0302030a08070201020f0304080705010c140a03090c0806160f030204050604050d1401051008010b09010609120c0b181e 86
    0x1582c541e03010850309d00d0b880034007480242520082040c0800e024000c0d05504101e0103140c9003440580180303000700e108100e0b00c176140000041c51f252541040324001160b2084401107641d2904202e00d00d40c00541d400004020190107400c8241646c000f8821202c4088810500701c2e514190781c480035025800401c01543c605200c1c540080e884100c500000d07280110040803c0944c4e4402c44050750040400f0906904200c0c2c00e0044c400c040d282c900d414030f901c00c5802c00211945c0f0031002c0c50801d0550350b80001041008426540c00141441010381e1460324003004100c170400036807290340303000940f00ca40c4c00400034028401d80c1c0584070040d0007681498101001c0c0b00884590580548983d50001000001c050b02400342e1440380018250340340c4114944406c003404c0d88c01c1c5510b014420307203207400103003e015448640341c1d04035007182a42241c01c40460a00c5c519060341034010b1400c00b074000030400c0d101c002e003001481060505441540180c2c007656412150090b1031600c0a038411100b0080c04881 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 192834505 1250 192833255 192833293
    0xb0d02011b110d2427020d060f020403031b0f14031c060f17030d05180a11010f02011e150e190b0904030203030a0213090c0e040c030608 60
    0x310788200b4a51141c25002030010310180441d460403a1004c0311003c0c1030b2810b80300c214100e900458500c00c00c3c0980c84007058181d00f10034070001c1c080e40c000c01306083c2009560781d0026116a1541107a8204201c024000104c07010390701c0f9000c140d000c24040310003504da0580015400c0e20250308109265034045a030f56440309440740c180c0007000e161100f8040042401d090b0391541c001c650440c00006941d0303250003400c08001e103d6901c03007911240030382140c1c9a02e140110440b02806141c110004030307552081c201100f81a5401441e0b00c00b1700c83d06551900300302c07004020340d00511098a80201e8454881c80881c280e5084503444915158541c180464000b03541d0003075045003601000840c0446c0d150300c0000c0ba5803400716918414010800000c103c1c3c20b025220f410800301050b03420050fa0714198501030f540344006010980307490303800508484007030300d501070070009010310071418442003041e04001002c070302025442d03d10403450004c0100320980a4032400084419032030103070810780400f003482c4d10702d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 192835755 1250 192834505 192834557
    0x706020a021c05060703060f09060b040b03040201020a14010f0605040203070203070f0201110d030f0606030b0901030b10030218060102100522080c01020c0d020d0c2310110d0b0d0201 80
    0x2e0071821090180c001102846011310500041e03600041003071509000c10032000b00390b804444018944041032165189280c1240c007501d0381c0c00303a01ca0b503a45039840100d1816420a001401001880036201100201034203c2c0c1e0164a0744801400640c1d00e40d820030040b480265069409030b80100008000a400420050161030050400c03132098440c0c52210b50500745c40152403000203655001c0d9800c00301040c4501009405646400c004c5a0b60210200c2c3d1645818000600150031b050005555a0f0300300c00e00e140591b0340030b00140a001881410a41040002d0764402e025019980850002403d01e1003030901c0743c80c0307060040310240041c0c004002000d0b00050107070b40740b4200300001540100709000401c2c1240c070560040060283c0f480c802801d0003030a00090080203072a1200e00d020810f658100124003501c0171565110014080b0040d1070150071128030b4800c0c60412800506074400080503103010704400c0c9050015403050420403551340741c55680240800d00908849916180c5c500000e00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 192837005 1250 192835755 192835789
    0x2607030603021306051503060a0e090a020a030b0726240607110310140a05090c0d030504180e03030a0b190b0d0c020303060f1210021b0706020706020a02 67
    0x52003948a4020809000c0c4040355800d460b901c45104010504104040c119004103503440981113003800d60016140112a01c18580404a5600468080d1034240940b03003007554020883c50b19036940340b42015980c04101c0d141c1000c50200e60595641c046005018842081d250390000c0050390f48005844500a0000324071240032200820058036454400c0180a50b5028030004001044802c0c1010328058800813031686d0a400e240401540e05070300c909050b00a0689540441d0a9403140003481c5070241010209612082e00350401040c582c0000042042d10300d280010100c910b00841c6034400d0395000224000b140e03004100081555400c1c1d0320100b82c0300801004211000c200110040d4150340c00e03008032080707400006001c0f81410b0382d4444c0540d40803650000d1800c600d841400220038007004003045010f80e0129101109559007846071340104403480508644414840c0c5a011035a0303015002e4010a103c0c41d140030900d54000180300045414030303401080420051385c01e1185a09070010507007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 192838255 1250 192837005 192837011
    0x5010f0e01050d0902060708180613090b060c010f0c03060603021c05040309050a081f0b180a3305040603050619020d02070f030e011103090607080d020705030c0706260703 75
    0x5031b80711401052850b00500c1195180c4440d0506407440584201d43c0d107100d2001002618903040c00740d0301d0001115005100050300d00240d9012543e40d2041462510042d40703040301c003400079000356011418403040da5400b00002030700c84005030100d22800a1001d0000c881d130030405d00c100040d8100c580c1c0540b00e80380c00c0c04220340c0d600c08108150510b80006a454000c40c000d500341182c800304606081c49000404c1c4141c0c5002004160800500300400c8515880b4500003501216075030440ca50000040d90419030b54803104d00a0240d0701d000c14203007441d81108040c000794924081c0a00420340381c000c4068046500e8410300c01d481c00c1c68200b840c8d5507280c0c00b8408a482d425203032001c3c0c20307818003a00b000b425140c190f1038010642016041c0d0581417081e2401c02000c07180002042c0c0319500c41c00d85000d66030f0f18503070510448030302603883c1d021541400090114100702010010748030300900101143c521984404042c0d8560600e6031003410b11f4651350000107518070340e554810780c00020900b000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 192839505 1250 192838255 192838271
    0x1230d0516030b10030803151f0c0512030f06010804060603080a030f051605160c0f0816060e033301240201090807060509070e0703050103030905010f0e01050d 70
    0x1400c0c0890221141c40303400c40c54100300140125001081e40c0000700c0d03d01e04c2c2c1180c0c11030769400750a0102620140341141b289840c03d00946440703415680f8034100c0003901040d020303404001014a103001d0011904c0c1c2c0690494034081064440076203006014074980342d00c069803031000448207010001c0065a940fa111040040440c4100004007001c01947c3d42c0801c00d6040300380002c0c2900c401619401d00c103082520002c03e5554000f05440c0036070703072190000980c03e1890524400b02c44003038002c038001d9018004001000d020010711403282010340075203050390580d43c0c0d0003a0703900700f5901a0560160441d020308120f01054018084203c1889049118000d441c000203881d10030090b0000e481004441c54031760548119090081c4140d902c510080c0302c403951684c0c810035035008010340148020b03100d002059940c081445140041d080f80d1352042c001e403500f003400402600b1700303101c180c0215038090004107043d40b09070082c0348180d07000d442d51401c0324180401141c2c240d00c604020788000703640d0545 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 192840755 1250 192839505 192839513
    0x10309030203040306110d06050f01080a1509021b0d110604020607061b030b01020118080904020706270c050901050f10050c0706120f0c14030a020702092d01230d 71
    0x70419041140c110031a11fa0500042d1107040380c0c0e46d0740009100b0070001101a20307036a8060540381c2d0000d902200803070a10000a03080c01d05080715041a445c01e0b002141151951415141075011507040e6030032200402e661400c1526407059010000f1010382000b000140581889002084220b20496000410098071070300306071810301e031401440000b6180c0d40c2c07082156a09001c0c050710030281c10703400c00b210030350b55603681c0702c0348280441c0501a031f40105120741400b480380d00503910b81504056040d0382480b900241a120030b80d54200b01c80c4840100b50109060822003841c5044e54006050080b40b883c9010802020180c001000c1d01001401c0100c2070201400380600e10041c640c603150954502d101341b0b40078068405220054070142c0c0f138030703400250840d4817038100301340801c0d510324050b0341c3e0301d462034603001900c503070000650001c850005020031088050b008042203415039400380282008126440c034030341c0081c45007a10180c2c1098a02c4503010324a030300c080f41d080b80104003075a205650b40d2 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 192842005 1250 192840755 192840761
    0x100204030b160908100e0111130e0c03010e040305030612120702180f042a0b03060906030706020606190e0108161a190c0c080f2406010309030203040306 67
    0x2003164035426035020b025444001d42810b80740c542c89420729607445803c1425a5541d4441c2c641801e880381d80792044030b20000e00079407118003801c04134160980c1e111000080d1b002c0300d041c20b2241c0d070408050f46001952601f000010390f8180c50745103102500c60744071a102114640c0010b49003643c008026540c0c0e80702e003c2c080158980000c40b0751075443c1c03030740e142d40100915804081103800c10340d002241003120001c1c44002440c0d103e0f0b803001d150300c0700c07094a07040d609807552800040c0341440f034000d5010402006000195104440480b044c10070b0750760b80ea040c15100c0c2c0c4244102405684040085041890f100010034075140d58200c450007895030b2110140f22240007030344030035416006503000c030311075800415214001d0041205440074010f044030303030581d07588240142d00a49040c00354584040030311032402da184c069044100701000688401d0100e80304c0d032440c00c0d40c90940c400d040300b44060004110901040b84080c9945174515a6603800540141000080031000c60104100c048000f8060348 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 192843255 1250 192842005 192842009
    0x60103050105070f020a02032d0105010e100605070b0402040e0f010504080703180b0406030c030f1e0608010b130209010504030516060806060705033109020c060f0c1b100204 76
    0x44004202402c1070f03c000b40044203101e02610442d00803810b01c1c07003d40c40000720b540e503407410f40300042d0800c0e90a00c40c0400001e60900e000101d54200740c00054041ea180440f1806000080d80524400b9504d540c1910703e48500c0000814041c036540000b0003501c1c203944005150b042410a40300ea02811086080c2180d000b00c404071030b1079401095800034558044842940040900402d0451a0810a08984e0341c00b651082c142050b80f41d0094415040c442d0b0003051841c42d114405220011120900c401c034002d03511101866580381000004d40303103005002d04012050f0213070240c4000c0f030000500e040650301100726a414050204000030005104028525014030b0210005415504140300180710000141005120f01c60501042000c19804401c50740d004915801d0030030411000c54448000d692051500c0340d19403865040003a440c0340940003030101d003405409070340c100c0e644c27440d1000c00d0900030781d040c1c030100f0001d110413107100e901e020070342510440c0740e000c88201048565413901230768099 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 192844505 1250 192843255 192843263
    0xd0c0801030c080c0303040b13030f15050708061c060603051f060f062a08040602100f0204210305040906150f0f05190e0d0b011806030206091e03060103 67
    0x8500400c24003040c402000c002d00302180141041c011183c002a5882c01940a031400c0240000740c015207440c1074214580041da48045144203101c50b604080741c60108002c1201c1e400307400c0038001511503104046c868800d1000a00303812003107104100a01d2118090102142e1040d0f0b40c090110114508004030000d02c11030321a606a45000034a021094610960141850111281c0c09001d010303003102030322810064045c0050030401c100302ca41030241e021190007509000e8001008138009601240110b035840c1142d0080c8000b50307082a00204a104612400c2c082d14000e03011405d6100c1601c130010842070007031409906054441c00e0700401c4070318580c04946104071000f11809044d40000e41c1511004540c108110003048054014101d4400d1120707540ca0102400b045164583c000d440c0030b40041c3d4003a0007400020101e10785000c0801c4c0c01c0c021404107103203242d00141401402e000e0f810580f5400b820041c180488481800031000b032004c0c0040f00302c9a01004010540c40811000b8000e50107 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 192845755 1250 192844505 192844517
    0x80610030c081b010e060909010e07030e0703050c0d030210020a0c02040b0402031003110105040b120f0c03010b04030308070519030603020906120c0f04140a1410180e030d0c 76
    0x654646400c1c00346540e4003900c09900415204981040440040c2031400000c0c20710000307a00b180717000640584921001c4070341c000d4900002051006049120034450740960f10200400d182188000e035880010b07200051666000301d00c4a01103041c50110288194070900464440034000000b043c20f03a040b64179100e000500c615010b9055140c50b001e40e203810708003036804500d5402c040c1c41c800c03200480ca000142c850304400c0c2090a10342d00c42c030304441c02818100106910341445514000031070b01c059824902641280d4003240d001c8144104030b80c12214100c1c07500e8a01031075540c0944a0388002040e82091210074041c000445c0141911074011065540c0e00144440c1144104401d1420280c032182c0100306042c003180c98040700143c201000c82c0211008408109900b0000e800f412980404c03004443c2800e080c0200c00299420100d66a0618003c0c55482e1341c0d4103000c111125014401c10755580c00001c803540888003103030b0115041c480980700340ca02d010403400c44001940c000000220000c3d030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 192847005 1250 192845755 192845759
    0x2093909090106110c040903020c03161707060f18150809060a02040b0a080a020405041b020f1b010318120e0910060203190e1008040303050a090302061f080610 70
    0x282411241c0c1c050031940c10010800210145800e544004d20689640225902c0038484280350003080130089100c00101207680711890301e2810550a5002e1240d20801040b00b0a000720884001c00c119041c0c0300a550350f001003101700201160080d28800c1d00c41c15500580d00003040c0c56140915041c0c00807a40d0b11801c070141031202c5002d20f0501d0003854ac04000d031061106000c481c42c01800c44032810454a0050100d448001550009128031362040c0c0d070040c03130001000c600d06040410400e00150503002c1e01d06100c000c245042d22200e841303034441034007080292610180c2d80280c2c42018620b203400f6424034541d480d5a100160790314107441d01404201e103401002400d1406048040d440701c803180d00005045d01d0080c000e9a02e015254007887c1001c6001c641c940708501c80c18000310001c200605540050303200e240003500010054505800007410300c3c0024800c1c107201d0080d03000f05030b45075004140695408500e01c211040c40e0754030f00f401c003101c05800141d20104001e940d024043c0c0c0501501024 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 192848255 1250 192847005 192847009
    0x2160b1008030d0c1205011205060f01060503270f06011509050d030806120a0309090c03020304020d03051809010314070503060903030a0c03020d0905011a0d02093909 73
    0x44005203062015404950180520100032054801d0019098400304a021441380150384c40410300c001080428a88070001510002d4234100f180c3d100d0103a4141c4986440d40546402020024020200480c40400100341c1c107850310030031135283c00154410504514030241d40036040001c405610030441d0f12600050100a0300c0300c94400d5251228144151104d1034980420f0068081060203024010407030005242c0c3d4488241d1000055210002d4401c6000c551501500940003801101840ca107825491140300740203100b101c0c00756800a02003070001e00207a07008c0303403154850715445030b01949400b90a000d540b074900009010310b02c00c1282803201010150514078114150f803140344698400f8003801003407030700842140d410005540c40410707421118102a400f034450039204824071843c004003107007404410750200f40e13844003040b550701030703910783d14108040e5210340d12001e0742c0704079000d020840c44000f80c541c0c80000c0c501c0b82c1e00b06101003248510f0704c901c6112040f5120f8a2400018021414 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 192849505 1250 192848255 192848273
    0x302060d0e07060e010c060e01140a050103050d08070215100f0803070506062205070203090603010e0702012d09020a080717010e0d0c0b090f1902040b0303091810090216 74
    0x39050744d1401c80030162900c80020b0901c001e03a031010b0400f41d5a109409801c101c29005082010b141e1950583d0b00d003000900c00d401010240b20136600d6002c0c2c850700d072042034420342c4058015400d660003400802480020f02608500c0586407000011028500051840e9a128036000800c0c217203001d140c0321102810f1003428070100601b842c0c850007401c60b024030102c4c0b00e9026105c044849105c00901075550040680c65840360018140d808074010000280c0414481c4d25244142030f41d84c02402003905031180c01d00f042d140380d40b4983d118030840c51701d0303040603006a02c2a64201c1c00206050344595948500c1801d00d1200d030019140c49481c0b09910381081c00c00d00900c40701c4505540109400b1107001300003440c8445441c0018004911040487c00c0241c08100e5440f0b401402010707500904008800310f0300306101800c080b40901c5c10101e284c0240d10300441565030814016100e03401d2080740d0280a2452000100050703008600504045144505407018045903051440c0600d030001541c2017026107 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 192850755 1250 192849505 192849509
    0x16030b03120f030901060905180d080c0d020901120f020703082202011202070605181002040e010905041403070b01030204050a180308070e03060c04030c06091a0906040302060d0e07 79
    0xa9030100d03200c803419101200854a0450054291a0f1a40c9a81800c41d01502855000500242c10201440740c5004001e000300a022206c1c001ca440d03002c611503040c0e40010084030050300740348042c0695001078030150014800340b901450611002c1070042d1449040b40c1155840002d0355a000c2030302c90400d90030001c1c080d04804200104520582d40708154a044a04e600300203042140035400c00c4440003254042e80c0c0c0705a405036043c0082d03e8000503414207180c60301007208280c1b01c1c01e00290085100d0b8401c41d0b06a44082007210126802c1104480c00380c04007403c107c40d0008182604c149444c41800070345041c511850101889524500410041e698042c1ca44030090f850503140e10603d4005201c4007501543c1801d12020300d070384840041c1e40c1804d4400300b0359010700900041107840318070301c0000c0099a20914030400c845458001c101c40703025907070081003a020700740211514100b0149004c0e20004500a00e268074250311380d0f012900c02d40150b255542c05507200d4a042c000c4500510030480 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 192852005 1250 192850755 192850759
    0x170405030a1404121502040b0c0c040b100801030b07170f0906010603140a151206060509150a180f0c02030306101d0f12010608030a0909060302010e10090e16030b 71
    0x20919013031400203500b4840803000104401602810501202d06580541d40100b243c2c1c00003175101c0d90100d040d035444c1d103240044180314a181c4101da402a262003581e0310065403050b5582e0713030aa82950f88168182402424400074800c103d4080c0352200c200500c0640314890151240c00c19040118540d407134074204be00002d00303242c1441c041c400304411000005500207a00000491010b03103003a821110030303982ea0490118001c038030b88140305004160300880b08407102038035008070139a01c98020307582c5c610454140035444030030040100300c0070139480002a13070150580302c0018122284211103007240e0003040c00f070300560008004c0203e02c0c42e00075181c13030722802c1901b0b040e940315191214906110801e5007145114020355802c50329551202496150030301803200007042400d0f100c040302550303900401c040400040104101040c462814060b40e001c6a80c1138503a01105505041003082010b1150303807030405c0001003080040c0e20065201c031035004021b1511440314805d0446001000d403645007030006c0c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 192853255 1250 192852005 192852007
    0x11070602091807120501052d040b1905090f100501140d05040605011503110412060605040207032a02030604080a0201140403120e01060f030204021b10150504180204020a170405030a14 80
    0x2341c034014486000c00607060035450b0a1100980d0400100142000040c0a40020150220781d410310b0b8412000800d40343d00300d0f0300f4a10340d5980c400640c90400300300c0d02d00449400512041101c1d5000310310039202540d03c0c2041c0760501c40e140d00c06404903030003194140c2e00c154540b4010000300a41c5030419201c00003074a028003000d40e212016800e58402c07403103419002101e1040c9001880350170741c000405810700a006655a0480b4240140712401c14024520100245002151b60800906180541a50150140c1032540c1c41e42c45496a07134000c000c01506654864510f07040c0f041c042c00e0751900c00da1207600c0303079649036a462001c9011607240c404400c520307a141c1601840209184406542103a0b41120090b0303540f02074030000551000f0f41684030000740314a50303a841541000e50040d0440708010192410b15540c0e03a8100400d8813118480d046c0e48500040e1200007504141c1c005055541e02c038180b28580da00d8209585141c82000c0300c0a50b1542c0010811440490303001c00101c0d02c1c1460340c035200d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 192854505 1250 192853255 192853279
    0x9120a0308040209060a0b0f03010501020c0a06020d05030406110c0703051c0206061c0503120412091401030e01111611030c0a090509010605101805041107060209180712050105 77
    0xd400c0d40340280c400381c813a030015000504240e403142400c902400301084060b48407200462a0f16560300700380103450260042c00d007061014103200c0c600c038044841640c010031000780000000c3c0c42c6940007034029943c8545982c640c40185503004000c10b65445401c005104051440c2041c41c1050409000c0c01c002c200000e500301d02d8030758001482500458126441c010200c545c1d40392072444050017030000c00d540408120100c1e4400c030818146d2140d40501100d00c0e00c81c0c003030301e0100c032440035500a00002c4c12810441c4402940710707500040080d000a80002404c1902418078804c540006050b004d0070300138600381004120841203460580c610680040100d911550005400c404070307401580f0401c0e543d14000740e07243c6400d4010000400000e80310140d060b10281c40242401c95a68981e0b40790801d07410300052900781407007101e154224200c1d140d8148851551090081d5001c0d030800365000001484400b05204450101e40c0100202c2d22810222003001e070b0044240e8070141c0c0014072501c200440 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 192855755 1250 192854505 192854507
    0x30812070503010f05120c030604030917060f0703020c07091104060306080312010315021306050405030d02060f0a0f0204050918060a0903080703091b0b2205102109050309120a03 78
    0x100d1302c142c82040710039076001450340c032009107400c83c051407050785445001c00b0b200605d9007100e0f10340c0c1603600c0300f4101c0b892980340b500c2c0a66a40b10503503074a04002c00c08400142541d1084d406403a10301e104609850301d20f90340d504050190f518150020406180000d0b0030040c0301c1d014420800100b0002028500b010641490000c854505102c0500609010094003c0a6005030704450501800410350081903803100b40041c141e40150085074060b11074103542c1c20b0382c1400010814441d140602604201d076a6404202d0007412522803030004075034092001051030740e80d20a040e4494148200d030f803840585174140062a00d200030342050720b03841ca08124907011a510002043d4803040608010400000e03621b02001c2015500d00d02d00045401c40c0f6010034000148030082c0040445084003020300390300f46000c0c814800644c8101940140c03404101c4449900543c1c80b0b5a42981c000d2004104005902561050f1403c940f0b0848023a040060905c216150910002d000041c415000704034124441d94 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 192857005 1250 192855755 192855779
    0xa050a060c050714070312080907031e082701080408040b13080307060f0b0f0112200706090c120209041104021e0909010506090a0b090103020d0603081207050301 71
    0x60080c146607192a821028603005004030b6a0041d0300a40015001d0909401c03607480d500e0324001140c1103182090040403051180441c0e500030090300c800303001c2e000c0c42c41c0d584106080d1100030042400010b041b40d0000f10700090090708040d02c90403640380c100c0c161407070380324010350892081034103210303052080c080070800140682d0142c885581c541d80d5105240348040d05100e610342d001380d01c5840002590410020613230840d0f82004050103091143d00207000800842000351009280000d000101032060360503d0b4008811048200c00075424501c004408017400e503100550581c1c1c080c1e100c81082080140c00c4801ca001000480443d0f104503032941e0020700c0a4a001e4000740854044076081c0b0000e94944d0704071900800c08400010f0100d800810b050203a400080702c0c148100b201900005240c200001110082a001440402294200207407000d81d078020700611410503500b8000b940308c0c0105840340c0406180030310b004c9515248844d2080088400081c042001c00c24140010021514400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 192858255 1250 192857005 192857023
    0xd030b12030703090e1e041a0108010c021011070203010501081e07060f0507210908070e0103020916020a170325020c120309060d140a02030709060c14150108010b030a05 74
    0x2031003045c8a501c400307094212816038011301d1004c0705200320074042000303d050008a159401c82c040b201442e070fa1400b4180c2269802d071005005a08031505000da05841580203c0c1c05641010445007410300e6500400d084440980200ea1907501003862802d55080ea280e50340c0321861120020700c0100c0c14480000c0403040c403c2040c00601c03401140c40d404010103498030840403c02c40d001f0103069007250f44002d01d6941e5600c00c290040c000c4001c0403030120584120581070720b1700901031490b10780301e400f04405141300e1080c2d24011400b6030b2840c2c4d03000680300c8603801e10380200043c001b40c4074141484c1800307074814144070ba00e00200d440c01c0b000c2e80c2c142c0c000c284c000d11580c0844042110011720035203e03040d403042c0c04845500041c00600a0752900c100c0d07010940c2d81101d80a20030643d540c1c40d000401320300c07054403001c000c1901e9420420160740f0541042c40c00700e2084170000454140d0310710036860440c05002e1040d40803100001800304080920600d4201c60040303006011424040e1280e9440c0e001340 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 192859505 1250 192858255 192858269
    0x60f02090337140f03031f0b03010b0c240a0f150b030a022503030e0304030b040803060a09051005010e01020a02090c0d091505090c0f0616140d030b1203070309 70
    0x107069010a0050750120f40140f411658143c1d07001c001494501500c96000701d92200303094050321159142600d04c0711840c026641801c1c1c000d403859085c281541d130a500014039030009807064019001c2a0754014910306002c4050541020850070580d840b00180e8908140070000d00d490800d0442c0c8603036201038804100c030301c19501c040d030342c1d281e90344080040e204441d03d414800381e0b0415262461840407414400c614041c0c2d400300009801c10001b2900d0344035500c405010302c43c1d5070021601241e0310000654000308003d02d031a164a0352901e26109070748c4112040031a08078a1001040107581101c4501e6030507500344041d204e00d003090360000d00950405803400d441d01d8000315000508550b140e000b0f5095030703000100602c050300b08503080806002c088031814000c2c010382604401e1030803c2c1041d04418400140100c1c2000160302c040c540300c044521003958441f5a69021031101801030000b280c07140510340e00464441a9402882000041e401019025500400070f01011a600141807801d0740e8030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 192860755 1250 192859505 192859603
    0xf070905061c060c2703410a020d0f0203010606020601081b0307030503030426030705040603091502030c0901110f030403020919020f0408160302100302070609060f020903 75
    0x40303131100316425412108140c031040340a072003522024910050140c1100e205046d0300c03e0b0304c16482050058908515100e00d0188107098051000c00003e514081101d0303034850031a04085241c2d00040e040c051541000d403000c4d18262a00410740c1800c0c0a00d034003502090000306200c0d4136000d85255503050481030741c02c45d00790051403022aa581404171500940d001411651203003424104840c4c0e190700ba19a94180702515410a0700c040d0481c070540c1e204181640301d043c18240342c014140c0c082c002c000c00c110380542c021256000310180c0d51016601821010040c079450b40700407000544000d10b00c8900159551043c500f0041440d800011507069a074161696170170360b00c5100d000c2d500c1e8a48403940c240020b0001c100001c06124101c06001141c007010119207001c0c2d00721a214442c000640400703034021500c00f6950301114080c0c3c00a08060348103880025816016440d540122540d9120802019400294610062804000b6003c0e61454800409019840f822484003000c0803104103400e40c5103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 192862005 1250 192860755 192860771
    0x906150f030a140907030503030c03090115090b011202030c0f09010c0501110d0c17160509040e0303040302060c160f02040b03030c010b0a0b070309050f060c0f070905061c06 76
    0x4020425660085011400d064aa003420342d40b0034058056955140c00000c0308500242c0200300c0001c820040f41e40140285140d5225200000401da01c0141007200319900c0b07480e558400600400e0a8005006600001078040305010004218100c80d000440c1c0c59401441403000c044810021200759410106045a41e10b034004010b80d4420217207100074003e94600864440342941060090500714048841000070b00d4610a013030b140c40b00d44003400031001464500007401c0e0803003006680c904a1280c105103003000500f500160544680b071455001c1500080144410542c04020054120025003030131810660710340c0c076500d4841d400c0c1c1d4001d08201100301c280c00c15511146d101440c07040e009003c0d00d0780da140aa81e018040c00200880501503045000300103030710138010058501c596450380e06c00e1200d0b03190104225080014012207070b8850002c0080c040e8200040000c2c0003844000e402500a1904d000105421200000c2200e80070360009540b11032601002d0300300f0195035030300101c0010400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 192863255 1250 192862005 192862039
    0x906140903100b030c0a06082a0304032007030501020706050c0c0a030c02060405090a0504051e0705040e15010e0f070c020a0501030c030e030c03070b0a0b030c0d05030739050906 78
    0x25030340c41c205c0d40e001030b006100071a2840d07004060a224107840003480c0341d40c20000492800b05040500c40d8010b01c801400800d0020f0b1044040c504100400c1c0003042800c0c0c40c1d07075a8a414183c0a80c0226203a03940000c8100421517a400b5041c0e0002800c0001c40c104a4003000c62503e55038001001400c200700d403610070045644132000c0e00c000e084090a0b804070f51410082d840000d00c000da50950340c80c800d48076400f0b48c892404100d202c00c0c03441c00c0060034400f031a20003400050079103000340201501504000742003ca91070000c10307009001e231142c04156130402c100c5001c0c51181c0074003080c0030409160190800350f01c941c10f41508403103080c40c0008030040409412070060030b146401d0403050200058891100344000041c0803a1401403030315040946800e0a0001198610203a10303425130803100f450340441c0b80c11201c0790851401801901d00c1c00d21306a94030000d582021140950401c20a60300300548102c008203903404900e44030f482148241820001581c0c84001080180700c0c00201d80c0d914641 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 192864505 1250 192863255 192863263
    0x6060828080715141810110904090314030f060a060903020306010608070c060911030123010306050702030f0409050106090602151b2101030b09060709090b1f0906140903100b03 77
    0x25031100b40242800d4280780c50b0400d1242d10183e03174a006442640c0344050144001c0c03180c0380010b801107100c10301d402c1c9143d00380809485115000d44c14808039000c40015a87c0110096102e90b44002d6510654075069040281c416400c0c2c00202c104010000300f40016100011b9103415290207003080c8031a0f0399003400403110f00d040c0000050001d414a112007041006001100309550f81c2240284200c81d80c0c5049449400e1030a2081100c0b08025001000840d006520490f00a08184107492401000034032110305030f40268800c3e0116699240100400c503844040c24000d02568030141520800003100d02481c0c1340081c00c0304a1501040982c00402400a4112040054115001c0d2108000d091751000b580307a0910046d07032009840c100040805401280303280c842c840a445044016041000000041c40d52544d201d400c8210307580364401c40000200018043c0580e551450a6203040400007020350140e030071920705469041c8020f9040d541c02080032080782d0700d80b020004419280000107490 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 192865755 1250 192864505 192864521
    0xf140a0b270a03030f0605060f0702190b030c0c060f0f0f06010e04060305030c070909050312070302040302130209030d03020307090b031b0a200318091306060828080715 74
    0x1d54890045041c08040d0550001d04a200401c81c0030081d09a403101480300b10720503070340d8000c2040c9041102c040149000351051501c125201c1007640901d0302c44104041c282e2046c0c079401c0403c113002c01c66082c02070701000a9076000c3d0060810010905017040105440c0c0d03030180c2075041ca42e4005c000102c3e9a40b0400d40c414032000001c00c14041644d0700c0c2813881d10b0390301011900c08030380501d00300441d0f42070082c061024425400f400441c43c115500005903400710001d0300340800c241d020400040540d0312800304200680d00081c00580d00c1001204040c6003500e240e43c0d0b001071500600410a81582222100c0b048600542005640780e6607801010300540c0f03090028410b400c0e020404040c0b8590020f030002517031115040f85450701801d100d10340d50b130b8000c400d421942038001020342c8109007400b10445400049104240c41c150794990b40c1d94094031800d0300071480584c00f0760101d04010148000e507840401030310001c40500001910360340464494200054500011014241813002440d030250310 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 192867005 1250 192865755 192865831
    0x2180618070306030203070f083403060203010e062e020c040f090210020303010308030703090f0501060e06131104030609021f02150a0b010905150c01090f140a0b 71
    0xc09490220780207802080e050206034000c0c819060003045000b03040c1e01080980d01c4400c02070229040076011a0f4619030480b0244640004100784900c0505c0c0440c070340c0c0b01070361045001580341d6041106581c1c1256008060500c10242c8040410720b900784200c1940b84105000c22000143e820101c0c2a468168264030098105243c0b0f110041120840d50003250728a04c200ca1852105140c60000c90340c9000038040600f1208040010a1310b0900991017000c50902c01d100e105a80642030b00d80c5421144980e00401c05040c0c0310042060b0742c50304602d829034400564108020504110210502c01d0041d40002401d00c1d964107140425036988903800b8408800f11600c0341200c3c41d031048001c0d142d00d48050a040050108008515540c10034082d018000c24180d4504010b90310f031204103c0d031550140a60124220104104c041c5c070b500a0050807007290180c412003455002c64a04041d080c414462249aa604003107110400500424115a003005c3c0c002c0400c03100c45401404d480341802a040040 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 192868255 1250 192867005 192867049
    0x10e010503270d0311190c03140c280305070210030204080f0d0206060609030a0308040c181a090c0d05090c0a0e0907081c03090809040216050118021806 67
    0x50074442c00024002c95240099409000c0c080c07080305118410301505115040c540e100c82108011940f050f500300404034000d03c3d00c14249407001699003c117612925001c5000e030421508070745a501081071503149414040402c048882450310000c00500500100074841c00010007541441480781c1c041d1000703484124182c0c2e4120440c003240076501d502c0741354010054082c0c8800108680340c02000d44500c00c0015002d4103d4003101d035011100381900a0044560703492152011614000480c4202c0e0640e59003032000a028004205800703c12036810741c0307544610000020440301983c1c0034262034810410003004511520780d02c489506206070110400c0e00a01000b0000408011070b804940c0603005030070603689442e88440a440d100c038500340380c4da40b0600720f280c0c0440c0424800d5000403511401386000900b0104210006810b07a4004641d00e11445816507411052000c2071140202c0c03e2500317205101e9800c40c0c0d5011820003a1501455900e0100c290002403150f10350305498804080c59000c00e07 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 192869505 1250 192868255 192868321
    0x5180903070615151d0402090103090c080a050705190501140c0607120e0109030905010e0307210209100e0a0207030c120302040f08060402130c1106101d06010e010503 73
    0x120030104052041c0009541010035400140e400f1702a1485200c00d840d00b2054181740500501c0042c1d88034220460400d40d543c0585c5000c901002048c40103800110054040040141031940c0391100d2500701d180300c0e0441040c5105007100e00c0c2d91900c00ca0b50f00303003848030741c580a0b00040140c900038018811000c1c080c0c0410810541e50283d1603184100c006442006000102050720b4200d84045000070045040031806000540c05101c0540030381000804850f4031681703e200307248480c041c10303c000440368529520102180782245c0456400141d9000c030100d401c1c40c0c841a40e51060000c0d065980040d400602c0d41d081c148248101c00510f030b086003041030007210f03c1d10006c4c0290700c00c0c82041d5032230504480c04140007101180c024007030303500184150780030b03420300385000300030148058000c040c09000000910804420f01019120307204003400c03008101c0c640b128000c840442104412900e20b8032200308985c80ea0007940745643d2100030704c0c000e07403290307601100c083e02094610045401e40050b2024 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 192870755 1250 192869505 192869531
    0x10804030c0c14010f02030c1515180f09060f010506070311030307020607090b040311040209030f07080f0106050111030a0c08090a0b040515070f080c0703080c0f0f0304051809030706 80
    0x34140d83d09400e9940b60007100302084200d86038003a4a0714090560001c01e9408401c03001340c50340c1604403610410340d80e03010102c4000a400b455180c507501c41c0c0d078034002c1e0400a003114403400f0150300c840720101801031458121401d2040f11014050340d4440d40740400c056081c5841138001410406410080300d0780c90501031400382d03940f0808c0b03034028001542044c0100d01409004155000c5a41c003401031030301c0e95100c0c0c0400010b50080d000e03040d05881211580e2141ca02c08011107030003040d450006d0039040f02400314260940b1642d4104905000d03400b01d010600c5840041200c41a403558079003940d80326218074020f485442910700c0103500119100c0c021400c1240075004000700c810859001041800203042c080540c003500340f02601d0b8814000300c070300129240f0360003840440760358400d40390010b80700d83d00c1c1101900000362002c0d140c1e008006400001c6002c200012407084c1c06c50045052629100003d0000e540c01c002d0a00022400404250559410019500a280d01103414490b401203010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 192872005 1250 192870755 192870779
    0x60903020c150f09040504060e1614030303040b0402010e0d060606090f091b0f020703051002120a0509060a020706140412170705040614070b01030b06010210051302010804030c0c 78
    0x218034800c203080b00001040010303010441d190381c86422242814948250308000090a00610a842960301c51080c92920007082c41202e980d41c40c9400c0b00000343d41080910403160410071486802680200140804241140011a88076030b091804540421901005c1400404d0001c2c004040f83d00300f01c1c010800541258800e010740e004e85c1c100420301c80d550b50b40303c000d0310b42c199030000070031040c0207a42002c184142051031341040c140c01119142e03a40d1703998941c540240344220030042c65010a402c0088481a1019a00402c1c05807050103523050000c002c2d074807810302800c0502d08550018131602001116040282c204c840202e90b91210700e000c2c20402d0380c0d0700d890707500c3e540010110018503421407485d0032502d00501140d55070030300703007410214240c0d840c0d0041c0d0340b01c0b008101d0034002c5000107021084c126006e184150200768690030a1000a40b078001b848000c3e2210505080030028044c0c0400803201c942c5030246400607060f01d407804c007030740c42504590020b1b0205503004004507102c2076200c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 192873255 1250 192872005 192872023
    0x30c091c050f010f02041a0f120901021803010c0923030a0609021c1e1119080123040f02120303070302090a050105030c120a0605040c0801050a120803070c030c06090302 74
    0x200034013041d4068030b000030491081c2c1c0071710409954603454110a500d18000580746080f5482e01042ca010641c0f4190050450103c8038548180e40000305481e126900002c103130703500d00059000384840202d40c81e0240c411805400341c4503558000e00c050300001d0310340d045610a00c0c040030b4195048040d5500b484002380c003038003805a00607485400f03141281c074040c0c1401c520700b940040c503d0303480c21005481c12948100d10349098502d10005034240220341e483c074602094006e400d00b8492409841c0c03480301400d4416060000c0700b034a83c4001e03907407103190400b00280d41c07040d0b22103c49a0700441a10010362080744000c0181040d10010003000501a003550003400070000890b000545565650011a0a480201d83c068100c91342800350754192804030503443e400007284030000c141c030781d02c541c041021104c020800b03c0010700b0034401049241007842004020f01602c0601101c1d9014540714800c840c8030141c2600c003004034030b005203402d0501c10101003070216030001c8148510110341c20001e507034410607 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 192874505 1250 192873255 192873283
    0x21009020a0f062a0f03030908041521020a140702040e060103080d06050319060c020c090907030b011202060a110a08040b030405150f0601031a09090f0d030b06030c091c05 75
    0x1001c1c90710b00c0414104404000300d50005c400900030010340d8040b40980701207030f8125103447c0244000f061241040d0b102034904011560b84003104000c40d0a030602461070400c84850051041101903816540002c1040a1122007142256600d0340b03403010138000d01c4003c55401440c003032400007000300032214000700701d01443d5a03403e1100030b40359001c00d07490b00749200401d01828541c1000ca0005030280c0c0050300b08036032030b00564021840e02000310700d10031422140d012941e0040b50007441041000792601e800740c85130b0030501804e0802c50f07010520714441e41044500307000a080051080040802480403115880a0841e4403a0b545004061b01c0e42c00c1540d04132014040c50044896507212021900d05c00e044c50b0795540c003261a80001034004040280c0e0b0b4540800318040c40111948511070610f0003001120000c191525500710054204800b0000034410181004200f4419a13215000d883c0c001201711020b9036113035201d400040c103124501510b58103401c090f15400e400e001010690800394900 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 192875755 1250 192874505 192874547
    0x52e020105100e010807060804050a0605151e03030a050705030f0403050106050909160b0a0302093a0503040303081005040f06050103241a090901030507060f030c021009020a0f06 78
    0x3a4031281206440c2400b864141e030307203c66410040c880c800e20062703030003900540559024110684400c001d8607400c0b0780d47c2142d151082e580200c00c0c18840c0c0d410300c111028101c212000030841000a44030302ca44015013041080200c0e1060500600307108a403265020110140d542d26500e1802c40d010303098a114062080110000090843d4404642400001890380a44100c03504210400050350090410441059070074000014503494441916503c00400c440c1c8503000306410f540c222000a000118107101c66000c500540090f2001098409580d4582490255607580c0800c80d5210741480c1d001913030150178520121400303115680440182d90081c0e800740003284903140807500b40051801b91380620186104104408000c6d09a44e50b90420008505494a00404005529000c081e001541e903a040302200700416030b008210301d030692101e0306080c0400410f01070040d494122150100110f80c0c0c0712103e1700c0440d07580c01070140c05003101c1c2400b00da4a80d00c6910085c40c3d05030b0100c10b0224104 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 192877005 1250 192875755 192875759
    0x90c0c0613050d030501050d1b0909060605040c030e0a080307170103140715020a0206070203190803240607061508030c031c0b092206021602130e0601052e02010510 72
    0x221a00446050381c101411690107105580d9900e802c031f525a801480e0ba42d413900c040401cad000c0590294401c400e0240d000450441d04140400044401c15102101414a0442c064042240100700c2040340b9070060030640c1c0725030b102e0000341d405d10200107003122a010210700100c204415030508581710001c43c000c4412003a11141c580503e21460006200581c1c081c02c641001840c0c001c1c01011903a00c05001c1e518030041d0b030403c014040c0c1e045a82194007010120030000c0d8646211510305545d124102d013a40008444400309007544101c0c0c802034440c50715581940d62000410403032500401d000d104495941c00001d038019121341107002d8002908040480c8601c254110b40280301d000d44004014550300d48540d040a103040c0440308000d0303814080390001c81c0100718280301a090380f0383d031400000c904810764410040d0803001299449002441d00f039240caa00c5c1c1c070019030903054640944413a4040c4ac0800e00b1290701c9802200d404d021015061445980c0903410340155020b0b0001d082e41424040e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 192878255 1250 192877005 192877007
    0xa020606010f12020c010b03030a020c1c020f1c120302031005060712050307090b040e01031a160809031314030f07140d1514010302010e03010207030203030402090c0c0613050d 77
    0x4201034200394001001281c907201c0703d611030307402800c202c540d160002440c82141c0340404d0841c4c200c03a0004000d07820100c00b141841c1810034a496008442a10b05602c140481e0f000601c4000b10030740a40c0503c41c141111001132107202400170b0810342241c1c111b0309000204c84001c1c00b075440dc494841204050301c07000a1503042010550320f0182d841030040c20b01700c2040b036007100c80340c100610120420101703030000038049811380024806000e04219561aa41c118241189607205400c074415943d51442c080054807400750143c10308480c0310b85040110b5441c0ca400e000e03d1070040b0540100c2c0702c00c0540002918104840007808000025016a4008000c9112070341d2070324aa4400d840c921445d180c000c201c0c41c80c1c1442510750103403281c410103029099913032004045848142900007100312500c014419980c1041e40702c55096402c84c0203502e0201d4541d4025143d02001e800240602e40380700104a54488a00603141c20f005540101c91551602c1c0005c6904651901400d96441c010000c03403644107 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 192879505 1250 192878255 192878267
    0x31203110d09110d0f06090f0b01080d0201060f08190303020927070f0206150a0b07051e12070206090a0305010513031b0201081801091202030702030721020d06060503030409020a02060601 82
    0x113541c000681e4045051141c40c2c503005802c46003000c880400000c403030040000c200308400c0d1f010700014801003041c1c481c10400a42196503503080303801d1a4042520400c403c00001a0b503044a42a050300700c1301e15006c1c0d1805070081c2c028040fa46074080c0384903e07845200099484480340a10100c1d28200041d01c2e0f01e20305030b807480f1410300f034800140c1241c2c00282c600d0009804507440104042c6c45003074003e98030603620303031a038001d500c0c1100c00d44c00081c200c1c5044000230b65412031504103240900440b034a120061074207440740704802801010042000c01070740c5ea03a20a503c0003140c102c0001c3c4031500d4081c000760f0841c114880e00700c01069495103200c040c2d05203195030411055041c1c40e00241521380010000700d00c2010041340b041907480f241c1590000c0c00014800d245052160021a11880c1c41d204150030407005800400b14141e82517114001d02842a030104031180d01a50a40b4041c01e00e41440f40107401e40781c1000350948800600002d06050300e138020890754555600341c40c0c55441d05d0300111aa = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 192880755 1250 192879505 192879529
    0x412030e09041e11030d0c050c010206012603090406120309170a1103010e0d03050108150f06060c0a1a1b09030a15091403090102070e070801031203110d0911 69
    0x103078a224000715014540b0004849a43c14041d003104c5000e05040d100082c03420500707804031300000745410f0b088003c115041184c0488010240050106981000480c4140f02c1010106031014125030080301b014850a200325030750700c07402400902c002c603100c031404020f801141c030040340050550307400000d8508001364449040d03415140039203800102a29103542c500e40b11345000b54155079400c1d0101800f002000041c400d00d1985d1004a020b61408101504044c107c1d485680c500351031030204410b07100c20908159001d101203a5103a151003910040910301000050000c0c014440c40c44c0c07000094540c0c5102d50320860710030306018808501c610007040c0c140a110582e9805911503001140012400c00381011314814072500001c043d0f0140e00c408002c101a102070b49000d4100207004c80140d64180700e45405807405462001c414142054024403030081444045e0000b0808000e88211901c290010404540c80b410156100c00e0300381454001003070207c000f1107109000d00c000031103038100f90401c088 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 192882005 1250 192880755 192880763
    0x70c0503120702040506060d090f0303060501030b010210050c090d150c0c020303091e1008040605060a03021014040e160314070f05030612010204080f0601270f0b060412030e0904 78
    0xc02e00006900340005014040c004a0344818140407100031403010340301e4000b8042c003070740310380444010605003d01260f0360740c0c0140d41011308007800000566000103842c5c1940c1b035020000602c40d6510203018031103004400150b5809030180107441c05002c488400d80c1280008154100003000c074640e015203807051810310083d0990000c0c4100301880c9805950207d0340b580750340b031120340c1c0080c95001035011009800d24001241c0e1107400d102c1480014401d9a5000d0000c1e0b59954041f070850300000e9105901c2d4130000c04000f100420300702c141d581034040d500104082d40c041441820080003503118803106910b128002840c3c416446544d2410303644590288000341c80310072402c4501201260154001801140c104055880c1e000c040542440180002c0000c14040c0540440840d00ba60800c2c80603481808040e4010315403030349801d0652905181408243d40010b110b940390784180d8060550604420b500800c0480e0008480860101d44104284240d80d41954a0813234020444c01c00c1c810f58010b0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 192883255 1250 192882005 192882007
    0x9060703081807150f0e0a15030b0402030f01030213021c06084605030f03060910031101110f07081c0302040e0a09141002180405040302100b24070c050312 68
    0x42034140100c1da1700304c1d440000e2622085058451020a04c00813480c1d200c1c0824442440000081581c54441d203940200210380662450500c04100c2c13142040602010340f0500281e2038240c4000440e0341168000f011a8040c102c0030308814100c0c10091560b4410342c50a030040780d4118209001d04811364141c10640e120b001c0b5a0705180f050100b1801c2d5a0003140c91a210310701900c1d02140382000608207080341180915070b88d1629005100e03d8002c090909400000b44000c2400011441500b19034000c10a10b442500807240240382c5160064089a80b035081c015481e010034494070106044c4d901041c8100da0300911040d01004604034480c0b44900c00c402c03c18400403034500420340c0c00c4081e009000d4640101030007140c2031140d041060414000801580c0045c8418070010300c1040055503a81c11102000070f031419450207911149540f40500803070341e4803d18212035680f0060003502c03107142c0c294047c591082041030011150300040041c2c68440e91144002034900c2c001861103100c80d002c2c6466 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 192884505 1250 192883255 192883289
    0x1c0f02030f33060717040812160623100302090709062003070b09030c1603050a0b0c0c010606080f060a0302180907091a040c0f2309060703081807 64
    0x7218180c0d82c062945603011608000c0c03030001c24500c800e0705041041401d001d0341c1d40c03854038249624000c0d04080f18a00d042c8140b260600c00c0c3d000640140015800160100c0c4440c600284109600f050303202d8400402600e400b4418820250214042607a02c00d4840d5045a00c8101c0f0a9602d141c84d80701d090001003004a0211b1400f07941c80d0a4108030103603c0403203088c40c0d40f40d5221507030303410101d40d6084160300110394815504010040044c21070845a65103202c2d07801c0d0b4a6590700c4400110003d00403e101802044003110005d088652002c0000000c10810740c81c0c10f8000c02200c8291481c2511050301e078042a180e00d04064040d080340c1d4024040394086003107581054260703200800f212070a00903080006800f035000c2c0101c10301d845141303030a0000d412840b0104021140b000c44017400300010301445010143c0c004e503068000401e001121b51842c108000340140d40d105449103a0b40207140030481c501056048a6001c1c05240e81c801c0f5030050316410f04100b999160030344544c444814200c0c1403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 192885755 1250 192884505 192884581
    0x3090706111e060f060103050f0105010e0f030610091b051204051606080a0f0e06070509030a020406060c05120705030a05030a18030909110c0706051c0f02030f 70
    0x80d00780318500c10041d559006a00751a000303902c40100040c2140707400c400d042000c007150103500c0710b51140e001d0030100031f039080200d001031555505004450500c461211031401c00d660305103e50034005001422a4518680f584841c005c0003600c0c41000c400341e0801d210500b880700000c00d02c40c07403205140d84650505560781d81460b1709003005801941c46018143c0f4404941080d81c4400300030340302984510700c0c5801c0c20521801190300030b40320704500500e0224041d0b00d408020078075603042111454240d49502207000000e040c9981d52030000c0d8828500200020003c0d00400b200c85014044d4060300e000c42c20306080f051040c0325044004181c1d400402420701424000c2005d10b030070030408540060001003516001026409001c800e034042500c1c00030402c1011012300440a0300c03050f6002540c1030180425001d13544a607640550414080085000301340c5c0e03502d400d011801460600c5050216034091260300c2c0c000c2d0b109035800c04544207000d00040d141582046860125050f21250280c4c25a00b0781e2 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 192887005 1250 192885755 192885767
    0x213051807140c0109060209090f0403080114010201110301090b03070b0408100207061413020a1406041701020c0304060906090909020904020f0a090e012a0507031d040e1606030203090706 82
    0x914400d003410f02102c103401e5000d1103840100c520803140103036034054400c2042081d013001082d80440c400c0d41c5007040002030380446101d04440755228035040c2c8008080050b409030031141c0340390950240110000490850310340000b42010415800d90f40f0007622150b14841c14441e50081c200d06a1080445000e9442c0590040c16018041c030000102c281100c030025486030710a407a0604840658000d41042d45041c0034041c00600289084040007403402c00400c00d140914458040c1060084400c084105c50079011101c02c20311060070349035255101d450207800070f2101e00500000400c000008520082d15110740b00c5126001400b128080d62641c0c20030000805500480743c0290b480c00000a220319a4004d01d04900d00103c0003180400c1c014000103040800c515040101582c006240c01034103800c00c084800b515014601450814019800200b6100880c0c816942103850102090310300c01c0c0211b0810307980418081c441e15410340c1c030b09080b400d9000545000320381d500620810840280161 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 192888255 1250 192887005 192887027
    0x316110102060f0112150c08070e091e060d05010c050a08010602060106090510020f07061d030703030c0f170a050c0610050a060f090b03090102040e0109050403081b120702010213051807 81
    0x15090240a015a259020383e85141c1009012030006418814014ac0104420310400c2e415554901c10789000c41241c080300d80f0312818241d880c1f40f048081a0592501455444580e400c0390080c0043c56101d200100640d03c01d03200000002d50200001c40c4045c0b01098a0b03040b110329958600e00c0c581001c080000806942c241401903216614100480c96402d00203800106480d4071402c817035901d94400002011031000b29280300341c02680742840001d030040e20010000303400041c41944d01c44d551412022644021a40030b19002c00800d90000980d0300070700030440500c0d907109681064941301903100c505511806260b0b40450011414005c05104481c950090b2032240b074030907050769941c0350402e0640d100391103100b116500081c00707020012514141e02e004181c0480108040d00d070079180281444c0c070146c0f0700d6403125003c420800000603000c00751081c421840c0f03603081e40d078241000080e0007503000d050413016812504000064a06d441c0d003038502008411a14241640e95840c3c08131080c1e1008 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 192889505 1250 192888255 192888263
    0x3100311030a052d151807170d110604050c1003110705010f0e0304181503080a0206040b0610090b09060c031207140412020907020f0316110102060f0112 67
    0x656018000c0b4000700071079105890080e10440c22985907034148070900e90080d1051300365a20100007a070b1041c4070440d4481d032043c84072070040c5045a031012014100860f0b030b0310540d072115800b08480c000d031001044070240b100d240e4032448140d1704034620690b241c41007158081c0294008904021041c2000a0004034ad40c14620300050340070301d09045444241c2001509547c181e54403151203191184500c100100307445400011410146025580851034001060282c5001d032180d403140d201c03040b04988040a140d00c29115074545c499490b00030b544500403942a250781407440d001c1100350a1840d4110400000c1d80d4600078158100800580e041e48000881d0390081d40c10091403024080c01d0014211100f5410701007142410465801031030b0b8240b00410005c117001c2003108014050810a10310243d84c1c1c160313840e0040356200c420503810401d50b890b000d1202c0c0030026803100c1d4002c86660042c0e2192140002c003a184940000480e59414103d07045004130107c0c00c01170001e41184410506502d1007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 192890755 1250 192889505 192889513
    0x114090307080610171009050a0204060b27150306030a120c14010c05040519030606080a0507081501120f05030f0a0e0d05100f150e1602030310031103 66
    0x941008603242080030b9000003001c0e04a041442020725940340e01d02c00910b80004604128404110002d4464651442c084c2e080c5549500300d10411030180810440d9540040c010048140d0310318040748580c1c4400c4207492204032002e141e100c1c80340b00c151111124180075002c600c02ea18940010862680007411444e418441c00d050080043c0351402c481e801d42c10140e41d001c00702046803814103a0100044c5110031a64100400381c7d21f000d03407102c140c900302c0d541210398040d4a140308140b0b034500b40300d94001420305030030b044010850003400103110611a02ca0310880c0c1116541d01d50322500d4510408500320072180307a80041042d12244010340006500036102c03001003203415581c7c607103103600c11110304035003a8010a00f040415080003000f10107000582d041c900005a40c1c0d034107915101d981c028100300e075580384070f10011511243e001986826020a4550400d82c0326a0402031100d0304581c00c0e82c01c40c03c41d40c03080c0742d01c0380f010040ea40103020000451051909540e2007101c40c1064a40d0300741c01d441 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 192892005 1250 192890755 192890767
    0x105061b1b0103140c1803100c0f090f062309030a05070501021603110603102102040e0d020d051b070f05030c0d0f0201050702060d1a01120905060a02130e0106091d0402010507020114 80
    0xf00f01d102700c2c8001c41403900c5d0044074940580000c0e180f81420b500115915407400c00811455030801800100c6003c0e0889520560540c3c1c03070701c21420f02030710075816058418000c0307007000c0040000e03401055507400d80840d075040d42143c2c24680545030b2404000e05ca0040b46003200f010f41888030155401480c0d41c0e0f000c06000341c40d040301410201c010211420b44031003042c80300040d41440d01c100d4100083d10000351400c0d011048007e50b541010f041c501040001c0004d00001c4142c2a90034404501d65400c1503d44c0d450351844094460801405210320034000d41110259038a0708090301c0d03c002d40c0c803004901000c907654005545c5600100c5040c0e8022004103c42e522005135841450414110100c14a10000d44900010100038000f48810340b142d24048a03000414400103c5c5540441c1280c40943d0f00c02c0c0206442411040661101c4612040300300040b130107035000390402e8269500c1407201300c001e02560302454072100080c0e0f406408900c0800040d400343d4482e46465811040451324180351103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 192893255 1250 192892005 192892033
    0x61b0c0b030f060f060304050303070c0201030e07180501081c110a1406042a0909020d080c0708121207030507030e061003060b03060f0105061b1b0103140c1803 70
    0x1074821210201580040070410040b072400703000790390801005441050561900341e41d1b49540740710180c001c1080c0302c82051404210382c07290f00b05011812016040d1046190394003168000d20900041a417000341c100000420014400515231003482c90f909503c1740702e0550301700c0584007003041f000c420806020b85035668001c10300070040000e0034111140113109a15281c202561051400c0c58a070303c960156081a8030480c1280440d4001d40e80545800151518a4030000301c101280d014020300c200c1e800324000c104007001160907421141054141e4420004060b500c18980c440c07507a0300390000c83c107207000c15840340c8039034040e5603c00c1241c18009250302c4610030580c54118112907880c15521170480602c20080d9074001d074156840260010002800c2603404060400014002e040c010000800c04010440c0050084481110b284090f200ca640307034803084001404201440601103411f04d245902808007400309148550300c5014150304050390703030329580070680340841070b1a03161041a002c16040d07 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 192894505 1250 192893255 192893257
    0xa030609061202100c0c090c020309030a031e08060102060f0a020d060803090406090b100f020a0b07020a0b060603072f03040e01050103060f1404090c0806100303080a06061b0c0b 78
    0x14280b08584810201400c0c4100030390300c00844d40c00020401c02254074000125811101c1066900d0031070081040362103444103d1840c01442c1d2290741c14410f240d002814903420400405031000603044080401e909000d0589003c2015a8040c2c010380c44000000d1039810104002034001c0c0c0c00c00d00c050314050000c2034450aa520603040a101c40d0400620344071a480e192191400410100002f0300c0501c040500040103400b49500e801d05006500b038107149410b10a001d26100c0d0366215400c1c01407424065002035642180c24800c850441e45103000c940c180c07038a00e09503446500e06030b443e14254000009601813140c4c0034014018a010f5442103850069810b102603c041c112608a02c0c107150700d0f10000405813003c551004201d184500c4060102c405040c040c0e1a5003002a500810f02c2c1010380360200c00341280d0391024031207029400a011954007002d01100c2100e01076540c650301030300d50815400407507140c0e11070000800c074410101d14004205036400d48400e03024981050708241e03180d40c41c20039 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 192895755 1250 192894505 192894509
    0x16020406031a0106020c01090f0506030c160b09010c0806030a110111030408010e0106090603030f1d060706021209010218012706020307060c0e0907050903010f180303050901090209010b0a03060906 86
    0x14481d400310051001c2d95040046c201c440c2404d11348890442d00d4030319041624551401128010080040064220021031040b160300c080c25029000040c003c07410b001c2d821100030703110104194203020000310280e103c0c1090034003412005000d440147e01c607680b070034004071052040c02d040c1300682d054071400d001d040c4081e2001301040070001c110302e21524407580c02c6441a81003158460701c1c0c90b50078004030b40e02c0040d04250003220b051a0f80c51140248580801000b1140240d901140018460040000c5038015000000c41c0d02c100c0011521781c081c0c454203174051800e81c8519080d804410440c6907101d4034040701008003a4030300001c603513484000503003000c0503a0020ba001d1381c00041c0b80c0080000500c1540b20741c0c202440e1100220780342c00d000072107041d030281c910010018044be107880c0c269020340c172107080085021030800c41060540e034072102d24882c0d6030b0190040f80c42e2a001480401043c002c8040d25540100200f182e68200068484a5045a84d128040585d14080426038107014440c0c540 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 192897005 1250 192895755 192895793
    0x120302070905070c06060f06140a02010f0911091305030d0c050705010606021e03130e070e09070306060306050f0f0904231609020a020a1106210a0b060f1602040603 72
    0x212000d1303281041800d4650a5100134030b4003190404c200100b991101076560500c1281400c00d40d100300c410412405000703132000c110b40c2186421a4501000402c5068a8160f5015203800e01244e0341c2e8864182104190300d0090002e4004000c841c072461159401840e00c41100d0424600707002440d201c2c2da0071116281c01c82d2003d6400320303070416026429140c04290302004a0002c3d841d10340020403810020641c1d200d400c0d4510090000b003810240103004030107400001501e8082c8900d001c00005000d40442d01c01e82c008030346003800110741420210200340200c180505400402040d000a000b180300b0300038000d8400d4a0f0030700d50024040703441e007440b0103060340100041a0156220381c10a0701d95045902c81c4941502c1040940d1819070041403807521507400c4004218051382d81d101041c0e00c1e2085e40c104860001d1018015205449003242041c084c10380c29004009807440e02007484031510a01450b000414400c0c46124240d0030480360b1100300c02d10241c0041900d540e60750f41c0c826070704e88078a0000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 192898255 1250 192897005 192897017
    0xe04060504031e0c0318120c0e01050102010e06041104110a020309090703090b0f0702071703040f060806061206150301060302211b030a020f1b0f070b030112030207090507 75
    0x80149a80f10140b0200e20b8406030030395114100024014241c002026002814403005a2400600c0c81808440200403c4090b10200c000c44052529004070003060298130811502c070300c00483e07a54814491480d408806c0c0000300400d1712079403506000c200d003018003903903c1500c815159148414141c0a04a240c940e90029a02c50f8a24000c01c0079103a070003041e1108062908218a0202d0452980260044008038581c400c542b81c1000c124101411500070b043c803411550f4a01105c03100010040040315240e0340c50040303141c0c50304000c688250065405507440342081c004c07401040c261000712500250002d0a100c400381940e030800d035440d0400d83c0500c0100341c0c0480d89031688000f8841c2202c08904036010240301d880c018246c41120501c5505074a20442e012000951034249603048502c224640303400203031582403104440c50002000345080b83d40313001d00d4021001d401c000160640590344c18901140c2160f081c02c0d00d40e0758051b01c1101c1035003144544203000030000c256216150044926907074403 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 192899505 1250 192898255 192898261
    0x313030b0604020906030112111c111f11150106080609090a0209010b1b1e0f01051006210914010b061e0901021e1005280f060e040605 59
    0x114640041c4214003460040000924075943d1100710380c192481c101c01c1480c50101d03030804400c0e54130759213050364101c0c0518161301038030000ca55960f80b01c10320480e03054203099036420030b001007510b401420420141c02c20901800391400384007000502440c180440d004a03004100b11801007400b0b03401203000c203010500344505810170241680d849a2030703400408441c4090343c0840c80c00b66052041140329100440c070303642c02e0b403c0800003104550b1010700b00c40c070360810001d4600440901d022194054821800405c285442c1070241900c80c4240c85800c00d4942d190400595055080e103030944003200700304846180110186c4140040240680c04030410002030001c0c1908440e141244a84a14030601c456107100708802800003250002815043c1c07070340c50400040c2d103080000b40c0b070f451110f40000300010528800251198518003103071f03001d01070354490f00340030701d4240403d4003050140220b0300c0300700a02e1480d5400c02160701c0c00b0391600049030350341c503e0001d0547e43c041c0d404441d1036484000b4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 192900755 1250 192899505 192899513
    0x50114040515070f200d0506010b0f040504110c2404110a0801050a09060b030c09041401110307030c02070906180504050f0a051506010206011211030109021201020c2b030b060705031303 81
    0x902c040413400f6a07601046c4403941e2200fa0f9100130510518462440004100c080c654409065500400c4054820300c0420350000848903cbd401c8075414203481c2c0b14602180030002020307081d000749410b2600b000d101750b0300c45440e003582c9a4240340301c440e00000320240028629209100e4140b043d4044280010b031403030305240100a4035114012244a41d000840e0080c80f035903513404094010f80d12002e4414000c244200c0369001d05400c003040c95081c9401b0041102c020b4043c1c105a4a5140702d0b070903900301c83c0e1a00407400440d400c9018240e44284015a2400c1000e1150301c190f4026015200300c0b001e19075140703c43c51034860842c0003100d4139000645c3e01c3c0d224110000c850b030b800400074000707807445605008030045000420600580490221404540b0075113082d0300c03030b80180d40c0190400c205c69882c246150b0107544070a002c0c8482d81f02c1c8501c0d038940804480401c2c03c240c1041700150145c034001001c03c42c05481d0860034540c0c81281080304a0004100308014441e0786030380c1e0341442c0d5441c51410 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 192902005 1250 192900755 192900803
    0xd050f0d111c0b03061609060318020a031a06041a040f0e061602100e0a080a09180603110a0b09010f031112190218011209020d0615050114040515070f 66
    0x504d50b2580140045090454012038401c1c2588c01520b000100720891a0104030324071306441300039400584955010080c001303404007003124100040619281511104d0a200c1120a80720000720013028035400464140f0b0305030005021204003d40220b0b09486c0c00000e50306001040e00e25001c0002c0311141d90050b203405206488502d00310580030400c1d9803a0b15402d54440781e500100901b44000001d52150b058020040d03440588800e1010454004030320a50000030b20ba18003050b03400c910104c84103281c51a200347e8031403d550754010032074103040b030201c0107580a41ea00011403040c191111200140480500d007e000011550381300c1c60094100001880340d1401003c090030400c074010811048841c1103803540000001c2c0a20702030054600344100503004182070300001354001d006120301420300c80d07281c1011103400c10020103407a96665079001559402107075450804142c40911007004280f45c11b02c0b0724402e000c09958640d282042903a2001c0070800c90345412681c0e1850b0740b12000001201076 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 192903255 1250 192902005 192902011
    0x807090b030304050a060e0a0b03070e041803020c060322061b080403020d050f042301020c0f0a090905010b0d060207110a05010c12020304080a050f0d050f0d111c0b0306 74
    0x50042c516050500f030110301c64135007a000705d005104108004286030348031526400010300700fa400d80b030340300c3c10702a000400c07144030a0100c0784103074103140401c102003000d0070681e20721903410b400500078210f42006002c2183c0005082030344007695080000c80410621030305c0640b05224020000380320071151249008420701030b041c41d08114000707040000294000a06030b081c00f10a080c40307034595401d2250102c043c420f58208400c021980c200b0f280381c1d8955404442d040c000c0903000c1e0f03420898110240703c0748000d03080600c0d9021102220400001c00f2540c404140c15004100104107407030104080391010050110856030b145c0c2c0000c0d00381c01c1c0300040122143c1c2c11000c030350814003a8038150008203819031000d806481c0040c212056000f46008104581c010302681c01075685000c3c4500b0259103a1001403201c82080c0503280b00504038034442c0040f200c00b00c1803000d8203810005206003410081641465003a50410100a0702070501d013a40b03c1c242000300703209030204100a1040034076050a0005e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 192904505 1250 192903255 192903259
    0x4020c21042d0f08100c0302030601050a030e0a0b040b040b070804150e07080601121103012a12060b0316030e0705011103040914060a12020303190e0a0807090b 70
    0x280070a114940840e108240c40c607a071655000b0441d5621581018044899400b60b010a500703d03200090f65880801d090b26808000c444c10000318900d14003e4040e84021180c7c14000f600400c50004581d0080d4000c040315008002201c4003065940e43c3d0603211390080e541030303941d80700c04000c10040000070054aa40810585811542401c05030713030301d80340a40c40c000c40d07980003900d071b4032540380403c030811541d401000c0807400c4604e15651082e410306940044c181c1500d080001001072501802c050040b82c00c44080803c080168440884113403602d5400c1500b200100200080e0000304408203014450152000b100030316607d04042011240742204130030844185801e007503908203460400b10302c900c1198020300781100c10101c1e1040c2503046205642044801900d070290380e45003d850308001500c21101030f01e00d035100c941c4480401940ca0044a8025850b0b8410009171000e81c0b2200141020b0303441500381600c4076010b032400204a10207541003440541c0c0070302c0701003203003110b0390050300c011a00c2 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 192905755 1250 192904505 192904507
    0x3020111310608040605091f021804051902070507090509010204050108060f010806221503030905030609060c090f0301090f050601091802041a03160513060608060907020c04020c21 79
    0x6045400f400c0390b14000c1c006454140e0f10345c0004c07a204428442c0d0b05400b50740d00050b00450046102e031400a400601c03c103800103100c03110300c1107541401e1203240d00400c0200002c043d400ea00461990103507025507011242d03400341920000d400043c078041c40303001d003080c040007580303031410b040004103440c400401052040d8400131183d502640c0006109070801001d90750301381c0105030b10050524850103154080718482c0752203040c0e140510f00c6444102500c0c4203980e04040306650700100740d80c50506599108036130b0001030200c0c482045076070080601c040040d0500c145414503000007800c490790400c00341c5001710105d0300c802c200a41800030328090724600e030301001202c1011070743c20450104494002c1c00785550f20b0030031030101c80240342c051000308010b0449065030386042c80d09262145900c03a460141e0150412121a180c1f140100c0c010703520309546018196a13000e04004030900701820320350030740c0500300c20803015407501d0000f07000400000e4010500d81c60001400e040c000081001400200c00c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 192907005 1250 192905755 192905759
    0xc0604150c14191e030e100b010f05090102010b0d05011b03020a0e060304020f0406030807050c010c110d021f02010227090f22030f020114060a050d0302011131 70
    0x10002611410481c0700340012010120a000395401c000e2044070b00c030450004c100280301958980c000c5600c10071150190713160624204412000e0b141d100c01d10a0204182281c4107003181d01c21405817030050340520004c07076410721520129076080c02d21082078401c0e0351071704402501d0307000425089400c850700345803c6140049281c03006001d0491501c9071480b407913000001c9015136480200601440a00074000c10405d5070300e03c3c08101d40d41c000042264140a0381403406410740c0074521080d400d542041044004031f80400411101c00c10f040400c0b13a10413403202c0792040c10700c407604080e1035400c0c8a03000144d4864941240440c0c00500c07138000c2402600003480100d041c1c8498072210b41006480b00d83d2000c540f661760040031030901c0d559095481040c0c032840b00040c560312001d40e0750303041c1041d002001000d6003050104002d110480314190042c1c0d00e034a04112a0418160000d40c8601030b1000044400880d0110310842e8410150204640d42d4441d1080c081d10820000030b40402400ca49140710f18 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 192908255 1250 192907005 192907037
    0x20d02070806190605060d020a08010b090a030b040204020c010504030503090114091005090f120406030f0216020603070e030a060606110a0c0b07020a0e0906010e010801060b03011701020c0604150c 86
    0x3003402401c9903c1d0b0b4201007a10104051542c00c1140a4600148a46d0f110314880542070002c0d00a034143c00b00160740d8400001e8a00414001c4402140000d4a8182000e00310f44944e1080c0802070001c9070802c0d8200038030070782ca06086c882d03540a82c0c840d17542d070369a81c101544854207440507001d541104101c88000c0c0041901700080340907440140d444081800da4070444070302d041c1045400c1ba1985405030501552000d11b02d04014402e94041c1d4604220320207980c160310081b4001d6404080c00701c4143c2c40c5110140c601140075590103000d5242800101010202003420300500d807200301c54080d2a0700080c090304c0e403c00040000c80740044000c20324a440360b01c036800d1403059072140402000f8005081d4040d521071030340c4480a0641c030810802c0d1820100030a940e119001d1041c0d404200501c03002140110042c0a0b40049418103000503041d40d081c040c2043d00800020510343d070300e6600300f1080c150a80c0c207000c0d4034030980c003445640c0c000010044c80d03001550414100c02040102d0916003003110 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 192909505 1250 192908255 192908263
    0xa0b0a0f0b07060e0705030d020604031803080a08220c08010e06160804050c04020c061501030e03092205010807080c01091d0712060b130b1908100e07080601020d020708 74
    0x180c01070f4011540c520134042d214103048046e0405500350040303008180355160002610340c02107200c0e80e5220700b49101700d00c0414540403180070041c03900804200095202d889041a1a003001150740030551052980010a0b6440340505040f50000c0181c1e8007040f09a40a2054910b204040c80140c500d43c646810b110070b00303a41c038003800418440403502140c180241048041748100780034004550740c030601404a96100c1c400c5030180840c1c01080340001044d4400d00a007001401d2820096007070113000000c01c030200080c185140a502041c81c0055102006400386074020b001580c041c21610f424051141d050142000099050085030201001407002d2003201d600e10b49032240003c00c007501d881c28100d1f4031030000f10141c02102e042c071201041c0c0c544404014542c0042000d6a13841c1c641d82c950a00540e4000d0180511107a10081240c1c800716018101a0343e0000204400403c0e440d1a15140c42c1146c0c020f036100c43c005901e6104016055804000c02c03d90f00c44180018101a440d0503425552 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 192910755 1250 192909505 192909517
    0x3070f09330201060305010207060504051b0a060f05070611090306010e0105061608071b1502010515010c050307060606030207020108010b1303030e011206140405070807020601031211060a0b0a0f0b 86
    0x507095100110380381280b003984814082c41d0300400035941c0d101c003814104080c000a85080e01c80f40945114820307103c11811019040340e0f0090220042d85141460035180d0344840c1e0001c4081c0f1004128201c000f8006116005a80004c1d54145490f54101e0050500c0d01c04140c021149050603880140207965030a0283c449040400a52aa1194440c9401c0146000d440c900070040352900e0700090036201c1803109401030742c0d110072104030a41c4042038100d0a07a0820364514204001000e040549944504e4200300e85500500c01c423860070410f0f9841104464280d44140d00003907000c02da850031581d2002c08980100f00c81220541010110550210070034128480102800003100114145074082c1e0074044071005824410071409035550000d10320311000f1807145214a28150015800c00d00030150580108441e074001e1000e6802c5980d80c000200c0824075001c284034035060032290b0b400080255621407101c2400105a416596051001c461846c2d0004513002080390030500240c8010800e03102 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 192912005 1250 192910755 192910829
    0x3131214120714070b01060f0c0c03140a0203031c0c0504030308190b0d03030614010c0308131b15030605041b0c06020903070806190c0c06021b0303070f09 68
    0x40e56444000054034031101c10710f0060140b1002150690620004814460484007541c6422100d0b80895100301c07411444070b4002440000c8031601440800c0404154246201150003150440d04560b00003901d59049a0f102003803000d0003882c0000700344201c1c001c1031030952075420441c3c00c01d400d6940180c21848001c0c100074100d0040e84001c1c16000301074000c0b078104a005040e008440e0603d09008010b80f0907402441040c003541d251f82d0400d54403c4212119080c6c140d51069030641719120540704681c0400003d0304d10709450941031100c0008410100014100f80700001c0701080701c00006001d036141d6600c2240b24503e0b140d20b061004918002c0300c1070201c4189441c0d440141d0903e0200001c0c02080e961580511503918040360007100007611a010b01c880c14507800c2c0c0c0c001c0c1e141c6001e0a807541d2250f11000036000c69059000142250058100400803506440c0b5000245900d00d1458008844840015003078000216a581e0003102c0d4001901d040c2100d110224580c00d49403802e40c81e4849068 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 192913255 1250 192912005 192912037
    0x313030207290c160f0e1308091c02060a08092a0609030a060504050d11010203090a06020c030910090f080705031b060408390325030803131214 63
    0x80b080d002c0030b010320100c5074a1184201d03005900d400112036407414a000b00546c009106010401075140c9000b010b01c0943d110403994980341c07090f0284400f0440f445a0138003d190124a0780c40141d8901001c0c2c20352400341e40d29a034161410a50b030318941007441c410400c4030814000d01e400c80c20b0f01298809291001a14000d54441d04003001c60701d8841d1070400a820b0528050074030080050100e485031a104007680c440c855103c1c0c0d01580340c203d02c8180e802c005a90310964215001840c2d5402a0084c281c03a10b013903034100a01040030594031902e070304401c800148800014081600140049005015070b00000c0c4400750420000c6652103000c200c00d070180c0d00743c1103e001010380d00e00f4100e4002e480350a040d42d4580284414001d5808100046d005050702e00d0358000a556400c07500c0030544c40c1000300280608050140c0051510f42c03540480e04005000c0c000120110b04104015402020021504015079003030b800c1c45a600042140f0041c2008041c406000c003840b41d41e8141d03202144460307900 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 192914505 1250 192913255 192913267
    0x90c190e031609021e12010e0604180309030b090a02090f0402032109150f0706090203190b040c060212030a02030703060e13030801050306010506040b030c0f031303020729 75
    0x40c2c0380c42c42ca880c0c000303500e00000c035000c25900c2454016180313150420013100c0390307180a0942c8410600941c41010243c003011001004840c0300d480c02c2e540c0101018100041924161003030b4030401c05d09030380c00e03400b19602d00410010080e6803628664040800b00180150229581c000b81d401003001c1e092a80480191000c00c041d90b07400d119482c00c0c60000340300100c0700707040400e5104541d000a481c0610039090380110344195001041140c480300310100d08035141495680d141001000342c003c09980600c5201400a20034050611094840b070080364540d5451404d868041d902161030381102085410000360203031040000c40075a50044140c000141e00c80d0740380c4000b1001400329038000003103d0110002d100c0380001c40c3e905048030600035616006103a80320018160358074002e00c00c0c00e0b0400c80c2004104545000c44010710b030485100c1089501d04280043c0c0c00301e00b900b00351030004004c84a60300f1101015010030242008101d201c0418164500224a5011a064424418580410005030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 192915755 1250 192914505 192914509
    0x16091505240408070e06010320030414101409010605030307030815090c0307020f0c010203040909140105040b010f080a08090904030320031e04150e0a06020403050c090c190e 76
    0x1c80020000191030080e02d85580d200d14542d29050b5101d4006010050070200e06154800d0140e400c130350101e611000030000100207406156440100b060b51a5140f01000c2c943e8481c0901c51f1030b5428003080c4000c83c034000101c4044030211000707005140141e1403d0000c0100745c4010040c1c0b140c1030b80600303007218595105000d034903c3d521656815a0302c650540200314400362014040d50141019508480b1003008070341603d6950b0f903010b01440d016a105000030080001c20b134000d1040c26124044d40b50b00c02d0303860b8401300c1c25600245c4d003c440e26180745c2c0050184041c02c82d00c060003000c9210041c100c920300703a11058283d1040d484840e000e80904d000080515001e5080105c1c801040c41c0500e40b550303440c4c0400f44482d00250f0348409944407464110780ca9100a000340d90003590050360b621189201142c4440c02020340d120301e481280981c064400100312648050801980214090842c2d25a02c008000c41c1346c034000d0015101007414850880141c000308030020000b2458200303036003103290902c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 192917005 1250 192915755 192915799
    0x1802010c0c08060708041e021e060c0f061806010f05090a021911011803021203070e090703020a120212040b100b0a03060e010605040308031519030516091505 69
    0xc90b50740d9100c0c0c802407195460b80030900b1480780d03005804250840c02c40300038600050300140c070086c3d484142030030501000c140c2044601c092034001000360b840c0000b901d4209050854100103040141c2200041101140701808500040340240020340540d60406800000012090107881c6c001c03010040007511209441c0d0450b0310300041601d04501c01d5101d0540101503600c4417007495025401c08020991018110307204c0e61200e0782c0364002c1c04c101003911599464035040201884204400c0c1070300d1142607110704500303501442290ba00540c1d1100c504002400c0a042800e0302e14031b4510400403081c920b000444401d4016a010500c48415182c0f0324503092030244a03081030396860b0780000c1380b9448070782603803040d000c6541800103042540ea95810540b25070082c1d100242c0100c1041001600d800740c0791031610601c45000700083c00c10740030303000300c8590040540c204450300e80c0b0030103d1411588400c0d0640b0020700c00b240003030112140d00f0300320b001c0926962282038081e006502544603004041e075 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 192918255 1250 192917005 192917009
    0x22a03070b090c0f0303031306150e0106020f01050f070503190b1302120f0f07080907030f030c061d30031006090608090a02010e0d1a0a060602011802010c0c 69
    0x4015900e07810044041c0c3d4580d4079034900300344101260283c103a8141404415203101c0c1c0c03040503507014020b1164580d00080c20840c00c030001904010040401c15008440803207000c1d0100d5401803508020741540103003120005480c03d9490b540302d0b010400c1d010350007000c4a43c090001c500702c5140080800012000c0c1070050b0581d58825402d0305c5201441c0419406000d00320083c0034501400d880b8514a6800d40c10159003000c46044940001101e05001d40760039900602e0f01011504c01c00d90f2038441c80d15690322407804800142e581d989100500106028240c98200c20b031b0a11034000e0b2b6411011942c0701c54004024058503086808801004000190841002e1502c0310707081c0d591a002241d080d25414074010403001c2034520501140b0203200e8041e10340b2a8143ca4014100500c242d00191040d0032030f03004c041c1c5d002e001c9a1f510700004030b07201038410721500603585004184c10180000000e46000e5008941160700d01002c4108104007035000c10080703602030030403502060407814040782c000815 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 192919505 1250 192918255 192918263
    0x206090304030f02101806030506031005010f06030e120c0c0a090c0804060e0102040812090a0605250f0503070b040506160203040b03060105090a12150911040c03151d010504022a0307 80
    0x2406c2e00041490b0550841e5201c0c0500314191403154010420074021540d0a00600780c030712000741400e004450196009400c0c0c10010170440e104c40f4406005004180d00050007407219821141e4454890b0501a030058080e00c4009002d004180e45030348018a18040200054541c5071280701c2000d60b55403c1d4125405865400306560522900c5081a511584040320b00c9000f904507e0001400c18859025200e5007000c0e443c2c0240c003984110040d40054801110644507051092812000500200010219148078484038001e504e09820401e0600c8001044400c43c1d12071f0014411b11568040100d80548280c0c102072900d03034075941d004036003034041d02207074a404c404142d00c0402c004040c01c1650b005d4a100341c0c1101c1c000004880848155100700100030304e051118000d824180c509034100f04400300c81032070001101410840c0201c0211b80b00e9010350300d01c801c3d030b01c1c000013511410150580500f4080d20107520b0802030100340c206608035004008030005104040e01c1c0e601c9014821501c1480d00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 192920755 1250 192919505 192919547
    0x14010905240f0d0c0305160803180102190b04050f030a0c0b154903050309010902041a0108011203020303070f020a1b3f11130506010206090304030f0210 67
    0x500d0130702c4800d107040c04250b89511a041040505150148224044e0b80b4120042c0d418814a095800341d100c20102d2400d0540c041c082c074460001c030101c1d456012160190303450b003419041500301142414909100064150410060008080d40220101d035002d0352204c3c40009030307034a009480081c010021030495210700f80e5140c80c0741000d00400c07400e40303c0154000058132075129440020100f17000c213541000105a4080c01004280260041c40c1c1c804002c0001090004203540041c0441b40c01200090003c0881e8040b0355880d603006944a01409140203015440039007070303d0180d036034040280240c00b001224040081a1842031146842d62580320601c9242e0f900c1d4104220f0410312103029041002912603046101c40041054a00401e0300d206a440da40450301402c442801c204028140c8449038050b00500c10307a00d80c0c98420358911306034030b800a0a403c003400024200407002d0203048080c2c0c4240001e00118100020808005504071034442200041050135540b01c545070710035102c030200c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 192922005 1250 192920755 192920779
    0x13060909050f0d080f0610110a06020a032306040903051e0301210c090b030c120a03020601061d04020307030b04050403090509010503030a050f0a030e030d14010905240f 74
    0x220014050559201c1c060030350b004540f00100c215200c14080790510107111508001c5101e84c10000010756600e07130b09140058100d10300f15802490185907000448402d5400280c44199581c5803141c41303d2200000000b02c00e50f03000e04c17043c80c40d100b03002c5d003124807985c0c0d01c4540501305802102107803222205d407401a00203000f1000e0441c41500244500c3c0c001a807040144a10100900780c040800c1e036002d840b0844940c104801680144103c0010796018800e15054665650350900c40380086000c01d001003040064600e40241000d6041c1c1c04001400b9456a800384000344103424901d080a0940700140c0307a6803000b80880c042c1007812900c1e0707040b6107008203000906503c00c840e801075920642e045030140e40d9420905903a44110566600021424000d40301d41c11840001401d011403035240100d000c003d1045080d045910428004d44010f0b9116002d890300204000d1003801084540c00800a030300e00141401180c00c00b010445506824620f0030304c0381e03507035142c041d040707510b0001d024407414034 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 192923255 1250 192922005 192922013
    0x5090408040e0105040603050604030e4005090d0f03090c0806040506160e12070b04080f06070212031303030e070b0a1d010c0209070507050303070305060f09040305040513060909 78
    0x20788280905001400d9490020030300d81064000d01045a0f03202004241c10303507854804640d0100380c1010540e010300c03010403800a42e8000c2d040755080c044032401000b0016040681c004c24443c0d030a40075404203041034104441010f020454080e10b0442c0d0070f101c3c9600010382c80c201d004022154005004032600345e40410b82d02c0c000103104d807095218404427004c03038076200215809410204100c0c0b002500c60ba401151504002c6070b40450002203a080300c241e2500d45943c00102d8009400100465101d0502043d42504c2000104d0300301645001900d040145e10802802c40d1000070440303400e104022089200301882948814100940541a150a80e45a03000e007030482d031080b4250400150000041210180440c0c03100031740e5070050311001c1000c076165003400110718000301248148002840707400d001c41c0f000e10003948203010350390f000503661600c8030030002d200001236000380c043c141d08000c02c40041d80040484065030003c5072492a000c64035501080035102a4002104003424504200200 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 192924505 1250 192923255 192923257
    0x303010f060201051e010b0706090f1412040b04060f11010c0504092412020312041508010e07170a06050301020408100b061207140c1b031b090411060405090408 70
    0x500c1076075009201507207074a100a000c03520204801c0a00d02c0b07116004002c2c00300510000c00301c00d4401c09022810246c5511840ca501c03000707010a4806880052800c2500c03031090001040c0c200d20103205038103103410036030f40390f03000d01450007010144446443c0003084180160346800904890174000e02145026440003080e41c0c00c5031003044601803d000104140c8090513000160aa082036918080b035071410035070b1414842550020b98040c0110003001000d404240001d0016000405041c11201180400101001c0059200368902c5100d00d0500001c690301c60600740a40da612040341036681c64007610000200364030341c4081d80c95840090002121003010503e41c0019845600801c01c0e543d18100b0b02c40c175489140c4030341032003102041c00540c100f800780c4121440d128042414500382601d4442c424904045070300c40045210782d8a44080051604022001b100c020802c24502c8507120303080460903258002c0d000030103400c08420203601c00d0b120030064500404004081d01c4040c14107050445c11 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 192925755 1250 192924505 192924509
    0x10314090d030c0c020f060304080403020604030c05030d0503130605150a0e0a1a0603040609031806110606120a0209060d1a191803050c0a150f0e0d021203040804080303010f 76
    0x210f810700c603a042d40c1d180aa00100c0d41c1e5500505202050310b00c0e003003008003580c030090040311610310900001c80983c9490000e0300c069840386614560f26400c2c641014984018120380c4000c01404004001c070b90700300c40c0006a0300305d5121001180584800f4408407058000d02c110a401140c89000090100200c51609018078010703881000442640c540062490f4a5412200c1c0c00000c2013000c41d0002c0c4555018040450003440c286c040300c20840200c10050416901500024460803601d814440080c0b100580180049850f440380003400e04034203441d0758188101a20a0b040c00002850944500d00c02014450744001071620f580348422592a01100552b8140e1001c0882c1c4a0b10040041074030401d07a80c5840c2d540c450202119981d02259141c2c0001901c10701805400b2044002070801c080345501d0002c00000450a5038508884c442107801d003240340089a032000c500e00f40405d4011407401842b4680810096036039686e400c0c89a090b120300d501c1003007548400030000401134444118881 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 192927005 1250 192925755 192925757
    0x61e110706050f0c0304170d0609020a02061003050d030c02031201120302100608120304060b0405012c010f03060203061206010305061006360e0c07050d08040b15010314090d 76
    0x20342c3d02c83d0031141c0c40c1460100c0b0801494042000450086007880c0d1201070140705100c0e940e0324001d00701340d0300c906464196100d5403580d074021408000c103680600404d540071041c8421000c2440c659140e09544150035034804080c140d44a000344543d038404e20480381129041100c05101d941d44490056103516072060590050152042c41d1034029a180641400c0351000c034020702040101c003400d02a1a8005842110166503408542c02c42703848600800c2e000b461601040c610130080780860b18411054114041040e034035540040c006010340c0c041d010103690700050010303220390b2114003050340c03941d40c03d1040c101da1041e00000420801d00043d10703072107074550701c400c03800310b139030300d0b0300982e01c4201c40e41810444808487c4099a07206c65038101c1c003480724464885c0c04040c0c1da2680a81c0302400d091300ca1021200f80054408240203042184859032980d42c6440b03201450992038083e1136000c040c000c0c4030181c503281d0050001e84e00c207030403252051203400d440e5801424008001659034841640c10340c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 192928255 1250 192927005 192927011
    0x20a03050313081501060f0c020904110a120c0308220f08100e150402060d0f0e0706020c090403110a060609020a03050906010513020f04091d0106050604030c03061e110706 75
    0x2c10303010f801203050702c0005011181c14069900300542902e00c840da04249104000040f05550003694400b80080e0056008441502600341d4403828000c0c1e500f215045100326003852035100b0001500c1c04410400c4a801c950050b441d01404005541084440110706065004818002c5225441083d11000710360a00084450303100e210b1481701c0c15540f0680786c220007604050342903920b50301d000c2000c80d0301c280300030b1049103007403010b12020049501d058080111107644004807994000100401c0001d082140010030601250b400011040b5000030b000604001e10000d004220750340400109c0326440d072064003804099200d0346164020341041c1e5283c00000d0601020076080c0402240d400c6c1a100c01604011f503d0b210b42103100d001c1d40c0100558091040c00f0040002e45407000e02c41d4002c0c1350b403400074850110245a15150940e040c81d0485445000108001c00c001003c0d005d22000b241d1b44000c000c140c0c041c11866418003060031850090540e400e19040702080d00d1140700401100e48141020 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 192929505 1250 192928255 192928259
    0x3030a0b091009090218090c030c09010e180a020a0612150b09150c060c1b030306060a0e0402070203010c031b020601120b131209090c0507020a170109020a03050313 72
    0x7454031001d6401e1074441c00040da050103000d8098000c0c3d20090300140420401d03410051010341c0d03d0500f250791000c0f580103c903210403240b505010410750302a00301c8442c0c1895041400ca0070004901807c0d0741c84400200c0711300300200c0740a201d143d0302950018444486a80e0350800548040102a510b8580524202d4010b64481d0448150f209980482d9100d0b4149400768043c09813840c6842025601c480d824080f03046c018008102c03592044281310a0143c1b2080054800902000c200002103400c0e08103000b040440c1c1c680d807003a07400c440f04500c0d080600403e002c02040092007003540c0650107508100407000150b4040e0001d03000750b404068204904080c84c0001c07a15000d00780650403c00f402210031101003256051000d030001e55054500b900d082655840010001a00d540000030505a107800c01c2066003034404c1c015a0000d50030042e203000345507400100c0c10019400f810b000544054015010444250b118614056020704881041c54507070420325601c0d001541c251103081c4a503000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 192930755 1250 192929505 192929509
    0x8100b070615170c0f0109180e010b1e0910030b162304050405060a0f030b060a0501030c120504060204080d0203071b18051306110a030507020303090d11011b0203030a0b 74
    0x209401858280c3e000d080d0030512242040400c00615820904100c00702d100460701100c0e03000b40c0c002d0080c040c0c074001041c0c070f8005049400d640c85061818841c91500c0c1c1c0108119201e01c0c82050b8130803046503c00d03160386d190025200c80324410380001d4100c0c0075040800c0101d154440b02661200002d441d40c18500e10340c015442c3c120100039280c107050b810140400c0050f42410b40106411100c004c00722410103844030740c80070384000245d00907542d0b9401c1005100700c40c20f080f05284007070701d02842c003031055181c2807002610141d0740c41c01d0031010580c3c0c0d000140501038944e050f20b0103455024181c07201c241003840006d41e2908148010348014541841e070803081c40a00700990f04071480d070520089051007100e0004000c24004001612480301c0c0803465000514503c5401c81c04901a45d42d03944440d030102c0003c040320401081e100656004106000e66800b001422405c41d04a620f492103003140c2c010400c0340540340a0000c4450a094030b601d0314141600440030b0f500c10030300004200954107002003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 192932005 1250 192930755 192930779
    0xc060301140d0f0602070317101a0702030115170f031206060a031b03020403061a01140703020f0d030509371b180b0303030f060108100b070615 63
    0x81100c0c4000300024020740036003003035050307003104500503c650240c000d144d80719036080c2d078840e6808030001000a988d1408a0303010011154214210380e880c4054181010240323440501c41c14058000b4240c00b145201c1190ba00b5040040141541d0308845c42050340c420b0769042d0380a500840d0a42030041080340c420048000080c1d8450205041004405840b83c50a12030103034404001d2104041d120f421500002c880401e16003a2408541c1e0016036035071860800c8002c407094070700c04e00d0914001e13040c8095a41c2e40600070105016045000e10b94500d9545001d91402400c031b29404004d00071491003950781d0390142d0046100d201c80130155510705813480030501146400d000c03101d20104c0c400b400203101804501180b83e003a0b104001500520160158540c4404c079141d010044c90744002a0072102c944103030240301c104010a6005505600f440041e45000ca90024440c0b410000008002a0f030605504100001042640303525540c0705098202100035202c21108a044906075a40000d89040b88c61 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 192933255 1250 192932005 192932009
    0xa1707120509120f0d08040f240b0d0b06060d0207201002070b040603020a0302090d050f0f0d080610050906070813120503031503010608161401032c0a0f1101020c060301 74
    0x4002d401c540c00b041c0c0b0140d1b0708420107881580c8040b000c050480000c3c200030a07a61200c60300320f240c00d0742c06124042c0306041da5805008a4014080c81c2c0c0c4500c006a07680c4a940d40001c000c6075540e445801c0403170301c2e900a008400c0d01604800c5944c1401c401140d0031201c0f440b40740030a0307440443e2031a80300400c0c0e030740f0005482143d9a8400810040280710700c294040c000200d05807802501e0080700030300051810260500c01d5946800070b0040018240c0200801108220a00050902d501000c00040c1c040c1e007000300110b00810340c10030300582c007900c00c0e011258051801450070343c842c80641010800b80d008003111110200320500c0c0483e0f250200c006c40080aa4850000d40c03650342c510b401c0300962407500f840c1c1505036480c0d01011680355024402d0075500c03000305c04400c400519104400c820811400e4440b4141881c0c0034002d900a01d01d0200b0044200540c200944101c11203050071340b0b0845d0388000a4551085070740107104000c003002200504180980c03c56848101000030026207100038 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 192934505 1250 192933255 192933283
    0x6110a080106030b0301021315080109051308130503012d1e0207020f0a080f16030309531516020c1003150b0405030a170712050912 58
    0x80360040044038400d030040308a980014001500f49403484004000201064005011400c5902c164104141c3d120300e0701d1340100000c0302c0a02090915031440c182c0240040409008100300080c0e0301c1d5101180440607004000190003008a11a0325900c10420101c00ca4040d1280315089079658088200380100c1c4403103503a01513828004410010741100950000d5401c907000060036000c4c1503076944080307020000b441800d010f000c2d80489a0380407070030500d80000c025812541c0c83c406001082d40100307400c060320341c1c4100c000c0b1003881c82004401c1340c1c402095000364410f0607518a4054009028441c11a00b250403c4500203c1c44500425110000b14a00c404003180d96800288826068112910490000d006031100700404001150480402c02c281c5030219445060039035221400788140001001440e81040c1890700307080004c5c0c0c40f07543c0c0d11000350100ca001c80c1c41c54072191403001154a46548243c40381e6100380842009840c9400090009108040c100c5c60004031403004a00400706601ca = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 192935755 1250 192934505 192934517
    0x121f051e032503030f140414270603101401030609050708030a090e010e1e0c07020612100e0415020a030605041407020118020d20060310051009080606010c080f120406110a 75
    0x8c03c6107203004521201525940035000181d010301c2a00501040c2d000d44000c0ba10070300d408d02c1c000c1c041c10300c1c00c0104130100141d02c2c80e0107141c802e07440058502c00d0540f58810004078240c402030812034940b001075002005203000000708500c40700d0700000201d00700c505068110715560b03a02c4d0350300418903500700d544041c3e1322a20340640c01514841d1110a034029150040103040804540104101d80c10400c241c1c500f031400b002c01c0c0228201c4014040e00182841581502d543c50150f5402c500b0301d21500360946043c6d000308280071a5400703908124050240030304100005840748007201d1000100340c80790009940b910305201111011018801d020b2500680070a60404480d42c0384102440f9104020800804111010702207568900095024040e1610050200b41c100030403c013010380c0700c40b5000140645804204400000803031440e80c403041c00d0038045e014020a04082110b4800c0860001a8081c005903840c1d04282d1802d20500807409003904200b20407101e254601944150140d201c04142 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 192937005 1250 192935755 192935759
    0xf070509010e03100c091d09121e0a0f1205010f030809061b030d18020f19090c050c1606020c0d030c08121f051e032503030f1404 57
    0x40075001040c041070003c3d04a9010135045aa0b280440c2e00200b10350000660414003080b800590341104007180358460802c40075410011141555800e000d244524a40c40100320a41015551201041d4107440301e01c10503a1040e4442e00102850f00c0d400b040700100301c20021146101d0703414840c5171f0682c2c860081900080d0300756251802550000301b52154407a408100203032454160800c0620801d00500095445c0c00c01c610b450000d42e039100f550300840e400c0600002d80540d0341c0100f40c0081680035518030484540c1c50030915405000b5412000e0203a040c0030034121025407007002072070044200c41c140c4986100c5141d500c102c00b04944039000041e401400d4141c220300d4004440480107100782810101c1c000d540e42c40c51200d4120344031038085424900108502c03040d04d0044041c1c5808943d05038a03042c1e0034640041e00e0544070510030710040221035071101440d00c0400c40150751048902ca9801c12030019480c090b030490319404101c000680d180080c1c1d40c514010050102040d00c10100b04c0d0500f4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 192938255 1250 192937005 192937007
    0xf07031505010807050c19030302071403030609040b090a0203011d0106060207030f12051603081e040b0c031e0f040210140306060d06090c022802150306010302090907020303010e0f07050901 83
    0xa0070a1212118a000e40400c07200c040200c0c1f140042c05030300c00c0c2c4015031261084e0500c00b080340314042004405400c1042040700d43d680c0d054901d41c0c815801040b401d0b090f2211050300c0d20b03040b0011002900742d0300c0c09101640c902d121540745000c10344401d000b48026a22208100c3e10f51046100041a0700c00d0301a0105c0040c0d41e25040c25880a030314540503007040790f07400740341d03071844d20361001900800c41000070702c014942410144002c0e080750001c400c01d6030400c1d59401641201c02000185612408408202d2541110ad810044101c6100181d50207060402040015140c150340891103503414400000c42c0d98002c041c80c00c01c103c030100003103045603101c40501c0f4403944040540880c1c955a06130104000c0b143d40710f10210040e80e98001c1c40251034808044004800411b00b035580703181480c2c84c0b01c0c0145da07001e01d0303481150311320160a910780c3c803440c0040e0702a010f00040e443e44003071148204241c640e80000030350304881d0341b4010044c4940710b284240c50b00446c10360f460400101c0410000c601d175 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 192939505 1250 192938255 192938257
    0x110a06090501090203030a0c05070512030d0515061201090605040902091513020706020c060105030f280b04050a05011a090402010c0f0512090f0a0510260f0703150501080705 76
    0x501030700000c2058141d950000341158000a0b000700031503803000d015030611004009050140030150742c1d818001041d200465542d000702e21b03c4d007501903180c1000642e0001000355104010202422164a510702c84006900301d01c0c00340500c00e8058640700c40011186024010b40c51180d4004e000241c1c99243d0b1500b003a80e403070016003219049941240c517000e0800d00744c402000c013540a481c0040e25031040c1e0107000d003070890603400035200c0d07400b1072220b0310f20030408140c0301d140c003180c901c0e60b01d4000e03022011400c145440d0311000d813404200c40c00300003d000340891b000c071501d40724000070030040100402c200d507140030030090150400e00c4c41c030025006502071070301440128020742a01403c00416520140f60900d07000c1d408941190200702e1a209013010004010801400c82c0d8000d2410b0030304010032040c114004e911020421400c110303580382a4110a45240744946c4011746150303182940c0906840070040d110080082d20700000c410190856071709180903541d05940c0e41700c481d12039103021151 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 192940755 1250 192939505 192939521
    0x902150c0705060d0b0910050a180603050d081b04030c120501090c08011e11030f060a09090309050a0e0f010b030c1315080f13020d03090302042a110a06 67
    0x20358861210085400c0e900c1401401c1c00400804011800c81006814000c0200000c0c10440142210365010b211550752480c10000351002c201010707444100000050000e844140e0002d40700c0d025400b1036442c240d07440000d80e032040307420581d03800c8541308403012246c242c42076120160030441103907002d018001c101210100318901400000c5460320058544011440349a0700c0b103941c0369910440d00c074804024008400100000400402404084414000c5540b0004204010300501440005c0141e40d0745840513000e8185c8000401900c425031030003515220039401400e114030441100050a01051100d4511684002003c6103c9034a48404405141c1002d8042c080304c2d4024000400c80c581100010b200811202070070b0f0390440f81070f0300007501000001c0d0441440c1e9010008001403004210000441aa4140c51046407044141012104905160002540107051240600c0e201c03070024000e20f0461082c21010510061924094a0846d441c0c00101019008440240c000c17a8460340300d03c40c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 192942005 1250 192940755 192940777
    0x9150203040e0a02120a090201030b0d05070504050702120304031d0f3a08040e06010801080706080405150106021c09050102120d0204030618050105011d1f0b04060c050f01090215 78
    0x1041c000c12068a102030017040b074015040381e5075080c07044190740e40745c060a0300140080d20f110f4610700a9499040d292101402003c0c003458449010800c154030030490b9a40a00100e50440d4580c00c15140042403020250910460301d1130303098400b00c0c949801c0c041a2031646008195001d90405648400c1c41041400c3c25409241d00c28130403100c0702d06032180b610361528031440d50b95903204d080406c0d89200d240094109410070196000501000e030000403128161680d6041070139a0f40e5039441c1ca546410709407150744600c40c8901000088094002817020304110040c0f119030224403000c40221403e15081c41468010303484902c0020310701a03d2030082c108404080009403810b1349039203c1605075980044130302d07100c030401d08080003403100070720425000d03145166a003148080304440801800e0000360207055003130042088103214040d0710455100604c4410a06030300c9070fa031007130043c1901103100804d480b14040c9046c58002108103100b480b070038036801080f008054041c1d0450410036000f0195290b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 192943255 1250 192942005 192942007
    0xc0a050304140c040e0d03060911030408071b0f08060a0c0509040b011101050c0913140114030c0904050d02101104061407051515090f04060c17040c0609150203040e0a02 74
    0x60850701c89029100b4030905c03000c0184042c4001540043c12035240d51f0001030f1142c85d29840080881c00e1728202c0303401a80051203180c170307050f4605020480d1081c034690340000e0b0022000014002c084000010200c7d8039120945002e0355640d2406c0040c2c0c0d484c096608000f0381c1c20001c1d00440c0c9000d0b400450042810300d49940c2240c0300b200306500710340040d5400c9803c0307500800c110ba242c1c81c01807041000445840340c184009c18141c81e444200c048103008078000050039001ca03a03020b031402c0040c119903a00007407051b816418241401c40d121a0b0a07207004006024118410139070040502071028082d00341c180017460907140c0b0f9022100e04189003607001c043c0d201000702c00c0100d90208244174900c0c407400e0381c3c1210b42c00d20310750001d400d07496001154001c0108008010a80e064400c1c0c1c298020f40252001c200c02844490842e04003003e120020040d0842c3c2d4140010311031250200b13025140c0035107410072116140c80b01c03052041e662100311030042e03000300801d000c0c0f45040ca1260307404c109095805 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 192944505 1250 192943255 192943273
    0x90c020a0501050a020c0606030703030203070303020f090402131802120411030106081c182d0f060e0907030902090408070804050604030305090f090720030405090412080c0a05030414 80
    0x1c5003514800d446484001e84c000c82c60106110040c403040e80c0002c800c0b0000c0c000503186540181d141c0c0100034014042c0740d80440d0340302500300044116400d14400038030841d950000c00b40340200c2032101e801902c0003621a04a0140240b08901c200c600150241e80c0ca041c9980e103036580e441310145507034242c503095503c400c40003a0755041085005040400e03004805518244044005c2c44140007031003032040180541000c111800002081c15012041c0c0e03840c5080d079107604015840e40b0700199008116081c044400010701030b0340103026200355041100c0a02c0c207130700c2d0490308030b041d10401c680282d4410040350101e0f00080d1140014a882403040e0700d16401d02d0b5441000070b01940140d0b006401254001610f40740504c1e10200304d101004048a090240c1d00f8882e0000304612401c006d036024890103030100250345070040041c0c400816000340800b119242034a85030078110301d03119400011440c124003155031064071405540d40450785980300d504560b41c030f0b2100007246403038902d03c00c10381c0075803150 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 192945755 1250 192944505 192944513
    0xf0203010b0a061d060406090605070c0b04140f0a0305070b07030215070801180507050d09020402070c030303140906010b030c0912060f091504050304030327090506090c090a090c020a 80
    0x40001000303d038940001403012202c1c00d6000b107101d0f40c1070500ca00d8080106100c91600442c00e002540e0356031410a0300c034030315480d200a01c4c50642e0840c0398420004140000c901020740072180d0041001d071100703c06560320005000d80114140401001508108000d0181140180180800301d000e40304650f030740d5040030080f403021a02900d0417030014031003500502001900d030b805220001481007080140c2d103001c2c6001011406041e0000c050380f40c072100c0e52000d40d40d9a0701503508a64003d01103104590b41c070314010300103081407244640f07080310f001c0c0010b0b28600b010808a0480301d50b0740032a461540c42c54200942c40c0e21151445901002c81426901c816208100c2140714442034843e00c01141401c1c0139292030400c5100810442d41c0410081100040c0e0101c140c50850380d060030f02e00d41910150207040c0b1801200d0701c003152804001180040c0d00540e90300710710300036403051b188a1500d44441140140300d10808144541024400404001c0d41c007a55104540001680c41541d03558409507403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 192947005 1250 192945755 192945769
    0x2f0f040f030b06041b020c060a0504080709020703090b03100302040902060708220f03021c05071a09010801090203040807110111030d0914070807030b0a09080d09230a0f0203010b 78
    0x2d0b10044811410410642414440d1451101410f2807040302c0640750303d0001d41d62845884114003450001c103d04034241d0280c020f480180070090207954240c0d0b1150780c50b0000b5042a5001d0b00003440100001600c14140130880b80241255a851980f4505640901001d8880e0080480c0c020341c040008001094a03540584100d41008500800d02d0307a902c80117058a20807a08260000007260b5820401642c40c214551140d0040c5c0d000d0580742200c81c10301c9030401a03180c0c0007505904e86458030059003008c01c401414030327400980340e41c400c07642c8039880d48040740000c0310010400c010401220000c0380714100c1c0f1005c4150145803024100e402040034508540024240b4840c0300d0300d60240c0802c01481091800501c0340000003443c450f458500e0859030b9903618071010f815840c0d41008a500c000c1640c0051410350340045c0c00b280da903188001060b00800800005950802c0400305400e0301300c5070341240303486040f01d0768010321121140c0c0d01c400b0404405e5600490b4590347c1d0303d1a00d4002e4540031 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 192948255 1250 192947005 192947009
    0x6030509070b040e070e03030901020c01030f180f0302061b0d020702121e01060e04022b0203150a1a0114090f091806011203020a0b1305010501090c032f0f040f 70
    0x40e0210242e0520344401340c07000d90201c406c00c3c8030745c00c24004c0c6400c80e40d00088020109800b440d01007081c40d40000c07844010328428034502056400700d00300e5010711800030445030416110350b003116065a6804440321400413107100700601143c08221409101013190090811680006d2500c11004564402c540c0303803a4030a1412500100c84200d842c051800a00c18100100451a01188a4602a0f0010714442c185130002c00d4440b04a189a00214043c10750401c2540d50142c1117031811200e5520342d114840040b120498861305101c4071040c2803c035280741a43d5004103844d1041141013049016501e0f40082048980221111341b0b42c0320781ea500c6e403175840c3c012041649100288541e0108503802c040c01608000c40c2250040c513960f0004e40c0c0080ea94447c180c1002c94480c0076140c1d4203404008100e1200050503035070078103001161421442c0c2c400a900e0710940c404110103490001841074824090a5204092800204070790381c0d90080030081c680b040140406500d85500d80855170900c84a507 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 192949505 1250 192948255 192948269
    0x206012c0f060a12050709050c04090c053a0e0c090a0b0109080318100c0b0703050603010e0705150f1c09030201110f090d031209051c090e0106030509070b04 69
    0x4182401018141143d0590180019034103580b9075001c030362101030b40d4895600c544048540e403403000600d81030605066a01070300825205010000c000038006286070130141034010040034920050347d04103412009070304030300c0140f500c41d000078030b04260702001481036690b9070050b4007400044005640d1945002d0b0710a940080c00003070b51141c054001031612050782c10107035583e4000c0250004080c2c4510800b00b01100880b40c04403246451082222080c0f10150f0080c001c0082009000602c6e40640089215520940c000c00504100c1030100d541e40c0900e1280940240d55481400c00c8150400c0c004c05d1121211140e180ca083c1004040e005040b02c60800350f8216a5901c0034503042540c2801600151001810700c2414184c030141000701520a1b440036522850220305420105401510941011a0300c14803c1149540c03600344a030b03c0d01414031103640925484580b000e00d160107020000252040e8080d0090981e090240640050601406402d910b2103640070024480015600a101070300b28 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 192950755 1250 192949505 192949531
    0x816030b031e07080705150c19110f010519030203041a2e030327050418050c060304030206010302011b06050414060a0b030607030914010507020309090708070206012c 73
    0x40c40300c0b8a060091a400110f000d4001c100c0070006a80c4040b9568005030300700c89425907842101024500d01803100e40c208001c40360040044050200460f0140c940e00c0707068840020000c18140111064451f030303020515640600c2c4a0b00c40c2c03a42c4a40e01079540140720304c2645886401440401e401c050341100c0361200121400c22254144c011201d0b00d180040384003110146403070550340d002d00008420483d94614080340031401c4444403440c0d00500003000e0140040091305031300407214111000041c1d06a8041c0319806000140b800c01c201120312071a010b0340504126400c40c1c1c01180c0188014044184200c0d043e0b000c1e0012070620710443c2e000f60f11a542200382c601c82800740da41854001096a407080e480d26203000c43e1600d011480a038440003500d0005000101d518001032850743d0040c00240035868541007100041d000401085a4001103807410030b070f84d6580c2c030100c0b1040002c40b07081006810143c01001a090581217810031100d544503060019010024039011043c000c40ea08401040c2c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 192952005 1250 192950755 192950803
    0x9020d021305041514190f0501032001020307150b03120c2d07031101020109051207020a050901150f050d0c0e0109081219091701090b0105040c0816030b03 68
    0xd0b135920540c0b0300102c1d01028000000e880e1940c540341e0000030044498000c180c66200f80d0401168006d81505c80340030410031031135171241020740c5400ca02450411118100002d581c04c1e560000050781c1c462540400c9542420036440e04110207004508020f07034051250040054501500101415405d19424010950803c0080542c903075a0f190162102000000010b16240d10701d020900d58180c81d00400c01c0c40000303101500403030041582c110080c082d0b02a030381e1842c00d000f03c0c0310000e08005000702d075102503043d1941c0c1004107110b82071140c3c4034543d14085a100d4524090b0202d05c8100c407460500f5402c03e03104180c13000688091558000000d207000c10070001c6507802070b45000c045d02d00c00004200e00d0b05500e50760038851058400070343d0b0703036401c83c4c2c1d115a8240c03048003400058800c001803d00400b83d8098864041c141078501211000080e0001182c1400c0a100d040c10000840d42d03880d8494840b0742003802040d010514500826840d40140101620200980d58088186140d040000d00d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 192953255 1250 192952005 192952013
    0x318040905030a180501090b0304030806030c060a080a1116030e061e030a1a01090302091015020f0607021506010f1103030108070e090304060906050f04230f010314010909020d02130504 81
    0x8045d0030150500824031000d0200001940540f039103e03501d81011042500c4034400240b400b425003210590000c0c0000301110455403110801d40184011842405801d001d41c88403585070040d001c2c51100c0c1070780d002c0700102183c800d000703012001c50060301203450500d140c0038140114081c0c0c4a00550710100000303100c160b600c5031050b101c15203000115a1030003020300b40020102e009031b1102034411600350001c10072000c03400c4074500040210003041c581058099074041c2d210f0006524031016400760741d0019414600124008214844003071001410f40d50f9100151201003a0524250410400301340502e40d0310402c0005502a09039440100f50305440c2c4847d040c85a0380080c0214501d0304240420820030350016104800d84085040950700c4d04c2c0011085829809140c0c0001070000e10000d0100c07540c44070304401d8240c0042580c007001491015001074040d80c0440500d84403c1d40810010000f40c916a0720000c600c5100400e282c0708102c10b500010300a100d100d024124060b618010b002c200 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 192954505 1250 192953255 192953297
    0x130e1207030813020a09022a010b240409020c0109020d08041a120705160804090b0901080604030806012001110d180b0103030f030e0d0e01020d030e0318040905030a 72
    0xc4010f9000340b4040c81c41c55408241d1240c0140325084a56030042010010069071241d03008000c64003a41039600310120100c40760203860761515203405400d0000e20400440500310b8628040f0040c400c50398586860f00c000d0400035401440c403811f66542c0ea0b100040140d96140c1d0f80c1041c10b0169030f004c1c3d140c608018001c5d20381d403844064407001480c1003040a400b800c0e2136000980c0440703603081c80c079200e0f140804260a0340500500040024400040124000718664000d1032074a03070540302c0a02d941c1e210034005643d000d0984001c0c000c244004d002418540c85a8105600900302d020051500c20300c5001036420750302d454603180d4201402003a050b4840d8010320503400141e501704403d17013114031651500d185082060001804011014110010303140c000c0d000414001c1d141011038a43e40d44503c0c00030598450846520300502a005000380024864052003083c898a140074610b081c00700f0070b14500681c50a08500d802071b031203840f5103002c00c000b8805000c1c0d00c10b182d00c039040c451400304800144 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 192955755 1250 192954505 192954511
    0xa060b0103021309090f020a08030c100b01020c0d0203100603060506040b0415060f050403080307051209010b0312091201050c040f0603020307050906070c05030708010f0e060105010e130e12070308 86
    0x109441400307a43c5a40c8140d10310502155420340c40003940206900b4405900590003001039041603008000040702c24000004003a001251800e66411066500200003520403002109005912010b400501481c000c11800c1005100804540d44003150b8242401510b20a500039500b9a035039108101d040e0409000329440b081c0103c604011110000030140e00d0901c040c040c0c401048070980801080703a0284044034003554000000c00d40300d107005840200035030f100d28214130440350f1140100b218900140501c0000030001009400c0300c0380700b180211520f4010440c51540820b9803a0603280108081c440c4d103010b1303d18040b0306035440d0f090400480311482c1c0c0b58021810117104108001e6016031010941e00800002c40d40d0307556408a40c2400d8001003115040203605001d528000a5a1030741548445003114002006020008000003101e031124024401d060100f0413600680803d880d101000c0420003400120003d40301d00fa8002c128940905160602044100040c0f14824103401000007030b8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 192957005 1250 192955755 192955757
    0x1290f090103050607120902030a060204050301140907060509030a080301150f050f030a05040f06152105030405040e0312010807031a13030e0301180602030a06050603250c05030a020a060b01 83
    0x426545955201e40d13584000070100c4042140084401180f50100d401000342c0680090480d510f508080c00c0410095100c0c1c89182e205c3d40c603107060348200a401e00915485032803030b071001c2c0811600d00342d000c5e500340c1e015032a030035458014400c4590015600e4000342d401380564512803400076004080107401400a441a2420f0010900254480a000504603940030038001c00220b45901d0b94509181c01070070a0000600090500041042c500c40d8552002d0480760313907200e80c0b80d444658400c045ca0301ea85455000e40990020041481281000d07003000404075641e000b00ca14156103204450200e02003070b00000385c0f40c0c014607000c20500c0f001c000c0111900c1c00c5080700030801d040c0010700380d40100341901300174107024041c1e0300f07195070355420361050481048400c5410042c08140c80c10400a500843d1804919480c041000c86c0070700340002620300c15581c083c40300600c1090b40c00700c8400300317143c46400b2080241400504001601c00e002a114441d2503800503e208a1580340c9981581e002d241064 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 192958255 1250 192957005 192957019
    0x902090a0b072109030818030c0f0303121018090303110301060f2f070f0602030313031206050604081501091104050d0501021921060b0304060b0301290f 67
    0xb00224004004071a0954030079158880b0115000c6825144a4104d50024150005c04a6028600d50180d0009048041e086040d20901d400040411403052281e10460380c0540c024080890705e074589451a582001c007075480403d040b951044800c40324905101d020350303105d4031040a4020035426005508600c80b40c1c0a42a08543c144074004160100c044a44801c0100560400b1511040982489121030000e413058481014107400e50b036a9014a03c5249159030405400040311840072094030b0042d0246d0503100c4194601e0b4a00300c8407403001021b00307014565181e000140b170f41d44a40040008000103405098500c40902d03c0d110110016400f04680c141000b2505c0b80c4110030008a5040e55030482d80c00181c1d60f11401c24a00a009a4001d0740f079003030085103421201500090f4402382000d6182c20325000705007142406040c1c80003449400c2d026041800400c00003403094008030000f01028000103480101c0c1d008064040c034818000c1c2e02d10032402082d030481c90521035504031900005440907 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 192959505 1250 192958255 192958267
    0x402131d130602070f02132403030f0513080607120b12030d24060804050706020c031c18060503090708060c030c0703020a150615030c12050703020d060902090a0b 71
    0x14510a907500e1000b440c203a400204401044040014544981d0f009444424400d103102c040c41d00400c00ba16030081c55007801007805a0a40a6074460000d5907450f0b07480181c0c071142008255025084041c4002c12030310300f0034000c50309900401c14140300c0e00d000ea86a0715199050b901c8d40c4200d03046150010f00450354400d80b00810a000030864181007601c0400042805c140741e00f125161280202945481190724000070389c1c103500503565800b40d03004070103079254581d590400780d0b81c8041c904001c0b901070700101c09a807410b140d488000444030b07840381802003a40e410b4810400350051242c2001000c250040140007103600d080141c00c0103040804014021401d0940c0c001000380002851442074510001700c00c400c05200303111440b0105e85c042580e11002d01d41d184c0d010701808041c09aa00c06003c1c1c00070b601c80f45032281c0036140391901e01d81c8681d612400c04960000180c04014440d4080c180c0800118008008900c5203074001c224031030b80113849030210070810040310055441240c2c80e10b401d020b9 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 192960755 1250 192959505 192959521
    0x102090109180603020301180201021e0703110103020f0c0a031d090406050402030c061204020f01030c050d0903020106120303060e06060a1e121e06051c0b0a02090402131d 75
    0x550142c0e0a4059249100e415825242d409408240c00081d055402c00050401104080074100141d0b4401d80903603401c1e16009001030810145201c3e000c0403507005420410100d6000b1422501c4200c0c18500076290a01001c0d102e0300c1540541c405001c980c0c80300c070042d4107050313000d000b12488604805048600110300000a003002d10b001d00043c00281d9100c010904644d02040007178803165010f0072294503203501e40000c071249242200c00303a0080c004c900c08014550310038412100a400c030f40e180c0b01d04200250740c800c801071184840840956594400128665640405409120b40310790340109a50741003544140e10010080c7c0705500406082c08600704142d000000c21401c450003456071400700183c12001c4600e0303074944010040741d034601894510700c0040719401143c1a08940c1d014800c072603607107040c4058040304140344000300361101c205a00080c046403d21b41c00034216180541003c00c030b1030009089a000203065004100405000c008a2041c2c40200701d00100746014004c07035142a5203 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 192962005 1250 192960755 192960767
    0x515040611010b0904050d1205010f0303110c450105100519090510170c07030c020918150106020a02041e060305010c0e041104050d02060409020c011d01020901 70
    0x1401050110555480514007400d40c4450001000107081d4052401e0504040f40c4500210940034002000c3c4030200c80115520301600b03040b205c65003c184000d0740345440442d41c0e4000601d05048a00035100d00301842e0f9504140003a0300602c8040200081c0c0403001070000c1074412540622070750703c2ca070354503030200d24203528101d04442e025140d103400c4103240c0c5002c031154421a0328620500700c1c601c0101d1625a8412141c00a0300c2055494018058240105541c10050700c20b0030794905101c1d1000401c001c0c5000c000d0801e051181c245288a8015540040c100c59400c5803030190140f9250b02e54281d07031200b0000351504010707842c60214907504000c0b00030b40303038403141c0c0c00030780101e40711141e00c07044405041f42c02d00303020380c0910200400c41e140d2030180e0182c0401800400042d4504806012350320740380c07080d100c2e4a88108401450301345880113010500c01005000d990000041c80f0001d25048140001e01c55a070760308000003481d00b11203030050700d420b0041901da85039a205108205c190b0341c00c08 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 192963255 1250 192962005 192962009
    0x60f0901230d120e0d1a04020a290f1b0c01032004030609080408060405010608010f060f0e0c0f030901022a0d0e04020c01060303020c030c01030506100f140a0810051504 74
    0x850312031420b404c44400b26500c1048030000034641c190b01c00d0641c060401071003025020314800c80d11901901da803070500c1e40020b8400140755069075040341c2003246c401c41440c024a01c0200300c4101a04103600714100c81c04003103605000708055000f81462031040c0da031521a070703080c031000f2110440441c01c0018422403280950f0000500d919603411780101032016580a0b28020140f0504a0383c0394038088c40d00c00d01a04ca20302c00c4505543c20a00480c101700b203640110019030b00d059049643e1145040d46440d00100054903903c08101c08120600c0104841c500a42c4a90301003800541c0d585001a1f000c400f0800c3c0340b000101c00014103600c0b14800d240400c100d0507810003450b00071151072001c00042c0003880b503854030102e29840c09a0000c04c06030003003105145441d040f42a1120708107414015802e89804980941c2d225402e1801c1c200f030b45008a1000c1441685864082c10116528804142c2c65000d603011b000851413560070003c02c0c503089200c01010b07110944038410040c03881405019a07000354 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 192964505 1250 192963255 192963257
    0x14040219120807060f2f16032109080309070501020613020f01170a060305010b1f050703020111070f06050a0e1b1203180a06030207030f0503060f0901230d12 69
    0x10301201440794640280e071903005100300801c040207010709800c09001080000d000ca0b066004242d102c44803240c82951071044440c0447d412424466404070340c4281034010744940301260712585003002099104400520b40b207040302940d20304103e0403881c03500744107900080c1154850010090300111101442c48015815200a201c0c0780b014401624142c80b4040041020307059141000000440ca4014508890080b802001103400c0c0340700344034100d40c0c644150000403030214007040c1041d02c900006e0011078041d01c0009155248098800700c0744d030140105a442c2010359404100740f01092081d15003100b003902c0d04014007010002201c2d107610108124002c024840011003040e034594401441608181d001aa0780c1c17420b4543d520f20300c540304c0e9131149004461409001c41c640b4064802c0302c00351601901c07090300c0c980b002d01c03044031250710003480560030514881107228691148186c1768081d141c030402c0c4c15008441c1e40c1c40c11803c0310740c40c41e02c0f610030070007136090f000031032110303001c0356019012 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 192965755 1250 192964505 192964507
    0x150c0903021e03010c02032203020303070209040c0e07020d1103090a030813051203030a061203050708090114070309050310230705130e1603110d0b1201140402191208 73
    0x480d0320b42030344100490541d015400c0240c04d00d103050380030000b06000725010003104010784d1249820240754901e804025015801040124090324010403842c1d0700911071048a03c1003510707a007910b14050820745e48480968004003009241641000e04501c0c10030111009600381040c50001402482c081d210140084400040d00360090801110354400b810000d0321240c4c4030f44000380b40c0c543e240c0c0100c4540d0b04d258944940807840d1022180384915032601a80c40074240744035a111075007907034841542c113414403441215402d0301c45c202402400b01d85010b42c5503080198a03080a0500703108001c00c8045120f0700d0928200e482c00504c8032804101d01003050544050b0b9610502591203100c0c01d0382507440b401842c000050950460201c141c071451079409030181c00035201800b5000da13140786003898404181400020401d90090340a0f020b441030090404a007441c1c110310080c00c58001090160b03680d141c035400c10081d4107082cbc480000d002e4007014441d01c1146001e00311030b0724010800d4010008c8130 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 192967005 1250 192965755 192965779
    0x5160501021c120b030106051507060c08061003020d090b01060f020f0d090e1302060708030106030605061201060c02180702031b03040f0b0f0418141302150f07060501080307150c090302 81
    0x45c00d503c01c10141c03e0180280c102041ca1000401840e001944201c902604012004200e14401e60145019a1019000b0f030700301c211480040d8060b41107041c000e243c441c0d50307209a40c00b15481e084510300a14544d154400004001c9034000c1c244540301c802100079500041c03c0f150001c2e840808101200e41c1201c0c0840651998000e90014020008001e9400080401c102c403e10000d54003c60407142c25880801c03016070340304240a900c1c0205210494812078820040260074091114901d00600c001c2c40102a1131042c40b003102611020340320280140d0000c148050803c010001400c1d8441c4024002c2d0700302031402d5035000000301140070f2440a801c002c90f451507828150400d540c09460030b110410083d140d0140070400034000700001698503c0d6580c0031401c0d1001c070f06001080c040c1c018142c03102c906407103280f1205a0384249140c551012081000401182c41403044c20b000e04840320185585402504101c4030014030000c400b400c4a203418010280c558112500104407039055076490700f428 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 192968255 1250 192967005 192967009
    0x32907230409050405010213060306120609150c0f0e0609030304090e030409021603200604060209030f030408070614190c0206040305151b070b0f0c040305160501021c120b 75
    0x1c00740398000014581081c05102c10014103402508c1e10b440001041c01089a0b14142201580c03c1442000c24440c0481c00c001c0100d802c0da000307038602c02d02802d03500003c3d01c0d0a954680444500c2100400002c44041071004003e5100012180c00407048500302d040601d00740009881c0c3c8168440c28090726903403214000151400d00940e0014480d0560454071003140500700640341443c1d03901100003407a45403094001e00c1e0900201c0004d0f048000041c08144e45642d162030007540805191903161040040c0c142010710104002d20103008218081c044107031800002030880b00300000640741d007030000e100480d602624000340c000c008800c0c2c9001d030840c0d14240080781c0c640c4200e41010f4603600514000e080b03034001820310503000c2d00103d0888240030504140c249480c4c041c808005101c4402400821032100c0c40f041840d801400d6401c10038581a40c030364809181c03d0702d41742d030f40d4880705180f04100210f6805101240702c1e8503400d04200d0020040700b030010101d41e0304231900d4050030760700d0110015903 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 192969505 1250 192968255 192968257
    0x305120c0109080712020d111005040606050406080c03060106030903080708100b030109020c280f02040b090108150903040f0509070c0602030711100c090b0d0f0603290723 75
    0x1107030002e0481d5030381c1c2d04074282105d00a42c2c00d400311300944109400c41195911a000c3c0c20100309120700034000c060581800c2c24054180a4030603103050383c4845000c111a42c80d48182d9000340304038002400c070b11101005041c1082016070100007414640003841c0c01180e0000c001d03035804080381c64181e52a03030328500322881d91061500b054000000110010032242e425500811500d01038500716402c02240c500c2920300350742004102050950003c0e50b100004100c61514044a440200003194014401c03011a0f0804400d0b4001c507259400030700701400b21a03190401e150402c0c80240650b2406d401d00c00842c0000303005118140c05602c0034030010305068428000c1100f01507100302c055540b801c000340300074800b4501c1c08606102d4040c40392030b101509034902c40d0316a0f1340d0b102d840f070400c014541559070074075800a00726101601e40f1042501c0d405c400ca4030641d0081d40c800d800c0c2c030500682c650b0380b5100c4a001030840c46009072030300d824800401d80021403040d40da940700c5600100309600030509a81 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 192970755 1250 192969505 192969521
    0x1209031704080f0f0301030308150a0611010b060c0303070f1701050d060b030d08100b180409050708010c08010e090a03082202120304030204051623070210030605040b010201060305120c01 82
    0x14105010031558030328440d004c02181201c3c080d40c1c8040041e10303241900200151903a5820764801c1c0d480100700081409442c0c0428031500c2500006842c8420305c011a080d42d102285541c140c0d00000108a0301ca908180b0285440460340b43c41402400180d0743c3c091a07a4040c00f03424031480cd610302000c10041c1c203800c0101c82140c080d050302c020042002016101100170394800a244012200105019441c502580e00264044101201030136654050000030a40500300ba2164060100003003541c08007400389051f4403a96940e0305035690300d404400d0203610343c041c0a80316a0340044000c6070120f903110460580043c40c025101c00700710100401801050341c1814029003002201400444c0d81c000400500100c03402920300b03022a5442640701d136007500590882d080400c1502d0340c220750201d12280380c0c10080c080c09c11001d1814046400251401e1111412140040e0f01c56501b0302082c00c06020340e20359042c01780001e2101d10b085540300e980b0f03030030110303140c0d21951004540f04045003000d40021030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 192972005 1250 192970755 192970777
    0x906090615050a0603140a0908040308130906050f060304061a030d02030417010e0a120203040905161706060d02090f1020060f070c03020f070603060501120903170408 73
    0x100000d07105014841518510400340f10301c000000c00201207001c4d0040c0500750741600401c003041c0e6203c0c92110001c0000001c140c50341c2005000c08000108114000d01c42300c0300c0e00c0c8004520600d444c0e0300b0303000d690445d00104d0040c0c1c402000b03039003561104000d694105501050220b6800d24180420910325000c0e0540b5034140300c3c1c3e020034142c50b034000c002082556039282594041c1c908903a11942070303400800d5810f07415030049010314003065041400c04110b040300c4c810740f494141c0c0c61403400b0035201c0903580004104103c0d0f064403070998004810031491007020440c01900d19140000642ca4041da901d103610807a00021034418603502d20b504048120130091002a01c200c400c0001861101740c0c45a0502c02500400018940da0002813054032845e5640b403581d03026034800400711000d4117001d070700301d05504c11141a4401c80138103000000103850a540e0000f5554030b000001002d1024596400118600d00044180030a600480b01845074100c20380b8915180c03514030b00740405110f5228024 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 192973255 1250 192972005 192972011
    0xb0f06190f08060604060b0703230703110c03010e1e030904020c0105040c090902031b120a03260f01030206160c060c110303091f090803030c0c070e160309060906 71
    0x305011401c841d2030420342d000002110b01c99942c40c401d200490f0344a026911200c08284507000000744100d0b0000c0784010038052000035032807040c500c0c20386a00f007144110301044000182d41c443d4001008441c00fa400210f000703010210180c5205922a01c50f02c42c400040001510103c8001c141082141e00c640d00103401155694229100d55009200c01d8030300b2141030074040000650f0200d20b000c5d14005c01d40050180007080c449a600c035200101500301150454881604280ea10400b40166801075000b600c0d14506401c4130382401d089a80f03040d0700c000384c6608410078001111003141505041d2039040e564a543c912010300c0c1d000462181c40001003041103805408180d05501031000c0304014400d620070300d101214002016164000e10740c115421401150800903a001c90504401d014078641c01c001183d030703031205a000c1c01c50b4000c41781e0481c40c00700051080304090041106c8001041c000c08415a6070828030800815071410b80705010030991aa1928424008a80d11011207991322403010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 192974505 1250 192973255 192973259
    0xc0c060b0307080f060708060105070b0105010806010e10030c02010f2a02120c0304081b010e040b0411040902090f030703020108010e0403050f0705010b1503190504050c09250203070b0f0619 83
    0xc5662080111014400622007078007223815940140180c0d000c040d07000c07420f03c200c1d03800e20004441c4041b0080c1a03e041203d4000150105e4075211a65241c40f106607601080a030000c2e41c029080d0350080d40742d500390a00e412132068545a15030f030045c90f00054095601c902e845844412458007860414400131420000750351588144000010f0044904d1030b42035400711141e441510f03145911181e0140e01040e40100e1410b010b01c0d251307115010004c0001c000040743c010814040322030b80c000350007034038203940d00080c100c90601d8100031003202c0c01c0041f4024100b460541e400200300074010312071341c0d07841e0950401040806000308240c03440400c0c00481c403030300d45107141401c1d4041c0042000d054081c0d0f0100407066210107102d000c49101c0c0b46850300040c414030001c14554003e10b4001e0003601c003070050142a0807503980da6034540b40a8141483c03084218020040c003821840c11103201c00040d944100087d20000303480c842502e5020f0b480d40451692f40da58070300403444018401241d01c1e100c2613002c00c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 192975755 1250 192974505 192974533
    0x207060207050706110c15030a0504030c120909050f04121209020d08030105040507020c01050a0e0f06040f03140118060e0f0f0d02010f11040308030c040b0c0a03120c0c060b030708 79
    0x204c840022002c2c021240c41e40407040500000c07111074890b0b007c80250400014074001314940025801c02d20914007409803c00130340340e000f00115888204800680326806c01c0002254600030300b1f400002c40503280768030f07091075501d4a925807218101c06040c0003104c510762040340c0c2640d0110a001ea000b4000e500380001d5440d00c2040c5034424000c06e44540d2405011a1010344001807006080006850745441c0001425003500d11090262039154072200a00d2501c1c219210382001d00010500c1e14140b051840c25403414012150035448480a16131401003070301491141e0280009000c0c1e0000300008010900d840c249041c40c040d26140640c030b03c5429591800d521000521041e180116030003004026a18040841540c83c1a0356125002e2000c0c801030011554000003550084a031a5849142c69514802d0b0541a0401c0e1203070380e10f5030410014401819040115521f8071144100100a089030150b0b000d409603085241c0035200b10398418004030f160f181000b03004007401c40582110200c280b0010 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 192977005 1250 192975755 192975767
    0x1207030305040309150e011416030e0d17090a080d0c0209101221091a0d18060204080111090904110301060b071401060e06010c0308091c050c07060810090207060207050706 75
    0x24070540002c14034802503207821412030032740e52010b540c1c1c024603e5502035910125008004405c0080d4081000681e2000288440c20000315010b01407028a856031a030600304a00b441c0503500c9105550081c454030304159521800c0d0f001c50b194101e544070120f4540c0c0d0076003192010682c001c0b0022215031050340701845911540a00340300c41380c018110900f071990b0401c450781c042e903201786141d06600b401140c000c2221040504034180c0c19410000d8640c100300d0700030307001904603001a20007541c0060107000c0c2400030b00074001440c0300b0107a1715140401141c0030131803081c0014000f8041d403d034002c01d181140e5080d04448010311072a0051138440a01d401c1c454611a480d101618044d840c0c5140003600d01540c03c01284034680503140d0302c0310310f041c9450580d6800d6005218400c40c1c018003000e07060300c40003007120074040070b8540d54003515205206c0c40303907140014030f810003c2809100000c001140d070010391007000303540b290400075841e415140303000c10180c01155402407a600800700c001c03909a41c462 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 192978255 1250 192977005 192977027
    0x504050a02040501050619030b1933080a0207050f0318030c09040302031b0f0d0504140109080709020d23091506100f0c061a12120703030504030915 65
    0x15030420150740d0740c0040000c24840c81f541d0002c0c210307400b07900d01701b0103002e80d0141031500d1014000c20201c040f102030038403c00c1c01c5a00720010a0b41440d43d420040c4542103800703a14030b41c0c903c084c0406452128000303050b02c00018000403100e5000940f0104014061140040e2510400c08481d1641c2e80c0f0000c29130b40036004d0807850702130f01c111648030002d4a400c1840500907501500698641032410000c12041c032003a1100151503c144280c85446110820409001c071040c1d98a09840303a0070016011400100039900394108200e1070401e10003d00046400403c807401c4c2d8100607a40c403003007500c22000c0c1c610310440c80c241d4200c1b4855001642903107111103100d160f0300000e07071b451520b4000d280340c0c51030f4043c0c0d80c4581000715452440d1082d4001c03c082c044002c500c0c100f001c590107840d5154002d03110198091400c02c0c441d18040c2c0c2080c10098800460140703414040e1442031100300c1c0588141c02004006002c168076140440c042c0f41c0a440d281c4003401c10b020b91615030715010385000d0060302c816 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 192979505 1250 192978255 192978259
    0xd050c010b04021206092503020d0f2c1011070506060d031202090f1c020901051203030c1b030c0a0b0a0b060a11010e01020d05010503070605070803010e0907090504050a02 75
    0x1181001c2460148200c9000c4a608961165a916010b0501c02200e1005208189203205a03407106441c0b03044440011030000b10b40d901503511503445800100381d83c010044212540d040800c0b130b07140401d10040d40305000007051100d4619080340215245802e401e0000c1c120150314001241d00b451141c0300c010200e00d8003440c2250150f40b91181401511190100040d000541010a4000c8507455130000c240408004184011407950000024000751038030700c8045094861114400450501d400ea03940100412281c0b00204422159041d8803803100901d4169240d4001a221001110301c2c1da00c05080c0d00c5001c03c40c0d4a4014009034250341da0301e100800d6600391800000a0b007145031500525461103400381003142000c2c1000026103000440040445580d5200e40b08505604002d2010340001c0d0130920011074254504030506081807a9070300514104041001000045074500e0110f034110703020b840c65148950345500c145400c2c9806904203401c41030030242800203200001030703043c21650007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 192980755 1250 192979505 192979511
    0x90614220c0c05160b04060f0c02040f1406060301120b040501200309010501050a030804050105030727060e0f06220b1809060a06091203090e0103080307080901090b01050d0201110d050c01 82
    0x4c01000c0c50480d801c140304030002d9031020001440b4030751041c0e0026404046500701524103030b2441c1e00181c00d6400e264031811a03d07654142002a4082c2d0b0703d101c903004a000c0c0d4044e4503550420291025503200780c1006001c074410070001c00d0811100350311803420311410240000003847c0011b88214030364002e40b5420015800c0000104503403078030141190440741d01011140ca01441d01c4015181a08020100002c2c001032144c4640c01441c1d0740c520550810048403403505541c1403210151034045008215405901f001b070040040751030340c004903403440003041960b4190003100c0b406030700c2540180d005040c603404c0200300c3c01a5136080039034000c8006401c4a1002c080d0780d0f141c0911941e0000c80c45a21300084c16440200200d083c90b4100c00300590003032405540c0541c650000f1100860281c1c0304941c100701c00810029180d0340010540c1d00491448002d01266030030761511070500b8018090715204040c070340c0504045a014400c41210b82c040007065502c112201407000d44503802c080c112003a2542 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 192982005 1250 192980755 192980773
    0x311060906100504051905150301060b031012080708070312060501020a2303090a030b0109110705070303032c06040507081f020304050c0604030b010609090614220c0c05 74
    0x3401040d040d10400081d04022190752030b100801c0041c0402404615070301c2c00d2000345c04485402400340d40d201d0300b054011681243c1c014010b143c00c507402c82e0b206190880c1c2c1031082c031a00c81d445003181d03811116003280c0044040c42a04142d0014032404d5030040011000055000401d074101e004900d044110342c1007000300c10340e00d1005a1303c0350607901c4001d05200c00020000000b2450b41010040507203040308884c10040b007240030400c051925041030f40c5007601d41d001048010198090340d00b10314800d0b40111b0400d14075030340b156070760421800010141074841181c84503600c261000400c001c100550509000c030b150300c13401c54540d0400d55041d143c50092010100d0035500001c0c44003044102001071101941140d10a0350003900040c0c000c40e5240203c8044005643d100f10191010714015080b031512035140c588098030780c441540c172511150f07041c807070704008010600c5044252100b00351050070051185001d62040b050440444540184c83c0900541000d648004504c40c814499000c45850741 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 192983255 1250 192982005 192982021
    0x6010b03040308070807021204061701080304290f0d0209041a0105090d0809060703020f010c020d0503190608030d0b092406130305010507030c170114010c05030408010207031106 78
    0xc0300889000d408105040c000ca000d092107818842c0d031005d4584152000c42d8010300c0901c040c2d9101c1d5101d03130000356401413103e01c01c0e2031054805004100100003146020300d0b02140c09000400400081d544091404082c610504003d00b102e411181c9148441d9950000c3c08001c0000d4101c40b81d0140102c0c0780c4001100d00310340e00006001d00200586580707083c8030000e002c0051110985808803902c0c0000c0c0141c1500ea207802014000c450f04c60b4014040070911701107054210b40d40c803030800c0119841072072102e0801c2d4005c400c4a07040300140000110086207004d031040680030300c0d40484c00604c0000b40e00030200143c1d0740302805018003200ca09134580c484020030704804240000c40075440072445420071007440c020004040340038a20808070325469403a00e9040c2110303022078540010a03219940d035000f059205059000c541e00d880c1108084d541815100c40741421602801b42c18016a8015a4240701f01041910000c1401600955403045c840c94005d0208400c2c0011107118884d81c804101c5c21 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 192984505 1250 192983255 192983257
    0x140901030305091201020d090302010501080d2d02031306020105070e040b030768010605030c0409020c07140307030b0c09120114090d0e01080a0914030a09050306010b 73
    0x200d0301030351403d062812034000c2042c41400c0216045032990308010040d02d40440380180150303140280c00004140d03243c0305569003096104042c02007000180e09108040a800844860a02e02442088108004e000400764658031030342218204050707941c00000303612031b415000903210b6947c40e550748030380701d07010b40602c016503003203040031035240c0c02c4600180803440d60241c0d100e43d0b201030005010a03036180400a01c03210003030105200035040d801004000302e51268814104100941c400399031210451224074109010180101010050000007007406a088001680d0141aa42d80c2c00c560f140c0c802030080381d40d400ca41c42580d41034010030788a2580c504d00803628070100ca0308a81e5200b40c3c1da86134000c0d121213500206405503c43e55221421050500912616440103000d00841d403403800d0030b85241d450005003000140810232114140c005d40d90344a001d0b079400a407513110100790240327107181c0319120340004544a5210311020889054485d800940c1c441101c200b03400780c891a036210960f40d00701e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 192985611 1106 192984505 192984509
    0xa06111c0203040210050903030304062a03020d06050301020913050c070b070c0203010e0d020c150f0f0a03143d081b0901050a03201009140901 63
    0x850916810440b8244158100b5a00700440100020703270f0380c800203000409981e10b40c481c61412218001c0a9041c1c40d0b110001c00a110108540090003500a0f0b1003510f080780c00c0440000306410184200c030710b2039401500f82801d080c000000380c40a071202602d80d18411320104400307008111a02e900300e014010380d50340c4a01100079030040500b542c0070f102181309240c01821000249035000990075003403003406d0341c108860808171409081c0d41d003d83e45001d16006000100c403607900f0340c4000101241e282c2e43e1400c00507645010445a031200e8111101c6030201003581c1103c1e20550880640d402540000003480b0300310111450503c00d0105542c020511a80200c00007203604540042e8842c0c9200b043d502c20380d0561500c000101c0070751341c6200c0a48100c560640d041a86e8483e00188000e00c0000790a10b2620311404a0042c40641c0510503903401b00140b040b002c09601e0481d40c9e60f81 = true := by decide +kernel

theorem cover : BRFrame.Cov 192805755 192985611 := by
  have h0 := BRFrame.cov_init 192805755
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192805755 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 192805755 ≤ n) (h2 : n < 192985611) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
