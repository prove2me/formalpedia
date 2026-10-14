-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1969
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:20:31.969158+00:00
-- url     : https://prove2.me/submissions/86030fe0-5aee-4588-b4cc-e4cfd718663a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 353956834 ≤ n < 354136690 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 353958084 1250 353956834 353956879
    0x7030c0807060e1b01030c080f06040903030e25050405010614030901060b0318060f01060c08030907030206040e04060501051903420b030a05060402100504091e0b 71
    0x91410800007050424040c0700c0c0c02c07a58800003007100381c82940c0e074000890b4801a00b030340c5016000c00d00f052054a116802949003611076408141919190703a42e00d0200700042000480440030b1540e98200552804020006501c0e4402d1201c0705c0180881c00d0b080e550f105000e140d2005200742d04180044c40100ea000320003184031543d81c901140c50345c075045503450140c056600401480000801001800362a2000d0303c640c5410754010f035101500c90082640b0f150b1024040c0802050700191902c000849207002160311141d000150342c0b0b89502d0740c3c0090303099070040d0f00c503070800c2d140d9100344010301903148103080c010f1034200c44c0c6040c5075a01c0c0840d41c42c5000e162101916040a880e65003c1b600103484032101c60b6540c54465500303011100c0c0080c0000c8400b40c402214951a0100070312190800141c44040150007100070849a1b40c2c59007004482002c52a0110806c2801e02002490b0704a5000e0303080c0001e001c0107119030200e901e586000441e9420175405200d0003030400410f401101c40301 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 353959334 1250 353958084 353958107
    0x1e07050f040902010f080a060b0d0c080f070e1002030c0a060b03060703091e050c090f0718030803220c0f03120c0b2e0906030b07080f0a09140a0501140c0703 69
    0xf48866150340f510310361f100904690b0f02c607200c0114000781c550480d50790707580a003010b0f49894643c007006072103060590b00005e1044a005000c2507401d28a107a0074600301c200391094005510440c0d02d400507981c0e11904050f6016030444000f0340314130020100386024408240d000d134180ca0104004a5103480c0c8122641c0a6500c5a40404440e103c0f602402030a1004a0382d02034003400138a00c0381820080f41d6108003003103c601000501201e403240c0c0d075820700e040d4102100c1d0020301d803d0564a07080c4d100842c4082025459508442502d420400600f11304c107014010314905184040c9180385060010031080209100c0e01000003140d0ba100000f4040000207800c96507450510078034017815141000180307030181080c1707043d901210001600b410160440360503039200d0101c889540e02c1c0c1d0f001c2a15030310001c0e40d01d20700c2c4075400c02c0020800c1e04580e21110810303000d190100c6500c0c21214100b41052004201501c90380d444a004d55900001c04071407036000469184401d1402615803401000600134a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 353960584 1250 353959334 353959337
    0x90606021b10030b03190204110708070b060315010f1401030c050d0c1404080714040c091502030d020721020d050403031809020c030d050606070308070c051e07050f040902010f 77
    0xc0203500380c0701e40b0a5009804084c0d0103021120600c1c1c0c603030344019034540d8085040784114102005208180c001c00c00391403000f82d010b000c036828000c4645d02c501802000606082e0540708107640b0001050150403c2402000302030303580d0310b056003005400c10760042c40d104986e040c50708081d00a424942d0000864070f0314807020302c0000d407140312803404541c0f00c051000c01e03400007100031034089042c0c1d00c04600082100d00408040e21440200000d100c180c6003020300880211307101c2c550811000071800c40002440300c0c40c2c819203241c01a40981c0c1d40c200e82003141e05440c20790740f46100c1d07141c0600c00d000c4640422094001020b400c0d0600c00024168421400000d04129403540000d11120360200314074003501c105001952100b100b0030119580c2c0d04482010303041d01c0d04040108001d41028012241001d1b01039807507070b01a980d0030005841c5072035070141c1183c0c3d5114003291008400c40545031040d07009084005803100915180400405143c0440e450b441180340881000c0103070b810036240c0452172400e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 353961834 1250 353960584 353960599
    0x7020111010b0a08031b01050f0606070606030b1302010305090609070b0f04080703030810120c0918020a03050c030f010509100e0a06060e010905011e03060b131104090606021b 77
    0x46008150240000c0c04410b500906216004251038134040040c105203600d071152a034080000c201c0d020300b0b8401c00d8032498204481d0300045005820042c000b4401940a1440803a07103903038a40d200451058103c455401d448040c0380143c08643e414007805412070340d21401402c00f130405200d100d03218003061151081c4540d00045c1014018811801c0e1002441d0210a8507182607403400c0240aa0400b1101c1450000183c040450070103001c6603142030080d00101400029030824401600901c00060140a41581605a40300603612055050055031040c40509105070345402414948003251030420320b1070341400100980301c0f4000441c401321031100880810110078082d078003420888102d501803c0070b402d20300d002c40c0d641410030010703040b00d1101501b085940e99840381135018826600041c510120001310800c0400c1e0540c101100440006203100c10035008032010104884164902c0e100200380410204906050740c4030b03440003013025002070020034050618000085202149072846040e8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 353963084 1250 353961834 353961857
    0x60402090117010e1b18091005040f0b0a12030c02100e030a0602030708060a08101104120f050105071106011a070605070503060f0109080a0311010b220609060b070201 73
    0x1c142e4802c010100e5030a841121961229200186054201c03409031140310400100b03408030450208039501e0f0540c49582030501c00b0340300c0c1008042c1c14017905100031441c00b03160200d11130360740c1d100300b280b4541d0001000401d0504a001e000c0884107551001c00c44030001c0500300007180d042240b00d80101d90485400000841804080d50300030341e4403180e141c0512846202c2401c0095aa0065004c4c083c1c5031203042081d40c030002000341200050080e02c540d43c1240201002c515000c0c2c01121516204a2186041c20348442c1010815150319006450b000c91204000013400000c1c4110b80e048052481c100219510302e0400c0382d0344030418443c00107854106c0001d083c010400e00c040d81e4280b6404481402301e03041001c0010107030b80065402602c54800303041800351540c01501e005040340c03000e0020340192550b9490035143c148212140c80c00d039548500704882150340b03c151041c03003119291560100d0301600d250701c500300c8a542d0081e0300014588032003441310ba0020f5045c1c80401d0750903c1e004e2001c54 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 353964334 1250 353963084 353963087
    0x9101406012f0d050301060206090a2102010e010f1e05010e0105010f0e0d060603030e0102010c09091104170109170a02030f07030215010303120c23070c0b0f040e090606090604020901 80
    0x2012207198a00350088840760030350f581d03106004504846003a803c03500c049c1c641c2c140150712480d00140c0109400c8011140d1340d03141c040b440c0e00c1001041c1c01c3c000041e0220b4081445400e54080f680400003050b5035042c171440c480950807076440700c00601030701004030390f0510088804035081801464140810191445403852103050b59200ca00070141c983d180b070145500d0304a01030801e501044020941c0c03005c101d40517510520072004418140d03030b50086410702e00300c07005008106a0201883c034032010030000c6044980014401161845800006071149541c01c05008440080c40c00c48406201000052511503000081d1071920300c600030702550f0b41d03e003032506a15044203c61041d0b01a083c070b000020504ad004107581d4ac4110b0506800d01c0580d02640040751403040e030706040c03010039545e02c2c2c0d01f107078658098014005091040c661071181d16202c8800c01003a803c100d030300d00c5091500050921800d8203000c03905030000e016000801503030500c10005030046500030001c4e40074542c049150185603 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 353965584 1250 353964334 353964407
    0x8100504020a090608010f050705270112020f191d0f0a12050a060c02071a0304170f0a09050907020303060d0503090a03030509040b0102060105010c12170910140601 72
    0x1030100c000200012680d40405074085e207207401e401c20000317103008e001400e001c0c012070132154095248080c3d0f081c0c080145c604500429a01c030300342d5040000c081c09006100b0030303900c0180310a00756028081c2d03d0f014010780c840c1075040409030550410548110010103400000b000204003041200e03620300355401c640204644410940c1700b00c44552040d6840350601c900030581c21200c5000310303004d000c8800810426a5210f04da8803501401501751319204a808040c40d02840d0410f109019160a0300e8010311055070a030081420b0003212000040e11035917090304003410900901061750000714610389428043d441780370041902e80942c600c01710000401034140111501c2e41401003c01710310719200e0030024100c0e08a03040310b9008604e01031003c10990300020307815040ba20141d503612000c80041c0c1c0c50503000c00364400580b040c0300d450f41c00741580241c058003c512a5038224000c00d200107941c0801c50941e960440148207845042c802e2140c2c3e640d005820318000031840c1c403240860300c084007140380d00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 353966834 1250 353965584 353965589
    0xc13090f0f11030703060e1009110c0105070906020f0604030e0f12101a150406140c060124030510170307020a0f080f030c0606040b0301151e060908100504020a 70
    0x442c903194180000d040c0310009540a44900d40c1e04004098464250410909082d280c1b0b440c80c500301c840030030820b04170b40c218031556288030030401d08100d0301158550943e030f401c0e00c0410105400f01000d005030781d030400008094500300350080940e41810f07140541401c41264441d80144003005400d8113685510640401540340e5404a40f03071036103141c685400420b03071500641424041080c07000d185207454a180e0f004842a60044e514007450003000f070710343c007402d1000114400018031400c01340e00c20a02025000348150788840300b60b081001c02c550044100025880141450b210901c401e000700c1030020020348a201118500000c849112035103075004140c0000d40c4412071081c003042c0e001c0b007180803104480007202180c40c03030200c0e80ea03110388900170286003440ca94042d00c0003403468034150300000c0c42c10002400004200e403022140d0788501b40e80d0303040002c0080104451b0404612044140350040107c0c0c40c1c2501040c0c100311203291504a500484c0e2481515480403c00750764404045200 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 353968084 1250 353966834 353966861
    0x15090c0d0b13020d1209060914040b011701090603060c0305040b01030b060612090c0a17030d1e1a030705121c0513080f060c0715050702030c010908030f0c13090f 71
    0x608103071303e10b0845440f81d40c200034400091120140010343d180150401801d85042c1d0404d0000c0a10400071300005060003910f96040010182181c0e0641c4044c2d0401030103002d03004408541607095082c80000d0341d00d0048420300305450401040046150340c4682419030380d10084c00059500c5000c0012028007940000400580c50203061280c03503080054440001c840603101d20000c9a641c036000d0000b0a480c10b107101d02608104119500100d0a034464a04400742e400071800e00d032403d5050b08102e840c046103500942000000000030b900c1c0811400f0300030a411200101509980b1461680790641e14202200c40300203404000c000500545c103507001d00c2802603503888132a036030b031600540d05e041c00c02c008501030013800301240e1481c034a041120311590304489000c00780c000d1041107400a060080110045000c14400c03001c00080238040c10001c140541442c139100d0800ea68181001c0c2c001600480d1008410080d03186407050b06402d8008580708a40001440e414203500203024000070180e074607 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 353969334 1250 353968084 353968099
    0x40c1a030402101806020106030c080604050d03020901170406050a1508030906030606161505090303070c0f210c02040b060a141e030a050103060b090105211002040815090c0d0b1302 79
    0x5e4225030547c80142181d0089c3c11454056a8071203203107885110a881c013804e0380e004102400410340c029001001503c806240031049500c88640868808009a40c119400e0b5110014041902c80f64058101c120303180c840c2c222503043c03500d0303051548e074407989a07814007843d804000503200340d40d540103031a44914214040d449900b12490020008050402035100c3e00b86802c0c00320303c550304000252403080c20706c1c2c0c407182c000c0003007612280042000000d04545071201c444002e030442000c044050b10002007070f140c044685803e4410081503d20b0301c010b40d40280d0062203c500b45030740c0910414007a03080a003409949031400e10781d602c0003104200900844040000a012030300c0c402e54003182c12a80105000c01074280514108140e6000a1007940c0c1d01c9a4954040300a190010030305520b140207817400c65190750031104401c030590f000b6a000040b036400002e48119240f0315002101c2d0f0140c400000ba00c0880120b02c005100450300c13000141c0310740c50351800181c83c80c20003560381e03100751340051105 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 353970584 1250 353969334 353969339
    0xf141c0b040c05070b09061012081c06230901061103070b091e1902010327060b0103060605160f0f060e010504060e0a030507200612040c1a0304021018 66
    0x143c2660301010003241c02d40402d00024074076020105040d4060129075054210361840e251001041210030041a24244d000b0803100c00d10041d120b9040c10740107200080400e1151034481c0511104441b5107284080d08240b240da5034081c0d41c2c08160328150f660b24180b141d00c0b80c031681403451942c0a10034000344210303488400d22a0b4444d00003850300010f03605100e110880c8a02d0200d4030b031a07e0170138018902604028801302c0040d03000742c01950102209410100720500c2c030181c210b103860b0b030006c1e0580391030f0b544444001040d64140151005807225003070944c81c1c0131030200790381c0c000301c06000d006c1c1c00c0c2040300000700200076180c03090b00d1b919504400244654001490114028001074404840581ca0000319000222000c16490903070f47d003507207420f424414039448507460f400b2040f40c8407515243d0301704c00210aa90341805040d801000100920762232800e81340034200d00301103412500e44c11802203000980410080b0403a544181c0c10b807010340ca9a021740310305031a814003181108102c40c050000c003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 353971834 1250 353970584 353970587
    0x80c0a0512040f06180b070c02031006032f030303070518060f030a0b0f18041a040b090601061805120109081902060606130e04050a020a150f141c0b040c 67
    0x141c500342070140c0402c03c0742c1e40301405d03501c40030f50354000001c060395001c4000400e424094007240049600140984013081e8500d22140b0132688550800c03144002941c110740140d100340c5062170b990f00003201000d444d10b55000c00080c0e42e03010081c1039404000001a030543d440101100341c881c0020040d054544a01c403078012401d41e600708403072061500b403410a5039403143c03400c140d080c00f8006010b80194410404986a1246001c0040064600504540305002009115252548502d01405403441d0a003481001e0340d09040041c0d01c40c03c104a145280c46105000340000d000480300d08072080396501466810160140030380c3c403005001d41201240b0b80b00303640c0101d120800072441c84e6082e02c0040c5e4a410811500340605121080c8000003250140032407a84044200d401074000d40c225000c09925900042d46414a03030000c0040a41140091500a41007004440c142c201c40c02c040e00280555018071f00780f8011085e400c0e684112150100e01c050750281e00071490001c01401c148101d000c0e2420 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 353973084 1250 353971834 353971853
    0xa0b0d1b0908011a010f03020903120403080324010504180e010f0b0f062104030207080f0723031c180e0603060601051c0b121006081c080c0a051204 65
    0x24242455081a0001d0310b41c2c4d24a03058901a28416181c860320003c240c881100290402c0c180e940c7c0520420040181800d004009031005501c11100d0382e5803440c0046010071048030740010003a0008010150003281c0e03070040250340c00d6441c030700540403091f241d0440c0c005c003034200450b5100f820b500c1e002000c500a8a982c00000c4120340546150556000406c20301810b4415041101d140300000600d50f50462549418a03411900a104607084261142c416a0524006900304203035540040c500b040020a0f50700103a1403104010180d104a84652021903100c01074051440d0000f410302c1c180b5408240100c3c40c1803455200d00c050650a5502c0d000100410740c8281c600394800e1050000080703040d88103104494101e00d403e414100c0b420294086580030304200901741c0d44c4800000d850f092100000c020017560b44001c4070011403554a8075554030f08200090300d00310003850309000f80c1c44000da0020009504400350314030721507440e84d8040045955000310f00004012041c50024071090010010 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 353974334 1250 353973084 353973089
    0x30c070206070b091c141804020717091008040510090c0f0308070c051f031a06160b090c060a080903070602041d010902070309050d0c0306050702150609060a0b0d1b09 73
    0x104071907032150302c00300180e502c4106c114142141000c1085121200007000e50110440c120141016007070401541d100440c00b400d94110458103003001c1603080d1170b49401c2260410b0380e03955007005401424281c42d11a00c402160803c0490240c03a4001d803020420140400002080006220700003152070703180046040e8130107413094a02e004071034000f1400b4501102c104c04a1054100a1000e102d4898030035409040c1001203003110710a158092807240d15a00e000340303040100c003425000785080d50728006103038440281c28071029510050600505072208000c443c0011002d0520015503544c8800c0315285100e0001c008103400d0002c41c1c0043c24444403405610304403a6142c060b27121341e0703c17800c00404901030310b00d01030002a8070341c00c00c010398242101840c070340c14040c0d00180c036503948175143c8034183d640661302000142d20401c0340848808070012103a0b000030703080380d984406081100014201c008540501702c441100090415001c48190703000300c080c00c100000c00d484c82c18107003002601a480c1032 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 353975584 1250 353974334 353974363
    0x60f09020109080106151d030307120f0206040b0613060302120c0a120302031801111f06060509030706080c0d091a010506031918050a05031305100203030c070206070b09 74
    0x100300204820300117000b0703681071300c5804441041841b184401202c158416030f065500006a10810302c040c0d8905000a00c149802500690124404908010310354001400391078119002201440000391000080d00c0d0044011608070b0032012007c4015801003807285c0c4000c8d8001c140380745c00c210b0403201050b80864040c00315400b030703051a17980d00d054000d89a0800e004006810812004005440d02c00300100000c1040c0b5080380301004034100d140c506a60003001404070403110008158030081070040d0380241c412842c02e18100b241c1400802e40e550094000d207410f0121940c0024041000882592204100100c0c107014107c454103216000f018200400c0b64844410000850b090030703d10212401000301d40175171003007800701045840007001030364854110840b03200c0089010400401c56504034a002c1c41c055541c0f818140250700c0c10124990143e4041d003818918030507203c0c0c001c015aa84641c06ea00301550741c2c00d143c070000f00345202740b44009200890701d4090042443c80016508080301c0c40 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 353976834 1250 353975584 353975597
    0x30c07030c080c0901080a0206130e09060a1a0102120922090c050411120603030c0304031a0604091a04080d020703050327070605070c0b04120606050405070507110d060f090201 77
    0x3c0c203109500c0000d018800c0e859020b8082d180040c10501c00a0491032290740c00e0390300031910740140e25545a03094860300394540c0001c060204000c0300b0301c120780001082107200448007110b00c002039200c41e200104900c8104000c07607002c1040d04c40c4820561042c075080a0303007100c400070120440007018641030990729544060004140c41c2400c1c42003901002c0c4c00e401c0c260910050428040072000018212a0540010300ca072070b002ea031b000c2000c0c001462040200036095159180314010310140105081e2244d400d105800c0042050080021010410303c448041e00f9521400c0c5220700388100454070a480f440041d00c2c000313040d88032026600441c1642d1828150b100582c100d490300d0003021141900c0c50300103c20400240b4041e9000b8850f081c4111108100c603980c072038172094140c00a9004111102001d1283c0c82001441d204400c081d080440e404c001d64100703100000d006001d281001080280000161400c5070f44116034401c40329805242070021007200900000604034401c0102d0201c0d28 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 353978084 1250 353976834 353976853
    0x180e12040608010911040b03040c180f050c0327010605031218090103080a030207031704030c140601080d0f120e0c130612060213080d02150a140703020903030c07030c08 74
    0x340b405030702046416040c05c1400e080c00c10f403c1d1280b030791000e00100e0b0710420140c400242440b2200d100700c0c0416480d000044c124040c03075a15402da80b8024002c240540c401c2042003068500c0c940110003c0d9030290107083d0120640354400d00500d9190003040e031610030000001c42600d5600d0003801d01850b580c4898010f0307006030090128a034030a007c02001c02c1ca050110549070751003a03000d00020341c0a850100344101d20f6082e078800e044016030303003580014002c81c100428410980d0445011014810003486a5032411480c10380740e01d003020548040000c0380550240c1144a0301040480b0820004104228a004011140d44441496201d8002e01120821101c4950144200f01c01c9524029040583c41c409030303039420003540800c0b03680050600e03030000031426000411070b64801c16069001050800c0080a101081c1a40140301100c51401c0001900c0440b403081c4e1125003004080c05c1c090780741c0102d180024214018141c200c4110b200c0c2d4400001440143c400c24011500c0d89410f807200e1a6 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 353979334 1250 353978084 353978099
    0x1207150b030105040f0b07030b060c030903120307050405090727060909061a03180f0c011e0e0f010519020102030115031514030106210308010816180e1204060801 71
    0x440c02c54010b02800f00c2d26205e140844c032801440c2e58044aa40760009001c01e400000804070307001503028031502da1000c1207421a82c24100f1440c0e10300040030241c50b04520700b008008000e88200c0c0603481c01080380c0004100d000b4042d04624a817280301d8071001c03050050b50150000030206038800c50340054481800019008a540f1800054404c0c400045403582c4148545145035800502001d0103200c001307207005c0c2c2d0039405101c4100d060300d111001c0d1034043c4541d0001055001d01e011030540141070381500200380e607004815000b12200942d4080c5c01c0241090060f6500d0240d2804501900c0c4680e94100246a040d4003c1d410788980308010005001d050000701d0444541e25150110802e0001040c00025000e0094400403800200041202500d9040715811066084080c0c030b8110121484802010b8004801902401254005040381400b864010308050160b11808080324005950560003940d03d802c80041d40032034500300c8042d0030404100941d168424440c0320300080740c0034008a60076 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 353980584 1250 353979334 353979341
    0x9090903110706140d180219080c0118210c060e0102061006020c09280b09241c170405090a0606021c0203070506040b010503010e0102030402090412021207150b0301 72
    0x5034142e4103241006150070001004004001b0700c3e00c0e503500d4010750180169600410409109455109541440d10342141d20f40b611f01c1580d42941401108440900030504202000b0101d0340220549004c0340507207510903a50840710840500440302030b05011600c1904460340c1d84446000703a085960ba56100c0000020f584580d0260f98010b0300f00c007034021018600031160030b810001001e0091200c1382070802c203084c50356900c02e92485464581c00049414903082040aa0043c40204610040304a505c0308502c2d01e04c048802901c281c24881c101c07808402070204992031250302008043c400401400c840103190403500c01c251064954000141081d5040e01400c82102e825400524a0120005d2480300098010208004610080c4100b002050007080624029406100c00074a59410a001c5c1420340c0c1d4040d9002c02c40da0700420600005845072001e8951260f00094186d404100d041000c81c2810b0b01804440c0a88001041d028240b05a20411844102480d4000c11000562006042c00d8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 353981834 1250 353980584 353980607
    0x140f01210803040b04051e1518060c13030f0606080c01050703080708071101023c1b031308010506040b100806090c0d02070f05011a09041209090903110706 68
    0x8100060002c2030004e000d000300b440c0c0144c031510a482001410140c91044074010303000283c0c140d4800441c0b00d22040d210f40780250464040d0320106c085892422045907280b60140c00c200f401c12002500b640140340003c408400307103034404102c1c44c92114500340000504418014002c0070b00031120100015070152003100c09040e4142c84910540e501d18900b0340350780304000c0180090080c0c4000d421101c040a20040100481c800c015036000c20402c6800358a245140e0b40c0080d020020181014071a03c182080e11042c1c070350600c10140e044d0303000c0c01c0d02d4150700444103180c10905507604080355a15041d0800303485903000392010444082c01c04200200048c3c09103110001c0b41c4d5110201c1c040d030600c400c0507035100050f10b24003032402450000c10400caa100c5c0e1819980c030f04403281e03e081042002e0150a00c0c910074640002d05504420000410300c0c180039000502030390b1018444035540340546000b90040c450b03050100074100840c28040c103140396030b01040040c0d0242d0080420b410340070f023250414 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 353983084 1250 353981834 353981843
    0xf05100507051f0f020412050d0906090504091a090a17030103031e0314090c01081b16050c040504060222230f060a0207030c0e01030222140f0121 64
    0x1940c00b803e158a40401c0c0141c2444404540701c00c3c1001902929000600080540707081000070818030303084c8603051600304409081003040880081040c00d034022921820349004441c002000e0703605140c030300000d51141d00d149124000f030100b00011540d01050080f8114015000091b0320004110001454403090200030302080c0c550038a80148650070380e40c1702520405090004001d101500d25241e42007007102d04170079030381c4518485021940e0250410350011421b00c00f6145c0d00440c050070381e000e80200000c1c8140f0000c0b0107030040c1032203c10807001c0c4903054080d000300010b051508024010b035004500000702009080f4003841c0100d089c9101d441210b440c0081c142c211040100155004c1070310030500795100282140010716645c400000708101b5000c2d800030f140051840c83e100381012180c3d070080c2d0784074a00307000400158507005000304104001944298402e40c0b08403240004101b8941c600c0400c1c20100c08000d164181202c60605a0317044030980081586040641e40070300615840040c03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 353984334 1250 353983084 353983093
    0xf0b040501080a180515071106040b15060d0f020901030e0d121e110d060510080f180d030c08010f0506180105091009051804031d0103060504060f0510050705 69
    0xa0760340701d0941c0b203505030034101ca003284103010341500c585103040c0320781851910300700142c400d10400d15040b188107186e103d800c8c07003c0d113030618042c0c4503040c10200081c00c000f881c00c8800d4800c015076940e1701c101c48510303100490400c2000300d401e500b1002900070026a60100c4c0c60302c0900d9400305000120915499805c0d5120030314010016603610240205030036150000b075028412100400290158001c50601941020713110341b00e400c44081940c065500060003904415200041658080540340d0320042c043d90142d0142c80f44407414110001d0008a15070600602491910301da03416048071030403c0003a501c0c81080c0c3d882e0704018a400410b886000d500110070004054040c0800c1008101c602050502d64203108240d00030814007400800300c0b00c006951003005203d5458464000108d803000041401d420745403642d00501641945080000101c0f008412440140e100f5042080540b5002d80b0a001c11070b075034130801088904c0e5016484c460b80e00c03e2280150b0a00c0780040d2071038150040b00a0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 353985584 1250 353984334 353984341
    0xf0f09030a03090507210209100812030709050a030302030702090a0e0d110111070b241e030c03071805151807020c040212010303030c110705040c17100f0b04050108 72
    0x65005194040d011501c078024102c00142c8910010281011681468070030300b01081d841c41000740f4508c00400b140d541880a40003800104000102c6003000020708001d940e0701d40f90404140c540a81c00d47c800c0340d0040300c194000c01007640c044043c00c00b6510035100494075844000000040c1c940411110b44d042c0d0000000303a80790b520403420011400d011800000b01c9038825144051140d000302025220741c04c0300c1b0140104210301e9000310100d4021121144c4082514000044866140c401d8070180805422260010799500303200308030b8000310007000c507050b0326550340881030512511551417144c5840c0000192250304035403091903040400502600710b94100501d46451a1009000030045204040c400500c9440b03501c0200b5a030b00d034860084181d980365180c010165040100140200300e03904000070080207001852006071907017143c0215544405401c100d6840102000d006440240d40d8180543c820703181c20300e00107403070200848a202c55200c40918150b4031452007558001101c0d40c000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 353986834 1250 353985584 353985587
    0x1205011803021902040f060e090d0215010302220509010506031b061e0d02030109020702040b030d171503032109030c03030a110f0c1005150303040909020607050709050f0f09030a 78
    0x41045920017040000e45000600001040720810341041003894130301414080c20311010415000d4500280c40284440395030320f2100d81084006100003401003101c4800c0c1c4885200b9020395010400e0300c4082044607141142213107000c0c040030390350b190184c05074100d03000f220070014207840720000d030140c081442c0004415600c440c43c0b101158031701c0d81c040f00340000c903107485460000b076000f821170720405038a03840203004101c00ca4100307501c204d00c25444484180c15a9801100201a20b5020f5460840326524a8100a5003002d80d021540d45400f0008000709040080241c0c9030a241d00301700415601c3e03460000542d07503071251021203070342c0d03a100f80005844102980c100c511501e0304841900d06280840d6203990440d04480c122504640082132800f881503564401e680e0310141041c22a400920248042601c80c412070040310003541d2100300346800d40d1500000c42c0d40055215046813600c55a40d560b000c0209000d94010815807035600100d4040e00e281121180142d84582c013840c6050401da40 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 353988084 1250 353986834 353986873
    0x90515181c020307170709020a0f0e150d0e0613080d05130f0b0a0e0705010e040b210313091e0b0d0c1706010f030507050907090305030301120501180302 67
    0xeaa03071920110060301401070710305000b180010024400d41302d141d80e0441580a0070800716402013880540705200c0032220300e0740300d0803071a03024500d424a55050311605000c108000200200c040d1090800a41c641000050f80d120b04110b44400f010380e14140c59003032000100e0f0603070000103804000148110b081c1000c480d8085a00003941501c00c8403070551554954182c00b09800c4262080401c4108001e039849880c000c103145228140058030005007801d001074031211120400c24000c903550720082c100c8d5100c10142d40f000c0917a424000400c50290001c1c00c3c1c0d80d41c48001108444503e51000080d2070f84140500d950411139213440700950b410503504400102003c4242c0c5070701584d400001004540d0030501304015001044454401560701e89046150540681c004074089401d183c040000c0b0b0400719541c1c003a600c048400c40880d859906080f164510281c00180c982c0c04000b00010718203142c2c084c600710b018400e10092107030a80c2d11006030b114040074600540960805a5540c0d0b0843c266030303 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 353989334 1250 353988084 353988109
    0x11040e120c03040801050a0f1a03030406030e1219021207020f0f040f0509010608010b01050405030d0f1e030b041406030d05212a04080309220c09051518 67
    0xc1100d081070744e15a411402d4800c00e07503140300c840741e4603146d2032165130660042e54001e00750070740403040c3e2001d0303800466502d00c11441001c0c01c1581d6401d14440d40b40041c000c10040d52000da08050301c1e0060300e810258211441110b54000d0310070b103041c02c0c3c1c0c00e070244025505443d030011b0034010701034015010300c11441030f0804010740c0550390308403e90315032820344a26030060404c0c1c1c00020b656402d0160303203421946645a090f05000050004000c960340016451340e4000003450310451007502001c0079504142c0d08800300160f80800e141c03070303180c07194950300141c80020211801e020003030810500061035941945c40c1901900319440c035a106500440041c515400740210b8244071440415125107840800d0301c1a4407080c8102551800000301c0d8159580117520010b40a0b28180ca0719130415624401c2c40d080314003949104882055100c21600b07403401e001d49025060001408015006114103c94040c0b03030b01c83d60005000041030390888080d503048842400310102e542940d88100001035290b131 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 353990584 1250 353989334 353989357
    0x1501050f0409050a030305060a060e0f040216150e12030103031d191202040506040c0512040f0f06020c0f0c030304090f0f0606050c1c0f08060307030602041211040e12 73
    0x21814030000403c00c00c0483e0300e40d40030303940026583c104401040071608995102c841005000d41e090308099842d505000c0c0840307012100140d44d02c40401d43d81e690041004005030410101d42510003000c01c441d00701000c1e01100078199444080c980d40000054002030001400043c03a0248400105c2d01d03104503001040c0c0300500481c84210180740000380d222442c1c0002c6500b0b4400c001c120304608280c003c270b90308480304a90034450606403950043c03060081e00691001a0343e010080b50500118101045c1515000300c001111000c8609100c0045c0d031140400061900c00c26140014403200032881200240c4014003a40c9000c0c40d0108080240000c03501004107141d4503014190610042d00ca03207801071126413111610388409000c0581005010300c0701030388014101e4500d04103254000d803d481002814103024100d9190f89010903d412095007004180501c000340106030701046090074582d052060f80003115540503007046c0403e44111a03500e9000b40c2c8005032a00da528000310182c10604100b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 353991834 1250 353990584 353990591
    0xf07150801091a1018060c0308010b03040230030714190312020f090607030206040308180c0904030e03011d0d14032a030c03012c0a02030613090b07020d021501050f04 73
    0x10740c130b400000001700303a014102042c02c2a2911040541200b201d600600320548003c0c03c5241540205020040300400900888803d00c0c002d920f00004907c08420000f00314203c0c1c0d140c1405190520300710300c81c010640d246100302d0b001844040000100b020503c0d40c507655003d0252210801e02003e50040520240f511030f0038820240319844450142140c24003a80c010000d40c07e05040107449980003402500c840021802e549444250010360b1080b0310400381d89501c0b21360384900b012142017039003c400d1a410350030800b40740e11411030341c88415810b445600645040c8080c140c410303100342500084694003e0030610000d072000c05c482450b10100c0f20691191101c22500d99115102a4401c44101d1b5001c2c03800f0005100c0880034202e84002c0742c40400101030048250811417481c000c0080036542e909400000245850300e81581c600c0101c8a400c1060000005034508102c0c0040100c44102c0107110b50351210000c0e910004016160001803012840142d00302030500c00441208a85203400944 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 353993084 1250 353991834 353991857
    0xd050a02120d14070c080f07020406090e0604120f27120308011a1c0902240405090a05061807170108060601030b060f09120f07150801091a10 62
    0x1001c00003010006094180061518501151202e2646020b0b14002c1080303107901d030883c0042d00060464401d034000e90b840b9501c079059803000502524194001c00d61003420600b6040a4003000120580900d100c0d429060103480070706400c032144805c400a803000502070113554440642000303125606500c02d4100e040555407a49003040600f080740c82c00300d00040040004100c12507280306100311411220050301c1c130303120320704800e56141a0a40c641480e05983d0340b103500c0865550141c440420310441e10000401d442154001207990010700c9941e0180040800103444c0a1841c480c291062a000f07010b10722400a0210a107101000184440c040c4100356800300020000840d0f214024043e0b140100030703e240510004042d2903640450600445045c4003040c00c5100c10420354400b0b00c01a0b4412351556045800a8509039a04202c01100d010300100407641810340312644601c19410b071102000b0f6641d0b5000041103542c12803074030504042302000022140f6003d0b031061414a45407030071030030030301 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 353994334 1250 353993084 353993113
    0x210a0501090f0c061e030b01030b041a1e03030f0a03022101052706100c0204050906060909060403080f071e0f0f09080715140304030801050f0603090d050a02 69
    0x1c110010688044404840c10810030403072116501c040c100300e00d8005070984042000059110807404d1090600d512608043d4103170b4402c0d4400f42036180010410f00c00210441c11119201070310301e4085004a441101c0d400219060382804401c00401400a502e0031114410b0000325030480001201015020032017151103501ea40d00e803a000381c04508240455501d008200400f481c03c10b00c541800b140c07121900f901c0b28207072001c801e40c464819100a080f0750280700b4202c442442110009500910780f006100240c0000910688078141c00d0700c4050b101e8031655003080d50380a040310010001580400000d01d00c00140d10040e4000754141480d10364003c100c2c0c85002c1c608000b046440004603010180403840b503004803a00000000c0c1c0c240383d144581800009602c6982e41e000340b045000b14505001c0d085444ac0c1090711074802000c6031561642000c3c03600810350182845000d01c24050102c0202d2245400400c4038014580c2c2c50082c480c030326110b0f2042d01d03603400c4980100d066008000d04108601e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 353995584 1250 353994334 353994341
    0x15130b040f05090a0c12150b03010f0609050d05280f030c0605100302010c1b1a130510121109030d020303091005010308040b0315061b0d030b210a0501 66
    0x280169885808200e0600c024000c0d10080100b2200401d4100350014040b0398101b109425101100800403410342d03c0d041c068040b80750380e0307800700e8001e0070000000501d41d8840d40101003550615a1408440b0703030345400b00001001846e070b001e0b2450b01300c50364241e0b0700074002c0348544101b400000d0004a074405a11201c0f01c40b032981200380d010400184404041014611505038403250b03402c2049182419500001c1c100500d00e200100b0b4141010020b0780e510091111200052440162000e00032403007034005107044d000480860000c4200b11000310b100d10b0442c505503411001552046500b00100d04a60003428038004138905004040240e401651000c1c02185098012070b002143d4a06240f55a2460040c07444001140107240100500004501a007228100d80540ba8416200c1c0c4600460000b1620030140d02c0354400400140c000d00340c16401461189c4c1000d120a6401c5220381c0302081e02612600003229901501e5108242b00c104000303152403803071507804000c6030001a00c2c0d5803a5800c5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 353996834 1250 353995584 353995589
    0x2110020a021501052704020f06030108073305090f0402030c040f09050402010c030809030d1e0c030608031c090f0c15020f0a1515092915130b04 63
    0x503000b50412080010603403603428010b01c0180c0b802d003031026404c81c0480400b600710000b80217459008011405655502d0504150343c1c0004060b00c0c1d076940e541e1081641c603005440760b00c00d2080c400c0c540c440b80c0311240d83d0b840b444040d65070089941c10122001181e8a0344410741c8580d215902640600543e00c0342d00c09140b16058070b43c0c1240d0b445003402d00302c44d807410159020005880c01c280c10017006136804070345a00d170180d260426201c0c03038503420811070560145020101540313140c107249c3c0402001c06003c500c2440602031040080e070601c0101102a01c0c00c0d405411403030350041000c3e0543d01c40c18440901c82c800050300000d41282180e45a80c0070b00800c400503100d840c1c103004140048900a071221b550408240014082d5001c1d54600503103990303035100050304400e00e107072011959524a4000341140e01d9174441c89002c3c50317241d11012000b05503440707100c0131005400709142c02c1c60001c000f49131194240108603410f4000003121480b26507000309c010b10148404a20300003040b01d40c400c040c002 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 353998084 1250 353996834 353996837
    0x307060e0c040608030702030705091008060f060108070c020f15040e0a020309191e020604030602031e011d01030f14101e02031509070306080d031b08062110020a 71
    0x20741910000411068481c103130044c015a8004000800050342c0000310441140e5064402d807071710b503940d0a40031501415a0303004007001e0088408014900c0e5020f03084510445003600c881483d9180d2503811034542405590082d08050201c140c23281c07a14140742c0d40340395a1940d0524919160701c03a45450004e8000b039a4001040b034000c0f041c880034035000d1016a00344040c12141c0158814240c0300c1820b096031180441d54098162080c02055407606811203000e07641011081d9034904050102c2c0c0410700d8460344088415411000103c4d50400384212049078901032a51012142d0854980140420150b0000c603080e400400100b50700a100f0b008409040c0440f140016034a80142ca440c81c2c1c98001000c030f0312070703030b0320410800aa500403801d40040400c010355940301c8541c0c81d81010381c020150b070b400c2401c00b44501c60301f0b07049642d0300d07030000c104c04c60000f071300c8140034800f591041c2c5030404180d607400d500030251509d251101089000751103c481040007169154104006500120b07401800001e0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 353999334 1250 353998084 353998093
    0xc030f0a020906010f080a02070c0308030712050a02030106020a021201061a0c060c0406080c0703030b09151206010506070f030c0c150f09060207060309111507150e0a030c02030307060e 81
    0x2041d0318100c5403042d44070f0030a00b011610707409040401445214000c180001c2d07030f0fa02154104c1803211640c28140a117502c0002c181d682d08110783c001d071101444400f1180381504200000300b19030424001d80c0d040301c0c0c4907001000c0855050303082100311501410110300f59135071860001185100d0440100001003a22aa0765448006180b0b0b103040240c024111561901304000410030745a001d01c0083e88141940c120540301c1d16030b460120003070044030003a0780c1e00007102c1043c844a00c0131804450102d043c103c2d0011420781100c2a000d4981c0003d02c602c603408102480080081900303502c0e0007172014400e04c2d0200110503696501054090550442c454008000c41195441c640040580c009404942040718400c1e10b040402560340300c241c0110410141c035240a00c04102d6414507150080400500105209001c028005699084000e040d18004100081e408044000d44915006429204050440700c1a141c0b0143c8124542000898040c8030400400c0301017085803003440d441042c000043c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 354000584 1250 353999334 353999353
    0x50a0c0515030108120313231b0303071e06020315010f11070524041e210609080d05040308062403041e020307290c19050c030f 56
    0x2201c1d040c40700a1511140040005226402c1c000560304141407101c005940d0303aa58000420070203040c100300050401c850a550042c609412246501000740315070700300c070001104407901e20303000403507400c9268140e0800c00202010505428010b250351541c2080c055040e2a48e5807010200da004440b5600c002824000745803c960344120030f04003c0000c0c1c64180c4030440c3c03482d0220b8983c0060302c145480350f0035240e00540101003006a410001d0b11810546071201c1ea5007010703840200c4c408804800c80e900320310002c180607102d00340021855100c82c0e00161503201507540c030401860511401d44190805100f05c100c595114040c40c2c1c071652013070b607070340d00141401001d001c2c1444264240c0a040c040e00451250040e00340c01c1902d9005401c45048400340d528840990021080381c2e0020307406009090b0003040e100b410940004c0c04510307082c28403200020380c01511509004880402050782c00c200451a40f80e103800c145010903500910646101005003030009150102c4551901000c0e0000c2c0482d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 354001834 1250 354000584 354000589
    0x711100903060b0f0303030a0b0a05211c0507080a02030d0203130c050901121e120c0b0105040203060f090a140115141810170123030a05060a0b01030207050a0c05 71
    0xa00c020f0500c162030030422141402d000944a000c000d011170b4060360f503500b08581c05c0d5244200840100001b0341520818981c0d01c1c05840280c1e02d0001c0000c052107040b01c96018000f01a000480e000002d50b07c0b01c0c00c0004e00c0c0e4603e10f0075441480d184c01103100c00d0050683c08509480118007902e04900101c800154901d07040344c0b0514554402d034410840b0000401c4154010800c1032000760703001c150000800c541800d44481c0c84882d04002e401820038000080105400807000001c030f501405807248581c1c3c1c1c8008010a03840308031040d9401c0f0719246e280344064200b007644160450800100070400d42004100d090030840260b0004107110100f0f01c03911440c54000d04a10403014400940354605017042c9019408034035035410803400391714074414100c2120700c600c07030151b4041e00444601085582d42e414a1150700201d141041100c1400f0b07021814510b4001032840c1d2050344480501043d585001e40040240b07081c0c00350702e0515408200860010700284004803105204160a610650a00f0203 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 354003084 1250 354001834 354001841
    0x70c05100603050d020c060a030908070b0424090203030409090809031b0a050d0f02190b0c03190f140c010b0d05030a141201090515041503030e010201020406080606071110090306 78
    0x2000c15900021104146030f1160408ca81082c0510b08000c07542440b82c0c513200402c4e100380000580150340000500c0308100d807a030766603407080c2c400350031410488000c0c2c0c904238201c82e04400000e5155104000c00c0210384295000940f49034007841030b0a0501c0081c00100b824030360166000c006500c0301e0f0110205a140c18042080600b10075035801000240c143c1d184542c030420b0f080081d201d550140078203080b01c4105006031020300b020303000c201c1d140c80c0400320f801d9598121140150f144610745c1005081e1a200d2991140c0004107591a41d840183c1c0b84a0042c20360b02c00c40001841d9501e0360440041030f03d4034000110220b120f00011030341c0d50444000105403031024018039003205001c00c05004400c162a40060550303c08590005007038544410304420105200d09480d0081e040c02580c0d071850b40c0046000084902a84803440c00104810049080b0f10450040c5000f184a03400892002e0500002414045100390700c00031100c4846000101d1141842550368001586000140108400c500 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 354004334 1250 354003084 354003103
    0x150f0806060118030f11210c1c0c17010b040203040809100201061a03010e01060f020a03050f04230a0905070903030e060706050c030a060909020906040902010e060a05040608130506040b070c0510060305 88
    0xc0c600d0040c4e41c101c64040d40c2341c4004c0c0c282c16100f01c038200700f024940d20141a51030341460f880224940b1055903041809902c03c0900f082d030310b05510708562001e003401c05000f02d03403040390b0111500e850030002c1c2042194405802d00a002199a6680c0c04a01171031340d00c82034040100702683c4142c0341e40c50310960380d0b56204144c028408000c1081040040f040d0001500682e01360b15050850f201c030002c0c1ca00b9040b41c05942e0180c1e00b66080000c000c0d604507002202d40d9a880b100f940c40e01c451585814606003900c20541c1c001d0001040c0c06030030400300e0300c2801da82031700380c000411291601d0341d03030344800f0282c1c0d00548150804d0b080001c1440040d07026803040c10010a081e110520040d011900050324000c070080109010300c1e01c03900d041085a1207000d6643c030040c0014100c5132500801d44000300650441d010f00ba0109202c1004507900d4046000d2189080d940704004001c159100e607a55030304e00c0b6001d0820fa0501c10180c4181c0005801440720003800080843d0009020740b550814515004869 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 354005584 1250 354004334 354004369
    0x2130314100509010903020d0f12060902070201020606090f0c090d1a180c060f0a110a051f05090a141c0305150105070302100e03090d0501150f0806060118030f11 71
    0x3485c150003c0d0300825103255410050402c54a03403c84218140c0e0200f0084c01c600c01d10742e1606101181d50f0003c0e5024010b1f46000ba0b081b503050395220400c1c000710501c1a40e103580c81205100004641c6541600101a4042d01a00c00d02c0c00040ca5a100060000c02d000c880042a0b4800200142c0600c041c080824501540300101280c00d21500426000e204442520070341c074000003803101c1c0550040c600a5118001082102c503100268208580c1b00d060001c480800c8030784101c0582201c995a00905000d80750100113001559059661000600d008402240090150006c114061008a16850499030f510345000c00e5500e82100c40c0d03030701e0746104003500d41070140c203104240100f980003440200810412200040d070312010340540b85140075074003810364000c0d0400f0403881080700c10341061100c400507640301042c042c1c036034881c214500d001d40514038155001000040d02d40d0b2082c020980d04a402400d900000d5403680c603800c1c0d6090315082c00b51040703510000040303420705003c0740000a00c2d090 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 354006834 1250 354005584 354005591
    0xc040302040e0319032a0f02060705040501200a02210d050a0e010c1704180c0201091a0a0f020c030712050405180405030c0f0d030e03030103020906040213031410050901 74
    0x2807908803104d12002c0310700700030143c1e9000303112030440304040c6801c2da51124030040c1110341c0d1000001800210310703040400041c05048046208140500180d400b900c0741612107401100003e00f42603c40f0b800c0c070549072864411056050b000d41c40701825050741c0e40808003448015054208014904680c000d10201003050400038411055400000300d80e45000920f09088400e03841c0c200101d50300c41c0c8a000c0c0c195500005070001d81e55144a10840f815440803409022580892105900b00e50348a00d018141c0c0c513450059008010a400c901c0d81c1c040c42402000980d15095142d50b42240c2146404c1003080c0d100007809010b008103102c8003218044545402e603d0b00c1e00341000718045203111080322160701922004101000030a1040d1a2088000001c490301e07c1c540750340540c0d80d014204802c0010074070345000000380c0d0b8400310440e4140c80d0040c01c94005500c0300c109010081d4806089449a8460b140c004400a407648082c402c00965020040c488035441400ac08101c032809008214507a14 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 354008084 1250 354006834 354006847
    0x7080d050703050f0a03111c05160c08161502040918170a11030c07030c080a080a0e0102010b03060408090406080102090a051009090507050a030f0213091d0102030c040302040e03 78
    0x24007a0072103944207468040503441da0a45c22040d07018040c04000403041000110300000c80c9848200301c4280c44a80c1c160500854503071044010300100010250780014900100301e90200b40d00707000900000d802c087e96292070b1047d50301c40b803280071404602142a2034000404005000181c040c1211a803001021030008c200c107543e802500c4600303041c1c040c40c81c0c00b001c01d2803486540509103a1070801c0701c020940b0390b5507002d00d01c07880d11424a800111100c1c000300340b011821110001d00041d000707600492092030540101815030700c07400e800d03028504642d00c1c2c10123510651424068079004d50f1048040c691100c0c03081080000303642d4180c001e030078560310501c0303241565614103681000700d40007070714035800040150004844510040d004800010704003028044402e0b4084003c1119003000e680030804048401046800d9104030700004441050420007448641500ea001d60850340b29013007080715000c00222a1400e9820445000041c1d03071004c2410025070900340241b000c1c10305c2c2100518913104 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 354009334 1250 354008084 354008087
    0x818030615010e0102030d020d0902100f020a030e13090302011b0e01020307061109060301060504060e0a0e0f0703020409240807050607140106050607050f01060501080c04181b0207080d050703 84
    0x18807103101c0b81006030307a20700c5401c181d00134000c031034076054003410640d82d88010494000192030701503401ca0250700360750b0403049221710a20381405028035a82c00b81c500c410440d10121054800c40d00140c1d0f100341da01c5148510114140704405050b4441d03000401c0840b80b6400028010519424601c00d1010114528403581e0303000c01155103040d84401c0001b555140080300300158060012010b40043e000400030461641082c00b070302c101c94259480707900100e15441401000940ca124404241d11114081200c2d0806440034907840f100900d00141003c5c0d440590200350b942d00d90076004041901800002d0041d450081c0f400500384800050240600e040c003c110144540e0501800182c1907003032103101c020086d0490b07001800c00504135901c03014070f414110b46034045000c09c103140e50319000c000101940548030a40c4564a036010040c1490714020400041c01130221000480907920004564200d42001c92181d0b008800d41c010300100e401c140c1e0b10b924013a1000000b400340201480350b00d0000c0e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 354010584 1250 354009334 354009361
    0x31e0607030606141c0b18150d02062a19030908010e070e0901150e18010504080406030c0207030203070b190e0d060c0509150c010b0a050f06071b0308180306 69
    0x10034048060201c4020f4207413541c0003c00009012542c0412007c05005080c900c02040b2401a2403581c09030501350402000c011810180200094106e40d00f07011201c0c0c6900e003c145000d051108003440d00720700d10380e208000e05040200a1506d0b401004421250a15900c80d80d508003821060008101501d802019603544100d240702c1c143d41d509120300002d07040d030420b41286442c003101d6004e03c00d806403280e1007041d03502c00460320a101491102186040980140105409107402440c140e24160414102310060b00464a0b20415880703480400001610108103450040100f00042500c40302c00c0c844c0c00340c0352042503410108001903070704d0f1007a09a0300c00083c1482c8a62143c000121001c3c0d40d00103440c64001c2c0001150b111078081c52603170006e60440000c06008400348000c10888030b0001c100302c030404c07040c000e840d00070780b803140e001d8040d0801000400c103072401380703401610350f5014820840642034603410480b240c810106030350040c40380c00c0228401440b006c4015015038680702d0311a0004 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 354011834 1250 354010584 354010597
    0x10302180d08040e010b0a0f030b101b02031009020f0901030c36052707090f150308090a14090a0903090b070c03020907020d1409031e060703060614 65
    0x340465400c480410222000b11001000c1300a0f595010390303510040001160014107842c0d01150781540105d610074401d1092100d00103005088040e038820a41080791200c08111100c014100c20003c2c0b2070160717034100144400848145030105046100c0e105005031000c103280e0307a5009007085001400007541d00034696040d2103072108030b44620481d11144502100490140150859648074410100c001399040244500300402c425100320315403285100358646400f0110f00c441c0c100c1c4d1424048046a078000003e401045040451500d2094440e001c501d281035008031004a0006140403190400c0d20401d80140b1414941401444e0300c503010594691004040e210103940d6004500100760081c0300c0e4001030705101d1003643d21401945403401c0c00c509940170607842181035a00040b070b010310008510b145500f2954a41d80b01d1130f11680f115442c4c0d085403450320f9041c0501c00000106040c0003180c1c001500c8034800511050401c220040d04a4589400c520100700c800081741d1003003081c0804480e035 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 354013084 1250 354011834 354011839
    0x6030c1c03080a11030a0e0f160e0c07060c02030d0b031603030305070c050d02070303021b061b070902121603060303021c0c080412031b020f09070c060f02031501030218 74
    0xc140d41e80f04800700041080100000704098080f0034000344d0130a5900844000b5080c00407695002082000316030303992140b41030807400f1100c00300248000c0d5003803110304d90003510013000d180c00c020740307603413407070300b07841d95050f84030b0042c0e101140312070b448400c60142010420040d005422210202104407a0032a4140005418035031502c8c0804d12562003105045207064104013034031b0386035400e00c2c4c0094840401e4803050b0010b1184010340050004140308000c20210f000389a0391030048441d1902c42041b0f12400c070b240603030083c40c00009050b0703e01c0c0002e0401244116000c045403910349070325a0342c6844109800c08041c40e005c2c0520009400043c655400b42000225107058035800f00c0131a2140511103004025403404280080c2030f4100c1d03090140b140d84a41c940d80342208040c2045005590180400380d03002240810441050800036103940d003156552422034401e2100f82c0310780b01a44c110801c0c4869465001040043c008503070079144200d66000d10302545403100c0c3e900780c010581400b445052 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 354014334 1250 354013084 354013097
    0x120d08180606150d06060504062c101707050904060e090601030311070807080f07210807030512090a030206070e1509280504050f0106020d0f0318050606030c1c03 71
    0x80d03005004020740c0c403c04e110683c240001c60b201c1300020815005441204003246990000740b03c011590444140b2040b240d00c41c1c244150718090070080c000000720400414003130110b410544070900000c1035840341c5040c2d100e103661003071041c00b030000722442036001c4100042103100b8010000d4011814904494040c64540380500300c180d2a02d007450125882070540e07104850340001c4680010848002181940c4140d40c4036907521502c5c50111841710369460900c02036a06180001071014001d08a0a40030749442401c00310240610008a182680c2800c115407102e0082420164100240e0341d000b442d910345454034041c0100410224000796000031010030000c81e640040d521140d036603001d030030740f00c551840c0c40c030b4010740b50a0416850f82c06411b014604110016030080d0340d51300c0c143e040b1251a4001c1c030b036083c4801d40484001748103003240c43c00c041c0c640c400702800702e840128811b451800384000e13004d41e003803d200b0103203000d03d80c620041c002e40002d6021203140d100b00c1c0070032902503010305048 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 354015584 1250 354014334 354014359
    0xb0a0c02070f060207030b0c040503030703030e0304090e0c03060a0c051c0f02070803040c080109110915130c09050d030f05070c030b040f15050402130b060405120d08180606 76
    0x9904026842c0c00040030000c1409001401d01e81c0000d680040301e0185e282040d40740c998004680c5980308a018594150b0301c1081810002403080e48a0400c000a0806403814603880350102c2040d58000704880c5196441220030015501d0306001e85500905194006c2085070084000a0501d004441241001844100c8900c1d04400b081c1c1082e0141e004000c421550350115107000f060f01c1c0c00559007035502004e11040802e2000052051003405074103d440c0b2145200800308202800c0e070020a040018048050b0002c02900da080c14404058072040c07000c0b9415890f124014080141984028030a84101c651400420742000e484059001180f80940da507003100d0400000714043c60340000c20034080300e010002403000350700c800341302548500b0b0455032112160100d4016160143c5000e984160000103482d101407069209070803251004d41850708041c0d880000448991a9603900051500010320460110380d01540f42540801c4280801004600ca020350554445000f45518054030056429 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 354016834 1250 354015584 354015587
    0x507032006010609060809070e13020a03060507030e06010b03010b031b0c0c0901060c170c07031e0311030f07062c0d020106140f04020d02120f01031209030b0a0c 71
    0x80e20358115a035030944080240d5211080d5503403030900c14140062850440842c0d51407103a0705442c040d4403004000c1541d02d00b8075075402c83c0c2c0500904064601e41d160340080d0b0042c2c0b90050510300450041e14001690315001001506903680c85011004d140c00540050002c1145402624107480a40851a031680e4843c8501030088030301c01c420400c031800220700110304040c00108800d00403001d0703502c5201030340d03a00d5080d0f40079680c2c070030b00078010b40605000d0241042e401c0e01030400440c416040712603060b500e4460145000a031070810b83c0381e29001c0c035003c00345030300000350b00070341800c00c0e008500c0c008d6007881c41152406506001040c4a0b190f50000d0760352890840202c600d45100c00d0000303080090360074000d540304120700260026508003c00058105456a10041031007030241902d0415070403481048025840091900e003450ba00f03005003e0300e403a40c030304504c1c0304034001824105d055044d03041124136a80c03107000759401c00403554000c0c00001c805903061900005441c90110f50012040c20 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 354018084 1250 354016834 354016847
    0x106030f15090215091005181009151101050618070c061e15060306080c0103020705121303110301110414150c070f05040b0609010f0c020303070f02040c08041101050703 74
    0x10084d6000b070008041d102c0c080311980080454080031501d9490381e40300e912060b5031074040c0081603c8288920081c9000e6410144200c41c1c0580d800d150407098252a44240e580700c050110801c00043e14082d080b9000550034420960000c80c01c9400a80a00e07c2409541c10304000070700d20420802c00e84201c008109081e04580020407440702c00011042c04116014000c002000c0d41e8000c07038000302e0000401b80e0091098000303503568203024206852140005402035407089130115103500c14010801c015030040d401800402c6c003c0218403254529505081608200c0011518405e074540b000d52106400020200c6045070a00081c2148038400d03c0b0010380107010900b5884000c8000140c19000c0c050042001c400359980903c0701c00c0d9458442c41844101c64802110715081001000340e0107056010740c19151058841e03142411a11406901013800d50f000310b601118040034000d00f000441c5840d005001c004940380c0340066041c5400e480f05101251461111818072400040700e00a040c4200c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 354019334 1250 354018084 354018101
    0xa0201121b110c100212130b04030c1d060d060f140903090a0605070203030301060503060a1508060f040203190b0609030a2109080303071803020d050c09090106030f15 73
    0x64804801c00c000c0070142c14141c90041d0302106005603071800c00c075458400328415024000e940205080c81d12002d08940030b620041070000890501d1900141c0c6041c00d9000f04040c52140710300003802c0c0d140120321620203088044080b81c25011004001c2aa201e00c0d803003040b041d80103600030440381a41d04a84000300f1180481c02d260240d20400c01031442d200000074201400151a000105650341004441500802ca00254150070400c0100017591040300910741040000f86200319059454140910003a80b801840c004104030b0001c102442c58003840d11515580c0940c1d0079840d61500d00b0756141942c00c507201000106940c0c1034150f1107074582100743e81034000041c04072071212590b410300030007030300028040d1300707600148140c40c10006100e5021502240c030300348000c50450b102c9803015a0b801c00000d031144034000c0c20340b00000c05661307605401006240110054600c51a4900c03c0c401d8034140100b00c82944d038104441000021000003034040415081400c01d00b450901400c000003070810803 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 354020584 1250 354019334 354019361
    0x1303140c0a02151c09141f020d0b060c0f010c0c0f0212240405060112020a0e130c0b1b03160b13060c08090115030f0f020d0605090703060e0307050a020112 68
    0x1c240341282c885680c4143c03417803400b03805480c003003980b0480300c6030340d4002000c8400d2030030140700310301240c0904c3c03600644030b40e483c4040c0100d0075040000108078160403520054000da8803161940242070420720800c034400e1000d10700040140742c0d50302c804111020051000380140c0501c05464045402804030441c2e40400c40040504c80369008084210000300341e43c140c400707006100c0002096110142c0d03152040e6030282140701c40300e240449100e14404000d00d441440341d04102e0080005101c1c0030700c50054001111442c0c3c507904051030605502c0341e4181307145020b03030040109035898012505919030141d0700405031040340c0d44110341e141000100780300007400c803410b00c403801d212241c100c03a40c24820100c1c0d10003088503c8480243d100c00300c0c80c91101a040807817003000340d00499030300e4541e0744020b0300160150315400801e80e10182110000c440404450700880f0051081100902070808140d990758011414000e40b603c03a1a00e4205007c002414014281014115142103400c540b00300c4008 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 354021834 1250 354020584 354020617
    0x8070f171801050f040b0c0a03020d0f140f01230a0906091413080304030f17100f050102070b04060e12030a0903020f060a200c091303140c0a0215 64
    0x12040301070341544880000a5400e00c00003403241d451040d502c2d441250025220245500e946240760280d82c40482d0540405408102c41401041c042c01030080741000001d00041e0600e142000c488003440140414101c0c000038001040b140003a00445d06c451900034100c510300d0700a41001551140103603000b28880d41c10890006070031031981d441490010f8050f985c0710710039030b10140c951891010a1340010f0200f142480440c0c0440d2040f01d0451207640242000f40200c89190840c50305080c0440e68940144803a40041c082c0400303e280c200e0081c4420700040c040c8604047c0140740c0c40c01039010790000c00000c0c0040780e031540d070f4201034224006801c0003a250341e0303000701100500f0f01c1982d0100ba405800c008031500d1407414500211074070032060f9032355881441a80d0541d910364144180298401c2d104080c1003805035a110881c0d68011031404207803a50400c01e40c41c01401022a081e02c0c140c90303160034810b286031a14003107a5040c4a940c12606020b2800883c0303070100d002d0080849000ba107207d07 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 354023084 1250 354021834 354021841
    0x41a060315090a0c020d0207060f14120f01180905070909020a0e0106050d06050f060a0e0609040204080c19060207060c0203070b0d020903010f0c230d02030c07120f08070f17 76
    0x3a1540641d82030149035007030307810054401000741d98030f810710301c61100024011051a168144030f0304bd00ea03d012a0a045503280170152113069050a1040e52501c8103c8899001040081c0e00c0c9009103030765440015041c4072005190b02c60702d80b554005d21400710400e4403807840c0000c554848a800c0007801c910801e844180d43c442000501a0300b081112605c482e161990110319442c1101080c1200c1038000c222910b0110941001c0f2540c607034805506801450a002d401e682d0b60b00d1b400036201030207000b4000c220010161041100c41200b03a80c02a0b04041d8065040c44015400304800043c3c4296040c103a110050520219140c4083d503071007600c005d000410044c151401c940c004040e203030f004800921882c0c0040362b03108102d482d1540b1050101c1c212400411800092264140c140303030381c4088241c24414840c140390180c1c3e0084508a002c0340b000294a420050059030250095013545849019444c540d50b0240c013540c0060315480501074840114415288110b0005600c0a5180e035000c06604 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 354024334 1250 354023084 354023101
    0x112709090a0314070c090c020106031205090906061809040809130515100219060e010f060e0a0506090a05040519030906031409060411010207230f041a06031509 70
    0x1008000101d001404140000000f100f01c070302034401d000e82100948151600c0c2c08250401400c4c10380480c01595264400000442c000d01c46404150344162999650740901d041041070110300240745502c01c0c0d4050005003078402401c1d20707c101d221400c3c0c0390858241c0752400d0458250054080d01984003c1d0803e084803000c2c11074000c140508504a194120303c1034180c10055686071013250840103038442140c0303c401c010501281c99055024150000d02451140e00c0c0c5030079a042c0c003a942c420203480700810824441c0303000003568002810581000242040c00005d890b080d0003825100c01e82d5100c0020405000c01072011200d1013890180c1080074541c40e00e800b0740003144038071a1601003460b20070014440b0724a18040d601c151f221601404140d075440e07485040c11914542c0d154110301c03a0000100700c00e080418122012340c0c188000f110400590010000070462000c410303130041d4200078084c40032080c01e01c0100021036040f01d419449070b441280030980e402c04581515402030800007440f0440 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 354025584 1250 354024334 354024343
    0x180108010204170f061f09090506010611210306210105010302090901200c03070503041710090209040b06150a05030a1a0603010b07150501090b01090911270909 70
    0x120402e840c0151140150503019460712590404841e0b82d070410300000d941e0700c5400007540c0100086c0b1020000003030300c510000c0100c410200b0101e0b01d41c0c0c050b00c010b101103a00000280f180310618001007950006c550001001499581400000314901101007580c6030340c0c007000c008072401c0040c08440c0c456015100b40d4064007003172105a014003140030120310003040600809100e0200c110403079020040300c1c054403100303502000d5071041038003080c040d020028a050004000500300b0014840f1a5421441c007a804c4c40030500103120854070301146040161036540e51581d001e900b01d0503c0d440d9070381e10400b01d28252074102c08000802c000040040042d5000b0300070b58085c45100d1000c1202112444c0c0d41c06002074002c003126030002d1306000401c0203c400d403004200f034920661070a029264401c1001f41600c00c280c112402003621600c4403c1c155a002a03410000e00b1402070600c01e000340b091121806105030001c50000643d07410041c4868045698400c0d100440604a050740d881c0095445484 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 354026834 1250 354025584 354025589
    0x30c18131107021327060b0901080a1707121227110406030b1314010c1115070e1002010e03040b190c05030f160c08031801020601030f020609180108010204 68
    0xe826070368013626040c4581c0b1980c000010562520303582201400c505c882000305585088400c103468001690f410340312111018001d154842c02000c40406901d42501200b10300c01ca100b4030064140b01c001c0209900ca0146904a4a02d00b409000e140c1405000d00c082c0c00002d441c48042c54040c5080030015000440b160521030040b04c40622810b08407080106565440c072000c0c08100706000402c944222a070000da0072244900b5020400d10415055142035a00c3e14294001249a1901134103003d0002c0c00b900c1003031002521903419507e42410058003c01052506500a82c2d0400580081c24002d40c03110078040c2a01d001c40c2c0d122580e4255480d096032040042c002c4010f13003551160803441c09983c6c1c48020f1036024000d9820004803001103107068005180c4c000b20081d05400d00c00200d0000100003019128800123156034512243c2001040b03030050213907a046502c888010404584c91000344291168119012031b6140b5200c800581c1241c41e00b54115500c144200c00061601c0055004004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 354028084 1250 354026834 354026839
    0x31e020d02250b03060111070f18020304200102011e020403050705060406050a051e12040b01120b040f05011d01020408071505070f02210601051203030c1813110702 72
    0x1040d001d0703042c50700d14003000500103010180c180707401440319003418809540e02401c185843d04030180d0f0013102c81d01d800501d9001900001c03050030107000714a098a0540c403001486e080c294a5814a0341d5012040c1c1c3d446414548880883c00c841d110071f84c0b00b900309000d546d100c00c400840c468500050700c0c0c000e41c0588001c440030311401d8000034441c01c001003603030f00711070b09515040d04018010a094449034041e080860103020180303080010418124098840b82c0c0840d41e5030911407800b85040c1c403141078180c001e40e80c6100000c0368140019030700103603d0b61080c3c0c0b151180864450a10380280502010910801d20344002011265403910540c0a00106c800300000c8034955a0b0b81c0310341005440d200c07201400018020001c0c10007113044903c40f2400706201030403240690314100040e01d43d40c40a01402800381d0400340c010029443c0100c030300101a4080d00295196003851544102c540c0308400c51103000f811481a000e056594040c5d010690001c9807100380302d80c00b1488504c40b001d1380541c01c12031 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 354029334 1250 354028084 354028093
    0x1212122901080108280c030b0402130b0f1e0306070c06050703060509040f050705150d0b03060c37080106021b010f1b1707150e06060d031e020d02 64
    0x58030350300c28111141280d044101a0500c40d680b40054600520802c101c440b405075400070303990005485c4030b0054010750203202c8046190070300b40304205045070f075403c81d5507456040c03101005180e40c8000c480001200e00b25411801e101e89002401c05080d13440f050f061345401a00b08000356141c029041100040c070620040000d96207407201134007241e103507008444e0400c5500c40041e0004042111140100d405a011140429074410000d804c5402840c60904580ca000c1103041403555075020b462060310f4201c01802c1c0c10b01c0c000d0710346900e9010b0405900d1780d8901a40013210102c64144443c80d148401a50443c54400074900103401c616003031043c2d0005108080c0802a4074043c903800d001d5003c0c0507507814003800107c04080700c191400078a1007a4426081c3c00d80000500e0b000040d04000114004003a22800a03040600c001d440a03400ca81030740c0c0c01c1203403180702000041041d6034010300458000121070b8450500315601484201507031000d42041d18000012600041c0440314080c06a0803035 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 354030584 1250 354029334 354029411
    0x20a03120606172502030405120619090c0f060f0e011803060509102c070b1c090506100f0501110703060c1107060302090415121212 58
    0x120840d201d611980d0005803101201c5445600c03009411a08a81c0ca210201141c1c0f000740004402100b10011001c05a80001020460f90a100c142d44101c080068060419490001d002030034448140583c40f44c00ca55540c0000c041042c41001031014141a041c0c50b05080e444540180c460410001c0c820003140b80d00c41c007030001d5072048603500742200304003600264083c80c0d960740c107019210240000e10f442c020a506560b910b1014802c0d000c1d03040c0000f840351620412500d00802041c1c500f450342e191600203e42c10301007200401d00b140c0003064802140c0e0707001a01c2c0b40548009140b054401010341c094541400584000d200854041d02d080c0288210603694960041d90000101c944409158100765020404520706034001c68141c0c1d03060500c521200b20201c1d249040100f55080300340800d41c041001022402c091160a00041a06108001e054100320b9030a501260522006010b4524084907805282c402d1640696000103a40c080c031200e001c01420728900d0740301b40001140500b94841c0d4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 354031834 1250 354030584 354030617
    0x705130e0a020103090302030c011a040c1b0f02030304030f030c05060a0507020c190807060504090b09060612190f0f18020901030210051c020301081b0109060e01031506020a03 77
    0x140303041110310400038803484400d54015405010b00d02801d13015804117103c03a003000c11742800340e13000e203154460030b640079501d8241c200021651840000002c020700e41540020700360b12003c801c855981c0200f10116458181d20000e490341c49103420013080d01c00c001c98180100b503000101512040e2140301a101190368140c010401c5174011103103400143d0050069030318500385a1152014581b04100142c00305451b40c666034a0103420364408070010303000190070443c2c08018420031180e042c003114280e400d81421000901c060040c5611340d0a581d216402040d6001c1103400c0054818154102c1484074000317042054008229a034000714005040000013800c8010350054001082c0e0b000b004040b040c3d0840c0c084c4003c0980d0500c11074117000040250710171152400100c490b6550380f0039005030b80e070360611000505018450040701c0b01110003021101c880c5e82c103e40e020040d0780703003407a1055403081c0c074000407405000740410f0998200815900071602c190302040003c2c0b0b4a01907104d100710344031a0301c1d2 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 354033084 1250 354031834 354031841
    0x609141801050402061b0a0b010806181605101e1d03030306090a050403090b1207030e06060d1101020a020d0b010608061903080901171e09070f1a04080f070513 70
    0x5000350300c150300304800c6c40c00ca882886280001d020901c1100c15600e9940e81d440924030007030b04054210b40c420030402c112458104e07a00d85a18941c1d1014000400340b00001c5080405e0034042c0ca0b01c5280807000304905a072203058419407440f180c2d901200d40400c600e1000d000200454031811100c0d20000b00500c060400100300c074000e450150a001282e904c51082900803d40070b8000c404010045100240d1400c015020f4141d02000320116015030416980c0a0100c1e288841070b0080b0741c0241040110b2681e5200300e0500e620b811409501c506225140102c4c1426800c00c4025030040d808443c002c03e11100c4000181a2082a1174103011074459104000c800b4210b500007031001400140b00f0700009103540046c10200406040c43d0003984140341d0409041b0604840c0c1e440d171889648044181ca420b600152508060410043c001240c28401404850308980c05012200c135007042d180040841600b04603401001c03110300799500081071480302c0f41c0383c08092048034403550585103c1042c5210074072 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 354034334 1250 354033084 354033091
    0x30f01020a050301050d1103030d0608060f13020d420504080406140f040306050411060f070b0903040807170606040c0f03050601030b09010609090f0515011101060914180105 76
    0x202c940f42168641400c110400d0707615441190317032950b6544403085586081018218194591901040007030400d02d000c1c0c0703801ca0080400e030240000c8000d002c0c0525802c8150114140c065524a0420300941000e1200300f14181e04100d42d007100b507103c8503100d417480d95521084d010a1101e200007007a50561301041e59000e44001d8150350b0304120800c400c5001e54400945035010300003403400c0034040d1198005075000ba40c400e076502038840e002c110821180003041038415408440703d60800384100241000343c05181c9006000c0c104440104000c1c120420503900107000329011034070415120950403260a140d40451441d43c0301c0c40300480c2480c40c06000d0b4040508483d6100301180da03014604501500380074107042e040c0b41d564044048603403a000362282c0a0812a1203c1021030f207420300700400c41d1010f0345c8201003145010b051001e1070703000c0001c918101c034091a01403151b80d601703641c2900424580d80030629451a00c006601c02c1206488028420008400c1c1c990b1210312540c0f5407800c3e0748044 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 354035584 1250 354034334 354034337
    0xc030c09011e0b0703050901080915190b030109030507031706060d051321091a0a030221040605060109080319030203100504061e0b07031707030b030a030c02030f01020a 74
    0x14010310031003548186501607200d1504100000035643c1c514540d0551102c1419000150000383d215800c0d608040c005411107a86401032904c106550100b8840082c0034000d000380302072401400031000704980001c0e081e044001c0003013000000c91700d000741407544026800c5000c03803a501d4031800d05411000200c0e10500011b0001071411060798800c2c8002d003001041e641c420550112200040f03040e00c01c222100002403815104006910480500200c5642c0c2c0711b11203801d801150401203031800c0d000d94003040d0352410056110301041e4007540a2a8680d103060f003201c110b0b041000180b11180d008a0301545003a01d40d40440f030303114081140c480c8503c001c0c0c010b11308804600d003500c0c64031039401181d010549041c00d041080c0c8650001e401e55105030b01544400c8140760348181c1c103180c0d181050000340b1188103040d01c1d0005564000d02024550188040c480840300c0018142a01a4018407120790006040d1744501d882858044c044401210003a8068071810710a04160b9005108442040341c19 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 354036834 1250 354035584 354035599
    0xd0603020f100509090406090b1009180c031104060e04111e091612140108070b0c060c07230327031905010603081317010b091f0e0112050c030c 63
    0x101c405000e80005c0c058422035040c3c1e03442407404041003090f184903000350180042400321524000b454819980030828600402c41000f05460004049511600c00ca035404200881c032520004006001007905034405825240d9003020881000162030f0810200c00c1c003201c02100100214020410394001340c810b441d001030740100400d05040c08841c0c18003c14540749000e088401418924a058844c0f41001120401e180e80052119403414045030014000c0b00301d06c00d04100c0c0c3c01c10f48580d01c0c43c0113415540080400600e501c1400541d526003104180007407142c40e25003200d10307022652070384007031101042154805140d45584442c580e4000484400900400702ca68060034148031055600c141150a590f0f1600000002450080030f00381210f4061000d0400134030300204500300078410451404180d02d0b000d50090103540e80011560003150031140c0c103180f000410070382c42982686801280c02c20f20032000020b070313200740e00803807200907440742c0c0c20343c0c000b0600b2200b40342d500c13903c2ca510319501c01c08 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 354038084 1250 354036834 354036847
    0x406021507051623031303020f0d0309170f0d120c08040507060f0c020405010e0708091c0305061c08090a2c072304050a15090612110d0603020f1005 65
    0x2081c5640908413070001c001c8003e0100720000c0310720310760000d0071900d030121a05d0820015441c141c0454210b091054440001380f20702950014450107590043c02070b20114910b0b210290301040041000d00d21408080325080400e4010240c41c2c4413141564128031818181d15030344691050f079400d40200c0d4000018207445007814400e4a110000900e54010402c00c06032100161381c56000f400d00801003142040940c2c01c04c00c0c00202041e80c02812085c1a81c8035842c61f02501e0310640e0f036000d171420302e8070340000c0a86400c0b0001c3c030144044001042400900c500070420321080c0802411815400c65030380ca1802d94400a030320079041c201303252440e4100c94203007032110b11018801150b0300c140305140c040f01c10b810322401d01d081d80c00410050030400c803003c20144664181855900090250755501002421210100a081183e5401031008102044c84d103204c100d0459000349900070f442c02551501d8183c1c2c0f904c0e000c01414107202c00c2c0c1c4140d0411510903a01c2c102115112407036a000e40d0703038521300032 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 354039334 1250 354038084 354038093
    0x402090109091109060f0a091d040605070905090f0609180307081b030408070801110405030d39021f17041b0303030506010e09010f0519090204060215070516 69
    0x2040c2c0d8942040c0c15801c1190544d81e6441100074480031074828840c68541045200007403018000e504551618154409640200c001c0505d00503030080d40114045103d5880b01c4003164160200c2e440f05403c440c10206121480c0c886208051050b2016281540b2a641d0b5104103801c81c00c03590b040c05055081000280b01060041000300300c00700d0702020700c0c600340221f08001c1e45158070542c4403040f0b42d04514424040002c00307025640000c2d9000031003504150800e00041e80314003e407900901400402d07101c090041c00d10300040290070300444400e4820740c500706d0100d90541003030402244500841403050042c6c0e40c2d0500300c10b0008006549074558044030300100b4250000107001550315142e440401c2010180311031004001d50702c60740c0d000ca11070420f000052b00c007100310080c51340702e01d985900511964401a5000084540032502240c00c4020488455811030343d075000344000d24000140491603030b8000405d07540c400ea480034a1111a500e0070b0b01260140507480904402c88032001c0c08a0104 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 354040584 1250 354039334 354039341
    0x40506060a0b0f130b0c0a05010b2409030114070f02070e070e0910030501020301060c030e1503060f06070204060602030a090602010b13020f0c070e01051302040b072307080601090b040209010909 85
    0x82509407481c60304e0f075142e034140380181d0032501d10740c25542d2103c0241c40801c14280031320441e481c41a0380c0505110440725503001e05580b980c480c1c070304003cae0100e0909a03540e82500b02c0010701e030303809a04600d03e040002c80101004000d00707c1e100544074403500044c6c01c610300480c0610a07055070340c1c0c107144501500c080110415014144082d41050a40b0100100e1000c3c03008500a24031703a110081480100d282c05048010380814262080003408000e4040c4415001100ea1000301201c1004000d448000040c005002d1604060b4000d45440d4000c41d500d90000000e210120154484003125135a8040c102d003610741103100c0b00d40000d550b85044240ca0401d8020b0404000c1c201142070400c5e50200d4400d14180a65000c0036200c0c2c480e40040140c0d00382100110828600c440e015443d090520489200b94030500070010090100e05d518101c1481c6040d0140c01d40681d19425260700795946c804241e40c690080c010281d41a241141040da00c2c545882151204401a1283c00c0070f149400140c5004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 354041834 1250 354040584 354040597
    0x304030f080c060a271104180c0e01050301052401140417010f0e120f03060d0b0103050303060f010306030f151d0a1221180b0906040506060a0b0f 64
    0x8040140010b400c0b4100521109101e424000000903001000c04621441240005640c03400c1c1c1c1e02000109001c82c026904140410000790b401203900c0805ca03141e00100d41e05080050181d14840201081a41811030b00324100c81044000340700903282c400081c800000510410aa50048240c10030391179401a0f080030000c0d01e601070043d0400d960380e04007589600705901104141d0b55948108400c4946900c11519a40014002402040d484500412280c811401c1801082c0070100014000740c0c1c3c1c2d0850a41171540c008101081543d403450195904d40068417554410b400d400311070861f55100e4851203088a0b00842200a0040c0c151290154500d0707402d10426869180c0c808036808144c80b07000e400300c41200e0350041a0118640c00c20502440318112a0700c200a200768884100581e46400c415000104071000034050111045815480c00d416500038a816040400c1280d030400200d07904d8070413405001603c003280d079064204012807009000d05c0f000d148090155522004031100940324 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 354043084 1250 354041834 354041843
    0xf04030c0f1b0b03010b0a03020d020d1803110109022803060c0e04050a020f0301061107050307060c050607030c3905010c020708030a0e010e06090910090e0f0304030f 73
    0x51030503403078840034100c89114805549041c009041240034020b6000200001c25480903214255410205224034500c00c0105c090b0415401185e80845014194100c50744100a4ac8080191204103070b07620400900f00c00040e40426003050103541d81c40010b00811002d9980200030005903d070900007078804c039003030000c5031048010f102c8001c00044c0c03040c42443c0810301c0f0790311950001c03c0440c041206403580101610a0540140130041c00d018407001a64103480d86410f00714200303640c1c85a90340c9408202d80c4034540c5441a0a400150190480082c426444c00b95003a1a4076070364101d0b090b0150785000440800141703000882082c0380e0071100d03001440480200500141166054074075039034031001c0000391100c4e55205000f100c80c54040011000501d101742c0510b0602d03a482c04094000d0b2302c0300c55000c0c14044040060b40c90f40e0ba402d01214034620b40145000c1250070804a00000d649c842c0c060110380a19261481c00e140710001400c008101a450085252505642c5c608245044000c1d0868 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 354044334 1250 354043084 354043097
    0x3030507030906050705190c17071a0c130905060d0204020c01021606021308160b0a110616030c050906030a090f020d0809031b030d11030c01110c070902030f0f0403 72
    0x14001110707130140c9402009540c2ea0540c540c194800020301d0f40c440c8650240038013030b040344074a00280c009000920071480080415440340d0341818104480c0f080220600f0160343c0700020403070403072803081c080e05020a540d0448051907842d29040d20880e05c080e51040d90185c044270540e00145026001000000780490000d41401c94516a01610a400e14000c0750760b0784e008141d0a20450499074607000508592000707001c41c182c2494504800501ca001c0c2c0340803228001014041140118070440b0f100240008594052070031051801d48071240b040c14000090400c0c680e14034040c403550607a14045c4000300303240d00c0c2d17881c1d600781d6500519101c40d00300e400403809803e00b405039071985503045841c0e000e4442d407035032011a20201814440e070280e0f003162840d001000c1a0039a00c0002d11030040100e58100080c071000c0d905860342c910300540802264941c01c0140007074042002501400201c040142190480c1e0740f90390101c0280c2c04210f884031101d40d001800516170051440d41c4030b400500905290 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 354045584 1250 354044334 354044351
    0x60a0509100c0e040f0603030c0b1e07020303060909030301060f210501030f05060a0501180b04150906180203160804082214120705040e1f0b190b03040303050703 71
    0xd541c0d014400300c0100f100444410900d003000c1c0191100300d0341c1d4620401c5001c1c155a000342c20648070350b00240c90754503480002584504105107030040c04064034100d0880d460007402c02940ca90088440c0c5000305000000b00d031001d000007040e42d05881c1075480741000207500710070456072152094041d5981c1090399290ba0860610b40c440d683c00f85000e045502c0f0213030300d281041c0c0d190100140a00901d039240400400085052004080008030000c02c0801c0c44c0c0f00600c00580078080b006182c00365041a460006044d03010746e400802182e03c04e500241d4126000400c040c02c80c081203600c3c1c800703561308480c2ca020082c401d01425074850701ca00c0ca054101800d600c03030710006202000d10b61300503a0f8a480c040c404610880c0d60304100341012034441704800344441c80300782c85900318400c0034091038481203025007074203040c050304070b003032058480c414541e0302150032850291011401503405420071400102a83c00200c2174901a02c250041c064034548841d81c1c01c07001000024084c0b41055541d0840307 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 354046834 1250 354045584 354045613
    0x50703060e0c03070f03020f06030a09060f0203061008130f05030d020a1d0402161104110f040e010b0403050a030806041b0903060506041503061a030303130308010b0309060a0509 78
    0x312881040307440000c0000041d030805043c80c00d005a0803824102e4800501000141e446541c4201d804a040d9001e035103a40360b402600014040e1024005c00301410b0174603c100c803503001d6010794400c2000300e46401e2403158618081d41d0b00b140540d9810b03520031441c28124081444407800b5102180325008a03071030b241c1c042a00c4403c03030b0040680c010005075001980703d00320800c5144a8450b10301205c00f1841c100d240c84c440700581c40d010400030324a0000c0b441480050b40e59900031344000154005882c1d0b91900001145526403103802212034085102001041c0c1400c48001e8400b541d170b1003401005062103036241660195001891a030703002d610360025a00d405940c6d220f1500f44c2c04141c4801020a0462600c1426110300502280c0120724010102c807008603040001011a034001500007400311400e84c48840c8501d200f260541c25105c00400c2c020f211b071060a44400440c000d42d07491035140d8a48842c0d05c485d10058035000350136030054002c114403070060750101d508140c02c003048881c064042d800 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 354048084 1250 354046834 354046841
    0x1e0306060f1912022706040e070b210a0605033f03090d0f020d0c05070302040908030708090607050702120f120c0106051c1709190302120615060705070306 68
    0x881c141040d070a00143c11030030300e8110744060700c0b0240403901d080085e54058809a84004213407500c6142c03200320000c40d5400621821020300340c0c2191050f0b9480c40700c034001d00803000300e10500d040c00105400003902210603100d1f06055600040103071180800d0038801158400c0c0b1000d940100c0c94001100c0c400b50480c2241e407414060400503815140d1410003401400c0010144a60341032162400b45800e9183d80405c065500c00000d08102c0d1940302d10b4103003a450a01079400080d00507141801c50030078402c171200510312130324466507810180e94030030344090340ba07107000ea488902040d824070941006141c0040796401d850450000c460707901c0001e5880301d14040c1d08079640045014001001070030310b0700c2070003904041c1602391000104580603115001d030901e000b040180103200d01c855410381c4a07903d441150043c010080c000e410703101d124841050034051500c81280b244044040c0301200d000049141c510030035503d050790141e03e81031000e000c119070010004030f440d40114880403000404620 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 354049334 1250 354048084 354048089
    0x1d0403180e190c020a050606060c030c01111309060b070206280e040c05030405070b030c0d0204320a0504020f160f0210090e0601030c1b111e0306060f19 67
    0x5080c985007040124600031a1500345604003150085d05982004c91400160140c1220b019a5255502c1865070542421130181022100355035080109444050712020041d0014000000e50500d01c01e584e41c1c40c0d5001c88207244a07006034a0001d0202002618149001d00403116071020307608556035085841000207001d210100010500b5008282ca1508252140c00744411141c10901e2540c2043e0b147c0f150b40ea0040d02c20b074105504008001104000d4a0b01076940f100e40d806c1e0255266500c80280c41d10000790503100d4148031200f14010124101006034200251001602084101f800d000034000a13600007140180e0143c020030107028031168003001c070b284490080400c1440007003580304100e0041180d1012204100d44000c0070301501c1443e1140030307084002400c00080c06440208192454502d800c900324030010003131744000511080f180a10252001165040318081d24010740144c54a4004600394155010400080c004d0420441185c00400c1c0113084c01d031451030100d03604684bd800794 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 354050584 1250 354049334 354049351
    0x90a03020a17061e13141f2003131403030103030207030b0a0207240222090f0c020601120302100f020d110f090d0c120302030408010e03090d080a23131d0403180e 71
    0x95a09030003014440c0a1020061000e10508d641000008003131500000c1d10000c018280a201d00040022030541c8060703044402c02034989070f40c1d6904010752500401d102c1901e410070040c001a000c01c010b0f02c02c03511002c0d4071044072000d50904035000044400004c6c9404426603003000001c05052030304420000d0b0450b440e1002d80c103642800034560985985403402000d05007824401c21006070085180c6054540c940e10b264500e6000342402c91804030f0505c1803500c03044c81e0295a145d00e00c0e1030b400411079001c081e8001c0c4206102c60640c0c01c0f141c45240186030301400e0600811280340f0746183d8010304113014070741c8004e006031902983c0d01c0358030304024100c000d40d01c005002c10081000b802030009094a410245003004c1112001c215081c0078a40b000f0b03c040400a50700c00030f140110900355100d080d0490518010b420001765100651256500c2c45881c030303070008006032200f600400100c11510300007680e10907880d10765059070f84240c1600d10588250342c010010410401c90f2103800d104a003c3e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 354051834 1250 354050584 354050623
    0x605181605010212030f0f0c0706020a09030209090a02060301090c140406050a12090b0621010e010e19050705010818010f0501061403040b0705090a03020a17061e1314 73
    0x80c207002900d03220300020b40441d010814001c1010f090040c1412590140241004401544d181000969584104040100000d00c080b03905200c3c4c03580611190141d0388207581b00d6043d40c41e545070150361540c2c80c1c4002988810100014042400c20790030080c2540011705194800230521034030309040d80c01581180001070808501500c0c801d0f480b0348c0302e2181d07401c196020000c420880c5c558070311280b03005201900603400111004c22003410398030303541480079210000700f007510070440c5403074040e21401311001c09a219607d54040a65101d03000d5403009036101004001d114034120054a07002402045120320309401c880c5540900000e0084505003403c100e00010190b0406401900b8030048a5107005402c60078810031000400408405070428002e00303100381c407603032034400003400103c440d01300030340102c03040ca4001582d4000501010000300c10806440785580e80884007100f80348106459440360080c035021508a00004280c0c8602c00d00a00c402c000101c5e60550241c50300c40c1c0303000604002d420 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 354053084 1250 354051834 354051839
    0x1b0804030819051303032a0f11060f030f04080906030703060f060507050309010c060f06060306080f0d080103030e0103090b130317010f03111c0516060c0c0306051816 73
    0x400c01000d01104142d4284181800741100058180303004500000742407240f0311858946140d00c3c41b01600b121141c200343c0d02d40302d4000d403070704005862012008640c00c003501001c0b200549003c500351030611aa62000074110359440c03030b48051400018100b624180070803c490042a103508000314442d040580300815558079210805010780c0c506c1d40f014007004801d102c0e241c005600030046950b0b1040034070703209190030040d041181c000c00e0b07501410a0000d1402c1b00005407950550005011a16402c2c1664000c0a142801e03640b00c01c000c8130314000060200c00117000080c024000c28640318018900003079011416551041e400c0010b5890301d4242042e190104101640060707840c0042002422403182c80d49054004246000d01e8080142800f074819081081d94440c00410100343c0c8048410b0460555a414810307100c04c1d9003604a000300c03441260100d10b40307009442c800e14480c0d100c210961030f10314688809008040c003501d804c55611640d00c203550401400c114a04080503100114006c3d80e1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 354054334 1250 354053084 354053107
    0xf030109030c0507050a0302060301030b190c0c02030c06180108041505010e150109260102122a0f04060c03020115080f010f0513020121110918090d1b08040308 70
    0x100c44d548100d2017002007080500040c3c4544042c0c1303044a500580c0100151030701580c070a1b68850b0301800f02e00c5036241c280c034480036981c800b240800c564000e5040e110254692024044203104411900340d00c0035804418161075440384102e5a442805030340726440d0a054004104141d03502a03001c2900280e05006110100d11801007203411380d40242404220341746800f40610000000050200c14280341e41508003d070b04082d01100d00c50040820796145a00d403000060090720b88250300340c000a0740010103d00e003107503541e045036a4040300c056550306251804c2c00458410559400403800c44d500c902400114248844032140501504000740c01805034841e45542102d941032035406a25062005100000f402203a4003015140c0a280000c207034807011130060101151700003840e20491603c040c41c21107000d010050803072540c04031142e04800700c680700a41243c460903600c0c251315400032101e0a4000340944103815007403080381d00585180c2c1441d2981401d039005944113071200c01e40002e610b610f21 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 354055584 1250 354054334 354054343
    0xf0c0809011803030b060403050111030a0b0d030c06150914011401051206060a05070b090f0709050405032b1a1009080303280e100e0d05180f030109030c05 68
    0x120a000003004214040103510b81c0306003007010b0140a05a031404010541e8032600211405107070458001e2006000c1c408001c1d4031a842103825004039840c000c52900e05d80340125801d00303942c0c0c0542d1045550501500c64038028411484080704d04034094000140714009401100c80c00706034a1440d82603036140103400360308260b482c3c1c0807074100002000011032440a07256825009001540c000d600d0348000300c030070355080c86500e80252510144004200d403c47c0001000500e601e1001c0c181d440190340d6048000c141c41c1c044d100202140c1091154203280b400ca56141e5aa00742e00540d07125101d20035956900131150922100c51518001042c000307903a080604860b00700c82014504000d0a80c688040182c8030300014003140f050783ca0a021b00c1c0c40c090780d40581040c0d2210140410001c402c040070989690340841c0381102c84407410070900080a140c0800e01442c0c0300c0307031070701c80518180d40368840f2030500140107481507000040c502400c0b81510244941d039141842030b122a050780ca454100f183c0750 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 354056834 1250 354055584 354055591
    0x90f03080a050c04210f023d0906030207033b06030708061c020415030303050f060f040b060d060329070c06050a0902190f080304030c060e01050d0f0c08 67
    0xc0100420412003031610075810740422249400a0f180e030403440c0440100406e00c2019510a0441e17203184507100400740003a103284074004003200c60245400c0401080c0d035070120004085108083c040060502a030028640070b4400c0c980070300910301c802948290001c06074003210151214444841030705494030816504032a04580907810b614104500401e80e540c0103141c1d500544e07040404801c0c5280744400140310b0b0354020024400d04040d42d0320540801043d00c81500040e003010049840c3c0c8054500490140c5000b0300680c001f40040300c00e00018003c1511216003004041180301418002c030710800e00a14450713545103106142c0d0510380501c034140c108910714000600c1081c44401600120700d5070503036074802d002180d0fa990b00600a4001c3c04d00c80806074005628043c158250407000002005468a4250410302140c54a000543d01d0095010040c42000381100500415008204604107010145801d0b482c051184086a05603000c00c8010388000b81c451405075611f54005510650 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 354058084 1250 354056834 354056851
    0x10606021e07050f010c050d050a03111e0a090f080c10081009090807050d020a050d0c0b060d060b130c03050f040f2003010e03120903030412030c03090f03080a05 71
    0xd400004403034260b00c0c1d400030b228051080b0b0100000240d0399000d58114034030070390000c0c2038507414104603002034010780c020706107040003e19244c1c5c5c811001c1a00420f03960240042c055024138540c03400164030071a803000103080300b40801c204000031512801d08000000e00300e140701510988803400300b17001e0034401001803281400015410802600491034000c42215010540030500ca015801d00c41d40d2440784e810043c0a5001c0c0c2c4200051158000035511440782c80f51041300c00410030010f00711081458804000c2c143c8a1803004101d181c80c081c00980d810340c1c01020005681144000014500009182d0000805850724a90180142c151160395880007010200c91060310b003a40d114079400c0c444078001001d000340c4800041210000f00c03034103001c08001a001704031090205842c942d59400414400780f1900e8070b031002600710030300841034070700a41c1d0040c00010902142e1038140c01030500c455841c010150b81b5042103020880301e0440081071800781e1951200c600f04010201c0c1030f184000c020300c1c0d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 354059334 1250 354058084 354058123
    0x9040204090b03101b050901031d1e030a020703170c15041403090603010519050402040b0702040b030a0b070f170406140a0b1c0303020f070804080709092006070203010e01060602 78
    0xc400007414a8071145c9051510b0b00341d13511400c110058000b403001c662020302c03545129080103944000020000c0039082c000d0a01852504501442941d80c800c5540000060f04015810000507008a4012890381d40000c6c2c1142007096040390245408002d405c403490480e50f580602c414031401c95404220042d070240074514000802010880c1d905c01031103410b01581c41500c1d000080740741009280b0180400030025540c55070303241034485441c3c002c854180c2c03041d4a03001117000c40346070009900d048075600070041c68050b901e188081d664100120001418081c06600e4118040350b5001c045201364030480300080c160340350036a0041082402081003941624107000c424103036588150b42040003c3c42010050040c1003454101c010340540b4006030582800461014100a030700c0001d003050b00e15101c00c8940c0542d58404a60a0340da0a40014080151079043d00d00170030303110402c1b1190b204001d89428a01121603000c03900311a60107600c825144d43d50394040c090244d0611890503500340c0b000451 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 354060584 1250 354059334 354059351
    0x307030c140a0f0c0501140711011113092706090b01050906010207150215040c1502060f010302191805012d14150403030e010f0c1e02030309040204090b0310 69
    0x141c81c100d50410a2400d00c000c901504d0200300d001d40058400b45c4100103000a80d06050101800c0580c0e8610ba501443d400d02c40d4041e20340c51843c050301c1c42d401440210307100300780c0381c440c4c0d020040c242c1625283e620050301c3c2903070581e29031801e8200d0b00180301e0b440000c0c4040d41404c1280c40000c06800c100c0c1301e0342000c411301c88103a034009882d03400ea0319010400d16001e00860002e0380303003003040c0e80700c04100305400c0c1c10403050101544031a02203404d900d050802c400400300c0e0490311410119404004a0b005000501c05030401c0c102c00c4003201c2c24010f048003020345904407030654110b600300103006d00b0b446900521a43d40d00b904e0751580c11104c07a58804c4401c00105403c1d0707000d0080d00803a00020186000b081050307580140c5800300c031024884081c0d5540c0c4905009001c848841c512a001c2200440c2020b4500d00c51400c5082c0c44ad04018003c0c01440d680c4642c02024a82d00c0e000da900d484203100081c0242d03550700c001e1004140c650b00c0010381030b2030070041c0b40c140301900500701e48052810071034 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 354061834 1250 354060584 354060587
    0xa1a01030b161e0513080c150a090302040f0516020706020307060f0b10020601090606020a1e050a060501120b09030a02030a18030f1113061a0f04030204020307030c140a 74
    0x5036504071a050550641c04618040101c500804290400903402d811603410100e040d08200280031503180100d284000b50f032240b0003d0350710035487c3d1945030040500070000041102c0000a0000c0102518140c1c070080d6494002a05849481c1c0300d80e115a42d840d81805200000c00099500411060015010061610b00007039100e00034018040c01541d1a01ca183d1050a4158400d5141010090008203c0c840c0c81000940d02c480034018042481c0c901f0b84007241240c0001008c4070580d60204091541802d020060900846c80e070b042110309100c0c0150080001d0039a0040b140030300140c1d0104d21a17a80a0305019800180140c2000b105401c10042c90a0700c59010084a8210020b070a00700c1c181804400850300029684c0e0000d00318140d481404d00030084641c0c0c10001d4010704079185120554104101c00c225042c910031310110500621911120480880190840c1d40f07000700501d0a2558a8010070180d078005c0303400000007540c660481001c680c01480d541181c0f207291300c425050481c0b5000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 354063084 1250 354061834 354061853
    0x610020a020a060c0206090a03030c032607030e010e10022d04050405040302031204030e10051201170304030c08010504051908040e0604020c0a061e1a040504020613080a1a0103 77
    0x2da482000040715840045d9101da80854806d1003004e0b20320010f6566a09006016094030704003200011000340251811204500d942c109011a40a0201b010385503184194020440a50307102200c0d500c3c1c0080100c081010300c014401883d4424001d82e0320340b0b8010710032060407500001c00698034560251090340c0b00e14102603406446c8260340000342a03c6034141a459400360b0090204032400744e80c00c20080552007445a20740680680703c69480c11104c540545490086000740c1d01c0009c2e035040100607004000e440b8a842c0e688840580340f400d51203807035060814103150071020140e91200b013030000300a8100300d281500d4402d140c091180d00c41544c3c402416100780c0c806d0300e0340c00310345002188441d0740e507030704036003080380d241c0102d80301d4480c58540b000c00703080c0803ca44c044400d804c008206c40c0c1607841c0148440100c04a02030340d69402c2c80010040204405441039800400234081c2825181100321400c0242c02c084c0c005280b20325891508410041040d0700c2e079008a61503200400010f8580007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 354064334 1250 354063084 354063089
    0x1d0a060b0c0a11030f060a061503050105010e010806150a050c060708130b0c0427050609090a140c06030f0906060d030f030903111606030e010e0703030f11030a080610020a020a 77
    0x2080100f5540d6803c00a0319009036890811614040c010030301c0b8000d050b60384003a040307a094202441c4411141c03801135007252401d20603a130100c1d49444100c2e61940c0726202140d4440341c001e0a500e150b40700410074075010340011039079102140300010310034038070201007041c0c0b50700442074605140319150408681c0b040321003c0d000101940050008503045040c00c00545000e01215184584010143c601d010b0700124982c1140480d00e18050220b541814a015050303ca0b6461a0092298250580d201b0300c2d0480e1109848e072013401501d01c01c41e5940d03620f800a5015140c081c0ba49401400c03c4101c05080010240c0041c0c0300303d942c1d00083d000031390456045c54000740c490a001a051242d400c1c11b803468440809400c0c0d85000d9075480c0b0303034017000318040c0c00c00761041a90100b00e000042c00f401030885a0071060890607901040c1c0800000e1f00c114404844000d09180c84001c0003000d600480c80c5030001030800000c0b90b01c8074208070140c20009522660040240b004001424203034006c81d42c40541c60 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 354065584 1250 354064334 354064343
    0x605030a0b0702030d02030c090f01030b011e052205090c040807030b060f031015050402031b0a120513120201150b0a0e06030c0d0501080304210c1d0a060b0c0a 70
    0x1c0004195900910035a1a42d014404007556a07181001d0072407031070b078041c0b500584115039a02404210354824895950302c400182c451030101c40d03a00007500c80c0c481e84c020742c4000300301040250711000514140340e1484441407407079003902c031805c000402052040080c00c5800c551403d02c0100200e400c00649402229045036142d2095201c141c04614210300c0700c00034076010300c03911030f00010811245d8850ba07594070048554030805500e460400042c1d01c030584051004031090240302a100b6500d0000381181d481ca0304200c1c0c0e0b4194030800c4101561011180b0ba541d13080c00d40008000d1040b00c0c2042c0208031150f1008005050010425541064041c001c3c080800030208609000074060107082c01c83c0080100500c1d100d180c0301d01c0c20750180c0d00c10902440800d060000000380d2800010540d01900c95491045140140300d41400700c11402c06102680c1d010514480080d60949407000d00c0c641c02a402c014030958540544c00d0750660f21540c0c031080e0319600c1080042083d10022940002c000da21 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 354066834 1250 354065584 354065603
    0x120c031903111204060612051002090303130b030406050a020a0f18050604030b060a060302130e04080d060b12070f020705150f0a020706030c030c080a20030106110606040605030a 78
    0x406004a00400da600700580700d4182c0040d00303075540c0c1040700318039109511414060165589895200100012460340141254042d080c4094003400c80d8001e010510400750403207040c1842c8401d5000076460982c82480341000c000300744018040c041c082c0c1a0b204402038020b62800d1040031008080440800b50035082150318405103000e04191141da10082000403c80ea803102d88a00308852448070545c0d1a92007041f042500048140c0070740203558450040c02c2e41c07a001c1c03528244040c02204401042140c81c078400300301c6036200100070301c07540c0054010406502d4440b910382560710b0140e540501801b080c040c0400401200f00d0b030028000054850541e2018050040048005400d000d801e0645505030700100e17100000c25030001d03412003180d045550034019140c2141040d02243c00b0300790100001081c2c01300003156950300381c00c8500d00b1010001c405498000501110440b44c1080c2c10403c0054800d003000400b0741e4007081900c1e000759040728104100391801c400295100c001c031200800100300f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 354068084 1250 354066834 354066877
    0x30812060a0e10090e06040302030403080d0603021003060617090d030f1103150102070f0e07050a0e040f06051311030a0902191e140a05010509220e120c03 68
    0xc03001d044000030000b8202800302800c02d4141e4a0328064a8080c000800e45000ba20044110001548601a0307030140c000d1407403c0d00f991909021640f05070305280f0103a0301e90000100503260300003840d441010903900060b1950500302c0040903104040742110034080e600043c050182c0340410440901c18081c1000200040c405c0034440c00f400000b80002d004160100c00c003d000c907549004210207840c00d03402c0d5113026485440000381c80c1c034940a095241030f0340701d0000b4000c41c001c000400383c400540c24404000f24107800014155810b14810703280c099114002040581003420310000031501212080c425061014040c040c10700005104054040c0c45501c0d02003503454140031840400c1d12440d07071502080e180d481c0b02c070006003400a03002110001c80e50004404d22441c0d020400140010704260342d25203040e0044503d82c00259085030f011010703101d4250440d104c2d4030441b121101000020510014428403641012488504401c0080003003100c100c41880110488180640d000030107042c410 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 354069334 1250 354068084 354068089
    0x300b0102120d09030206220b040201050c0a0c090c1b11010306030b0a0516050c0a021011010e061b031e040606030804120203010b10050f0705121b060a050103081206 72
    0x742507840c6508032100028681c4103240c2240c00504a4078000d400703e40403070301e41000d52101100c10400c224860718016584200080001000d103410500515102d800e2520044450b41048001e0404403070002d84000100320800344d03400703800c0c011303540c0d400c1032180b0180c00f00d003202901c01c001070000d005214855200107103038041d5000002031500130f40900030b80d103000c501600052609407400c00e0104071704103c0c0d0500c10303c00c204076040c0d144980098502c0301c030203500b403008010a4807823500a10038a142c1c0d12600308002d220f512942d0030704600a002d94145980c4851512a81400198417070004000f000b80010701f401c144180710f154640d1008483c4d45e2410903100515564000070891303000040c0000b01d14000d11190b4010b107008400810090784030344100b00343c900720480c503600850b030300380300c2036180c000c501c0d01420649020740242c0380b40032844c2c0030307400603640000d510680034041e081070300804c85010410740b0b40c0880308540400007035040d034a64082e14010b141c00d5140c00ea809500058058 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 354070584 1250 354069334 354069343
    0x32010180c030b15040603020a0308070213021909120309061103070209010306020405091312030b06190207180c12090812040c080c01020a0b070302160b010b0a300b0102 74
    0x2a000002075000030384070314008200020642c1d8200e904184c0c20600a5689418810181100d0b0f0040c00105c05070b1560307844080580001c041a41e00c983c0403540c5002d488280d0004101d140501803003680154069840580070b403003da0404d00c440e094800407040042d0b0030040200540c1d0282c1055403089500595240c80c44c800c01c41d000350802c00e144000010040303240c0180050b00c0b0200c0d0748098640e10f0702080940e030481404058085682c2e008038124140c0280d001205195020f040f0514110004096901100c80080c00a00607400810100042c035001c0e2252a1019071481c0d052001c252000760060041c1c03181c83c00030b80c185503600800750401c0301d080201c0365109202202d1300309514160402c1401c50119215040040c000c144a60805600c080788006241d50300481c120019207078490202c000750440c07002c900310811a4003003c804210542d5003d8002d02881e10026a21030511100510a214000b120389054043c03100b00e448503007076a103481d03c50390f203005400240c01d0701000040b883c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 354071834 1250 354070584 354070631
    0x60604110d09030503061309020f0f040b030a08070605160f1b050d020a11040603030504031b05090f0412080903091306050a060c0c080c13020a051b0a032010 69
    0x781440c0095440c20107400c4800703580700b02d07021a81916480c849501f034100f951b1001000942c00783c01c1d415850942d2428800d07202c2c0700d8201501c0094280b80303400c0401d2030202c00c1e04040d200641c1c003241020030402140216540080c1081e821500605145800b5100c00d401140d402d0501160a1078103010019400740c0e0f041c10742d0480200c0d030b603190154401035100d0f00c104d44c3c191520504034104d0701c0a41800c0c0501c90403281d250b0346d81403805146840d065400da030842d0b4042120581c6040000d03040c0d6494a200d402103445a24855940c10145445c2d02000c0601c0340190074400658104504c112011087c2c0d80c0d415004d554003c1d42c800e020010000400b003540100b44d006281030000f040b555030000e609080c40e8480c3c40691102c0b5194003032983d59000c1101c2d501d50145000354640a039440c540c0140000021506000e41003846104400704000d42d403503084031841c0c0c4105105024035038003e80310182c000c82e00200c03100e0100803458142e110b040c1c140e140d0700c1d1240c40e0030b003466096410380c011652 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 354073084 1250 354071834 354071857
    0x60f061d0607030e030c150409050a142e030b010b0714060108030c1218060a0e0301090305090301290d020f15030910050114090703140f090d030e06060411 68
    0x1a00d001c140350107021210380100c0382d4046c0c07040800d80c46107824144400201505522500d608080c0341c540940081c1c003008120301225500c8070b5843c00b40000312111755000d05a014004074203510100c05244038509804550880d02078043c604101055120094030b055901c5d881442c1d41c3c8445600b041108008850f08244c0d15211700c0e000010000300102c00340c0720344e0701124155000001180d407940759030302489004a1051100f1040318440385402002050b00d4802030a021001d00c0300c0c080080e00b1641508002d03400708030300080101c090b290a10844144d0741c0e0300c0100359000c5841c0c0441310706c03142d8000c0c02d00340207003122014002559554214041030380d00080c00c0d101100a418540001e98109a034101c0680c03040000400f020003c07801000c1c1a101844604c1071900e00c900100810540302402c01d000f0308d5500c50b0b90000d1241519500d0b881810004d0b01603a80d410320705240c9142c0040704100b203041600d0814803003507404000c40c0031034002d02e00719004a80e003404c0e4440002c15202e07050110700d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 354074334 1250 354073084 354073087
    0xa1205090108090d231b0c0f06031b21071e0f1706040212150109050d0b0f041106030403020c0109050301060308030f090c060c0c0102070510020a2d05010605040c03060f061d06 77
    0x4d6000800060f000d214100980712003d440070000c0c203101c09808241d4030361480781e02f0902d00c50601d80981d4003800030a10b1003080188044103000322026444400d80c0c64100148041c10a00304101484420343d80051051070001c020400c0d99100a01042c1104403c0c40c05810403808903041e03940740d80548245040c090f101c0318490901140c00c1030031181c0b1207043e602180d070b56800060075103010314251100c90742100c00c1030304603920b0310750010080c50010000c0317504040d402d100018a8445030082c510a6100750018281d5070b454000240100003036a010300d1082e81044800c0c000140c4800c1031300d03040b084802d6032811540b0341150083c00c0c04e0103d882c0c1600107401041e108059200000d501d00e600100b03030281c07001c90741c440040c440c1c1c144910b002003000d80d001c003030840f001403903094040b17000980e4600000c800741e070048a0600040030304038081c0e034941c1d1102014480c51900d886150044c05035801d00701710607460460007600000880c48be00b03003400f01c9000075501c41c0003d40e00051100b00300810740c9 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 354075584 1250 354074334 354074377
    0x41d0c27013e030c150702070e070c0606081f150803071b050609092a0c01090b0c03060307030f0302030403080f07060f1505040e0a1205090108090d23 66
    0x2030800020b0501071010501c0c0801000b03000ea030100c101c940700802070001e0448034a020340440d00f1007001502c224118070444200080030566040180d000d403d440d078030107a4200c2e6500701402582c0c4290040b05d026000340b000001890541c0700d40e10500500d80070301103003031400000d0784510884a80d10100141c000061003a080080c042d48400d0783e610b0340d50a5014582d180d40030b001c0030307024072904d4680009084001c1100b5100e600341c8082c0e07918450b4020005c00b06c54920314081c1750400744c1c0104090b912403000c802000000000c0b280d01c072220b0182c080c1540391000019a1b640e0103440080c100101455264051500c20f2045a0155800404003591081022101c1001c0d40c040e1205403410340c948cc040d641507011900400f5450400000418400e906200c01c100c000e1183d6201c0280c031b071003411082000112030500c6849a001c4513210b01c0e4842c501e00002600301a0001c1944a030358100c803000010741d5400c603c4c2181c511401e10b56405407100d6943e0900ca55102d1500807440e154002c800a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 354076834 1250 354075584 354075647
    0x1020d30060608090f01020310030b0a09020406080d02011a0906040e0f030708040303090e061e010306030605090a0b070903080a0e01050d0213083a020a08041d0c2701 73
    0x10140200065011551700014510a1600b01d000c01c2d40e0700c43c403480d507140c03003000400d00d1028a203400440e900c0c400101c082150340000c2c1240c1080d4080740640e004445500301c40c0f5020b2207070005601c01c3c40044208072800c0d0001940140d002400240710b0343d0307501e00c1c41814070f40400840340012003080c200d03135950103c0d0511202a811030710048001900c024800304605910a0290b800b038803020345000c01c00204015000b043c0c260640c40503040656540d0004042000360140f00e00603410200036284820082c03d008844c500300034560410300456180420029000e40e048844400462510800c01c440100040740c9a01c07a001140350120300100e40c14000031000d2000b03804590a4a040b0ba80482c403210300300900320441d81d8040e01d4443c0c0c000d81e004000c10300400d04110300045106852064846568500f00303a0056080130704001c510710304480003030b00c2c0740b03400b03582180c232a1800c642048910410001070210240080104031503030216940540d000740510703400441c040c60818401e0702130f420f4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 354078084 1250 354076834 354076847
    0x70c0302040e01020c06090f010f020a020d0f05160b01051201110f0a090302060f0a020d1404170309280e0609070e030a02100f1e09060f090f0905010504050601020d300606 75
    0x3c60230029440c2944070368035039013a8405c440c2c2c122029000341c140c8030103014059a194408110a10500c0405c010700c0c00e5030440c0060301004a8070504855080d541040705208601e544c080c0d629000fa850088800c1005110b00d00340ea00f030800c09618981d5401e080b441c112480101540f000f504624045480111000480b000d00103a8641c3e60071101042c000c0c41013191b5441c0e40480d50140800200030038004503980c5045041c006c6000030031a0711340ba00358004180c6400500680803e091800c0e200d20b10a4050b012018000f041c1d14500d000300e600304100040c194500290040c0244038aa11268606880c180b09400c149074006040c0c03888142108001b4111040b0712541c000059284080f5000042680400c500e1340441503513403100080c2002010788000000c00f0410040c860320315400520084144903010246c0204072020230703507515090502068440c090003160564109120f400a121341c03080d01450b410050444001c4c03070000c00780c00c0c0c4800010381c0700c04019040c1011808602181c0142 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 354079334 1250 354078084 354078103
    0x20030a06050601020c04090b190204050901030f05070602010218092e05240f09030708071d060d0b060103360b0115171905041b0b070c0302040e01020c0609 68
    0x800f45e484100c055800c0204a03446139000520700c0c08000003180b000d19140e030700030805100c00c4000600d0541c41c0d2000074074020013680102c907104801e090303050130480180003200c010146400203508010140e20500c1c601090004001d0140b22104005061a40720103695000e80ca03c204020541c1d0005c840816100707000d0340601c9014105480241108070b00c8040c07170b8408200000c896034245141000e0302c1090740d00c4008160360511505401098403601401040000d04110131204030000d11468002714000005002c031344510140c2010901181c1d01150f03180d80454240307000103a03c080055500f40b0300001c41070014070000c0303102d40080e01442c0600032800b03031380c051002c0032442d80c1d0f0345942d149a244031181c1d040000340880005d80702e844024020704c0c2c008100103009402d40c1c0c1c0010b4180100e070401c4400341e401521002194071070182d1408810080d20107800140d1516107262a0010038502c1440000e024a47c1e500b0301c0c4e1000c40c001e50650310f210104909441190902c000c40766510340560 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 354080584 1250 354079334 354079337
    0x150e0d081617040b030c0a0c05062d0105030a0f051e030702150f0a0f09030b0c030709050a080307110a17030c0c0f0a050121150602010e07030b0420030a06050601 71
    0x41e10b0b03001c4003640d168181c900b22442c0450b05461903990000d00c80341a0440710003c5c013444038800021001900901880d882000c0d514078290ba01d00100d6907581e100d401020701c020441403070300018410380c3c50200d006842c280d00700c2e50141a104441c5841407400382072818143e502004407045510140011009240440c0205c440304a05041030110b0f07040c501c01e041000e07034804410440303241050300032401170f078156016040c04441c0c29030300d0f107a030364040004581e500030806000041040b950b0b0010050005131500307460f4241c42c1030520603031580c0c1e44a8000090500c20340c0c050710644560381d040700000a4003200e8a009002400c201d80d043c1d030313a0441c0c0c10010190081500035001c48c2441426000c02c6200102030181052500c801955191905211a101c60b81142200441c00c002e600030500303038451181000500518020b0024211400200c0c14012a00800e03010008a100d500185402a41102100394506100a0300d40f1540f8228943c3c2a0940180100131050198550002d40310303240a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 354081834 1250 354080584 354080603
    0x90105010c2f09010f05220e0307110909070506030703020f041e0303090e040f03110109060c0807020c0102010204240908070b09040b030c0d030525050a050f0304150e0d0816 76
    0x20364117010301e032421700d004203030b004180d0b190300c844064a0100703100110010728000240b12003140d8400c0703040d0760000d00b003616500c00300b50884501d42040c484144c2d016070b2210181c101d0074104000107681e0711015000030100354021540350070401103842110300408102c18885900c40400c1d881d810144450710090b808242c00d03d100050084003039041c4d9202d03681c8103149840305500d5950035502682032031300d2203980e513590780c50300c10010b01c0c01d03c90701d148124151212800f6140100000346414581d40344e090459005100410074070103a21040e40c2ca202c25103010706400d01c650360342150707031b001d8a9100d000e01e440742c5100014605158030080265007016101413015003080030074140d4411602010341d80041c0f251800c180800e118401404161070322001070991040c0e200103100032031285141c161111b4100c000e80c4010828200301070071502c0d201d08040e41c03c1038605041e4400001110448c80f061080a401d004103503519150011912a40468159100c0602441c50305964402c184111608001c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 354083084 1250 354081834 354081839
    0x3040f090c020d0903080706090213141305060f04030c0506100602070605040305030316050912061501030603230111030f04031d1309020607060c0c06050601080105090105010c2f0901 80
    0x30100d08141124015100c40300a9461740c0e650762043d0380311020658070740ba9900170b0032006941d400e42348035489888100100703141c081d061503400000d0015000c050200d622010581c001480821340c254001480c80b030400300f640e12030500340d5070a0460b10b002030441c001c0d0010804900703088402d100941c3e64a9080740c002e542c41e808140d606103d540005002c0768001d0000449004101034108458a10703442c249050441c0e85c030114000c0384c01c1c0d03900c2c03035800c0e0410030410034540c1c1940c1c8041326a03030303003440c09000c10b503c1c51b200c100c03214400f45502d904d0160302c1da10401110a00350404016591010617040ea20310b01903803156000c40d0b00307031001c80003d0f009000450f132480c189241030721480340091040404100789071000005148401e0f007203802020510858000c200c1f45d100b03074074090000b6201c0c4400041d1030301d001c1044880082145040c80312010041c0040d480300ba0249055550a003002d42c41d0390303024280b000607106096007000300075040348007511500c400b00d044000c25880988400e00141d8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 354084334 1250 354083084 354083087
    0x307120b0a0506030a020903010609020a090305100203100e0408070c0e0f090d09050d21350c0f16030e01200d0c0c03150525021002130803040f090c 65
    0x7101071041542c08a020300104285018a07401000304ca1001000090010b80c1c5e9041c40082c0c0c0c001c030f4035000210301a101c080080c088140b000786000c200d01803046203075181c55450040078800600601c80200381003400602006061380440d03c00d2508024850401d070350300c28042c035148030129141010080420045100040c3c00a207008145940d0380322950030340c0c10300040c440d10a0121f01c00756001c64140c038100e071440540a06842c00c4014075078619400c146c040c2440280b10603d400c3c00a158035905070345902022602800da41c001501c0030907255120801d10703a9144a001e940c0040c01d80c05462018039081680051f402c5032001820780340c01c900490480850800d00080240c2d404580d04001f07007a015071ba1085020102062007444070b0840161a40c07150305000d83d22014540300703966607406002100c2414408041039030740c082080c140724510340d1402500e0701c0050000045003a0003080350b1a45501c030641a20103071a4078404c598507a80c2e1100c0389030090010344620590207242c00041451076 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 354085584 1250 354084334 354084349
    0x17030414010e0606100c0204020c0c010824010e1f0908060901150e071e2606240903150a050a090804060c03050d0e0102071407120f080f0307120b 64
    0xc0b50400301070a10b640e6903030188148078080d007028400304117200007024010f0382c0314406402c1d40079000c0010200011360200150124501070890280c0c90b8034402c401b200c030201940c80d03412064080c41c100c052945e041c0d0119824014034006c4484c400d1a104051600c144d220902c034080303803000d10844000c2e07101d410f107413800c0326070101040401000881040c0710952001d800d0035082211490010500403020644024942303481150702d00152451125050000e035140c0200c40440d58180b800c0c1041c205440080c1c040490805900d052071085000342211010b440165407501d04041c05444030240c44e0071180b20302d400c0c11540200e80d2890b0074046070403801c0900c01c3c95000b680c058a05490141000010b89201015040460401008100040c55001755001d41040d6481c00400582c40700300d10f150100410891071052081540007050401c541400d0184402c0d2030750300070b03000c54020f00040c01c04143c10300ca27002481106280000621034143e0b4070141c0280c2040b420102041605844010400503 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 354086834 1250 354085584 354085601
    0x91a090c09060f0405180709111902010e01060803090a0b0403030504180b0d0c0612140a1d0303040c051305070804230601030510060e0903071e1703041401 68
    0xa600c240061801801e040c0042900320400800c4618042c00da0340014050b104102d480c0fa1001190340201c41418004000304c030040d26030741c4018000401440c18801107400b41120942c00c08030710070009070130355000b90310420740b0800c0f443c000e100c8213490311011550395002c151124010281c540c03000604440c8542524140d941c143d80d00c501d098603041c40d6908558100d20a0820320303682c3c1c00d114155507101c64041c0c000e07078842c40c1b403950b08a02e806005000c884403084442485810710411380c40c0300e08060b40b490f43c0104502c80004203101d040d204c441105c00080e05103070305403000205001c14019150030601c1110b4085407900003641285418509540050b103907030003c56060004100041c681001d428415902c0040f02e110003a240300c89549000170030ba10076601500507000200e2911701c130703014ae1000f9084c032030300c0d2100a00340501c0300c80d5248100c060240201c0e454180440010000300e54600e45a2f4011250301c1c174407240407042102c0b60307200f554200c1d02c021003810b410000c0700042c05050301 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 354088084 1250 354086834 354086851
    0x90501090806040303050c0d14041103010203040218100801060801061707060c0204020318060a0903120c0c080c1606030b011d0607060f0623120609030316050904090501091a 76
    0x243c1c4996900b6005010064228016041c0a002d80510600d05210705803418190b070740c001c016410207007006142c0420503180540603900400800015032580319148600150500e418503140d50713040c05804010040360800d8840d0750a02da00020b04003015000441500e050560f0800340040341110350f84d480005124490209001c80581c101625141d406540c0c041e2041e15040f4002522040d801d0415500b01c0710040c01e196100701400c10701d9030200f0305c00c0800d50700500c01c00c1240c0c02820003400c04031500c4d030024500000007488845c04030f0244044140380340c20424000030591902d6000d009008a80e44141c0000e07a0002183c4800c00e010103420144031000d000c00f4901005519201d0240400c40030f02401141c99200c0003940d00f02820801000200c03264500040e01031200c1006080b035100d02c9411020391250302480b440c2c031004022030383c01040c00a814101c0c0480d080007a501030140100300c0354050300e050400c006124040d00190351451040701c0d041c0c05501084654010400c042d0307520308 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 354089334 1250 354088084 354088093
    0x1215090308070c02031e01020304140f0a0f0807060c08090115150e0f030601061d060c060705030406090507060903030e0d050706050c0109020409080c0f01020a0516031209120905010908 81
    0x6041502030f01d800249540050b05a0b412108804031010030b54407481000209a075000041000b840550203480041c289183c01410303000080c03582090380c5031500070300035003040c0d01c0035a00401c200141c0225102d141d40b00e0004e010682480701c0c0070b0042e072000c81c0d1625865080044403240c04503030081c4041510703500308600041d03c802d031500704c6280c220460115048095000300c0c5040365020030149000301070f150f55000413540c0d1501c11443c0344001c141418001c1c0818040103001903030205440f680040546000c940b41c0ea2641040e10241801400c09000703030080c044c0101e5020362002994050f207001e83c40f0b00540012000c00d0120901c0004030140003504000b80c1800450700c560f004044c924001d00c004266103017290001000c991896400301c03440d810015002800710310a0200034100b00080b00214144800283d01420f2413043c103488003210501c0c4c0240b10101405035104d807071043d0030b80354100441c018501c0d1040660506003407000105000300d00000343c40d80f2400030b03401601c001d01c0103003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 354090584 1250 354089334 354089341
    0x309030212030603100f0219050f090d1502120708011401020607050d0f06080d02061f1503020c011a0109120203120309070b070b1006030501050906090604020c071215090308 76
    0x10034640c0003d460b0503414014441c0d804c071040c000d4080c1c2480340081c40001030303944514030410b11095151030740b5541032150601c0382d070000c40a02000c0d83d06800c003c1d2030410f500e42c2103291242c141b1103400c1f60070b0300720761011034a82011200040403910030403035522401c2d640d0b600d0320a40f55514004144540c01640400c0c00240400d120300c000d41180301d80c00501240000b080c20040c01541c900783c002c8603039036000034030804400c1c2d4108a01500201c00081801801403100e40b0710407019518050005181887e42103170500c00c0c4264100c0701c0c030034403a000030051004d1340c01c1c56540d4001d118010724002544004081032800b801d00b050071540f54000d00416403254150300c51041a040101050540d002d40d250005a50744048010700c507491043d043d104007032030b220000b00c102c101d0030781143d81010316100040c0041e44131104515004002114807215503511800005d0103480340d864101114086e00600080103802c400e000e0b274600d449940030351201319200e05030704121100300320040c0014a06e280031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 354091834 1250 354090584 354090613
    0x70c061205181b01030b150d060e01080d0e1318050f060105060a08061c08070302070e27160f08060a0213030201210c120c0c05030d0b0d05120901020d03090302 70
    0x340c1c0103040c3c10704022841500b2000003807407080030b0119100706e900c40080c8030f180144d214458140030f810b505501040c5541841e568940c0c1d850f141c030b1441c003032050380c80c07940ea029540c000291101d50000e1a0511141e50580d0103007264a0030340c141250b8611581c0c00542803540003146090683d04041c1041d0705041440b6022501401c01810288d04040e4040000360041440072541d1041401091034641e0341c950781c9002444c061940d4411500d00725290b081c8140400c81034140c1d42810403015184c0040500080d1090030546e50350340c00c00c06040784070b50019055840c40c82d003608440c800317810388090b503603014104000da2185007816126400300382414001503004203031000505110a4480202d04020f0b405030f01151305110541000c14170300c1300c000d01e20714018041c00f4050711051412a141030740303e50742d80f50707240200300c0840015a22200481943d860301060003031015040b0040b18004240c003100388000b0383c05200c5140c014042c091024040354040d029110409a15a00500c80185070034030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 354093084 1250 354091834 354091873
    0x102120a0c110909030702120d0c021215190c0203071a0c0c0a03020304150507050a170702040f020406090b1315030902030f06061f08010902030606070c06120518 71
    0x408803089000040445403d0f01e82c80d101900c02e4440c180159600c08a41c010480f1501c13503800000c6190384528100c850f482c0e0f1010f211144039a05032840200a0b145520441c00c01c8540e010b09110030900e6070802c0040c900074508255841c02181c0c040000710311403c07003244c803031044103009004500c07030610b0000d0200000490383e9010341150942420055840b40340c5090074016502500164000320b8148800000400d07018250718076424100d00d8440165101d03a211400440080c00602c0280c1c40c1c81c030341d1813031501102c01d05580100100160401c04900a009400c50f0080300001100004003195621240b0101d507060590004a02c03401864000c072851400d40004800040540301c0c0c82c03610058808125240e01c620183e00901350610f0040d05000344080b441e000c0c18000c0020520504500d034204010505465810780051381e2644c035000030a2481c03140c140c0c000e24100506e00009002540006040411240c1d250103004c40d032181e010300810038210311300c03c0c1c0685c0c012501d03202070651140c2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 354094334 1250 354093084 354093107
    0x3070f05042307021608031e0c12040303030203160906080f041403040305071409130b06030c13021b01020a0516050c0306091005070e0f060901030603170c0f15060603090709110405030c0102120a 85
    0x101103174400c058a1004d2b902a4215034812408640c02100748403012500810b61442045140f4140c21410b2401c0340040c1007500180601001e45c1a080100d4140901c02040b04050b4201e41c04a960352907491400b40c0c0c1d5604188030b6405880c4417420b810f5441d03d0026000c0d8061144520380e51004c54054545079080c9101620465051042003040c80940d103030300380941402e042d0400d00503141c07901c4500089a80240801c041010f0344100000c00c10359070040d0540300d00d0b14040c0e060b00908419840d10380c2c90f06040d03c28040e8907228460030440111300c002140300c440203450380c060126454450040e2400310322040ea0320780c030121440040300179041100180201c04014500032410039580d80f5440104074815072030a0201e04c000414500c00d40041203d2641000090b0040900b5608201410070520001e04824452303000040032030344a03001003203010084c1c0b00c6210b0400c49441d0f010741c4641d065205100f1240a4007591001d004a90b0001c00e089401c10960b030380147c40e02c2c402d600201c52004501 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 354095584 1250 354094334 354094357
    0xa02011206091508011406010519120510030311060f010b0d0f0603030504080c0d0b13031808150a05042303070b0906040303050603070f05042307021608031e 69
    0x20764000503007000358000c00d25035409480103803050a0401104e1802c0da114500001000745000050207410303640041102c0d904540407400411176043e2a104803900d80d12000b0045041c0d08080c18401070300c8400103010704603071207a00c5003030124102041003502c544045410444120100004101055050005000e251526540007c4c0034900005c1d40c011519550000d90028001180c2030199070005c1210b0900140704481e81100d156043e65031000e001d80c01044510f11040100c0035104060043c1e00103011603c01070542058180c4842651350307101c103207210302e80c581d0040801045482c10340348075450045d500101e04070500110206988003007084d011400e40c0d2440104405d201040c45c038113080d40541101d1014101c24101424002c09a99018100350700c2a002600200841e0a102010000b00d940588010410340f0111a0858034648020904154203000070104508981d020600704000c0c10360010880110781c458020300c0c0d40b80240c0350b00b84035011032103138110800c41440000c1c00c00e48944 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 354096834 1250 354095584 354095591
    0x311061303050a030c12050403050a33021908040809101103040b0d0b0102030a0c03120b15070302101808090a0f080f010b030c010804080d0b03030a0e0a12050a020112 73
    0x12941c0b65031500c90303210410740025495564200c02c010381841000b445030400d20f4824240b6085865940d200c01c0c070098010104070340c055003030003503034ac00d00400d29502c6206401d84040c036141000780710103036012a00840500503900700c031541c01e9010b5482c0358000c07904a500541410b0419040c031850100f141e281ca420f0040c24912400c24200400040014114401e0000c1d01c6104101006082e105075140e100d05540003440316140d141e50100402002c04c1d01840c00102c00b038880d40c8a84000d055180105400075203800c2014842400f90340140b0529210390f08803000c10700121404000c0f5005224002c16650100000c103011a0044003d82608440180000041c07961a1400c4800e0080c03a030205401e500002c1c5131181d469400e208290183c0025000341c1903004181d00000e1000b103000303000902d40700d80802c540d103101c503035980802c40002c03005d4100c0303950f4805040c0203040903840400d600d100d031610103800b0030f0002100c0e0084a00540c050028a0f00f621140d00540c0c0402121140141d40d541e03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 354098084 1250 354096834 354096839
    0xb1c060e0f04020d06050a06081b010f120e03361c060e03030703150911040605071b08060a060f0e0442050106020d020601050f06040306060e06040b0a03110613 70
    0x11701d4400c00f4014404980001005841c12259a0415100d144508040d610000f840411641c01410f4030b80320084d070b46400302d021003041071000000c00c49013491116611021600441241811081c0c1c0341c080c500c8a4002e400c41c070500e0380c101d60030304c80a052580111001603145009241200a1542a2301c11100403c0c40408400c05914681044402c000025140c241405140d0986031901d80a8014140709002c140361300c10b40403040b071045104007030800000040d00d2060000b10ba4034064500d08000360014119602c1c021640d54003010b803040e495040c80c00e840000c9801100b00303044100d5106d0101c05400c1d41e1240c03500c04881104400ca144034032012407a020410540500c2c0c020084aa0f0719000c81491000c0c0c0d03141c0131150305810100542d4804507100350031a8000071054111042204d0320081260b1410100d0380c28040ea600c01081c007418410003156140f00804030f24880c07403090f0b40801011000ca8100b04211045101c048d1181001c9852142c003070501c04003c00c89041d104020740111507 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 354099334 1250 354098084 354098093
    0x1308060613150b271509010f140304060b131806020702120706080106020114040515060303130b0403060e070308030a0b0303040f06050702030f060c090105031806010b1c060e0f04020d 80
    0x1d01a00450300e0341d8035080001e40c400120011048102da90030b69054105174400b0412410900c900860700d03040c0403c4007060059144079186400282462040e545c0c4c413401d0514000c0040c002c0039165512419054200c41c4040b1a603101c7c4a11a2100302c081c8a20201c0d10b4407003a00940c004203040e80c0044518402082c15001001103800910081d40c400300d481d89009402401c640b008504290100084000d110102d0f07400941c0c104004070058050101d80c85100c0042d155200e1004004504921610002011280c00b4058801c0301e0082c0710902a02a0001210b51110b0f404c0c0002840184203102284403004990b0001d41058409030442c5c3c0b51584411500600d0320382075125a00042000420004509003803000106000c07000e8020065800d200080503090300590700154104000400010004101c0c1c40340c41c00c1200003441520b0055031121403581095021948243c6041c40b00c3d420450350b015140300d004110b40d804140c1d148d0940751a1000002e001001c2c006990001d609903441e40441d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 354100584 1250 354099334 354099337
    0x1230904020c0a060b01090513020c011d0706020c090108031b1227040506090a0f14010e0405071502190203031905090310020301180203060111030f1308060613150b 72
    0xb1a03401d000700040000c61070410181c802c4241058104900d80701c0c200510780301c1d0f50801514002d5900b0140e01d5146c1c0041e81c900610003050041e8100001e0034503161909400b041c0741007562416400d503030000b5948014000c40c03400c01c0c4242c150951041190003030f541550b4049116554610040d02d03852501000340140e6034003c02060b550841c3d8000083c0322641c20084a020440400d680901480c0703851000180103103002400b00d010780e03450343c080c1110750b0420348c0604000803125454440c1d03940c650a92100c6040c04903002c540c94440c8090110b0908407024401408203561380c010b000800a2495001560706040c8040360103110511141130201581c1503c416910700c0c0c1d41d07540e1f446440200415291002c07040001c29072a02c10001072010b02c400070140b822803040417001580c0da0310350000407100801202020441400003140101c50b09140c0c4000789007091154800d02509601c4c0c007041d94450505581865000c040d800b0030051841c01d40e04120401c0b10040c0301d03003a0f055503030100074146 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 354101834 1250 354100584 354100597
    0xb1b0c070f0e130b0703180b0c090102010b0303042304020403051b0307060e01200c06041d16020604022404081f0b010c1e0f0303090302011a0123090402 67
    0xc403001e8020500c166007001200507840000e40d8030002c0c00d0b002076110640c54030005004038041507250800c0400d0440c8640c001001603610100b181150f240041d10403c040e0040d031803207801035081241494081c540002035909607051941c40026400e000c0745807451001c1480e5030350381c00a03000e020000c0455401c1c001e14645142c1129000e4041c0100d50800d0300340451500500240301219100d40f0300c4e80da1240007241840b05000c00c403074603031080400b101d01c0c1c58a40c46c000d43c3d01050009000c555a240400805426844e048071804583c07200f0703103025109440c02000d00f0040c1e000c5400035000d442e08101100c2c0600000c551000c8080c0411005900e6921a8000d60002d5202c0018024000014006001072a11352a8104210480b00b40020400b05207290b02504500261450b90350780350351494404286580001c0c8941c922a80740781c050080c0640d0301040c0e004d54609030000c54812a40006203801c0c51050350b800102c03809411200034901c40700d040b0205070b00424031440e000760700c85100518a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 354103084 1250 354101834 354101849
    0xb130c0e0102100c090905150a080d031802090703020313020a0f1712160c0e0f090d0228030c0b07090305060901060f030b040501150b091c0b1b0c07 65
    0x5034080400060b10341940240450190b916000c2010141c907803000c00ba40942d40304500100b42c07a11055005504407401c01896640075815100c002030a480c0003400c0b0881e05280c0e102808550003016a90701d40070501170020f90091488400140110701c42c2c1c0c01158440c0c0070410040190a02d6000715040c20a0303030304182004104a0400d000c024458035040c141524582c005000351607503072100c41e0300703400703094100740340c0c2160080c80104215807000842c01501000c29041400d2a1070300c07504114101c29507450303009004001c1c01140051006c11401e00e51141c0500c0003405080400e551042c020425000f40c0800c03130507082c00400502c44181e802c1c041c003960355940c182c15045050450400d44054042d028a80c90100300300b01ca0394552191a003140c0d00111404c0c41980c0d0360034990701401a01c01742c2601c000450f9004111800c0540c0501440503080c0e8000205500c140110042403c0c0b581000d041c84500d840000c00c2080302040002e10032219055060400101c080e64506d0804250001f01 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 354104334 1250 354103084 354103097
    0x3070311041b020303071101020313300e0f0916110a080705030703020115030f2d060c03060b25030212030c030f130f030f1103070302060105040b0f03100b130c 70
    0x40441d1301c0700d01041d01f4059a00210b20f5410070040048103070040b50801890795010300303240c85100e0000130400551062008559a10015501c1d0061545040c158058030800d2490321000407410090042441000742041e00c00945000c184107940303501140300510414852140c40b40000798290300600b10641c401e030001c584440d401d1801a09486540707400f803c140f0003080b0200045882c201890011a0704a0703074101c42820340f200224407000d282c1a5254078541d5130040701c410000c5641c4101860485540e00300704650300e40413900c160f0312942c0840321280000291700e00c1004020040d60035a544030b0300481d03484004490250545030007c130b0790071203050008400c203c2032181d01c0781c02c00d51056070400118034441807030f1340d07034520080c1001025040001c0480054011801341d5840c000604540003200d1303c6030264a4020750350b02c024081c19000360300b440c0c031803901400d206020620300c0038014041c09000d2401000b42008186040b40c0580c44160240701d140010100c3c0b08200303038100c1d140e8a04 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 354105584 1250 354104334 354104341
    0x31109040c05060d0902150f120907090e0a060c0f020c01050903161205070b0415260a020c0c0f01020a020112020708070c0302030c010c120318050f011b020a0203070311041b020303 79
    0x7c207445500300c54074180001000b00c100d087c4020000c84001d42c405511020785a100c18681c40d2510342180c0000c08028940384076961280000550b503485284541000d01009900388000c503280c0350380d05841409030b032202010041c1c270b47c01140a0034041c1d20150898042103880c0750003c1104103250b11800c04d4444403243e40060200c107004410180ca03854a42500d003e250445400b040e54101d44141c0401078a00c08030303001d5000c10949940511151242d071101810300001e07540003503125403058160340c86040031131921402d0003480782400080580180c021520a0303001036a09480009408142036420840580020000d90160901d14020b080220407542117205240c81c06500507822810300098034003850010700c000501100c08152413501050504101c110303071a00d5515824000c0640c0600d20740448a074a05500148001c80003c01c030704002030751248141d0b126400040007a4154100041c00c0c008101450303a180c800e03039009000011228040804080340309904450000140c0000090 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 354106834 1250 354105584 354105589
    0x11809080d0c1404140618030109050102090f0a08060a09050708100c03051e0114010905062101150c0b10170c0127030204090501020c060703050106080a0501031109040c05060d0902 79
    0x280c90428600521103844d0608242018000e0702111080c80e2044d0400582d0b00352071001e10f0800b40c0c01d40c1d0060000d2100541600d8014040d400c40c0b00d20702e00038050792401c1c01071868034040c4034040300c0310280503042945895504030007414401200756100d20503040c0c0011040000c0082041a03022694002105511004000c068642c081c3c41c0078002141c21484500410105040c42c0c112010440704d124020b4203400141c0c0ca07141a5844990700520109038036000404070b0051888066000240d001c2e260380311005a004c000c3d50112090024842800820024130302c18440d5030003100c101c11050340303560b0b40c05140c81441d802c101501c101e908035941c80c1c580b03943c03c1100a44414041528071811154001d00421201031512001e0f00c110b4070b64601c0c030140700c429811911211381c584141e5010f4a40070101034041c18082c42241300044000d80002c41d50302180c4521410381e03510a400709140501d081c108006940060420385032403c06c07400019040d41c8481c000c1142098540c40132072010307070b81e004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 354108084 1250 354106834 354106847
    0x1b060412090f050303031305010e0a0f0c050901030305070605060f12010e07080601061202070f0204181103030304080703032c0d0e030304050d020d0305042606060f09011809080d0c 79
    0x9074002c2c841d020040c03045941c0481540c0e800401c00c090452501c0e8241031041c050b1403c0c5120007980d000301c007114018001403100c00581140500f6610744196611824024861802d100260001e042402104d00185460300095041075000304442c03907031001180050028409424482066076403000700f040220010301c44500144040c90283c2020341c580480a00343c20702054010401d1a800a0f00004114107140448013958003e081001030038401120050840069502590910407008201c482e07403034004101c2c0c2c402c5900c48816410010315507400e401900030b10350407134004900b105400c2059811001200304412a01c0c008102c251518000a41088480c1d02014003a4004010038460b58a0f21140c0b05219641981d480d0100c0c0528101281c09010f5a04502d1000740240700000300c01c401c210035003502c42245010354035981c07540340810441ca510150083d812070300b000010400080720309103010884075400c4010034582c00c259034145c69a800110b81c0010241c0e141004402c080c3d0100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 354109334 1250 354108084 354108089
    0x30507030b0a050f10030f0608011d010603032a020907050d0b012c030304090612120302090a03021c0503031003030207050102120f0706180302071802130b1b06041209 73
    0x4990312810b9003440302040f00c078802800c610f400348041401e8180c08501c0381d4029100d110941c41c0401201c0d1711560464081c1c0030024801d65008000d030b07c1c24240308010300c80c01048950540381c0a007103050101c41060520300c0c841102913042c0c54031000c600540c85101066120f0f0013150b8032265074007a4020400c0480e41c00403400c60401c40c420004500001c0c5003061444402010b1340a40103c1e18103d002070f2552117150402700e0100d051a0000401c441f050003014000d038400c040381c8802d00fa580b0710403400c0780913100342c035544500e0740328041002d41001c0303481c414042d141944070000003103103485461650348117a545026904502c1410003d140d030601500d070260000344040c0003030003040b020b840281e002e00716482080102c00034840c8104810b65215080100402101005041c61412301a450307050340d10132111884040b84904216002c82c0c800c480c1046010b0103010260790405c4429038403608a00039140d50381808501c83c543c0340104010551046100d9154440044140000100100c5a55 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 354110584 1250 354109334 354109339
    0xd0f061505040303121a220f1803030f150f0e07030209010203070611091002100b010201020a09030609020d05011e0c0f0e240408031b06040209060105031e07030507030b 74
    0xa100900001c1d920450030351840646420105846841c081e404140c0c0500383c103520350151042c0c0304070952040c7c42004044204950344100a142401d580340f5050f5101c002131540001510407880300001c1c001c0d4031650804170690380001701980078070b0741d284207510641c112a1801000e51000c0207000c110482481c0e10482a00d02542002c0310400042c1d940e0080307000081005485490400743e0101d07241c15200b15403402800c01000c05076000001c9c0d2070b0b0858084401d43c036030400c407248165500500840320201e00342e94401e102d01d032654480341c00500342500201c1c0e018154946800105009000341c840c3d14404604001c5854203032920103089905000740034043c005000a0320591070f0b040044a8107144041d205041000b540039000c0b0207404c03030140e11000d8490041004100d000307000006d801d100321550440c41c0c41d010300301c0741180d503400100c0d4000e6001008030001600c551264002d550030000006180328250006000110784c9401100c1840020b0360710303410411401c0d818000ca99840e0f030107 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 354111834 1250 354110584 354110587
    0x50c01051303080c0c0c130203010e070e01020d0f0309020310020a17060604210203161a030405030901180812090a0902030402090610200c091803030a09080d0f061505 73
    0x35030b50250101070b00620b2004207110204101524010500c03c0241e07a400c01403400b02c4100013241200d009410030b005080c00f0700e1410002607000b0740183c2c1d880300c440f03105030001c0400c800c0c2203a04071122078600071a14109501c4d107032600b0060301d0030400c00709108864076002da150300380c980006000c4804d08214020380c02c00390003440090f80b01c070b104880c01c0d6117403944010350107036044c1d0740201da00b141610025010b2140e0006441c9543d4002103038001e5992030010801035504031000398440e030000382c40180c0f10360020001c0039280c4d8090b44c890442420180420302c0f500b96241059402d20302c10a014100b10100001d04000a1500303010040151012078004c40c1036050540110f14607220041c0014000d0010311141c070030300d80c010406498000040b1100040e003e0140d416180c4501c1d0280c040c03400f5121141c003013444030503103204880c1c5903a000c800842c254ae46220005028200c0a0415126407404120020036070310f40c2e01924450301d200d51030125040d4030301500200381904070300c00c00c010480b0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 354113084 1250 354111834 354111871
    0x14010e09060708100317160b010e0109020a0e0405090703020d03030507020c041404201207090e030304050604170d140709150906030b03070914040506160801030303020c011506050c0105 81
    0x121140504c0949402100401c568464106881094810070a000c40e0300d5000c00500360811a618202c030741658035550f09040705990f6026480b0071303401141c040ca8085410440040d1580c1000d5002c1a40154a98200c8480e29a40c2e0003244a07100d81400c01d0300025180c10400c146c0c250100000b8881d640c01f03031400c01c40a49110701c00c0044800c040c02c01061404001c10309c0c009030210035101da4507524001c3c4104190345070078542c03e9a8440901c1121501da0401441d41e90b60340c0080140d0b440f071a005009411951307600d0340c0e06012030207030100107100c2c0d40c07052180c070002c1c0c0301d030b4841c40e0501c2d0b809682d143d901d400e000101828034180313039000100c031019641d034403d96941e2140b5544100c0d600c0b410081000d0280400117400c00c075040c1c015000030f62510b40c95160035101c0640c03882c040ea000e01e068400c95121540c00702115074040301060085034000e0010400648280c1c001c02c5840c1d00030000150301820101865065141640903000003007003c034188022110a10030b03250070880c0e03010070548988 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 354114334 1250 354113084 354113101
    0x8070513060e010e0a08030a1b02060403021c120914032e020c010504030903171213051e06090d02060919020102150703051504050403021b01020114010e09060708 71
    0x200d0040c50708220441c0b4461140364020034000c0c90788100100b4480c1407a171a909a55584c0d0861410341000a000c07254400c50300e50417005054520790041c0a5a140c070b8110313000d000100802800d00301145000d4111040442d95446284074424121755428040303034900342299101410b000c2c60036219801c0034441e5000003203000400c6440000d1250000d819000d40940f08000f1b00903c12034818035420300d0700700010103904c82c0c446400d0702d11a4200d691208110352204659024034041c045401c184d1201044203001051008400700c2e100c0c1d811180360400303000c11891050750080c1c900f0805c0d880b03803040c00321000051182d602c45907100e100400b003610b02b5500c01c55440105c50801c05000190240503000d42e4400d2143d03240c00341080081084a090000e0018000c0000b00e41c2c03514a401100309001152400b03005180c01503030142c2c000c0c0078000100e15007400241e640803a03503041d90350340d4801d00b0b00c031961380c03803600c1c020503008500403581d20f000610a0706240005254800308204641000142d2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 354115584 1250 354114334 354114367
    0x91505180105040e07030812090601121a1b1c0e2a04140123041e050c0c190c06020109050717070b0711010f0f05120901020702150703080705 62
    0x681d022a000300b40c4e804080383e40c41c1040115080900f2841002032152410800c10f640140115540000c69110743c8ea00c40a00404d030045881c01040d02d0710401d950b21500080828158100c61141000581005c404410030800e0303100c00320f042045a400300d40c10046005c64070540c0c0074100708802600c0c03503a10b4041c045640182948a4400940d5000c1c1c0071211a22190300051003142815100a007d503110b1043c607a650f2a0380c0d00760b1103c03007541d04142c01c030b0782068040c00345148800228588844a030420ac01c010308801001c5400f854424803140342c0d580c070100481c1d895403440c440840a108518140840f0070f05042d00043c00703582c1800610303400182e0006040c81242e010342d83d0710318007000c50b11809040c80c4a680c0030039440c2d08089226414411140b0700c202c240d8000f48c0710041c20781403004080e00c001284c440300d4008240244415001c49040700c600c1507000200400051400480e035001039613484e0702c0040b50f1640c01c00420080100b54000da60503400000500f081400c0011981c01840007 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 354116834 1250 354115584 354115589
    0x2030313080f13031118130311100c0206040b160e060901031e060e01120f030807020f010603030806240405061602030d03060503210f0d090b091c0c08040b160c0915051801 75
    0x100300300030000342717000300091041c8840c8a60892050202d54408900255100010b41d01a106001040c0101d84034501c40c86d0054611a4151119404486036004100303064018420b102d040c56190601100303e0307498040305020302805440001412070410a90510000058101280c0b0038100342d58003010410024407600c5603603142c40c14a00956030240120f007060189038814203a0742c04d0450200425402401c050f10a600958401c8100290b007007500703084d0300070080b0001020404020900850a1402c0107160311003801d403180717000481e29400700e071a00080ba005400003e94405040c4520b00d02030080300c80c1203114903580d01c03840b00190362000c803501c520902031815000014007440d0784982a000043e10540010f1481304e02c1c0781c002c4426807125004180c074400360000301c42024a01d8010078100441c66004192181081e041000104003584507002c0071540921100940d0002400d4070110b1015060075138021034040121100500846e84035040b070f030f201c1d51081008040b00c02ca122901c904 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 354118084 1250 354116834 354116837
    0x9020f0402070804090e0d14120114041d0607140c070e130b0f06040e122a03030705090f090c1e040b0d05100602030313080f130311181303 61
    0x1c2d81d00c0d4600c0c101080b841aa80084a000e007001c52800e0080e9001c540d14000c54556225901c55828030000505644034400c074603c52020140014046e01456401c0302041c400c1c040c100182580d070511a086000d05900c003005100c1e07000342c00300003040ea409480c08885c00a4172480038202003408090a440d920207004860904028070300058156811100b40c1c12042d80104a500c0b480c28600303081d05c20104121002c2e80500c2c1805c4480600b20400903911400324002d540ba00d0501460a0308181d1482015252030034224000449201c80b40040c0000c3d40071300c8c00c949540b603036691101e050001d00001c0c94109407094568400f0461405c058508560580007100c101c110207101040c011100c5000741c0e04406408840070948204a82040e800301c0d000c1d03040d007441082e899a90761001c0f03130707030b44022152540300b003044c020960700007181e040150040d02060040f06062040d40c00c903444400c14103138801d0354000102c0403089180d08160350740701d04140c0e12200307001141c6000a00d080c980c0348501c00040 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 354119334 1250 354118084 354118087
    0x801022701020a0f080a0e09062206051903060c14030103021309080f0408060a020a0c0b0403030605030a0803070807020109050c0f06040e040807031202071110121506090909020f0402 80
    0xc0c0681c030a00072600540e0b4056403c1c3c0700d0242d0341c20301c100d40c0c2d00620310410228484100e46041c0340340900000b071042800070420861000700207581e074882d03000d540040031115104c250100c1c20307580b06180901d514020003a0b400c0107502e14204003050700d4a0320002028450840440e602800e0181d0481781542c1e0159500c040340506a0140e50080258601c0500031090108503060035105020040c011100d580d4200c0e44035445600100c81207101c2c200d0107001084150b0301c043c0004210303050780d40d48240a400c0004405565102107801d0039101c44048074142030000400c01c51940007a41c8642100062008100c28206540c0e15a80c0301c5c0e21102d040d1080c4582c80c1c240c0f44a03511340007110003802c403000c158100c5040c1841c180c840c0780c218500850100b80d00e22506c43c0500300c2e91080d00c12540e0072070400c03850003080a017480244002c04c54603030101308496100b11400e81d414061412404000e5591440729890100f0040045019800640c80385007021135400c00350b030301d030602c6481c903210440c4c005 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 354120584 1250 354119334 354119407
    0x5060f1e220510020307180510140f0301060f09061706062a0705040501050d030e210d020a020102070803040b0f13080a030203040801050601031b0c05190f020307080102 74
    0x1204884803500240310f841440b0300c0f803004110b2500914095610b50719183c43c41c8007960003002c1c61500c0c0e8007680f40c100c056484900c021510490444041110b110006490200c078640f48030655032003600420f011030345d00b088441c80301c4da0101416006240f40d150054450300ea110403183c850401422032840b03480c1c0854001002401c1480000c051045a40c0c401200c2c01d0144042d500c0b0202c0344602d521a910b004e0000072242031001e0b5944100340e2540d150075100810070100498010b07440a50fa414500c1d000c110b810f016803c2007a0302062105800070b00388109240300083c42d202090304440300981041c401001444000400d444140f2280c458031303a220b5020328147c80c0f400b1000e0344034030124807485c2c0c2000c0601d50040010025158403c0080c41903a90300d1700190265000c2d90400320580b11115405031403644141001206d0610a81c06e8074614610400680f418189540782602c1c0412036040120441c0b030200445402009241e0080d23080c2140110780100e01858124220002000c0082e036 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 354121834 1250 354120584 354120631
    0x70221010b0406030308040606090b03060a02180d150e0708100207020d02150a020d03060518190227090c120702030405090106030209031b03120a090f0305060f1e 71
    0x141c44554081d0080140c40c0d9070b81401000c12400781c8082d12803514114002c15041c0d4180034403034140c8409801801c00d5140c54100c0b10003940910085d444c540c4001034134100a07503880c2d4142c10424041d0102d5440d000400480c1001c03101d14503c4207881da84080e9040040e0700010840c3c1807810175146005031100114008184112501000203600c0001d05119141c0c10080c603024007100b4008ad401c03603068441090094007250a1405400c3e80900e213681200d6150084502c07496010850120f1007541c400142d40040980e004800c3c2410341000903e20440e03454400d500d06e0703080290890300f484040c108224084031a118004480c01c1d1a07801c507000a001500070402c40f0010715016003114415a51104020020742241d40700504ca030241490742d80327501080c0c40c2c65420350000180608030140712900e0386001940890090b00900c1072040001405c1c14a0408001c011401240607002919004a254034240300007080c02c001d43c1903907255410b5021405508075409060304505c200101e00f41a00e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 354123084 1250 354121834 354121841
    0x30601050d08190519020c06030a2a020d020f01091a0403211a12071701150b0a031404080307050318010f150f03030509040216051b010e0607022101 65
    0x3d100b40c2c08005210302141e2142d10000610090a0183c0e44110800b101c540498940a615200d01e90052080c80401c5141c051503000740d501c0c800c440481c3c0442030104d40e0001b040d549000400003da0084800c20214640501101010007001002040070541c16682c40c10308915520303480c42c580c04807000003801c160083d0000d12441600014958180098907003000141040f44805120100490300c021850300304442c000d10580190405045201c0c02d0035a41d109207000e00050041964a85c40e0a00c0f03c0f030442d204042c0580180b41a95079108200c65000d816a4061600c41d4851a0000304210100b0f0342c00c0e06490300310782ea17842c0ca56500c0d2030b03143d001c001f80f09440c0ca40c01c00300e500c1c1148041e407000c1f2941c49a004841020741e8859103581c0c61101454440b140c0c84068040350081251040e02d00d8941d0051105505034040019599000d4070703458034190300090710040d08285000b0000d001e47c1c10a900101180084a1951400c060307540441e00c0d2404076112a20283c440601ca032105010070b40 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 354124334 1250 354123084 354123097
    0x1c02151812040e27060a0507091d09060c0703090b1c1424010e040b130e06010806010b190302090d02031006031407060c1b08120903150402030601050d08 67
    0x40d55503480c1d58543e40d074040040741c1a55800d481315100c0c0c1c00340b807a02040c4c1000c000da1460400c090310440d91440101c0e000303480001c0c400010000300000200d0030612407009602d8aa010040c007190354900690128130b4281d0240503a40c007020103002040005c0e9000516170181c8059543c05921201d4039641c640e01c10100d0340d90150340e42c0c2405a0b40c1c01009900038044d210303103d00c5900d8881d03a02c80c840d03095400091241214009001410a00018240358102c1c40c80a20003501d800e00c1503811175103500c01c85828840304965504000e0042028450030031156001d480b0034820145405644880304180120740302c1a0f1052603000304440f00c503540d90712225800c068000d002d0311100400c850844000700b0b514002103030078544c80d1101ea46070900c00121141602c1061300c5440704040d10b41c0f2206064121000a05010f5492003c0404c0001c000c0c00402c16030010007500f19141c0303503100e04142c248111041e4403240c1c4007500040001603900011070604442003928246050021400c280403d0320402 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 354125584 1250 354124334 354124363
    0x403080a140412020112050f16050417030304120f0804030f02011d0102030a140903030c1b030c061006110c0f0a0e0412030e030c060f060109030f03021c021518 70
    0x214000a0903031441d41d9803c002d41c0300b40d0303d8165400f1040c5a0348104d60040c2c5010000c80d0604000518504c18103221700c5800e5046d042c4941031540c0c45d40604e90318041003c011300f00350408020b01c010005ca41414009003502d47c02c10f4900442d0b81c1000400c8400010300140401800c4c04500096a001391b0140780769048164102455000e0160458042d600c10b44414030304c940340c848a00c40d4800006080e07402460000065491500c0710484508035070016105600c10700e0803513600b02c512980800003800101160b00c003424031131400d009041090003a550005090066950b0710001c10310012a403c14250000c451070820f0700c0b4007901040850030b50307401c000c0c1c0e4007103a502070100303014004e0042803801c0d001e030f68203226056494114644a0061010803c61079010700c0100724646d03da04c5080d94094010b00d008a0159034949850154403610541503015030881c228030f010180000a400d0082c80103030004050360800c400c81007040c180001c00240b2940c0040c2090180e240b002c1c861101c543c0c000307 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 354126834 1250 354125584 354125587
    0xc0a050d090f05060406060e1501090b07020a0b030a0b240901081012060203060f010c1502090409020a060e090a0204080c01271e090b0f0f0301110309011a040902060403080a14 77
    0x1840d01b54014200c074021040100320000020750040701101d1185a4080c06a44501400b850045c1101860304085c208aa105a103c0004106101824003440c0300742d00700000868030580f41030034008a0110071880031280b803081e0742a2141181401d003110061a000c0c64415040e40d16041c415929134400c1e00000e041081d42580c4500340701d4540c0145000d41d82c1201d0300c6a2101d40781c0010344008441d000005c1500d030305140000101030544d0b02400c4041d401810119568840d5030025842510542004000c20a006807400070760825010140e800311030f0010440c0780ca414400c01ca6a00d41c07000d0f4040e4104604108000000b81085200c3c80500c0c43e60380755a008030b03407504c0f880010f06e0052929481c480781d080344c000481104600503003841100141c200d001d441a12000e0112466a03125515010b40d04c2e2102c210783c9552402c000e43c81b9404410000416500e46500d070104442c95001662080341091010000f6039a20b0086500312903004d11480e0791205039403000d8030905c030341c13264000c40100c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 354128084 1250 354126834 354126841
    0x1e03090a05030a020d08011d0c0c01091a01080c01080f0612190b06090c071101030c050c0a06020310050a15030504140f03070614102601020d0902090c0a050d090f0506 73
    0x13000520b10406400e9074555038450380c2c80d816290441c61107400000098070340791000c18031883d541d03001004040c041030300201d1040856200e40388000c80d04c85404403801c1d43d290040120071000d2084807444402440c10340007606009045060b4a84042c0c1207522510340b0a50b2801864030401c86031041c03010003090660481180c1c00e00c8450034000700d230181d00071403001001481116941d011500299030101c100d0f44189100401140108100e0040b0800e01108000c001640701e4100040100d180c401c0001698911b05403848410807901944030a000741c100c00000d02c070040c002110745260300c299150004269445040081e54841c515144240600035002c1c0040d900b6004002014410701414041c04804600054118241710880c2c110100d403040f40c205000f003107401200103001c0014034245c83c45a2000c01005800ca030f0100941c24200c9580b002c00b6411400e00c0603c169000504070005410325103805d8014109100b901c03910039040391391302c190100300f1013600102d410054002c07003241c00e00c2c81c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 354129334 1250 354128084 354128087
    0x6030209180f1f0c0507141f0c14070f0c140f01050901022d01022a0a02030601120f080a050a08010e070f18120503130801021e03090a05030a 62
    0x11807080070700714140103541100844210008440c80d1580e0b0030341c3c54010000d00210050003c0c10858580020410b0410040010407141640c04141c952460041c28066000039120701d002c0c405a807110a100d41007000c03103410590800801010324940c6840139039100c140d0310305500d5210107948000c20f00d402065010a070f241d0206d40b4151600f4003525000ca00d49040030064807170f80202d0030546c4c0141e001191040300016481541c0c507140d200414000c2c02900038903400303800e87c0c20040900c01021517041000b06045500c102648900040c0c0018045200f000c1d004240c03144814020103041c035107144105020020803100301ea00c20340d089442162100c02003d8002c0c8641c0c4125202c1e000100351a00108078845178090080c010b04c2d050315054214608858140e411100c00e6150409404441400103214070380c80b0118040b40e1310540c060b40c0e4a070031440b482d10709000140c2107030400b6881070001d122112002d0400403000c0c000321600d2a1643e44e01684503103040002c0714014080d0001043c00e40c00c15 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 354130584 1250 354129334 354129361
    0x31d01060e0f07090e070e0d140c19140d15050703060302010806040606051803010e0708030a0801090507050301090b0d0c0f090c080c07120207030c0308210405070509060406030209 79
    0x58900340b107010301c2e0f5121200c0031903401c0fa1038081c054103003d20b400400c1c040c6005180040801602620b241084605520f940d61080e15501c6400701fa0303000f0360917545803841d0180100c40080c0d10441c600c1a09402c0c013503070801d442114130220740104480c04142e000d0265001d10042402c0d41d10300e0078003503807600c0d01d0020041c2c13400703200481c04504400081500b6140601811040c3d60ba9a90b4290520668103400741e103600e5019130854055503102a2100e00030400d21000019109020007960784cc44c4190004102c128142e02c03d00145103002c052250151b440030481c0d045843c0400c0108080280e01c0010300d00c54044040240f003000314401c00550600d40d079082200301c454032201040103402410302581e59000455011060f00d10800079000000c4c000602100d210316284111000180c481e0369403100070340c0b0354106032040342c0c02044c4003142403e141506440c60310a80150f0704541465621142d4600e0075010701c6101c2d00d49a0700140e459141c942c803810007140c004000000b981001c3d0300c5e8070f551 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 354131834 1250 354130584 354130591
    0x80a1203050603150c0f1303060c11070807060c020604150806150c0a080309030405090406050f13050309040c020309040c0323071205060f0d080c010e0705010906031d01060e 76
    0x10a04107400103039036140210b20500300c0c21020042460301e60f2008000344856119080c003800307440e010301c801d41a5032400801640914401c21002803005071140d8060304d45c5901c44810700e0030f0f03130241c0003c0c03040e60008070310b41c01210368904101e8401070880c400240300703000740d03000055141030003c4009074043c0d00040460241c90252040c0c006c40440323201c005418418040c4614096000c2c1000708005811a0001c5038040a0613044c1d909154495001440858003a00c05603101d42e22a0140221103410145040c0c102c01c64101100d122881680d5580e22805082c10131449265900f0101d41c00b81e000303004995070701e60018020000410041c9010f001054003c0e0a20b000e511009031030070388020b10302c01c070304e004211603198010b40d081e0070720300e0354042c00c1c0051074240c21070020f200c500004d40f1920700603041a4460400186c4480790503d0803821550440e90030030b12580103000810040c4d0700400700e001501c4c0745103008140001804804004c1402000f68481c4961a104000a20720162240b4600 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 354133084 1250 354131834 354131837
    0x910080601120509030f1b031c0e06011a03190c090612200c0f0a0b1e040201050f090a0b0c010c0908010606050d0b041d07090f0504080306040b0307080a12 68
    0x1102e10b042040407088803400c41d080c0307495a1042040d07111002c04540500ba40200003525004442000220349085400c468800c61004582c03d0220f03241038003030301420b10340c0c51507100181020740c50040101c1c18126207000259454000201190098403031800d04402118211070600c02c0100500340184280346a02c07034200004d803065107170280d118480c001c2c02001c0c0120f0030344401e400a115a030718420b0740000300b03201403032241402505c1d00410500c0f060034080c0c000e404001861038400c40340c0c0b02242c0020b20840c16040080100001030380c2000680ba400e14540082644600c05500859400005600145c0c0e001c040403031480320300c00054012140f52411562204100e9588140c01e03070070380b0381602403840450801e201c1680e0031038099001001c172a000510200b42d525505c1041c203139000c00000d40d4085504040000c1c0803030b0806008068002c124000c0401051800f52902c144500010f042c051050352103540350743e41540c3c1003160030040c21002d01501c400083c1440c1590120072500000310 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 354134334 1250 354133084 354133097
    0x90d050f031b010504020901030201050f0d140402121501030308060f04060b07060c09031a0a182f010909020307021e0c1c02030a0b0711070e010302040f18080306060910080601 77
    0x5800304410300a44d80101d40c09006c600b40e030b03401c0d58010345490300b1260492020400901c81c0400c0e80082c1d015528904490a03042461802d080c014010754007000c3c0ca01211982c0000344030304400c0001c04a00781166014074220380c15072107000004281140389003440c0e901c035052a9000c0340109030400200340c3d1a20680b0100051814400261560040344c800948850b02141802d5807009035540d200340d0222600400041d0900d81c01c8241d6050b46a0132020754150084102d540d400b4030040c0c106c099203440c01400ca40da0104158002803d0001d07500881030101d8021010401045c001c000040c610304d60130b05e1601100962680c007a90b184120702101e031041001c0e03600d04000700e02ca43d000b00c151a0f000b8002c1e0082c240d00b0744441c1024640038002c2c0c010014005001e03010014140000006011441c00010440d45175004000c00e07120f10070701488130b0a250600647d03100c801c4441c41c1c1c81c02c951000d0015100e54410313000401c20300442900326003010709910780b58109540130075110721840d0240c8034070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 354135584 1250 354134334 354134377
    0x10b060c100f0c0c0605070207051f0210020903120711030a0812010b091f0e09090a0501060819030c0303090b0f190c0f140c01020d0c0f020c03060606090d050f03 71
    0x100030340d4001c24010020810501003c0d0110380c458000a52005e0329004691806641cac0d4041500710002210480702e00000d10031007071740c0326410b224105104100c10029410041c03c100000e07180c801107202240310311000211a0104803c0c110a9001010020141c0d9100102420045c04684c8091442448010010004514040d9810aa60150f0405004c2526400407004042d000d40981c0703a007141441400c0745840d1099541c41340040c42001001c3c080c200602e200d2030701d1402d498071034114020b40e811905083c9803018070103021511407900751401152444017800d05074002d01c0030b5503000e0301d40faa000d020004148809030340b06000c4c00c03240307071030140ba00060780c0203604484070622098000f41290b10651811841909585540c0d0a0a040d0318900f10400885030300b2a8003280b4002507190302c0f4204010380c29003101c0746c013027034164500203404400c11410019858900060001d44604008aa400c3d91512241700c003040d441d5105c8121030040c900020b426959800100320041801d0103404017 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 354136690 1106 354135584 354135611
    0xc0f060721021902062b0204090212010b070c15050906031005030d050a090e10090e0a0b07090e06040504060e060103110108060105030103030503060d0203010b060c10 73
    0x6000450344600c4000c1d0900f241191900a4010310542100140c1c44000454a20131000000e0013060030a503004000781030907840310700780c110740302042c046101051a8000c140e0803219a0215029030f0780d551000c41c091117000fa0003040501103000421220510a500c4d00d150201070a15504103020701000c5007441e00121200061860220301c1003040e402d041c03002030601030452801504d40044440068010f00c0c95105140301d07407c00701c0c0040d601040d00f11885001d028040402d21800b1060221280e955429000a4a0180ca0403021440b040d004094040c2183e0001809141655440e81000001c1c18020001c0d581a61148290000700d5803d012082c081c40c030400900c03400b01c0c401000100603650081043c0d041c003100700010700c082a0484240ca602910454600c0051500b62000c82d025211a512040e0800804944c103404203902080c03d001d03001100d4010010321561090 = true := by decide +kernel

theorem cover : BRFrame.Cov 353956834 354136690 := by
  have h0 := BRFrame.cov_init 353956834
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353956834 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 353956834 ≤ n) (h2 : n < 354136690) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
