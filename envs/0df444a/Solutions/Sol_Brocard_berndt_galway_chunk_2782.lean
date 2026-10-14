-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2782
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:43:49.148307+00:00
-- url     : https://prove2.me/submissions/685fae3a-5789-4416-8dfb-db52e0c8d22b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 500179856 ≤ n < 500359712 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 500181106 1250 500179856 500179859
    0xc010515031014060f010216080601180209010806041d070e0f0702011b03050a0b040513110105040f0b030c2b05011e15030603150b010207140901050607170a0e090a0501 74
    0xf40601c2c2c01c800f4200c24061213030b81d8041c03019a0300920001280700b00c81164107000e681d0716048140e543c02c0a03c00c256020ba0440014410940540215070307000c1c10603140c0e00403d4035281d0610000301214100ba06207400d21484541080c0020f0109800420034a80345018904100c0c031441309c403002c05003240040da85001c9910181c00025500c0d41074081303d6040c0014150303540403091001d8000190496441440c0804010062109003c00d040260044103682e081145020066840d0703c40e40c020440c1c2c0d01040e03a0100403042c0200003d55120504522031414096003011031a82504000c1903880c800248858160940b245440340c980103180d0000091000740b00800c10099000f1103000301d20144034010b80765481c0c2c0e4000e8000703400869209191480c940c8144007810b00401c002c9103194014014807100103020a250302d200c46807010b0044c000840c0340d28140802c007980d0b2000d0400c8481e0182504201c810095482c00b50100c3c014644907e00b0070001c0904000d41c445d000ac02e410b0916281100 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 500182356 1250 500181106 500181131
    0xe03041707031101050d090512030108100b01090909020f13060503060a0b100509011b03080108070b04030818010c170a090905091507050706050103060204060306050102030408061b0c0105150310 85
    0xc0028030fa4007820203070f0303646030b00940020281c030b5030349006801c520442d840c0c240c2092100d0000c5048a4105c41550a20410704240e142a5a9140c0b2810b00207800090244800c007102c1d030150f22450b2009118040c082010000b2502020300c800e5410b00c1c481d5290005c201c113042c280125540207160000030000b503480741303001410580c115030a4004212011070b200390241d0007200e0050341c002c00549000c103104d00c2464018040c14090150689038000e02900140c41e2490005880990340c0c001c2d112800c4ca510700c15204c240142208005042210441e01000400c0c0091f824024000701c0026840c5c0e100511100a4101d0000e5402000c1c400d1070a02000b62104010441030900340c80021119002e40700c9807411644c5001d040c6000d800c0501e0040000100181a40103000b1655152814410f2541c1d030001661240a144522615504440005214402000018220208d54951460803c61000e0300f80c0d0844d06d0440d00da204060860311901e1007842e04219400d03c1d003400e100180b000f400f9964 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 500183606 1250 500182356 500182373
    0x2071e1e050a03050708040b030f061201060f0306090c0e0a0b04050106080f0f0403050f0c010608010b1f080c0d020a030b030114130305031302030616081605040509060406090e0304170703 82
    0x500c050f04205021a0150070410341da400c8500030803a0300340841d1a42000d00c007486601c20240c0d0100d00c41c01c141003814602c6a0180103180c11552503c204500c1c551654030b8090141000881c1101e046c02071400114000898a8210340a40c00e04131000401d0b400280c00d000c00c685040c0c02a2007482040420000042e20f0782075000d6012110300110350300c64503640b4095410303006004603030310305070408240b14114140c1540088210748510b0024070031080c0c0001440420700303464081410070400090211516802410202d40058564880303614148114401a04036000804c0140000740c4611000030645824000c00c00328001d00d130b581a1013820182c890641d2010003000003002e1010220001d400c40c000c213480e080c8403035009010b40396103282110200e904030041c2417a00c404901e00c40081046481d0500c4154926002034581c50f10381070610080000941c4014402540181c41c1da0002c100310080d805020300320b02e00c80e0011a2900e040c1030908468501300310f11183c990f4010002040801c040e203 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 500184856 1250 500183606 500183623
    0x6020c060d0c0c020301180606120210050a090b190809010b010905100c14011e02031005010305090316060501081002090307031112030301080c01080702030a0206150402071e1e05 78
    0x20000b4200301081ea058401e18050000a50705500c0d01c0300000100d1540c10001643c3c61081004102d442c1e16486100218600c00c04003075080103200007110f00f03513806000206902090740c02c1c9801920343d00d80c240c1c2015804606005c066189200e540d80f400c41e003100304250420310340310081c00101840400240081500d100340d49c03060003010280c426481c000c49102c001d6070f400c880d4041c01c01c0b038110f010a02803e100048400e0314814112100b1074030b0690710035607001d0b0032005500a00a482e101c011805820058040714aa00041008842c0d1024131103040d01924807915000c211985490460390900c00380e900c0281b6400c0c010001c15105a0f030114003501566803144040d924901428040303810f400c0c4480c040d0460344400400860081d100040040e1007110036643c3e0442d81e99140c02c12a04d03030040e0b07481100560311080124002d240c00d82c40442d03a81a01620060400119840308000d046560214400200c0c0300403c641c140045d070084420070030507949446002c10b03d15601d40b0b0365072400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 500186106 1250 500184856 500184877
    0x18010e1003020d180f0c050628030e0f0a020f0a05090c03070201110f13060e09060d02120706030b1212030c1c0f0c170105060f071e0c06030606020c06 66
    0x2984011842840d44000300075111075480707500e42401c920303142c01c89440b17840c3d007501c1904a625002500303140400c00c40d8008103801c03a180c002d1107066514101c5400aa40304071050603281d441140840e04100000314810981c1d00c01020041e8542c0140000005100740e07140c003422000d50240030645448003140d4114128001c001c1da2075603503603812030040510040d407103181d40000500b02503c0d41040e000c0c1a982a490254810303169684809840c2100991a441c3d0040d034a030300042d404d85004241880458001b4240403c003040d00c4801a0401c0d283da04101d0200f940d03000d10004508003011030401e0b0300512401170042c00341c5481c3c005000d0000500104c00030000041d0009550f43d00291048a010034010510502004101d06005012503000510010701300403640301401c1940542141204c001810321442e0032100150303030361568055502914125064000c04646904403207060100500450000000e5818440018241c0703449a00940466111010341c50040d41c13114110380b0700008 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 500187356 1250 500186106 500186111
    0x6120305070f290112030c0209040614012c2502070e1e070c021012110301030309061209030e010e12010c080925050402090a1a18010e1003 61
    0xa41d441e00300e12004410400030421500c1c1c555040105250080c12454425243c007481d10585e240c07181008032801700d19001c3c1c0040c18030010030025041407590540c109010300001300700e0f540d400507140b02c07214003339004030b00098001c2d0742c070031020016800c11a80820300c507502d103199080603030001c00f4810f0b05c005c242c0403158002910146003402002050010001d80426030305516050716800b110010b114021800c0c2178403800041e40c0b46200b1000300201e80d5004003449184006040b044403a40d03a027081c1103407251f5844150720040c14a050245000314444d80d281d500041c203000004210340942401c002c481c074100854a000290000d0003c510b1550130720b08114040106000034081e40ba8541078200b1552070301c43c805400ca0b0b401006544100d11003803c54081800090104000c0d0364071402c860000401720764144050701e09070300184038208008040078500c5032a00c0402081c0e0142410310749901e8000641f01c4410049062008000307003090030140d1040d00f06001081000c190070100004165 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 500188606 1250 500187356 500187367
    0x12010b09150a08010f0615050703091703090312030a111e0d1d070609080d021b12030309030d150b07020d0201030f0c021f02090a18060b07061e06120305 67
    0x1c40c2c062495000f00384050007400300d000020b0b082c50003860780b8042c241c4030842d81000c00c10101c3c000d80803221104e80c0340d40c840460a1138080943c5002e800340003142e0032400200442e00c920b07a020070426407080391036442c2a50b00d00701b09200c1030440f0180100308568074800d000642d4600700c0100e0400091002c0488996503220703035080c4a00a04400428a104151400f1280c400074000204002902d4544d211105450380711401302d0342d1401e0031104840144d10418004d540e205680300d4142c03000001520a96810301030a911604503001112082c0555002050105440b040d6000d0300d112441903041d502000d0f400c040c1112564452044003a0060b91070704c40d0041164820340c4000c048640c00b080800c1240c0c4104002500c40703124090742034940e0080707010340c8510901c1e4801c80c0d0700030b1707401800038000034508200c0905004500b106040d0b00c669038280001d05801844c01824401d01c607000000703010610f034003d58120395450340071807240761510509100a032980d2035030b20719440c4c1505255881d10f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 500189856 1250 500188606 500188609
    0x903030d05011503050601080c160807080f03090c0a0302010c08130f060507020306090d02150903190306090f060807050d050304090603030827030702010f110a05030912010b0915 78
    0x600c03a20421014040c40c0500015034003540b2090000b811030300d541e09111549905004484400c8142c41134007036a1001c0217142d51100d800c1005111940c4103400c85402c2415a4440000541104000001c8120000304005070b0000502c1140b828690446449043c5802c0d034000074100c442404000b81091000036011004000307023003507040109004540048001d413140700051950f000088201d00901c80c080100c0c4100c1030106103412540398650041110040c4144058000740d0301130080905400b00f000800d2008401d03045064111440b51004649203251040320b40c102c50000e81c8a00500c0d142560a103c0e904000c5414401c07074104a5840041d02c0c25800e0031340c114030441e840b102c0c009107003e00020816400c03000041c4100401b440d15001b421000480b44018042044041072981080218038015801051445c5a0000d6441c2c03a04980340400b5809207080d00b800381c00c1d20203a0010842208500c1e100340030301140c0404100900c02c0e800e0150110721062030143c50b0707008444a003008a81103 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 500191106 1250 500189856 500189863
    0x31c0b0a061d0a0e0c03040201140d09020a08060717060103140f010e10081203040c050414011a130306180503030f0916050f0f030f0d050d1d030a050903 67
    0x1802001424244069034a1501400400d50841c2010361440e002c00c511490b450003040748400c070751454001c1d00301c503a1554003e0711030703501c000d208906008060901c400700d4490729010b40343e1a00d4111000948120a0041161a9465070310185150380171004009030190f010100b0826041034051001681d100c520040c3e01814070803500c3c000e825008410444021000b2103107a0484081c010b900f95a500c84a9190142c07070324602407084554804c148d0f150318040c0e540011640980120102038005850781e002405440703121080c501071000410042c400340c12081c0c000340502500c0c0b00031610741074032503440d011030000c5880f003e0016980e40c941e0b80401c03501c4640444486074004150b81d5289001c0c1a1101c2001c01511f4000351803042c0b00e01a80c80d6601c000d00c440913950002c0c02c8054450146007001141c4a90442950f0140030f1f0146807c0f464200704000c21110145031281e9440e00f464140101c100c0d010700c405685504078815050124070760100c1100c00d03d4043e80780c080d43d0343c2d0603480460300c0e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 500192356 1250 500191106 500191121
    0x9010c0321020d0506010c02060f0702010c06060b0711091605030405070801020309070f08060403200a080301090f0e01060f0320090c0a030b040627060506030f04140a05031c 76
    0xd8900704507440c94039494841e801014101c0a800041220b074a600c8011911400000f00080d00b004d010451110300e4030038040034040b024414541191014515600c0400f55246980f095400e1403000c18018208002846211351030b072000d4844034601d1404080c0075031140c115214550034000c0c0040400d050107401d220100241c403d81b8000e55890406000c1103523602c41c039100d104d151200c40c1001091104022400d81d0242e0b82644d104032a081c119824a48100c1c80609420020311443d0511000a50b02c44040c40c020020b56500240000707812509000355140e840014065034034181042c8140d0105503542010740b17030001e402c5181009103401a1041048201d24664402c0c18402007000100b4400010052810240d800740f03c0c0003007000c2030005a900c18001d280c18201c1c014907045203014400c02a8000700f010031800f244031981d883c0403c18a600a95000341e0920000e010802030066004030104a24003c2004020701d000b15100c0070f84074051511b00d0a074540140a003214401d00c503401226 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 500193606 1250 500192356 500192387
    0xd020d090c05150a02121b151801140424050103050604021e0a090209040f09080403050706021f02090f090f01080105010915090c0c0807060203060915030309010c03 72
    0x42900101d003081520048544202803151000c0161080410f814805aa03a0103925030014281100c4801c001035158000e090039603404611100c034001c0210003000701008407250449084464145021002405c0840c270f203d000c070366030520f448581c2070300f54162407990080d04100100400800440f49140c6030740a04601e101c00c0741030400100074032501244c1c160285108640190800c1d405080703203070740d40000014080d8880240603003000091550f4004045034180140001409103910501e02e0890f030301070505a44401d130100d01801000340411140c4080d101c01e000411b07518071041a002d10024000075011b07107050300420f900d0525120045040b1003110700030300c0c41c0114a4400c400c5003820f003003441035000941c00d2100000351201584101c840b249a000a8945801d040c40c0004c1c0c050401214103030100708420704082d02013111440500741043c894200540d81e4142142003080216000d009045444003c0615114a6600004a8070380781020f090171103540c641030070141d40d050750450740c10 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 500194856 1250 500193606 500193611
    0x2120f060f06040504110f04020408010c200303091b040209120a060b0f030c19050d0f030e0604060e0d03020c040c09051c0215030c070807150506240d020d 68
    0x140641440411260701c10485100c1c4940039658500c100700c00d840c07080d68094100506000007080e1418142e0098946543c041c0000d440d26075181e42d03017030849640300802000600100d4040d041c40305400207a0214203e950011030450402c007180c280c407089001910b042c0001c10409810761504c40350180c0d91009002414100d14400b00703081d19848a1020f20103c070440d140c40b0070540d403490048001c0c40160f0001c1e00401020f80c1101c10302c003500c24103440b030b5040c20017200c600059560310001c094940910a00c00c07100e5401e03c900c1c01805034a2546200340c482d001c2440140300d110f40c0851600c0407814200e039010726031141e41c103050f030070038544038040758200d400c0160380703106290480d82200845402388c408180f003440031003500980348030b06c0c08000c1d440800c00364400054072080340610b070429142c14103680b51102ca45d90340c00e51580b08680403144aa442d00f640f41c900081480754603848078090364206443e00c5000d800034140c0d03001d01c007510ba001c0d6020540868420300ca60542d02e002c822100c04 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 500196106 1250 500194856 500194873
    0x70b010e1801090b0f181902030c040905030c0d0f35042301020f0f030403260412020c030c040c03021e090f010f020a021c23101a09040212 61
    0x18240b4450803111034032201100000f082e25440aa140754900e4032050003d0300c4e89544001f80d8440d5010803e00c240c0c0c1c0340c4030390400c101050381c8901c140d6411034400d400440d80d0b500c046a0903801c0466129051091140c14095222030980012074101d04141c507280c111456008200c0c8001854804a17140514542010801c010425070521365080b0403807102014100301c1c4900105403d03031003840345a007401c100038080c0715481803044029581091181c00d150100d000008001c105e485184054071184140d26028802071001075a0b13911142c050350b10140c01204040004643c6e6079080d03000c16801180c0c0d4450b4203880300d00c01e038141c8108500d084c5400040140d039038000c1e4207540004141074800c1b0140c59a1008640c0200198200c16480d41c003d411101c510780c080140841e400d65011072460b11071001440020104191032800d4640510207082d081d95080b091803500d00a03201e80e9a100340380c14203000c600f548429000100900803103440c0d07a82d9490b88085a40400482d0981d0214820000f4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 500197356 1250 500196106 500196113
    0xb0d0506060c07030f14010f0c03060503030403080f07020d0f120909050c0307110c030d0e030d0c030801141503090d08010b1314040f110403030206060103060312050309010e07060c0203060606070b010e180109 91
    0x20602200e041075400b8004203433500101500d038400d40c80000c014900801100041d50381d504007030003550380024041c1814030b0700c0d43c4a03422031605000003254034082480c02404541d400c18008401303005002010041031412801c030080324800a07280606000c0341026004010000300800900104040c0039140e110071451000f0b403040d90b00e40140e80c4640100b10500705410301c55a000d18001d9010303604c409007a4a0b00300308110100400b56280d4001500000b011310a0281800640c06048120010300c1140c01d040801820307420181c0010050744010803200c0804001440c0d5041521181c00c80b58003440308940001d4001c1c4039141c0c1c514002410b1642450a1503401780c080e1003241e00a409442e451b540b0900114100d40741c502006001e80316101201c101d007441880a154803170981c0740002518002100100e24042495106e08001000c0035001030450400784039280d080700302a00c01c80c1c1010007554680c4417212050081407065161235002448501c80d0b4490180e0021009000300850701040c00c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 500198606 1250 500197356 500197361
    0x302040c020a0512090609120703060203191503170a0315030303060312080c07031d090f09010b090c0a0309080f07210516080a0e0a0b0d0506060c07030f14010f 70
    0x600503180e034003030b04132501e10360601c000032242d031010300402203440d22201c54100000b0005010324500980300d001c20200002d0802d10085002e036401c080c08031a00c0801e0031b110410354541c1e4001141303071100914200009030340302180c0442604c1280d40c65444000c540d44c100c009004a0070a82071a0310296000420315405900c15025240aa040c12070301074041602500d007400c0079614000105410443d9801091040d1441000f50f20540c151290300c124410016594160039141c00c91702584800c2402041c4000348100031052405a415024526118250407081c0c019088003206040d2603a1544080182120894281900405070340d5110081800c1c8401e1760116010810303107205c00c802102e00d15500480aa4105c03254042195105404595403184540c10542d00c4c08180407012000202d0b9a481180d00000342c95110300464903030000303100300320550300060541e60081a04010315500c1b00c50100340e00c42607030b402440c58154004036141080e0a0003001191141c103501e4100600710280068 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 500199856 1250 500198606 500198623
    0x503030a14060a150f050c030d1b030603020d0b090705060d0207110d26040503010c020307050c0109051c0f060203040f1a010b0a0c020609042c1908090a0302040c02 72
    0x20034440606a6400050250207150740c06003d6a24a100200e400c0091007082d20b850080482d240447c10203074910801031542d00507000290000d5140c0100c0500b842d1001106507029840b4501886101d1451f00400e0180807060005864040ca040000c2c205010800414004000c0038204a6891004002110094006a00c00ca8100c03080400c1008645000000c8002c0d258000d90b143c8844421003440040e001501c0c0358610350300d82c0510002840d61b0707007071040c800c0d0101550061955482d140c44c2050070b026203208054180a8408001d000342c0d10780207108a12041c294030240c00600d41400c1401c00b8070000200182081c0c00002040b0800054145040c003d511030310a224800a8402c00140c8450090141e168201004e000200c4024410100384070018006070605290000380b4000c02c1c250794045807180103601c1240d291441854140b03009004400361403001e4480c0074904a42c9030862900144094048000032805101560740e01081400a5030300038010416160b00110113519513540 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 500201106 1250 500199856 500199881
    0x40f06360320130207021206070906090803070f0b0a15030c0503012a030c110709020301060f0c080405130f0e060712182a080a1e020a060302090303070503030a 70
    0x76a8014034802c6104100381141e40002066040c03001802c0207200002e411040b41030340e200150f007003074001d245000c0c088680215000e0791000c40f990b051440182a00c107480e4420140e550040081002150b96102d40d003203540e61101503181140c071000c6100025120340f0220502e04681c140303000042107140324096048031800d034000d001c54035401c0c103c08500d20b0000d40000c1c103c544519545007540c443e0307200202d040e01d2820000071500808050514105141e00244c1003543c1c004014048160400f0900100410b01c0c9807080c005802c943c1c80788101e000b980b142c240102d6500e181d0051911058000c042181c1d03503160108100d4469140b219070b924800e80e0a04081842c1c116810703001d1141d4001d481211803091078a2400032030130360303c00c144060a0741c0783c10b800c0800100b92107451034118500100929541d002840810700e141011580c1c01074000c0d1a0341d6410f8100352240060301c40d14801c00490386030b030030010703140c0340c10202107400c512500c100209603000000401080c0840396101015041c0c9 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 500202356 1250 500201106 500201123
    0x2030d050a0606080f04020d08090315090124230103230406060f12021c050304030f0b013002120f0615030105060102071203032c0f03040f063603 64
    0x21106080c00a0620546c0d02035008004607503150007080e44caa008051100c40039003240c052007203010070700d601403206890b91403490b5101d0502c200c01d031098105c09260801c00d411110059850151700a401c0c60740d0701c80d919400740c852a00107515a000354003000c000700390350a58548030781c0c5c00d0282041c108011641100e02a00d000008a00d8001c20304042040da0045100c450f2601145e4081001821600c911504000c41e00826440007882c140040d0008512403c41180458403502e000c031451b130016000445001d11214020383c50410544180071513500c1181f43d01c46095550020805403800702e0400c00561143c0300e510303425000009091071040c0e0b80c01c20802d840c003d80404050913910181c0c2c4e030500507800360b80301784080391f1002d10040b81c481c4207050010368410501d107520748003403984003040084081071101001000e1f00380440400a044030020314503003810030728ac450383d8091038020001003007941d480d40d007000f001083d4502d000c806090311904560400381151000c075001030004036280507 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 500203606 1250 500202356 500202361
    0xe1c030305040b01090e0d0305040c120f061a1c210f02010e0c0609063004060c02070602061b0403080301080f1e15092b0f0c15090302030d050a060608 66
    0x171588568021050140c000d40038800c0f140004a02901c0b0250082e61a1707802c000300000c644001d205015192407161200c0340311916282080400c80b82400c80c45901c03018003851030000c0d943c0768840c00d100c0c002c2d00348181600d50000d092010002564900202da04480f258044401a80003003984814a076158000c0c03010203405c00401c2d4482000b2211680c00c203e040c088410f0301c1c54444094401c00032088001a1440d01b43c008151002c5031708042d20303190309000d20030312041c000f4034040d0001010850009240061821400944c0c50b0f000a11301221461b00c1d103070601044a00608a9000b9500f044036940c49503103405c0c0240d128a40b00c080107000d0300c1180c1c102c0c08150401d0031a000304504400181103c00d28440c61403011400003414503110340200604030b2903140801180701e01c54031404c220001402100c0707030058030140c480300d40001804a44810500040c03198000030003440403901010a07000310030300c0d050749580a481c808950107800d25081266204090b80114110340d1280d0321141d058 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 500204856 1250 500203606 500203619
    0xf0c0504081209060d051b0708040e07170c0a0c05030409050f100e06090705090d0609111503180a0b010b0a020d030501060c03030e030f0414042a0e1c030305040b01 72
    0xd12880464981102061105400c0c45c6200d070b229030b0b031002c414101c41c0402c0030707011848000b0780d009030030441d40c00340086810704c0a07a14003151154009000c0c02c2c41082555204a03041c51820020583ea460680000f51000388600c0307039090000d00c41c0e001080300e0b20746da141e0300e500d009446c1c2150764091600f0a100000c2207014a0390010f02140c00b51480080716032a40814406444401800f42c018407030204160700241e02c4c1d00d0400300803107003d5580002e2014440c030b81400c4003d102ca41c00c6109420356001800d0303601c03500048030341024030680b00d04654200c1e401514100b008100c0094080e800d84400000e003006024001c060700c14207075095030050685003006404a8000b030080c000066000912140068043d501a00c02c130002e50048a04007080716030041041d42c040d0308840240c141003101120b49040500800036400d84a804010f0342c080100519941030540001034010010800c84045054446454992051804000507003401c0420704000d8080c002c282c404440d045440d90001406 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 500206106 1250 500204856 500204893
    0x30210060b0403021e18070e09041203050a020a0f120e030a02030703020f0a0b0402240f0d0b03030c0c0d1407030303090203060a0b150c070e0a090c080a0b13060f0c050408 75
    0x50328802081c007180300801106c000740d032800040044040c003000e6011603120b607640000082c4114070030041d04c2a0718500d060020165100a0400c50455005008034002d080e0040c0380f07180031140d81d03c1c100401224120400001d030013580903a020ba808005441c0c403020354044010a100d0740280c0032206e901d540e20220599480b81188040e0801c28000d0205006103800300030300401100c192424112a064912140c080c3e9200c40c1d49501c1403038000511a22418090042046101d0300310040e600b07000c2c600a65949921200010f42d100324401d08100b030401602850242c100c80c00201110381294907460064000c044c641c505a02c688581e0001981c05000350150740b1800c00081c08500451221600e003003855000807113407000278000d0030400300d5109110a01c0500c42c0103583c8000c40c1109840c241005c0211450b0409180c5405c00c0401c0d40c003055540c0070154000e5203094180f00004021708011000304070580c1020103103410315920183c01c8d9403000240c826164000e0540d210548080c03184680c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 500207356 1250 500206106 500206159
    0x290708040602010b091302031e0a0c06020c0307081b041113060504090f0903020a020f0418050304090c02030a05250209041109060402120a0903030e0601030b01090606050301031e030210060b040302 86
    0x5150b800030f446510403480951031075504032802401c540060318035072f031620340e50829900120300592003000001c42900e01004403c0081584c040a0010100591100c0003140e0090f401c05005a48a504000102d82044210b0352804911100300015640321b110042956000380f103840ca15909051224a48295900c03e10303008035856002442c1e0b64405030309001300800810311642d80300ea0340b04091485142e03c0d40040300070078800e02c050340d55142071400c00c400700c4000800e41011940184040c0c1042034000040740c0700d144080341c1c000d503e0115100000f1012064110013074000c160f102c00e0004114286c43c4158464204940d412070360340e035181c1484100d0141c1c00046860344070b628081126101240d11514600b4040e180c08901000b10a12103894404281e004580e00c0c2e250500402956110388110400340c60540f80c86031442d4550b89a41a00c4000c410b01d186c00c881c1e00caa224401c240c0208200b0b5060240d9060a1010315500c030f400d00b0385a0843c0c4030581c01095584502c840400c41400000b2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 500208606 1250 500207356 500207359
    0x2010519090503100b3307060e010e0c010912023106140a060806030309040203040b040b150604032418020108100b12090f061501030c0207290708040602010b091302 72
    0xa440c00c1c2d08000000003010b1091b090650b0303801150010b460050480c0003050f00a001e0300e0041489055418950300b101c030f4240e42c015041d0441c0d07001c004180e034440c002c2400c8407800740c00301d85104858000618080d201502159460702155007200e01a40343c01d803000050701d02042e0812034a83e0f600d00c1d020041502080141d07000804802c1440514064401b1305c2c0c1201e00501143d05250101c40800c0803039206035820785a00e1221030412007006280075413143d002d0f1540c85c0c000c43ca20f03102000704005000da800001e0403030f500d103203d8902142d1034251000151740103002c1800088200a28641004040c131f030140d0000344000000741014030106161000c43d40110841031a0200e400d02900c0c00300405050048280506590300c030381c240d02009194002d060030240c0c0f0111042c000009001c5540c10030040c0d00307540251908100a550030803052001e065002c81c000020340555003844014807800c28001c210358000318000c40d195505600800c240c0c002950b50f90890703103c03038206410702029150b00a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 500209856 1250 500208606 500208619
    0x50d03032a0f030c1b03031b02062502030904021c1410240e0d1b0906050906030a11030a021302030a0e0f030712030b040207210e06031302010519090503100b 69
    0x3001c04100c0b8011144176500900d4005401d4a01d90b07054100f00360914004001a40007005100b280b0910b0800547d032504540c070398503c0003204e000040c2d00c80c051040300920465010500c00c0c0300d03208052002604840007141044a601030000680c0c0a41054a140e11040e041d0340c80030031010325215100f000d0b040b0b00c1602c002101d8805600311109110600e01d82d810080ca021860700064000700306548a28901c09501d0101d42004030b4a01120b0381a803049205282003020711045840200d880c12a0780e400030541100fa001c0c2d032000c20b00e00b01c200540290050500d20540102e00001d5000d1809107990380d40a000d0581da038121607680301410480380704940c001304503003400580b010280410f0318401341404031314817420400040498026642c00d480d88a0100120326407140b0000a0450080007401e000713607008800341c04580540001406c42000700440858401075a005000f40ca1019440651200006465070001050016540302e202c0c028400c011504e21042011700403502042d101a185 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 500211106 1250 500209856 500209877
    0x10519141b041503020304060c09030305030601111914190201021507021606020a02090f07090e13020306040309090e03030c070312061502160e0f01050d03032a0f030c 73
    0x79045911071095252a00380000c200c00039084280c4010545416215200140c491030141850416100240d041030100a6034600600000c0d40040550b40c00110a20741600c1c0785043c240d1852500c101c1170391b05801602c4404150303041003c05203007840c05000c1c02042d03841d046000e000440d10034421030402400350300510000b4551201501440f42d0142d02032044414101c8400e11183c0c8981881e000040143c120280c00310035401c1c6091b810f83c01c8241c0f108022614036100c07100070f02e145850301540701c00503e46004035005800c1c1d2480c52140c2c81e001000c4e12070314101464080c001501c02c0c071400030440c0c10000306c061041408419a4426000042c0d0289420703015034045a01c01141450000125943c04000c02d000e450650f80001140442c7c0080444002c9006041004c05450f03100650b00607000e410401d9407159491450704603403043e1100300b180307902490198054200080b6000406180a00740f480c424001400041c412005455103250b80c014080d003182039440d5807410b0300200d62500135 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 500212356 1250 500211106 500211121
    0x1050c0904060f06170a02040f15020607180b0c07090507090f0605040b070204020c011b180b04080a02010e03030706020705100e1603030f0203040506040803090f030304180b120f01051914 82
    0x801c946c03000f0034100c010702e404d4a03025400f01042c0e0b10b0f004000a81c9004407101d40d101d07010445140c0260f041e06040580100c0800030510781c01050294200ca0400456001e0f8405400c00007040980076aa10900103031070f220070010030040141c41800f00008040c0c8000840d580030700129016200903010640ca80003154003440083d60104210400e2507503103030085c19031000e50300358501901a031581c40320f00c000080da484139900c040361703040b01c1c41101c404c0008104444001030b00d41d4910f0b034203080500b030058080e400241180210840a8a2a40005241020401c005c1040429681c00803410042c02110b00c44803a82c5400d000c20a03800e8407102001400403038040c0f004801e9000440c411217180c40d407950040741039a0060351080007154004254588186080703c11807545403010f0b00154281031402080d0018161944c3d280b075803107962051064001e40380c6400000e031010782e920455000041101c1918000d040c12182d81d451400c1c11101900450320f240122800600c0481c4001c4007510390300d5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 500213606 1250 500212356 500212397
    0x70501090605030c130306020c060a0b010908190606080d09060927050414030f0d05062409060f0a0c050705060306031515030a0f03260c0a09030501050c0904060f06 72
    0x4d40d0030a14410105c00040000c3d5a400100100071f4400050269410800c2c0d4110a0750001c806a40c103004a418040c0800000001d01c040c0d40700e081201074508641070704040000b0310854124444074010f01016400b0590040d01e01c2003200d01e01d9941881d0190340c1e90002c3e101801c2c0070b803000e02140c141e40c0c8d200703505d94842e04030580080c0102c1d50700c41861102c00ca0b180c507540c481071174200e9007140400d101c10080342034803c107035000205a4100001d18080912036120942d0300000820f80d400100c0c00140d41e84402c41500c42d07000a0680b030310303500c0b910181c0142c0641c0c406401202c0b00d20617203401007840e0402409603401500f020b40148842a100c00c0c07807400319a0014044414a81c0042603d1011340d010000009118000c01052104a5060800400040416003103076025820024040ca05110b06102c003603001010711050703a1501c00d00402250703504c2a50388050050760034541400086066880182841041103408105d860f81c2ea01084c500300c0e205200d04e00c045000103150108420303004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 500214856 1250 500213606 500213617
    0x8010501150e1f11060a0b0d020909010603121707090303020318010c06020f030709170c040b190f1503150b1615050106030c08040b1906030b090a0302070501090605030c 74
    0x9082c0d502102124845840c0c00c0b640141600001300c18074100e59020307105000554100c03c0850080c440c4001c5500810ba08c2800c41384000c0c002c02c010f07000550f00140079400b1070090b550180b40254184100d120041c4420016a0a00c1e010b040703041c0403580c080d008407920022640d25801450a010b41c14a003c0e075120b08030100c5906210300051098001403541c40103207042d44030504440d80740d0500755002403000a80780c1085c481a41010705c088038910300000c880030544030031980841c20081050116003048002584030041050000c0003144100104040d00151130040d0104103250240e004101c044c0d034050207070f001d0031506600c418001e92201038010702c00580001070300b0b2982940c50b0355078610101803c58401712075944500503c20140c0c1406511100c0d029803a150100d0f0525444060100001410318500941c41943d6100d2144054202d0801140c00c50700310401444d1035514540c03102d078500000c50050180510200340e035805101a1310039941d0b20b603105030443c0d4030041c064101e50700c0f0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 500216106 1250 500214856 500214859
    0xc2607030209060408010221010b0304060b0409050f070305010c05130311010c170702130209220b060a020705090c1317010f020309101b0f08040f0f0f05060108010501150e 75
    0x200b080088a48610b4001c0004007822000165141200460301100901c0641c60b4000350300390300b0040014141000a50b0b030000e4201000040d01140000010300516012500030030b0707809070842108078044007045000490380600001d0008407800c042c101c41c94890140c5014540c03a8941c402c3c0003081c10005285e0003144181030803881d000180e12000c14604030070f20b032000c080000190b0f81c02181054000f4045041ca40c060035410802c4610005e94032100d4401c0425001d5001041c2d00b800319200d8000c084450f4000d41401d07a030f1880e6035002501d0b280fa0b07008090180000b203005c514840062000c403929107030241300030b5130740b641003001c0e42012484403100daa10640d214030f90f07083c05158a20066001c3d0300b003400103129a1046c1c0c0d5002040d00c03056071040d8222900c080c5140740d441d0300451520042d900a1401c1021540d480c605095002c00c0b40034090041e60420307034004100405c6000d1002440d000304120781f4160b90b0f400c3c8903800d0721401d0062404840d020b50061010b1405618802000d040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 500217356 1250 500216106 500216111
    0xe01120b0604061d040507060201061802030411120a0201030b06030c031602160b09030c180601210e0304260d11100e010501140406300b1302040c260703 67
    0x590722640900c81900c0503003004811407400601c400c12501f000220020907140c0000d020552410741e0003503000120100d10000f15030004006000c000800b2410f001c1140001c0180c450344004808081d6914117680d0228042490b040300e0002d14a4540b0aa034070982c40040c2c0240b86686102d25500c2c0214641c4094040d4422001d1a181140d10030000d4809030001070710315030b2515034042c00c041c40c10f0342d1241c042d402001c1150f5205c20b86040304211a500c5442800d2264451024004200480140c4180b101c8010302d4a43d52403c03500c0080000c008856108140030107043d91003a16004034400e071a00d04035260300985440b0307200390003000150076040ea41c40c1901d40c1141000301503c00d80381001907080d0b46966400043c009070b040c0c540c2d42c1810b0603098904100ca2418400c440d0f5090062181000011043c4400000c62845c00c0e01c018035042c1e80880030300901e0900200d60a040c00c4000c0c0101d100b81d060500000e10a4030505540e002c0030010015200e4111742101d180340c442c0310180c00201010f8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 500218606 1250 500217356 500217359
    0x316090b0102071805070806010c0b0109020c03282a02040b0d023001140a0203131203050402090114091305100c020304030b0f190e03091003150e01120b060406 70
    0x4100c6014800300f102001404a0945806c0308014440b0358010f0080d1b06019400c11000007281050841303e055071400c0ca4011b07560600c03000c00c149140a03002800e1000c840e22107000c1e0f2048204c090b061542402605e034100c0e9400c030455040c200384800d44424200c1070403804d500c000742c40c09800694400b200030f8201601d80c4030b40d801040c448440d540f505002e01604408180685840170040a4507002d00d00080100d8217202c508000c244802601c080f1040d60040086483d0059820045c66065889a000000b5540d181705c0540581821034041e48600d440c1000000c0024220385000f41e4640c3c001d10400715591540701c848482d011700302081d40c4c94881c0e03100b0303008001c0c901d2050310340a050540003035440e0340c5140780c10501200700908071114030484100384100e07915131480401890144880124109420084c3c1034a14041c41d01001d50041c1020400303030075682c05500001c104590b501048002c6601e40c161f8000050083c0315200c0d40302891032400c00841c0e0b01d0510550070080c0200301040b0303607 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 500219856 1250 500218606 500218619
    0x20070906230315130b1e090c0d020d05030c0109050d0f020d0c08030711060712051305070302090711030d0632010302071703090c090115021c20011a0316090b010207 72
    0xc2e17001c0741c0f946c0e41441001d17801c01d07a0810801071154407411b418020b0103421307aa0800300c2d02d002400c0e40000d00950b500c0d402201044001d0041d01ca221440070001c00461965080035a45ca12502c000007000c182140900c00300b41d40b01044001288699848200b1069090742d20032440794001041741c410000381c0c4694009109060201c03034090f0201d99111800700500c140381c0c60403030340094246102075070880b01c404002400420b5400440e40c044400c0130665940080565012900401c1440035000004218005088980c88030041d92079481220001c140e220b03403100d080030340048460300c03200b01d80d052603160b6621079001429050700c585944038880b81fa0300b01400d00343d0001d6031a040c0316000320005045030304080054a0061510710b411500c03001d0060b001a4444a080d6084800a522410106d807031078051030301c0707404c4084e4110812056400000c070050092044014114a0008016900c00c003813500040d00030b42000d0f004440460b49103860071200c024414070341540c2c150701841c42d000030325 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 500221106 1250 500219856 500219873
    0x30201021507020a0c0314010f0912052107030c0813050c0910030c0b0a0311040e1303030207050604050c0108090c1e0a050a0306051005060313032007090623031513 72
    0x552141c400221f80000001006083d00d241c03142108990303240c0000b42e0b020640c9200480b040e015503041450381e840c1c2c0b100c41440c441502e840140126841c0d002032000455150b404030b0301c00c01c00c1d40d4407190701d40c031800c51410340c500103d480940300b030b0b0100b00c24801c14030b0a01c8409030440000d092810b01e0540c0c0b645d80d0030522200d0f0388500c12524021071003c000c241c150294084000500006030720303190a045038082d1488004d01611290a00b112420040501a604580030140c015003181d9082c9060716006a480e00900235290008510b8400700d00403a8000a911801010003404c2054101c020b00390540c118540c90003207503000c054400d00140030340326415000701560080c000800c00746450f02120210390410340c03116014100400800c0318140c0070601c60392199a161030494640ca661864a18414500d141c10124502071000005100c182d581e0041086500720310040c80450743e031444488070300f0251074110780c0640058001c640880100707049941c0c00703c2401c40400405071a40ca90020 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 500222356 1250 500221106 500221109
    0x1312060c17182d070b070305040e150d0602180102030310030b25050c0d0806010804030302090d060204060509010206010f0302030303010b03070203160624050f041104050303070807120504030201021507020a0c 91
    0x141c0d01e08440c4840c403c0701044c40024041c0c010061680d203402d20702e0303800404c5442248502000346040130045200300c8007021703115000040050004160902c1790030800c0080d807004920003903403812240140308075400842524440c0e140d43d061003801c00d00c0c58441100c0040c0041a01054016109040c2c041d1800414414504010790760380c0d40c0c5800c482a07010f40b801d0000d52100c01440394050402800741e03442000e9980c80395240c980983c90b51038000100e240080f0710003000381183d00108000c030741c080d806006444401000d03402c442041e42d84502000380800742c0e00010b9019002000180a55100b02e0001d42e0410082d20481f4035040440d48403d0342402c48101c101e902d25254141420407850a110681e400d00071003901c1031003146400005000d503d49940004e000d5511000740311044100c0d13500307a070004c3c1b07005820f89948501c2407900342c0b5941e1105008845e03112440c0145032059114006a03403e40364181c00070304940414030003c3d0381d92403004002404500c28480c0d2040012031030030f070460 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 500223606 1250 500222356 500222413
    0xc12060906060f030204290909040501051b0711040506130e0a0309060201050610030e1f0605030f1926072f0f0f0102031312060c1718 59
    0xa005810560001c049030f007207014150800d801480280500b0040c0000c80001d0450000041241c905003440c00105008502c41140e000c81c103c1c5c2000140541908054072862050607409140390551082034070a0181c0703480076044070711200003200a0300b4687d020320307007120b001402522034030304055006e800d0340c8401141e0380d030941014001c074041540100040c00501010300090201e841d240000c112001d140717090341001c0503101c0390140351100f803c0c40a50303129401000f2607000214030310b003202c1c05005144900c44c0284141481d00b07290140c00314180680f0b0740c000c01c4000540995482e01500940000601c8848429200ca064210150030b4000c001440c0301e441d4011000380d06c9a40c040749103424040c81c44915500c8034401ca00307907607814404014014200d42200b22010b000004030301e0350140355012400e0381c56180010031080344042c07003800403500c28001480203451004d4110746141c3d0f1800a0003e1a00800201c1c003c3c0740301d8001c0c1c28000e80f4480440744005e150340048100011400700c0072 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 500224856 1250 500223606 500223611
    0x230a030515070305090a0f080c030a051c0b010206040b04020301060509090c0a1403030f0f0c07030f050d02030406050d0e1213080613020108040b0a06030c03080a1209150c120609 78
    0x9100e15078088800e207502c0446400d04105031704d040451240c80b440d40c018000c20344007001030070740d042110103030a5404a42c1c05004903034071a407611101611a43c0309060041080151917008400d00344a8003e69060940603406002c594549640750065045c014108aa0554903038101280c0e0f03440740d20000d486900e000005100550001085c402d0303001c081c0c2c000000308490111404401c6d100042141c40c0580503850700756a84401070201040c41c081c10740d9100d600c3c0102040041400081d407403028025016000359660a85590700c10790741d9104920030740c004110144500d1172100b03259032000a442c1d0818050390f403820303140100320f05240e200c1c3c104d55512407481502070001580422500341d018a40e034200805410381d540010b40350700030080c0010802c180300ca00090210791190400002190702c00000c00d8000e450703207003116458001e8541040060750402c502d41c000d20950160812840d0081b0180c4220303014000a10041e20701045141f05112000c01c4d000b48400c898803a0000030a01c0d007000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 500226106 1250 500224856 500224873
    0x10020f0304140705150a02150c0307180e04082203030819270516030b0a29010e0402040f03060606030e0a122109110307050d0309230a0305 61
    0xe12008086412050700507400f14400f4840d58071200482080c48607003c098a03140d40761404100d1500b009032a1010341c80c4002014040f195005c54061805010241c907801540d0b400740600c0c1d0032021180c89505008002c00300818041503079100101080506803903006000c40c0340c40140c1c1d0042030158003ca002a80c180108002c5400341e002448030041001400c0c03140e100d03ca05440326a0781c011002d210060001182401007003020818126441c1170128000c40059070303402c08800c00c401c1280d00105545c2042100c102d101c6410403030799540e071304170180000c8601038500111580c8003411030158019a0800001c03420b250045080703802588145008204a82030840c020162101e10b800c0f420a0341c84604501c00241150744041c3c4001002d240c9061810b0010711410301c1128040d05400000345022027a1090181d802c01d0380c03402440c1038040b2483c01d0303a134030107201c40c16110311030207400107400709001c0c0308005003003100006922802440040c42004e000c000b40b000c5030b06900c1121998082c801 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 500227356 1250 500226106 500226113
    0x9060103060b01020102180f0402040f17160303020a150b060d0605040b010c0807080a09170a020f0316030803092409011a090103060e0f010518120a170910020f0304 72
    0x340b02c811060a2000b582810020441000e84403c16075603503214442e90501d011140d00c4030b034141c40081540d070856202155503031148200340d9048081703650b5a03014201140c03455100e42012135040301e071b0550081c0030040e22619642d440000714404290026211450700010356640360140500e981c0c0d100d0001522460f00e401c0108580c500002d003418042d550305210041120441681e6180350801c48070b5a46400c4400c0448081d2000d4000c2c88604141d02561914400c2c006000d0301824400d48204540e004100209a82d8105400841d04100d0705440140002200c04020b190420081e00440b400300c0584000c00c030364a818080c0c1900070880040c00c00060443c00d00805425855050081080425250100f0700c049014040540110344075103015070030000400c00d5074071004c200e0b0020011400c100003440f083d0300890603041e80b58450200c001c0d01404800088403070040454075540400c0804002e90020303000001e1568119000324420361810600070f00082c40035880080c40190349150916 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 500228606 1250 500227356 500227361
    0xc050f18070905030f01060b0403020114130b071101171303030b030f030a0912030906050306030a0b040501051902030c0414180c0d112b2a20120d0908030906010306 72
    0x17100101c80e814030804005135801c000846040da40c0a18040615000300061442c0c40e10404011700d2400c00d1242e00018408601d00240502510540038500c00e81000382c01114a1017200c0d0914021340c0300c100c0824500d205040d203100c105480307400e000c1509801d82000904114010b600e2400507000042e020310304039809456103001e000500090151202c403503e0040c0101d03c5405040248640000421100e41d0200301054681d544040500c4241c501442c1a9000e00025201000750b40030900620028445078021340380318a8403214158142481c242050b07104c6502000d10a40040c000d40c04200b02c0303e0200c502910580c040c0341090764803500b050f020021100145044c1902c1700e8240403144030040004005400a42c3c2a142000c00c2d07100800600d0040044003030520382850b05040c4400d5002036010310440c40001511200b03a031800d40c02600f540c0e0041e58042101e140c129a00d400c0f5020200d4015011078020306000007200d920075581c1c003000380c1c402c4c0e41030005a4840e070010800c0000c0d50 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 500229856 1250 500228606 500228623
    0x150909060c1b0519030512240105090f0d0314370804170408010f05040b0601031512030e0a030b0405060c0f0406051818040303050c070c050f1807090503 67
    0x15002c41042c02443d1926600d52040c01c6000005400b0f0110752018144224156141c803607501140f0010350401c04454000803a80c0501d5203400c1c070625a18640540c0900142c4400603005041280d555440c00d007000402414164120b06001007800e40390703041a41d43c0007414424620000010002c69039224104a0020f41d0510f4189080135114510744194455449500168404201100300170300450000040c0241d030009190381d840c045c0c10100100c07503504002c1c02203020701600002030f01c2d00d100440541d00079200340c01c040b00300248100046a802030054440344d0092604402c805516000120900840d500581d00b41e90f403c014003040c0301041c0038070f903040f1f8500740001d450800306a031612458080c07407080030280103022400d10315640205100036010320000b030000b82e0040c0741d82c45150118400383d80640c0024036200010740003034165802c5514643d081a1010038175441d000421840358800c0e601c0340e8101c45c200400c4030003140c0b80031200d8052102611503240a1707040c08241403521194 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 500231106 1250 500229856 500229887
    0x307050d18020619171018020f070311010b090a02030a0e010c1d030f1527101802030106080f010b0f1f05070b090d0908010c080703150909060c 63
    0x1041000d400503907400040b1090301d02c0741072800d103100c0703040c0d0300907107100c4048848171030038000d10401c200b418611945614280c0e101e100c0040150780003c980902280500000c092106108028110220340207004418a0340340140010441d681c3c03d030085a0f0030070b42511502642c0e41c010040c05508416401807120804c8210004c02c41c1c2e04601400500700c400c1d40038500420328030f112904406460500c40114622070000856101c0480c000146502038030498004244400d0740785140607280506100309401c00c4800e0003019030280008521008002c2d20081c1d002a50024842c100103071030030301079100104403100140c1030080389413182d1350039200c0034038030144540001c50031142031b81d6800c403c40c1001010b1400403460a54100819a07451150a10141c81000401b007000141e810001d01540c4d04040c0d0f681b40707184941c0c2c44035000d00360fa01440b03a100208040740000b8962a201c3da000314001c000c81c2242101c126941d074015421101c441c80c054400030785610300341210325008028400f41042 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 500232356 1250 500231106 500231141
    0x6020f0f04080d0905190504360201081303080a020306130c02011a010509030316110a090c021203160f18030305070c0e01060215100e19060608150d080f0307050d 71
    0x281901c00303403100040c501807e44540c0d65141c1400142c1d0001c040300912410b03070f505082c3e5460300c20966410102d0384010403400a041e5800003400004240705038060603070325450303c41054460712012800381d000101020b4021200030342844d1132803a00e000d200024080e680001030610054940c400d10310640414030750511400b000000031a0310000211003d040c280054011070307003414500150501c60320000e03150300000c40c00d404035030b1041e0390b80001100c0c00309808031134a05151248400080c08100c1e0040314416190309281801400751100c4001f0601074a0301c21046000100c0b80303c0c40541c55001580002c0340441d40d0b00130030000b03580f5403029100900c0358001030341c50031000959601e808192049400e00d290302042101101e50401800751245048101c09440c0c40c1c1200130303004118042d50b030211402d001c4c00085450041c1c4829008040e9214403d000070060014082e131440391010844102c3c004011400c002c00e5050041e501503182c5a071a20390b44c18070314442c402500c2c03c829401c2c40e040d1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 500233606 1250 500232356 500232379
    0x1b08060c040308030a0207020424050d02010e22020406030b010e030a0f20040c0503060f0901050a170f01020d021317060703050c09040608010b040c02150406020f0f04080d0905 77
    0x206000d003980c049039846070b42c0a6482c0d07038990340380010340105030000b90005d0922840c0c001103003406600810480c0342e000702605440e0b40d2400c000350a108450041d0100b10702c014024142d04049040c95500343c01041031283d107400980100003207178855132180e40025a181d0506886691102c2a5500f0300c40c01c400600c0e0000807a21203074504404540002c040407810011540c0094050001405202c4002c1c4104801424074002034040d03030003200d1141c401c86401444190300d151110b0400e0596101904900c4180d05100c091032442010038039000e8a8802c0820703540c1c80c5d400c01d000a00d51410f40d6500542c807455050403149036200c07940c215102d141114804144109000101d050740041c8620380450a40c88026a45603e4840e05d55100d4006042c04404500342905401486200505490820031841c00032401c030303102c0e1f001c0e14107081510108004540030804036005006c604000508882c0303080344c1440000c52a80c0f251348140700c5a004a154459807a40041c500c40060900b580c0446206 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 500234856 1250 500233606 500233621
    0x170a110616050a02070803040305060a0c08150f010201090b0a060e16120207060207140d090f030804121103150a0606050301140d03030b13020405090a1107030e1c1b0806 74
    0x150401d6024500b000780c0898100031043c801c028041c002e207031070300690341e030390382c99040c03c6440720000c0f00d82115090525103104460f62007019034034454040c2d84001d40042c001181001000c0102e4040541150b40f52030440780410540310056004030300c0d84800144140c0350070214095800c000307000d0498165400c40d60707103000340c100110b01100101840c00503030300c0e0241c0c40c1800c02406211005003e0114822040416401c0015030322141016912041901030707650940c900201a00d000c01401c01d001030200700420418120001c1801d0b1040c81102c4412148401003450b00311a0865149146010810b010040b001c2d032080344043d0801d440c05518640c10700c01d15049514841e44181d0107815464690f1061501c26840781c103050500038a10003c400f071151200c4003075009802a90701c5980764030082064501c0700e01c11071144d03281e4031900c903040112985064402c0e120843c41140c00044540d01c404020703c2207210140d000d40308650000c0c1d5002e80411000c80002c00750044c401c194081824031401 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 500236106 1250 500234856 500234881
    0x1e020307120e070b0a0305090601050301110d0b060c0316031107030209160221040f0e010609030b0405070803031905151c05100e0a02091e13030c170a1106 68
    0x48030241c440031070300360035801d60b80340352003407640c4000b2000c507003c905081082e40c16040305020f0501c05084404990300e41040508840340d590131200881c4040001084800c00750300b080550090040c50700342403101d100072203411507014003ca421100070000c0341604040d04003043c0501c545408000302140750030340d40031842040010b404102d0107981802c80c2c0c03900310300c00c2106a80056510a895007184010342000c121030700302d40500c980300c50076000b02103552065001e00c0c0b4100c81141d6a28a6501e1450b2603681e80c03844040c001b9500c40c0501880031a01b00d00400c02540101c21100f076240310407042c0b002e000301b128000f8005071100102038110b01e620341d0f103050400710850850041c2e00705000752841c2c003500e414904001e00000604100c65036444500114081c0d12042c000d8a140d032442d510504842d55030f103550740d41100806220030104901e400c0c00903205494030b00c03a0500050060a644800ca0f142c43c80c018500e0940400080e40300b08507520551b01c00307141c01100018220741c14841c01c080c54 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 500237356 1250 500236106 500236127
    0x302040509070e06071a07110102030c0f030402060c1204030c05040c020d0e030f0a080a02150702060a0209421c0902030c060706090605010b040810050c04181e020307 73
    0x20450b2030f0015070042d5881504490369035502ca103c05500200c2d09410552809044402c3c80104180c81542c0520403018003c49114108214005207070001100b0f548126070170143c0182c3e00132a040c054078808204c1004a22035010940c070038103484910b50f2614001c2d030490780d003040780904c2c2000460145150005200d5000080c03c2c2041c4200900000100b464510564010012449290410310a004418000300b0740a200c5500791004102c612140848c2c0203000d59020005901070700010318040e62035405440c0c8140e0042c441080700c0e0440c010100b48074180b030ba00c44071006040f8600391502c00107040c012a44103081060301d06088a0003202c02008850180c200c0f030f80d07a2074200b800219682800350f01c0380382100400e0251100781c10b0034500300502e641c000894001d4904400880d02c1c10208083c0c60403600ca02000f400c0030411040404040c01000d8135404da103c100f03007c0801d0b81d00800189008050740850300240c4a280a00d280d42644030a03815a040d051041060004003031b0300543c0d045 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 500238606 1250 500237356 500237371
    0x90e060c18090c0c01020a080103120309120f0c06020a08070e01110a020d05070b041206060608100303030c120507021b0a0609210503070809030d02070503031c02070507080313060302040509 83
    0x29203d9940d400c50309824403483d241580103520014508403100e410155035030589002e007080810031404448240c048800d1380c60064034903039035803000c0c21181e4810003030090716090a1520300c1c003c40d055990a410380e0001520103012803614010030010b542d0103075285014030000d1a1110400140542040e10303070605040190040c03509881c0d01c024400b0800c6440014901c044109070f5496030f4041ca4103c9544201040316420f080c0040028185d10a40115005450301504814a02c0c5940d4060b4000c100c110310145c1480038188216401034054030460b4803901054025207200100c000855103c0a07884003003600c2101d89400601099612904178010343c0c00c1080d01d03650900464064a1000c100e11710000c01520000400b40c040085000203084180c0c0c00b40e00329031002a0000060f0b07100d01c3c1501415416901c280440c40c005640b8002444094590181c0180b8142194031014288461034020200070fa0000540c0c4012590b101e000100401445c98114102410440018580f043c041c0000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 500239856 1250 500238606 500238619
    0x70f240c080a02090307030c03060b12010c0509042a0806120316061503050607090e0a141f0f0806040c06110d05031017010b01030e03070b180a020307090e060c18 71
    0x15005505c080040c000034640003400c1c81d00096982c50103034050a01c40e0b0b2003a0190354000c60807442446c0c140a001e05104140d12020b0404100c0001d200081c001726503036806041815218400e04100d4029142c240c00d05503484014910301903052101c1014001c4a100c100c0c0c0c01044030498004201340400d8500d6030054010460110035aa03034036010b00307079820150490142405002d0842c1e040780f0100100c0b1043c030402c440c50783e50000120100d4503081c01d850389019040c0c000034095040d9051642d041c0080c80c01d82c58686d501d505414450104940190000d0781c44002072000b840400015000100864640290b9119001640c1501e81005a0a5800313100c0c9c00301c0030030304208107103009102034030b400d60b0040080d43e0941c034000d0191a10320b542c140860b1801a1710b261101c400f000f11042c2c1a0005001031050f1903948402141e01500780001803240150601d070f00069806001c0a8000c15058034040b4030385000b071020500b0404040e0165850b603e0412440100c40c1d01c40c807203803080d4041201c64 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 500241106 1250 500239856 500239867
    0x6060a0f150921230607031d030406021608060702210f03160306080303150d1e050f300a03151d01090b0607020d0602070f240c080a02 59
    0xe550b000665080b08040ca01c41d90200014085507070740c0003180c18010f1504800000b2001074182030424003204010b070503004240010100390094002404100d00c070001d5410250038861030034159081a0042030051f0415100010f0040c0e49407802000b07003521402802c0b0508105c0400f035030310041c0003030003020a4092813102410004080558502112071000c032562450a02c0200c21a02d4034100380c0804a031034280041104080081941d12541d00c13074640150103101141041280c100021007150040250514038001000e0f00c5540c1140500c2200240703107d51301c05102d03509007060300000b0001182070b29007100440d244081d0441913142c40144841d566075800408501911089003990b034004176042d80010a4994401d074414268141c200000c550790b20b0300d01e12400e07101400745040c1e00100a00244004d850010000e0039024070a40b40107181c03150700d5980301c000350309122043d12540c1041403201c0780d0b0740d13114803007008000c41c00f002085620b1222002804008000e070800c903445a01159 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 500242356 1250 500241106 500241149
    0xa06060504051309021017100501080a0902060409020a050310150203090d0f1703071715010f0c0b01030510060603020c061503120d0e0c1221040504090605010806060a0f 74
    0xa0741e138142c01a0980c1d030a2421070360041e007040020584406903402000002e00d800c10b0780c100a000713480059440248546403001b1a02c050102558242ea20040030400050202107601c010242c1b14401e4840a40303c0c60641c850031034503401544024401c540312520300e003110b40c2c080116805840c003110003050089007424a48101020040002d1035040c80354841c4080120301005503102d644d0907540c01007400d06440052810000c2900d45910b403125048804416600802851151105520708083c102456031250500e40d02c00f83d106540079040503031211141c1c0c1c090b008100140000303040035850040388501343c1d42d503080010300301855808900c0c030109003641e092050120100c0c8030340e121516140840401c00c028240c100c1c984806105443d80b40c0301c1424808449400e000681c0041c0c01c91050307402110828070b500005c41c40f07010008100118665542c4c1c41145e8103a401210001215814400b50501d06040507150344d11400c88024204205952a0507807015103079900b585041e000f90180c03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 500243606 1250 500242356 500242361
    0x11403191509140312060a050307030b060622030c03170702220209120f011a101803120206070207050a0f030809040212011e0f030c090b0a0803030a140a060605040513 73
    0x102c0c220f15000020700a13802e10b049965480c015001100e03c03d24035996242007542d12034483c400100480c240c20001096403034858040c05038006542003080a0208100b01824560400c0d00202c0f450715a00d1014814001680c003644418403100000f2442c00d50355400181c6030904d000481005007505a07107110040d041a01555030100000d0070304a12020000582501d90070b5440c0d2002c599880d00a0b00300d5041e030840d07400c601c00d40c0054940d45018030074290448501e0039204c0b0340c261640402c680000084c103031840090440300345e64041c0640781003200303000b418035125500451107001c0f8900300784030b0380e002d0000072001c40b580440242d030786000f060080350207409109100c0351000310040000a1041021040200c41404803880071045912103d909802512600010300f15071008001808050900d9000c500d5000c030040007428510f40c0c0e1561030707280d80d000f10b40d00e80095480f4545540401003d8240c0c039006101200184075590924038010310034002c0f031040c1885a05d01c1146020b2112099 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 500244856 1250 500243606 500243633
    0x10519021524030c090705070f05120a0206090609071707030213050106021212060907050d0f15080304050d0f0311120304110f030d050c0f010203011403191509 70
    0xe0507248292406850790b00c00075284900280a1800c80d451401e071a02d004100908100c90080414443e40c0329544219419000150f00301d4280c45007083c00b50104400300101c400e05082c480c2c280b170362074044441c02414424080c103078025981c428000d0080381c3c01c0c00718151080e0baa80304281c0c111200e20303150320703442c01d0100e5002940100145005109030b6213590492410784005400b01c2d41a1480d01d18070b40c800d44100d510000c1041da24a0205805103403500384540c011101d0b00e003440c1010003d040e0241100c0301d01c0c5801c00d0386560365205d90103240344405c46c0c00c010f00b80c607009581410b103008040340000303040c844001c02001110380c0392410140103803a1108501991000c4030f141c0c1301100703902c1a05500c03e940c1551710444140d440a400d241100050241510242c00b0300f035609a0f9100583c1c080e001241ea0300003600074600c4c1080340e48000d10140d0f000300040d1680e0350401600a0078141000311140e003110300100c0501000c0042103c1407412040e00d88441c0c40020144081c2c1411501140d61 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 500246106 1250 500244856 500244883
    0x50c282307030b0c04090e01020406170106050313020f03060f0a0b100203120703110c070303030605090603100929102c0702030403020402120a0b030304080706050c0a0501060b0a090905010501051902 87
    0x7e0880d548a010015400303081a110951941c1170911120222030f41c10b07010034413a0307000050040001800f0a059007d603005006d00c081c0c0284400400740d00000e0070001704481802c42100258100000b0080600545201d140182d807900900455054025100e100e086d048048440e85a404104480e00c40c1e40031050300c20385d40006544401f03101210f01c1e112103851000380c00081c20081d001c01c080c0b608607606030050308006c0082841d000f14010341005056107400941c1c10a04900c3d81042c16150307000a1070982e581018048002e00d412007440800c11802d40001500e411414400c4025542844905620145034a0301801d9642c071103000302e00e544a10b0b04025001800840c40013001d085440c0c6190107420400802d004103c00d01042c19641d00440c0f117000007a5110750410403403103000300c000305041400481903c080c018035489503400d40b00380d0762210b121644006680c070b00d43d0768010349610180c400400180500d5140c100020700d540030740460701e1041d240030700b28042c010b4001c10526500c90381d07 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 500247356 1250 500246106 500246111
    0x6121a0d03020f01110412020f030c060f040305070812071707020409080d0c031118060909011202120304050d08030601122901030902030a03050c282307030b0c0409 72
    0x16103207002510b800f00c80960031001d6003007041c60030b003041140c01500d0644984501043c03920402e0780800c9200c10201e044181c25003d00c0d480400f0b142c4a035401044001d0318045411b035518951b01e800c526000310795000e4100c6401410038960b40040340d40448a41e20740100b0611410308640c3c085035079030311440c0320003540300c0e2601c55041f04001b6007030007900090741d10750804c0005400075001602550312186030310040c21010403180d000810240c810010b20980600040e0904a005c008118486030a801040c0c2e60050f03c0404030440c030b00411a01c64640243c0003a41c182031402000c0340058000d2000141506000300c00500c540e48509014401030011100030f01503001e40c08005000284094103500d18019650000000ba50280c001c6a94280c1d001d00205042c4a450303c0c111060b4201408823a104e01640e84400d041c2086d1003082c0503600c17644004002004200e1400b601080d0030007007a052034600e825800040c00c2c070080785000071650000c01e010303104d6985801e090024031070703030700300103059407 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 500248606 1250 500247356 500247379
    0x93f081b1c0e060a060b0a080a0e010b030a0b010f0614180103090b1510051c1503020307060f0e04230907121b0803040b07120210060b07060b060406121a 67
    0x5000203000b84c001c42c8005010024503499440c51100c41c40b400c20320b500401c11040205450300444d82c04100580340e1800000b4918448030002800e00302c03824010398019204400502c45a142170502c0d40c020702180c227101d4122408460002001c2c01001003448070745a520001e40801d9000384c0108441c941e10040412a9140010a007004440344101c014041e84170000481e040c40e00a10456007040e80c15218104210030304002c4601600000716110103404035614000016101001020041d042c1520751a0124814600c010400003841d007a0900c11424013403204480500d441034291409880d104007001961010070041c43c1c90340c941d00000150301a00400d80601c80d003940180c031201403048040f61021756490301c1c107580e40510300440540c10008c20114001032202981c3e28004039060040d6600c0805142000701155507030352056401910008014041103103610501c6030540080701d04038282402e100c0020100c060456104e078846d41d46024400e020b0000c0180710400341e800401000d01036 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 500249856 1250 500248606 500248631
    0x2a030a061107050d1103091917030d050a062d03151e0506030c0904060f150510030c0801290301170f0609060a093f081b1c 54
    0x55210b0307201076945016116190000c1441400400c030500c000701c00850070703c4002420001204000503c4a416400001c40024145100f400c55400038004402454682e2182090103003a500010308007000719160038000d000c414003059003044081c10003141482040b844146900f614040b6030805407034089024030300181040580c015401e440044072080e454180329481d440141d6005540d800d0f896000100310741c05604000b8961980140641d90108420341d04529000c22501020003190028200140030b100301c2c2014000080e87d2140741c901042541c1d90210000e12040040c00340154244181e1095030310700280d134060010b42006800c40641c0c95942d2120300703410346040c01944856020f140d150341034816000c21075504c5240000c000d40380030703034820000388010048904111402c0c0194043c5400c04035107020800035842540601e88825045221154440405640500204842d030003c1200500004011070314105103105400d48852150700d00e003e60484418aa00640c0d181c0032105425 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 500251106 1250 500249856 500249891
    0x1403210a0f110a03060e130206030403021c08101e06120b03010f0207020a0f0803180a030506131704061407051903050711012606120a03202a030a06 65
    0x40f2442034600300110b40e0790b060b45d1031460808581c00841c07071185812a8000d03041c40340c02580c0c003e2003441612100d1209154021204540e00d00c141d00088400381003150280002c11024050f017003074401250300290035a12004940c609004000c2040b20840b080b841d0001d05400c10111600010024001e80b280303046843e00941041c0320981c8540300740c3d040090119a201c11200a50390311002030740c50300c84503501c001010321a005005c0d0704078094501c000301041e0f0500c1510302405800d03401c580c1080c41070501903080d201c48104a200018100001c224032500316200106804204294640310940340c00c000d801c000200802410300c100002c0742500300740d400802407080c540b00d4945101d500004100440d007041c0148054180c0b000200c00c182d586e020340d00c1d00c5c0c1d03502020080a00410800d00840c50341008419101140411404d248801c81c101386030061044c8150140c000b4980401c800d0455514000c16145008800204030b8080520f41c07400c2c4201c6101d0303900300f44103200044c101050280c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 500252356 1250 500251106 500251117
    0x30c0206090d20060415050a090e0c0d05090607090611010e1e0d03090c050108060420070c1d160e06190e01030c0503010b0c010b0d0308041403210a0f11 67
    0x5040c141a00f0350400c6141803015070f816991040d042c207460710740480003aa100da0021000200f8000114000207401080c40d1724a8801d00c039030540c1030340756141d01e107038601500c8002d071084803550003440801039107079401001c0504407031040c900b020406445504542c01408001d080404a000d0034a04441d041249501e040a42c40c0e040c0407a01d925040300d1084045903907a2400504042c4008010131030f82d842040c0d8a0740181000f0000507040b100c00f194600c6002000c1e005007882600400c1c401d042c00038040550000b09050324541389290402402c84c0000c50008013008032103807060082c00300c01c5110f180031204900000d4011980c0350000000c0c40e0b1558100c0320010000785400002e100294800c0c024202420b442d503d50606603400c0c54003d0319a074001440300e61071036581e02d102c802140e561000c0e0b560652b0194551040c3e40c1428101520002c201c811024501d074800c1008000c0303000c000f0ba2005846c0190801204c0e15141c005080c07028102c141000c0b82d403a0f0a01000c603120f01e209000514 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 500253606 1250 500252356 500252393
    0x31a281508090f101a04060608011d130201451401081810020706150e131511030901050702010c030c140703030207021512130b04030c0206090d 63
    0x44030341c2da42c0500c1c0340d0b12811010180c0e8590042e01d0000005030880c1c224000c1800544650009849400041400c95140303070702010000d81150010007800c0f1070050204a44080c6125844003880c05890f0700700c040d4500e00780241049940361000405003000140d074161290050b40c0d548100d048014154039080301313621b02c0480e05800c40b50014800020710040110403406840300805540d4420304411411120707007a502d02401002c0c1141d0130046c907440148042c0f40325140010b11091612034030000118240c11040d6084042c8041c481107405c1d1290b44180d05901c45074102805a84002c2040039000000d0004402e80001c400e1140d080b1040d01b100d03101d025681d008214004050200701d081c0c69550391a0004110309151101d40585030100800030305019080143c54501168081651584421090030304507401140c034200340352904520903004080d06112410b184010388a202d201c45014100505204d04610411b0071500d9603000c0e0b801035400204034645041440c01c20102d040c03458601032 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 500254856 1250 500253606 500253617
    0x30414151e0603010204080f0a1403090d110d08030108010b010210050c390709150f050f0d15020c0f190b191d010507031a2815 56
    0x851000611106562003034070349515045036810514035035031510720090111034065408020124400c0c1080109022100217280204000c2040781802d40b074000000066a60f039400811548105554000c400a002d0790040c20b020303500c0c17800100003602d104a4030303401085100080700000702d0800640c003160707001e207003a0252010380d11b20034496403c50304c00305c2e004d6100007414050306a403110000221203c440d0005045840f250001d105c0c03100f00d441030250840325038050403041c0444015802580202881000b541040c0c80c14016409031890707060080c1c1e8000e920381c0306209001c1d40c590300382c103007100d411062044489004080075006980b0101015101e440b9559191401010018507880314102d08c061011140b22140e035440311102c00905009590310309041c840301414458070502d0f1040601c4800b507000108140c2046080d600c000704100141071500d2910020511031462040e1b10850494034403044001c0b4403c850103800a420903e151968042c1d4081644454402030100168150701c44 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 500256106 1250 500254856 500254873
    0x192f100509100c020933030106030605040c06090e090c04110702151305030a02060a0305040f0b0c0310060305090c040c05120a0c1709071202010e13060609091a24030414 74
    0x400010415840600300c0c1d0380d034443c0803c01b1101c940c00c86030560560050010a00c240e032034962006584090302c041e55030180300c0108000e49074020b000b88005041d6107001555928054001d1501c4a59411040d4080ca0f15558540c81100c43c1c00700300d407404c0c2d9004203ca000c14174001c903080c0b1903801200b10b001020f180110041028034002403c0c034001d6500420340b03850410320500c02c0b0301034100a0000c0300e510400700c41140000c0d040e60802486052020515034480c43d2075280040000c02a500c1a000d00d0f02d42018000210f9010501c6002403d042d203000c80e90104407001101c0318407401d803106101264550900611910310f40210702c0000741643e40303100018950104003a481801d071610341f13039503201a030304228100c61440c2980300b01e801418580c10541c0320501055406c1290045e070451190354500600a207500b0590013000b801c914402000642407045024107503103c05039109120300010496905800a01900300c4560a81d0800c01c644078141407030320140900944000003028044d00d0728 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 500257356 1250 500256106 500256121
    0x3f0221180115170712060902030c0f060d0507021e010b0301050a0b09130204020f0f032514090f060703050d050f04150b0111192f100509100c0209 64
    0x500c0382c25105100b01010220300c2d219880e80c000440624481e0b250090610019800403c03054070528203014a030f0210300c864a03481010b04204203918000c1c400c0e00c254038101000e0712400c096540c07080c4c1c0c40c034000806d6111004240d00c0d1203030300040d920028801c1c442a005100064004140c012401c0e0024049603d40760310031020766401284080c0c11810550000d00d8103107110f06004012030000d41b00526000205003669065440001c0c96840c03c4400024021108d01a01c2c502c0100f0141c4001c80c80c0138400e2601c0242080d8480d03004800424000c150094283e480e035107805a40341e00149032507500e92003481c003c3c043d60042504418100d18080c001600d0102d00040386225a600c54484800409400e001000406a40c02d045042041c1c007105440714410400000c0344800d032035111a50818510725000e10309132259640150f4044404500d8481a084040e01032003403141243c01da401c0c61461502160580030b410314440c2c3c84203215050102d800e0704010a101802c1c0241c0d4010420b80e902c80 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 500258606 1250 500257356 500257361
    0x3190b090c01020d050f040f091a01020f1009061803020d02070f0f031502120f0109060b09060306040902030a080a0f1202070c0303180306050411013f02211801 70
    0x24507a80c00358100318607541c03155104a00030001c26601006c0b050030141c03a41e00d54114079035a0b400c0b5240240da261042d441000800011402408092006204140c00c1600154640d5035410000307105a890328004010064a9000100040340c03081350a8072004541c10025a00c11002a400002d409002c0e004030701e1005d40035200c0d0070307146120748103040e00d441c680c0c442c1c100341004100c1c030848690900c0406046040041e0070fa004000c2c00b900d515044d410202000200c078096884030329421002c0081d20026140c0380e0550381e010000701c600044907051800424102015404020449280040c102c010640c0090b402c08008007682d499500c40d03001b90011500b01d205100e00a00100400c810800000307203d042516400c0354401600d01c9101c1c2d40ea51008141c58050b6805c580c81610341e101411b103035920180007030103030040f07050813024540a540c910400350703500c801c00901c2490242c60140f50251540403500006d030409905502c90540010b01042804280d80f1800c0004c420a0070001145050 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 500259856 1250 500258606 500258623
    0x140607090612110c0c011b0b0f0a090203030f120105010806030a151104060305040b06010816030b0f061209060604270c090608031201050406060801060503070e03190b09 74
    0xa4035040d4565041250948110051516000c000b94a882e010840d00c1c500e000a0f1400200560081481e0210f01002402c0540003a5450300c031100360400b02004911038450342604502d0322203640780c00317458100c0b40d4405400b22560103034052200003101011388291000400d60310744c0501c4426003c1e40c8a0b0011911001c0980c0e48980c140e00041c1d43d071010401045602034403184183c4000f0386e11070942c0c4c2c8a40503410560142c2d02283c1d0b05c808000c02d2100160000e640f0a07800d00e0000c1a52411036407006210b00c0e000442c004050b0745140e02005ea480700d000c0070515a2005203a07613111101c000006660280444950401c2d000b20800309140b030400380134514034a1454a00818490f003c42c04140304003a4038403090b55001c02100000845552074403d89015029002c003855941941c0c01030b0480340302041e03000307600442c42d000b030801581c0e80c8030046038107440d0185011960b9484950b011a0025103921410342c0c58015040e0078100c183d035121160402510521130301c0d4459451040c0e0a0704c40c0e804 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 500261106 1250 500259856 500259871
    0x12050709032a1a0c071401090b0a0918061409101e0905010603020405190605030c0a0e120d020d02010207021c020316060e010e100c26070f1406 63
    0x2080b09181c403000c1118100034401260400a05859036101d825141c0320041018912054600142019000d6014020349025100c40082c1c1000c0001c4a00007d040d0320300f80c42500a2580040ba1081a41c1e1141d030141c0b0040c41100011030040000384518002010144100740b013090140303040d060f003810031041042c414205204944881ca1a04080315142000e0385a0306002c00240340340032941a00740e2050a020340345e996801a1905d0406041c030070b40c5001200d40b00c4a121a030b24081180a501904684d0700031308041e80207440e2101444191034510721982e9207a40101e540100003801d400c006901044c0d29010340c07c40d14001042c0000303900b01d200d02d40001e50080016100ca101c80103800603540041c0c0d201808890222408101283d02201240c003d640090b1038032120704669a031204a42c1113448084414041ca420502c0024045d9034080000414414100b030745070030b0817002d8a0901140340c9000c9025a90f0700c030140f40a60400407225800c1f18480801d0100c561480d034001950b074400d022 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 500262356 1250 500261106 500261123
    0xc02070e06100c1205041d090f0a0f0809011103070f02031b1e011e0309020a0f080d030e01020c01060b030105040501120b010e040501090215120109150302010518030106061205070903 80
    0x140d03125a8680803020040d00244031080000044560fa0501f90364418005030b0001080350038010f19540c1016a4a10b41990951080070040c003c60110952540483d41c400c8e02203940313074103020050710200a10b0344000b50500021541c3c00c01c1c00741d4041d050490510860030348540c0c5410220522000d03111080780303a008810313052500b50408e50a10000048101410201c5480c0c0c0c003400302c8082036600380a580002511000d0010460400184c0302000d03002c40c20f02e024906040145990780c030395640596504040e1030305107000c0076110a604681e81142c1c650002d0106e640c40c1e01c4041c4103580284550740c01185400700001e000504200400c080e240c2c0300d00707120540c1e480c010040c8039101c000b03030095801d9540d44036104016940d030710030030942c400d020035101e031a5030400c4908004804d0580c00741c410780e810300c1001141c51006100c46030a5a07424240203480e03145c600443d031251101a0941501580703044804141e860b0492801906540ca6150138004e9565890040303a5042139817000031700000c0f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 500263606 1250 500262356 500262377
    0x5070f0903110f090c041404020702060307080718080309011b080a08070e0301020316030f0c021e070306020301062f0303040f050c090a0f061e0e190c02070e0610 71
    0x1002c041610b00840c1c001828425400c201000144143c0403d845112400d800020200040500403185210000048404508200c441d40204500d0f20006000004015200380080c01c0030303009962501d0402c1c850302405511a0711411015503d84c81003000f80d002c00c00e100d00640100c00f400030072480c5c1c0743d0f2010080e03041c8111110141c2d01d00b00090800d07810320404c03616555503500c0c2440558030541401045181e903401030f41c00501103480301c4c1070b00f408641c1084030290301ca507000074038841602645d0400d203400c100d012030400d08000c200d8000804d074034000000090b000e5403064140030700d0800004000700b801203285400c581e003c8035805404150b041403000034082000d0003881c44480307015800b0f9601c16600b03800040c0c40150101d400580480c0da840ac4800301843c1445640090042d441644600900001952002015030720641100d0560b4500044054546400c80044400038003414400c120b481c031006901c60086001d012085025580080e42c54030300084400095075403601e41d400f082 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 500264856 1250 500263606 500263613
    0x109060b16080c10090c0504051518060d0c0801051006050c07050907050403140607080a0e03030c0903010b0307061112030105100c0201021c030e07060305010303021f0b0604061205070f0903 83
    0x26084031081e01028020701c01c440c5051404c500440302500c0c80364000500303250404d000c00c02101c10290085500b0781c00800042c01e50388444d03c0702c4810001600414205540c0d000005040ca41c000b040100725105045001440d00340540100740180e4201102d4040c041c0c45803c125900d001d1900451540c2e40024402c2040d0700700b5224694002159141562509850303440d2500c80e0faa4000040c20b590b0b208804210981e13910060b00741c0c001010f100c0c24850500316404880e175038003004d007000d00b01070070009003c03200daa4258007402c0050000b90694070002d9440001a024103940301c1e51039040c0c020780041d006a0001d400899040e580000e25203070b00304041c80d8040380c600f08841c108034154440c2004c3c003c1e03020392502602e503080c2115500451034210b800203103403e0002e103501c8030041c14108001400040e40101c0d15040043c400c00301840c04034401a644000f50688200d05500200e0001d008a0060f52019100b00388131070040c4140940d460712481241c2074030840c200301001903440101030001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 500266106 1250 500264856 500264873
    0x1b12040905100b07110406090204050d03030b0f0d0c081002090120071a0702031207081c06050d0605070323070c0302030903060a060503060c0406230705150109060b16 73
    0x400e0001c0807040149480f08045095a0300c100d406843c46144c6a00300703042c910f424046c0002a143d1a00154280f80c41c1c480400c0c02480c2610000f81450748a02c4890561f072124508410041d4008045490020240c00c08061080c140c2c0541e40c10781c0501c00c40715070a440b03140229815a50103a641000c02040030101c4a40d442482c02c1920150107a0403000904250aa00d10b600e5035600c050056503441d510300c105803034a908000d076000102004d002000104480c9000d880d8603080c288050400a04401e01c643c2c010300741c40e042180e00410708174420060007902d610203803060969860030009241b4507220303030000340ca1980444294070301520001e0f604a116001281c540c41c0300c0e00403a070401404500180c1031102c12596040c1260b82c50508000340d1404102840d000380c1001e416910741410040020300148c900d140721601422300d00d41815035203050300d0864070310342c0d000015203004070315040c0314242021080c072801c01c4442c00e103103011800c4c0c1d00c0790040b01c0c0f0b03c0441d10243c2880c061036546a000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 500267356 1250 500266106 500266111
    0xb070f12021c020d0f02060f060d080417070320100f030b0a150f0504080a030e1210050114011407020f0409020303030a0606080a021809060a050d05031b12040905 71
    0x2180560102c18400e1007155111075030048194014240804c0c02e14001070298410003c14421903100609000702c011449505a400a00031345a400e00c041c0300c0d060100e294881c0760710072000a5968507040200d448081140382c2a03d108170346101a10341d543c1604150306110038402544907003405940a4894065090180849407600340410203050b00c0c0006141340c1140c1c1d01c018404c00440320490000d56000000c030441a00c41e0502c1e40c201410849060355400c40760b01d0042c180300c0c680e21300307a040d69164041c040548504030110341c6a410444102d101034a030a1048104800801101c240e4640c0201e0380c4040c42c440301022142462a40e408202022044243c0103800c1a80d80c114100561001c1c0015881120b00e4400801c9240c40d218008219000003480c94080910601c101e5211541c90b84840e04035880443c0c6584664943c03000281146280c1d0b80a06d5102c4c6a0240c0d0350704021020025201d4010071403141172042d001181204e071500305031810641909801c0101b48132004560b4001034 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 500268606 1250 500267356 500267393
    0x3050d0b12030403030203030402100807090b0f04030b0a0c02010e01060b090103090602040e0c0c0d03140406050a06150e18060a0e0c0909040606231011010209040c03150b070f 77
    0x9186221021680d402c643c0950401e600580000080206604014110446041061402c900e40d03291200009102a090f40961882c56600141400313001115105071005590400e40c105068184100c11074010f1a00d44060320240d400c013450391108180610880b01119149040c0c28035000584004600034202c500049030710660a202c00300e0400d1840c4101441040181c80c1c00f6942c148201d180b80c47e16103640d40c400101428121040b00040c1c4581e130031500a5401300c40441c0b991903640c044030150006030008111342c0b108003c132200d440e81c013a100600c0d0b01ea041d0390180306036040002e51751046004a520503000703882030341c003008403404102000b0b6205801c0340c078090410170004009004900183ca060340c40075201d103c2030044000c04048a00c00504403100030401240b44408109003100760400d04081c00051318084140c05401c3d0110342c1c600030700400c200071a85815002a00900d00039040b02c0258504c408040b0b2480c02800c200e500c004c0e0040041c4044009039601e0b0300114103402d1096 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 500269856 1250 500268606 500268619
    0x152202120f07030309090218121903180806060a0b0c030f0703030f060b09010804030f0306030816060c090815100b160201020f152e06030b0f060703050d0b 68
    0xc020340354148410380056a652001d414040c2c030f142001440943e054200741c9444d441080740144070841140e9508403d141a41e10104d998110200d072800d1260038030b240f101c520012118442090742c85080d0040500ca000744038604151140030060b40ea0a08072a40741c1c001420540070f0200c1100c2c6c01c060400c100c8980202d9203409980b021421803600000812004a0f40f9040846000c01076401004007521907040e401e4144001400020201400a40b002e814001c1d03400004008510a4001401858000c8a4196141041800c1a2170110740d91000d031241d501c2c256a0821007803068203190f0880e0580802003200c68003540740442003a401600032030403048000000140e150029029058040e07900840140d254007900000e400c12290494081e00d03600000700c6000a5040342d5045074010101e405801b00b40d40841119410726801c00547c0680391040c020001201030f41504618a145400d87d02602001d0700340f001d100c0300d0300070090003c01041c8240000c20608180d41e11003d980c20008001 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 500271106 1250 500269856 500269879
    0x340f08030a1b0810060c02030c130f0603082508032e030807061a0114130e0f01090e0703080a030203090c13140c1305010c030509031608152202 63
    0x119800d03070502d81c4810003051006041000c8040e00000c040020030403418000c404803825400280c030b4100e15516548940c405003c1e00801c40440d6000d90380c1ca80380d0310b8007048410780700d00309021240c00241c42c103150800140c45089803e201c1c09508440158040e045605545900008491601c000010841031401410b404a020784805000d4001036014404c00d9a8841341c40c20120b054494006480d0603180108187c62841d1b688052032556800100102c3d9031114039040c2200b041a840350b020603c280d0920041c0110400b410310f01e1412a005640700300030704401000c01c19150b0b01d40d4400600010403d0000d640100c0c0281c004690015109050340c00c01591540080c05840540c1c8440c0401a658040003502144084502e500300c541c01107410308001080140c1c2e500702929004060401a400c0f040c8002c042c0507005841e25004000c0c19030b001e10450450700e0111000302d10a00041d0300c2591450f0520086000c12240a42000650b040f210484080d205a4590043e20200c0c0c000248440 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 500272356 1250 500271106 500271131
    0x3020a0f1101020f1c05070c180212090105041e021f09140301150b0f0403080f070303060b070b0f13080c060105090105011704031206030206340f08030a 67
    0x40d0140d01c903411000c03194903000c000a161007424015450607900c1415101400303c030000820304540c250b0b241c070f03507518001854000303074002d0b0b1540007901c0b48203019001201c80005401502c00c95071059103050f05c0341e485040e02800e07940c0540e800b40000c04031801440c1340c104020071500b03055002500c0503052110940d008802a5500501d02d00041c4c0d01c0c4000344400b100c0c20402c50030b030100450007400725034030425054460b040380c0e1052504c0b01d0750005070050004040c03400d450041d81c00500700340c1c40d4001524081c0380359004100c228002854a10007042e01a01c002c02c0d1084030b074001c40160001d03907a200f4003400c1c9400c007900e00c4800da61542201000911440000c01140304150040c2401c3d5151030300340507441c0c50627041070b814480b25100f1b4280460858512a074800e406143c01980c1c2c2011007002c0c002890380d07030000303508184000345540c0b81e1810b1900c03070a01c0201340741c18010140d10700350071903144070744a1a0013411106200b24000200301110003658000002c11800918070342143e0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 500273606 1250 500272356 500272373
    0x3032d150803030f0f0114010503011806150e03010501120b0f06040b0312040e060603072c0d05010e0601290c01151e060c11040218030102030a151d040f03020a 70
    0x2580c044001e04c082c000c00080c00b80c1d0907000c50040080d01094408803d0020021700780d408140145013009810382200c0b0824001600020010442c0d07c001e91480c003003480e401800e2240e007050b62400b940c2800d00010744848460600c2808130707080040d00d00c150311401c1ca03040d0b5141020300300c154480c2d00e4a01180c51a0303000d001c400080c01050b4000e541c1c80f0714109840c81c000c1401003016100d803000780104080c260700181c50a00100c0440000043c205821409400c00380300c0c0301110b038005809019840800c48150301008a0f10300d80412244a6aa50007801c05040b0f13030714080c01c142006422044010b0200310024111404014001050130350704045011203040b100c0e400010070b85c0c1d50907819490340c0d803203202c158090b0200303242090800d1890b44419000f1441440011300840d800034038055400022521a080f02000400a5580b07081c900d1000b0b02078075003201c01e6111100103d1000610903002d040c40c0304044c0a0400c1c40743c040e41e0329154580540010b020540c01c5d805904d00300e038009920f08 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 500274856 1250 500273606 500273611
    0xc060207020d02130603020301060b0408120c0f030406050d05090d02070605130b0304050a1a0705090904030c0f051c170a0203130506010b0d0b30100f0903032d15080303 74
    0x80c3c10000b45d40d4038500406081d54907943c811a941001040180804007001c40d0000d099812403406540c0d81400b4011280382051600803d1a07900000c1404200254020020850b407172400c0018021600ca030b070740e945d07141c6002070304003809a808107104010450007580680311150600c25070700c182c65910080040309a00446040700d44d50403143d03a800421003e0710884a081c002c003180c440003880c114402501364442e080485100b180c4087c0000c0401d13119002003a00c4560240b9840c0305120b9910f0800c2d40c030050b8044410144020b80b220242443c0b040505660075940032007586116194400300c0c000030361014100b880c80d0101c0c2100280801d900b0088035000342111221990740b200754080d04001c591103614800e2207411062443e01c40716440a00380c03250141080110840d908a010205141030445110102018148050070001903029071050b00464040d840600807a81405050b030844010119204d0b1201440d00030b0401c0c80b0125070040305184035520410091540390910039107950400c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 500276106 1250 500274856 500274889
    0xc0c0a050a050f06100504052502010c090803090d0b060406051203070203070e01080303040b07020c0a06090e0903070b070c060b060712120209060a050d090b0702030a0206070806010c060207020d02 86
    0x41c03504a0100309080100ca2181c100840140a00d41880304d00c410340c40ca103e2084038812034880020588000c0416840301c12070fa0301003181c2d1242e40d04100d000c4c1c041d201c0d000e174a00118504000020b50550044100d6001c890000c01c1c40507456010b07690140c128038041c0801d500907550368070100e0641c50b0400c86000417591080115181c406074810140760113000d8103d04981007104e001004440070000075a84c2050b4410a40145030362140f40032440c145a5404959100030b80420004038590803000c510156003004000c240e4075580c01c10415a644180000140304030202000550414031400301014582d206042c08074549107650002505078000c95815a010025050240e0400d40c125104089440c1c03030140a609005100c0d00050071401511000000d1040000700c80900c0c078440d6218426480e4014041c440500340880025603c0e0007080d41c20b4050b20444011400440c011400d09208003016500c0c6050781c3e03d1036903680042d400040c4100d82001640c0034410040c0d0f58041d441004001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 500277356 1250 500276106 500276113
    0xf031b04030c0e070207180905011e09050114040b130f0501110a020c040605090105060703030b10110d02060f040f020402120109051021060203040c0b0f090a06020d0f080c0c0a05 78
    0xc09048441e080d40180591085d90b00403103042100c0a4040a0f41803107050b08000000c5260701c80c14418090400789840000380c2210090180e14144642e00090a4600680080241104074418510019000e44011b000390300707440001a11000d0140381142c60038032485d210701d0601d19582e605401c0d1810348172145100c050108501d1140d55040148000006007120284000c0c3d2400e0041184500e041c055503000314000940030040c140250032135200c424018001894542c00700000410781c584940c08503145006030f0144540d421300c009a0b25001d440407004194143c4c41d2503840c01c030182850075040340c1094090186211444503ca400740c000c02895001154038602607544088413001c68000c4c5012018141841d00d100351401b0380440c815038005801642d9890b1802c00b42101030042d4000c2420150000c2c0301c55518403a030016000e0303504291242d59a00e616644240d031990b2001d644280002d1401590a688078480c0e855550081000300d50f4500e8609402961820b0020329042510244e0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 500278606 1250 500277356 500277359
    0xf03040b270615030d1d0102030c0312011e0b030a05070c0209040b0f07140415110f01150f050d0b040c05040905070315020901090b0c011803080402030c0111030f031b04030c 76
    0x710703101140b00940c4411405481700868100c030280c0240030300c603886141d80011410000659000700200c6155800c40d604598813078102c0c002000c070705c010902540d9249502c0f80c19019010303141c42c0c202000c1d156640d400324110741c0c0b8140510700400004200303d04002c8144c44000c0542c583c421518061405103581615924004840c5201143c010f081d080070449600f40c4460303003002c41000d8506460022645c010490b401c060115808a24000301495a0260f1680d50108020550018801071000d21801d8100c41da607901c4242281c0041c8603041d08031071a501702000190003400d203540d0061050144445464498000c03e0440301d101d10b0445041c0d00c2854180240705080218145519a003002907252060780030008190712414410000021000701d03d2462070348003034101c95590100304280014085180c00d00034480c06083c0d83c264064040c111680101c1e5100c1e200c210710030007044c401145071454580300140e5941c4000d191840090800301031180c3c2080c2000144020b602440d24000707032a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 500279856 1250 500278606 500278621
    0xd02091509151c05030c010e100515012a051c080a020a0e150f0a08070f09230a21120306051809100507030c090b0f03040b2706 56
    0x1e101411a601c4052101440801ca6403031203180e803188a403020360040c0c9007403c1d140c86840c60042c0e40c1c203000c455090242502e030440000410f80204083c0d8003003484551500124029030300b0504c0300a500080041641c1e01c41c3c0004640d01c07005507802003404010350760f00c60b00c0355400c01c0ca1580415184484114a4203802c95220801e5608401c061a0861401c0e00d042c0020b801e02c20b4480000d0302540c0e40b03031036020781c5491301c0094540102c4802841030346c1d00420200100341881c1114030b50089034150443e0f4100300d10490100e02983c00c01c010000030090340300d01800280880807000ca0b44050044004a07055411000c5802d00410480803c83d0602d040c2c0751420905429280301010076140c2441008030303039101e00c00b0240a00c1d1005030401c01c1e803103d210603030070514681e400101701410712042c0050994144c0c000e410300300290343d854144a0302c810086c8480d00c140030307664040803c1800800c02180e60070102c140c00000d03001840c01200c0c1c407104480342da0b552440900e9000e40110003048500c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 500281106 1250 500279856 500279869
    0xc0a0303080601030606110607110307152703020c061b15040c08150a05040812072c03340306020c010606030c12050a06120f170306060403110d020915 66
    0x1810075811f00ba04444590300e14075958400040c2890304004c080803014680f0b40d001d104841741903812a40ca0b0505442440000c0d01801c09040c1045d841e156055111403002d504001d0300e0402ca5040c1d024186050105040007140d8020b544088402c140c1080b0004c00d0300d004010164031034007140800c07101c034179060500304800381d680d030300c0754081e038014444c0741ca602c01d01c416545901c50080074000900c0c1d2030b1414803403510b000b421200009401c0480074012004d80000307e0418824203400c8030303500e08405003152000c201410303001c2c5401d0f074400d460881c0d045c1c4404030944145614140641c081005211590321000010342c02500d86580c00500118000028040c0c0000b410590605100000700d0580c0285011840714003000080ea507180490005d003e241c0091000b8080030f080d1040d0400ca60528428a029900c0c040700e4412803a8000c100e05441101960f00c54200141040e06003491502c500c80551a580c0946070f1240e400303146440140d590003d8240681550b9044c070001c030304401d090000c1c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 500282356 1250 500281106 500281109
    0x5030f01020a020d080c190201023601120912090f1d04020904150e0102090a091107240c0c11010201060e0a0c050f2d04050901090507020c0a03030806010306 69
    0x180c0d0040112205031500066154a40a03442c64030b50140e5959550b007a000340a21a40d10620fa01141c0a040c0e1443d815000b41c2901000c030001110601c00314078035407220802d101310301803a160820f140000d041d03000307814400c074408241101003210595075650000c202da007088100702140e80f21105101902200c401c0030042c0c100c1d2051000c40104044240c81100d200420017807050b800e40000508204417a90f40c0700c2c1060010206104500c0b6550040d40030750405040940240c0ca15100081c83c04003c0c00340141c070681d0368441038030786005030b00c458280882c0543c1c5030301c244104091090141000344110040041d5681e500e0300040c540380b410344400b1000c1c1d05924110ba0401ca814014400b03485c082e1030304000d0342400043d01c14007500080d01c10380144900b075140028080307070100850307211800c1d01520a648600c0b1411000f0318100325046401240a03039070300840708800521140d00c803540002e401800c0b90044030503044505001071808403954200724009080481032081c02c0d60075006680 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 500283606 1250 500282356 500282383
    0x280b10150206070801090e0f01050a051e04120809030c07140108071e0e180a0b03010b091b030a1b0f030e03040b09060304080403021309020f091608091e070503 70
    0x4881c241000004c255550600440c0c0d200c40d50340c0400d0540310800c111001d00d00040400070301180c640007010b04001c0000302c85034850343c8850001b038441074884403c12031040c0c1e4096102c4000c0344503074108403001440188036102e03e202c00c000d11100050b040040000801046162034500c807900c400050080300c000c1c00e84010301a5030f40c03a4524841d403401c0d0810703500d030303040c50a551400e08850005941e40456000701d01441c0c0b80d0310034050f508015400403c02c28005400a10000040e4418002c400304125100540020200301808a0991030001140c000c845070001143c80240880034003400c0c440c1c4207130307100400c0c0701c0070040250315054082c46013070842d07040c040c5040516264901485101e020750b00da10031803001000a08000610382510044c1d6000782420a01202d804220001011108402d034030500003003022004501e041c0440c80c0c03140309132003640505d159006406a03142c2d500548440c07840e00405810003001c0c1511003002443c20f461600405d6034a2403c410716090142c980c2610 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 500284856 1250 500283606 500283613
    0x603120408060711101104080705030606060d0f020f041d0702011e090602120c0a0305010b07030e1915051210260a15061412280b101502 60
    0x4200a0a010420582c000120b0074490203124400e04d50508100c910b03e103142c03419180c0011084101601005002a40d01720012a644913464070100359651000f125241c2d4000801c108004d00c50b50b16810010380e02401c011302600700140702c86076010070f0304650801b103560055159900d000314490709446030049018002003180350080c503d04040c00c034a8255260040340c865649034200003c903411159081c24445601d0781d141030540c104202070b80300483c071600003420720001007030030880c440c2251000b075890344034000c01c0a011814007041e0483d40d000c041056011307000000d100b021040d03101590010964a6540d10014214074885000c80900901d2078220f0041060042d600d03d00e4005041032000c400710704042440800d001e02d400c0300d07802d000740780c240c951078242d010383d0064024800b03660200550012013009002400080c0284240002c030b1588104100460402d00d1145035010081c2d0006440200d050390722290352819040d42c511000801046040000203043c050303200c400185071026 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 500286106 1250 500284856 500284859
    0x314040c05060702030c040905071e0506091011102903030d150f030503070c0909020d061a06190f1e0e0a090c031406010201090201080f071701030b06031204 69
    0x124448400326014040c051040002d88030150768042183c5c6840d110001e100f40031601c81c502d070042c0c40e961030744103810708880c096140c10b44400c1401c170000709079500602aa4100721061080050f903480701d489200500080340984214680c042c01711050b40e114150003c58050304140a0540d602c15180d035000e1040720390310101100740d401100b01c420390340411001017400c0c410445082042c0340313181d02004595000400010411101001070400c40f4040d8481c40f49055640385000d080d14802d810080d07103c030084100000240c17107607102c803d2181000c228981c3c403000840201c1d883e03600036006401ca1100300100000d00590142c0c5000d040103840c80c009a049146007004003030000c201c2441d074140881c40344500300c40d48a8480d404024000d100d0140724440301220701a00510300130b11410205482c40002641c55401400381c0d2101c0703681a03445200700c0d501d1041040c0c4a5002510402c00c121b28801a0f6141c00d03d81a01d82d806980145041c50450420790101441d10807981220300440506010 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 500287356 1250 500286106 500286113
    0x15020406020304120611040312030b010e030a030807111e0c030c150a050d05041104050708010f030b0603030d0c02060a140c0a050d0e0d020703020f030105010b250b040b0403031404 79
    0x25102260350242c0803e99003c00c1c0d1405e03001503d10505180b51400011a000080c41513440c030072003240318140c0701000f06032152401121b1844103864001c0d016400364a03034500180c030901613140c0c03041c80c41c0f82c1202d1a02c240e4401c54107050481c122100e03088602c51031866001010b00c20341801ca14203d0080108680d081c0105182401e00080741c02072840c089078545510380a07500b1292040f5100000b0049441c0624010500f101e07203442481c01289040001002075018442190584d89105c030340121103451581c4600059200400e9a5010f000500200c0c030b2100490013004225030064001e80184c5c6007039581c800407110802407041114281c0d4040c0150340119030100c4003003440616159540d000c043e20040c01819250064000138400c2c5a4441142a401f1842e1030903039100f1120101610360f0305c4100741c00c0c0c2d0001c2c0a23001003183c08000c48110300083d41c880c10520040c404071800403003042c1d2103500c9441c9044806480f8400f91000700001c00d036043c455181d4121022440804509103500e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 500288606 1250 500287356 500287363
    0x21305090601030f0c030506180f07051302070f02120303180a02150c0109200109050402070209070f02120d06060e01020102070c0306050a020f07150e07120b04021203161502040602 79
    0x710207003414112440601c140000d03400c0d00c1006e1078104086071040d06100001002901907005842194001da40700c40c0700030f080110354081103403c0108a42070811513540d64500035484204211501c032000d81c65800141c4950300c09a68a10b104c00241d0b489142000c9030101041c001ca20000740394000303d031020016903039501d1010700340c003803400c00d16190304900840038014000444003030318403800c0d1048503950003050421207031624001c0e80c0d0b40c0e03001c6540d0300501050307004111000b94040a18400141464441c1804040307042407481120780110070700c68100740c1d035030101c0b1304150301540300c96080c450141c101d02600383c100c0d000c2c07008600d0070b0303120b4460a040c8411030200618060300ca001160f40040c150301995520f800302e104403981c071000b918005d80900340540c03211000030704040e88207039054000b09004c000c84071414000c52502400c0d03030301c041d0101802807040740d202c0c500511a030101042013001e016030103c421140a200660703402e20710420044c8041c81c4600b00c2c01004140070890303010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 500289856 1250 500288606 500288609
    0x901081203100504290109060c1e0b090f060112081903020c010c020304050f010801030b0f06031204060c020a0905010f06050f19200604170a09050405090a021305090601 74
    0x300c40440d00d07910303400c80e50000300840340c1c0155801410010001074000f4040c1003d4026501c01c00080315a45070308006607038402092043c0c0020400103e1400046002c10070710942d004c40031520640f50160036585e5a22007842500c9180d0f8542c007228440c050041f080000768003500c9607490034120240240e98071141803207403001078924000441c4041c1c0c0414000e406903038403c07608100a010501000d20025540c1c1c20622071705105106002c00491954004c000b624160b903040100200345130754820030044400f030090315442e00f501c030715130018081e880301201900190142d681c031a00c0b5011580100710074032501d07811009405140500404c210300070148002c00f224494101b40717444800441c2c00b00400d000342c2c12005001c0800403101c1c525550300110303a480c070003107100c00700040340650b8100c075946d01c50407a0007c0ca02400422151407101e05074005d4503481509207040d50f40c41d62240007240a48400340c4200925601000b000c00443ca404100200c5594400804102c03500c1c02040056984806 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 500291106 1250 500289856 500289883
    0x3060b24091503070c03022b080c0f0304060c02010c021b1005040302040504080c0f0304030312020f090d0c06031103040c05010c020105130e010603140402090c09040b03010603080309010b090108 85
    0x181e04140780d01e980058150b290150351400380c69180c1440003900c0700a1406049005005a110f03480240c8414080155440d4116419841c1a2080700041d04d4040000d01046040c3c0c3c814014007030701c0e160720002940304510a15011400102c4102d0183c01e580110344500c0654100501035036010a03c00100e51840000b201c401b4544004a0802d6600703104640001e900242070600300424030400d40010810060070038100c1e2164401140c8080d1640501d000c0140003681c0402203100c2106190060040b0030444100755241c44110070014a20158042040b503664108010801043d0b1b01441032005036541c504d529403a624003907503508a10300315401001d051284080a54080da403142c0c080d0307140c1d40c682c024103200d4035445680303102d141802445401b0000b400c1801d250700c10300700401c201d03024030341c007601c0c12341d031502c440003118455080742040541060fa180198100da507001d0158070300031402030621a40e03074102004900d0035240141c9100d4010595040104164800051440543c541 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 500292356 1250 500291106 500291179
    0x90a39090c2d11030f030402010912030503010902090f040906090615030809040f020f0a0c11010327081309090209060402090306011503231023040908121003060b 71
    0xd0070400750b509083e04401407441c0d10020501d40204011040110b004034002d032035441c1440e40d01c50701f070204001403200090010f2000e0004100c01000c5402804018030002c03c20038614100310301180440d4040c410664029031110100b03c18441c140c0309a8600a00c02c00c005a003c90850300c542d581071060090560240d0740c3d42c0b060174900c01480c0c1c156410404040c0e0a2070350b80101c01402481c0854065081d01c085120450b00300e419800703482803603021403000d80e03000c0c40c40e02110000b00000c44500e8094444c0c0307404100300c2c1c03101e2075020182c10142942c000d0000b41301c41c0a0040c0031040c840140118040d40c41009014001d54001071950b044600000c281c441610103001c00b140600b2100202c100e1103103a201210000150f03883c0300e1440313910081028001d040d541c0c1d214089002c807a44110f01c110b00e104d080c8005600b0140c1200000f00d000b070821501e0714511540c0f40d02a007008603001c110b80b02007101d041c02040814040c07040a0802180c03c030500d01e0882d00b001280146900c008601c022 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 500293606 1250 500292356 500292437
    0x22803030510050612100b0412060c022404020a05040f0218040c0e090c0d0f0905010507230a111603140105010609060c1e050606030114090a39090c 65
    0x1b4055440300c0007909050306403613111a0b5030f81002c403e5048450f81101c1c9542880c0c880d07140300c0c0c40002c801c040300031460050604209080c0c4032a01e240c0c800f500c242e8015026640200c2e49450b1801410401e10300c1180050740c1d1044121419041c0600c0030342c1510a40c2400c0700510075542c0707d05d14082c03400046448600d00c0c2c5855108084505c00c0c0c07401d44c07090908000e803034040e05100754007404807070307001300002e015aa40f40c1e20211044042c5d043e22401c140380307414035151500d00800c00b61805216600f041d03003900c0c02540000d444c3c51f15141844c1c100741c420401c18401c1003900761100e034544582d40020300055040810107004c4513032500641080101c030100b100f083c00b55000044201c822000700703074610180e06080043e1505001c0350064029820041c6000400c24801c102c02e2017442108090f02d80c001c0581e07071741401c1640c031030714039034a0310800003440784081010102c100400d0111021500000c1c034008208040e00e00003004031050200514641c1681411401203841d105002c0074030300d142030b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 500294856 1250 500293606 500293621
    0x903030a0b0607060906050f0a18030503090c0a030c0807080f1f0b0d1101110c06090d0602040e0f0703061a0915130303050310290703022803030510050612 68
    0x500030200c010313000354203200122091001c90381c08580265824a40c0c1c20322a65105081d2050f10740b0200c01024407140d6504c10340c0402d110b103010b55000f030090300a40d0090000e0800142e8070010315007080c1c4807015049403c04c01d0342c4c001c1082000404404002d088058802060780c0c0c1c640011900317208116a00d03e6000315002159444034201c90380c0100b500303031444428141840320050303003d1b0060100300100190170254000080814207881300a00319482c02d15003c0502041a0916408a0360150207110118603d40c0d8681c5181c4503551618000b403a51501000c0102079494540c081c21071503040420800340c810252007201d5110300240e868042e11045169540e405100b509155000556010340100030154018000c500601e848034141c4c200715100d209211000d400201001c10030102c0c682400b0b07040020f440503140c034038080d0041e591040400003d45400d07560b0721510710001d0134017004440c1095090f2041c281c00c06030090034407030000e0034000824414415100d168004810210009401 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 500296106 1250 500294856 500294869
    0x302060f04151e0c022a0409080a02150f04021c0c0b180a09060605030609090a023601050105030a0905010e1603032c0d0f021f090503060903030a0b 65
    0x34400d07800c208104220003c08010700c88403183c20b910f00c410741004075074004544002603000c0d0010750b440003000d08070415011110451022030b43c5a0300a034540e1200d40200d1003c5000d0103612400b81c0140100980866204403000c3c0c008202c01e28210041042c4005a00c03100761005400094659004d0907042509100c0070600c5164400140d280300002c0145000d1100c41003600c1014040d103002a0b4507403204510425101103014000c0060070510018903107140003034883e41c10800c40c0c82940c030200f00d140c020a034a0001c0c07815550b00001c51483d540f4141c0fa02040703611810f00c0000b030303500c0d4650414000a2461202401021800b6100d2500c03d09100084d40401341d40001c22040310743c0a9140c003052401c4050910054000c100d1404014040950444042050705030303605070514208030740403c200c40401c455000341c038520407180404e0016220800c07403002101c03089502c0220303050302070402040d007035040d04080c0c000d80200b41403248103140041543d400051800000c141a0545000701d0034 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 500297356 1250 500296106 500296133
    0x1012080705030904090309140402040e060415090c030501050108090a230705090118050f01182304380c0d230108150105010219051603050606030105060d0302060f04 72
    0x4c2c050b140c420300e4020142c111f21a14201c40f0382d18403251810307802c1c0003000304034001da2151071380811403c2c0c00500c0c1881c0c950f2000030542e6030242e006043c2c9231245d0440c1c2c1100e42d841c45002c0881d07134500060100b90f0704600940c0d406aa038500510000055a460094040084622550714500d2000d0441c02030400c1c80460301030034000d41816000e40e500c40d81c0295460481c1d00700d10030286408085050b14146074901410b84145901401000e16010308810007028003001600700c5401031811090941d00c0c8020040c0518050181060581800b0f070703120a003080130161004803c25040d140d8003000d001103000303a901041c2040e030a9203a11400c8810000f400c0701c01c03c01c0c40e1001410161094901003220000c1c1643ca143c1c00701c410019022400c0f41c41703141c080c0680d60259002c81e0301e41305a00d02604800d210244640280c1740c0c0341285003056a442c10654000302c4540d0411010481c01d41001d20030950700c600200d0b48079508080036100692212030250080000315082c0000805201c5034114640 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 500298606 1250 500297356 500297359
    0x1e3d080123061c030e04113907030201030207050f0a0305180f0916021203090f0f1603140c0d0c03030201050f04170c1c020304030b10120807050309 65
    0x40690120076078640070304203441c6000a05861400882d4081c140200c0d00007025045009032821481e0603202a121502d500c010280d1003911090255075100c00f030005000035400700044003801540ca110b070011880303400310b0880000345000d02d0f001c030f01c01c00000da0642105d0302804d0043c0d03a6100d604140d800c2c89480088031040748200403000081503400001840c00e00501520303405034103401c808200340d0403c1400743c00d0384400401d01181426250360b02c443e1998600340110b032148104c5c4030000340301e5002100c2400d41b6400c40c03d1000e02c450400d002c40907000000401822003040e083c0c40d0301c0030340380982c000600442d400c2d513000d1a4084040201d04c00b6248010940003580d109071616041000071404210015400e00011130901142c1c4981c15018035401440c800c0c01d0032100c2e494007043d0300312401c0719496108500d50140b6050420540b86203c05a90b030103540d8603421400d04c0c882000d0050044c404d01c900e050000c000c0309188121250703031140d20007101c03135441c511410301c60300d03500030515443d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 500299856 1250 500298606 500298611
    0x607020a08030a0f02040923010b03070e04180b0405030c0d0203161e2012010b090402191a030103060b090415050c0708180103270b060a0e1e3d0801 65
    0xb400200c025480140c6100032301c1d82c0e07c0d805a0b07200d0720321384a940415919080414511602609145801c2e040b000484e82d210040100e484265120b2038002c60042d84c060b80c02e900005a601d080b4641802201c0ca40c22490006600e410040d0122012240c1d9a503070180000003040e040041c00680c1c2141404803a40144075000d446109004403003c420803400c80c41d21401e828100c902c81840180107001007140002e2940d0b03103d030303038035001d00c0401103d290300500c00c1d0b1965500407550308001e4404407800ea0041500c18ac4a42c118039000003100c50216113144a0403214040100246001481c143c003d80003c0e00072450762070b1442c40c00c4031030080c80301c01400c991006c02c02d0700e6000b4110052180c044000d80e01441103900c01c0304007484203810b400800303401c15445d020100c0840c007a105200c1d0010006425124083e648940802c0e810304140e60710701c980c169041e0200b400701062a001a00132500c1c3d0703112a610060120a40041e01c0131a071141440c10b12183c01c8035110b4400001c00006000c0c001c0203 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 500301106 1250 500299856 500299871
    0xb030916060809150402010f2a030305060a0504090c1503060f032402030717060a03061503061a06070308060a170d093503071e050607020a08030a0f020409 68
    0x260400300112070f59082440b07990403041ca09820701100a02441d010f84031380100140010040301e110340c081c503c0589203980c21a1201c401030f042d10f6100340c030394000d580018417804d040c0100410f00c081c5501c114030480c10060b620010801d9148190304903803440c1c56000048945400580c090810740c0e1103507409003684c9000000f03006100c1e40b1007540b450301501140850032102c854500700c0c00f09403445000503d400d4014100b5501c802212608081c2c002d2492845580e2075407198160f9441035a41000760007113110410800201d402020300c0c402405401805090342c20000c2040c0d80120789002d400c0015420201c0e92540720800f81c0001743c281c03840904040f1820a0800b40d0790700d504c00f44000000d5445500140060502250210b54030000b42200640480101e034800c224080044010316030000b00a104001801c0d0500800b05000e001d2640200000c41d0410a040881c014085010754200003400c3e00000d102d142242da000408140000d560b4028a1580d8002e0249401005a81d840c0c07000c03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 500302356 1250 500301106 500301119
    0xe2503060e040f0605090d0905010c0212101b020703030e010818060406060602070803090f0f0a0b030a0f050c03270703080c0705040e0d02060a0c0309080a0e030607050a090b030916 79
    0x803e454000c0c0940e000380010b4884a4683c0e940303505000c0a8800128082c6080c00f4561054803201e100742d00003405903549450100d00607003480f0181c8201006039a50300072085110b48141885000030314180044c045c0f452464038083c042200d500c1e2050b041001c0071000a5110010b041170312032504501c0c08440d00c03440e04e890205c00400d4140101c0c03015100c4e40c200099080c400108031a02450050300c102c4503504a4000c0c84802c0040808a5900118800001c00c4100d88040075510600b100c2c80080380c0c12840c80f01703003400ca41001e01007850b47d800800810040382401214031080e60480d041024100d00f016400b00d0409a25401c028000d8400103a840342c0d254001442d14181c070012101003102000c8a01c1540d42c1c1c03400c816008016802010001e40d000045511121401c3e0107400c01060b5100c0d0f40c1d0322016154030000b80b8101213002c0000b0701c0c00310f0400f0405c42d0382c40078850801c0c0c1c2ca840302151020b06100014400e0310340070740c400000542865014400c00c1c0b22035087ea075510b482192030b4007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 500303606 1250 500302356 500302373
    0xf081b034204030e011803030207170c15210126030412141e120c1e0d020c04060b0706110702120607020c01020601031a2715010e2503060e04 62
    0x20380e5140015207041d0f02e406d5050a0b02000000c413503041d001065581c2c03030018410600c19010300301e20703010b010300c1e4890001e9858040d5034101c6030125180080c6d8400c00d1b804d02070f020b09248001c415180d10031200520175803c24207604103610344441052411414103500d500d145200b039400180a46048120301000c00424100d402940042078050b41c0413100e10f44c90020b07904e0341d00f0702e8080480d03012000e040c000c010703140001c050710099075040d903820541030100702c22035140c045c240c2e0b9805d90003c80c0c00e202c403d90500181446c2c0b84201c809121031403030b05848007228056404042c10f40341d6101c010004001c086021203a4583c0d001e030030107040101060006490301d004641103070140c040d1000c0c2194540c0702184040c140c0780d02c007034500c1d009100d1540100c40c00308001c1180d01100108100f00300d004480c0100e05901d50741450003050b0391410040c841610107410391040c41110095824400c08400881e4010f062581c400110302442e1506101200503105a42c005805451800d05002c00c0c4504e08 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 500304856 1250 500303606 500303627
    0x90213021b12030402300d0c030e010f0905060906120406020a1103070c060c05030903011b1103040e01060315030c0806040b06190b130f081b03420403 66
    0x1c4140c0e0002e00503201c142002d884125402544401520807208204200d243e208207203046c1e085294000c1002544a98a0488180c00c0c0030041000c481c081020150700c10300d101c150712020320b8186503040d54082c0103019800103029442c45a0000b18842d140350311020152881d0724040d081d030f6121824541040002507102d091480006290a180d0142d4103070000110b480c40340d4001800880e1918010080b900c4405280d021141400704002003440c640e424040d40d11000000400e030210240100e0000c0d100c54440d0b2203005003a0414841000079180045249045501c40d080201c1c000c00f460301c4100e07500703c0c150401881818030b204049000c2000260b03da106500c6a0451140342d05d80c00104000c1c1186000c030850303100c103040002e01111400402501c082c410131015110503a03103407142090031962503001000d156011140b50015103440c004010340c80340c016400381890a00051264070366080744036106c9811000500181c44041e03c000c80c92580c400c07401e04940982c113103480e0040001282c0e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 500306106 1250 500304856 500304907
    0x60b0409050601080f0406090c05031b0109050a0609090e070302060c01020d060501090302030307020d031101140f070c0c0e060a03060c050901110309130510080d08010608070503130609021302 84
    0x109000200554054907204d4090480c00c0408a03e030b03070b955519040500b10091080314480703142c400001e6280c604004d20040d2000e020b030998400d00d164400102800032980c0054410098060204125904003c103501650b07224030002c1345940c07010102a03d42089030740000d4209000103080200c40e8010350103409002d0300441c007800b05581e514011603000c000307400065410b0300f0070002c02c801407901c42c4185035041e01c01e080c024084101070103904c1c00c44014090f4078080714011000c004004200c0c07001c1a5101e281410700c0c0f201c01c030319a04d41e01000d00d10790003562203400343c05021650381d0750f41e00018801150301c554140409000d0311001080c0760003607090b0501042d600040341e01c107030038080280d515124010700722100110062503020081c1c00f02404050a068089001150100050144903000c9081c0d44070502294904400109050001040788040000600070b01c84000c1303c1e03010186003107400050100300701c0000e000090418090703c42c4811850f1001900f100310081d07040300c44140582 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 500307356 1250 500306106 500306111
    0x30403060e071410170c0c0c0d050601060c11040501091a10140f0708030a0203060315010f031101020f060a0b0f041e180503042301180522060b0409 65
    0x301c1140d40d9030071035001d02500305441030250407450911302c101c0d40d03080001c4d24240c1640361082c00104400041941d260320a00f20028818018000801c103492111206403a00c03c202e18403034803031640b07680040c0140810000c13580d6086041c0500011050141c0b0340040040005503500d150380001018038004210b070401c600d400d5455186030004c000c809060042c0c80e40720709001e0400040c00e05600068050b00b130304805201c01c0c400b0500f80360283d440b070701040c5401a03880c2044001c0624010354000c00d1099000e4007001840941d1003034643d00d003241c3e0f00038003445603001440f0050703040208466204c9803e21840080029501498004800840302600d01411403a15a01030000b610006d102906400f9802031041d140990742d0350009031003a0340c002c440c420346685542c4203403c55010398046034140582021042018039641008201d0404c2400c0c81401000c04441d00c00d204241882007074801e01d80380e4203010881010100010f01c0c40340208040185948403183d8007119080ac0c09940411403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 500308606 1250 500307356 500307371
    0x30f1009230703080f0d14040203070e0115030203190e06150a060e090601020c0307060c03031a0d0b0613090f120801121b0315090b0c03010b0d2c03040306 68
    0x10381d03449032400045a2010300001c40c10b40d22900078a80c011111004c03442e01c20004042ca1070030754840c032144104010342c406000d040c41e004051900320035401c0045601c541100412400000114130703000b191060030007588030b0741e4040160b0703210110701d5044d800c400e00b00385008603403903000b01d0340511030303140310b540500050000401e02404503420b0042c0070101d00c0540b406e003e1881c05203900c580c415014412a081d548114011a061102035070118001c2072001035841e003010f0b0103000380481c500c000c0300c500e100b90781c4840000d0120300c81d000703000c0d1403604504085100741e21b07186220110740780d901c43d00b03100550140ca000703800380c080144199550a503c040301d003101c61103000310302d04030360411200180c54041c684806071101d00b140744c640016400b82a000001038403000a0880452900c00c001802c1c04090510090540f4000c020390640d010030070052240302d40103800c0e0341e85002d000c600065594000c0300c10b0b140c0d000326030459802c0881c00c0152071200240000c020b0042d039114190600c03419 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 500309856 1250 500308606 500308643
    0x10306054b19120305030907060c151503060608030406030e0312060616120503071e0f0e04020903100b010207061103070b04051005010902040f0506120c09030f1009 72
    0x41e24981c01d00c040428250321540355440e003066809445000c40e845541550b64503183d541400c15200d00480214201204000343c415040c0b040d9001051a800c0655011189540303c00c0740100120403050b8140e41c900c8114004140303c5040c10203160b120350104041c41e00d03280c0c0e4030380e681c100d4460a00000d0a010b54840000c0d008001e0340c00c1c208030541072070520b4a6220402006420078520040031413120340544010400e0310f402215107007001d8503125620705110314010660507959131021a101650900e03181000d0340000406528070152821010f060070a60014001c3c1c0b041846090b031611401c1c0e00c0c285e070720040c0c0d8407075200b0380c030260211014160394100a0710300e24030081c1d880303030380d03410912052020600c2c02c0c2d84594490311400c140c2d0464400e800c0444111082078114800d429070204080c007a010b114000000640b0b000c403141810300c1c0309894025120003000f890b24000d84404580130159450070402140344a5058054a9900d04901e05420062081c2c00e02500d9600c24800c2a2110 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 500311106 1250 500309856 500309959
    0x1e051e0d11030d0e1203010905162102030a061206020405120d0e100e03060f010302190812090a0f180c14180a050a030302010207061a011d01030605 65
    0x341c4510281d410600741c90f000000030040f040d03082402e03010700c4440c00382a82030580294080c005000300000c0340c0c104007201c40c20f1000003004031301c1131041880820320000071529107001924003070b08000d41c1d00d07580c1d00c46480c0605040d909c00c00c408034014a068007006610340251041c0d40c0c00395800304140c503811a00d25680e1039030313840c040003040d00941c0c0070002d42004024081d6550703403800e1a00c8880111404a40fa100045840c08044080c0d140144114501522042251508201401c000e035003000701c20342e166041d128111350b40d0305001481d1145911580c08180003060f00b1403c070b01040e969560b200711100ba060030006c05241c0780c8810b000c0d10f00c0c011314a80c01c0800c8010105402c0043c0010030b043d40d01d0812603001d50280003144002401e542c0d140c42c02000c1c621075400540c6404041c078000080ea05e0307018031903440b40c220701e6944a643c4da020050717030026506c6500e9940d00e05562001030700140540d42242d03401580c0980e810040c030600c07020414003a10001c4a81b82500c826580e85440c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 500312356 1250 500311106 500311127
    0x1a0a031a160c031d060304050d02010e03092b0b1f0605030c042705180610060212071707061d01060e01260a1a070207080601031e051e0d 60
    0x1055820950b03001180c4640c040780d071440f002c450b034403010421410000c0d03401e400c100c03400c8805a010400746031100d5428000c800f40b018800e4020f5052a40300000120104004081e20317004800300341400a99414500b01d40d0340040c0c20001035406420110300c0c07025891040001d40c1402645500d00107043e9100b001124452a24100d0b02d42c01c0c5800c00c0c044480e5030401c11308590f8240301980c0e11107800c81d0140f14003405189000282d81a41e50619803890504100500c1002900700c0c4617420040725401088015184840d0120700d035448069251a0762900c09a03140e40c00019804261708013009110f904c41d2003031009440c0311a0005e10000c40d8107003600c02a0103400d92005821004008906166010700c000c0a03400006543d40404521f049142010b0b1402c00d4842c3d800c040a480c400d6240380c00c8103500004d462001d0400c043c180b4454a0340e80c0018400180f905001003005070648045c2070450018690102c10385842100c0d1020201e035000c40502c00c45814001c8400d0602000d011f1001d001b0f = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 500313606 1250 500312356 500312401
    0x402030d090303170a02070506090c0f040203010506040b030709032001030615021209010e030615150703020303070507020a0506120702060105030d020a060b151201092306041a0a031a 80
    0x58a900029401c04c18440020780756000f101d40038850240001d03018401103110315200d20089c00403a642d0030404c4411920b1080d5140614070400060103241c81e81403c40d010303107884d4001c0360b50740d454074a02120f6480780c40d4000f43c5044500080200308070340082c0800401c0308260303010301801ea20313150b9482d0138050614013040560710081018810401e00340203450390710814140610b07461040008a0f0906008907640c080310020001c240c421884c00c030404118021081e00304500f0714a16070760107940ea2001405203020b20002150700011582c0d00a842d20251801074201c58a88000495100d4030103401c0d22018058055440049043d023000621101070210680c000d1054041300e0301c0c8d4074020f00c01407030050f42090700d0b8003480c245501d00e08010000c0c906200c142004540c50205204211116085130910741d0704607100e8464103640d0080d010350400300880d00064807a10103084502d8901c180c0212a801040c002c40002c2800a400c201300c1d40c1841c40900e0440f42d40d07442d410441e0035001601401d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 500314856 1250 500313606 500313617
    0x50f0109020f040612110102250503010c1806050c01020d1406040617030904050c0d020a1d0f09190905060a0609050f04020a060f020a0203031c140903030c070203010b06030f0402030d090303 83
    0x801c049451b1418080d5403e07018010395007800c00c1110010050300180c14603c41c5511161010016030800344510a000324040c9400b445100b040d40c9104820304070b03072095804100000c505804c3c0d602c02907044584498902030b040000003509584511002c02c1160320700d105600e05400000c0c61801c000d03030b50400da4100b10240d45860718141c02c0000604010704540080f20050100500e203a10303904c0104030102003515118128001d410385028800c0301c83d0b2519000c2c1905c811035002c25242c41146a1300702c400181c040d0100c0d218030071110000c090b15000074046100715004d10043d01c002d40d21843c20343e0030600c81408280e0722035202145521054800a400c202c0f05075040000c02d11441101c0c902a4051050750804019900060b00d140c00c03003003c200118000b1a01c01d060b48507940300fa071f003138070f415840000050300d85000711540b03034000240411307071500303000801c0421540c081d0b000d404002c4c6e000304110f860342030050364182400c8085404034020311511803048980c81c00350f0410011240c0c140c0d04d5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 500316106 1250 500314856 500314889
    0x14180607050a020f060108150106170106030902060c0601060809100506030d03090507030c06050a09120201021c1202030109020910080f04031416050f060109091a06010c050f0109020f0406 82
    0x120780e690701052129007140201c0015801c43c0780140410b5000f095518024142102c0c0140c61003a20350301a4000e0703050001005070607180e241c62400c0c540c11210582400610940b4030b0001c01c84500c90180001d0341c50103008008a000d58004500354001d41d444c804541190200703207003e500325003060b00e02c1e66051740f054003042c0c3c401e8440e810110301f041c490010b407010030b69242ea44e8860341c003440e000000400d20110b843d8407010740c01034007800107098401c2134440f0001c6540001c4d46030030403a0040500c445498001c2040780d40503103a19418101c5030702c1c00319601c1da55604414025007200501611581b10b11400ba0751291003041d42d030b800365210340c0c0585850b4484e980c00f6074402c80c900c8001851910184254072a60051940b0404140e008902410710200f00321540b50420724140c000070040d5250a10810100d18076191459114002586880c82511001e006903040985981c004125100309100c0313420100c1c040d0400b00c00b0900c00c0e10703e00c004591880400045d504940580d00302950403041 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 500317356 1250 500316106 500316121
    0x2f0303040206070c030c030809090f0708040b0a110406030b0f0301090c0e10030206030708072a030e0f03031903060504140c0702210706090b03010b09210a06141806 72
    0x100b483c0d500c14007245014a540395104090301010350300c15140d0090108007a03910342000350003640d000c8a00815882030785400140a01000c2002d000580010070a00004010407102d07807204074040c4080f808140c40b5545ca0310000c0150141c1c0030094059680001c00711102e06050082404041c1d010700904041410044000b00307581008082010380242d02d000000541c03904001180140026655a0403c1c5000080601001c8034400c1003150150320740302c038039640c50044085002d07040d81490540c0c40c0b814081c00045510380d603000003d605010004d80300ca94603202c01603a5041198541307080c0026a40e88080004850312000020b030390040500c00650122200c600406000384010b0144506880e0719100d25a580c481d08080d4441c5c0d1b0190a042c070403241c01c1031240004200b4500c01520f07560410071942e100e801500d48040c010007140361118465503000c0c84041740031701140e084030840403c50070144040c0401090f41e188504650002c81d2805d969005c80070030346688000100741580322540f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 500318606 1250 500317356 500317369
    0x130305070501180b060906100225030b1e0a0b03071205100504050607140f07030e150307210b090610030b030a0515070503070206150604152f03030402 66
    0x30100c1d0155079401e50070003030800403044015400d02805480e0382c0c038a40581030054002000d8140c602c50880c00c00c1c0201e0266000881000c2c0e013291040c5140320300058074215060203d982c1005114864400401655500780000e150a022040300a61440d0b11860b24480407540c0c04046a60141c1050005000d5866441713804400e451041c402c403000b600541d14091b044032000e850441d0103401140a00450741d40c8040705403601400c0603001d03440c18030914031085462141440007030610007100310342c0741e00303644000320b8802d01c0505c651140c0e40d0b45410b19000b042c0d003680705428501e9080645000a140313403d072103004410003026040c000252120341c100018031088030404800c060300ca0070b841050703071010f01c03117101001d20a10080000d004900c1d204401c00b803004110070304000d4240300f0043e01e582c0c00550300d80c01210004641c500310208001003902442650083c4205820134003419001a500c10031101400100100e01110120540d0030b80d0707489602c00e85480682c0e88140f001c9005445c0c002d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 500319856 1250 500318606 500318617
    0x101a1023041701060305060903090a14030307080d0608060106051c0f0213030b010905070806030a06020a031404350d110d110a08090a020904030e040b3006130305 71
    0xd8500368109a80d98540c5000b07541401c10030001651030b03100c20801c000b0100f00032500950424055410410b82c9800b04141c04c43c0c6206000c001641c0302031004850300c0910464190740d0b009008642c0c0e450801d408030016140c10700c60111244a0300380000f80c1c0310721a170203481006a110303d0411010000300d0300040176081084030506900e074200b010481c40313030185240c000254416013165074551314242c41d8604a4100805101c00c2c843d01300100101e0780d41c00300d5103240445c1c0c0041c3c0141c8800f0340c2d40c0200c00602c101c4140001550411040c0300c20b00500e24803080c066240404082200c01604000540c0a0700240811200d42401d014086601c072854101c2d28024030065011810729101600110039152130011840c00b00c20006281c05e000c80d8400391280d40240090002c21130010668017207481c0385030042c07020f0200305110907a16200e5480e42c010109002004121000c0819071418100c60264400d0840746180c3c110404400b90b00c10100700540308001e095035a0440030301c282c40550b00c65000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 500321106 1250 500319856 500319917
    0x914041811010e0a060f02210a08040c2c15031b0f090c04080d2a1401090b010503011a0904030c050708012a21021b101a10 54
    0x4843d41c075020380c0fa41d08a0304010302e516642c00c00c0014030040040d0400342d848856420b1854490942c6c1003101d83e070000c540c1c1d0071445142080fa1590f5a0620900e45002a0000c00101c4c01000602c042050a480350401d80306840e03680b0042600c40880b101204d6250b608551b4068021181c0c1d14090040b41e148501e440001910300080c540007000002c081392021100360860701008501800250820040030728007040f60f007041c20010740d400140b01c41005000c510b604240d000c4441c20820040c1100642e400058414001d21800c51185482e000313041b02400b0b414065841c1201a03c20340c6103040b64464612800f511100c00c1d903e030361700d0898010708182004c0c1c40380c2c440c1c1c82000403442c3c02485250341e0407903d03100300c0307059204102d4170425400d01180341208000e4076a80c00600802043e09084c0c43c650744d40e800682c0c803e0020400b058001ca0603001605500407084540002c100c0c0d500300c0080c81d04100b1030100644010002c002c00d4903041200000040c0b0320354100c605841502404c40000c292 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 500322356 1250 500321106 500321117
    0x9010209040203090a0b130308150a180e121201090902010c05160510050f0d091e05010228080705030604090606080d111b0607080f0703091404181101 66
    0x5940045010b9900580c0d1014440e8003280350700c0180014052401e03080403a4103c5540ca102094400034004038000d001d00c03003102c04048a50030a603480c2d140c4d541c010a00c1c4245c900c1c0003031383c0305e000900410a0345015002d0b8007428140115800064044030700f60744d079090721600c0340d03403d144445001f000907a00482c1131041608128020031810030400d809030840440c0d41d11810304250070710000c0407001b071518040c4642409000d0050704450180d4003032002c1180d00040000c818140f200c000508460400302c802170b0b8803106401d11a040d0014940100341001710240e00580c040a01c110301c039040b4680c070020304481d0109094921410046820550040c000b040b44049030710ba403821102140e000c00b0031603000c00c802c0d2550640080d4555803d6003508090f000f03e02c0015844540b032010250b10360321815000621004004001b000d60b2494141c0403c1d07552968094030300035103148150700902503041009206401d41c0c0c40d0501418001c106c280d00054204000c075960641c1040752180003506021 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 500323606 1250 500322356 500322367
    0x6060a14071704030507141806031015060e03280609150b0906040509120a020a080d09050f01180807081603030c09050d050304050603090709060b07021203030717090102 74
    0x388182c0c03000003119042c00c0d003103a5903442d5240c021700e4410036620002c0740b10030f2130000b086036036070306a0319190440746046140340d59614100001d0520b010100e10300303001441d200c24610484902c802403400d40e405170300d40801141484040558698014001ca8101d02100c040382405040c0b00300410021403060030003080c01c502c1603648640001190b0b203c1d5445a0b55410760641c245004c012098000c00c00b65020446410219089130b00c44100941280450400140598240f4801c1000d40312084e04034094540b00ca0441c0040030241c14440300547e200d200e12401c040e400c80040c4964489502d100d81c80202d00038a03540e0324103841d0007046d001e80d4140820301c01050300000301f131140800e26110340d0b00050701d102100710113040f80c925500a05d004000d10300240700029800002c442c265502251300c2501c80d41c8a042892600d08a900404445420704900054204840b400343c454144215600d0b0490094240200d0340d900080304c2100000b6103840d050900c4402e8040c1c81c0da00070350524000340c40c0c074 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 500324856 1250 500323606 500323613
    0x31b0705030f0319050f04110f060301090c090b030702030405010c11040207050d03150302151605070305060610030e0c1306080d12050105040b06221205010218010806060a1407 77
    0x142c100740d00301801d04070000b08002068081c585403556549581d07204100f0f0b824501901c000703100000f00000e0162400c82e01603001c541d5054548080320200030003080d0b90b51313111150800039100290b00c540101d00958000b0031001d00480a403880b0380402e600942c14145840d004640220144105440030506428130014586850008080040c05030004007400c0300341843c02021140084c0c0340d40941581408140016550b40380071000401854040716110341a2004010b100b02c3c0d00a001007551040c0c42000081040202c1e02502c900d01c04c0300c14030500d1500450503010344034100703140e07245038000f40c11885052a00740d20031780741ca101001c000604a6281c4001034174094000c0e8510021540880728041c5480641c020117000d40340c141d409201d40c8040b5000309800303000e442e415008040f1410801c0c15a65040c80f0106d00a000010500c0c1405141e420641d000317500444d20300490038000d40480d0340a500401d00c0c0350140c40050f00f8146000700d080404c40340c1034a143c0c0c000341c90200400107003020 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 500326106 1250 500324856 500324863
    0x9080904020301081e0d0c02040b152d0405010903080a030e01021303050106091407051b01180201080a0605091b090a06092d140102030d090308010f1703031b0705 71
    0x280003040000c04aa0328450350f003c0705c01e5500c8200f00e81c1548244546101168040d21189100ea810f440c00300d42d0444180001c0e05d10041130071002640380020804002c10061012417440e80c0b80d040d5901020304030308031500d0313026200f1405200c3c0410b59030902007001800440c01080700c2e21103450001030302d814664116080e44d0002c51940000400c203601801030010078440c0c64000c0010520800c9110304d0800f26401e0000010044410700402149802c02413010301100e05d520200c513002044400c48103c1c00c842c4542d0410010703400901d80f8000542d440c100c52088405882000f4450304082daa54403641c0c048144001078206142c030b05201d2080350341c4a00e801e04020780300d103444d1807011500304500c0581ca054407800c8a151042004885034900001d901544241c500e40481801454660310060749540316080484100518002c503c00034507a000607103905843d021016480c003680d5601d07402544140c0d4880d007460035001040031030001c400b00700081c292480003195143c03c00180b500c0d00c504 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 500327356 1250 500326106 500326109
    0x2a110301020909041b06020102030108061602120a020312010503011a0f0a05040e030d141915120c0503060604020a0503150a0f030c0306050c0c03091009210b060904051009080904020301 81
    0x1580d00e00414001c4170030100c00030310000b6112a100840c215071601e80769960b21070b00a8000410764a04032a0314030010b00c20701020600107016440c0301c0e5a072041c21002542e039071000c003100c2d921500510002c644d924040c000d40b0030f1903000000074105007000c0030400451003203200c80c06600880054002400e80c8a502034000a100c440000c0d5445620005801080e900580340741281c0010301410001145501092035400600390100007805511202000c04200c0c0c0f1030b001440801c0c014203101040010481044007514416415603d00c7e441c2c140a11083e40100b145e42404600184005030358400111b2480c0000c41c8010043c03803460b680c4520340100c140031500141c6003107861580c18001d00a540c015140c21518641c00189000c0c10104156124040c0140c1144181c1c0c0e18490220454460008007024000c82000d45840c00c04c58050760b094145c24000c12110704440b64000b038914504210024030842e0440d0151080c40b034036401040c010480c114045600a805120320590394440703101450 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 500328606 1250 500327356 500327363
    0xc0f010614031c05030a3306080712020c0705040501170610060e10111207060f06050603043305150907091e12030c02012a11030102090904 61
    0x54100d0070a4540d194100d007580784140203034010504040f8440500501d40301281091070855200d403036440c1000c0107043c510200d0260985940b1202c816040b03c00382e01100c1000d114603600885642e0320f000e8541010458403100480d6194081842e134800e00d4006010100d00301060381c4026032144001821644281c00c0106000140750f1660340c60380b41001081d801c0f440c0310740f003100000d1400d13000074844002c0407102e6001e210300c90710b602041390013405906000e05100c419648014034444601006070000d000030f95607242032035400d41031040c02c0e205140c00d0305d070050155480c43e1799903151514001500c0d114644103c048510342c1d514600322802c81c403201c200040c1d010840c2d050162158145001c840800c5d80f040700400e00340016a9004400101262060b00820300b2641300c4107040f407e40d040540c01301c80521000001a03007090341c090441e041c230038802d8a0740320080da12151003540c0101c04c034140c5607e50540260210100308488001100703510010000340c545903084011a070010001e0382d085 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 500329856 1250 500328606 500328611
    0xd060308041a1603030914390f061b03030408030103060e031216020109300804050c0103020702130f0501170c0102030301030b0c040b0301080c011e0507020f060c0f01 73
    0x14054030400c40c561560304032105121508105503800c1c41c400e40d183c0031000400380341e5601c0102082103c0c08002200402d50310040d0b034080b2210044450b90206880c807528003010031400c4002144221008602070100f015280340c102c0c009110134030819905c111845900c20310b80c0540710804000400c0150b10945c42265901c0d1254554903086094810034625096950824441420b40b460b0084071702c3ea0000200c01880510301d01014283d0043c0700300c050280c11028900503a2030200d60780580c0115620008900700740a074a42541110401010340c0c00419640213049840d0896210b60042c0020360300042545560082c4446500c0803140340410a84406403640010001c5900c91441040e4125010010f010750702c8440700000d440740301c1400010a031190310703070109a04114000684001d0f00b02864001c0d503d58503208107507a610501e98000d030002e0300204403070752800035241d81208015031544400e41451007550800c9140e05401c601d0320707007002d030500c5414517408081041c00030494146000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 500331106 1250 500329856 500329859
    0x170a020f03040b090f0405010e040303050411040f0506100306150c0501110a1121070b040c120c0e0c04030c06030e0a0203160303030f0b0904030507060209060d0e0d0f12020705030d06030804 83
    0x1809511a8040d40241c0705511f00b4004000c0c19100840b460703409941031030b00055035038a6150030805404280b0b08160402d144c211a4141c0b10019488140a801c00310380414840404e05011015a60507005003083c0303810442d001c4590b02d01421218074a540310740004262010400603201c4c235508001c030301800041c0b88004400c203240090000344002c00c42c00815007940700640d48044054803c0300c0c0000c04000703a400c002014450760741c0e0aa4040c100500381508000d01c1c604144407a00c403103000d2900003c0b2000c0102c1c018802220440c9d0850740c0c0103807a280c01d9881c240d001da00804404519410714060b441208005990910600c00c0100c41074204088031400c60600404503541c60401840036880c10400620135500c0034045035100d6894505259142141e1500001074000e84503140e41004002c51040002081c60704000c8410340c6a42c21203040a800721012900c582040312a100402c1d68070400070380031001c0750010b1901c44e00070011280b520010b80f00290840e402c40d8420341c0d0300c0703402140 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 500332356 1250 500331106 500331109
    0x1d0a29040b01031b080d14040308070b0105090907060e010e010e03060910060519030b061c050102040501080a0207030903110f13020c0105092e0b0402030f01061209170a020f03040b09 80
    0x5000f80d58540d4401314251150420309003e0b0340f1110301424909003c1c03810301100c0e0380b0110100300c0d8081d503170042e0800d031240c01528084803280350038000c151040d40e61000092605000185042c1100d515a42d221600704032600151419941c4802c5141044148420f0140940301080014081c082c0e040041481884503120071b01219050340100740318200841c1c00b0024000018604801e60ba000412000b007030701d80074005400314203000c1c040b0620200303032100c080501c84103601600495000381c8850f90281c1d41c8500741030481c401c20310001c0c0410745070b50080c400300d524418249041c02c0050600f6294100c04000141c0d203c4030312045192180d00090000c10003003082c0141500708000c4002000c1d0702d80e031110310021540c80c0c00340b11140b10307182c0b020184900c103c0d90061920070300c010300115540d0a0a442500101a00340584400f1074110f288000c0c00c4903d5124100784d680c0c201026154050180a1181569204498040c00c40c858041a1440f00d8400c1c0300800003051203000340e582d200c81040 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 500333606 1250 500332356 500332373
    0x5060d051510050f031213150f0e0108010302012c040e01061706131403071703041a0105210309040219090e010303091214070b0405041d0a29040b0103 66
    0x104258050002c1c1010b013449a14002182c3c180c1085040501e40c83d01d00d600180c1844041d00c1d0300c010711200c4030300c1c0800081c80e0002d103d90030942550303640151a04e229001950001028070000b0b00154805103400c4440300560740d403040100001d000002c200017040700050646464500024050355901c1e01040010800300d1105080b00c0284007420302072402c90f42280600c410768001401c140e00011182081040c280100c511907039000501324501190f000c1140351700d4108071012184420b00003041c610468040300194100c41004184611160706002122500404a60009000e100a10091350345545e1800038003d0b00d04400380c261150b00060310300078941c200da40c1c04103841d90340030001070000c0b0387d1001400c0700780c03221642c0900b440c82040c40d000301001070311100104035001d90304010804040e0200148100c9004503014408059007042030a103c610412010b00c00b540700b0741c00540010392a45803001064010408002d503480b1025040c5580c800c111011a4904417207001070003000501d5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 500334856 1250 500333606 500333609
    0x120318061808060402100809120f0c010b0306090c1c020a1e090b0609010e01020c10080a0b0619181205030d1a0a031104110c011a01080f0a05060d051510 67
    0x10001c05450400b81c000c126080b80180da80800c0000c030b8000180d01c0b00d4100270054150b214921465a14125226140441d030030003040d13200b02e5400c2001c0c44030580740029040340200403c81c00703091030f01082d01c10800c01e52404503004003004286100400982c2d03c490304003005054003041c084c0c10140c402e818000d5201c0d00e8100d118001d107400d80340c42d0644c4400007075907969802800c02d84d250040540060780780000e1000e50ba9488442c0d0200ca0540e076511048403405040742950500002e803828081140c1800f514040c4500e000c03441d8800c03008503103d50031044030300081031106020a620b40c07400700c0b00c506075220151001da03c0000c05064034041d500c18a0704c4d240207400c44c40881d17644180041c0340000d851001814440803540d1081865480d94461040c1001200f40c1596451000110602a01000c07070084510380b065180c40f1403550240380400c0c0301e01c540083c1010b1035034545964600801000e05a943c10601c0d0524030030029004100f1900302c10030303500e00c41010346000c50f142d50420210303 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 500336106 1250 500334856 500334869
    0x30a0609050105062b0614042609150901091e050907080903090904060216060e070e0907090f090f08030f15010e0105073201060806010f1203180618 65
    0x82401c22401c8030041c080c80718040444c40300142c030312902c0c14040c01801010b28402c5401501800b07120812003941c001c070710030101440da1031327040601503034a038840350094115403a00700b0708203a5070102200d5030303100070800000141403010700d4507110680040d14a0f078020743c06408e012480700034403841c81c0c00d40c00c865004205240c40109481d18207565902d030f01960100070301407040d1802140030003929805954174000d00c04013201e600766035030a120300a0318032004210311601420300d01180401c88420303107610614840c002003100c0340c54888100018070301c44100d4140c40e40c0e10503082c000210b0b4012080101409581c0c0715480b401c001601220103c40500084006140780e85190380c03e0360421998803c0d400242000740d16100350f400c0c00040440c40540340c4207194041c0c40800c100c2d94601c00745070480a03001c03000300309442d1600805591103e081c02180c0094800040401581e00d0428915038224824a8514040c9140343e10402d4002c1c4a80c000c4408a50018807014554107107404010003480d1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 500337356 1250 500336106 500336119
    0xa0609020a240215130b0a0605060d0609050901051e10150504050f2202220e01080f031806070201031d0606040b181f031a0703050106020d2c030a060905010506 70
    0x1400002c20741c02c0071060400030440718440b40090707c412075961085004000c09070940390713225034070000e80c0010800c0707010320f401d01c40c070740004540001342c1485400e100386420302c401c06030141c0c01000d010400e0705c02040c440040100c03480100b91401c8180d00f4640515098880039103981c1071004001910040f90b00c41c17070140f0a04070b07992100c000706000140e48100501001640d80700340030318042541c0480300c445403a854012400182d601e020030300d028103d407104015103282c000070306002d5131030b44219404540c1a6401c845039140314500f407002840000e205040000e900703404158810381c618101c414170b609a4000390100010f500b05400340c1c25529104440030f400019405042110384880500941207001d0303407030113110440071019009406582c0200c0e45480105007048205400c80d000c41d9154002402d0000018805000042c4036460704400e448501b0707010381041c412041045403551190240398100c4c403000968600380318070301c03045010702400714400b41e95040403420f43d1070140c5018007454 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 500338606 1250 500337356 500337361
    0x20a0c1217220602040305030702040c0507150522050606030c030f030d09030c05060118060e01141201021b2104080616261006030506030a0609020a240215 68
    0x100003800691001c11440844065500154500a420b240d1500148000d10000700402030100000103840060310840b028029000d0890084505000f9614000c091030344082101c02180d200750001c0d90b0100f02d580744c3c0c0d01c03407900307044074881c100803403003800d0705c0c0340d00b105051003c1401d050020301c9150740d06400074400c04010582241e600e2042d40c0100c1e084a60781c0307a010341018411b118016440307400004171626943c40d626442c1d804858103031456002c0b46004c00000c0d00103c00271002d8100c41054162010f0045481e050050040b1006804076807950708108250078181d03209882540d00c01100300510b031810081c2040380400510f440c03000c00c010010301040103031030f9000078240d50146003220b0030700340d2503240f460980752105459000c2c0c960304400304544000c54840a08903204070503001a201e407195503030406500720f1740295100c5070150402d00d000300c046610341d0850040d0b60302c06011124a0765507030b42180151080c1804068140392007014140d010b9504001c40e001800c0502c11507030090 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 500339856 1250 500338606 500338637
    0xc0d0b15010f0507020f061b0f160614070f0c06020a02132a030f020313030f080103030e150f0301140901090b090402100302130602070f230607020a0306020a0c12 71
    0x1d002d9503200030b101b051408503034810364503031506642070241001d2901f100150302401064a8490034410407149100fa684460203040325170182c00308490868455600c80c0c002250200e040394484841500e0200c81c40e1120304c0003d070503100001c01441d881c0d000e041d9002c8a0320401c1b4580d03148800c10b0070018107109410b10400b59a2840880c0407030032840095000001410a402401000c08502119031004c4104503045400c400d6040020b0b11a641d0014080d141150035119101d007804003030000380907503213550440e0801c0b1031950400c01111100030b0501e906410020080d40c4242c010f2180c841c03220301c0400701c900713260402e940035100350002840000072200116101c0100103201074030906441c1c0448205a0003030b411200c2c0c3c07400089208844c180c44400c06075541d440e922840001c05040c481c002000390032301c1414a1040c4a000b41e6184101c804c800304512031300203103010380c0d0100c502c20000000496a200510740c0611940340c65030386c60400e082612240c02000302c40010300c0464030010b080b6 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 500341106 1250 500339856 500339867
    0xa03020901050616050313060f1112160c181424040b0405070903020102060114030c0f0a051003060f0e07020d030e12130305160302060f0a020c0d0b15010f 68
    0x54520075603c8580f40d2200301003040d012181d045010340580000200c040031403030700200d807500b61a02505e0b00b62050714426400c0340c0c402c40010711102203070014241180c1d005009801010f02480c40c216400402c12107403600c9a01c0c1260fa80525640020480020390108140c01a2841d141c0803005440c5180350111425010610410710000120208101614196102e92041c0c0c514a4054000c000610740f040d0087c01c2849180004d038090b20418000083c21151990300c1c040041014003d42895030f5680d0a01c103000000308151540103802010101d901d031120491043c0450960340c000c80d500b0700d000c1081c02c2221060304143c100d41d40000800980e11b400240444122619103400143c4080c8024450304003000f4506160040700000b4288440d46c0340e0001300004d0302d000f082a10414441641c002241d95440d100081d0031540074041d00b9a1116100060581c640c0703140180d884280f20f0100190482400c0704048072150444003d205003100c1d14003407210044420300b0100703030701c40b44020003414 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 500342356 1250 500341106 500341109
    0x90501170706080a0609060608090f03040f1806031209091a0604050904170415020c0a08060414010e01020d0204060e1516030207030b070807020f0619050c0c0a0309060207050a03020901 81
    0x80c06506804114104015400340000b00506e0745c1c00c000da151148001082d900041e1400e01c164454891070000d0440040700722021035541800080250f45003003003483c0c4030724001c450301004a50703a06000002c20035030990348450076800d030f9402c8026030400d143d0a04440b06045a41d26010881c40c1c18000d644071602202c0a640c0c00302ca00c021990740b945480c001a20340ca000c2602011800b04001131025080101011545c02503000e8500f4041190180000386030188a890b02079403002d40400e0106101c2ca91124a100f00304c0004641d0b010965030a80c02c1e40d111101200600c7d03400602088050341c0a40e071081e289904a608100b00098034100b580680102e899900c280602103480300105030003046070000456118420604078585004003503c0080111000340141c01410595185104d01203001882142400702c0c0000c03040544800c4030003018001d1031180c08403410081001c00b01010015103020034071981d969590581454002418881e00d1b51205002e0350b120501400103940300c000160 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 500343606 1250 500342356 500342369
    0x1030317040309060309022805040b0904050a0303091b03080406110c0f12150c0c12070f03051e030a0504050d26092a090705030f0708100902040e010905011707 70
    0x9550142e030300010b200e046400e0000072070480340740290081c40201a23001e400300d44044508210a4200500b8001c40d01401c90f8003c2580d088503c4803400a8020340c1304207a22805080e540340c00d500e85180d0200c54a40b50703041030b14040d1003c6002c00440c0d6000142c00610035402000d040310404100c0400c0c80240310f114030741c0c840d414402c2c0704222250100003122080e520806451000e041852260109904c54201d81c5198010f0b501c1c42c018a080780411500100e611a0310010001515201140c1e6034000c44040504084450038070038040003020082d501940c001c4600280900346490a103141410364141e00b004d026500212095940600068016840c030f0503200c00c0c441e41e034aa0810781080d044117100381180c15031404004c800021000e42004100c0d081d18003102c55100d89000351a240011100c0c088402070460010312400d104041036600071109040140074540c980c12450140d0304103822001d40c00a00d0001040744850070300405004043c2c080c44440c0c03080400401070780310303e141c5c010b15 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 500344856 1250 500343606 500343611
    0xf0e010e0a0c20031c02040302180405100b180403030b0901080c010c0305030a0e0f150a0522020102010b1507020108100302010207260d0332070c050c0307060305010303170403090603 80
    0x2c1e24191092007111005d141c500740080d001140c1036030070b9000f034002e03010990244440c014240c0c1c000036019035103170046810400030f1032049400031308500906901481c0301e40107401800380c200e2f10100500d0301c5008074407a85000c545808100240180780105070f200001c00c1e0300c8078400301d006907042288468415018544035940e540d84001640241030200a041070b14854082103001c60754000c1141e0084a07520860480c1c203840d10040c100944005441031200200b1000100d00703040c3c14041002c49081c818000802e214008400046006120085440f400c00c0009081000c41da4010085640f1000345c081140e2002d0a540000755240d60901aa07a04014800c04d4110f1144001402e0000440040c003124046881028010081c11301c000c43c0c0031100c940101c040b080c1c40c0100407014018011012609070558401d0b03401c407480d14080c202070768103001b04151200152014009180139003081d85020640303500d50314000302000e0300200604850380c1d40b84180700000b60301c00552002c40300a403401 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 500346106 1250 500344856 500344907
    0xd020301020c07060504080d080601020d0f0309050a0b0a0b06030c0904020702150307031a0904050d080c04030f08030105030706020d0518010908011a040e0318040f02040f0e010e0a0c 80
    0x464028410b8022128a91045220000c0c4003a03104d001030081d9810701d01612501030b0404000c1c2c40013403080d071b04280913070001c4824a134681e11032000004000880d2501248041a90711410b0500076a0300c2c00742d80d0018090104018550280181d0044001c00e481692131803414460000c15030041e1507082d44100c0d000600003003075641d11210000e000f0f40e07080c0210303582d0604c80c10107002007180d42c244907075020035025401c0303403482c001d1441d91140760403a01a01145442c86802c41780104d00400b681403210301800040042801ca000580043c1c5c814072050ba030b294104420185031000ba039001808541c001c4244210903070f0b000055980108402003420f010310703881710050303c8040071508180e90540c6000100135a10911038020051004c09a4040002d240400d50003900c9104020340210789a03070395051101b45007003541c0038001c400780e489401030600d62030b2000400704104030ba01504803c0105401440a49482c5201d01d8200f24070741400c00010855046c080c003c110b482c00441650040c541c803 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 500347356 1250 500346106 500346109
    0x2040504050c060307050304020a05040b090f0c0c0a15051308040e10030b0702030a11120f1305040e0a030906031406100314180f0601030c180f0203010e0402180c04050d02 75
    0x2c11824000061515441e0700e0041d4006009410445060307200c0d00a0a0000450342820f2140301e40d0440b0150540180da030f1209007000700801c010f00001e00401c0c5c10440c684021909100113441144950701304503c0103009900802620b0000d42000400342000b602c440000d107004d0f003285c003210014004640c0f10380d40c4080714001003403d6440a0008400d2408002c081540840100700301d034025154420300b0a56140d80540d04c00741c20b902c0f030b400c1080c00c020840c20500110003500c4414100d20007890002e840d0008601920159401c1040780c0e07020110072400c042c2c000d802c400c0507080a241c200000a40e0400b003003600600a410345004010154050407000d10a40018109002d1140c10b00d0541c100305030890410340084038011010f004c1e0354101e8001e8680812042d04807038100c00030800d09401d0007661801c00000701030300d000700c50340d414944d0a107076501c0c00514004c0c805c1c02440003d81c5054010b101d8116821640700a5669103001000b5440e11140199001d41c1c5041ea070121080c640d0b8070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 500348606 1250 500347356 500347363
    0x30a02130e07090f0c02010522020406051f0813080f03060102210901111615090e0106080609060105090108160c0602030c0711030615150d0c0306030302010b03190204050405 76
    0x580c1c03941d980500880401c107080380350030002c69420481d404021186220704202c1c2211000d0780c900482e26031650103050106502c17260f16450900007000024a1540c841c0002c0c03440c010b01c004000015010f0140038889038200340042c0d402a81001269aa54000c0e85d44000a101d005500150868048049804c5134401c0190003030120109042c610302024201103283c07240c000380c101d103000626000360840c00c1031010600000a170040b41c00303018554100045980c100481180c1c2030100120854005400500c0343d01060003801d540d11480c1103800d0030028002c0041000304000e05010003045107100c0c3e41d80c400f841c0c5901a5100c52002c2900d4001f1404546410040001516141c00401405030310036850004100d007910030040c82480038110000c2c1920b4502c120341112032002d030002d070800d0508004100070700d498404c01180b881e0014101103003044801e4428004002a0384000500030541c0901c101d203880e00c0210014601581002811725030a21040c030f0080c000c036101c002050401c5000c1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 500349856 1250 500348606 500348621
    0x3020a031d0a0203010c03020f030a0b040e030a03050702070b07120e01020709090302250b0414150d0e0d0504080c01140405090415050c042301090306110901110c030a0213 75
    0x214012602000040c5040e54420b00200d060344694070309151000543e0181c400c507a402c600008038182142e4540d01f4081c0200152900140c00588500c2001450030060004041c0b00c0c0301a18000755a0502e814000e01d0107049030005509007900308003000c0801c80c00d58200c2c007030307070001d1428082d101c4043c00102e082031400d074850000135042c80340706410150003052106c590300c00c8084980905e0140e00c0d0390342241c8054071817411051001c20040c0121806405402900354000e00040000b60346002d213080305078400c207100d01640c1d0362000d014542100c14095444070351800d1a00509107420300011030f0300c03482c50803d0070341032010107007601c200e0100c4407040e600200002000d041c110300c0d05003090408072105000340e0420750f140c0000180b000e80030205442c00c0d00d8868400d058030880381c051104003008841d03a040d05020b018100040043d150303000d43ca0b09401d81408080e00c0f00780d0b540000d40038034026200441c15030080000c14010f40c800003440034659804945007000040c0340240c2d41c0c01440803 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 500351106 1250 500349856 500349881
    0x62a0304090903110316170f0f0913141302130f0b011e0e01080c1207110d02030412021c06060608070f170402060f130312090806150103020a03 63
    0x2080008034682550b0100840e40d02036207408011604039020140c0fa849083c0103000c2c00c007044101a004150700c4d0440403c2001c41e40d035800d20f040000d4000344540e800c9000c41d071148200004420302181444201740c200e59000c4201806001d0954000000c0554004d044101b01e84580e42004c1c04c3d940c50b0311543c0a03424400c0001c008880031002280f01424101803002c1c04600c840c880b12250302d0680414000c11000755890081c966800b50045802031005000e40040340300900040e8007014403924a0b03400340640343c469480221140044e1420b02141c9402c54055400030310041082607060b4414652040d81242c810120010b5070042494130100110041c00c91850700030003280450300040090300a09c80350b00c941d100100c212008580100340204c44010700200b8a01040c010b0509802802d8003103814405141031619040c03020382d200e20030340e0040d0b500725101400d185099800c44c685601410b00310707001c1c144500e408040243c0131f05840d030495042590000300d50390150300c01d0b8007a12050720f9 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 500352356 1250 500351106 500351113
    0xb1014250804050418080406050901030b031006090f020702030622051509060a09230f0f0a02090108030f030403120603120e090c090f1201150308030a0e0309062a 71
    0x6881c105210305811900034180a689094007542c10044411040340c00035a20502c8285032500b45141100d540d00801342d030301c2c189501c031480c1582c199002e00c0b85105207401c1c42400184540b510b42c2500594642141d007040c4103104104600250314040340e0103500018020071038000c6d44030280d1400710f80c0300d4201c014010340558214a0003000030348190714085c5101da42100c46075181ca240c52000c035075a46900428040c042240c0c0c848441c070f48494104140003000c02d0311804140c0b04d070502d045c244050b070080e4040c1c000c840800114a045c0f000e80e0301500c0350000075405c1800c50084454030b4070003c1d0000e4280010b9068000d1040c8154200344080e592210611110100f407000203440d4124000303055100300c00440c00900448401c00944040c0a002820000c200301d0344824813041e8060360010003840e540341d01e8004030010b00703850b070759004500c1416502d40c0c0c3d181002039a0221600100f440c8242d0700f041041c04a1a0758110544440380c1034040705400e000c01054060404060040c0c10601600 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 500353606 1250 500352356 500352427
    0x605180f0a0e0408040e1f051c0606060e190311130603080403030e0909010504030206180f030a110d030509060c09060904050903030921041215060b04090b1014 70
    0x1c00c028008032941b441c0030b001e01e03071203070341c00c400c591040031a00103509040c907038042209103003800c180201c0c0700342e1413034035009412541c5a29081d154940c1088002c268a9007201c07190f030400c2c0020f034031000999982011520300710b6a0301209002c40c504901d22a41040c00d20001840b85684101c1c01180c0c040c06181c0e0311950780ca0090403400b008040d00e8840d11403040000c8140380c0601440e40301c0c44c1e0540c06020199151301a0711405981d0004101091050400007040c00408000030300b281903164580d0440d0300065210286032401d4910f51400301802d00c020300040490026a40d5005008440100c1d15820b01c0c1000c6101c0d40079004420780e00c41e042ca01445491140400194024030b454000c1d00c03c01074449003180d29000c00304203100b0703502074208010441a1468000002c2075407045850050343e0600e8031030f00c0240c1d0020b0f0000400082c002031704100030f280c070740b05107024000103aa03141c0300c280da1078030054600080103002081021000400d85095a4110708441c800f864401800d645c46 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 500354856 1250 500353606 500353613
    0x6050913020a0c020406060c020f040519020d1b0c1a0c0f070b04020405010503010b0f09130507171e0303040f05031e0316091802070204180501090c0605180f0a0e04 72
    0x50f0b1000e01070b0f02030380c039282d000f0500c14416010019040d070050140d00c15000c41405010041c03000034105000c2c0904c21752260b510750040e00041034a5024075a02281c041218851000002c2001a589061001506c2d41e403001030030007802005014404c81880c04107a4800d410a00184144c05103091020000600303907080059000c0c038140280d0082d2800c02c003981c1c0351001d0608035402c201003130b03030320429000844180703141c6000e4851b80034000c00e07200c941c54905940c41c1860b101a98000340184d050b08608a10a24410044c0c041d00c03d450031019019050340500303060300c1c0c2c880035201518884840c141c00003802001c000308d489108403424200e18400d10424000703503903003054511024104010000c8451a4400d082190130368105031320041ca416100b248010083d441070908036042921462442807140801921b00501c5d4001c00020501003003619000c040d15505401210034410705220400002130070034006507400390b040e503076040d4565103c0300050784540309901c1065004000010030040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 500356106 1250 500354856 500354867
    0x1203010b1309020c0c0f0a05151c060501140a18260606060307210c03020c010c1d150f03070302090a0f05130c03090f030905150f030106050913020a 65
    0x24911103010a00701c26031140701031030581c4101821045158092a00050359240149081d41390712401070855200716603950105040807001c101082c00c08002040010203920740030382c100d0302c200d5610010005c00341041d0018203084140308280e000658041108075800b4041c441c52604030351003e0b03055134581d81e1240c2103010f281c3e8180680760918806104510303042030005005024040040584d4103595030f04408403000b02c00302d81042100410304001c20b5110155109640d400100e1780e40151340c507002921100d003503e1909500108000300124074410500c1050746e50180402c4c112165000419030740c58805560040107425a016800003003031003042e07034141d8000d050b8181c0948841c40701d566110051083c00d0800e100f0107801c40d40c46205c1d00d88844640c0e01c401d0035022513042c00103c000942e12400e80d0504002d00c114003107a9468414009482c2542c81c100c8203844660440b89072503800082c440303c1e8001803040a040c00b1010550f4105999183c03840d5404040d400c0c405c5403600c8130140010701 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 500357356 1250 500356106 500356117
    0x106020709090b0a0b06040906030305090f0916030b0a380f0304030507032618031e1b030f03150d0f1b1e090e0109021309051203010b 59
    0x5485000c0d000141c1d41c1003801601c1c00306400801c0d52800b69594071424000d8290080c02d69403103002004049480e1f070961048a01a42c0655926a00c0380b480e20180714141e11600754030362281828204000d00540c44404031100d040c00d924010810b041003d02041c00340c0307645c3c0c014610169200c01d04540c07640b00702e00d2541030700300c84a180d182c6800d0020218510b611500401c02e612000c00c10000c1c01103070196006241d2140700789010122004042000e03202e81c0100008002000c404a0074080b04c0c124201234099040019000307180390043c032900e803442c05c50700c054900d008a00c0c042640079403004070340038a038030600c0d00700180d0b0340e00e2803e0b0f03101c0c1400f90310848450a24085400c4090b01c2801d184500d450f0311a44500154030380399050b1501122140003416104805c05403280201c0c0707981c0a4142070b0401351a080042801900309031106081e00c1c40c20307a090416038504403007200965138644c061413200e402c0800018035000641025414480040051041c1b140000700000742da4241400402c0e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 500358606 1250 500357356 500357369
    0xf060a0e0906040c0c080901020a0611030907050603060105072301020a0c1b05090a050a0b03010e030408010e120702090a0e1507020c0a15031e09060605010f05161707140601 76
    0xc405503500d00803c01103921548441001490a03441900020700c0c0c2c3d0000d20940300e050046407040251566140d09581c40741c00020245200801402a401010061b140141030200d946500394030b003000000b0424080d481001c7c0480d0492551081d8404422a22506460701c2500940d40c40e041c0210190403070440c403030300300e0300881714145924901514454900076148010304520942d1207166044025000c00390040340d0b03180e50f6610740e24607682c0900c42c0d485080801c038040c0d62a6803404038030501311100709220440304c0c0c1007202100c5030501990200c554440c1d0440c0e0348030158540041401c024040030100c0030302441400340c2040d03408020300c8500c1c07107446103508880d00c08803a40240401c00032240710305201c44800d0840448094081c3c1c10a5800300000366485150402d05c03a01007050b9020114181c07013948d540c1c2814403441d644899440d009020509109240229000260200380181c100161401d010342d0642001e002000049421080c0c02c0b45440c410000c00398003843c2c40e58400e202d1039 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 500359712 1106 500358606 500358619
    0x1005012001050f060312040b07021c0605040f02040c0f0804150e03040e01060f09030507032607051006090e0601120201090b1908060f0913020f060a0e 66
    0x207032280c40b0742021581c0d0f03030502c40c05240c14078501c03500300041d8290402061100301c01c41170450f416164191039100701c0e820100103000d41d04070b910304020200d50030b0400703110074002000d90101c032086c001c4804100e683c064032410b170385103052110b002d40070400210000d401300300385d05a00786510315515004035444074216960380c10350340280c000402c0c060f403410052001c04c1c0d20140c048040308250401c45056415501c66540d203080900c0001c1c40c00400070744407004030b200d0306544001094408030b41500c681d440e181c0103485440149002c00340c683340c0f0500050009203801508101e2145201909199092a1b890380d080f03c0305501c26414030410550000d086e20140c3c0c010300c95210391244d80c0b146c2c0362481400a05003000501449e21031103000c9860300c0595201c032000e64019180e00c111300b62000140c80400d0a2002d84a21540d00020120701590368940091200070500c100302c07841c = true := by decide +kernel

theorem cover : BRFrame.Cov 500179856 500359712 := by
  have h0 := BRFrame.cov_init 500179856
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500179856 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 500179856 ≤ n) (h2 : n < 500359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
