-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3219
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:00:53.236077+00:00
-- url     : https://prove2.me/submissions/6e927e7c-efcc-4f7b-82be-877a993adde6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 578776978 ≤ n < 578956834 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 578778228 1250 578776978 578776997
    0x91501080a052a0d020309030d061d04031b080a050c0c0303190f120c1e0206090706140d0905162112020114090f101505100c06050c0415 60
    0x1445100c2180c98030683c542c0300c01644900d140aa1081112202c1c107040d0020740d5249803145d904e95884c0c0c44000407000051a080f00014036900b10302d0003048005090207050903a4640e03803002c650710342c1d040a074050700701401c3d6011000140123a0041c80c0208440d10389644070392007608458105000b41820b00d000e50810401c0ca00e9140049101100c1d9021a003480070440101c00000c03551080001c00041d041450008000c9034250481e01c0c000301d080c150b035020f4903090400d55040762108415203032454990301c010801c0c0040e90040650801c42c0d10000c00040c101540c440aa00540300c031500e040e10310740c020400503460011704501060240000c060851000001c94a8051250002c00700241c0382400c5100c50f40203180c400e420020012800400812284c1444588141c4860a50112104074030612401c051066654002c0f45217024074918482c0c0c0862900c010b1106e07510340c00001a08222581701081c0c0060024850a8040c156650360f6584550806416034544201110340d1070510000b0302 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 578779478 1250 578778228 578778241
    0x90e0c0d0b0702100b030607050c1504050a021c030e090601030b060d06140a140118030209040c08010c090602060414280b010e04050303371509090c2102091501080a05 73
    0x407285d40208c9180340c50340c0c1e00c000d24100f250a141c51064400c0404045e2000e00060110024041d16924000c55441024504001c914a05880d504200401140905514243d1484c025075100d60010060401040c2c0e6001d2100154840c5d00c12090440850f50fa50002d0041150642001050940598a02032a80e0620b823164100214070200241040704101d914940d00070384409600c010b5502905541c0182407038900f84c0e2920100340110134944d840c10003400000c2d4402c0c103404040754050340140100c0e0719180c0314a81d4420980708201da15100d0181d06840c142604402e007503403641d54101907002c1c03800d47d18021101c1c0038103a200883c2d0303071004400d000102c1d201200712500612003d80540240a9450002c1840391680c10301c0544503d0308400c044c0401500c0d04402039504801500c441c016486540d12000c0f00d035443d2018010b03003504102801026030001c4050501c2ea0030b099240c83c4480c03181d00103411510112030f20a0b40190312081a07015503081051607400c00054002400f2614211 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 578780728 1250 578779478 578779483
    0x80a06060f090b0a121a01031407091a041a070c06021f09021f0c0201080a0908030103080d02160c03060b0301090305091c050105090303070215090601090e0c0d0b0702100b03 76
    0x14021440300f1075001031034201a03801071103582e81d252420007082c0402c0c0071810b004802c84c80032800c21070209040c112000003a807a8000b40610800058550075441401c08900c210b4101910344101c518080c2084042030180701c5e40201c440046225046a940d40410310340010389030300b00d0b807090023594010304000c5102781c28a81e400d00810303d60440000e8180312400000c2012100038501d424615889001c9080e6580c000304940f0464000e132500c103402c1d1540f824080483d1207494002c0c0c003581081c030062000a100c4001410024004440542001215405050300490105044502050200e0200100007180c06070041e038400840c002c00480c070031a1005441c500ca04032020b4810000d04001c030340c03900c08000410900c650007a008100600c0c200120725929481070b690306016128050990b03401d07602109080d481444840c01519550b4a4000d884014040031040300031940240d0359200c030741e51074881080361510f0141a13010b801c1d0900400103400d0149200f2094030241c00c0c1230203110186c400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 578781978 1250 578780728 578780747
    0x60106090605072609090103050309041811010810081b120c031c03150b03090f0a051009020109030203030a090303030e070f031103070e0411090a020901081611030a080a06060f 77
    0xa152150b10892a0400104c03001e11410110079801040c800000c000d00100001a01c44600241c41c100620081c0510b60325915844000041c0500c0301814007442651242d0764194000c10440908041d55460740312701414400403802441c4031481d0320008514038580000806142e030483d02c050078240c820107002c6500e9161030040c1c85070380d800085140003070324400c0e40701414155106004540f5961224031100306540180c0365014940f242040c02c200c00324002c136200560580c01402400d840c0804100ea07006030032031100030b90601012078030010258400b80024050922156101e10301c4a00f54038000d02101c1064a20b00259070080d5020704c940c40d03103800e410003542e800a008481441d07250002a14291450700107440b241071050034441000314801000004580c215042c80d1140d4592044c00d0881c007600407034500142c0c03102d02241e036042c5e800e131041902100905e0901410707000d60301d285265520000115000911400030004080814842d4802a25a525081c05c444055034002001c04c02d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 578783228 1250 578781978 578782013
    0xc100306030f0f0203031903090c06031407211d060106210f1104120b0a09020105120a09021216170304210203012d060e0a18020a0806010609060507 65
    0x5040f604401d6503420000d071001450410300c1c0c14550240040300a000c0e26404a00f103d0381c0340008404580704d4040c1c01080a80d4444c002c0e651203c2e80c03103074400c40d803403c05071030380144c40c0134544c85609410096009802068003254010600c00509241c0145803140581c411400c010201410314101c46408a0318074044410142c0460421400101d01000f448070038503241b41c022000030b000030018034000030410b107107004040b45c6141e03503142c10a04040d00c1c82c0c0c600c020b00159040202c00404080071001c1500f18010001c0007900400942c045070300c100440d03841140c2a0302190607000481c000b901070b10007070300c5030071000000362005005850b500d001c0c0d8040d207450407030201031000462610f00c01400145400400038000c0c0517510a6410078140e41803200041c0c440c59000c4102d1400c400d020703d01c203c034116480d400441d910320049800800c064540700445070042118140540d0310801014050030820014180f55450900d001e03010084950000061090500021012420300181c0c500d07401d1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 578784478 1250 578783228 578783243
    0x70906030b0a23130c02031b031204060506040b040e030d0c110a0308010906060513050108152106010e100302010c1509110f041a04150e01080c100306030f 68
    0x10303000d0004076000c0d4a9084115440300c00702c3c940711400081c1000030001902554071a0355540700801e807206940c031000030301c000340e40100881d0003030b41240444075402d0240c08d4250b07414181c80c0b4031301d0744c15020266801d86683c0d0316981481000d140c184189118200b04031010443d80d0001240152203015182c071607500340d0b95820704103003054010101c00e5100c0305003070142c580410017807901509000d400e001d0a90305902c1c02501007442401101250015a070403881c100040d454200112502c000080c111359852200c0b604600c616102c401070940820700350549907129407a0410318924001c01680058102d000a80500480c0341400e0100c60a80740c083c40e00340d08109860030200c6c0c20034000381d0f202d0034552a01410f1002d200c000082861803100c100d4045100b4006003041000740d52080d2452108001505103200651505d40d1241c0c800c01800c64520040960f1401c8902e01007109a00c41841078000d000170320150300e010117044405103407504080014500350344035071104040c1d107540104403d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 578785728 1250 578784478 578784491
    0xc0e10020a030c260a0257031207061a0618150304150c0203030c0d2c060702012a0807020f0613020901052707030e0304060e090a0507090603 62
    0x40b88040824141e401608034183d85c0c503140743c803000f90381d003080000c40c001c184403201c00c0c03100d860041c002070750b00b42d142c101150380c940c941d09044800b24140a100700b450f001c0c00c005400825141071002000b2064610704440c0c8405070b13801c001c0c081e202e001c800e0101c50b0798440301b02d1420f550b480c07069550b0781c1284070420070514079907404510243d81038003210100700000301c100800c100e03078026490040350717085078140503405080f9026139503400156410010308105000c00b80460480d0b9210301500340f4020070000300000030070140d0510240c2c5030a01800d541240e82049041e0b9024000c242440114080600c141e03040d00540540c103c84640d1000c0c2000202000314500e039108110050180c240c10b03056848a080030004510301c807100507012805603070741c5400052a840c1c0344034585008075550903040212228003500c81c3c0d00d0346d0f0060001003851756420707c4501e010343c100b020304050181c940381c541d070034409a02041981c0a006212481d460304110810890350352201d1400100d070260700340031400307 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 578786978 1250 578785728 578785763
    0x703080c0f070f05040b011706010c050c09010803042904050909150a27110d0f081c05150d030503190e0102030a0510030309050913060c0e10020a030c 66
    0x80412007000d00d0402d02c285600420400200e90a4504445049600300b00d0412210700540302d45c480d403014030f030140a100c0f0000324103501480c0c1c2441880d00ca2401d8404c1c0032074074400610881002c0e00558425031001c101031202007045c9440e909045581000740507148401d40811a00d40f089000352401078600c4001300d51071003003c00c016035510800054021203407a049861b81c0040145410001c070346411420304c004506c901d00c02803031780782d500420710001280c1c03840e0500120f0039034098122110400000c6000114000001400d540c4e1641aa0b07142807900111107807081e120080e00d0010406400c450301c0c1815600e81d41413260b01c59060a21580366520f0341209546001210140507180341807010480a03108103500a500c00d1040701405c102c0c40c0c4800d0b0b100428a00e084c00014007103001305105000d01e107004d804456016985082c190070419103070342c6a02c2981d41002e801030100b4480000c400c076038503086500704c0c0c015441d8401020110101c0d10020200c803640600a0078140f41e08070303207052 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 578788228 1250 578786978 578786983
    0x40f0c090e0a0308010f0608011a0f0307080a201207120204060c02090f010503070b03040236060105130e0c07050601080a06140709050f030a0204110a0212030106020703080c 76
    0xc0480381010000e14070310950880e140d141a020440000c2e07140740c008030f08403004a00580a884080c1d645060b640c0c01c4c02165400795600201728001d04a0034403800100d084c14a000314405c1240740e4400803039091441c0140f060b150140d2940b421a120003c10300348050f1402c09036200e2030b039100c84030180d5494950050314000c08078100050301d42d00020300032466a8115201140031482506d00c01d000d80c0c0d50300001110f1620030700690351f0581001c40c0410040c0c0841020f1600903000601c0115540141520700d6002000d92080450b80c80319a0080d2014518540440350b000c0e03000e0800300e103002d5001c0744501c082e54460055100508480b40412000c03040c000546c0c070190390080490351656141c05406642c1d020414046600324280140f8002229080885a00616041c0c4132a605a0704110030080c8508621503003070740621440c0350b0300000da0745e9805014006004440e40382d55940e840c15000f07060258070404404400010001007101a6000440e24122030300304040075221040624000d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 578789478 1250 578788228 578788253
    0x30804021315090e07050901030203031603030b0616200303030a090c1a120a0b09061003140103081b0102120438070905010305070c020f0a0b28020f0303040f 69
    0x68042c1c0c681c0020584403041d0380401d994054240840d0b034955610702c1005403040342400b0094058009008001c00e60040210340d03903200d4401e0030040b80041d07484021400a4004155241a40400342c0c00c1c5801d201c0c1101c07960f45102059000c100c1409100d60200c1d589100c050f00300060f4540e0b441c03403402444a80c0c078050b000360002c0c850481c2005d2010500c0c88054002d000300c0322460b038003100451406802849003644641000e441194230756504410002c80340300707069080c0241a1039240c1408030b01005294075010398480c003c400d84907490420f0008944c0500c0000d0f02c03440c1c1c41000320f511541c001d100210341c01036221a86c40c84050003840314008000700241c5400342d085201c1c1030046001514562a4070982e01581c501c28090703a123000440c02e50780151030031004030701041150b01c058100001c0100c960303c0d0141c140680999508c81c1c1c00120707444281407010840540c00505204c44030040d0a41c540c00c103030700c0188145411403007407907100d01c4003400042c50b00d0b841e495050100000840d050 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 578790728 1250 578789478 578789501
    0x1090b240c121308030430020d12021e150a021b0f191113021b0309120d1d03011b122d02090307030b190e06040308040213 54
    0x20750351101c981c9003510342d40d00320036022032095142500220704208004183d40464100315520a0242190a08010a00d180c52204925900006520009600d5042c0d811181c180f081c09410310980115200a09220314550010520208144550307610074000400808040260759180b0031740d122444d11100070710810120301c2c1511060700c1e0349114480c001c100300d003156200005079103611b030381d0001d01d000e482c030904401810440c4c0100d80500c00d0805a06034101004403140045c90310360104945030074810062981d038900d900c0050b42c100a410080000d2990201c6e40006000549807060090302c601c420100c0c1820562001c2034201c3c29607401d4200c0c0c1c4590080c0014202103481d261340003008204000c14159140d03041508a14240380844690282c0a000c1c0e004a241200030041c040d029602401c07800d80c0c0343c8240ca1020012414041d002c07800340040101d5441400060300540090b0f071209160650740f1f820060411002c00c0d004098140d11a034100e03203032901503401070311840052a0307041c0790 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 578791978 1250 578790728 578790733
    0x60a030e0328030e030306060a0c020f041d1212010e040c050901170613030f0c0201020102040e010902070c0602030304080d0b03160b13051c02010305040812040501021201090b240c 79
    0x5552210302e03588a04114099555410702944c24000b26070741e80c2c1c1c0b10a4542c90b41000341006060272403441010000d101500c014101d0101a40050000d01918030300c1c1202e05094204080440700010100070110030294074403134460400311040d02c8034801035070500ca6030701c20740300d000006004c0203042d000100c050480100703c0b12640d44c540c81c41e07400e1421000191031451090b08040380102c11107246407a030080d0302d6a10f00307006641d101c02c112903540303902c00100d040d036400780008030381843c00d00b21550203008414001a211246030800c2e2100014640c010b40664008206000c0030602d01d404a0b411011560f0f03010482840318408280b030140203120403000c0010950002c00c003034481400a007004008081d01c4035400c2c1e15a0200500100e035942202d0050900244010065001c1c0d00310582c01801900d40900707040300f190203003c200d001102c1c112540d950008022011403403400440d80541b18481d070801c4a031034900041044228000050f4a452002d01d082040ca95164021503414007900000d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 578793228 1250 578791978 578792017
    0x318010c0801060f080603060c0c12030f1005101d0117240a0506090d03020102090a030311011a0904020118120807140109080a0e0a051203070501050105090105060a030e03 75
    0x801800c4403803c0c040c6000041d00700c2200480d083c484e41d006805200010040c0500343c86118540c40c4513440321707141041300c3c0901c0c10394600480d405d074060b5119825001542c0468509412142d61b94052074100a00c2100d18814840140c3e030310124401100d110300550505454080c0010307500040300030b94141500b240b0a04100301d407448000701e02c140c2d5003918190200c2c0341440c0e04221403510140501e0343c108000b0720020019140c400c0c40110100d00900006140290076004201c0840240d00180c010508034a07489800d02c0c0244951402c40c60380e0480c0c9200040302c40c000648440b00500042d041000d02e014890840c0000d5024038001e062041c0e40300d50743c050a2511000c0c4c0c0e0010b86003600c42801d40721020407842ca043c000c41d40740340d030700480e103900d40341550b84203480f564110710449400ca02e0310600480c4a44035540141d2100d18080011902c94031246001401d44005070803081c0a04130b10360041260762101e9050b20303074003241410082003204a20740214950f001c0e02d40d0047c04018080c9 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 578794478 1250 578793228 578793251
    0x3061e0424020d06080c060d180501061706072607021005090d030f06030b0601050d060b030703020d051b040b0f0d05070e1002070303080103060509150a020d062108031801 75
    0x2d00401210329070540911243c2e80e607071002921030480245085d000042000001c650800d80c0d03100c15a040700180c1c950303c40500ca51142d86c02c64900360868024901070381c1403409403040801c181548034186150084150600300810311304075101e161402c032144100b9000c141c80600078030030f0007601012074030100881d103040d06c40d866030b51200c2155000464607100102c4a50009030007503c043da90014110400e544490300111407550248444c0c8258550369100807504d940d20800445c01a81c40d83d801507103e204641e400c2e01292400b40804143d00088121090070309180b134140c0b411030301c503d2002d9444111940000c070fa984141c115422843d46403204010000c0d030000707080c3e0700c0808103550650a11911803420707a0b40e440c807800701a0110b088040100006561a04038540c0449154191000360554031f40b96882c11005a801031405600428150081c000302c1c0f1400c4000d15103910401d0814880d00000243e020030003002030f0518400100045a009425000c1c807250070290000704074428415 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 578795728 1250 578794478 578794481
    0xc0f16080d0e1f050f060111032101060801090902030718020903190311070e13060b192c0c07140a120818030d0902010311072003061e0424 61
    0x140f410001480d507403000700c08407000342e00c90b403845a04036a1080d001034071524015906807100a2a0320340274072013041410510030b4003600800d5800312515204845506003c0050308140c0142c10181110f881e103072101003d650005107040448220892a0074100488104403001c0d2046002d11509880f8010b00905441112040a50800c0c000c0c2c0d030710b000305941e02c4c80050302c1d01d80381d221b82c02c0010900c03c0801c0c2030618002d001d803034452280d003002826107240c03804500c3c1000c51018001a81405080404c2980003002000810004030040081d07501120003a0f0b058090b0041c1c07040c80380040104140e02040080c00d82c1c004d0200102e01201c0c2020b8491618030301e09001140240d000404000202e03100344a84c0341a034125030180b40203035040c0140c00c90081e009201150007a0304141c1c40d4548a86d60304504402400441d01440c01800f0340c980c2d080400030710764902680075000c3d034451010050300290080a03001e88140f81d90007500c0c0d945440c140450a406420360300241d0740f43c01014442012080e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 578796978 1250 578795728 578795743
    0x70503071101050403030c15060306050f1008060709170c031c090e0f16120507030603020312030105011b03110d27030203060a330303080c0f16080d0e 66
    0x20050861101c0c22080111468001c038403000b00490580400800000c07030414941510750074944000032030307540c3c0ba01c1d603000b5150b060f02c40e03405203110b180c1413000c0001c0c0340782c1c4000035000d15002001103040c800e90007080d2007124401d046d4590904100c030585444180850354014000804803024100344074015944400720580701d8002c500c042c0c20015004a0703101003a44a0100407010745016034070b0300c01441c000308803084110704200500d503090414003820300c2200d00038103240e0760004001c0d00f1403040c5480e10000a42000034810140300400091303034000b044400310210315000c515800014a015241101c1801d4a10700c2c3d406881a80ca4020b5480661090400420f0a01c0c0301580591845198101e86c0360101a40540000740000e00c40004c640142c44044040e0b03148003004c122140300d43c1d06004062042c1000145110f0007003040c1644105826000010780d10b9407840d01000c8901803105100d034041c1c0700542a02c42c14110140300c80312080d20000c2041400c1401303504000b0810b561034510 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 578798228 1250 578796978 578796983
    0x90304060813110919050108060601020114150d020105040f1202040c0f0c030305060a0f08070602010b1509040f02040b030a0e1e06010302090c160c140f010804020f0406080307050307 80
    0x2608000640c4541c882205001680c0c001d10f40d0142d20508400b407156a01000b446958000c0c0341c1800300040c2c040324420603001b020014041c00302410403000080c2903840c84030042500704011001c0c4070314404514500070407118200c1b04407081000318401652203000b15840b0056980390340d200002e8007840210b00c2c0500718400c8500304540c1e03400364025504028804e410714001a07040c990500024001e900003074010384010701c0c216201d50784002e0540409155004801035410490303042103c1ca409020b808014071003112903c02c030180485203c0c03514094500741e14401d50301c80c0b43c2c04019100326411240070382a140e004036aa03141440c010000b810790b40c80651030510074030300035804024007200041e0b400c034080b802078840f6918503020000008400381c216190028200007c080301c05038501d030444214404c80c0c800400314500001c8403e9400b80700314103070045c440c0f01320f0591242c0e40146202d90047c2d0456040c2a0508060040b84c000c2015400403002c1d44400129002403000001c080d103079091 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 578799478 1250 578798228 578798237
    0x910031a04060c0903050316140d120b01090608041506180b01110c1509060912070303080f0606040608071103040609090b040e060c0a050c0307110f091005010c1a09030406 75
    0x2040700108451308002c600c4041c03c260410b00c10310b80740e540c0c0400c180342c000d401070400310310045034540d06500341404141101c001c1990681b031220301ca032141c003404e002180c0074200400214546680606140d00c000d2004180b801045441d01d039a00481d440b40c00603001d01000c4010701013290501d400280103c11096010403560200010400000501d00e020080013920621007000c0c0a41d51040640021900039404102401401c1c3e0f1a10340000b501303c0c0c1903080c002000e0051540c28080c158070301c050400340d940b503450010800710f0b4940c0c3c0202d41c00c40f072080c03803c42d0a5940c0c8517422100e40440303055100460000240c001002540004c0f440e003951511082009082420741c200811520814040002c03a04a0800206e003034440c980502500340c84e40c10309501e881107003000d0605552210b102200d141e101d0003036102080c280030201250314841900c60584609055043c920f000c10584215410000040d002c1ea003000541c51040b44200200300c03524003a806d000310101e4494200f03014610004 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 578800728 1250 578799478 578799491
    0x250609030e240d090201050702031b0a0f050d020607030e031f0e030405031c1202040e04030e030a0f12050c0304032d03050d11040305030315010206070e0306060910031a0406 76
    0x12084500045003410710300440900d010020f450785070203001020010ba041c028103014100250718140621402ca00840950203040382c00c0104004410980340c21061f60a40500c10030f01c2241c807034518482070f40d41c045031190703110310140c0380440b0802c41d200c101c15018010703210707075140343ca212101d011002d1620180500880d0701d2141015030b6400b0b24803400da40360b4000d481e4995030f0364400416a00d08061440e03d690485414500e51081c1e0f40a0340c002605000003104101c1070540c042000e1a00032022400340581d80780725210080000035180e00948030300c00807810041c0841c01001160030400780c48040c0c0c5d0729140d070303824200d100c3c50101c94450981100c8070504c0c1401520280341c208880d915849050030050710401c030b14010301641400b0303880008104030100219001300051032041d200d020550a6032050340c000241814400b070808030a001041000d40103a81c5c0204005a00020a8940160558400c003141000d06c403a0b500107070820240a102080380010102e0340d6218601900050040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 578801978 1250 578800728 578800759
    0x109060c080f0a02010e0304030c05031612020f030f1e0625030513080d0e070506040b0a03050411090906150a1406030a1b02010903090902040803250609030e 69
    0x48100035280108811410000c60440c0c0740950082d01d0b920070184000151416426040c0c0d107076604c070340c1041c0d42d4179a070250100400d2900b08440300c1054602500202c400d440c081000d1110f00394250021310440c41c403000b102c407903102008000c0e5881562001c45100701c84401c7e007480c1d82d180682e41e8040328001c03d400244801403400e0301c016100d0841c01001508002d00000714000d10b0041c0000401c0c407407044200c03022079040c0003d01690761240300d002881211a82c0c41e185440081d91200307000d85018001006202811410b80b031115015080c0480c1a40d0f492030280052001c000610b584208100c2c00c0c0480c0c1d90f0009862480342d0302c2000394038482c0c4541020417101c07442d40e00c50005104140c11500e9801c3c00c1060103160400c85000000c580e03003895100380d00f09001c1125a80c1e0050303540d000c10070149a405000e2500802c0d1281e030861620b130806c1085c9490f48201c09204104981001142d0204812481403409041d0000742c20011007030305290060491400511032131046031401c1c3d0400c0b4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 578803228 1250 578801978 578801987
    0x7020a0b09060a23070804212406031b08060705090a050f130504110103150e0a0c050c0f0c1512041b08030c0f0f150a09020409150506010906 62
    0x2040703040100920f0914202c24000c844a0007020038124644012002d903150662401c406018150b10501100d51200d050101c1c103514020800d01000c034414014003240041950517510b0b840e80041e0315006607000d0940c40d02030020b07182941c030061210805510080000a810441c8005d4420320300079a0b0342a03d641c0012682401204541c0342e00041503a070410187c41c1000760915040e40c090044e46d0300d0a210071070b260448004480c01d480040c0b40181040d11503926102c1c450440007501c000554060074800403064420005040444660b0f4500d9201c204500070015a5004421312040351070383da200d400d0640d00d480426070b20b0781c01004003204e00460920400d081d41e90080d0f02c08009481c0399103903102d01e0043c14900d070035881820288803000c6200c481c1407000304103550102000f091354090b40c120452400782e80c04074001064000c2410545049808610700390884003885002c40c109005000040081c4843d41000700fa2a510303061011050031290085842101c0036201d4006007540e9500649 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 578804478 1250 578803228 578803237
    0x1509110432191e0305031810020a05071e0b040b040504060b0f09130b030703060b09010e101202041506020c09180a24050c040315060b0912010f0c0507020a0b 69
    0x110300102402060100c54240510003200341c104003d8400c01039600e441d91420359000340000c0360b0740d5650280c0d207645804c0903d4100c0303110f45248000e0105801549515071109110b004101c0600c1d05840207420030720040c1508400b038240440c44e1a9165620007810066921521406000754144640040e00454410580e1120714110009510304031400007044811262804c003100c0803a5250400e00142e20200180009503110302c0c000501482c400007044400b09d01648503803042d106000c100003282149609040444000c041c0c0f007500e840c0540300040141400d0150401c000d1070756640022020350006140049140680e0800c4c505c5c0c072100b031034544d140052402c2c20b07603039800f480d03241001a044907090f80c000010900403d41683e0107080340d805480054030045d51400000c1024001c0c485d4103010725402e581b13201800c00c2000d07e41103915445000c0c00c110340e481800e0220703014030212002c2d00705005c481c40c580020040701001e00f0020305141c01c0840c0030703802040c03144c101051003001c2d0000c54 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 578805728 1250 578804478 578804509
    0x806040b06100f03050601020a1b0302130902030736051617150d0501050411130204060c020d021f080114150729071707031509110432 59
    0x3c140e28202d200c05402800c409001e460440c441c20b89040301080c1d0980200c040148800c56907a152441d60040102c1e035101c0c9404400c1061038001081d006075000644142241c20000070803042001421183c496000000d00c8040001800c01090f031070940d440e800a881114885a54000c4c1035003100708030b0301d6180c41c1c09000b2540440001054141c07a00d0000303c84401801449001221155038078036095840c2a142168404050107182e50b05182c0300c41c18171040740c80c004045040c18548034008004c10085c0074064000c3c40020804020741d1030711016401a103000c2440c0780c1019400d0540146802c07001d1183c81201c800794110204c89142126004a481e0018880c0c0c3e0b060011684800040124284080c180c00c120400b00c0100180a80d003c1c0348150039603261111842000c05c1407521004004201e2400c0514182400343e0110b40c80d07000900391291020005044544540d100002c6d10858000704908040400d100300c603000000100966580282d802c0f00110002400b8810030b070140c80d459 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 578806978 1250 578805728 578805737
    0x15030b1f020d080a0906091104140c03060f013b01020304081c050408240a02030408030f04020f12030d06330207030b1302180106200f06010806040b0610 67
    0x560030b140d1049104540001a018000030b1200d0580c0d907040407030f940010102c0d850000c11141c043c0b145094801d1012a1030348040d21181442c0003182d2040510005090030703c41e16198a020302d041e40704515072a0b120300c400010303248032564005000d0007030074810b90800c220391058010072604c1d48040140ca080b03c0c10000181a40100400c01c070030a10468181d030020003209100016848004000c0301c0780409506066054400010041c003c0341000141406005030040040c800019035a81c2260341c000c07040d00403080562100c1c400101a8940c7c0b000b40c507480b2802c140c40d0400a00040020400c0d003822260030440c1503a61444c00d955008400003014a40b00d4110b419080c103040b54410076513200a03803040d42d035043d03100d9482c190030500c11382c2e0222010440003801c1c021814420900444001c12030640e00c1d041d03141410080c1040703004d1518410b640254074405a0f1070804116040000c0c1c410002d40d0660b41c3c44941c2c01d81d4038001110150307080c0c01550301088460804640c84040c1d00100d44d40d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 578808228 1250 578806978 578806993
    0x30216180c1b031d06030403050309011118041d01050106020102090f03010c09030b180d0908010f060b03070318050303010902130f030b010b0714010c0f02010b06131e15030b1f02 78
    0x5098640c00c03810802d2100c2643c1d040000c090300d40d1741c107006610075032081d11881c0d20390130013909450845500b01e0400c1d21416041103001c21070300307503200b48010b844011030740482e4202e603000320400194060b0603c0c3d4080d608010011030f6403074046d00031344120340e000e880075841c1d02d0b14a010507007138400180904e00032420900080c00420000c010107540303c1c00c0c83c00281c400c9004000d0145c41d148001040000164151000344078942d02070081000c6036610441c180221402c240c460589888081d20f40f80a043c0d44e440d0140c141080f0640880c100da4200040c0c90722580c0d1040c101001c2d5000382d840d06220b52a60a002c00d00c0b00040b03880741d060340d4102d00c150380c0c1d980c02e1681c025200c1c0c0c41b803401558a900c1400340d6450070300c401d004c2c0034810f15444d5110048007420400190a4400d4402418403c500600c48640a0241400c443d0215005004001c1517041c5080d01c0c1000084103410003110050740b0340034078100381c0e09a041055001000d8548000701000e100c201c0c034503a07010060070380c0180c01641 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 578809478 1250 578808228 578808233
    0x3060f140f01030b0c0f04060c0b09030a120203060a030b010f03020123070201030507031805210405011407080c0a0c03051005130609140d0206010810060819030216180c1b 75
    0x83c4241c1c0594038045440c40c2001c1b00b820321070303142c000ba8031020014103004031400030400c294108641217450000214245250308e00094182a40006507000f015808000a00103540c1c410224000b150801240b182c0d030750710341190f414900c0b224002a4041404038090501e44604040c2c0181c2c00f10151665074100815940114080d0101401340350815446201c0017071420307400341c94001d07090b00c10001040d60b410003802c0b04444014080b011024000180001c00c4140d03084200b001020701143c5109070b03501540d161410722401604130b01c2d0f2052123000503101c20004400c4007042030702d0080088604510040020b1029508103c4607150010001224840050207507005100110322030762401c507444c60007030b41e070038074190a8286460060748003100400c030380141031040e004030350001802800080e0600040b40d0b55081c00ca040b1100d5000d45007154030500d031003886203662411888100240351942c0d0900c1c041c0c00d45d000450900168580342c08a14039078000c0c1a801600c482c42c5c084c80e8400200c54 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 578810728 1250 578809478 578809493
    0x218010e0303040e04080f0a0e010f110d1b080406020303010602101e090203010f1a0a050f010f051c020f04210b19020912030310330c0c03060f140f0103 67
    0x3174070458500d01c0500012921000d503074090103018410341d40f014841c650041c00101074100340f0200740300380800e02d0616100c8401c08540d00700600414144850141c0c3c2c03c01c44040304800e140b2015140e040042008201b495010008504843d405c2d070843d00c50380d03a41c100000c101c500d20b0860941012409410322164115600308100036030008000042c0c20b4400e03403507081669070041100c00207070b591211247c01842c00504c0c0d28050305080d21801805070f2408000391102c0141e07206036060003008a020800b88040420018109032085010b64403070360340c40c840003110380050003444104600b40000c03904a10700d040300c1c2901c80380c02920140031030701e03009800000d06042c0c4c40f070440029020054800d1300c0d00c450383d1620701c80550030011036030b80c0b401011110300d1188a801c41c010035100701040008070610200269414012143e0707194903055101010340b052812080d00610b44040c080001091000c268084042e0703610703c0f00309001e40301e45045c82018004044a000381900d42c500010710100710107 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 578811978 1250 578810728 578810731
    0x809030a2301142805010623070209070509130908090109060e010807050c0f250f06050f091f020f0c060a0504090905120705060105011b0201021b0a0f08010218010e0303040e 76
    0x400001d290101300520309502a14000d030415808502d050030f000040004045601c1404200c0f0200c083c1071250b1a4001407035054060040400c00001213600c2120703071760390342c26139003c4c61705003004108082542c41d01c40c1c6903400840f822400b0400403240010414003c005196441005070b440c500640d0341d000b0259106e4000841c2c84503035100705c892061131040200400300e108078011000751100c401000802d46034640c2500300c540c2c07070f15201a0812401c0d801a0a0f94440d4140800d1283c50703013004008640901442c00500000481031150484c0290b0003182031409800c1d008243c030040007481052051501c0761040d070f140000c0c010003080010403d1a840801c11900c07407400d4485c010025941c5023a2a000740384182ca05400c45001004a981c0003084207659007000d4007030b00e1894a0302e80010b07440304228022105800081e910b41d031030669076080e4240260540d5a0090140b07600c5181c40da0007500850080348504138400342003031456028028117003075460018010351920b820300b1030502c0710410 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 578813228 1250 578811978 578812021
    0x50d020112060f0602030d11040803030a0237030f050709030f140604030f0909180f060b120f07050906030607110102070f0303090515060a120809030a230114 69
    0x1030701e62000c1000220240c0c004028134560b40156203894440c268081190010401024001d034100002c005040011051b80d901050041006881e104030b06161648011030610f5100c1440d422003401d040302481006a2107042c0d15075404000085000b5540c1084841c00d65402022038400d000410029100e500d40c1c3d10f4940c45000c130746a1101007241110b01d0010251001c502059030800200c600540c007003003a0001303154844040c00b4450500500d84074800c10480e02070020301008034100d00707200d581e03000008181405092422121404558a038880c0381100c654440d600641d01f0002321751424a101c1c41c055071004002e40560745a103803050711100b11106c0c3c4414a035400b401076502040280b03044003c0e03980030740c8000c1000403061038694101003280490681c80d0f881030b8144420780e102c501d0b2607025104807402c2442c241c00780782410030310f50040c404075a60503c0b8040c60241000348040208598071807140030300c11124004000746003a20960703242046c5043c0d0550000c2d4940d000201c858507002c1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 578814478 1250 578813228 578813231
    0x319050702070b1303020307080309030d020705090105102618070308090415030f0b0103060f0e0c09060105070204050a090605062e0c141c110606040b060405100c03020d09050d020112 80
    0x1782c1d69408682480d100b60321083e90b03a0000314514005040901900080c000d5910290a01c9414800020200c0d08107005031070080043c008038400d82401000301034251002c2450902c1144020508512046000c86143c400450302c42038008542c1400245d00342a03030360088640b0309150301581840020000403481d240d510442304000801302d888583c022402034010000004d0a42c110b081c81d40680301400c074544c0c0000e10f049041440c00c43c0204450f00c003e041140c0800c0c0e162608801200c440c0240000698011314200a00450034032607440201840d1090105220360b9031a00200050381180c80007000e40d98003404c10040483c0f2781401d40502d06410b6090981d004903442d1502c0e80000c1c415881f03190700c3d601964a80c001140380e681000300400c010302d0522060b01b007503002c5035107d00001d400b10380113503200d40020700c3c266203800659000e40300141800d6804080000000e00c0c2020101c0c0a8000d40140300b07140c0c40461041030600d0a5440113081940e5404e8281d00440f1a40b02e40c425040f00c15 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 578815728 1250 578814478 578814517
    0x10b13051f030c09080d1808070807030b07020102071a040204091509140d05120603010207061103011805040f03080a090204020c2b021905030910050319050702070b 72
    0x256100c8501c0030316510001010a01e000c1482000341c1203401d45a07050307040c814402020890004002040280c0d484545480c04030700540b81c2c14a500c2415681024841d4040c1c0c09010940b41800a190400c403400f803032112100e0386841d82c0c10ba00300c0c4500c1c407000d0240300c00b9035101c044205082080030303017261001d0f10014000f031041d2211900d1601035103003482c0603500d1300015001e0000069100128114007009092070b0203603800d014007140f081c079040968681c400c00c00501c46a8003035040d40c00381500190b0034043c1b001050b40e003980c1503100b40101046044803281c200d516040d540320f124401c3d07901140403545e0800680702603c0e425001041e85540c180c4400204005031114009041c600040000600d20210305400c00ba8400292101c4c83c0200703100001c103442d007186d00103106c4441c510320080c80100c0580c40d0030064154480d9040c00c541042c0d648080200c41648007008600c645401d4130f564a8a04100071100c003603a60682e0710800590102c602404903071103400c0101b8900000e00d080d20f144 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 578816978 1250 578815728 578815739
    0x121a0c25080d0218090c0901030c0c0b04030203040e0a0b13050a0209120c040b011107090b2e09080102090a1a1b01020318030309070b3105030118030503010b13 70
    0xa9502c98841c1c04510307a00451100c0a540c1c11035014880120104e40d01c44a40c81c4c1094904c116024928081c0d04154071402a01d400340c0c0207148141d9203d070051110b51a600d0700d410044c1d0b0300c0d8018401c0040f5003440d00c0008140d06114031400035048002411031a01d550b00551131009088042e00c0c0c041c56503405c004010b443e0f500c80070005000040706000d400c90900003000c001c202d0b0302c410700c420b040c400110031551101c00086202403e940e002c1000040c9180c03450081005959255a0301c003041d45031140c48084c00c1c17883c984902500100341e0350414840d8403441500d00703074021041c28681194000c0400d104914031034040702084040d000c40c040c100a00c0b540d42c0302c804581c003415003209941c0042481f0007880782c5441c5803040c000384001035266003040c0301c0d00c45d62150b6071700c11110f5003000400c00e4520301d900301c20440030b00014258110030940c0e4041203217a14030f4a51080520940c07801010b0f480c441c2c2440e00c540921601502c1302801d680c40e0841c3c0e5011070303114900e45050324400704000b152 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 578818228 1250 578816978 578816993
    0x40c080d030c030608010908090d1a0708160507031d0f04020417010f06290909070807181a0306030703050601180608070e0103031b050601121a0c25 65
    0xc0c4418199004141401e0a1002408451858005820613418000302001013004901284c504103402d84010b400c0d1403e81c20903401704031001c940d881030f12090809208600b54004020390048034110038100b101c0d000e121f0180c0b95441000c80040c04500a1507403c0600c100e44104104400e00140c489504e0498400000d002c9910a03082040b040ca5644045100200b003445160008405018108169410b000a20010054041030301d003000703000104112003000074209446d00c403003001d48448458146004013910480d012500000081c0f460500c040c20343c1288610f040072110040380740890030130003071310794150744d400209615018801c003400000018070800105000f410381e201c1c4c01142c3c0b222070501605a40c0a039104260b00c3e030000b0014002e10034100e049034112641400d01500b0054401140340122055180c00390403409028000154a040b0001c03160341c2900c5140c101c802500d10000d80054220705031510826003c0034019203d030f0f2903070308145071032401489845c05220078060795030b200d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 578819478 1250 578818228 578818243
    0x304060e070825064a0909060c0d0e0a0b040b0610020a0b060d111003020913060821070510090c051c15061805040515010b030609040c08 60
    0x150540c0c0210010001c80d0a0041c0031146103e0311039400614078034200000b0106a5140541081c1420207010a001c030090b1030400c42d032010074480341595451103001c2c41040e640c0c502003414001c115030350000741c100001040070341c8100e403208109420481104005001026428559011481761130b010f00042401c9500d4180710b14851070010b4210b20b0400705207c3c0d007002c200b42040655101c9003000740003413100035005c0e60007a010b5808601001c2d035030804842d0914900304040d00303c0c1c1600703c04448543e01d5001880845400c0d40e00200007040d204008007107074064840da4605070001c2da40d040c01044034250700c0e520034500358545402c000ca41c0d00e0751400c059940d00728a01090340e4018440400003040001d9006100c120f0340071445808603c080f600c110a41000242662045240b400d1b510301d00f079200d000a8141504000320042c0f4035400d40300103210540301a100f1b44a01d01e034284040701d480b2030150580f03600180280c110303101d0100b401a000c0014008454030500301c0e07004900030b0b1040041d103 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 578820728 1250 578819478 578819489
    0xc030417100606090303170601030605060a02060a0b01051204060203090c1903030801270c051902150901020a050a0509040f110702090a05090a02280f080f07060c080304060e07 77
    0x14140450381c1e60350a0308480403a4012014001540b00801c042500702d9158040406241c200202c580d072540300490051500b030300196031001c004500000320540c0010801e21400c20800100402187d0000569203030145408088012038803900150008041d41c002c0c5030010420702c00c481d1112003079000202d4000030040350311141e0301814410810b060741300c22594010310f82c22030340500201e0b000c403803119000005000304039040c1d00c4442e011001c900c0341045500300d415006070703951150300c07842d030003502c5401000c2c685241128640101b1450300781842107078006103c40e1503d1b4a480c9030300c1400ea50755004502d000760b01c0799941b145598040b40d140109003000d03a44603a4190744c1c10540c410001c000d6006004407800615207000c1240e8000c3c00250148220f40480340031f0000b500014010b0940341e1016a040494140044001650b034803811075035082d126044d0658a0385408201426039501940c407030750000035515600d0a01203142d03a001141c0203030041c0804540f1140c07501c22240b070841258003a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 578821978 1250 578820728 578820733
    0x3020c10140a05011a071b050a0f091b090509150612070f110c13021e21060603131110020c010e0a050d2409080403022704080c030417 59
    0x10462684014403c06014041c040720f84203c1c003c01c070903003100500a100e401800c40203800100348074191390004400080c200200b4004a0544030b00035000d1201881c07161800580c20071125000c3e42c0303440203a00140031056036504085515203420094280f00180003a000300e421805880310711746840000380790f50070301d0002d80754441c2054100100f006010881c03000800a1301545a29902c2d0041212000b00c8401c83e8144030504400c0e080030000d2161240505450386084181e24680e8010740141001103640302c4140c42c2c0380c2c03189000c05000d580c01c6030000d502c81000c00000e514044400d10440321940a003036114001680000481d5403410101e4103c40941c0c412504030490350707071102001da4410802e42c0c0a2141500e00b60100d003d400c10b44400030171814000c180d11580c1c00811040308040307003214a040c001d52440d4240403100b54442c0c0403ea0003407038001c0441d01072001c445090b0896000400d241c00c0307d680d03207032180c010381c2c0c001514251070360108110029014480490445242980401 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 578823228 1250 578821978 578821981
    0x5010504051822033902010e04020c010203100f0e1005011209020d031706030703030504090b12160317030723160b090d020f060c0a03090b07020114070e030d03020c1014 74
    0x501001c4c0d4100c0c0c2e4201c00601011502005440807802179040c084c80d170a0811201c81c0c03c01500050280c02081166151076101104110010100d5138242c07040303d51842e005012161a14007801c0030503c00c0350b400c86845425401001594413807e0700445600c100040003454001980c0050303118400524281d00045003815440c40c0c0703c3d1444c5000390440021001044003d2460380c0c042c041b03001f03910074029031603034501641c1e519441e4604242c00c001451001d8030031303a01810140c0c0c3d000460500081e658107810314984420041c000c001c0703901a0605403500318428021a0500e03900701640303900501041c100f03108488242200c5001c1c2401244240d06040071440c240e041a8a401c40c803426240855000240c001d42e080360110f1504d40200c10241d002d50344940302c010960140010140092100700e1907410801d00c60341c198000745402c0c0403010303e1032598685031011250f2444258581c0e0b4907402c448034402c0a0382c00395006040384c2240106448192400810203011a4540d04200501c84800030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 578824478 1250 578823228 578823257
    0x40f110105090d1515080c06220e072601031b1802090103110f091215180d08070210391103030c04181e0e01060501050405182203 57
    0x25039085c00320080c12040785940350580d0035a8420410080a0150100240c0c0440c0c0c4a003140c40c0d0351300c4010944104c0b003000d954900101418004441080005a9401042d0b1000464910703403480315041d030682a030381d6429501c6030841060000321035a032440c800400000c0002d03801c904140c2c500352403080140c40308076400000d010b031505a0000c0030107480c20003c4036000f0a541d401d9510583c000c0d9101100d01c503004095a10341214004026513083c1904200038102e044021840b81d514281d00580b0f140a685003819241c0034400d81d800030251b08000c3c250000d0820302c1e0f101110110081d048800c1c60503e0249a040444004421102080c0000a8000b51540103585403107001c0c0c416006500e076191802e428070b0070740518018a812407808072411403507118550401c016081002c00c00440308000c07003a810005100c080310003030030f95003007640c00189907000d07105550496030007811034422000e90004641040038010000d1540b06031000003040448400f10815000c94803070b480741200c00b01c3c80c4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 578825728 1250 578824478 578824481
    0xa0303060f050d2006040e04050718021204020f01051303050304091d060718261c0c0b060414041209051020070b181002010203040f110105090d15 64
    0x2a0451801210020500000518411000868080d0b041c48051300e1640720303800100303d403180303a00c1848502405c005002c14014041041c3c01251f21510401003020f07424807400059000e1390042c0030400b5036980000c2c026040042101604003014940f8515190400120414000c601c0c3c00a0b10035500110f81880f201400384101c3c00703e80e910412000a41c1c61018271580c0d94800141290200a0b9501d15640603020458601001d00765480c0c4e80c1841c00802604403111032100105407105100304c0c003002c0d0030350105c03c8544010424550b10310381e0190050311407007103007503015101940060380c0b06e141c1d80c0103800c4409480d00691241000e41c040d410ba03d40000e0125403d178004601c02e082d034442c440070313a0f9005840c1e150780e03245403100b07242680c2e102e0801c0c508200789544682402100014160103a05080701c141c0c8112004035010b00f544510300008034200c0c04100d40003010303100c2540b00f040102e021034032031540442e0145003207403400c80c00318040740c1c0d1002070101c00c403290510b1240800845185 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 578826978 1250 578825728 578825759
    0xd05040b09031e07080d020d0902010e0a061b1104060308070308060312030718051e03071208040b0f0903100b10140f0c0102041d090709091709060c0a030306 69
    0x40500550625141d9411903982802c0c41000f0804420001128400c005080040c1c50300c81040b07100464513088400c0000c400b43c00010f404a00280889031100801d10b0040210ba066850301d9a4540c448400d08124551140c50200161403d804129000825655501600010310f01c1a0585600c4602603d000307028105c2c05409140300350801301110900741c000e0300a403584070350343c1d10300041100c02c0c0d0301d124240542d403030300a41d80019202885075085a00380518050b20402981158442940e079190409030f40003490740140070704c1003040f003009481040c4000c0c08a20f1401e80070145008600d0300060300e004a4266240c1c5100d480304c1b6070b035580346880d5005414110090602980d840c0c2490303044112403040501c4003592030000b15444050007000d605441c0540148820703410a00842902a00020021101ca08181c401c3c0c480110f1201c58a001ea0140340380d0140c1d00c003a00c0640c40551210542100c00c019030464001c2c0061a0340d0a0204030b0030352910301a0310300040ca40d0409914a00e80e00c034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 578828228 1250 578826978 578826991
    0x3170c03010e0f07050705071e0e0c04170304181d060411040c0c0203120c0105100812031918050606030c01080a1503050d0327030f0f03020f0d05040b 66
    0x101400100251035502c000d4a90080b2003c030444080d940e0081c01341c595008014015080c2e01c2806408141c0080d80c01549002010118851100c107503a04112950008115a0100c16007814007040000d03035040c0b82c00c00909940d40003601c3c100340c0c6034469641000e094100c8003408545500f650a40070130a08085504070400741c019107500e14040d150000d00a44200040340600d669080644200340700e03034001b003c0c0307036401815144000344a406c40382181e0011504415994a407102081002240e480c030001140d01c3e1754041e26411008031749034a0540c000a00c840d5240c00c0e2008642034201c424860040b0134040017031500c03003200460030403900d003c5000300030902030b500c0760513100180c2ea0480c601c1c1c1d0388083c00c542c01159001c40c0c5000180000340c90f2344020150320a624440030b10f40d806410001d00c0c41c000c44003402c0540c031307107a611001c240c41100014020074028000d01c0798043c40354a00620554031420054503001d95460f85800544c4204c04c0d00c8601941d03202400100030f01d5080b816040355 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 578829478 1250 578828228 578828251
    0x111503100302010f031a090a0e07121e050d1103090913060c031104030605061c03050301060f0f08010b0c160618050604080c091302040f0506030f0f07090f180317 71
    0xe09513201d22000c1d6000740e0214800c100d0f440000300c8c1c0a5068018806588048c41900d4183d030f521100500d112020503004c441e03105140c00f154102c0d44040445409441c0c02000a010040b5410825034000c03440d1302014540d40010007001e08180c841032100c90250a4a801041e0701c6542810080c003102c2e400f1415104150038044841c15054410003500c00381d0f0340050300095075841d408006494251114000c0080e180d080030f01000341500440074504079200d42d107d610900240c502c0481d84000f456840d5030201d62668010301400906401420562110504540d0b02d145030030a40c1304c11b6643d55010308002000504ad0390300c0c0d4a40c0b480c03014002c207019103015081c14105201c0300e0700c0c0c2c800416180e000b04405e800140d07d4030741400039126000e0300900b04000c106c071111564409408210350707260083c8907070004800c407142300040e900340074540c40c0b0281200c1130400e20311101070000c40040802c100d88032403005082d45d40000c420043c561090b01e61507003d0302007450f00c1c604400010031414a10 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 578830728 1250 578829478 578829491
    0x302040e06090318030a0614010f0603020304051e0f1509070b0301151b06020301120b060d0b0414070f0906090606020f03041e09050717180a111503100302010f03 71
    0xa850382c500c01c045504004244d400c0c0800c0c503041c40044094105810861198014006400814141c85030078010468081d140c55054081c0e100c2918010810b070b20452687d030580c24a280300244c031403141030030784400d24812008140b80c103907a001000c855407900380c1440a0120100881d9009202c0140303842e00750340c94034001a001e400a140f4010512481c034a0b14090410b06100c1a1078042c1c3c0040c046449585a039140031441742c06903000c5408404807800300300c80340f41c1a10700107001640a0b010141c180e0301e65440b0b410080a108949070f4030320600c0c2d40400c08030100030040c8041c0600c130800194403850004860281c0b00c0300da010a09540110309803000c01740c4040219425110801101c0408000c0d901914491096990203403098a10f04400e00500c16030004000c0c0c420b102c000d00e0f58000e03482d140446d2280a16514401d8210b601c49a40300d8005041840507800e9924000c090012030010400e0082a80e80201c80240c01c44c0c42904040c0215a044000c402d15180a8035081090 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 578831978 1250 578830728 578830741
    0x20f1e010306050307080616020c0303040305030c120f031609090e0a0c0e010302011d0a03080c0303151f1d04051602060109150501110a1209050f0316120501060e0106090302040e06 79
    0x12104041c16236000424103c101e04000b40c02000030000c20395000c2e003204d5480d5a00c0c01d0480d200d030495001100320b8007031584407503140c40701001600d150b0403014411301c5c0f640d03c07607548a1544c11301c3d01900d501800007030040010000624440da4003002c00e0034002c1d000e00f0159140c40104210140c0221000c3c83c07a000062001d030b40d200c810b0f100d1000600002105038040003000031358003000c55000400d8040c0000e20503408030800b0025500070307503004402d00c008242c00b4040041c2c1031000115403050018800c8000b2413244074580014003120801c00140c18080a080410155030302103a401d204640d02d035400d40c19080e03042155900400710550304200c0c070344008104400058051081c1410001422447c00e401c03c010b01540a5169204160102c0403000810103000c0030521b1140510490003240b00308400e0030045018004851511600d40085040c150609400320a440c0d043c0d443d5035031007601250450030524154040c00c07154803140031051552041005441d48001e0208068025009000c007 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 578833228 1250 578831978 578831983
    0x1120512070b04080d060321021c0f0e010311030c0a021c020303062e0206150103090512031305030408010506120c0f0603060d15092102120304020f1e01030605030708 73
    0x7000f5038440710503170f43d594142800c0005400d50344c10140c020300030804a014041240741c04a40046850307000c0c1e440110001b040300d601284036840007008905044881c0010300d1040500343c02d0b034001418001100e0b002c8110014403500201c9504690b0030380000c03070484190b01000f25016200c00000590b209103a24103009403a404054442c900426070300716084004404030010440814402106400300407400e01c0096a8010a0760038118443c800c2031030f801d45501c40d0268405c5d07a90000e004000985500241a025900081941e03c0d01c96250040c0700008000b8801030006198100c00415141032007801c11911820098002c640c5500004030000d864650120b03004403804115034a5440359120300105181c1002c2131030041941ca8200c0c401218001c040d80000c440c40d0080001c1003100001c0c0344400030000f001d440042c05a88000080d03484009030500442e8014405491240c000c4070b4613001c141c640d01006c401c40408411a64444480e5900d4841c540040c40100c0042c10b800d864110b40381d8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 578834478 1250 578833228 578833231
    0x3031009020f070807050d081f03080a0e03030a090302040b010815010c021512040b010501091d07021018020f040203010b09011b122106150318020901120512070b 71
    0x20489034020900e10308068000c01640c0355141c0215905070350302171505d000c41c0c0f10090003600402040304580480c860070350300400c0d0902c1c1207640d4510048075007140c440b0401604001c058400b004854a400011610144090b00c02404d05e1b44800700428214410441642c081804450410009904000e4601c60088201000900038280110315030700342c3c0040ba29513814500d4207100000c000400d030001c0707007400707981601c200e02a50140400d41d072203400440d01e10016118018580300044104140303078a83c1c05076580c000000c3e0049401c0d401d001d04108080e1240c0c9080014040c2c900d204041c19803d00c243e1407003598208880862541d810319442c101c0301d0151005460420003ca8802d000b648500c16a113010315800848402c1007244508004210184502c161251482003941e82d54400c45c16005c2e8005580c50401070a00e1100c42c058110f008103101034000440c8210380003460b0141e02c4491159019110003041d105140c0070908083c0d00d410b007003017803580e55031400304007410200e240b0308001ca = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 578835728 1250 578834478 578834489
    0x30306014508010e0c01050405100c05011b030e070303140a0e0409050307030f020607080117160f1403061e04020307090e011a010e03060106030f0f0501030c0512030310 74
    0x40941c40500007851004079444030401040320100612010350715070079000c411181804001e12458040d0440b158480c50a540e000340402c10922040c4210702e001100c0d5403004806260065a202c0161251425103004c1d41200b83d213144000d40418501c1e605020306140d21b0381030f100620714149035a9005200d0508040c5851203a03c010441404a51041c29402c4407408002c0c014860500309003410f5850340d002c00c0048001c2004040261340940c00440d02c144940500d4461007500e80c81d1101d00c0d030000a1110507a081c90290560801541100c4450310b07020b4100b254254500500f00340c0036807001042c03e8140d40c8654482400c02a0010510450141c212095005490207440d00e101107403400c3c05a40007500c81c6424120f88282c0400c0551081e051400b96042c240c101c8040c1c4001501d46e20706059a454040e0028401807000c1802500030a19a84c08000005050070326030880d042200c80c2a00b04a801912440003040140360004203264804998070140d40b031410000c0c11081880110300c200c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 578836978 1250 578835728 578835767
    0x6051c11010e040f050708060d0c030f06181209050d151d0a03030c0e0d1101032a0c060615020712030905180906011a22081f05010803030601 62
    0xc840c869100b2212035144100c0544240314040c04600800d010700313000c4807881c00007034600c6e0001780b5070700d440300c024400c5a41002d5003c00050541e01c42c83c07a00f1302c40400c10740c0c2240c0c4500d080a00f000c130010503910458050b048450b4200b010754402014000554440c40c07255610700ca0040104840e04540d0441800c1a240000c4c46580554100074000c2e824464401c68007074014140245a0903421510322400c403aa44e440307050004a0401084010403440641300100112481c400c55003e54411140c0c00e0303417051501c2001781a04103408440c024042c8150004010840344000c000007401800043c010f00ca035001c0b0300401826000b50745e49010302c50b00004105608948040c18066042c1c00040e200280448048901d824440c3c24042c0c015549a086482610000203000c40f010f145245100071880020b031404042d002901d843e1086141c80220070034120a00145c61801004613491070302e169034858240b180400640c40172204140d00200c2d0380c1e0001c004100300d680e4011081d0104a020305007 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 578838228 1250 578836978 578837003
    0x3060f090d0309050f011104080c030d050a05070303090b070f080609160807120c1d040515041a09040326060109120311060910060b0418181506030606051c 68
    0x1081468042680c2c00324046504c0d000c100387e144000000244180e84e29002140d0f81e01c10300000381503413440c6a40e0b00600280d02444070f02c2d800c9106100a00a8600914010038403040da51902040d81c0410b42d28080031403542540b200100313030488100d6a0014040382c4007841e610300200c01d06080b01901c40304104005c0d20b200041c1160340100c0034910126554402002a415121000ba042054541c0201030300300070f0442180c0b0618041c0a40c41c41012262075601104160800303220190207400c0c984200701e0020500e00341c480e107030164020300c11400780ea00c00300f000540c4d05480c03240301090042c4410b0421400c042011a0740c2040140c0129812204500105030040c01c2c11580c48601000c802c150380110b40074083d04142c001000c81c0751400c00d40081000a5454001950034070491245070724200c1c42c010030b1201481564495201d0100d8480142d40b0681c080d07407131060706200300c0c1c00905200d0b55410b05009000c0f50341700d030f400503140c20303905840c920712070810352082500e00150041900c0e50141 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 578839478 1250 578838228 578838233
    0x60807051215090a030e4e1e070b0a050f0c010905060f010b1204021905060403060f06050103050702100e1c0801140a0513230406090203060f090d0309 66
    0x104244500e11082000c142a003040c00f2800e0f100e00e4030b40c3c019000507200200c16039a40c40c0820000c10010030001074030102513929000f0104102252442e4004c80c1118000c1f032004228888019101001020180001c01c0881140221a140381c00d605545580100c40a000501c541c0086590080407414610303200c07000c140380c8510030b00c0380c408401665403e0a142c3d0303007003040018125019a401c064590290381e200e403002100c0d4015075600040c000800c50100e400340c01d0005003802c0083e00418500a65510788020135042d500c40c2d030040710820381c0c44210b0201030020348166401343c44240ba003807040f4203022174000c1d9100080c04904515590703d00001444080070000303071013004040d0752818404c05400341c0203401070310240706030715141d1000b00d510a12440e0a030300840a4460050807180700040b101a80c40007030001c4048040841007018520140c0b10f550000907100e01d1140e2804602c4903440c0c030515003840c1c406000360004064500500002c0b40000c219013907140d002c0c0c83c000803128202d0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 578840728 1250 578839478 578839483
    0x603060c1c050c07120215060102010c14130f0f080d0201140726070f02010f0c30020f040602160506091207050904030305100b0f030a0b010302070204060b030a0c030608070512 77
    0x4182c02041701031450b5400c04100d8001c101150030702100040e420740c030b6440c1001a400e9545051b0803000040c1002452101601d5040281541c40419240c030b01205403200c100c50308584e00c68201c500d5261680703404012208003004007081c200f64a2009101c030304c0c00312010321214400500017400b0302211142107490005074007100030611000c2002100741f03007003049001d0503140d00c1640c803a00650030070035465060704480c0100b0742d02e500700f07554401e0040000141d442180f41c91350f040c40c1d007820741c0e880445283c40540c00078182d59002481181e584624002d0080d10f0618400050030350140c2d03184003000142d030b50790251a10380000352111025003146408280c2030180c00d802c070035031080a64080c8014076906510182c4100314141008134030980780e210903002e41c0508034801e5408070702040042c0400381641c0240d10800c1d418107002d402c0a00560014051b54001c0e000a004d50300044200056800b042c0110310742484542070410034641015190354841d80389000301c40c00b8070070952998239404400c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 578841978 1250 578840728 578840737
    0x20f0f07180e0a0b0c091318020d02030f0f07090606081315060e0a0f050609040809010302090f03030a03053702130b040b0405100e031e0c1203030603060c1c050c 71
    0x4145030701305501d41100710740041d41040c0d1015025880481c0c442c941c1c0314542c4144d50801030040c04c02600200c041d804c0000080c10b41000b02d0701401201c1ca006035603501040040c000ea6080b40260040e2802c2c0340c12041185c08991100741040910018000461280804003110a400081501c42c0d5a00c00444c072002e4840c0303901074040e0844590410072100c6550780240c6110140c880b041c0b080c0d460305002c200925a042e02c001d42f008030104012032982d80a94002d1800c05405091140880c0d42000040c1c1181c000485060210740c480c0100200c8080c02e542ca410b020110040d04038130b021040030390340c1e140d03a00d0f41e609940d180e500007940107440d60f070302c0625401010440b075403513a41d40d11001186502d800620034070b4020041441d48558031409022070b0002100060020720300d0240d983c0c4445045c0740b901e030644000f405900d00c0c407030881d11604400070064040d01c004599030f0400005040c0781c00b000416609048805000f80700140c0300c4d0882580c50282003060116144d142c00180c0d654512a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 578843228 1250 578841978 578841983
    0x1f0e04020c0f100c0302070209240a0602010911040501080a081c050c0c0d02060124030b04020324030a0302150702010221190e28050706020f0f07180e0a 67
    0x3202c202544864002581c2e181c000e001c0071062281d80a03889094003640501c25000758070280200004800070704443c1c8038255402d101900e0089160008082480c4050981003000141d45071001542444045443e8444841c010781d030406c03441d03142101003602c51151400080441000207072030700c03070301c00c00d810800402c9805400c2040242012a24103090f6402456070301d1076070103021b0082c0086400421410304849540861560a03003660120011100c0d9503180901810b5031041800c0300c686407440a548150901e4070900e030042e01040c0420340c030300c2d00504114800d601100d82c11340002e030f000c50100c8490860425031011074031001000d901a014480242c25074080065a80380c900303080740000d5020350310030340c034118071801c1da2080d180030380c0d2440b400317580164840710658100f02e55180c054042d60103812480d50700208981d940d2070501c811a03101310300584c00200d41400c0c000d401d019a0000c1f201354001803032a14540414050780011000c603c2e0342c0700390b0310b01c10301c010004140007003d030035035 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 578844478 1250 578843228 578843233
    0x70807020a0e010f0902041a28030204080f0303130303021b0a06020a14090109170709050a050405070b0a0804060b120d030e10060b0f090406050603241f0e04020c 71
    0x603112564180c0c003260901c203951300b14071080300000c1d913201c43d031085034107854260b0f2451941081280d41001a82d1101502c4410451707105407916250791509040381c10840560350140c3d4461524000c50716041215040c5001c5820810500c00c5480960b40303440c10580c0e041c1005038443326846201e100315440d0207450503041c0101481c0500b04200303079004010100498446580c3c9901da00d0032480b06d4095261702c1808101421428843c0000e80040010342c0d40e900001c03212955142e600c020142c54003a00d2030318055460704140b2040100901c4903001401c403039040c060418004a10007050a54060000b4100c996a45a010940d8032071000741031482c450f01c02103c0c0d0014103201300600500880c040c40c1d071a030049482d40c2041e80e0090040b502120f940f0084c03541803c1000b00f465800d68065114280c0c407558901c400500354841002561184210b060b650342484009007d42c40498036003515103104a000d04031581400d6000c0c120b42d8510f03543e501d0089000640745021400074810204010010b1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 578845728 1250 578844478 578844499
    0x6073f060806070c0506010e040503070b1902070501090506060103140a050606070609140601080c0a0306020c01180308010824070c050109020415030c05040c051902010f060e0f10030b0105040207080702 88
    0x15801c804803140341845202100c1b403681e85d0306801d2038201010346004140781c10800880020802c8400c050340c0260340044032040840d4000b160804030ba106070b800b100e0994484488505020b024040c0d9544001c081c00d003400000c0c60004201c0d808180104141c8a10369101c000c203205456078003c1c0c070901076201c48100506e03135090400400d000008640852148105c50000c140d1031004241d54074412009400a404103045070b50344001b035000a6900ca009643c2c442612001c03121700d407140201c281c02a00c4518041d410545a07505000214040d80040102e981ca9044c000c00c2c6030502991240180c500b411008010785030031409043c0428010b0362050800b0140141d640200610300308891241e80e113200c1c0d00c0d554500340170a58200504041c007094090041d140352140c1d190880e40240c010380f0000401c21781c503040c143c00b00e5a640d0411000341410000304900010800d46654000d4440444004140c9c65642c1e124150380307050080c7c6010700e401045120400c80c8071002e440c0c04079070051503021030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 578846978 1250 578845728 578845741
    0x132c07150c020907030b09190b10030c140c03090d060f11130e040506060d03110304060801050a0b131509030b0f0708070807020606010806012006073f060806 69
    0x19402a901c01c0c0c0c41140801c01040da02402032080c0301130564082d141c0901c0d41d030f41000c0c00c41101500b10a0100d51500c4038410310165454180e206000d10103910001002d8103440c00080640128068005c0300c8042000241c16030103001040e51425a401c03141002600e80515005024080000004a0403810703c004490940c4100b400391002c4814043ca22100c03a42e60201501100000d80e809459a08114089a0641807803114038440724040d05210318503403042a0b00c64595031080d480540058080c1c00140032520b4a96880b10050088001c002d080a01401102c107810700b06100e104442120303660380d10385241c0101c1c69078005640262041000d4544a920320503015000c0b9034031000900c62400180349a40100c0100c1d0142d0f000e64004c00450ba00d2400540c0c4400001e0030350340c1072044c14803000031b900303523041004600b5030640c501a01d4141019040940410000440b01c24038801c807100c2d904d00401320800326131007181c103560605020600140c206000313103084e40181025000d0072082040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 578848228 1250 578846978 578846987
    0x3021302040e040f060c05041802070f0515070207050603010b181c0f0b060121020a050909040302010b030607050c030a03050a0b1804030e0307060f080a29132c0715 72
    0x513040c02480d080c0218141c082c021a03441c45540141c0001068542160b120a1080d82c0608030641c4103299900003d8030540f10707030386807000c3c0110b00c100d05d03490365080010160b414000392000709826a600750541d41009002240e40c014071003009030407660350300003011b40e035141c80701c40c4062255840d8448800c000307801d00c800b4004c00c03044141c9000e4a6100803620f0340d4442e110700c000c103032049074800190303441d00a80d076006075020740742d00420400d0510503800160f44c0c80350214020780c4203400000b081707a600c030709040c1828001002481400810b10ed43c000d041d90120031180b441b401803400040954807040c2d000c004280c8001070036080110361001014500001c42064040c5000303840710001c40c0c202c1c1082503a2601c082c0a10000241020f02079004180107850090304480d00100101e42c41c00c5800265241c1307051180c0355811402c2c141031350107030350510403203800b00d4452040c410300403e0081c080017458845005001d400c00104101080c05001e002c0c0000805861131480c80d00c1c000000140082 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 578849478 1250 578848228 578848253
    0x2011e0e060409060608060a05060f0f1e04090b1203041e0b12340e0f09150112050112230d0c1a09060609060420031f060903021302040e04 61
    0x4022551b8a400300381e0b01d24100d10b66208940c0c00031b0030549070410510b6a4030850300030604520000c1e03c1446103c1e004140c030044a200f0005401d81c882d1a00d00d0505d2503000d580c90340615034013460241c9020340c00c1c01004021942912101d0000401400080101005a02c0507500040107040e01180c4112114841980d50f4060300740788008801003000b14000e00e102050100d510040880030092001d071480c081c50703809040b80c00003000d6007203503030702c0c00081074811000712001010401c19801c4114190f170040414150412481d01c20040c030341c142005801c80c116104c2014021860560540700e194500b01c00b210000740502c8150788500004d540054841440c0035022500a414020b0941c51601d8a802452140c5a014001c01c160307100d400520840c3c940c00740509401c25210340f0243c0c02203030001c8a245480c0782070a00c0796030303900d0401e120b0090100799014030034036041a0802048029400490881929012031341072a80c5590340e41e00c4002403040f9403000d40703100140d500300018030071741080a8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 578850728 1250 578849478 578849489
    0x3030405010207050d080708012303100605090c25050f070f291606111804051806041106070c030f020a0b0307022a042906030402011e0e06040906 64
    0x200c401014000b02030f2606d071800c40d104000664039100401201d03000703507120492a4a0f44404c1a0040c0082000ca800c201c0003a91080c8120b8542c0303010071041c1801400b11b5030212402034081c3c24090000b41d0300c04200241e5480645800c040440c41050000c1131110784100c030102d40440350156030b62481150b0b040610b210b4400075a042c04101c800012180109198840c00100294904038281000d5803613240800010b0310050382e2501807950f11b941d04401452181400100c0b000c2c5c00d00d505042000b41d50000700003041c1007042d0710325a450404c000403c1c581250707120240303c074a0803001020400e18011940050100f1001c08130000a000d01e414079111010f0007940d0480d02951504281401413209507101d07401039014240c280c0b0b80d845910710711490100a41440c09c000311001d00060151040c3c03441c0f40290030141d204071604a41503e8449008038025100709080d403402c3d40010b482d0920300424501c030410b90070640048603200d42504023022200500315030f104e5480c6d0000c4c000074205070086 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 578851978 1250 578850728 578850733
    0x12040f060e011e09050f0106080c041a010e010c061b080603190308070c02012c0a08010e03030703021c0f02090102010f05010b030c07050316050a02100e181003050303040501020705 79
    0xe9101c0410302403080001d00d042030385840111440f40a400501403080152164011031519100d00758081c0a144008e14115008258201440b0704010072110000e8440906842050340d108169800490890019100342400010350030281400d00180010002102640a20506001000ba08000e03028040c680c260308071a0341c01010380300f1084030200000082c0c00700f40e41800050b80c192181e0841c4504a00c11b1404110700c1e443c66844806059105a00c00210004000852030301d040100012000f050380500070f0000b000c03200b03288d94481c480034100d20201500082d001100c88a1159152040360f100c62041000c04200c810000003500300140d040d005501344041c26011030054003a040c141d8010268186c0380d5203c2d40c0c035840980d07100f004101c826010501c40c261541c10304281e1105880d029001800d26a0701901c10441c4240c8101410820300589612044190b01e5610701c08001d07168150303064034141c031141c804103099165a400105944070000410007007007019000360070780c00e00c11000c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 578853228 1250 578851978 578851991
    0x3070512270306060405060d060204080715051801050702041407090e160504051c050d020304080111030112020f011b1a010603020309100207030e06030708040b0601110703030806030312040f06 84
    0x1003036030004180340741140d142e0b0060f00802c0c0186002e900198000500034526501000c0665444003070382c0041d80a100241c00c54481045100c5440e07100c003170760403000c0c6442c41c5061000d048040c02c0400f2004071b281005000f01d2800c0454846038841c1e00402c100d0a0001550b01e0301c92401003040f282070055200100c204000300307001c1074007040c4075280200705449260401d03050000b40003030f4820045180012078686000e10b004580b0921100c3e40401c0594065603481d828544004d0130340b850200030325101002000100a1040300b0030301e503020240c0c125444000850840e0040300c000c0e030040d040080c80030218618804002022605481d4132070f2503084004940e17079821080c0e08a000032510391855400c40c1d41203602000c0380d0750003890994030070b0070904211003400d8089400740d00304460040102d040102031105005403a81c9482d0b00107001d103801c036400180c0e100c0094440d5480d10008013807044040129017640d506006580307100302200409603161600e400c1140d1843c49a002c2600d0040c81c1c0392 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 578854478 1250 578853228 578853277
    0x5091e01020405010e06030a11130e06030a0c03031107030501020307050d06050a03050a290117010e07080309010c03020f060403030b12030703090302220903030e0f1c080903070512 79
    0x942c1e04841c016110540000303414800c0c01042d43c402001b071054240d03101b105503100055500a071800705211070450520790300f00840c00f82c40040280465109601602c0000c000842c0b605071072060304d50520302800c1d1031080c8541c442c81e120558200030a030f540040704202ea44e5511402034240c40c045118244641c0351b0302c600748004600b0501000c2c11540003407101c4408591510442001c0500a00440d50510611151803102080c2030700107003604401060b5420354000309028018000340448040d09406103001c040d141d880c41003400d040c1c14041400c0c414000d1600a004044010400d141070741c1e020301d411f1074014002c18940e8801c901c1b4010740325078203e4180f0000240d840c095813548075800140c5c119001c100c0d01248071b8a50082d80302907003520360422101c81c000c07130410038802d407400700741ca00c030400d200c90a103108084070030320359884000d11418250030015807200d0025035051030005c0d610761060190541c810044064a00c1c81120744e034408109041c0000d042122412100140302251034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 578855728 1250 578854478 578854481
    0x100c03110717120f0d020702130501060e1201150302130b1909111306051c0c0c0b15210c060f070b0c18190504090c031e020102070905041505091e01 65
    0x2400e014214000030301c85e4440f501c44ca0f03801000038900080440300b081040e00584000d0398030980005e40081d00e80102c0b0300013070070401224094104d00c000240244040881e4050b40b054441c0320103842410080d142407103280013a4422490b000b0080d0612190a20003800c0c110540320034402d100f0312629050f01c4050420a6000b510418008205000116841d01404640079006007100c69021800d00100d6001489180700710144000c0e940c8a041402c0120309069110041c01001166081e4808a810215aa600099500602c140070014014801052120303240003902501c0c0c03a0840000540801da82d0b100c00060071a5a10a1020711481d41d6481380c0522903028040820320b090368041aa13403514500076404403200078822007902405640c45001a0951b6107910b400d84080041308010f00901984100d40101c180341e08503010648801c0b980001d549450320b20800c41065900c0300418204241c02c4404001004807140c02d000700d08000440c20f0b00d980b883c9e0134481000751000d00003844498103 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 578856978 1250 578855728 578855737
    0x206160206280f050910060e09030f030901060305060123010c030503040807111306080624120c0d11180c0d0c0207080708011514100c0311071712 64
    0x3a00c0c55030048826000340341500034a071042c244282e41c2c41c2d0400914280952054510035210a0028040c900480c5110380031220710360005104074180e8810440741c1c03400007080701e10708424400d4040d520742c0c03095071050040c211034000030824028071000107084413280f490800019074204450040703820b8400150380c0340300c03094001800301d402480000c000c1900e56000d804070354000d5044d688801103c10000d43e00510b040c825100702c5541d030300300740301e10f500400c403041d881591400800030401d905050b9100e04007401c000b41d80f18440e54921869040001d1141501c1181c3c060200b150420440c0f419803d201c480e854841c0c01149118001810200c0071200305008180314800705282c051900c281c18082c0689201905c10352294032000510f41104020000007030034024000601c0c81180d2148000c19074883d884010135034078200014255070b840340340100c0c100728207042400c83c0c17403160310341522911a00c90010403a0300806d100081d15120014002c007108001c03009841100f0020b02c512034440c050f = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 578858228 1250 578856978 578856991
    0x1020a081806190b101e0201060503100e0a080301030c03120305151201111b070b03010308041809080309151b0313022e14160f021c030206160206 64
    0x40540403503840d02150100c8240045410408149004c40d280440d441605039282000040c600c07803401c1800d08028540380703080401c944004d0207624a0103000940d201441c100140311166505e40c80301c421081000300703500031b552003040d00343c60350b940b82018070915520340f03c00d4442e03800c2c05132000e0f0b42030b120b4031840d44038480c0c91450380c0150034035005129400c1840941034403150b50b40c002e05150241040054041010304840d8a0f915580c40e0700c004d07007019075a92140740061030030300c014070000b8039001c03c0c0e800307584126503801011041030000b4009001c1e0703407034040c040300400814051031580c0807c0b800071020049a00c10320b249c40350100e6801c00d034403800850b01301c61824004502a100002402c0c0007050000b4050410115981c8602c5030b886000e480341080c44040144101c0501d4200701000341000c2c08628503403c3c030f110018050541800500002c04103a480900e0b50211340e075030180c40e4801420600301002c01580c03454065524501030720320500c0c91000c800041d011610014100d031140c0b0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 578859478 1250 578858228 578858233
    0x140105101805030304180e0d02030a03020c0106051c030906140d0506040204080d0507110303030f0a18080c0c03060109022104060209061602090604110306010f0c0507030501020a0818 80
    0x5821541200e440c500d44080641c4000c011800003001d983c00c02c05000600240440580003806001c078503004c41c0c8240b0848030711908104840b80c02c0c40c1d00070003a40e20000305410b015903900100c58046004103000d401056010f503120461540b16183e1a041010701d44c800c1c0c540c055541e484500c00d54100200c0c024100b41003c0400010510f4081504601d070025405040941815120380a035410110849407800000340301290b070500b1722248502c1d01002440540256246090525560507074a000a04e4081e2040d15504480c40702c80200e03100105054020404a8072041c1107198161201803111000380301303200f80800410040303200d10845004501c1d42c80ca909002c40c450f103111042c20300040003580c6895085c4408051a101c4030000e000038800f10011a000700200c0c410000403400240c84075000e1894450380c000300e10003000844c0c2c0c1086c0242041c502e00903500500300c0b010360004c000140140250039002013004015005014807555a4446155540d0b42081c00e910046201c2c09888007503 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 578860728 1250 578859478 578859499
    0x8061e0a2a030c2c190b0c1b130903180b031f080a110a0b130614090108181e0708010506100504030620130303020d02030705120d0e070b040801140105 66
    0x2240c8070810804c92110103080c0040301140c21150040c001c01d2580009540040020074098004c000c2c4210006055a00c3c040c14646881b103001c500ba0200054602121690f903d040c803050501582c840c944035500b440f1290720594850b80209100c3d0401d03515035a00c07217402d4828400c20403154004900741c41c64a002807403a00581d407944140003200c086440c1c0c1010350340c000414407005010045c200d0285020003508120301e0400300420300d0442003485a000181885010096039000240c0c41d000400da042e00580407600388409810400070700d125149170231074502c0014002c5e40200d4001c08942c10b10700200560350b101814014038082e60030580d8000f503020001800010101c2d8040c00c0c03115072485860400c90700c0350112a44550003001c4140c25414030000c2041010b0381000b0483e445180c43c4007650400c0040c0e521345603113020031a0310128009001c91050441403a992148540181200440b422955503011126a65009001e140b445500300f48034100800c0961507114100d601c00340c07052252 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 578861978 1250 578860728 578860787
    0xf0a02120a03020c15040f080109021906210b1002010e120408030d02030901020f1204350f0702090103031d0d080318070504020d1508061e0a2a030c 65
    0x1500901d17540c01c10003240a00c00410350103070351080340c800b42c4880400014450000e0041000a800800c80d020001d200100144009a4001d0401544502c5000f000710104005e07080d06c0b01030400030700c01641048207140c4500c8050fa0540105c03d40041039400d40d482c00c40d000c0c485509d00c0c071907800b074011641d00c100055080702d0400e60007550b0000303003140010305005c10a06c1010207540701c442d10620001e01c1209010901075440c190354268003109400c00314960f0f00051f4181c941c800b40707201500d500070204400b415262400111040c1903802045070307100d0f686a1402806003c0c00f100c06c6560701d003c000c1d8100d401e080c04c00a606030240c2040c1e04a0071642e40c1700300c0c1c080032405a108180e581c040c4d164009183e031150b0024001030f8515400c04103100000010315080001160b03c0b061040d48001c0a001286002d8101da000403640c40c80802e65550b02d83d80c0103000703800074580001419810250140043c0c3d07481815030300c108183e42e818001c0803020942100d40d003500701a51041401c11928074440c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 578863228 1250 578861978 578861989
    0x301090512031f06050c010515011b0203070f08150108030304080306040b0f04060f15020a110904031e020c040b0603060330041403070e16031802030f0a02120a03020c 73
    0x3880000c200300f02c0e078040c08442c480d1545000c20b030304c2800880c1000c07480c00c00b090001c1c052141d000540329480d034199102000001c6c40203100170360032a14160100510700554400f0b000d1700002d407244180f41807125940f455420354078000701c08000081d501e440000300e114903010003140d000d640c10104090540e03c860041200404083c4400e561200300450b101040d91074034050800207158820010410f1441e000001c0d00222058400c081150054000b110010f1103d0190101c08401560070004950b070300c1c40c05035490483d014a00d443d40e1003052540d00e07055400201b0280e0400203a4007806241c03510301c207000a6000030764405034590040c074869610f00f00444810f40c840e003804038141107c40030350380481c502c90384aa000720000e00424800c00038279003030420a034802015100e54035140c91610041c402d10303a0086644000425488904c0741364150080c04c2100071843e00103040e62030400207100e4040e51303000305402c01c0303002e82c07040c000c0d0480340c0350041460480c907609500503200e0303070344c0c000e08100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 578864478 1250 578863228 578863231
    0x1503071409010e030d02010f060b1615090c03060b04060b070206030a0e1c022506050a0e030c09010b0a08010e19020f0408060f01090501090b0109060c0302330105030109051203 77
    0xd04000140031040f281e503404010b105880301e0681c00015400460700340c0102030300d00704d0b0041e101c1580104500032881c0b00c0121800080da8200c00320191580e0941040c40142031f008030003800e80000710070007000f40800b56200b80070700b55044500700103550b03458500e1803541c002c00c01c005e50710403018400141072502030b400038800d060011701a10300884192600300c00d1600402c20000044c0e210403000c02400341c60100000305244265100106a4648480100780b8030030214230700c0400c00c88603003000c40c0da202000f0001618000030100c021960315809a04480c0e0014451080000c8588000050442504030181c1c002d100c01641140e9140680014038003940c0702c81410724042c0410040050102003d111980c00b9a0002c0c02c154101e500d480304070800e075041a080180c1c400d00e005010002a03030860842422100203082c0040143c800e030030107131306040c0f5803002c1078444007154080c4074510050028640c10b60444070001c040383d907210020f240c2210701002000789950b101500c2c01540580c201c0185 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 578865728 1250 578864478 578864497
    0xc14010201091502040306051b041a04030210080a05130203071a07060c0503070f050c060f06120105091e1606030902030a0f0803101d040303110d020408030915030714 73
    0x72030400001c0d5a80f000c04850f4000c1c0880c0319074082803e00c10041280241500440390002890303d12a00104801151245200e5498007801404105040031303e84030540c0c0046400801d0543d9180c42e00502920074541116240007031441e050010394030301c045051341a100c980190040010710306105200303100c04070b0483c5d00705176102c2c10300406001030114012026103890a580725a00d81c1440381c0c01901c546005030400d000d0000c14800050241c400185050748540401c00d441b0031600d40c0030101c0e1205006191403412542860100a40000300255a511070040c01c2c0502d0b41000e606085180c690440c052800111070070810200100d44c820b4015101d05030000b01030701e1035042c542c0e8a1449144d40e18404035040080441040340032000c0d07488040042131b800d44480d5a0704610b18520418010003400102450741d0742c00e1004a40341c0b0302c82914107045080204541c0c0340c2c0c688010b59503d420110b0f884d48580341c480c041c401c095120400f03a0b80900801d0300c0d00c0380c441042c0071610001e9004103421 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 578866978 1250 578865728 578865731
    0x31006120b03030c0307030e150d020904020c030a030b2809240807060825030c0207080a0819140f0d150b0310081b0105030624041707030c14010201 65
    0x41ca0980e8083c8018141203214100a640e5101c241c90094040102505400d1280501c810f600480640e01c0301180c2040900d0b1000503034070880d00c40020020b0041d000d010341b82d0300c07011601c5504103415600c07050b4003ca0486100811543e40c0e61540c10700c500140b0460a0b60754481b1041002210300d41041601280029140c0c040e000c400c4d0311b402c0311123070740e034454131191b80000c40801c4841c0c1c02038626600100601c00f00c61804a40d0b0301401000d003200b81c10542015501c051020a035482032003904041c0c4800f00c00e944490039941840751041d0003180010b424201c0f0031080380080ca0041000048000446480758103100f01c2180c00c011035085610401c80d81c0b81c6940c01c4504084050b0007110280600c0000c96403030f130800605504500c0219082000c1c0d652000300340c40b00901030340034823086100003440c1041c0e8956540e80070840ca8528145480c030030014800023440ca000902010b0825121400106901c1c2e09500007425a55141d41c40081c09088040f10140500300c81c0340451404948103000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 578868228 1250 578866978 578866991
    0x15381f1110090309170304030b010618030b0c070201020111070302071a0d0c05042102011b0606050306040f1b03030e0d0809130c1209020a050d02131103070e030303100612 75
    0x4107400361030030b41d00100c000030703600d04060080810300381c5c00880c824903540085041504669650741e00300700c1030081c64288066100e020302e140040c1e02c8054091580015103640c81d040c60103445203560413180c8101d001d5400c1505500c82c804a9500762044941c050703004207101e40c40c08492003450a01c1000400a50104100c049090307400d034041c000c0a54480c1c0d540700c0c1d03030320720b01039526003440202c42e128040f460b442d00c0306e0b20250b0703800a2506c400803585003402e2550304841c50814004d0610341c1c000ca03054040e000402c014004159864002e5a02440800f07c411010801a84294146000040c042854841080301605110002c40000d40c4245050740c50300c0c91050016095010414034030700400e888004801b40c0685c4184040c0f8903c045c0701c2e09004100702c950004612400da801224000c5100b100c10605640c3d403240c0728241103d203030303004100700000c3d0100b08115501c01c54507540800d48580c0010042c0c203001044034403400c45c6140e480d83c0303541460001c0b200000340c022450600c0d0748884 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 578869478 1250 578868228 578868253
    0x6011a071205210106021e0d210204090f06090b0d05030d020318061501110c03060c2805070209060a0e071817150105040903090315381f11 61
    0x1c943c034003a00090700140014200c0003516003504804210814042d000551a007a409401c85460407802d581d4042c410108a140c030f107000300030f00950744000100350810b404032859503881d60012040c5ca03030040c803d200240801c03044c0103140107031690040240d0300070800840811944d82c05142c00900407602b254104180324900d902d400c00a41e2008050120008071000130b607000344110b041440300c04068808014404002615814001d20303100d0030400005031400310940740507019103040104028807020b4600030100034401d4202d0681280100340c0302004c602c0c90314007030b101c0000f156018846000701c1e58941c0c008443d100a4141c001c2d010b1a10b846000c284004001c012002082551009107819040040030484050040e802940518607184c0c1c00d1000c244e01c00703060000c0d00e030000c50700d40c403034598650400004c01002d4400076003034488149841088812250015001c03a8040300c50841a01220401540404034904000b46c5050f04418101c15805000380201005210040d240c2080c40c12 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 578870728 1250 578869478 578869537
    0x50702150c1015080c09060d061b09050d0f15140114040501050901120f14240f07050306041104150309050607051e0904020d090506011a071205 63
    0x2100800c295401c040b05150304000c19201e1040714030481010038098514243c00749840c0c42c07107900058000e004400006245840d580c1c102d0440c0b0758401c0f410007500f40c06020344101c0a0b040b0100b40009980700c440084c06103402141a02066000394028000c1d0001c0c0c1e0b100d04a81603065074a440668a45103d444003c0802450324000c24042d804203074196003e01c1008222075050304020b1140003004014007c030018180e07100e1041c0e90001012148486d20b0800c400708074440320440d00c0c1840390540144803950150a0091070004000c03d81505031181d8003955400c4904951010026100b032000811518058200c0100545140300da82d180c2a16602110b0780d0341c1072503651502180d2543c0150081000401000f50300c02c1a529103641800303080503111500700c0325048107a0a1190108243c0c900f0b42c0d442d03046030002c440c890004c0003164442d161150311074500b4031828001c130184420046146101e03400b228545036100c0380c40c8288222144099480350048500d003021414038001100d030300b5004 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 578871978 1250 578870728 578870737
    0x11060f01090c0e0d080d0f050112030e0a0807080705010314090d0e0d021e0a08120d020304020f030f060412030b010e042f07050d0e010509150d11090f06090a0605070215 74
    0x40c106141d44c1b080440501070a94543d400a8541e50b80307000d0040020b0003032145000700b1030398180341000c800860440000d6183d04543c0000909024400c0300090418001818200f10b80003a01e00340100004101d82c80c29501c4100d0340c20f00700d0b07045001c107400c846102e5681e4030704c0c80200410748a00b90010b42c0215460180c0855085018070a180c05102e0070303d8040f46550041c103c2c3d00041141118284c0281d02c3c0303000700c0c188221040d4001c00410210341c3d805418155188020f07046450303c40d900104540c0d1400306840986a00380f1114161000c42d1083c02011010390301a140d041c140041001444018a2481ca0310031001048030081200092405000c40c0880b0180178010744038119800c20604105160050400384480400ca008440e6008020766042003000c541c134000008a0a8a01c43d2030b105440e8401400c5d8a41000f009480c0c030018017801d413407042507841417045603900080c4900b520601d91b105601c03108144040110601c60402068030300d02c00b50144800045050030007855400 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 578873228 1250 578871978 578871983
    0x3091503090507050306010f0e1b0304030c030e0f0a0302010c05010e2428050405210c1908040e13080a031b090e0615130e0711060f01090c0e0d 63
    0x1107411110007400070800a40d00504000c0f1701800d940e51400382041d003540114414034007088454000110200c005107803214415a0700300c407103682c9107840d2500505100c900c1000720302141c9003800d0f8642c2814607404466545201900c041e0180e800e5400644002c4202041101c866480d100f8814078000b00384004440c03101803011107001d071190325650018242d4000d0020740800d90b082d42d07000000704c0312081100d5032501a00001059143e9080250070514080070740c0e01007003c404c829100d094100750041000d440440192205440804180251484001d44c06800e02009000074000707125070030103203a040100c410306030b418000d85a86001a0381c00034445000400d598807411a11100082405c02000b00c8515280720002e050600395036140344040d102c07034040c030200e0781d18104030041c8504540903001c2030308080c02030030b0b40d448441503295805c55401000507520703a94075000a2000032024061010006030a10682c203282144009107800e40d005000c000d031283c030305503403500c92107000c209450 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 578874478 1250 578873228 578873231
    0xb03010f0905030a0f020606030303040212010209090c0409060f0b090418050d032903101a060714010b010f020304030b0c070b040b1512030403021903081801080606070f0f03091503 79
    0x401c001c00250103d005d40302c030541507400131400c1200b1681c02000310303944035a040f124000744501d0840030301e009001d00c0d02c4442c0c01c190030340309210741c7d00301100140084842e244401c4c07200c203448540189204030a4800e00d01c003060203012031700303a504c0c01c4d03000708401c0910071a80300c0300910140c81e40791902c0d101c062900080303a42c984010070014011915550081541c03111511070100c2e40c004aa0b03120b65020b00810303c3c580d20b24030740d64110711200c129184858020300131a02c40050f4107001c03c0105c00e4000034201903203410040c5020b54002c40300484010410f4000d981001e02e036031124030000f0340080021503d000104107a00011340c0104182e4002c074002c02001429241c82d007494004200d40d0403006115040c060099604000008100c50540754151a000e000801900e03852030b00b21200c0e08000d1400d500840c0e000180e0214180d681d90307040090760781c1c13426030315510b0901c1024410518090042d40160ba280404203141d001401041c40c40703441d0403010555104a038030b81c4900041e000700c000a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 578875728 1250 578874478 578874487
    0xc1203041a0f0702031614070f050306102102040623090714040b090d0c0e070207060801030b0406051b0a111608032d16060f05010303120b03010f090503 67
    0x18100003900607804903842d286164a410201e0010351399004e0800b4002d58081a40811802c10070442182ea0001ca50101200c603141c0c1c0b11070f155454200640501e07406846030358002110207290210b08005c464000a01c0204082ea8411030040150541e078241d03002a1a0b0b54005034411850a0707100481d4400c5918074080181c3c0d00410088079000781980c2e04010240900d200e0a0f81b4030001c8400720740c061412266180c160501003104103904d0007025140168803d00080c1d038111281d01648111029801d0390013694450806803040341e400c1c003000d401c90800c0400100040d07620ba101540100c0c00420070002e0390385480c1410360b43d074040d180300000101c0c15125541001800c104040351004100300c1d002c400e9080000182d82d03030051080c2c25220813441c0c3c800080303c0354140c40075044944540c10882c0da68502c10740703030b107921062464200c580e20310301801e4803001c020310f1095074141c0354165680e0200e10750f100301342c201900403060300d640d15568504e00c809110281b0b1041c01d0155200d48081c42d241c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 578876978 1250 578875728 578875763
    0x90c06030501032f01050d06050315091e0c0f01051b030a0207081504020405071e020d0905030a0f020915180105040507050c06012106020d06031407050d02060c120304 73
    0x505221420a00904c0d02c04881c2c21020100c1a41400042001e1800301e440c0c1007407000c1c10703002d0021a40900e0b0103009425049079140c1503000b40034841d800c000100c512124000c54076418a2141035144a00d50704290710000c1c030303890501061490158145070081c2171892107a542800f031600c8148071201503100080c2100c040340c0601804005002610191091b518040307442e510340040100000c0c0300301d6417180082d6505014600e103013030400300070182c60844107140d07001a50303e80c0e41c0b500410224110703d20001e01c034500000c007040f51991000301948401d8043c1e080c0030046001030043c0c000d0800c0f528118585458612140300c0700c1d10301e10b903115000d524000a0200700d40c00075000004101003000140e081c40d800207410742c115025004c010198124a88140c40740440001000300010700000360501c1c03a10558108009490140d01c090010340081a034566a402052103500e40000d18648603401515140300038280d21440042551b00c03c511407520808540c0c0100c404072010030304150a07612 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 578878228 1250 578876978 578876993
    0xe040822030c09060b030a05130b151906050711010e040c02030315090c03010612140f04020a0509090c09060402040b4009051302091008150606030403050d090c0603050103 75
    0xf0000c90f1010000030381001c003048103d1100402e1111a0fa8a4101081d91415010f4040720304a0b040303107000006003001c910745925400d1502c1070314824074145e035041c149060881a46822140552239032340c45c09d01c280c5e6a415890b03800c0ca409031305000545a01c0922903c40d03004e040d99210a0342c0c00746640c1d150000410400303035008401ea0340a40041d00810140703040d00001c4a0659900d802c000d0b031414100c10700400a446c1010b2103008142403402404003481e014011103029a01c221840b4070740070b8480c0d003070041824048410070700541c00000c0c600d0716801c102e08403642024016002515050316190105110340c01454485203d0b16008010796800729141102d900703001c20195400503858021080c41c2c0c0c030041a02441a0480c0d03680081000f0f201e01d01e0f4040b01d0715501801495192820b000421960030041c8074444e1240140792003e903002c0008450f581c82404002e0000e41191a103032011100c0f0b800c0480c04002c000c4c2d4500000e004144000504c00c000c0c00180e50208041d0305500e04502d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 578879478 1250 578878228 578878253
    0x60b040f030629120a060207060b012c011103070506090337050901180603022703071e090e1e0c010822060203011503060518010e04082203 61
    0x79200708680e00011005503006140c07080890003112036911000080c0710a034240481024011b00326480041c540e000c0201c1500240304c1420241c80f140401e10140c0c0100952035a0785503228009141c00503800d00c0c0358003030113440c0700c1001e02c02c04880c1000710980e00d4900d030903426203d4240707540c4003041c02580d4004070000425025182410040c1001d4003210605c0c400603d64114001e2150102c0c884025074820307403c000380030408084141c1210f5032064003400940c884075a4814001108040805113001040c2d0710000c0d040240082c00d46520307210280c44c2100d40f6038418680b01da86038000140c0300c1224041c0c0292403407070a01414104403622100d003100040c0fa50502d6036034100000c01c010580e080300b0344590080c48000c07107155000c0c1d00c946802003808952001042030f48048004601e62629004041b43e0b08160b841c100f188540700c104200060f0443d00a110b01000040010b10420741c0d1000815001841503600c10f0504101200100c0440039980c035646010142c4041007091180280c400c2 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 578880728 1250 578879478 578879501
    0x31a0609130b01060e01030e01020a090503100b0310020c0c030d0e0316060e040f0e0d0534030507030509041b030f0c091a16030801080d030b0904020d06060b040f0306 73
    0x110590702039a544821000d014440c59090207242c0a154003207034000d0700311800b0805482c000715610340e01c00c0c2010703041035000e001e002d010b40b160701040444152103108004035200d005008154003400720f405039029512800816055001e0062000038503241048807240c3c03960581c44844000382c1070404d141c80d1142500c19041c0f044140b0078200a40398000b20084800402a275000c501a890f640134503000c2e040b1860301c02c0080c422b000500d80059440005088038190f80c010002150460460030b0460b01c0d903035019100c80200751b80c104070000340100001c2400a101c2d04011b4100950540003030100c40e01165994801f40c0300c026082c103019810320403d42030405600c2e04010300b40161600a0540d9036030f0117003a0031134480c40d62800c02641c0340c009560079480c2404070b460049401d460010301120082c82014880d03c1041210f0202c54001e014422b00100058841103031b81c0d03555006c1101d1407041140581d01c06585800c00b140e6000c451000f000901108440e44c1e829074698500802142d1044501c0c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 578881978 1250 578880728 578880751
    0x2040b040f05180d0c0b0a091a01081501080304080c01052101410f03030f0d06170a1a04020d0b0421020c060703050a050f0408070317121807031a0609 66
    0x10030000d107146c0d130703031a4110000308800280901e541c81c0a0300d6212120714104000000d50b000068a140c000408005000031650220340030f981e5201ca56a0300d000e0f034080e100b100d40019984e08a00c5d44540003420700c040700160b1011649011030100b200d144000e030007480340d0514803440b074200000172500c203540030364400024190003880021051100a02241700b04e21400e8050441e0300e1540e4100706a4241804980081c0c0e0740c1c5a11103518402040076209001205000f2400c0c55002c1d00046401800c140d044a6104141c510000031080282c00c01131003284d10640c180f0706500032944014415120b54441d400850001d480400010700c0c02c1a0f0341005011580032055110583c1c80304002c1d03540050341804e00e543c91b11146401030f0f449000382003201c0e0130000c01080014038202c00048210461307024004c00d1108000000d44180070b440f41e4405e140c256203032000810700c2e2001c00c06243c02804090b10640e40d1180c2c030ba40c0d90b01000c0c4c05095518000c003c0340000d0160381d1508418694110b041c4941 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 578883228 1250 578881978 578881997
    0x131401060e0d0c140d14060601080c070b07030510080604030c0209060a080a020609031903020a061d0a110105130b0d0608060106140a0905150a02070801050903040302040b040f05180d 80
    0x44900c0ca02445029418501c40c20004030007041c5c541c0c000640c151980039071046000811442016034404c4111050b500207101030022400d407168200490b480710b030708007045400583d5001000c2d0081d00e0060a0ac241403942003400107079560b42801210b01541c40395136103c1940c1000d004201801e8000385c400303881801982c800304400a4002125401c2a6041e1145502e40490000180c140200385070410b088c910580c54400416134081091050548542003c0008111005006074121285142006240e12114880300442c083c80b01080d000b0205140c000d240889074003584110303000c190b00c07001d55224046030241c4501040e00030040904101001486291b140040080540c0e40c1070580d8070a900001800e017649504c01d840c8000988400307044412445a4080c00c0000d55100e580319400600460201286042c418020070f4003d1407460021170600d403c6800308001040786012071a806a0307203610155508580b4001c440c4101b000011000c0394105d4030741c80c1400d11061610040070810400f0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 578884478 1250 578883228 578883233
    0x16080a080a021606050c040b070c06020d031505240a121d0d050708090a060f030b1f031109030f030403150c17041e050d140408060a0b131401060e0d 65
    0x100d10115442d004130010846440300c240b090481c0c8140d8205101c504c0c00010761030140002619282d044034101d0b800c40b0340303461002004604a8540880d0203102d00b008140030043e0340f07030951011440e007131003400c160890222215882161350114040b08041408601d00c01d076407136900d2040300038500951404c0c40f0001001c0c0c2c140c640b210b4100302602c060007004611541070100410540f610001c0c06408580b5507921645d01030113a580d60000400000d0902c0714000d191b0070b01404071002400050440d01030307002207000c140c0c0a8060b441c40556101c00500c441191658104400b02911a41038091690b076400d50900ca00302d5482e01c0411a0b00d03e040074801d405095212040344600b11404400380c03030580702c41ca01012034840c0307050807403207400c4c4016059040c020041010282580d258850744a0981483c10107001c5000304c0c861041650402800180c104405800040800c0d800500c41d0072410014500001102c108480c0d20400506800c010300260340c008400b9500301e14200c52440d440c0d0708a0307 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 578885728 1250 578884478 578884507
    0x905090c06030c1b063903090a0f14010e03030c0f0a091e090b01090303053009010f06270e010b041806050106050f030406090816080a080a02 62
    0x20548500078100040040c062030792410548040000210a445018000102165a40720255903114264100406003070711a031443e01c00381407111b60f54002110841c018541119580c00062154005004d807070403800005200b40410920107100d03001c01c4100002c0ca5080d103085906807141207600c1c1c1c1c0b041041c00b000c4034200081d81c02041d071446c42603a0f0340080340b004035030901c65503211255922510f84085071704030800e075a0009844090a0800fc0041c0d40c0c0011108512548009800f080041200d014001031400000c000c4424a000b001d00e0607420102c0744000070800c588100c0603035500c0403c520417032a140110401440c540382500c0c1c041c10080001169408d1442d004850940d07508140706083d4801e42200305050001881044041031181882c940f2000441e8100c440d10b140c440007041180c019002d4070304610303481e141103081d035643d5600d940007050780f06c005496818050113811849110f4040982d60706200d243c045440d4400382034043e00702540504640401c40c014840c0e4012403045 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 578886978 1250 578885728 578885743
    0x1b0305010e010308070f0c06030b011e090b071a160809010c050a03051e01090902011701060c150b0310090515040506070f140d02090901141507051c0216090509 70
    0x3010313640c1c4c5240c5440c00401d25040c80a0080c104480c086000a90715010303030010035442d8007030b00e9452101c02515210000440845d1031000400d510240510505040a0240014603c2845114030117040c000d103410754500200c030b2004906200748115040e031503204201c0c0ba044441c460007404200301c05d00000d46140681c07100c040c10107660b030000420410740c40d051100311251251700054156100c00040c0082d0502c0d840580c0402c070750200807030502c1c5940a01e1030486000343c2d100c24544034a80c1c1c91a0300c1d04007007129001c81d02c0e1903030440411590140a04854485424000915440140360440c2040702d2810284d084d00e070860104408503201051306544500b40740b421120343c0600c140e0940340e0b90300150440108500c0455120000b00484c2c2c000c01d410351040740d800040d81c2e41c0791305c00f200c00e81c0c88454041c4c1010b220390b03810010b0f00c01d810140584601c85d0f070070341d103250740700080d6984000546145000140d10445043c801c1a00e185091809401520001e01140c0742c0300c05403950703544a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 578888228 1250 578886978 578886983
    0x518030c0c1c06052d010b03040336090516020a1211100501030311033a092d0308150d050604060b01030b0a180c09090c02011b0305010e0103 62
    0x50446400150740b1460300c01c10780a591101c0d00b0001810425880c02501000d101c42c0c861041c000e0580340c45482c0103a40040c101c4000c1c007025407039035035195400c44100303e00010000c0503c1c0b100a001ca82c08116810a4500aa8980c0307207084e0546024403020540c0d41c050007603241d040035140034942d0964007044012103607802c03000041215000d598200d8044045207031424060080c01c00209443c030381c640045048074001d90b40d05a003d801181103030345910a5004150311350340d260100081c02c8441503030b00c8865981c0803c550350880c0c10081c040094807041e41007252483d40764003440d00080c0d540c04183c079150305401d07900303110303140c0e15038010b0450f1001070601c0c60300d8000c04200c4045a504c4584d41d00d0400e52050569007581400d141480241a00500007070209040c00c0c0c1840042c00d00303d4851044070060110342d410384001e21841c2e00140f80b00102c10080207044100800d0000c0345004808100015a000040309941c0481c0d0840070030240c0c0e400401c050034800100320300c02440f600a415a81c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 578889478 1250 578888228 578888239
    0x6030605031509070b0a020c040c1b150605040504060e0d180506070c0b0f030114010509060a180503120706050a0902060f0f070618050f0d080a2d0518030c0c 69
    0x101c98183e564542059944080044e00c40020382000702c41d0301107a005010602030340e0501681c000064151204901504449110031510015502092003510a16113050702c8c0c10300014104d0711100450140c1c1c41c2103030256a2203031110003424422404010b00d007180c4030300d881d002100e000c0000300803103c0340c03c2c1d20805200f51800b0403010207020103222000d00801040070300c559155507510050007990001d1207001500d041755007040a595024500311048014018200c41c90502e49038800c2e5100e210074820207200700c0d0701c80c07000f1400d81c03070403c0602124080003000c103440303070154900b00003510340c010240d4440b42d0411404070010f072240816a0380c580c00890049491741ca80310001100f034002d140e0060555410101d00d026650f4004603c460200c0c001c400b0b49024a04d201d000c2d583e00d1181c3c0f042c5800080d8207600040c902e040c240d00090b21034001c0c28140c0010440ca03446400e00d00d5092003240e40d02d42d500e809200c0141400000b681c80d6660746005503081000d0130424946581c034086101d4002c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 578890728 1250 578889478 578889481
    0x10509030c0a06031e0e100504050f07030302031b0309030a020103090f0c030c060818100c021e060f0105011b0807060605090a0b1c0b0402060d090b090115060306050315 74
    0x1980c040c4016610454040c2244002941d1200014041c000340c21042c4400c400700d0000080300444ca00a0510000f43e00303000786000d9840c01940303401803400510540307060060200c1c11040398401d002c09001035019a0007580c48400e070b26020501c8816048041b00c0c0c6501c100900000c90701d000c5180300616409080c005140013190820300c4001d42071420080c0f0400c4505070100400c480c45c41b0140640e402c7d96140405540d560502481c60b50b08100d00070206d40c006a003420f000520341d00a00301180712881030711021400c00c0300c502c0740710001d100180099001103041000f482004417040b8014582480c2c00c001f0f0800b00b80c01d40da04070322034240140c000040012a0030a21040790094030003000040d000c1202c0340303490a042c070000c09544000510801003c0c403090480410145544952601b000707a00c00304da01c56500708452a0301c48070070440c45607100d524550100b800d540d1818440c04140c2e0000c164400c404001c160b05899580001c8285441c240090103182c800180c049080568010280103d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 578891978 1250 578890728 578890747
    0xe032a01150e071403040309231c020a050310091406070503010e0703021b06040302060106081b0c010f022101060c03140703090503010e1006050f010c0209130209010605031815060105 80
    0x310b082582004001391000000e0100b010f5110985404440465200c0c0d4800c4440100b07400300e100700004100d0788040c1301d081e8014415491003087c4040d0348001c0800c810981c0d180080307400c0c14101c40c05418403544d42e000c0e15080c40ba041c1400c540740940700300503003080d1500070409852404180034044100c82d880300002c000034001d0341128601180d01a4504130580b06641d41c03a9112412181140103000d20300000400c0b1740168200350290001c1c41c40b251180d0f2205021015940000380015039664868a921052209038801802448245a51640c10b00d03500551f40d5100c110691144003001000c28510340420352014850343e070b405541000a1381c3d03607030302d0404903403594080e0040781c1c2c59443c19020480c44980010000780c0c4000d0000e00b4420740f46c0d10360401014062a00304580402c1e181c510800041c03424007402c1d903000c603100825051001080e0042903c08070240c0045020440010030320240c400307202c26101d8104901d034010045640c0c02c03039000b110918050280c41c180040031410450 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 578893228 1250 578891978 578891987
    0xf030907080a06020409150b160c0b03090a0309140f0904020111060a0b0114070203060718031b030303180224040b0f030604110c0d0e040e032a01150e07 67
    0xc10800007142d89450709400d0100c0203500c83d2040e100f2062030480c00b401806405804401180d52041010341004940b01064444544041080b9240c020200012681101000155010341081001046950704c68a00603002270b00c80e41000c5426042001c040c000c1e62b41d40c03143d145002c01e042d103000005489501c010b8aa0000000075080705000358020000409155403001e078161100343c0e2030700c00e041d00c40d00b00301401d8440e9500117905074100c000003418942c0240b510541b800c10380305201c20b0842d9a510b64094a034041038500c900c008851408100703040c0d06000711079420198203d80c44826200780d00080c80c16018103116031020503601441f54960f9248001e4030010314071244055981c54041903203500c0c0303520850f80644618175108680d08002c40f150159078080c0c0b2108028a010304103100142e5071210403101890f403040e02c0780800c1950302010302c05440c00340d451412000c41c44400e0945055240b071003100e5051182e14040000101c03403000715240b0704440603100b407014141c407000c40c200c8 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 578894478 1250 578893228 578893243
    0x8040f120c02030d021015030309230303160b01271e0f060e100305061b09061602012c130e0d0915030501060c02010f110106060c02180106050f0309 65
    0x20f5040c09030b5030340d5065003a004299082244000501001071800440034100e85480702d02020300011209002405054800c002000c484070490803101a86801440020300c3c5a0110301000d0703440005905440411458110f403030702502843c04c80494100c4120b8140401d1403d0188040d6410f4951400c100113108101c07032100d086100200c203001c43c1c06d8a0182101620283c0302d058890088000011000040660400d0a407039020000d4a084e03240d4840c030000c688174580f1041c940400c208410341c2640d032240d00820311054820748085c00d01d4214000500601210b08502030400c0044600c030ba102d00d03408400c40b9030120101c400392141030381100d4550042444901007000c07841400f0740c0d40301464100b2181c03001c0721084403800500c00d4100b00100c00f03498080c4940307004101d0800d688c0e0010341c000ca004140c0e03c0d040e4901104a0500f441000b400d5901c16446800418416600700080d07091514240d54824503840510350b555142440040680c8a5102040314080b80800030601d490014007040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 578895728 1250 578894478 578894483
    0x906060f08030a090b0306011704030509090406050702190809060a0c0209011d07032a110d08070f08041101050903120706051801090c1a0906040b12010608040f120c 72
    0x10305541d0321071400d5641c0703602a1079490b000c982d0454001441490000880f0300c82c0d801a502c2e0401925100e01d40c040c9000060011418400280203400458661040107886117014480126007402d04035800fa09080a0f180c22240142c00101d4840c017081d0b2240032643c81141c1642c850f65224a804421604407040c110000e501094540001074040003c0c07a0307250022024084e221615291910160100d400d240000c07008001d420f032820003640700442a0b400f0079101400c144400300380780c2d00c1701401d1010580b94040441e40000500c811641e020b02045400c003a1801d100f02c29044c65124a1800712103103840724100900040e00b0b03078454405004103040d000c100181d4984841c03c6203040c0f0041c00c4205c0d001d00c4600243c1e4885480104140160000c031604101c2a541c514181600f003041e15102c4018a06401801c01488020f51113401c0100004e0480e03010154880003000c400804800e8103900120400854809001c08200d1000c00c07002c50300e91000c10350125104440302a10b078210303040000b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 578896978 1250 578895728 578895749
    0xc120807030e1e0c06040f141c0308010602100c021506150c031206060f0711011e050c0d02011b030e0a0614090708010c0f0503040c0b0f07060b030a0312090606 70
    0x2022120080801400456190341e4141c80014031303e1014003c075402544100d200d04411401e080000368000e501d0008668005442e0390002e00c02078859520070500c0b504200e00062012004004a0340d040c0800700c0000d10101060200d02c0030410000e40d105840d921f01a042c1001c003003c548a07940303141040e00b0484e0301100c03880c0c442519140560b00c82e00710009001c411040c410001d20300345085030884070900c210110fa00e0800f00315440300e1300034100002c0d0503814080344c009904250401e041582807607a2803556066034826140100c5400d03c0003110701d40c0e080d681449441e0400029003040469116041d160010f00110303062440c03403800e003442002400c0a85064058051035240108c0d8a05c1152144201c601305c40c0d030382c03014500703d5010587d00c5000410440c0700032007d62084005540180c0520040e03072565456000c1420703e83d001c02c90011a04070002110401c2003050b000b602c8034840118040d00e204121914003030314007a400d54210380800da540c0c0746141006480d031300043c00b8154800d40f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 578898228 1250 578896978 578896993
    0x311070e040b0f0106021609050403030b03100c030f051509040c090c09090b0a0b0a0c0f02091e090606060702150d09150b0a030206090f010c06020a021c0c120807030e 73
    0x4050150342c40680d9034070802201c000000c11034900001f245040c1c21540281450054608922440100005042101019240c0d03600312515907042104101d00f07444003038009012400010050211014400050030403030624041041a19109203900301440b8107039000400e5a50764500785e00c40541c103420015400380380000f2130803841e60054584003918101c01c010018007100204106113403c051243c44044001040b04d180c5192040b004800b0040c407480d80071555001d1903001903007040c1d0458503010310b40c040b940c1003032120001101e020b4014a04001810b0700b41068401b02c1c00503c5180c07000b03405030100461980054200600302c034404d043d0244108a0700c0c4442ca0984041800c140e0165800d0f41064110500b030314068142e001140d50040c0b009241c00107003418002d41d18281444d1906116844020b40c011481038001401d500c141031b03010301a4a0083d9503892190010510324108101c02048040700203281400c0c214002015400c0841072655528012405810740e46a908104e024011 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 578899478 1250 578898228 578898233
    0x602030103060603031b0c051314010810110c07060f0c0b18160f05040b040b0603040602041505040605030a0e16060315080f0a060504020d020402030c0306120d020a0311070e04 77
    0x40c401401d5a00c0786e03030341d0700341c1c0720300c1c0304205040c0425404060300703d545056040255180001e0000320148030410086a09154506a48242c0c10264041c110640104031222a13002c00343c0708984006895800320b074104411400035a0b034a0500340030b043d061040c484d0211146900034a44010310682c8001000307000e241003121a140a10400d030401c5452140c80721402c60450740307000d024140d84c208101c0032421480d140801c0080d228640c24180c104d952103443d0911901c03650003d61149005030b001595840c0350000c0d414503004117000103004c0044c140400c0c040f46500204070703030700b1003500c29010964000d405440ca0611900300140084064510700010b00710f50984c04c004100e00e01d01070b010794a5980c07680095121030094095500a4100300c4454002800c0d82d800f031608980050300e44400c000d4035a01140403680252100c050286021007041102d140c0b041d0000c0c0304946901c06808509041c0c0b502950340c041912005007404040c0e02c01140510040080034001c1c503103c10880c025040030f0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 578900728 1250 578899478 578899481
    0x1a060c100f1b0f021e12090604030c0f030c0906030c030b0a0605040204151106011401080718270b011e050c01110403170c060c0a0e0d030504090612020306160c060203010306 76
    0x400100000d401034604a01280c0c0200c002c05c5007062001015010100c403841e28041d595000c180100e030300200034417002c00442d914106010140004074031000b01503096051605002d02198030501241c0c0c2401024400500108104806c50342c2c0415181c2b02900e40050703140203080a40c0149411a101140c009101c403e412100100d1507500c0e02c0b010401c207210301c10240c541c7c200340149541d20058900196203035100f250146d41c04013203450481210120005100060110755110301c3c81a613405c51103c141910f50060700810150130301c4101300204880380042c1a0a81000c000d084c40c0e00c02c6400303061150700910840381c064550400800025140200120f0190002d010945846d9002c0f00c4480d40301d5594405c90780c00c3d29a4000801040e03035030b01c000c541203900088607102081440d22110354503445004805500900c40e8035095240c40c14080b1403400c03950182d001c10a1209418011805a1804502d0030340104034004c20101c0c001011405403528142140000c11441c4008000014403030799 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 578901978 1250 578900728 578900747
    0x309090a14070f030b0a1505030402030709050c212406090312030f01120305071b031a01030b070201060303120209011b20010804050c0108100b0a031a060c100f1b 71
    0xba0744081126171584d0040c0001134486001d02c41241501c258410280f50080003e198070520007021128015111040c210a13107005680100c2401d10101da55803204000e56110648114011b00c60040e62500c4c0d589208020102400c008000030790303001042082d100c0320111000d04002074115000c4d4007000003400da060744101c3e5054006032100c0004600010401044403031143c1542e5a6810710401d500c4010702003200c00600ca080040f00e030030000000b207905030000e03041c0f070012803048119072450a08180d003401c010325a0301164500501072000940002000000c025a0b45d001600e81941d0001600c0c08203118400e00e544400c0074a0100c01c02140c002448001102a1035216448a0304801910b10035010313a0014401d41150f440508194440c0600507401030074007036001d10b03042e80d50b00107800d15803145007804000780c2c42d510b8954061038007c481410380031058440ca0b1030008070200c550b4450b500e01014450503504c5c1d6401c02440740040e041525013403846000e40110f400c0b010000341ca442d92 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 578903228 1250 578901978 578902007
    0x549030f0e160504020a02060a0f021c0506010906030b0a0306150812040303110a020d151b020d090803040e1b090307121a1b0c01150806040506010905090309090a1407 73
    0x915240203c0c050420b4000e0307455500842d0001c0200303440c1e40172010b01405441d00b80c071070429800c1c4801c0c280603091100741248000c0c000c00028003401d008000504098041d00500103050500c000700907251102c102c10000c03242c1000c00010603000348812100801066444100c042c403500840303081c048080c0c4001e204032442034480c481c0e02c9818004003520b411480c400654801c0b101024103012581c0c081d0b0a0700c042405c103000040c104450f01816000c0c80d000d01612005900c8001c131207064a40014001c1c01810f002c10040d030800307141000450700a000100078182c000d0000e09881208031800301541e60030040242941d89294035140f094050207252902601c590b0403020080306400b030031030269409417002051040070080d035201c0f9140c655000320301c2004650768441c1d101d414084500c0c480030143c480403010340b48a00b4541049858070704180c0040070000c4c40c040034440c0964000040307401170344081d42c201f04a0754420740510000c0a8402028080410308410880000c1c0c0c0504100701800 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 578904478 1250 578903228 578903263
    0xa050601080c2a06093a1e0503100509090a030c02030a150f0f020a09060e01050409050103060605010305222915010f0203091c0c0f030549030f0e 64
    0x940c3e03400c143c1e0380000b80c0c0001034034820401c082d0b4821102c0090307007a04100d0313a0038a00380c41a006100180c11a40394464040021008000d111b001c004000b00341002f41400c5604442c1418003d0340c4a80310034207403c00600f8810101c03040011501d042c00404c0440f82c0040107641041500900c803809012603410345c6064900d0302142c0040c2e0f90192081d10403041c01c0380d44290301e09041c0007055403082d4900000a05100d001e00c800243c400d000c0c010759020314442c6e440440e915103020b0002d4181c840203401c9060600d9009095060341c081108210b01e015007201003030349a900005004446501c1c00c94034061440302400c100240b50b0210400000c0e506000c1c1d940000c410102041203807a4011210081e070302440c2e01d04074280340395490000022990060720041115682e030010010001003581c012501e035041583e11900660500c042d40e2040424680c904507010001c044104010172171480358404c8421004900002c284261700450100d1807404040040d00566040103941d00801c2d03c0c400002e5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 578905728 1250 578904478 578904493
    0x6010608040b04020909070b0d0204090b0d1718040f050f091c120e0717011815020714100605030c150313150c0806090a050601080c2a0609 61
    0x51140320140d119541100c5020400d48503582003014265015001e0320451285a001141090308600104801c100700507006a6861902280d003064030344d050090351085458010010108038400340d060004140610682d90b02d01d4100004002504640c44154000c1d240007880c4000141a91245014140105200c00a0f9482c10344090307a40c81d00400130b20f41d54520072074031260341d030281a086070510804100481c00780a40603415240030225844421211564054910450400c0c03040c0b00b02078a600852903030b0360780c0c5030b10b8080f21031065019250364258000344c00c8003130011015120700f0450f40d4400b81c600d48000d250740403002c2d16450040741e10038000c43d2002e640c01e11701303424481c9000d00c0c00b1580c1411076440d60381d0f0050351a0822001d50300d84038000200101180340d840341c981400000e440d0205a030921100740010b41500404198030b483c80e01062003400c0e80c00552040e070048120101079901e414080d00078204044d070745801c039030380f5240e0300c2c80b280702c8500030071030511072081201107031640d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 578906978 1250 578905728 578905739
    0x9030c06030f0e0a111c080a0203070b07140715090f060c1d0f010e12030c0d110d0918090f11030f19030f2c12070e1503070302060a030507020601 64
    0x2111107284d001402c1d0110303d8038a00313160a0003406800320080140d8040350141c5103840301c4000d58003260005005810000d100010411890035082e0404820300e0010070254070b410300509c01d4858150301401502d1305201c6044000481d4120b614101d42c015400903404040b458101d0180074061942d170086000c080800f00b00034031a0043e1044648018003030207512070844010340d024525040600d401c6155035100e41c0003214100000e1561154171001412103c4c000d0000412a01c0c0c44010401144c0083c0e1401681c1c60340450f0203401e0392118000030860b0010755235424024140e0000090003807010040c4442803140e82c08440c1d8403030701c003501501c40040e08168003070b4807000c06028501d942003000c100da401007803280302140500703c1a400c045072025100c441c02501c3c400e0744c185888078100d1042d50f4079400d0a08410240c8080850720080c0240ba05008007510741920081c005259200b8540031003800d55010030892000750740142410f59501c1151600078007400301100c0c0311002d4814503000094 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 578908228 1250 578906978 578906983
    0x71b060203101e051f080a05041e08130506040302090f0c040906030609021c02030d050f0f0318120c07050d060609050108060708010b090a21020301110903060c0c03091009030c06030f0e 81
    0x40b0306071146e0310720550740d44444000000b488090810f40d00c201d418a0990f146074400d181c0042000d00031450756848629a543c0c2c8000100c0982000307005000500c02080140c030b0344160329800080301c07041031110b5941e5a00d10b00c1d5038000d40e800702404904111000050100c03030750010007180d00030354404e4031055112101450350106a440250940e10164600d180181f0500c00780c44d12030b103c240b65600d003901a1a003040300d07420598010030f0411210008080b030103010003000c603810500c0c216660030f190194030390302e4031541c0b1407203414090301f0f11041501c20425213038024405081c0d1940c04202c1946c49114081e43c4503030032510071010038101d070000314084809270305071b51044038014400100541012403032a045405c000c0381c1d52544039100001c6006903804c0c0510070030001604501c036241d064000401d454405c005d8450000703110200011490350b0700200403074040040954043c02e200f1380e4103900f01c1d010344c0154005044032061020119210b076040c1c102031170600d11104240034042034200840d4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 578909478 1250 578908228 578908279
    0x1512110f04302603011401020d03091e020102070302040207120216050d0201030b01050d0603080903160807051c0503030c041d06090f06031204030807020108071b060203101e05 77
    0x102c22292405562002a00715524240e0b0b5640796040c1440324001100400c0d0542c0003a0484c41013500448544451568100b10003002000b03030303141c20f200300e001d03030303250301a000c241050616080034040f42d021040da402004200b00541c0d014104640c0e841c1c0c682440390b40b0380b80150a18005010701c031b0441600d0807880d10024103444000305101110341d12030f4019001000d44201c00c07414400180102c0440b042c4900c10840114011a1020380d941464403c0600b01801c9090342c0600304a0351302d00340015900086c41505035030b001d454441d801941c5824002d101c0003082e00003082c1e8800081000082c09034180070384215000b801c440000b142c80d90402e030702445000c4807000d40000c20341000400964110300001d8000724040c0035a010130142d2130081c2500d910a07041a40c44c4040044e40c0021564840030090340020146170003103601c4018021580011104400940269004804078081c4178a800401c4003c00705080c0320b420f6a8421100380845260603c5a9445400d100c1d002c0141d44d031080c007101 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 578910728 1250 578909478 578909549
    0x80f0c1504080303190b0d0c03020a050d0b010e130206131e150305100512060103140309130207030e040c0c030f02010b1c0c030206130801060803041512110f04 70
    0x96007107070382d40c408440005191724011103595880311600880783c0c40d00101078143c14081e240c440c00407802d60062118811140e88000d02a003001d480800102e1080303c140780c192224601d00302c0064030344044221100d00e800700301031351001c000100c5c40ea6007000c500605c03003202c01082007070559000a1064a4700c45403148559008441140352411400d0f1007548965071000000303e0381e0002549480106e13030710098400181c40582d110100510034422400e011002c1000d20500461130700300d000c008110220b8840d5a2812910740200d1a00101806a080b0310000040980204403c1c1d440203170007404003c05060a6012aa1300071100c5842c030301c1805030781c01340ea00103001c41040c9106800f0030440c1a941e48010303940c1c05102e083c00700060380e44000606007415990400030405003440002403c60300c550340180420f90040008011407901007101e01103580d0f40c0c2c10190000e031001d40c02d010180c0382c0d00441d1104154001807680c01c0700700920180044d192450300a907800340740a4059880301c100c0f41c464 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 578911978 1250 578910728 578910733
    0x160b0c0f04090b01020a0c0902040503120702030d05071e0b15010e031b0a0b040f0518040f060509010f0f020d0b011103030a0221010305010c120507090e060307080f0c150408 76
    0x40c04100c42c580c00600703a80c00c042c41101e42860083d11a44015502600b0020030b044e000642041640740070029003050140040724503103000d80c940d0000c1d0340e030103050280d001030180108200c803d21502c00500c08203802001040b52018113a841c181c0030000c000c6628122000f40507210040d90351007010042c41e40d000c050300910002e43d0b01c0c0124460072240105a07039100c007001c0c04c0030038050400000303070000f0a040410072441c1030511040207091010421104062460342e800c200c0480c000b003e07202203140e004140059140c5032070540901404003d0220f0007054104001e0744244511680103105001ca002c8040107136038421001182c050039407960b240c81aa100b40049094038856a0060402f5001081442c03420301c45c1d007100300f007680026841904e0503555101000380342900b0550060314155010000c100301e00d0501d40c06060f80d240381c0240c41441505500041c540e40f820448003000e0410002207500c0300c8080e03440603070358424150045004290b1701c0080c004400e02d51042d901034410710b802 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 578913228 1250 578911978 578911987
    0xa09020903010e0307120e01020d0512070302040308070f060f0212060405101203090f060f050a0c030201410105090a090201020c0a03080c0115050d0303050a020d02160b0c0f 76
    0x103904024480c581c10b5580c0e4020840207402000104101c2d40b10b96800c00d010840544040c0c00c0c02050310840c1d0540d08039031120300540d90301000b11260742c02c030070340003504507110407100320000c1c002d40c0c000400340c2d070b40003440800780301c11003540441051003480103100207a60701200c40d042c2c0c080c643e447c81d008005280450b242d441c01d50804c41d03101c2914800c0c80c1d0241e54404a18001d80340404042e400b0401d44002072207400c884080c01c00151400c0d0904c034001707106020340101a48180c00c034a104002ca02d4034074400309403007074100110043c440e100d4140902000070780c48100f90941a010312001ca907828007940b90291001d0203074101e40c401020124140d89594504024040c0c02d88100e04500a40c16007000590319020341c08050341c0160300c9591505004e40c5428210351143c5c0c010b1400c40e0300442c042006581d81703803c04100310307810726002c40c40d0344030700c0c030b440020340030340c2038680201400421810107489202009002c880e0183e030500c0c0e000c0d01c480c11011843c2c866010f400100240800 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 578914478 1250 578913228 578913239
    0x20a021309050703030c12031a06070c080313061715150403020603010b070201080604050402031e10050c12160c020618120304170c180903190c1a060a 66
    0x1035100c0420350080d440841d005040da81e5690030038034140c00807800300e0200c0340c504041c841444843c403c1601d40d03040030080e81030145030744641c4841103030030b561180b800018001c080051008540c4010060002220b4464100b00444011241c2c00d000b070b400002c485003030400340004608000d5015100842e007c14101700e8050611000c5000100e5006103900d0400c00000142ca810008500038503c221103ea250702030382c1300060a103c00030f080244581e080c4030902005d07a0700032a400300c1030101c00c04518040703c3c03583c100a00300900386409040d43c03490402009680307a0140001c241100c49143c12070007990701c0382d422841400b030080262000a56103019180141464001005000d401c8003e811400502d000064100c05c00c00701050810f800100e010030010b0344403800054903a41c11340141955400300408141c0032480813184d5070004001d44003013103150b0000d00885200100821201c2c081468030040500b0400218600311200c0c01007401100451100010386030189200400d2a21520b207003a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 578915728 1250 578914478 578914489
    0xe0108150103111912060501031e031d0a080a0f290103021e0d06062103140a260f0a0504110f03030f13080607031512080f07080c120406020a02 63
    0x8110342c2030001144c100100e80320a138101e00b00c1c580743c0310321000700f41c84d0304500d040544020031003045030703485803011100380000343c018404200085828042c0f05540c40f41c0e01c001a890300c0903078404007090059034402000d100b41e51100004c4507020380d980c2d4030601c0040f5554110503483c40c1182104402d40d800500c014980303a14039041040300250240c400b00300000000c0e0041450384c2084a8895940e00208281000310089003400030103000b070484401e11039100640780d0080340d2080b002c2407600094001540d8054424110540c120700c400707030080c441305500030603c1e241c00c1d903d54450340342c0f003000524403003024002c4901ca1035000400d5103c0d400c0c000b0612010781c2d0b00d2034459506010600421114201c01d00103842080c86e02c070090034409150000d81750406201a001d8000c0604020340d0311864001503807000c0c200c94041074141c8000d905424000361601030261410500307800041e026007400551006041603205143c15034010010031001d00016208501c61040541c100400071009032520 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 578916978 1250 578915728 578915749
    0x8011112040f1a1303030f050114091305010207030f1713080a030608161d070c17070602180f030703030f03020c01021c091a01050901150e0a0e010815010311 69
    0x303100c904810300c2661481c000c1c00d4001321043d1a040c55034450b08028103a0602a1480b084081a8108070a506140a16402d841d205258600402da03500c040b600001c4911010703202079412000864950315285801844c2c0b005207900303c0002002c9480300b604401468000c02d0080220f884260140045a65070000e80e4100c880414149075440b14001113910782803120242e005803103400d0b50122818112074421310341000902c008184d5001d001c00a4150300501003440b15900a00d010403d402c10040184e8944683c010083c0418000b28003c0030b0402c20540703880c500c882c02c0f541e03444031118800078507940300c91610000d030000f8007440e5402e0082e8003903401814024180c1002502d000150601035841c00012042c001c82c180c0e0f00c13a60741c001c0c0144544601d2a404541c040e0030010f5241c4400251005418003454420300c003131845001403036000d0b03030b5241d44202c0043c0005410702e40e00e40000c4203000091044404c20701841c80c0c90907000d52400e44180c107880c0d0007c030300d600704812281840007030078a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 578918228 1250 578916978 578916983
    0xb06030a1a100f030c170c2214090114090c0918010f030c060212121302041404020f1c1704050915100905090403031e0e01020408011112040f 62
    0x1407180303041e0754079152500300d07a800c0e007210780f03038109940c10b2554020110b41078212500e08000200f04c1c032007030702550006000d0700803480e00c0341c641e164413031020751f04980c2c113803c2d6060360b00e8003405000050040ba91104111032010441e112445685d0f6600d0300c450640700b80c0211948a5110800945105182e0300a07002c66180581362520f0b92602e003484a4000300c0a030041050501011020402c1008031a00342001c2c040f18400388c400001e0310182141c10b40202e0480c400210744540015000c1a507841c48039401c2c5400500620000c1c1c07003102542c098403000d0f9400d07801446a0314520a80d8244140d08590b040000e080d1074a21444544664002d05200001c00c488580c040000040c0d42e918941708a00442d10304602803200c0207001c007009032400c1301030840300c240b0218460400142d80c5140016034010380505002c21a50000b00802000c88444198007102a20b06050040311520550142c401d4800c0b400c0200001c1030400240074036030080b00ca01d450241030000000380040d1013400b00360089803 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 578919478 1250 578918228 578918261
    0x103050406020d090506040203160b07080307021002220501090620030d110a0f0e0907050903011104060c0201021b0918010f0911100309080405010c0206070f05070e01090b06030a 78
    0x15040e5050300544d2503605050384c883d03102c0401e00065240a02ca2001d1130464258070003900c0b8a0b03ea84841d02d4003992070040c0540501000180e9140e009001c1c43d42030f40901d040455843e0303016444413020100131100f41c0c1a082c1d940c000454294052003070b850030b42d6000c2d04d500c0014800541820750522040b5140300441c0000d001c00c0b10f8550441c00307221410100095030b9901c0e0b0400a5004103c134003a400c11303000300152404400b001e070b103500c0b008030f030094114070780789940311007a1020902401400206400c2c000300002c00054056003e0128000c0c24401d900380c400302d000034001480700c42c4e00504820f9106140e038020a440302d28041500c1001c070440c0f000801c041318206032103012a45811402e49050240484540d42d80c0384c94000381108a00c0307400c041211010320346600341140294058503040c0b0a04c02010b40555a030300c820b440110740c7c080300e65041d059543c50480d071503401c03911a000c0c402c11080008182040c641c0a002d801c0000074010500355641d001e06da2010f4914a1942800c04 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 578920728 1250 578919478 578919487
    0x50105060f0d0f110301031502030402012a0b0c0301061106040510051f03060c080f0717060604180e0613050303130c0503010f0903081f0311060c06010f0501020106050f0d02010305040602 82
    0x50fa12030098100b58100b02d003c00b6160741c5142002c4001c401c03020040100c440c4100308100c0142c0c1c100c440f00b1401503144060700d00c0c4000780b82c080c0c050000c80120103003d80c40d0490800944200c00030065069804d01e50303c213400c40d004484019a0784505880041440e042820103000c0d4110750340c050f03603002020030800c000d0280040c03520800900d82d40c1003991207907190f000802480c0d07001114240c0000320a03502e604985021000140041070603544801d1a104103000310780035645810558016050fa030765540c82e02081071001e64000c00400944402e54006c40c00058808610300403052601ca400c0f801071441e5948518034401006440c0d03800302c440c0e9640e0740010405440920032061064154800020403620314240a00000b000038071001142030388400c10040940e40001407003c980c1d01100c401040c404000000b4040e004458840400c2c2c454032000280100704100394200b143e600703030020000c0ca516101800710440303070b5552558119030014038407001944030b40d014650043c013420005050 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 578921978 1250 578920728 578920751
    0x6012601030807230102070605010f0e0406050a060b0c0c1804120525060b0a050a080307060f020f0a0903030e06030f010605070309080118140303060f0d030203130b0319050105060f0d 80
    0x269808843d01e41360a80d800f28042c010000c2c117100c5c0c0b81c050070381c88002c82c404516180208040103001480202010b46510125104407010741040000e441c0b099141e03a22400341c0e000141e07443c1c0c6400c1049104480d4443c108241e0b00c800c00005028a80242000340c4182d080d1070283c1d0a988a450a46003045003000c24411001a00c44050007040c801c03480031851310b0b00f1008000350007941e81c00c901d100e4000c00408000540d00082143c00a59000704042a00884030309040002d000d401000004c02a0000e03804a40a40c04219041507902c01e84071030200604c00024880c1c1c500003150003480c00115400140b0406000c0d03400340503002d10904c0c2c0740c00a99101d4400c2400d40740747c40c0c0c50795404441da880803c200326050064001c902099070081d0300303500c0d1040c0003c800e82d000c1e00489006038000034103082814800d00466102e050310040c005203070344c1e9038492400c140d4011502c103281d01c5a1840410020200d80c080c890403500c00500c12800c019121103000381c203038030000f01c02640c0307542d50600055 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 578923228 1250 578921978 578922023
    0xc0b090f031605011a0f0114130b070507080606010804030c020607120503010f05030a080d0b0d0605070509090c0304020a06080603010f2f1c15180506012601030807 72
    0x1008030080c000e0754140b04a490a107003500c2c040fa41d5204401d1010841d4961038035a0036519070015400d10781b0103d5801c00065413280c6109101c1c0a450341280440c4c0070421540e00d400410306544036904540014cd07854a425886110130b403500750028080c0c001040109110302191a812030004003007900d0664159503002035070300c1d0400004086400800100304c0c0c42e40600b0303260700500080d4060b10501149a4a084140c42450850454650354142440181e01c0b040c01786880d09900c40c0c0100002c0c1071003000039000740c1040150701d104210500c00100320320088810740e402190b0142410b02c0e224100f10040e20110001458907800d0344d070b180601d007603440450081c95485450b00f8480d010400c1401c0301c00480304005000303616204c130304004242c120b40da0550360100d0600c1000001400c1c9170402e080f07034040c40082e801042c607014100a007000d05404c0d07074070140c00391000362a00f842031958401301d01070541e410150034400e514001d00400224a8003001032070340d54400e1a10358180e0021201192 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 578924478 1250 578923228 578923237
    0xf0f020a080a0f02010810050a0b1810120b0105040806181c0809060105010201061503020c0c12030d0b1906030f0b121e1209040911060301181b0c0b090f03 68
    0xa5803030b80c0090309042517503003110100d50465001005a14110f0514002c20606880740c0715080040400140b09001401c0c2c41713044584040e07000b42040360340f003080000146071159180c80b1014052500504403034070b41c091012281141e9100c1c0c01b0304015074a0a05048080340e07540c0b904000c500490026004c2a091000390100410b01900d41100d00e040646001d80740200503005181560306d080d40900ca035000008142c03480c0c030348500c1c0169075510103003c10307800c02043d01c2d1000c1e00706e0b040c20341440e20000040060f001c669007441c002c01c05081160700300002c3c40103054046480c04055001807012a100c1d0b08a6009a0b110714408a0101e00450100b01c9004544001154030340261080300d076001c0b01000c203025465850001801100c00b0758032500c686200f4000c1c1e081c0b24a90b00d10600f000c1103540b200300030000f04000c4c8021307240c2d03035215140c98625210501c1d9400c03040c540451110140b540f281c0050b2404800d41c0e030041c100c441e40c2d844a68108028146070140e101d41c44000324000010402071 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 578925728 1250 578924478 578924483
    0x10f020a0b09070806010518060904030203120c09041b12021812010615080714030711060106110c0d0b1302060d1a0429040507030e06041b0b03040f0f020a080a 70
    0x28803407103203058130710340c10400103800035441030142442c0683c1e010503846846412401c21140150700d03489610302a031030340c440c0d03072030844045205a00300407440800c603000d00b42d030903010348051080d084440d030828101130401c91040c020501c2c4100885801d91240c0c003a04100704d1040800c810600744800113410007008000d04610b580d10303880c090082661803802c1c11244281410050380c0d60400b0f02014080d00c01c0050b014a42220201c006130039140725a0040844280b500141c4d0000d503141c1c10700802c1c403880c41044400c98403c0490f029581c0c100000c550030b0780c0f600080c0c40c0c0d46c161502c01500160280010341030380c3c40380c8280100b405441040c46603483c004598410000420080c3c018082541e12035007541c40210040d1004021000c809004000c0400c030450380001c20b661401030070380081c2850b089091051040a0810040006003801c506030301e1025485651036a81d6440c101e0340602c400c480027071024620302c00c10400540301010304680c2c148010303c1985120b460301c2d4080d203400b440341001d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 578926978 1250 578925728 578925733
    0x70e010909110706111e040f030209220b0106080603030c120f0915070201090909020603040609050f0a0b061305010b0706020f07240b012c0f060a05120702011a010f020a0b09 76
    0xc00004101c106d04010340c0484140141414642600311b03200b00741c203110190040c0006400100e078003140c055a0f1840001c0c1140240c0300111341c0c2041c40b37003000309025200200721003902040c1a0724000003034442401807100104081044e1283c280401c0c3c005400c541d5007298140f01d03901166070742108a0f0300d23080041c5002622031502d4000109000320301d2780900a0346141201030790240e142c14040781e038000d0704803002141036503481c03510500d800c4480c0101490390042c10b642d0340802080c41a914040e410440b090314180b8015011401203a20a100303181200c003040050600150030f41c1c014008002d1014121400c00e40f5949501034908580300e20301009400910260204040500c5010415642864640d480000206082802103945132140309c60700700300e00906a25039680720a0211402020708450703100c91400c10050083d41180d850340c0b00ca0030003d4001001c85205200b1380400e05d40e00520f101005201d40015144442e003004007078110b004d10440d2402081c4139000300390207400000c00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 578928228 1250 578926978 578926987
    0x912070b190905010f0c1b050a140f06030603060103030c0302120f04061106040b1506040503010c08040201021014010510120924290117040f020405070e01090911070611 74
    0x2002018804150015411701032103500e001e0109900091507811642e1001041081c4024981c46106c40d1100d44c0c4501d034040e015500c0072134904903042104a03481000c2d1603072400c44203140308010a41c00201c89050300b42d44028010004244a40f902403408c82c0280181d4101d401030824ad048607a001d078540001403940040d0804c0750b90750064189030320701d007040b015000505003583c0f40c200c02107014243c80c0c0b41001540440a01d0390310b1004640061100070020451400b103002c010f800c14608460a0b4003601411141c4034584d0103a008002c80412000040c194030f038280002c000148900d40708883c00c01407542020342e00e000d920701c03a6580060042110038802c0b090780005e10810362050945425503418100440c0d50740c201e481d64001d4294070300c02039441d405100b5004803000d80c0081c4130800b40c3e14600c0207000c02d100d4043c1407a1200c2e802954244460380d00d20000391203548008500c0c0340000e81d029001c004c0238015501c88944c400705142c03d20b241441d9603e4913826548100102c90502c0b00004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 578929478 1250 578928228 578928277
    0x507110904080d140118020a1202090301020c0a1118100501050d0209280605040b031302010309150b03010f050601050703121e050f1503120d0204170a0201020705150912070b 76
    0x40140305580c0c800501580703016230004004204006c0c294001e1801a00403030310071040d81d000e405035840c1055400854159880f90306001010a100c00303456409000c0142078602a102200042c030b2203010340002111065182400443c2c16034001c0c800e83c401c0319401e100c014000e80d10a503101c0c403103820b10b80040c558070700d000303031760418080e06a48408148842040104500b0045605407a4000032000d04400510554001600a001560300080c101e0084011804030300c41980d2100c005d098080c2c000b0052107043e40041030440c1c406030388043c04180c003408808e0000744103541602075599115008036041070300102c03096102c41224030304c400d01074a034002c1140e14004040390b5988080e00300c0d103c0e0780302000e0f0300c0800d40720854131a5142010400040e0a40c041d001501240d00401290700c1c5480f11340c04400340e064599078210b070304a0050040007000500d900e000d6541000c04401c0f42c1416140000410070842247d610b2540c1030700c1c80c010342d0b03400601303c9460000b6005006000019045102c000ea = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 578930728 1250 578929478 578929499
    0x3030c020d0b07020f060c18010503040c0308030c0c070b0a1b02130c170906060108190e030a0f0e0f0f060c071a040503060912070308060d0f030905100507110904080d1401 75
    0xc0c00c4241f2000c051100c04030103c03a44009a00c52082824040d40d26100c0f402c0071080158140c01c0600078031000030500075120082e01c0103141c03000c250300a440b01c0b940c942c2da440269204540c00040011401c810b00022039030700c66079002c185e0307200520401d0704c403c00300e1480041d60300c1070100c0c0d00030034100010540c1c0c0600c1a8106503102845101801c42460620006001d600f0050f0591040e101c1c0c01c50007180c998201d521240c0d00003015000c407a01c502204500402c0380d54604514400180c2a07411508103080040c0100703481c10b8002d11200b4821054002c1c440b0304e802c04a00c0482d980f00301c540000308048030200311194115000c0407190b40714142024140b52400c0a401c0c00340582c000009804056142d038140c61905a00d0b2404000941381c040001e190f0125150003d40720801d0f100c9410700b01900f02403403904540e0705988141004c2c011791000d60301405204d401810709850840c1c102010710380380d494154440d22540815080980e10840101202c0b070b000402049900340b000103201c01c4008 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 578931978 1250 578930728 578930731
    0x415060504021309090f0b0c0a09080f0c0f1c0809040b0d030c02010309020d080d14010602030715050601020106030f060c0306230906241210050a03030c020d0b07020f06 74
    0x5a500b035103040101c515101e000e002610801502c942d41e404803800b0000b11070642c064a5030407100074030031805c04500f0700d607055100706060780200b04015400141c030280070a098581e80d42031341c041d11030f407003030f0000f0b00506c02c0035404840d134030041520711303c00d10441c4030100b041d1480c0030385241c58807038040c04140402c441072007040d84c0c800d411926054000980c04036141c24129820729020450100c00d10100d00d030320384c038610000c0024102090f0310007141e1681c0d000481c042c56052010501e40d0341c0b00c0099031a889250006440c500e41c0442c50342e00055260400783e08080c040c0300005010750f80f80c5405803203205040c01103488036211000015400d6041c003905010f007002642648002421904a119007401c0d004214060081d03980010007981d20400c002c100b40040c0745d060300c20a401f481454a880d440000b10442d0440650302183c100582c003448130f03060b13640140a010780345042d030b1415107001d0500541264803410340380040002801d0141c61a000d01041c0e002403114500340c80005040080 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 578933228 1250 578931978 578931989
    0x120118150207050304090f060b0a080403081008100e150108030a11071409100b0d0623031509030c03040b0a120e03180d0210021c0206040308010b030c070506041506 72
    0x5001c4030b008035201100712402c44150100021701c06500d41c0c1c0c0c3c54050708560f803049400352800b261440c1074542103d000341c0300e20b2103591500910750f1004009040f40d111401090300c41e6004e19006900101035a010366049004002120400e00e44c00e207107100110400d82001c0c0f243c0e040800c00301641c0e42c1040209920000701341c0900000c60900f00040070500311600f000d880390300e0300c80216183c0342404800c00040c02d401825160340720b1b40c0055030405840a07102e1040418030100d001c462640750030190f01c203420700c0100504081000c04460000b0701e00060b062140740d0204021450032914200001c00060031049640340d180c0111103400b40c200740400e61094041404c00c03400010201c2d010048810f407144002d100e668464884000c1500d98400250082d04800c50b04078100034150006400f0381251030104521044480081c4122f890719400c0c1c81c0100403c0b54070f0018003020b2414030185070300000b003964880c200340c40b645945180c280180c070140c2e0828594203200400394494003840000e4003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 578934478 1250 578933228 578933231
    0x1704031b0e040327030c0f0501030216141609150605130902210123030f06070806131407020709020f0304020d020d120e031005071d12011815 62
    0x245400050301104000600c01030030400c402c0c1c2c0034041c0703c00d514480b0b0050304507130003040c0415407245052601e0700040e005c0c61801100c5071800145940c0310b4004c40c0c40300d030b02e02d00303020401c1380513a641d80440d811402050411030140104401c14028032020850041c40351610204200a40708081d604000b00c1c5d4010303808000382040b03407680401a660b00003044074095140141e90b260ba94501d0f20080d510719170001815801c10000148941e1074403042801c020b0240c0e484203544e01d6074404c05680d5680c540c0c128429421040c00643c0c404d01800b0b04960248000d00104a07500000c0c4540d002c071800003400c0c032000380311032040c802050f50400865028000c3c8000442c0340190741c60301410715010090001307201c0e01200311140e085403503036100c10003803076801080d00d20b64012003000074003c0490558900d01174071902e00c0f4040d01c210103005081c0904030a4541200c10018110002002c081ca40c2c4802e400680708014403101c4102449041c004140540a209a84920b46000300e54851030215011165 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 578935728 1250 578934478 578934533
    0x3070c050411190905060408010e0d0f121e0c17160212130314030406030c0e100e01030e061e0a02040e0708100b210a050103080306010e0301020403170403 68
    0x448000e01102c2c80c440e03c00c402562101141c0c1c10445410580d80c11060300890040b80c00075074908150050302c05080000e060303400748681e121080710310314108440300d070004649401c41d03090402e00350701050350301c1c8440070300310324400d81030910500342e07100444e207500010401007180e4090f400600b0901d402c800d241081c4040c4070b40e1010004d5036040704270403042c2c0310f003800a05c2481d01040802740e03d000b95807102420448040100c80d194603500f0501c10b43c2c0129090044003032080d4820031000c841078400400c0011158100312045422103d00c0c142141032640c0d802c0c007429500010070100380329840107254150220300c17081c501082c5520180c000c45000b40140024005601c0ca610301035480046898101d14a035200c810f40421403040b68401c0c003404c10001416404400761542421382c640c0110b030110201d880703c00c213944c01c0314800d2101406045062021500f150320401c2ca040f01c528005002505007038880d110802215510648046130080000d130400c00c106118814410120301c640c2c0c5800c26 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 578936978 1250 578935728 578935751
    0x9150705030c0a081b0d02030316200708120a0c080d090b04210c080306040c17040506011410020604170403051218060301060c1506080607030b2404030b040c0506070503070c0504 78
    0x8c0740000b17444d4501c07003051111103c03010741c401d280b000d1201500d803203203481c80141041034a44a5000f40644202406080000f00403000520700700e41301412184d590340c042d02c95940392174a280c0c1024030400005500d44280d0b4001c100c82c040d03541c0c011800388100c1e03400d51961309801d580381038070781080100740414060108041355031201500d5022030259400701d034050001404555030406a10301504c00030380981800240000002c815050f140038441160380f50041c0e00420407001c010034041e07401640303c0800140041c0302c40d921202c0c403010901c0346600341510703039594a050800070400b0032123640c03010564440808140050080c1344078140d0f00c5500c2e6505128000b042e8940c81400600302c0c800d21a00e904a0071026400b40c0c000b0300da50002e035851402c1c9010014050252001c500348290114250f0300c1101024131081d07689044050041031510b0702e03507500c0f282c20b01d80c000c1003a0b4803000030120006c0c4588030200140a1781c0e1240c0059603803030340d032131400800009003900240c0c0210318101c45c8003130 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 578938228 1250 578936978 578936983
    0x501121803091418060d051e0106032d11010e03031204020906010305060306070503130b01060804050d092904090908030a050108190204050a0b040e0a0b0a0209150705030c0a081b0d02 80
    0x170000760581d01944280c030181003483c40c03c00c0500303030b0300d41140c0b800050b40405803040d84074805503032040d0b4245000340800c0c0000382101c00320150301000c0403000750b81400010f600e07001c0b03040788000c1030501800d40910a0006415604548411003c0f10340e210100411450032886242e4032070824203040203030381003a801007686d40030014281001c3c010000042180040e429544200707140c1d008589900d25a1034020003040140c040e60101e511b0f1040000300c413949801030004106840c0e142444072949a518035840c00b0075176040e1a004c0c0040720402c400f04034010a0700804a980303008244080c0da81c100040d609044840c143c0c4074655070b812401801407035542c0c0c01841c1601070f80440c1d000c1019102c850b41c0704000c02c50646001d030f010345040c40c4000003100119507110001d000d440c0d190002e588580c0c5650680c465410a598419101120101d100c0c01000223003d42d07902030800c0320f00340340c00000e455142030000141a150440c0105400100611200d004c8002145c403402804100f01640c44c06503 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 578939478 1250 578938228 578938231
    0xc331605041242110d09020a08011a120705030309042403030807030c0c020d02151c02190219060f02091c1a010f0501121803091418 58
    0x8220040b26041001402804000f0b5210000302c1d40c11100102c180c3c00c2c04a800c0c80c1c0806014400c1050020350b00d41c2e42910344074080740c041e681c1e006140b4110f800350f90309000703080c000e0040781d10000b00d070000310b074500f400d00c039140b441d0245002c0f40300310300c420754200201301c14001c481001951010809202e2a01d0110585224807020b850214403a449006440c2418401c0440a2407640148100205156101400c02d0013840c494408202002400200700c0d50110004406908640c5d910000700040c1482c5400c5201c01d8007190016062894101d03044404500300c074017600e0250780116003000c0096403440d9414801e4030070b0005188049a42d0740c40c4103d840c0d02c18025240303503680c1c0756200d5020419011a2104c0300010813404001c0c04c2d41883c1d00228080601c1600c103844501c42009540d00705c148100c1c162007900c0b030781100700c51a1400446218280941a90f620b644a0305422840a000341c2000591482a124401420b080c120003484540101d04810b00c42d0120480b0080c00340e90510703075503 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 578940728 1250 578939478 578939489
    0xa0b0937080d1707030902040f0b040f02160b06010507050d0914121b060417070f09020c0a060525050316031e2007031701090b01080604020c33160504 66
    0x38406030b9152982174004141d070000c081d40140c2003140b142034420042c0d02c107071640c4000b01d50400207003103000901412802074071254481100c020b03e10388082090305456580c0004145081c500e0300d80703583d91300340c14003004c01e000e81c022600701c81d402e000b280d461106d2200441d0059882c2c0c220144d056440c2955441c0c429080361441c580c4042508540e11140102c401500b8904541101e00840001495480106c0d105a6910034140c0f04003103480c090030300880d016180c145005090302c52840d00c0d414000c0101a101803524808994a01c40300a100f802c00c4942590b1611084c0e2a85030003e460340c0a19004d500d01000c152404c1c10a40f514601003031145441c6814070302c0020207070384800ba000341414001140c4590012b0105624040681c85010103041c1030314035611507180e90b83c0b02d01c1c07a4180d4140804490107e84060005a17207810241d0250a219400c88125251410300300d003c85c6030703801c0391180f03911401d00302d04011003004180303027040d40c0001d149070302c0b801050b10004004100e0700890040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 578941978 1250 578940728 578940767
    0x1212050306130c020a06020f0d06120b070516060518010b030609060c09030f030301080a02100309120e06160308070201140103020a0303051c0204060215060303090a0b0937080d 77
    0xca070640f82c420044031018a41c041c20865443d440701d041a15543c2042c94004607003401c2820104000303444250751800183d10411892031500d941d84140c1c4e2a4102981170001808680b02d5607021070100e01500340140e075182d022000c1c54041510050075141400e000318080c0c0e025000748103013040300250956000000c1c10700720303813520304c1a40064245160411503510a12001c00049007804001c905a07000d18402c40c1e102c0440204540b0603015508404005004c0040c0304200d41d40b11801200120100180104141d10380701e41480110100c40740a40190700048100e010040741035024400e48200f80070b0030000c180c0e190301d1179001138404001c0b0700001b42001000300b803482401d200f0401c17403e07019503500c0341503450325100d07000259280341c3c03a504040009107050110b0264203010040300e11556000c0e001c40300250816002032076075032103401416000164103083d00c0d8050701c89001611115000080d200310490840140250110240c0040b54241c01a100b5141604d0704890100800801e05c80b0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 578943228 1250 578941978 578941991
    0x3110d061d0a02190813020a0f06091509050d0c050405040f020f0a030c0909020409051902031209130e3a02030322050c0a2706060c080c0115121205030613 68
    0x18406040306c8914000d41240210402090320079080c4a070300c041c0d0310103542d20021181d40320369204103550203000300404502c100c0c03024000c41c1001d41100403442c0c0181d60401c851940c0344041801c903242102e06444001d80000300c0011890007540e41a0314a00c00c8a00b1001e4500b162a030543c0f41d40c4c1c03445406801035a80e0194011512076403c03640300150000c05843c048030041820000308041c01030124030034060500700e8501c111549003603a01a54010384403010152540ca00030000f481c07200511811407240c01141e8a5415042c0301d8400b0065114020001000d00300c0750610044400c180e142c1c0640d0000d10070003114001c2030209a03541c0c40207002d0f503682607417203040c800d003020301141215400c5865a440460b0f1450161180d01601d841c4021110020381043c5c580d20441d1058060781e80001c4100041801103144e51001c1c00e200d0325004000910310a8000c12110050303041c1c1d101060035140c03034200b40c1c01c2c406241b420703c080010303606000740385241020005003003020103100800c00d1580c464 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 578944478 1250 578943228 578943241
    0x6030b0d0803040309060809010903080105060a02010f020d020d0b0603161b020310050f15130213122d020901090f020d09141902090703110d061d0a021908 68
    0x150406003503074110a001c0c0c0e403400c040c10000c103403c450740540c4c401701d00b495002c505e0707000741441500c0c03040c2c0d016603c60015074204802c000c050b501550807001150340781c04140e22210034034402031100101003080140e690462840d50707400d56000b4200d562040f00107008000c0045040740c1c03849000d03202c42c83e00c1f80441d00765481081130340000d1038010b9014818441c180c0711001c000d44c07090340507034039043c40310070b135907030755407420800d00d603d080c00250030681c1c220009568010a801900451486915018016440b1022552500540c101c1a02c00250524800042c0c400b01c2c0c21200304100307103002414041d240d603004150082e50610800e48561b0340c2e02c0c600d85024284d40e044c2c1d0707191040345c0424440da0046084c0001c0c0c406105c0041a568055800030000c08600b134116208240c0d4013074070f0000d20380d07540a0300760000c2484020942070b03144200113207615130402c0e00c1548080c1854685482030000c10302c488041c1078000400307003200107104000c1641c650f00300401c010207841c1d02c0e191290711551000c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 578945728 1250 578944478 578944489
    0x712140601110724030f0203040309051002030922150b04031506030818030d050a0c0602071a090703030305060108040317040201022518051e060f090a290a06030b 71
    0x15804902c050400b902810140c0145030030b401c402c0702d0344e0341d800d2201002c1c21903800128842581c00a0208075520740810050a160404100c0002c0c540141c1e42481d480c68081105400181c81d00300c0703048801203121940034000c0c070514202c03940304420703410200e04000c80c1d000b607885940405040d0f005c0d02d00e99101480c1c91504010080c5030b1010015803607410014001002c040c54a035090b12900504841d00050340c414415646020140c1d41c50103100d840580303a080095004031004d80340c0e802e00794011850410351012032030160505100401d02180f56007002011110054403207810420f8040c280004a82d110140e00b5000100740801069a101c500c0141d1034130544a041501d4041c1c100314030300d03844010a0208080744d10520780740071644c8840c005801101c004a4007001c3c2480048020280c1e2500c00540f40d5210401800345c02200c112800041c40380003046400c01c04040d01d594200400b19440403500b6075503070510000740c46503500c0400045544c1894060074042664611441c021035840 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 578946978 1250 578945728 578945743
    0x203060a09051509100e2b0f03090c05040507210506010806130b03011a0901142d040f020415020703080f0a0219030203030916050303090d0807050105010806071214060111 75
    0x42880420103141d140d6619500c0c0d02c01082c1580e00d258003c3c08191f030303484034401a0035001c141c540d110b0441a002e00030990007450300d00001d84040c21501c0010855481d2846202c2c02090315031150904941d841c110560503a0300800d0b0083c4140c205000d00039982d07006030440d50800011070340b900344015004410801085c00c83d500552640c200340f220600010f4098036002da1700b105540402d9140e0700c50602402c40c100030741d0740035046201540d1601043c1d1307039107401d010405c035034948132140940984001130a580740030440740c0c4255400902008201443d04852401d04c90a00141400c0c500d152100d00041c01980c2c1e01c13400200c000110104850b00c00d0000401049542c0010190301e075103414001c2d81e980080b41c4002c03a61003240f060840e0f543d90b03403642200310f5000030001e5140098000500502c0f40c500141111420001e10003100015130a01aaa010f002c00f2401022280350030480240303006007801c2c402d040c3ea850005891001c80041c032000703038096000e00b01200202d0f40390194600d403c21 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 578948228 1250 578946978 578947003
    0xf1c06060804140102181002100c08310f03050c030406080105120a0f0308060d080409020c16080309010c0305090d210e0d2a06050903010609020c06040b06010306210203060a09051509 80
    0xd048030b240300e0716030420519405140f123000510503c0d04012101e5a5081d000841d038149103004103140e500292137402c409681310700c00d103411410106d04910351461500301d41c101c640880c03520401445030342844d11031200041d4440e8024407242c41940c0750113010700071070750300a030421040c0b10011301543c4034002440000c540c0810025540c5076a0220140250032005029105009001c104000c0d40c240c03080d82c0d004d5400c10400740d868089060300644075504258401c0b0140103060201040690750344140c401001c1c003400031903902d404440f0350961035502808100007880340c032280003a81c51701c0e00d505846410798030001c07458060091008045884148118050503901011404038080d580140030f001004001e80090020039205c111400030780c000d031b020f07000c003030741c40107000401149600c0c0b211070300842c0605002481548612000401c0900c1115488407500c81c4030580d0118207040121030303071101c1103400070000040e0543c1c130180ca801900780c007100d0b079481620115100000901c10740e0905030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 578949478 1250 578948228 578948231
    0x1216030c0815030c1818011e1a0a06120f0c0e120307060504050304030309082109011404090c02070f0b040308250b0105010e0907050f1c0606080414010218100210 71
    0x50003d80c4101c0c4641e04072000d0a16500d4807001c046c00d940140581844215010b24680c400030002c0c040c04020440c0e0305621300078a10949034608141c0711a035048000d40303619600c040600d014141140c094820b141d0f0040307166031400c034030044a258080c02d5000702e03d50485030340300210641c0501c02c1c0346020740359015100600d404107100070040d0000c001d20490b07109840300502c044c1d5800d665030b1903203a18400100c154525441c41d00c1c0920808006101018050400c00c0003a034005a000510381c1081d08071500e0340d6503860307800100c9030301002981d005210400b92a40f0306402c0c0a02a4254000c40c80005d10800f408501103d810b0202c1d841c0d04403141660002c103200d03a9840c1001c0d03061360300c02c3c401d00303010944030846880981890040c640c03181e900307900c0b00b600d000302c8491411100c6d4051420b0340038015050315191180000e0b4040c0000800c1039645060040c02c1609000d902c0f050703000022900e40c0e10400c6047e0342c80a5050a0480740c1c0b20498010188503c03080e01a818400c0b4801d401403850b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 578950728 1250 578949478 578949499
    0x1140106030212010e0103020315040f0c0306232203170a061508090a031b02120102220e0c07060e0f061501030603021c05030f1216030c0815030c 64
    0x403503040d400b4008407807074048900c8144c0d80e100c2034909960740c03e00010307425410524061000c24080948070350803511901000000e0301c541c0d204d40950305500d0b08121420b9446c2c480d0b8106000104140c41c8580c0c59502c041405802d03d11959829240252054039150240c5580a0145400350200742066064440d03580307800c0c030700a4070b40c40003010b10f4011440c910402c0030301010703860300ca400e9035481007527010b00501c4408805e480c1178910900600f40c04a810f00c841c0b00340001601c9400880100703602040c000b584400c40d1600085885da0310282c0aa071001d080801001a5054007008980107049032102683e5481a414414050035042200f14030f030740301d614102d1480620015000b84a2602642c0b42c0c0346540a2200450503542c8a100c00703540506048002d026881080507042701041c820f50803246048028828007803640c020701d42c0f688811001d441000042422842494080707003241c034080010400e0f801000c2c0c2011000350050300f48040c80c1400151984080102c0f400b00d050080405c0d021 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 578951978 1250 578950728 578950739
    0x1060f0819060b210c07150e1002071a01140a06030c0e041409060109110403080d240303090e0709090b03070531020a050a120f0c0c02091018020a02011401 68
    0x2895444071000180c50108000100e8150001081c1c0b41c0c1701d40e00100c038000c405211070550300a040245460012801800a60140d0307058500c01404400d10800c000c0d8150f400c48cc5685035030140503406656006a090203004040c0c0e5000420320030350720381e03040010300744401000494003c0d100c500c079540c0040c0352410030300f624070b86402445c0c490508441103a68982e220f821802c02e40b66044650a09008180300c18400170706860080d00826155100000c0c0c1003091320501e0400e00e10040c1840d007407103540c1d601842410350051900d006000483c1c100318580c206400014404040c912030000180e68900544034155401e100c0070005003001014450014290048489603c808030300080d001c84201c0100c2a01b40064000d4508082c0135442e641e0605a8142081e80c1d280076102407c401190b40e60050032804510b4419808042020b58403015010b40d28414401103000280007014217161040c02002602d88241103445901204000561240826001039014080300100320007000c203200000300342c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 578953228 1250 578951978 578952007
    0x1113150f08010506040e190614010e01061b0302030901030c0c060c12060f180b1512010620062e1206061e23060a02060601030501060f0819060b 63
    0x6581e0110001c000035160381041000b1508584100780213038100c104002d025520361480309007424040d213008245581103d9481001c81c00036003000722601a01c1006002c0c075079104400c4030f03201011480e031503e143c0c10ba440c0070b03580e03025520242e81090b449040011055208541d403004940d40020b081c0500c1c140100041d08442103c0d000d54901c0b881e000c0300152850765924104104d400c2c01070040300d40181a0540070151204c91034603500b2030501c900c0c400250b100c21000744102482c40c03000e0801c55045c0f4000502020307400303003030041d0710b4030500c509480544086801074001c43c5460040d0414108241d50441c0c81344000c81a0314484514031001815480700415101c54030b104041c00c100f010b0301c40c1040380050780100c1642010031000c80d07091000e11152442a132694110058100101400e04001021030703200c4209607005030041024051a941c0600580b400741807a801e0030302d400541150006c040020040c50340d40700d410355015128006180b80d0000001d0041c035001c603552140c10700c0e00081c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 578954478 1250 578953228 578953259
    0x6091104020714061b0d0b120f010b0f01080103052d0d0306150504080715020106030b01090c110c03031c090204050103050d0908070e01030213140709080c0904111315 73
    0x20018003403400065050f901200402d005c00143c55055030400c000046040000d0901c1091550442d9141c3e40152512034200641d4402c00100400802c0366000001407140c46001b1080b80b41c18018070100500029801040510030300c9296004100e410107038803800d41108125030b50380c42060040a0030207030740700d0341034202030191810681414207820a000046485106910a0341c4564208803001d0251682c0b0026500812102d0710001c201ca640300c1d21204000352080c0c0c04104100d035900702d050403054004600c00450303088107014045420101d40841d48900c80e0042080f59403c04040e290038014050780b11740c91190b0060300c104203c1d82c4030303d45a82d03105166007041c0042a000f20f000510b08000040403015100d02100f0300407140d10b140e080c00280d8280065204009072201100e0003520314080c05184030300e081e42c0d20003071218130f020349850a056003446030502541068080001140c01800c0c980c42c20182582d818006131040c030781d01e100601d0302e40c013400a140041400003425085030760041 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 578955728 1250 578954478 578954513
    0xe181006090e0c0901180510030c080a0c020d0302130b0309010902120a030c03121d010203100f05100503040507080703060902100318120e040f09110907050403060911040207 76
    0x18102d0700c0718511116101d007115981c0503c001001584519486541c00f2044017240c00c0300ca40e807468541d0000b40300349001103115000a5034590f001c0c800c07a40d000741e81c3d0360021080c01c820422005110b100030340703a03a4403001d241e0505400242d0811400050001080103001c1c680000740c9a040c50701c2d5060291001d080282d11921346505800c1215401080002c00d1035415280c07844c0c082c0c01c0f994107030707011941600d000c0f00c1e01d5602e898644000b1080002614107020344800182e480c5001c421605005241350021a200e68440c0c0d800d000310b449400f1580207110302e03030500d0394903503480d481c0051414125810004031409001e500004000d6550020380c0358920848903c1d0b07900d442030000320b04070f400c14400200a02c0600d003070340703000c14210034a001c03402c15a441c0c40f004004010000c2401d481001c141c245070255151491800d00407050051180700f0011a0382010900304010001c1c500d000d20b0002401309a07544052000700710102c064007500a602810a41d2141e03210b0901400c02406003461 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 578956834 1106 578955728 578955737
    0xc030512270102040e060915180406060b0c0d2f060103140102091e011e05120702061603051b310501050a0e181006 51
    0x1441a6400308a01040001d8000d5070403071a040d082000e240c0340d10600040c8148003204036040c0d017000c0c2c1100d4a44954980c0304042d581c0c6a406808a40d0081c0c0108240000f403064840852060b0b0040e04100601a40d42c081c2c0c0c0158420b005001c0203039000710301050a81802604004140d101d154081204c07040741104003284000482450901a07120200400400940d1400d8409020640009600300090603004c54410140b01200420344044104041604e034454540212805861545020098194200906107034010031500b0003003040300300000d02190000481e0780c09901048159180003101000c21002890301500745100c000485003071030b912341c0010000e8052548210502c6200510f1410313944400142d14084941345c13032805c182000280e03000b000f5200c54500c070342015500701081e400000c1b009a60019200034a10591040c801c1009031500c2c01002c4ea02661103 = true := by decide +kernel

theorem cover : BRFrame.Cov 578776978 578956834 := by
  have h0 := BRFrame.cov_init 578776978
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578776978 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 578776978 ≤ n) (h2 : n < 578956834) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
