-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1787
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:40:26.088172+00:00
-- url     : https://prove2.me/submissions/7d243cdf-762b-47c9-8aae-310c79f41aee

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 321223021 ≤ n < 321402877 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 321224271 1250 321223021 321223033
    0x1603020f0307051908150613170d09081204090b0607120f090518060111071a071106210903121005040507080c12070504030f03030509100e03040306020c 67
    0x250190103680111902c0000ca4400718100b000c2c5002c001380b000b444905400c4c08a100e0902059200d2070000b002d480354401c000010340c080c01c64801c2c0e08170340010840c0b8001c82a844c805840c0e09a2150394a10410000a0b00090b00291101000400c442009090100c442c6010709000b03140026101209042da0070400c01c018001c0054842242008000043c1e6180c2d00c000c481c81a0042000c4082d0784124030130744101c0744070109480a0a071950304000c003401d1051044240f029202e00308002d561141c00c10320b41d003091103210340c00c1010040440c0c610801c6140340c0074110804012042c003a600120007034034207400d02c02e448501c060303d200740c0140002c0205c80c01c1005030b281607640902c0455a145541881001c2008542010301820380c001c1c4103030419022626108250000a008808405c2a00a04134000c640120b0146c07007120003464028100300907504035810082c0c007805055030b4a180d2031140e82d0104c04ea0b400f143c81003824409500010310302c0d06245896000280d04030310821200c601401e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 321225521 1250 321224271 321224287
    0x30118200307080601110312190e06070c0210080f0a091502040b0705010b040915090f2a0b0f0f0d0b09091501090c08060415080706020304050a080d0503160302 70
    0x200a036210790300d0b9944101c0c19141c500700042989070303200705808040c0e1003031003d00d00c0020000078503580580080d041409080281082d600580901011007105025150510550716400b0030b1407403541e8000d83d1004401c1601ca5000c80c0c0c0c423482200e29440380003c00d4040364040f0810380011000b180500710021031200d600c19100b040f60b015a0081040340030006807802049028003c001020301d0481d010050790f1219107415081c0410f02c0786074220726654400798420440340e03051482d40301790071618031580b800c001c140700750409000c0c403001030070009a180c0000749281d1400c110b0700c04c0380d0054680c509040841414a020b40c01a0703d807039685988038914910544c4619040ca4841d01c038580003000003c0d10b12411400300c19043e00003400480c203001034010030640180419410100c10745000a02158610105090344603c0c4c1120046026505001400340c4c0e000001e0f20917214211803000c0c20568448403242d40e2000e0b4a81c0d14003244e0180700044a1a40c0034500689406d41403d000d45072206c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 321226771 1250 321225521 321225581
    0x10510050918090c1f0e060d093c030e1210150e10290d090c08070e2403030409090305130914010b0c241b030118 50
    0xc21078004106501200302084a0700e001008003020603204245d00380306103003015008152080b4005500d00800001a034884807170190342c00242c180c2e412213030400140c05500400c011813941aa00b41100000b5102404451500040c04842c7c0580c1910b85c00104c2c4048001e0000f01c0c800740013003140314041d0001448040340d4501801d0710a45140a5618049041c62600d400f0804040d24424a03442d8038601484514811a2039032240703002d400c0d55120708942400f08070303200c1c444c1d84003541d115401c020301e072401c2014940010064804400c180c545590710340807910803080003111070a0310194860030f810404202c15034680b40740d101c0034060324501500c40e82460203a07102c2501c11400244005901603042603c84100c4003e041780010600401248680d0300079105018040c4900c14000007e9409990fa000c01c0542c1541c003080020040307141c13070450b00c0c02000303008580000f40300c11000301c5803036178404440c12681a95510956039501103042420b200040c2100804030703c0c0f200c0e14050b20116009 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 321228021 1250 321226771 321226819
    0x9070507020a0f060320091c0203030a08040204051308030f0402030a020d050d030506120c011101021308010e060a051915050409050f010f1b08061f02030403060b03060105100509 78
    0x455040f5401103d07240c00401011130b225182928404410341165115800c048011602c110f0021612030001000242c0c000304803802501c0b000358184000104d10001c1d13900708000740c0c46079000711000c20170340e81c03004514480380520001c010b00000007000000c4010550850f110b81150018003180e40c9100143d0105060028182d0241c0f481e0f4441c4045c0f0070090741c1400b4039a07021001782e0b070300301901c520140b805542d1681021600c0c180019206004a1a0425410388490400f6041c0070300c078590787c401c0c0a6000708240503402045000d6240004e60b0490b060085a0080c220360450524076440791010000500a5415200b200e10208000180303565640c06138410103401040641004001200c9090031106070004039810107040039003a40c4120002a180c446005243c00d00c0c8050359580320010b058a00201e80c01102c0c00c000369009065694008040c2c02601d00ca6001004018500b101301685c40900340329a60744030b1007000e220ba06051054020307050060018102c035076114081c8a0890745e40c4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 321229271 1250 321228021 321228029
    0x6061b030516051f051003020d06020c01140c07021302090603011505070506180c0108190e0123010812030108030a030e150405010c12060b04050f12030a020d1e020c09070507020a 78
    0x8951110001d440484c3c4145c6400021202003048464550b9000ca8004034403c20050803050380404d041c00040c00a400001ca003141c503020a40702032504090440c0c503900020701c1030b4040e0362101d05421404a26100300c03046928020036440c03d6a1810160300c14400180362140c0401c00140301d15000a5000c00031a40140c1032002c40303e03100800b161241d4034100c001c4040341d04015810742445803008002c460b82e5440180c110020600341e42c68036405000d042840d1103007120040c2056608905608503080506070b030100d070199610044440d00510040c0801c1c02000d69541080180049440c002c1e07011400d40d06195080e1409001084d04044c1843c20031503007510203075150402c0000c80783e440b846007500f295103400c0c1046000d08054000750076000da4012075010740c2d1452840441551481c8518a00820210803a55503544e4907000944401e034041d401d60208194444450401110314a22000c1005a50044c075114034090200801c5910140840e010b01100b08000000f60b110040c0e200050 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 321230521 1250 321229271 321229303
    0xa0909020d1b030b0f0f041b031a01091803120f06090207110f060a020709051008060109060f051032070b0402030c06041a0705011b02010c0306061b03051605 69
    0x3a10b103003000035104c0030040c910b001c1101d41400300000140c82048042d007054010300044c00340ca501c3e0000107441640c030340007e4900500d400f0400d0f480d075a01c4081d00e069809100302130000c02c0c44105003620402d04250300802080144600c207200c03071281ea00294441c00d1003100401c6107991000b5080881e400000d05560414600301c4d40c584905114000740900c54050750400d01c1c0c419640002074a64056002c1c501880d920303803000c2a90400d000d00c0340009403140c20144d03101c1e0359660400c403004142c0703441460301801c0d040714001443e1500c405416400c0c601c039210040716000090502d0b10a8803900072803c800342d5001988503102c08103030040c1c488140300b15800c1081c1c0c24540101460203895030b050500c034103020003042c84620818800c85403c02020b058598560220f0315009015240c0803551810009844d44180c104a505400c02100340d1420b803001c110180d2600d104032543c46410b2010400c120a460304200001d2041c00100300742c1010881c00810f803129540c80c1400c144024030040380c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 321231771 1250 321230521 321230573
    0x9060b0702100206071202031e090a05070503070308030f070c06020a0513360f0516110615130209120d080906040b06010c111206070215060a0909020d 66
    0x314101984264140b29007800240400c0c584814000c0c620a00340e01d0910f945900800421070400da90700b04500100140800031480d45002407071103584040f41d0906580d01c1c80780d880009804d00b000700e96441034079004403926145a0741c421103c0d071240340c0a0040350070811103015000201c0c003070b44060300300c003101690303440c0d0740340071240301c0741842844d603048000c22088040c58070300c0030b90094061500a000c10111440e40e42d92400c440c23001000d0b05204004500d0400c82040140c1074060f04800940b6003648411004090183c120380d13455100721444203122130b42d811042094a07181104050350240c200000d85481c451001084000c40e40030b0030300d81141d00a10b50141c03030603000a21142d006848100900d01441d0070348a41d01c5d02013026003440d05000c080c00014061042e168101e404548000c0c01c407001030100c80348043e940f42011180034005010300080c0300c640e00c0c0150041400740000524240c41c813400c1c580140c000308004a42241e001d032070440e586002034420654000520102620300c00d03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 321233021 1250 321231771 321231773
    0x7020a05120c0c060f0d0e0a0606180c020a020f1516140c0102241003050a03021b031504020f0102012306040c08040206121f08010213090e150702010609060b07 70
    0x498186480b00f4103105003014448034442c80000e000f0340351944200c031310110311641304901c007500740a82c0b07500c090070141c01c00402050340c80308142c01d50450941410100014640000101c0c0c5910b89284000e601050200c98407e042c0b8000e8103001010811180c410b2915071303840e41c40e400c0b080300414200c54a0714109910341c0c54610901a9800032403081c000b92461980010f05103031614250311441e203900507100702045182d4810000302c0055a4041e04580e10746c187c0b8200079540305608405035110f2440c45109041c43e0801040c188401e911a41254580ba140e5600f000b481c0450700c1a072604540da90701c0c4684a01c1562035a02086038082680c043c01801d1203018401602d40040440b011711040105000050f194501180d407035004004c0c0b0606580c940d804004c0202010030a041c0b0300075203030600420503400640c0140b4000c3c800411445100fa0740780e9002d42920841d042d4103034550400103501440405466030107600142c24400040c5942d2a21002d1089808540001c11407000100c4c01c04 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 321234271 1250 321233021 321233023
    0x70b09010e030c06060a060801030b0406020f0f0406020312070306080a0602030c070b040b07020706050a050d0504051f0209011106150d0501200403120e1f0314040305090a09110d0507020a05120c 85
    0x507000d407c4030314180c1d05a40c10358a0700455100083d100401c11940002c1c40303880a0403035000c0d1a1301c0c01c0c2c04036440b65070755500c0500270341e40d810903481080407400303c20206100b680240300311002c489407034000e0400c494007503da880013504014400710040c4420403260b0009044503044030720982c4a41403513111400d00e510000d01d4000117800100c1400002c0080f400da641d0000d01b514462001103402003407036a0f503843d00c6824100c40701c0c00b098201c0b6070340b6900c500c81c0c00c054003c1c29a0107003c3c2d130780b96030303d03564101210f9035103100b0341e8084442d81a0352051074882c180014402c80700341c010300010a410211130344040e4202e40c004020402144041018801c01c5942c40f0142d4201c01d491400c0700903402c440002aa000d40303022020745010b101c01c0d10a50121b40690020f480c0c000a5140001c0daa16040c100603000760300c104050b45c03040c0c50744140031441128501c140d11040340c0001c03030b00341414520500c0800420303010300010254818042c0b0100040e60800c21204c01711002041e05071a0304104002c2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 321235521 1250 321234271 321234289
    0x90303090f0b100e0403020a0b060f0405091e24070504031a07030f05090c01211119020604030503060f06070803250306061209061410030323070b09010e030c0606 71
    0x3c0d81004d81c42040c070010903400118a0b24690700b01c0401c2585403140740010710031201407000c0d907030402d05200802c4080400440c4e1100010180d5401c3c2c2e000d00d810180158484481d00a074081544a074804c502d440c2511204007940002e0324100207203003e840343c131480b401c8110429410404003061041042c0c40c1c0c0d0500602d045106800c070107110720f0a020000649035003034001818100201110898140b02c1c1d0001003010440c0208000c0001c0382140d8003070712490340003601d00c91a144c220a80710400900c00a01d840c03140c0c2e010380e00e0300d007903464078010404401c0d104d010080c2c2c418401d10510001c188028001e40c0242480c520280120150650a0100d581d0039291007050500e414020014a41c01c50307080075603c40e8000001844401901c0d007800145200306128a84400260070041c1f101c102002c00805d4a0081d15103441281c5010b000304001d0307012040044007100d00b803004400048020641c1c6400820203070000c00e85ca01e110070244e00d9a00298035103146984542c2c14400141000300344 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 321236771 1250 321235521 321235529
    0x320030405100203060607060c1404030b010807050303070803010e0421120f0b01021b030a0b09060a06090b1005160803071d040e0607050d110313061d0d03090303090f0b10 75
    0xa42c00c5107003030380001e0700c54047c500b00a440c6030b8403101c00f03030312040c4181d004c0300c0010503200c0c43e946c07034945078102820f40362800d02400701c41d8480e10a0209261a0010075504140da01030031152850b0300700070a2141c0084064011034080c000000c400d0040d1004201d00005101c4a03035840b685410002c0e03110054a07054084070001901c0c200b0587d203142d03400310f00501207203180b403540c030314410300203006c00e182c040d0a840180848402c0310038041d0ba2030011605600400c200c000912150303440340045012166180301d081da0000010b9005e48486002c2c1000d4503020b09030810540c04028151500501e9038400c031986000178000014900c3d00030520395200c910038100b42ca040101d42010100e4990307601340680204140040820140f00c0e41405401c9080c41e11035500d207258803030814000c407001065104100310341d602c1c14000c40c46415001c8003401d400fa405260000d14030300100f003100340d00900f00303075000b82c3c101510b03881c000e40400c03540381100c0406441254200300a10b000c1c0300b80b000441580d00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 321238021 1250 321236771 321236803
    0x105070306030c05011b02030a0602031626180105270303010e011e080d1205060319020103050a0f060f060801060206150609040e0a11010906090501080a0b010320030405 74
    0x30040c000300b40003c2c40c071420750700b082c00c085040c950101c60300800030518400c000c1d45403003000d072442c00704199500614001c01ca00030380712014ac0c010b0241501c0c808031120113250700b10300140c00608080192a2115080340f80ca14540307030300b036101084031420f60300700301e5040780800d17030504000c002040761511320001040858081d505650402540c0451104107203c0c038640340c0304440160129000c286082e8004050000c100d400d07409070020090b0000c00a07c1d40d030b001451415002803000d060108111a43c0c101c003007102d100d038101650040d0300500024160314010307661450355050b0110a4070540c00070b0803054604241c1382e4a4210700600001d0141c01c000210740214044c041000c1d1a03842d1600d8940040310119103665440300414014100003031050302a00c03c8400440600c185904030401404082e43c50205c01c03a01c5d0340301940c80000754418203002400f140002040700e4155400091010310526002c207200c80403040503003030b02100d92040317140b03c0300c00004d01003000300030002078403003107500c0c9 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 321239271 1250 321238021 321238031
    0xd02160609180b0307050307031a0c07030804031812080d0509150c09130501090e0706030506010e0409060e0330010513020c21070c09020310170c0301060b030901050703 74
    0x101c840080107801640003005519220f200c41d0399941400724001405001c3c084030341035036890500b85400c1e0b0b00030601510a5000d81c011038034100d400b00c1201c0c0616007580310304405444a82d001c8030808180080084018a07114001c41e0170850105146102801800e00585a038500900365080394806800b404559200b0310f00c20240501d03459840f540040b10800994640c900e041c0454009940032110401880c0b400c40003060b41c09442d4040400d41c0c400c1c00072609a140c030340030140c0c112642030b214140403c64040481c0391a1070035801c8808040e21910007c1400841034415a00d5900265035221140902c070b110726071401c0e8619403880300480c1242d1100c0041d4900004a01d00700412860700320310310340004070f540060104020030000d84080800c1e0a0f2640114080743d1210381001004696880f05180c002541300b5042c005d80f4000d8950f040701c6403070249855100c00250410070a03405250040201c541000d96080c030840b0000c0c040206140d0b40d80ca01114550b0840b00c00030b00e100c05240c681 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 321240521 1250 321239271 321239279
    0x60a020a140a06050c0406020c0301090c120f0c0e0403080703060b07020d08090a080c040e0309090f100306050a0204050109060f0815041d01060302181608180d02160609 74
    0x2242445903400c01e4004180d0704031807001d54103140707211802a210504050500606642c414000e2048030807650a4070210007498041500780e41d540300000e003010030005002e1050b4410809070050681c82a201419028400e540e9104c02019650040b88070071155001c0006040d000405181d004555203130800c03215003415001c0c0301c00d005500c0301900480150b5480400c011000085850021004111001c2c5c96559160742e03960b0369078507503220701923400c0001c004c03c590400816107070102c60052654070142d55400208050000060064260201a582c0000858801d105440c040c50070200056a601c0c10000054624440d980c0843c0c02c0266016020f060b40750b00022141c2c1102d240c2c103d60541d80d042100050181082040c51030300016a0301c3d4028030408154825070440e80709440c1d00c44448401450f01010000c210390b20002c00403900d5a0300c020720b10840e05258032000c294140c00310003600038810780ca0b041000d041c040c00f41e84482c0000c1a813154010000e40140098604141c4450030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 321241771 1250 321240521 321240523
    0xf0a051806010317071a040615050105091215041a070e06030403230a0c120206061302160804030f110609060417030c0109121202040605040e07030b2d060a02 69
    0x1440054001c0201c4c925515101082d034040303840703c98110000c010205202c51201c840391030f0545088500c24a400303011080c0300c40c03210526045580585840b8206200305040c049680c0030910b0004550048514540042a64059290081c0e00070394a201c4921306074824504081005040001072003c10b07880c00c2c1c96940c6d04003c83c0d0f40980e1515090b0703010b003203400354610100e00359803803c07256002c00b040d69418668420038054405004d081f400c003030584001c90036600c4003400c0e0354058000050f00f503841d865140ca0b070014a444070004049540c90300d035035100c0c0c4505400c590000c46058000032010b1050200d2520400798650003103404030711300314000c0c00181940c032072441103140740354640b030790942481c0b420310075190110452002400f41403078a240681000c02944210310108001040760322034403d02d4401c1c0c03401c2c1ea4154946c1450710b4202100140c44640c024290410191559884c074056122044010740000480c2a580501000310296229900301e8400301d034051017060260412181c0c1c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 321243021 1250 321241771 321241783
    0x140c0102310f1e05030d180f0e2710230709120c0803030403030209100503040206030c030a022a070603090b061c061a09070f0e01080a0b090f0a0518 65
    0x3080c03c080220203090a0b845010340a41c03544079551600600e4400f03001590003404511034141c2c00f10440c0b0400d0b40301c034855030310748003a809010140c104400006a901c8071034501c003080007840c250001440b03540c2d86031a9160864000d040820540ca403008031b06420701060b40b48240078200303420751b20a4540628010f042c0307001791040312403041810300410280b00c07501043d003020b02550b800341d85d82d92130281401b402079803040e000a03003c0c103a080042c0f4150b500c602c064a000d107078028541351541c3c980303030084485074002030041d560304da908005003444284030000c5400c0c04a5502c8801d080318600290490504030b180e0302a4013810306001d9080d0004841030b48980d40500100c40f10f041584c07110000050260424000070306c101c0c5400c004101c00a6112940c9080d00c0044a20a1883d82d03014411252410000e10490114030111040304031903001d400d48603031041501790002220120b0400245050b2001e8483d81d201c42c034940240017402c3c0640c01119400152110348030400d0361002010780d6100 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 321244271 1250 321243021 321243029
    0x81b030c0d1215140a060207080604020607060b06310b04031509080f04030b06010c08030601030b1c0309091d06070e040b061209010f0c0c03140c0102310f 68
    0x11101c9154541c00c0c280b55803049003030b0494100319008550b12802800003c1985075a003d1280020f41c01c0062824400501f01041d2003e001c00740c03d09450307950a0003c103400024048840c02e40701c0c2c401800070380340d0341c02803c0d554000c5440312061b01481702103076030b004204020b40402c01a0b0b9400500450b0519400c64044952110302c4072031585115440c0c4006040400d0700401c05140080d107990641a03000141050301d001d0684941903894101c010341d07009019460041080d0400e0000824560080e40045202d076009407684081092000911070b4600b0258800c40101c0e602c0f0400380845403440c400d10261001800003d941d8070103424200703942e084000c02c040100026602c4421240c0c1721038100e0034442c540900941d4407161507409000d4034410499062649601c0d02307c10031441c812900600c11001159295007100e0242501c04544501040302c0209080e80e0030080130b10500d000340300400c41016a60001c55004541d8250b008018280d00383c00b0014240c40c070b00a200340251140a00219 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 321245521 1250 321244271 321244277
    0x90f050d080715051006090b3610030207030201140103020a031b0503010f0203060108060f06250507031a0a020421030c020315010f081204091e0603081b030c0d 70
    0xd0442c1d00d0021a480345000d140303c0800d041009000708002044044401d41e40ca035200e1345541c50320752210f0042030040200c44455168282c0d00c106901c440208200192000c3c000d0050083c0102c801054104a20544c4030700001d50008116043c0740d070a00c550032014000341d200180c0755145800242c014010f0307002c007812040c110f6400d405a0050000c00c0c100500d4054000d00c03480c0c07000c0083d88002c2d0821205580428100310000b1018a840c8010700c40d2040000e1065007008442040400d602d1040306d00440c041090141240106074108807450083d03100f84c104814a108113240c0a007c4c01000d00184042801448244010071100301c540380700da0051001208841024201286c0d45030b035503800a5018085d10428090303084040000c00c0c1aa100251349040181e62800c141e913442c240140002405a010300060140c2045a000000c142d10200b51841c0e10301300001c2d00c0d004459499104548260000440000346012100c4d100d00b010000000745003812140c00c02103072180041c41b403000c10 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 321246771 1250 321245521 321245527
    0x50906030a180b042909070603051e0a020c01240302040b06041517070c020901050603040204091a06010e09090c1306090c0c11060310060c0f060c0f090f050d08 70
    0x3908814a00c2c0c000c129402002100242c1801e04100c004401c1007008481e10548001e4854071017480c0480450113041a00000c19946142c1101280245000341c14010844031001e02d560b240c181e07042c1d4003402140003200c01680c1d9001a09514215001e13002008805d280590720f00d0048070014048804503a0140d0700441c1145183d000a40da030b1081c0d41101c8000c1011900300b40529500110b40b585100e07091810b40d140d5101c1d42d10075640e032040f0300f074001d610542920040c400e03410010080d580080c0702a002003468a01550b41070b0542c4460035104440e031500404000700c1c1d60703000031071010240c0d0030f540b0488039080280c2d002d500c0d030003a1641c031802211311000200f1035107240e43c09040100201c640c00c1060a560880003000c1c04548101922292441604d4207800c3c5024002c0300d0040700c042d02402c40183c5402403d48000e04a8402964844070004103000031801c0da0040000301341407a92140951100300b0009003904610303800c808407401c0715039014800ca44645102208290300004c0c041e407 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 321248021 1250 321246771 321246791
    0x40504030c0b1b030c0307020c011107030318050a0602100c0c150e100204142403011205010207120306170a0302070618150e10050903031b0102130b040f06050906030a 73
    0x200b00103c0941ca45400e550000c200404007070306002842c0240e5aa07400d94954590072001194002e0303101c3c074101c400b0b8000d42c404100003402814040310011650b164090465a1100095110300c155440700700907800c01c640030b60440320039124401403583c4500b400c0c0040441911050420094882d120350f400303546a003404c4800c07504200c60200c0d00080c43c015036869441e082d902d101d40b900355a6443c05404074200d889141c1d1070f1118a0700d00800d40380100c0341140c2c43e1100c1030000303c9005801b96000d55080140c0c0b00462800da840f00c0c00d0b00629200801c403c0d142c9000c100340c081c5060914645904061600c0700000d40c0881d4000c126501c500e04000003681e2019070041e09881940b1142c003c5691081c1018566041840040040000c40309001c0c4064241c0080e0344600c1003c1e403ca40c5030308200500003241700c1d00e1841d0a0300400c0c0000040c14580202c00042c0c0482e801d4201100c000390129041000c2c03c4000a0000500001d1034002d0402c44500041160390202030b03c0c0004d0f01351540b070480 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 321249271 1250 321248021 321248041
    0x307020309010531050a08030304020d020114070b04051605040207020a06050906040f1502150f011a07050105090105090c0103090f02040902040b091f06090e0403030f0b032406040504030c0b 83
    0x1a00c0032504200c000403000d00d100c004c4200226501c60342d400746e21010300001d040e85010050300c1c4138640140c900b100c0340010b640111580000710440c049000810310640300842d06880000784550720038001402c80c10081400e0380a054560380c0700764440e6004001d1440140c0382d00d1317907800031680345041440d140c0d8980300009209002e107402aa413900b00004c0c00007032000d0320150199000e03c1d580c00b580d07030403404440719070940301d0304483d110705008910004120074094030351a61340d180c1c03103002400e0034800103503a41403d68005403072203025a9140c03c10b203e01746100340000d0100711003d00f01000000801e42e248402c900b50094040c0c4950b6903043e5200964495402818002000a0915084d8600030b004660b02e51070344480032008521035035020410501440340b0b90107075203001421154507600e0355811001ba2070400c24600c50799403520051000c5843c10032038540302c0000c00e8000c0d04d1105000c04501150640240141d115905040511020a13040b901140985401011843c602d0399416850 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 321250521 1250 321249271 321249307
    0x50d050a0618060509010f03050304031202190f0308010e071b1401020c0304180504030804140c09070905012d050c1c030905011506020c0f0f06030c04081203070203090105 75
    0x2a02d650703030a648540041042c951003101600e500700c50702c000701d9888440c0c4420089480c0801071656204110520204a513450b180b941020326204a5010210f800e50075151003031000702c100d6458a01040c40d42c00c050700070035610301501010f0340c01102403811510040013011000d04140d03501040b0b640180501900800600143d04400c00035036a81d154002072544d42c4d44075108e246040304800031b000362100c002c4d0081600841e05507840031216141d507103900d550080303140041403544c407512125061607200d04003124843d001c0c40d151040c078140b5000c005030642c031402d0070482c2910110071803084000d031600d100f110845032500d8030756100d080c145204d81c504251056102c4103000100c00d402d60746079268101c00b04c4984180e00034041c48070342014076400312000303005103400b6804c401e40380942401c01e02d41c0440c480000070f00780c4140c000d0301c10104010340d0007560a05040000060b040c0301000f420031264020350f207101040c6207545081e410013034490095852144c1002400903164401d44404509 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 321251771 1250 321250521 321250529
    0x2d0a080609060708011413020a0507020a060807023702030709060b0315010203070f06110715090519080d09080c0f0d020708030a1e05040305150103110f01050d050a06 73
    0x300c03002400c107012480e40e124000c0301d500d8001035210001250041460f00d0000b091540034240d4408104081002d8000e5000031100b27104005040c00840701507500e20700c0c0301005081e140c84240d06400c00620081c10800340f090032004600340842c400141d98110403031a10791580141c420340e0510317010b10010342800303001d82c8004040c41c00e013030011900640030401540104843d2000344446540315006903183e0180b10b4000c0e10254070721003140c01103200b6400481c11240d03165101b0307252404503520280e60b03118001c40d9042403170b0384800010030041e080003142d008030511000018004030340c2e690340d0440c0c801d811459410680380d00e407030303810810800306035a0800f44250503200c07010a010a40e0f41e4600b0380171007200043c4662000043c1c0200301000f10740c402d007800d980c0c05484c03012084139a10456103105000081080402002011400a002d0b04101e943c1d1004410403d515508090071741d401c0070000075204200c4100701c0100760780c0000485010071700881e80805c2039554540190001c0c400313544 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 321253021 1250 321251771 321251773
    0x8041412060f090c040e0c1203090a0305100509030708070305070201090e01030503071a06010f030b060906031e01061e0e03010e061306140402180c070c090212062d0a08 74
    0xb44040500c031060010300c11002c200c00c0352088006042000242c076408540740070b282d004481901d80b5030030080e03400111842c80c0c004491034045004041401000589e10583d069081900a83d80d085a42c0c0601600482003000540c180500380c4c0b1140038078407030503c001b008e04c04002185c004590040e24000001c02848120320401d680d6800c0054507640080f400700c4106d190070b03001070006c2c0014100c0a00400301070303683c141d100401c407000341d0041603c1e9601aa01050611036400f803960f500004600c210502c101c18240d4240c8119004000c10043e003142c3d06000008400340b82c0c003103200b0309404a21b0024504115166903500c01f090060126015420060043c40204500540744109180380e40f441140104241500700c40244a1403c058034000c1d4000a400104403128541c00249a0405800d1012600e4006155a095140e412550140e03055036008a072402c010080e05400d03660000c805c9da14818140b800f000502a0741401c5070100742a010f100c8120882501e0b41c3d58444054001c0b50 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 321254271 1250 321253021 321253033
    0x40803121008070303090905070309050c060904020409060b0a1202120703111c150801110a1107090218130903091e050d110901060507121b020d0b090706050708041412 73
    0xc1001086da10984c0174501100d824500400d04c003501c284201c1c041282c000c000341c110030300311008000c1c0c03943c42008402d41c00f075000e0001041004807885500c0051039224a0359903142003010b405003101900c106207280052041c404c2c50100c110030460340d5800035581c50b0010741c1420390501594203010390038006101c1201d6400c045481a1113a0040c0d0b1803030300c01066600c529550352141130907280946801e840080e030a0081401d0340707001b915165150b0344080d00f40d81071291a0708420381280c1103040078016480e02c509031a0a241010b0b180c0301d00000c0350401c24800c004540d100502001030600ca40c00b10014409420701809140385802800340030b0080030304c0005140c83c1440c140300032501c14000e100b401c0e4603000181030780c01030b8112802140c1c44100c42000045d00c1100b0740d41065001e15035a00140b03688030640c0180d60b19580038101382e102d07004803d0740d400c3c0380c00207514080603504100140541000f500c004102c200040e03030102c503070303150b00042002e881c0008034414180034030100c8a2486a4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 321255521 1250 321254271 321254273
    0x30c0403060f06030606051002031218060415060b161407120c05040c051e0904060e07020a03020105060603071205041b0314010f05070c030e01020a05030c010209040609020408031210080703 83
    0xd60083c10480b80140c50a110050303c0d078003040904071140700004050713401000003c034141c450a503142c0e44040110710800e00800040096414004d040300d08490b4190072600301c0861907100d00c244000780c0100c0c811242401740d03040c040d0007841c81040014040441d62108860041010443c81d00a0408074909022444071884d0007101c242c1c9a0160340d21817400c2c0030303400e14514422400da43e103a00d0300d440c00101e518455140391109501488180e50001d0315007501160141c500c00500d030003141c16a000b07000100c01400c000317003100e4018184a00c60320f03040080c4000a50300002c3d03030005e180caa90001420352110301e04440d011460015816403003041200001c01d12040d40401c4c1513405440c0024040d414400c01402c3c1125003c0300e108020400d50701c5403030003103072203503040526103a418011107828440a440305441e41d04042d68a48003a0b40010f20007a4a00381405000000d10708031800f581414100600641c60340100107032010000824800078074000c2c00300e80c89200410480f070a0300d02050310303 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 321256771 1250 321255521 321255551
    0x180906110a1112070b0a0608030412030f0306030305270306090718020301180e0309030f0606010908060c0a180f0602060103110111070311220e0d0207081002030c040306 74
    0x841d000c8140400c2d4076003801d90490401241d1070300c1d00e0b04600e410b645008810390300c1a101d4500500914581c0b541c580000ca00360004000503c0601403a20686c10408560b240040031981d0000d410000c1504140c41040000d80050540303e80070416031161013003c0382c0001e014002c106849007240d0520544090048805e0017050381b106560444040c100303001800320316041a844284500e0082602c102309099901429502100d05075580c0400e60749010a0000003a00d420600c20508030590000c1d41402491368000161400400440c4060611031802c0810058a806501210400c2c00a02c008001161001e840348001810b40a03225030600350700c914009540700380034002103078070503030f0305010101d1907014450044d4a6102c030801020410700f142e8980c010103411485982d0046918140040442036000c0000c022460101c1d0000b1450200781d011403500f801001d0b15401c0d5000b145082c80780c1d000104560400300c0410f4400340c0c1d2512500da40c1d1409100382c0c0c0c805001646800001302c40005 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 321258021 1250 321256771 321256777
    0x3090901090b0102250f21110112051005040b0a050904060b030a0f0503030103050613080a121d03030907060c05030a08130c24030b06090114090d080406031a0a18090611 74
    0x1d1b040e005941070752903500d030040340d00c6c0219040091b40f02d0204040c1c0010001040300c2420b14043c9410070000016244850580304107941e041003c01b0511030500c100c1c14076200301111410100c0e036648440d072130500841d440100142000d00110740b40c1e00b00143c40d0f00e04010000e400b962060100050722850705040d0b450340c00c207010840b81e50040d940461240e00700107100c5500700c2c1c0c106011516040e14400142c9400c500312080000310707511107203021081c1c031008100c6003100c40304030051760f5a072030140f041c1818090141c00c003c00b03020f1542004c07008104004251403040c0c0c40342c00c0c21000d50700c4a4449007003680741044001c0a40340400030100c0c445001c5c006501070b0300b944c42100882c01a42d0b81094003030703403805100250042802d00010381d41c0c2d84a83c0d041d8461010806e00c0754504035184010412403d4030782000d5400e484002020030169515108944010401c40d4402c4071180311400010618401840340c81944500500c140c8210509a031040d100701e40e102c03100b0030580211030000300d00e43d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 321259271 1250 321258021 321258029
    0xd0905090405032511031f0213090f1a0402030f011a0f070c0602010e121903090203030f070201230703030507031b0206060f1f05030c0c0607080f060303090901090b010225 75
    0x200c1701c121041c01e0000d035083c4071001c0c1c2080440d00c1204100460020f4015180a040c581e0a1031000104441c3c24402c20009040c100000b1402400b54038501c1c08880800c54194042c0b40704104001140991611060540340107101000c0b1055040d400c92105004001d0800040540040c108041000c0041c1d054111078550f002031064001400700140c480c007207940c5000d1101c03400c00c84c00010040205e04125000250f05001800710a00d80100c1c2c81d5401000548500c1900083c440041d9a04544040040070300c1b001424003081d01180400c85c0c0d4010720344024281500c603408119258000c0e00034010711440ba0140c540c0005141c04025500d58095a8060291a0139000241e45042c800001500346407044110380104122010840300b641c4002e142051125050080780d40484042c40317410700804440d90707107600794241100e005105180141c07900d80301e644100000c54840d114810090304540c030031100050908d44410043c0e040040b007031a030351044403c00b440a0030f0550403d0044082d2 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 321260521 1250 321259271 321259283
    0xa051c05190507140306220c0201060b040b1806090d0b0a0f090203032a030f03060a050a030209060405040c050a09091209030203061603110c010e010b030d09050904050325 75
    0x8059110308030440b10152400b500103600902541c1e00134941c100110781014010302248070100c255070001e65181c1d240940c02c0c0c44161280d0001280c01c1e424040ea0307000e0304400c0519850b0501c0c00e8440c52441c031540d88110144070019035029101d0381d40006649031104054510410715400e484c20b0401c1540403929403140c05d2404041c0140218144690405c955014001b9403a280b801680c00040d003048038000a21600c5002205151a03424400b41c1009c00e2410304613504c9080a004114040704290003c0740100342141041000d60f6800181c83d40290040c1c2d4000f4481e16039090690204400303401052f080603140100044040165200e0014130f8058110a1071142100d40c08940c11740d01c600c006941a800340d800705230782c950407c1e041e10f00c0a5060400055200840c50000f1007a0802c54080e40941d40d282407051030a9002c0c010101440800c41c060950030701042c4001c0c0515030507000f961301420003000000e0402408008440c80001c030007d411040c000300040c100502c5258240840303003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 321261771 1250 321260521 321260551
    0x260403030c0b0c0406050d0b24070c0506070c2d0b09090a050408121504060906050108070c08181305090303010303091703030a0e0a060c12240b0a051c05 67
    0x90114100a80f070581d80c0360307036500746051404108500500f100b55031481e800880403420f8416203404034020090144149c0300c29071240b245040c0042d42100c56400903014010030440140042c0c003010301c801c1915411490074850401d00c6002c03043d0810001030290200e00c0701240032500400180190000f89012161030482d030b524088480181c0d04192001044820240502c1e08840f08408002d40c0c02040150306148070624a070000c3c0951b50994041420113030307076032420321036560700407904c0e50b0008490400491450300c0756600915485400c042840e031489030500c2d12038594402035009480c00d00d4203411720881c10940341c1d40342c5960081c0b0045020803d00303400050403620f441d000c00d03c040c1e5a18091825640d0701801200034120070502624240685043c010001d00f161040c0208080039951300050f001c0c3d5002e059086402030f02c901d40825010740c440d99a400803407420381c420340301101d8000d515a6074a10043d603550180340c0740c00303082d4114003120112020840e44a948201010443d001e1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 321263021 1250 321261771 321261781
    0xf23090c0301020f0a030b061e3402040510090908090a08160902090f03030703090801050a0b030c120a08040b0c07060302030121110307060216140904260403030c0b 72
    0x100b00e1080c0800d000480300c1c02e10580d40a00d000358403088007e80090880c902c2c18428484070f04050911a1030100c0450000c95503c0d002032011070130048580701d0000201560101003010740c1c100e2940c3c0700c0244140d4071600000d03141c0f0500505100141070503001405203002c0b034034204080d038000849880c051035803c0000074000f18005210307141d220003812a15a12818a810340c8042d5100c5046140c00107800c0415200300e071010002411014080d544034510b05003491001c5007956806801c10b8422420404035000d0b0f07580c0402c2c02e410b1480e0858a01e12001c0034041c000e810030414010240680501180004402000760300601c1400c1022065400307680d180c0d10198120300081c080c2041501640010451441d0441c01c803000d014001c0c0030810000d140340b40042d01c0d004860300118010f070004505800c684041d008050043d0903408203004002d8010400300e141158020706c060715040303a00720800901400c02e82d28454190302440026a1541c032418043c040001000c400c4440d480ca50700020 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 321264271 1250 321263021 321263023
    0xd050102090906091006030c0c0f11090a0b0a061b08040608150d0b2409130204150501050915040312080f0a2c01020f040e06090903070201050a030f23090c03 69
    0x76114806500c11080c243d130030700306d00320000c0140011001c2402411001e1601290521f400014200d2088c689903030400040d809104500b200a841c1155190030006404071a98403458194251252440c00180780c4500c000c206059400784a00038042c0400040c000c600c0f00c0d40020440d01c1224000402181c0c2200d2100f40b0030f20000a400148c1428591f00214080c103128070700d00040010f03440c2c22184030031441c000145181c48240ca00740503410b980604181141094018014600c0e0503840c3c00f54010724020000e012841aa80c105114942c0145000c580a040c00c2c2518051070300410300941c100b421402c0541605420748041c01683e6200e000641d050340e190103017445040300c504540902210201041401d0413041d000011700e95002c3c803003048103081c503101034001880143e4ac28089410300c082809074000001d040d0380c0c00354004200100140c0d0300803048400034041d81c40c1c00100d410040070198000d0040400c1141e1030120350407000403990800e516240101400815141921204801c00d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 321265521 1250 321264271 321264289
    0x5070806040c1710110a02070b07020a14060c010603030e01110d020735030712020a030207050d020d0b0a090b060321030c0c030301080a0b01060c150b030c0d050102090906 75
    0x2080c40c60000c0d024082011000c0f140301c1103850940488401d84c02e4038406109070b401d0860441c0c60028003058601260741d04000000003400c1c1c2e80e690b98640720480d00402e5190700341e030082c8210720311103c2141640b0344480c021500002c0c1e1000c005c114694403460020f0845200d402840d0000d41600d105049148000c503003448402420f8000300031613460210301c000c82200d1481c20100d860b0603a0045400b240c009151091a250701c140659a0717a140340c9407286a2180250140085620018072000003940004004058640403180a042c0012504c0002c0814214240050030111000d06100204115800011300980710f030342540d509961740f4003410358858441c01044500902c2c1485102c1c5030940600864016000d109034500d0140d44100e4140b46a00c01e81c46200c080c0d111420681c14000303240c101d1303409410f00e40307410041030409445070301d00c1c990003051001c960365550f000c0030096034041100c0001c0c90009000301d69261882c2c20024002e4100c500c1070b900402c0100700155061411481d1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 321266771 1250 321265521 321265523
    0xf08090a020111030c030a0201061d0702151003060207110a0e10050d151803020d090506041e150e120d140a0c0209040605071101061511030904090b040507080604 71
    0x10009030035150011114203810201c5000c0c40c0c0020050400c80385414030003881980d2481e000811380600d020b8114000e24013081c02d14091406403000d00c41842e501180f50302140d6035508100354203440e034007280840e1100303540c00107144c00c0c40010762008100404981039030100d001c5462403c0d0a50312088107505441c103c07000100308007404c0061100745410109404d01d54043c45440c540003aa01c602c000840303440740d107204400d10000301e01104140d03040081c0242e480c402d1070b0984200381782101241e103a0003240a50040301958115807181030804d822454000c0c296243c07018401c020301c060141c100d0f0042030f035080c042c81100d60b4a6042e0200040e900c0d0300d074800380c0d440581441101110034800c0d000b20591030b0030010540d41c0301c1f025075a940c0c4003e024034016680010a0300303183c0740180c03100324089000700559040107010048410300740f034205002401030501d03080c0c061405807880d0840c45a98445d81c1d00c18504020003041c440740c09129803090b44078000f1200321726200c00c2016a940b0f4205d030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 321268021 1250 321266771 321266773
    0x7030c05061605060f04120507210c06050c04050a080601120b090a0c08030a030506030d09181503050c040c1d13110304120815130b03031b0d0f0809 65
    0xc000e642005802000000d910012048046260ba500c40d030511506440c8105a54880c40c240b005105842125555004040c2400c525198081d55500d002809070b402c808000030201400348111400384003540415076001400704201e1a001c10081c820350040d010b864000c0415410105801c1400500907042e600311a03e1080011061354603142d44650003412a081ca00500368140c0014402e04031600140c1050707000b5646580030101e004040700c0003b416240301e03500c11141c40042030781004840c8203a4a001400985030841089000c0285c0403a00c44400f170301480410000602402184245a1701800c440900c2043d00e10541252110fa203031000b180d00900e002c2e0141c08900d090412203400c42e0b08903002046100c060b030320814050304201d40030b6070702c0c07892006242c42da181d000100799442861000100d4240d030825020030800c031280b82c50302940980d139290602090358100103882000d0030340d106800d1000800100c40751260b008082e64008a18820021070340240a005030301d1103000c00130 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 321269271 1250 321268021 321268043
    0x708011a1017010803040519210521030105090a020a091e03020d06090606060306120308180a080c0f011b080402040b0411120105150304290a0b09090703 67
    0x28100501d01c0e105560038401e008100c00c0d140500c03440c140219000380481c801454a036442c03c4180241803500409154031464001e509000487c504070300f5024401002c4e40208050b5901d00d0058034102d00014048a5907410703070514080154000c00070742c16540c00703454044c20340c3c40380040350040c1c1c00740e60b04520114011107424440b500811030044240d110030b240d80c002c041d5490f00810102ca030400c80a65401d83c541902100740a41400390703600a240030300e01000541e140c03a143e032000c5044414020f040110220110f410001e8200000065080041c20347e00f0000c95440d04151990108031080150f01a0126800d202c01e418443c08450941c11411882c0194400c0c508841c1c04e54002c01c100d91044d60f90200315159101c0d40308450303c4680700b100207680c1d00c105110440403410140d001f01c2c859000384580c3d000880d80101505d400c1540429070f4064541402c080071502c403866005404000b00d03e0040003140030840c0c2164104c0d640550f408281c58551410054030f410b101e010286c4500544 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 321270521 1250 321269271 321269321
    0xf040506090609130614070e010c02060904110409020a051314030601052b1101021006031a0705040e1f140109030b0702070b0409060f0b07260f03130302070801 70
    0x1018244d61048400784040080701250361944103ca8141d501181e805620300f007044103042e00500b00d5481c041003420500700c10015030780040d04030301c134024695018039100c10001800c0001001514082c101080065480e0f0100600040141d00104400754550b0030b04500000c0d901404540c51034a01c0b070140c0a81816821303e01845070310305a2403d200d000068005000a80c107140f5940a4a0709200304010000c1104403000245400034010f80e4210003484e008003040040c0a0810441d011501c0d8140320480b40d030340c224140da0a0003944d1085c0701c1c0948030700401c2501c1d608503695031181d0310f40a501d5156542c40b13552042241900007074241c08911503180600104001c0f64a00b94003000510440740c1468540090010b1508150700c000669a2201424403203e00c03141e0f0144040d05130069500d0038030216445058200448411700218814980c00c1c2c0b04180011344200c4180048030a4800d60380c3c2080990b40e41c5120641006600500400d180420030607018043c0d01001d40c01e00c4c5404031301001e0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 321271771 1250 321270521 321270529
    0x503030105040510030615061d061e1905030405060a0501030803042a0905090d0f0f051e121501050f181903080c0d0903020a0e070e0a12020f0405060906 67
    0xd4850003039034020442c000001a540c7c0524500100c040c40c0c1d012045150040140000741e00703580902511500030800911900da00e0705841d40d48440b041c02e02d0410003011880d150b80e10880ba0078600044806122010564020f030096001e54410402c40e8501ea40700c0704020201e03402800000c2c0300c001e04101080c00b1402800341d0024421641040490007030510b094440902a59800b0324a0503445904100d4045024070205a83c400f0340d003045214058407172401080c4a510705914002d115000c0b40400c040032102c203210a6084c4102c844555546400303185850030b4004440700424107201a00c080d1184d4420b0003170300c0882c404180128200b80c02c043c200b80c61114054260b5401180a60207840d04083d2200600001c40c0500465542c550405105d00d041009211403c024021601d00400050b200c0302d041004440e0015400c80080d120203c084171034001081342198413a0f0200d801140c400900410710300c0c120b208a8480040304801420300054807000c807050390780300d000d0500203002030030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 321273021 1250 321271771 321271781
    0x4081504031d0112021305040501140909010e03120703020d18020f0a1809020f060a0306030212060f0403050c1609020c0d140d0e0f0d0903030e010c12030f020702090108061f03050303010504 83
    0x308140c41010345904c60002c40e0840e913092f0320400c0c2004940c491100c1e941412580182c109020070000d116014602d44d215903244a004501140d01c1039900010359100c1c4258199802c0d844500018030248003a010742c1a1901c4400f00180c2c856590314a1404e80c41c585003100c2403c903030242080d148486595800d0500600c0e44520030790b0014051401d06004ac1d95901c01407c40340100e46000920034218010b0020f000000090081164481030038445c1036240e401d61140d11036410f241041d52440d034840300c141812804c040f05c030602c07800d2500201d9450243e8015120902d07200c4d045456280750b101089901d020410703a03030b0f01020020014603010f400300d0f170000c0300100e01c1c100450b0a000141c9074114500610f04030300900161992030140101540400c000e0000c0c0024a404035070340c000c42c0ca559100c0307040c1c0f141c6482031541d0707540502400825034040c0c48003250000c02c034241c4c5607036030100d55484040858014030003201042841c2010324074a1180381c1501d4210f00114116800c000600c8000c007 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 321274271 1250 321273021 321273037
    0x90117072007030507032307080312070e12012406120209030102071b0317120a0b1201020a1709010207050a060c050d1b1205071b020604081504031d011202 68
    0x100440340b020000c0340d4100801c0c0d006500c5040c01101c0d6103403200a180400e410f0303040c080816001001c00b0884807030000159840c100003c04d605001313880d01038084d03c0d5640c28500550b041440743c240c280c00913906500000c003180c4103541e43c1407000c48440410361550340c00e024900100d22400030012400b60180c1c00381c4419000a4001840c2071990b40b194690161015100b0002c1d034121201441003140141900e00c210018030451070500c0103820300c42d0203c4400401e070300c054a80e1601241aa40d648190207147c0a84030f10003103544502c1401c000700091010f01e440542c0290090206141003014801c481203a0741101c080c195040f010b070748100c09060640b10110404c9418490a07224484510510741042c13611001101c80ca400c08001604502d0f00d03081103003034186000304205200340c1017841900c00300c4440c0d00c51100300c0128030029000703008a4001da41c0c24442c0340806000b02c0b1b190780509000f903020752144440415020726070303200c05100f0491140002d8103488020030155160300a07081070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 321275521 1250 321274271 321274273
    0x1060b0a050c0c0d0c1503111b071505040f050a0803070312152c0c0406051c06030c08070b04030302120c011808031e0606091c12050901170720 63
    0x441c0080f0000b905006820020307100059000010020030b509400256018240e60405114035000c6403040d04160044401102408269001034001d6040c00d02180b00640714040d1041884e607504840145140c01ca80111400d0000302d5001060604c0e00540c500100d540031b40c001d46c5070400a0380d080755503810310562003446070784909100304080818580000030b00f9402c0c0204254440d030b0100c601c0042803000a440c00011200280100200008201c8054440c50300789582d40d041e07180401840385ca80e5144100b4000d28090000c802c000403410f1400c01c9855401c111800300c1d0303c644450702c480c8114400100968800910402c3e4114100044d0204001620000075121158010400101481207048078041000000c20103c0c1c0e40e003c4803107080c02600448400b035407a011020903014846c41e4030b8180314000c1014030318134840810050400c03c65200b150420440001d25000e400c2ea0010340c80070780810310750040711409103600b0025034440c20bc540e540b0b4904d9101071900c13295103000d441341c070405 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 321276771 1250 321275521 321275533
    0x207021215040c0504021606181e0506180709050c0d020d290f0f150406030b010806090601081906150e03010b090f040305031005040e0109060506010201060b0a050c 72
    0x2010209200c0e51059a250018000c9075140030b281012903510365400c864403813403042c480b0a01c80f00c200d80b1118411540072038000f580945401c07100184100801c0001c00e20021040d00d181d0900041001c050b140b445041140e0007910742244142c00c0f83c03038042c020328417980000c00401c01d100d11600016000b901d440d07a02480c24030480c15400c1668132a1401102c00341d15074002000c4a04007180781a007104d81034000c9001c05001e400020400040010001c0c4a5401480e4500241d50b030000781c0c00692400c09940756a503965810b014000c0c0c10a02801c50204007148001689402c000901c80e100d018140d4555029945501c040c1495901c50164240340c0b170340d100008941c40c10340540403c01d02c04191039090030302001008040c20340c0c0e04000110b00031107a25083c071060050321500b550b0401d0b41428515100e030f446600d001c5207038405a02046d4030604200c07020b8171040041d4008901ca0307008803c20301540e900c440c016800d0f200d03980b150300c803000000c0141e050014810340140544070648016500707 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 321278021 1250 321276771 321276799
    0xb030402131b050d0b180a0f1806020901020706020f150a0204080a1212050105061b0f0723060a090b2809170d0e010c0201050408010c08010509090105061507020303121906060311030703020702 84
    0x109e80001d9031070448416900159000056804214080c003d101e980f0040c4020307207500340c8560301c1d01d8240a488134101c50810103c0d61030a50f0381c05880151028000b1a109945035091414000b1100c55400700480c82d0440e00040c05a0140503081c1a60400344c035040c0340007070040301138a00307042c007017a010154010914440080c120600c900c900522804440704800c00040460890f6200c0102083c2c0c86080c08000c048080e940200c1490111541c80744100d4940c00c030046c2c2d640c4880009801113400458a48004d012aa04a01c40d0382c10340d07140c89003407207103407a103801e8195a600780c0744103a05c04202e0311115141198803640303181e00d1540c4107151450910b0b90359186242506e000d07034180d0340440c14410050003d401c0608146502c0100300000b841181080004509140b520400ba5a2140d00000315041551010412a80401c51110150f03590f840c0851001001c0d6103003185108038141000310004405200740100d071003003181c04030818513648480d40c055000354004881280c0040407007407940 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 321279271 1250 321278021 321278051
    0xf14060a0509220e0610030b13240b010c150b010c0b0c07050c0d0b0606090406150e03070506490e010609060b030402131b050d0b180a0f 60
    0xd000c00800d0b80c40c0d00d1050901c0d907820f006803000e0b420100b120b070703010004000c0c4140100302200e04807900306d40a09116114900070102c0c0103a1800302800800460500c80200a1890801c03403410f802070504001000d444001101c550071640c40140583c0c4c1481c07250440c0c6005079101c0c000c940414140440d03940710541d87d480c0c03040c1c0202c1e000c00c3e03001804070b401420710106100d080d1107924103c40008824520b40d0702e1000c19440902403900400021500840e541c585a20900181141d800403140c10f41c0c170351000810390203a20307000d640a40102000058507003030a00a13508007103450020580c07412800c403040100c460b5103888809034000c0040210420000d480700c041c0402881d0342d03010400b0300a841401c0d0035146140e0249480741e14140301008204410b00641c0e8020b030b411121010800c1489413200c0141641841c22150b61440070441c25000e5000340060040c10034001c0240100307500343c000c101b007a0014080c140c90403088480000d55100566110302000c150168000a20b02c00701034503c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 321280521 1250 321279271 321279289
    0x1b0f0d12051909030203060708090303070e030c0901080a050f1f0b030102160c0306060506031506131e050316150c031202040605120f06061606060314160f14060a0509 73
    0xb00042a1582801d0041d0b042c1880981e90000d80c0d0b041c00b40c0f8130305280303074103c0d81c0b0320008000340d080104424000c1c610b50b034180080d400e208001040c2e00c6895031545100c646540280204540504c1422078401d041c0402141c81c00524041c00e00c1c02100044110000d4058581c80c141d040e41554204000541d00e100d4400688901c0c4c0101c3e8a5660035086140280880340581c20907885000d0600070006103685485293b04a514107489454071403d05c81e9259041d417180303030401100d5540b50a84001e41c14210710309803007112021012203100b50b00e08141c0350141003e90141c2020b00c014200ca600d19240202d0010035000c0c42441c0030314020311610340e004226003094016000041000502c007030103140854640e81c108481c10b242000505081002515600c6048282c280c0104219401000c1c04002d6028000070750b08020030801a940d00c52826407035405101c0c841c002604102004101c000c1d90003080403e4900c200b4460f401030246008000c000d401c00e00c00c3c002080b90802100d021515281e0308 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 321281771 1250 321280521 321280567
    0x71b020109080303010603052a0706020a120504050c01031d1e030c07080724121805060112021030061e080f01110405090618091b0f0d1205 61
    0x41030f0500b0041c0648007046085000b09d0800042e5140400255000c2201c543ca544100c0050340c900c980c102c10307900c0c1c0130241d141910382d40c50442013005000c40403850140143e001d0ba810440a059540300d81c9004104100e0036000c1c2d030082101d5940c0d00b00201203280210000c00449040502c82d11030390380b034189607400035195a0000c403010454420307009607003200086100340d251019002000020940002520111945501e5500501015031600e80307084015801406503462076031150b0382d1038070f261800003007240158811a9080307d0980306408038505800018044929034101908054810507142c4000002560b00c460000e10340480245040240c40e800400d00b042901c0c1420080c01c00c9050140810564104188000113044080407141a10811103018101c1e48815001c034484400518550411104840500c503d89000080c050fa40354006004c418a01c00c0502c01e005c4440c11400d14103400001d2401071000040031881001c800070301c1841d10605154811a6000c1d00f204001d003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 321283021 1250 321281771 321281777
    0x11070303030c0219080d0c090f0603140c04030c0e060a0e1807060306050a05011220180409020f0103090611160506010f03030917030f04031a0708071b0201090803030106 74
    0x100210b02580c040c07001074843e42e0204903406100c0910340752071000d4481e1102501c103140d40c0b800300102c3c2c18007074461000a0452028003004058031007c014005102e05c2e000742d20941c80020014054158980441c0c054a0307003c51390300c440b80d15000b804c0c810b1490107444687d001c1c1c0466404552102003041242c45808600101c0c1d18580d10b00025078184196a0070502c00c06041850078030540d201c4a034001d040320b40c03e103811030340d0180d5139803118002e104c501d00a4002c41c0450100602c404034040203030540d130a0350600e400981d6400c50030401214880f40f0020740200305e1004c81443ea40c065440201003501818010545c859041d00c800c0043c0d01003000f410003200000542018048200003ea0141503201c114251040c250f0300c02070036459842c0300b016403220034449e160002d080c0910070745000150403c0c0e40c94a4681300e151003004a040720708498490340d414400188228403507846d00340540070301d0716032140b0351b08558150103409a0341d007000c0e030610000440000d5145010402103000b440159 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 321284271 1250 321283021 321283031
    0x100828021902060f01050d0303020705010612210207061409090f0702010606020a08030a050903130f090b03010b0f04021e07050d173702070b15190e071107030303 71
    0x2008010a00c0d040001c0104540c000e2080000c00c840d40381c146819110104c2d20224103141c41c0c60118017911840034024200e500780400096800030708000046483e00c94140721036440c075000c005c0083d4001d81040007006038009201084200e0003442a08e010044108075140f819161801044100001b640c00c01d4601003000204200241d080c4204000f0713203130714400b90038440d5550712050100e00002d0209030102c1da888000c81c5e0300d038104004448100c202c0706840454031742e40745c01c10090306245200798400c003401d280444d00701e1b24048c8145500400002c203480c100107140d400f804000c1d044140344510340c03066181444d20015591001d040c2e0701d4414402850540c0840c1d00c0246031204407440544100c280c0380a00400d01201c240782c4000c60301d00b0120700d01c80c0505d0b241d50400329610201c0e5000b614030026892090212021042e40304c1c1001408401c243c402c0d10052001448038080302400d910440d9805101d41c3c00d901c100942c0140203450000030340c0c2c0501c244107040c501d5079482213021036035031 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 321285521 1250 321284271 321284287
    0x8040312090e0c0c07030206090414070c0c150203030a090213111b030f1210030f05030c0106060e031506060432060306010806011b0605091b0f10082802 67
    0x106408503030200d0281e11060810284c10f90b019034030036940c00003c1c825900442c030503400b81c0356603000728001c6201038404140b50070b188001400c4040c2c0400141c441b11032856020901c2e8001000300e02c508107071940114516a611070f03d2000425504500b26805040c600e00d510301c80f501c034001c40305032641039642d4999498100200340c0d038100d0391038800462034005010b16403000030240e0a40c2e202c007201c0f1140407459a2800400241200103070002040c410f1400131100611200001030840c22408000800c82640c171000d050b1291050300000e168035521112001c012a006009110f80056001c3c01c0320b0700740360710b80c0014086d00c040700100204044034144140d200e030b0404480f00f2600c1d0410faa00d0f51940c20300f0800280403c400420b4070341400310311050507410500c45456000c0003074124104000c1801e006030f603640c0b60080b6000200103c80c450040011074503006020041512005090b04526203503450190740011009010b06c2420790300780d485a4044900c1c6000100404880000603a1041c1f0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 321286771 1250 321285521 321285539
    0x30108011d060103030c0b040501020403060c05090f03011b0309050f010c030b0114090f0409050a120801300b090a0512040e070806030c120a060f0e1207050601060c0804031209 77
    0x1c1c6072000d550503844003004001003074004808803032180d00511a51201d540d1428030502900c507551008200380d15060440205550002c050503201c10110f40001d54481e00904040c00d991030385a40d0b0541c4460101d004035198041d9002d21807040c0300b102550501642c0142d440c1c2124441c440040c04a80c031040e2031491907030310003c19282483c001d203206042094600c00f0900e1031404400a40c0520307651071102d014007404100199002d075100c1c0c080b2040b100d034a80f00418800081c40b5540c0e06446080036040010201b00000729560b4241003550a001c1d201c1c2c540ca141d01d04080c01a1b80c0902440c0c00318004102d0074012901d4008410b00030313a540c0e5241554005601308001c00320001c002c0400144400303964045004601080100d07411b000d58054190400e09100c03008038018202891310440c401114016000004524a1842a00c4c0c003a141e141d041c1c103c038801c06230010407581262005205060050500d40c0145000c0d501d582c1c07c2c25143e6407074840744590560820086020048100043c240c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 321288021 1250 321286771 321286811
    0x1401020a0204180b0c030c070f06090503030a090605060102190b06010309151401210f110d0c03120206101a0f040603050f0108010b010e1e0301020301030b04030f0801060c081b0303010801 82
    0x1c03801038172078654500700152625a001d405401000b01c1000c0e1040410f106054000340c0c900ca404c2019255a400c00c600d01100500d004242120040e0519001034030560011440c20141080060003485071202307980c0e0b024041100a101c00e05140d641d80103040842c5c0c402c8014850b180602c5000138000c0d540014080c080c0a0580c0300c0201c0c10b06d0104484411103040840040d1654420f42820708103810b80b4010400355240c1405681000580082d181448809900402140d0244140040099072a00304a8442c0c0044a038881c105440240401000041d00100501407500c81c001d2401c010490588030380036845540000d001039100c42c2440341d04240c0b10821801051624000c0042c0500036002030401c0c807155140c2882115000c100400c0c001003e070b0000c000820042c003c42d82c9607102c1c980004602000d0740c0c16400a1182c00354040700b00d0103092514142c2d580c6803504082c034421940c4801281e8005110169940c10314a20600181030400103140641131120012980191940c80c0da40105 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 321289271 1250 321288021 321288031
    0x30403020f151005061b0115170d0e10020712080304020415051513090903082e09020708090d0c05130908030705090d08031e060d03091401020a0204180b 67
    0x8824072060001000c42c0c00306210490b201a5509600c80c41a00d0680c1850010000407825650070008034041481032008800c0560361701c4802002c040c1401c4036600e644000c01c2d10440045141c18090303104900c0c014615000e1180c330ba00c125107805413100401e080000c1c0d001411100381a0101c2844114641401200709035114160a54103903841c0c100054580e555007504a5400540051000c0da11007a91a039a405800d692005106a01441c40d0061060b04215045218103041c002c40185105020701100014204821240c0f02c090030510310030029844441d040300d0b8000208090401911074410040440d401400820400c0340340000303101200d82201c0a04810a01d060303640c0001030034120580c1e802c242c2074601541c4500c84400450a0b040e80da0101403c0c165000c070401400b003c1d2200a4000c003100d0007940800c98480d03005104018040a10040c0460b000d108203100d030211a890041da054170510446014140503004581180c084c05420100c2c2012074412400f8040c40e100e02c02c0e004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 321290521 1250 321289271 321289303
    0x3051608090a320303011a07031403191404060c020d02070909140a080301090f06121b090c17180a081e04060206090f07050a050607021302030403020f 66
    0xc1c5460401075850b00c1d0803600092400199040780701d20b40c010200b00c102030200e403619150b03030f0715840c04030903550307800c01d00c50110b0b5140c40c207010b03082510341c00b001ea6011b1645501d42e40f00524420440084070380000b0f0036410071141e50b0340d0468074010f80d40030b0f404040c0e240000341d5a2030700345401c1c91401e4480068441c001d540c0b080b00a82c1060340e00068030700c1140c080c0c1c03400080000d4a458802d009540c015000d43c5240700b500280c000b8800d410b030095040302d4110804110402c0c160344050240d42691003080c0b0b0743e40180252070041030960f8900d800980c04004050711a9840d01b0000302103442d1050103000043d215641000b241504030000d42d0032864a00e1807200702c2c205c400f1107070380d20719100c440100024404904140040e138040c031500b00710900c02209580b5551079000003952080210742d0f80d08640b083c1c0e113150700c4020001c2640029075801030301413a4641d00f8982400500c0d030001d00202d81001c540403884100e0005480a0b5003d248250b010300205401741585c1450718070880000d02034 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 321291771 1250 321290521 321290537
    0x1513020d0f1505040207140d08070206070905090718031e0b1f1502150a0b0f101202090a030f061d06070c0201080a02090405010e0a0e120f090a09020a030516 69
    0x2c40c00116054200301d4808450240e500d5005140c00f8460703105580b0541140c3c41051843e64046c0d42200c5443e2044800c2d41c2186c0c600e50706e01c9022914156503108040d00f003065000401c007441e110b801c1500451a0751504c10070140d0752a541d02e42203070204000c0320b1500801303404000401c400307541c41c1a00101031404440461001801e400b00041c100e114035200103680d015805141402405404003400704500d0040082c94100f07041009010407102c2d0521580071003506103900e24043d01190184541c50f42d40103400c4161800220095000d2484950f010410690020000f0041201075403401d02c500390202d203402606000000800d50f503d11100c4982042d010404c3d00c991241030400c0341502480d00c00400c0c1c031440402c800a11800c9a034941160801001240201c0e110076410f02a050b01c000c100454802003843d5038035402211003e40281c5d2080040c11001c001c50b20141c42908001806000c841d95560280e1003260300030020a00441d813640100041010b036400c0703004071038031039040040f8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 321293021 1250 321291771 321291791
    0x20105060a0e040201090b07050105041e210504050d050d02010e0d081302120f060601020d0908060c030408040b18031903050306040f02091c0c150807081513020d0f 72
    0x407066101d00401011442400009080d603110324065070007480190121035076640a400c10314042e1500719000d6540360104240d031407a002c2c02100d0b41e440d44d900000490781030103010781900003101c1c10302c041e14208070f01030102213a03d0f6940440d18142c01c4c03141c0001d1070320492604001c1d080d039281c103010070f42a801600d4227201d219008003d05521180704000307102c41c100c141c800501c0f0101d4020440e0b0311403141c2240c2c61116075000074050f015039400d07000c441030b0441c4240c0803a030312180d49c000d80c0b00c41d401c450042000104a40d01650300320380701d001180d00300394642070200070b10340211403220407111012400c5082400c00b4400e4490404051808a00e0210b05450190072444003038591070146660b001075005014140d41911007000d0001d2a11504101c01001000d03204046c135020340d94a00424070020300c00040000d01c03d11101c079078541e00030540d1007000c2540c844e100101000740201c1020b030b01c07007059134840c900c40c00d141e0181400180c642081d542118125070a11a810706c0051034009250 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 321294271 1250 321293021 321293029
    0x10804030c030302091c080c070e1003060504020f030a0506010e01050a0e0106081803040b28020d080c0702030a0c08060f06030303010504150b07060204051507080904050a0e07030501150602010506 86
    0x41e80498040c01d0150b03488007040003180040400c102ca10109000c040c0d24003041007280380080a1080c0420200e42206072954200608280d09507505009844191010000900d00c0c7d04050390050000700346006400c0340101182c205407008108944a4014200621000b07020380307251409044140c440050460a0080c00b426400301802407205001c000000101900e40054200103a06503071410350352500d90300d0854111540000d5087c5034000c064100c0046040e5065a80411081c1c480c0d006010a81e6648415100c0032000381c148031500204001d4000940c404102204106214130101c104151506548501340b2902800035142083c07184140100c1c1e65002007134030305684084a00107018103010321501400612584100d800140c0403880c42c040c010740c2c0e4094000c648094488184a10340083d15680511031000003c11228052041e080ca9041c9070340100c0e444810001e0009080241c0410715290a00943c401c5901e0b079118000501c01101507103019005000c079000078401403c00380001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 321295521 1250 321294271 321294287
    0x320a0b01050a210e0106150c08160215030c040e090118110612100501180b07080304020d02030a1202010e0705060d0906020f03090a02040c0e0913060e011e060501080403 74
    0x140081000707100090f0345440c0018034040c45008440c0c0d0411052860390350f400e018200620460b0b40000660502c80c41003400b680f81d00c60700d40d500508180c03178441e445a1200743c250200f4400d980185100140b42034000c0d998004500545070841e40b59125071400302009003040e001400d10506906018051034050b214900302c1042c40c0c0e0003500d2402115442010813014014404554400f03620b6000340a0380b41c6040c2d6454054070300a903208880d034a450720851a5000d0a48540080d030b4008000b404040b812807406503400603c000c1510b6a141510b40010389404071a1606480184580440740f0a498091044041c904500805029664505000100b0382d0081d101105006a12151044100502076040b00d2264815041d01901c80c284030b43c01503601d500c108000c0340120300e000102c07581c180c050790031a00082e1000b000083e0664032700e100b8400541e0104001c481980c0c8030f560250b2103d00038010001c03400c1c948a0006510364013100030109841c9560701680c1480245002c0c0800300342d002c40c40d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 321296771 1250 321295521 321295537
    0x1060504050f0f0621100608011d0a02091305100e19050a0f0501060210060801110910030905030a031a0a05150a0e0613060e01141903320a0b0105 64
    0x8491041c0da10f200105400b0300c1070341e26040322108441004086035003001c0301c86000c2c4181e1010080c0c4241c503114282c82c0310000313000744100c00640e0a041404801d4034007440d42d12209200340541490030410104190030303007215582560a40b9801040215044841c01000070080c00305198202d0424164411381d0011403050305c04101d03200d20001c3c2c00742e20260051800701480e15010460366960b520001c1d21017070305c560302c88109410024000741959050064428662001d00b10030720b814044010805100030a600f503901741506c0e918690003140c000d20217444110302584000c11504041c404c1c0585051040b07100a10440014034188400d4890503800c0c4030a441104070ba594510518005490454140f005541d01c50310000c2d89140e000481e00c2603604548a685035600c40d8962840107442426900303201d00154441849045400101c5510050403100e0340c0c00c00250b80d80096010700c80a00c54103039014441c0b09041070034903940c51104022940540c60b010104260308040c00000d0843c824014 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 321298021 1250 321296771 321296779
    0x30c060f010602060a2007030c0206040306020a0f1d0d150606050901030e031c0b210d17061f030b0301020c0f070815060f010908100e010c021603080f0f0409050f01060504050f 77
    0x7c0030b10406001e09031108da800d40091000d03032181e0362860040040d40c444003440b00080c06100140079624091400c0013031102c8240140700700c00100ca02030101d000300001c070079142181d0a1280811103c1c2900c204005040386a489540d500c01c010000b6090720348400c45080c0a900410a0381d007202e4034526100034030b0398061030100d1280e0f2804000713501040003400d5994031080341c3c0300c40030046d54006030a0101021036114500010300b1440c2e03a0503003810403141580c20401c204454046c5141c040c40906c026400f0b400c0000c1c0701e1304c030040400d089800c03180804280354401601c5004c066420000306004114880c0245102800418000340e8200050701c554003450b80c054400c00306a0003202414007410a43d02190b0130720b043c204008010f031282851701103595280c2084c40d40303030030310201d0044801c5c45121042c0c05205d2a581c2c80035401e03804007090001d19038003440881542902c00008100400f5101000300d103d06104420256420060f88581c090040070001003200341c96282c15808201d00c00c0b1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 321299271 1250 321298021 321298027
    0x15041406070302031308070302130603030e040507030e0f07090f0e10020a031e020304111e13090f0f050c01020c1005090d02040509031c2309030c060f010602060a20 72
    0x102e42a443e502648103290b2101341d0815000c80c11590010b0f0140c1242e000300d4020714a2301d048040e00084804c0d074000940050348040e034420700c0b03003080c0c0c21080c0c000c0894503000522614040d2038908010550742207180b01e8004240030048000c85014200a029040c41304004104c05101502c0d41c0319a5141c00c11002d68000c61b5403804140640d20021007402900e118407030710b80d1101da0301d1000b540101d600300c608041d81c148024490030700030420a040761780d82813030014001c0050208504813607041c0c40307814056264405c280005000354010f0001911520309500031113958a001da0600d202103450504651181c3d01041c241d5580e00074034003507034a80d42446940c80c42c800e0042482d006103144040c1d04181407806101d6070400000040c1880246c10320800c490400340c0b4400b17400d6400301141001034684000b440340c4911f0380d20004a41050b0054122481c202038540b00710f040c01002c5542c9810f02c105000102b05040d010b01c10940c0c0301221a07003c00c4440d0400380c41c0030103034403a40c07120000300d0808 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 321300521 1250 321299271 321299273
    0x31e0e0f033706020406050318070501210603050304033f080702010209030105191107080306060c190323030906160201060801021204030314011409060f060307020a021504140607 78
    0x120082d0502c0390f0001c2e410b541d20341c1ca071000a0101c0c0d00650352000c040c0c010100b841541100402c1c0841a54016504c00c20740d441040b020380240d8040507101b403a8651b40350b00c00000503808000402c0150302c44c001c2c0b5800c51252110480c01034201080703003064078454044103021514031008402900c03050741440c012a03203d0400403802401205000b0760190710b040c00344210381c0c00b900998100241c29003820b000d092641c1d07040840701d0003503a100520098003400890041c0c600300c0d005d4040010030034100c030200c0044051a1a840a2820701a0045801003241c0750580f0300c041c0000c440802c40000c040e207142090f100d1142d403075100904418521102c17401c10325045200707401c42c40081030800020f5403500e1300700d00e2a00e2208030a84044011070b28040c440c500c6403482c050518100c4484240c0340d403070420000203012160b80300501155000414107002c145907510b00c4059030003030007241d00a10140c0094814428411800c0d80c086420907400e000030410000303840c03c3c500b80c0c04000e898003038840110f = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 321301771 1250 321300521 321300613
    0x60408060112080c15010305010f20070515130b060a0506071506050a06080a0506031f020918010311040e0c06041e0504110307030501050105040e01060c031e0e0f03 72
    0x7481c18080581c06001132241100b81e1076245241600c0c050230080200310a410014800c407a001a10756500142140c1003913079001c0010701500b0214000c1054860383c942c0c4c04c43c16586c48d04100d86206c04840b43c180581c2c05d014005071407a910104c1614400c9095040c0000903a06000d034000040c00511a5944c48251014070b4011800828001d4a5807421980301c031406441c40404440120081c1d10f82000a00c0c2803500040c0c8154ad078203c2450a41c9110903134949201942c00286501e030007020f01e0040e51220b04900507598000c60154481842d2618803504000550b03000c1d0318424619400120034440f10703600d1400b12000c950038030100c03280540c41c2c80091440034032140e0040c0c1d4480e24001d101d0780029118801036200b224650360821050b81c0300c00040d6030501407070142e241c00e60320000051140300c0c080d900765100a4024108155501011411015200c0e00ba1000c4c42c0019003607154580700341401400d1605208084001d064540c403490194902c00107c0624040c2100703200028070310002c5 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 321303021 1250 321301771 321301777
    0x606060f13031e02031501050906090a021e040303020f0606130e100e060403091a0409020a0c02120f0705010509060901031d0303040b01030b0105010203121807080a060f060506040806011208 83
    0x1910200441010a030064680c50321103d02105902a00600a44034625000060124180c910044c5074808544880003804000c2c00002c2c26120150b5080041401c540050b40c44900c40080c6501d4079640d8505615000742080e00700c0401c0480b9500c12002d101441e540d05107200592011610700041e4a0100c1150900d452403000c80140c460340b0308400040210800b0a07201d10640c0a600c1d032540907503407540020700607100c481c1c1c04202010700340700500c04008244c004040c480c49601c0d28556550f200e400240d910840e040700410345500065125131072140038003107100140400d0030505d06021541003c01c40c188903180c900c604141c2d540845e6500c803600101c02d030f98030706418001c481c0c9920f001e26014040f80c2080c0010740340c005014000081540c4000211000e00322980400d0680e619084c0c2e8408481d0214080e111443c0948803011034101c03010044038030014007504001c2110300300e01c2049800c69902d0f40150b4000c0d00300304014480c008c000030f006411107003c42e403010703c102c0c11410b003802c00e40 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 321304271 1250 321303021 321303023
    0x12080f0c13030b0a0603140706021009230a1b0b04050603070302120c0306130902060d0903050f120105091003030516060f060602030904050a150302060304150e0f010c020606060f1303 80
    0x10715242400741d00213031a031042c1c00b904e1165440103c2d05100fa014944d5490303081c480d42006034000201d90000c003036aa00b05000702440b40c100081c028844441003a40560b2046640f0407d40c000c0c04004140812482501c01690344d00d03e900d0105800d0030080c444074400d50055038010107001020443d240e00c25411a031300d441d20f800e991030035410142c014001c603910a48415200d009100c0451410149038411848000d500910141c03402d07039003226507009411500b078140e0900c4000e0000d05040d810400040040780c4140b50b00d26159130601041102c030071030103804021a04503030401840040d070000d080714024800081040041c3d640e510b000d5003d8840c42894040359401c5c000e0004545070000043d00541104560600c2030f542c0c0e0407144d104546000b0b074034481030700e03445800b00003504010b4025a00310780202d05035540000c003c0042010b40d0500e00f240e0485510030710701420342e00003e119544c195a4035102070495400c048000401c1d6010300c6484030b00340000018801104040303008000021 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 321305521 1250 321304271 321304283
    0x15030519061527092c0a020405011721041809022d010e03010b180403140a021c0e040c080604180206030f0601091703030412080f0c1303 60
    0x1900e481d40c07940002002214030b008205661403020302200f80440d03001a2850305030425100034501038110700500000022501d0328071a0160800c0700c58410170007005000d590b00000d1101500c40c2c4140001c4440580c41400c503009024590150303c00c01207400c0c0200c20411000c0e007244602c00d28030400074452548469020500c01d41d21a803480301a0300322840d0507000300c4000b0000c0100801440c00c1c0b61005510b803007507200100303008a2540c0180c006862840e005400060343c02111230104a00c4448003c00380208014807041004059008803860b2140389228072460920746505806991456016240e400040c840d110110390702d8400c0d45159401040240180080141d011002c1d01500081d61030902441c1441d160746141568210003566103540600b12034555078034a9a000304e2a44040d0015040098030b400c009108209580b0718400c0d58400005107a890400c0e06d0701102e109240311030581031002031400c01500c00d40e102e2030f20341e01481c5480c6560b40c800038580410700c0120a03800040003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 321306771 1250 321305521 321305531
    0x306090702122d0901020c06180a030f06110a0e241206130603030c0b04022e030b0a05031c090f0f0f080f1011090d080304050c090115030519 62
    0xc11694082150810800100f90030400021007a20220303108490ba40d601581c0114140080b905040b8006d0414541e090040030324910f241c0000745072406070741c0c01aa090840c2c00c1c04841440058850380303103409040400340d0710b4001594005000d0180711080c1c0ca00c41c4404200c0e652104816001c40c1e45d15000c400e01099a50140383d104000c1c880056130322030702800c58400c43c043d1100b028071400d400c0d00c1c1c0648071204801c080307945006140d04c00800498111040f8500b41e0103a001c1c400180202c0303a454a649014040b2030107008046680d1040d034948280152a81000262404074481416070008201e030300b40b01201c0c60302034a2aa120b540a400841500080052590540d00140c802e94084800e0f1190791a941c203c07180d03a801e03500308548401e401c603902040c008039843c5e00480412a0340794400d0b0400291000040240305403080c01d42e03644d1000020001000414480440c0000c0200c41199155040c500f81c421410b1030902c0043c24166100c02042c00101c080035102d10180c084041806 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 321308021 1250 321306771 321306787
    0x426070206070b040c05060a05070b1f0303050406030507140406080a151508060d030e01110a0f0303060e0609091b040617070f0f05150d090b010f150201050903030609070212 76
    0x1084801301d4060725000d41ea00c40104082c50084101c4144412680e10707035050400e2500d40109121010300140d10b500a41c0003601c40702016600c6400040d4080c3d01c030b40361114900301e4040d0944500801070350800c0b040c602c2c219241084c90b000d40d000e0b981071b860700c00d10b2030380d4008201d802444030094130584030001901c00110f00412205030420715003590b5503007020341ca4142c02e000594429207401804110101180d8106500c6005510901e000f200b0413100c031010603407501d006a05000e0340640010f92541070a20030b4881d2541c003190000410350703500301980780240d19030740c81c0c074081186007400160440f5110002e03584e80c3c2108008c5c1094002004001000074031541e80c4a03031601c24052500f00013440007a92400c2da0000303c04a920280a10095980b5540c210843c0c3d0f00c4007141c1400c40e5132b01c02a2401080c40051083c0c003030181010741560701401d107a0b100300b0300e2100806a41c03c680c10501040b5040340040f0942c2c1c2c004100350381d44030140d240c0310380c00e80c14400d00b006041c46002c000301b01c003a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 321309271 1250 321308021 321308033
    0x302030a03030c121506110327011803030e211216080c0705012d1808010c0c0314040b0403020f120a0302031305011e080a0213060e03010e0105042607020607 69
    0x10308690447d240c0310200250300304c54540f01e01803c0700c1000c510342c010007625810855135140b40201ca90500d00007100c9504100440c101202c190015800115034001c02d03a9241020807074580c601000d42e070910f2810007c513056a64441c0c00c00001c000c107000218246d00c89140030f0041104080d8840301e455141c01c128200c45a4440c21881002e0010300f041c2e0300a905002c0d6510a44c40651030855a981e14528500d02030315070a8112046510800c810240002c240c90b082c07050001e018055a19501a16440c1c2401006000c03880b6140780101000c020411451144400701cac0e0441e5410f40c0c40e040aa180d0600103500786403840103541590003540e074100b0405070b0100040030300304100c0c0e079000001e544541c01125450b40f0310680c004003864207031610080354061040a42d100305210703005071803c031408034500624105544000085180c5400c03a0304a480c0a0090128029000c0002c002515081e282e00b0003807418040a8050741d180f44650100a24080d401ca078a015005000740f0341d151403910b424 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 321310521 1250 321309271 321309311
    0x91201020d0c090f0b07030c02090f04030905010306060210050c1201080a1a040803011211030d11060a0536030708090f031f0e0708120c0f070302030a03030c12 70
    0x1c801c5440c100030798694600604004043d2803061600342c1c0c806040114500d40c40e40f02600c00d03010b1082d61801d41c00140c1c0d560348514410318900c1d401d41e485007858540505a6501e60300028107042c01c0040034400785500003440079062110103408a03042e01d440c44980614421018292000182d81c800400c0b001000101000800c2c840c20b071181494500d13461a440011007a100149214000c00041042141e400b04484503a4000c0110b079054130401070000349009a5100c031b181c0401d40b03207020319000d4207017400443c0e072118a07141c0c184060325000c0070700386012808102100c0c0001c0c01d080c80400300488040341010000b0943c0c00c4a60b25042d9040841d2550070642456205440301e045054040c2004100c14442080c03d4052581d0107c0103401e030300c05004520076001081c412b00e100002d20050410a0070658128240e05595845e0424203c6007031009036461041103a200040820042c1c80002d4081001c03505803400291a0380300d00c00840b82c46da81c80075440c80d55810985122102c0b0442c102c4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 321311771 1250 321310521 321310537
    0x306010206010906050907080720071401020601030b04020607032303160201091101050c0c0603010e040b0601110c040c11030a201504060b01020c060a0504030606050d151109120102 79
    0xc803040740e80e0300c10f4018140c50703650050640103944000418030940c0a40d0742a500800c031418154044244510084042560b11710225503940c0704030401c200f000461200000e02c0c00d420300c090201e660543e190545020400780009000d010009001e4041c07600c03425441004192401c0d80c080d1034220030201d626503800a51f48004040294442d0007855401481100310307199001d81c2222030b1600540054410f0382000c21000b016003c6c0d804480e403603650303c03401117001e4000070f070400e03406040906000c46000e50040c48103040c01100240d02540041c00902002c421100311404524200b01d401e0446504107840405e800f03e2001292000311144c201c14046600ea6134000390200d280b4401311000e950701a02c00c0942400d02c40c0303001140116000e5040803c1d042d00c1070044610702146403020a003a5840030308624009040071038207104022441c0903000c0204000c48446d801c80005458210f41026201038105500c1c0c1c1d611009140300805101356061400014202003051001c000360341c3c040e41c040c0340 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 321313021 1250 321311771 321311773
    0x90603030206010608090c0112021b070f08031c0b1804110103050a0203070c1104023114091306060305031c0b060708070b0c09060d0605091806072a060203060102 71
    0x20130700a214495962164550740002c0078604603010054908040d0202e11014a0b5000c22280c1d00c0002150320074001501d854005028061800840212910007600a007806030020840701c140c40801d00c411b4680c2211040000450300017101c00254080030604080b0344656400041205002d120542a108a002a00c05209568814140d0804c03407004541c0300d004a2518010000403ca800341c0c512261413001d04010701c1d101d21410310460340210740c030120702a2200380b4030080d50035040700401c10081812560841d259040003002030405a4004c0018800e40301c4d9240840c00d000150300218000c603005001d4a54030047c00b00b142080844100031850740ca82031030b260303c4040c14800202d83e03403e5080301210741072401964640c0110100600640c1054009000b415070a540c0c020003800e060100c13801c00078265140c10140b201c0300800500c007605c0f035106901003043c24040030a4040c0d2206551810900c0d1200003290015001c040d07403048291100c1c0100368400b0000305500a5014135800d070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 321314271 1250 321313021 321313033
    0x10504080903100c082811190305041a060d0c060806040b010e0306060411040801050c090f060306180c040317030402040e070b0a0e0103020f070c03061116020607021206010906030302 80
    0x100f070010a42d140403041400240000d0000346604055580e0960040060000b485141418110090a032071003030703800c03001c69980018003000441c40d8403116064a02d1a0406120510b00340d161861980c03005ca2614511300c03d04000100b646d683d20707480081c075650044a41100644803c00105001c000322880b5015501c1d1400f403e03101e6000703511020601c0300040c0100159941c00f0103010203440200301450b034000d42070101003880442801824130410024a00304d841d4840c0004019100041807051030080008005000c560b8660072460075148910000c0702800d0f4030764610002c820311450381301908002d542e0301c0300c0c0e0000070b51000942c002c600854003401040480d204190703c2d11228801c141c1481030800c801c00009004069224411070141030050070400590391090740c0b0341c850300c411200d038240e0031018410085188500c100207001034a0340c0341810200c3c2048005000d84078000313403281d000803458070110740c0c411a030b80c403203400058182d0f595542c0d54000c44014105502048001d40112 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 321315521 1250 321314271 321314293
    0x9090d18030209060607020f0d03020303061306060507020d050f0a2913110117070305040311070f050d230a210f0810080303280e07031506030203010504080903 70
    0x12210303420680781c004000f8901500c40324104000c070344c440c1d0000c9800a20804000601c1d682e900303940901035019801840d80c902c0d14004200403c8181629905500d150440510105500806403148242d05071048464140c8904025141030019101d044144c449c0b4450743d410400c02a996203a90300e5452030400d60302c0900301c90554012800c980c542d08070410028018080340000c801010410810305000507031003071140304002c000d1000ca403000e02183e2681e091004150344480041b001181c442d01600c181c6040208001050703950344100342c820586241200123214007940c5a110b40750899002207103038101500d940d9114841c2001c1a206050360b4051414803030030320580222041016030b201040c4403940001903c40500140c011204113050840c003141101041000b5400b0b03502082000f004000711080102007040783c4906c200c0011304041401200c80ba00040c0c02c0c00f81c950010711800c00c0a0030f0403e58004040640c0060352540c200020300041c481e101005140307201082d0199090301443e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 321316771 1250 321315521 321315557
    0xf061e0b07051207062c06070206010e01180b090a0c0f02010501030803010b28030b241803280c050402031e1b0d0e0c1203040b0f040509090d 62
    0x3403064054415006a0403c00050002400408140344203280005202d90940030400c404143c0208170131014403600c502c101210010090340d40d112515200812440d81450ba084920700018410f080c030725045400c000040403940c0d0006101e850003e00f1890781c030301e400d04000c4c0c05400444466004640e14a070316203c0d151042c06002e041c0c9400103440b91960b441c100800e06103038405010302000c1c00c0f020f51034524800c01444c1000c3c030940641d0f0082650000c04003040f1610401c030300260900010400c1d24108140032109807800e400e150811030405c2400000460b04050510203196030881c1c901801c4600407a40840c14041d2500030941e07405100e0b140c0701404224441602c042882c0018551050214042001d4255110104c0c403103091a22000caa40410317030780c100c0c0310303d03200b515100c1c104038000240401c030192049104031480d98051180498040d00c80c0725030b0080108020f00022140c1d0550100d500b02c800500c0c0c094101c82451524103031994071140c1403500d08000038107101e04107409140c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 321318021 1250 321316771 321316777
    0xa050604054e07020409110a06030b010c060509010b06030c0c0709020325200f0609030738070807030b0f0f0603150a0807080115030f080304060f061e0b 67
    0x4026007040c4101103403035011119441102c00b80c60102c41000307500016103c50282e007a07802d01c00c40e140c01525400504111050919070040401c051405035a00c00c80c0c1e07441140750b21610b80110002516483e0701100c00d016281480c0350f540c00640c000103109900c1103010003132003150b41d070b042511155900e4000704816032006070341380060a40c0200c0400b1300003040c014030358081c032404e0821400f60002800d8010103d5200504600640c1001e0810b2540c55000e010f143d5101d2404005145083c43d03e0380e500c404e0303100c40401c5042d0000c80c081c104031100740006c01080da80001e07002c078000301d180241e001410b91400301c07000e100003802d00c0f40400d02e41c10400c0300744403594801800e1f010031190060038400c3c0c580005009002c44490a048101103031100c682040151100f00301a090050401001c40e09403000090554000c3c0c2c0c101004101044d081e1002540c01580055400e0b501d469a041c8640502070303811030086002c0c81c0c84030010352040381402000c4101c48101803001602d6403400c1d9013000b80 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 321319271 1250 321318021 321318103
    0xc0812040302062802010f050f01031a07050c010504060614090402010504090209040906020a0f2006150d05060f061908030406031e0e0601180c090501080601020a05060405 75
    0x58080c4030501c01450041c0c01303029900401c00d015140c1e000c4001030240308613410240100940d5444100b1503c010345030044c188c2c02601e40b0346002c001d5142d07584084030740c00324841e2042020b43c0c00f00031510180c03151080700c001c59a0340000740054107003410032500030401c52041c80c03408000440302c0c950a04211140e01d00c600c5d016100e0310304103813600070100080d520003824141d01c140e4035040040011b4840c13000d444041016680e03541c40d05155030028051180c007041c1c00104e10403800c041900000d0000741550720114601c05800071103202c002045005616150003440c034040c000412a0004007400260b100c0c46046800384068004189003860084243c06a41c103030350010401400740b5806500300b0507080107410f1701c807000c9a5048141100320707107081d41d999019821210040208096901c4050020340001300200a07644084001900d02503080c82060b06126442c030020703115a0080c08545401d507001000c1e43c4080c5040d15140f501c034101180c0c00320310840380e580c0403811440d1440040001d0303 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 321320521 1250 321319271 321319303
    0xc010806010513030f0c06080c0f1818131101050c1009080c150a060f082a0a080f060f01150509040207120c03030b0418140a0c0b03040c08 61
    0x19840e90001165160300121020700d0004000e000000000c0240c14103001c0c040c040d0068030055410000c1c02881080081e0010b004a041803014816031500001160000c030521540c480c04201960042040b0203400d8032141d00348000b03502002900d00c500300c80c1d070762075500c80c2460030602c00ca80001500c06000c3d00b86d000405074051203107000e900226a0003015464060003c003410901160050361901c0c008030024081e00100348140a07052015000711000f030208107204120b02c1d4200100c61381d6503000e81b0031441c040d41c0451480805203195000c00d51403040054000702c0f400781c442e007565982d00541305c40d101031441064001000d414480f10524161110941c40080e4041c1005040754140c201d4500d440e4095400c021010000d0001110300001ca02580c80b62400c0c10300301d017000f508854020584c076009900385402c0a080104030f01c0003440c3e10790f2150020040324000d082e0305151140c088001004e40c05050400301c0c12440171400317548aa8403600080c1d12840e19001c00d039444d031540c05d640c404d603 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 321321771 1250 321320521 321320537
    0x60105031f0b36070206010506030c1303150605031204030203070326031e0708070219060906180b0a060803250b040c05030d050f09060a0210050712050105030c01 71
    0x80e045850700503880b07118000703054203030b0318000d030419a00c540c800d81151034a00c0107140f012408440c0c4062444e0340001580007900305580342101158440c0f100a254254440001611011580c41000120042c40e0441c402c121840d010340a02d10007450705004a61003032040108510704615980704030303000e40e03501401402e075091450b07803020a0750a04445103052120380090b141e4980c0f90007030207181704e18402004103c00c0c010f0700d0550290f01c04080c10b10f90800c80400108a0350680010300b00d00041c840101c1d0314000051401c18070300500e29400003d01450600c203065000400560b5425a440d0180e2225402920380c0444201150b03124482c6185075007051140745006199080d5903c400f54000e44d94801c0c030950703581d5895100c10b0032030702100c80e03050005080c40702e41800c00c038003101d01d0610705000b403402d200b84843c202c00340070300224030784100000a00d504909209100181202c840c2c06c4007404681821013014010791b1030523907030150740c03450100000342901e00054080048901a120100 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 321323021 1250 321321771 321321823
    0x1090c091d16090c2109030807020613121205040c080618060402010e0f03030c0f010f02042301030905030c0c040c0801120609080c2e05010303020304091a2106010503 73
    0x18000e800411014454031156405802c0350030544182185c45145002848110614000e040c6990203071151045602c00001c1000c2880b40d20901e4001c590007048581d541c202c22642194500b0a56502840ca02c0c20700c4244401c0254400440c01034400b860262001541c0f0901000b10b1840d111346090250fa1041c07000c80c001d54020b010242d06050080d2202d082900d64102080c55680b1000d41500307582d201a0074190742060a01c81c0c9660307560101030a614080c80c00c1e000c8508200ca8082072904000a002da40140f81c0c0654022031400354050700b501d8446000c0c1005503190380700100032030301943c1007001c600c00c041c1c407030750099050700c8440310003180680c0592180d40003808040000c171149d0b0402c01804012840800040022100c0031110696500b1040040785d40c4518004044400701d050800500019401000740e4058071000000061040190130500c692250700c08042034000e2648020b545905c50000c502c0150104150110b4a550340d85100741340e941e0b0501d0b01c2a442c803940e030850313001d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 321324271 1250 321323021 321323039
    0x15092502030c07060c0b010b0c0703060617060708010510030f02131508010603020304380c0703170c1b0a061401080d09080d030e070b03010b070203121603080901090c091d16 76
    0xc109c005984080302c0f0100c0d03c0356143c2007156403e0b004003c005060062006080d030702040303d90b50050251600410301d5242c040420b400007180d0400031b0926490303001d030303500411455041d266201c080d044840080ca40e0303552180940442116680c000441501c00407910764024021640903640c8800c00358000180c3c03190f000300140c1409041e074940807801e00d0802402805c2c800160268441445050f912440c0d850054024110352059202c0100d04804200c1040100001c4e01c4400424000700ca50360783e00a00b01e80d05124140c40000c01c041e20308400c4682c4801c205444605880d00301080b6117501f01342080035500c20b0128403030800745a001c8503032038041e030780300b90001c991291550f8211809941c940c07090103102d4000742c1140308030280c040345075415031504006114143c1d00412500746032101244510814002104000c1c092005803c08115450b600b5402711450980255001035120b40b0f03107612001070503180c5803000c000e1a069444401003100800c034825031b03000d50071441407403c3c40c0110031307 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 321325521 1250 321324271 321324277
    0x11e0b18010902072a03110d0209070e0a0503010908040311060f041418040b010b0a03020408100b04060e0919170304050105090601080d090e0403021507050a0306090515092502030c07060c0b010b 85
    0x76030084c40c80140c8e400107031a03204581e400344145403a540c1c450b400e64414400300c0185070340050300c81da0401c01d00e580400c0c1c0c104200c030292a085680c080d0300104040100b0810322405c00c08091040700010000f0b01c4002c14452070721481c0c0d00303e91703c411080c401403000c0111441580c2c044e10703d003404001006124494802003222003001c0c1800340c2401c0d510790505041012000c0c19503070054460282a10318a018401c100190102c07240980d814200340f41060f560340c08402c102e5207520b07411050342e0280b00412010014030488007030016924905450300030302034102030324070071100d20030310001042c28040420274138070b102c410f961501020752030602c0c0c0c000200000b0384190298020b00d01004205240c20620921509540d10f40955549a20400408541c540e41c0000700d264984410710001c070000010b28000000102e40c0c2c9001521500d07a414108807250410920001d02800e42d400c541d9000301c05400484001002c0d01c80e41980d500054944121081c80100351140d04001800010210005 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 321326771 1250 321325521 321325553
    0xf0402041d06100b0c1203060402070204060b0901090b030105030a032604080a080709050d151b09080601090209010c0210033b011e0b18010902072a03 66
    0xc0407801d4001d15a2070156401d415400a540703800400030041c4014800001c03d004000f01a4614a44000a269607490701040070303500784500400804a400e0780d4881c6c044d5031103240c00030001c100c684d83d6268462032950180131041d000c0340316000002a000312500035a8103c1d00064081c1841500035078044038401e80340e028100203500c602c80e107071704040d02600700b9a110301c0c030880c03d0a03512500100090003400c401040c400401450880c284000c0c0c49840403601e076070798882c0c0c0d941c507003222814010010340300041410b074503500110220b610307540c1e1103c40b15003200e00e4581a0380d4544d0701c070b001d00c01c140d02c503102d901c80c0410440741c141c000600307100f00007880f1400030740f80c00210f041c0c20000e0314100301c0c1903020309415062010b58401c8407101e181800070000d15210001c0000841d40007801c5007806414131241d201c1c0341d541d4800c1c1c0c810745611904504a0074805441409517858821a0000750081c2005031001d034044c1418514604080c1c1d9105d051501802002c200d492445d5621041c6801c480a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 321328021 1250 321326771 321326779
    0x616080a0f0207120801031e1e060e12090406050618060f0409020c0c0a0608040302120c01020909130605090a080306190e090f010b03030708040e0c090d030c050d030203010e0f0402 79
    0x690b4004c0750340105070000007075580d6280c40e12540740d42003803088004800c08101400310b4a05c074220001d40602003443c0d0120340f4071a0b035504500c69050210007400110400b00c0d060051052500b03c0c01001c400400b800702d4201c404020040d100e40a0001c0e50013118000c20f040030942911507418940035019004c9550155101c92600d0348529400c81680c000030004205544014420103c1f8a001e5484130007414440c6460000e6242985009545041c041d400f40e44154000400603400c0c1404e40442e500a00c0141c861001ca003000e0700c0f00301010400803400c2c0c038410b02d464081900d030000070070046e0046400c201c900781151605000c11800c80c3c0003a4400c0303d40210304030005502c06800c8081849000e044001c2c203403026260442609550180c000385200b40c01c10003007a000968039070f040c2c500344d4004161803c00d60f540d2686402d01c1c0d2003803201c03c40c0d0260200614108050b4402c4a041011740304406a4546606501c41a41a80000e00607040019951400103491010b83e40d00755034800c1c0010 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 321329271 1250 321328021 321328027
    0x80405040207230a0b060f090703050415140402030d09081209030a0f0f050f07151206052d0901060c06020a030b09010915080312060d0c0801050106050c0616080a0f02 73
    0x624542443c1c19246140107040d00031140c5007083c0f040303507040d4541c0480c0550360700410003044000540c101b03100030081418156a040418140007071001040007151245004020315032a03104014005581120124482c0c413a0180c19840503100340c40a50444040c0e1004000d18a000344031a5181e4103c02e10280d0584281d010b0074000c030703d00003207285002c0d000760000c0340301d0300306409e14900308441e06a28100562200508201200e07007240301303121101207868000910111a00b8440203004580c0c00b0592040a08405194131070502c841e102c1c0241235442d4013007006d04400c003407103103820091007040081440f18111101042082d0010906503609180025000e2510000161000401e80080881c2c665403800112503001614003900640b17072030b40042d070600e05100345403603620f5402018140204c4003c64041c00304000b050070f440c090008500240201c2da180e0070004c10036040140280c085210700d002045030070800804603104141b00340d4419034650744101032140130b4803000940300b0b0070351390030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 321330521 1250 321329271 321329303
    0x60a02030d0213031203050603250b03180613031403041e1506091509110409091b0608060117090a02031902091b0a030b12010e010c110703080405040207 67
    0x180c80104040f00020310058074540c11400c20a0b441c200660a40c82071501d0f0405000c035581e4005810a50619112a4040e018812038070030403441c0c1c03150303000f414007402c04000d205400324600301c26403441346148102c4440f903441c400f070400080d42c103010140100c0c8516507114408400c1c240250f501c540621001c00c0c0440b2524205102c0d50020002034034203090300d030701c00301600070140101001000c1e04a028041c80b100c1e03040414030103001d0f03c649464156600c1280002e0318142341910b000703110b50b0301c0c10001040c4900b041010040d980203400c100101011010400354000c0401600030607040e9101b1002501483c80c019480b00003411078041449050740e45401a502008030000182c080f15100c4441e013014414858501301c00380c6107540e0350100c5000b025001080a0507194512010300d803700300341031003401284841e044d1701034048480d400e0070020300460720b05401c10540941d459580e01d042c0142c5162154503103d15020042c03000034108030800c26858a500a4401d03180600c2048101840b0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 321331771 1250 321330521 321330547
    0xa0b043e060304031b12080a0b030c190503030d0f060603050705030727030c0906092304031704050c1e010c0201030b031c021507090e010905070908011e0506060405030606060a0203 79
    0x61728007205c01c1c0b41e100c80c43c401119842484a5040b401000701400f40420420000341c4960084141500603c40000c1d540b4010181c48200c0000300000707000d503581d0302d00241e40b40025001031210503900c5402d18200080b114071a114103441199160356070340c155200d10004640000b9540b00c440c840c80c4100703010302c05e1b460040786098000d52240b03040c1d00010b45071101035019641182e01056140d0b10300310400301590440c070b4011660f24102841e248095079103240541e80200544800208130003000100401c0003400504584504012102840702c803882c80307240c11003100c4400005000603001d800b00001540a50441c03107000c040181501c070408c0403004c087d502800301416103001030b4407100a06a1580c3c401440681200d15441d00004050800209102111041c4540d80c405682d40700080d1240b4854115000a44580802071152152030010301e100d4403074040503c1103e501e010040344031450814101e1301241c101038041c00d51942c40f00100455500900c0900b019808104818122181 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 321333021 1250 321331771 321331817
    0xb0f1c0e031809010e0c07030c08041a09191a0c0319170c0909071103070606092702090408031f0906030b0f09100c020a0b043e06030403 60
    0x608002d0042240842c002004003103101030b4051002d4901d20814062407003518012502000c0c0c05040034a4070340c13101d00d84110710b4070075a8403070214140c1040f00000c175020410014402401d08442d010a00ca642070b25905039a030303051250002084a00c0c2e80d080840d61100094954800308c0c1d0244c03410407001050a1008a9223420f0720030028064004d190105203420070841c1d00080d100c0c1001d41840d83c0c2e039002c175400c81c2c030203480c100074003540c0c8100841501c03082040780d83c201d50100c018000c1e0b6549010341005440b2403104460718244070080e01141c0d0141d81c004900301c41d0002d2845a5984450304e69104540c00901811800c502d22014000d0325500c00c1d42d010000c09480b50f0002d0500d1442c18480c4c010200075141074012758000c01407101c94100003d9200c1a20a0380e1400142055143d506034130702043e000b80140343d40045400c03c014840b441d16080c26104da603552400840c130400c41d081d18918440401c440e1559140d01084000c1d007004070155078032901c2404c1264000c0d800c0b01d491150382c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 321334271 1250 321333021 321333037
    0x10e0310050a060801110c06070e04060305030703090e010b0c15040c031a06041b020c12030903011509060503010207020105070f02010e06071103010b031b010e03160f0801060b0f1c0e03 81
    0x680c9880e010003510700d003442040050302c407801c0b4050821184003591600c23418043d000340b00f080a0001c0e1244140d907940d010070021a0710000302d035540c0202e482c000c0e12180c0c05100d2018602109000000c0c100300c7d58003203400009040000c0c1a6003210030f112143d144101900580d014181d00001000181c400200031213030011080380020207190410400c0b095074041c50b0b010521602d490724650800e0f4000904d082d2210302202c6180b08200901d20180c61070003001802c0f5455801c2440441300a564681040291000c0c0101030081a0b2920141420b0b4890703200700a0005108118000108000d0004401e02604c14034003000040c200200003080b982000c8020364814080e544005010f00d003d01c0341001d141020340140140b080c6400d05001d022341603041031818851a48148100396a080c0a4a80a409a00014401030703842d0070b0003121060741e6000e4a0481e600e04000450305040a0050b92049114105003510300035034014005420b110340380c00e40f94000c1d1070302a9214484000e001801d011 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 321335521 1250 321334271 321334291
    0x912030f0424020a031704030c02040f090302160f0e1008010f0b031504051c02010f02030405060105030d140306012f01020a0e060910050a2a03092102010e031005 71
    0x449804454942d11040720440b00056501c0319507035038006a00320124410361070032080000402c1e84d560a054807503401307401009510500d04010009d44248a40c40a04158025400c60784130120800041c007a2000b2405440039030b420ba6041048108001101903601c10844a00003821a55503180d150030340b080d003600f00c00410388521210960382020020703400f18146884c0543d94505040d15a1030f228a04a484840403807100781900091600035003001c0e02000000c4003c640d41d161a0a2640c2c0f00c0a0a000d4680309000340c90329400590b20441d00080c1d0700c070a0f114154516144c140065030302540c40c0180c11b4054003440002142540000b03620b07100b03601804005a134617070150702c000703000809068010f0711803030702445845240e4a962030341020903002c60808540d40c035030b04881515540602e11401c00448590311010002500207031403403e03250301c04d446207a03d107512034003042c080d040f41941360705081e0414a020344c05513110f24140300b071043c03001d81961580044100028146e4100f11043d03000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 321336771 1250 321335521 321335549
    0x90f0402310513020a06050d1512060509030304030807030510171c05120402240c071406040e0403120f0609052505040b0708160f02040606080c0912030f04 68
    0x42100e8040c960340700c081810041082d41d01c1c0d03400103440403030328040c040c07c11102103a0096946541e60000c1c1c503101c80140d10340c480d00e80d1001d1404404114500894105052601080c6484800810f5a004a034182c882202035500d82c0c1044008140041100941c0030240100180440700b498901007041006ca000d064946a460810100d051200c00e081c2d08018003080003040f49819400714540003a070440380a10464107903043c036038000840301d10154048000050034003007188001180b0084030004600d012034581d001040050500442c440c00b14115103810010300000e103d00703900c40441a03018400191090051140812540d290f04003608483d0f0303400c141f01c0b541c4404602001c6004024030107803281c10f80d203030000302240114400c02c80c0b58500820f01000300200791040d21000e0f2100282a1185010750400508901c0031680907030144c1c2c545030012410358401c45c00984140c600602c071500e0301400c03100344203027140050f060180ca400203210303400d0002e400070010f000030804408410382d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 321338021 1250 321336771 321336859
    0x90e1e0303160e01120510081f0b0a03021c24060609050316061107080a060507120902031903020c03010507080603070b0a0f0f030e07060908160302090f0402 69
    0xc58000c0169604280074481c1070303100d42e40c1e07170009011104009617000401c0316100e100d031500c200c4186070030140d00d5000391300e050240a03650030301e504404d400c008001e004c2d8001c1c0205000341000b160001030340000683c4100300d0801984140da0021170f00c1044100c5241c05100c496400a0100e4401d043c10244c5800003040800c1c0d004441101130881240644200d62000d010500445414803c503400e103c0c184a00c1903001c0c0c010301c090360040102d20140c920154103490050001c1008070f41410104c0e01004441902c40385621508207805e5000d8010690340c0d41c3c54058280c0b6040c03401c0100c0441c498400c9030305060b14207000d451301400d1140c58060706424040d04040c10051990000c81a910080c00310750342e800d40c400a48149500c0c1800c0c540c48030f980010b012806000741740d0002e18a4403441d400042c009a0007000c1408440d48402955004000d40303100341030740340043c80060f60041550340443c0308180801116500148000e01c100001941d804801c4644260710100000042d0040c3d4090 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 321339271 1250 321338021 321338041
    0x910050a090203090c010c0f0507060509041a0307050609040908071a09030a0c0b04021516030908030a081807030507120201092c041e0503190f09090e1e0303 69
    0x14250040c1c040d0b085141c01e40031160b40d0000d103001281000035454400c400e01110406004895030050181c0b40055141c45007e8241d0b403040006900503841d0103445040e804079035007a5429007400038064490315240600300f100c0e94124800155104e0b569403e94000190304100030012284504140030940010b44c0d41003000c81c00041c000703110740d0820050321010540c440388a40c0701035442584981c4507159030010030030388403011b44800c1c09190b001501c041600354600c030200d41c2c0351081c2c0c1e582040e0b58852032226102c0c0140c5001070082151840071400e811030305a1340f41315000030f01080b00d0602e030352500d595280c181140d0000d904040d14481075015960f00c0a041c0e00601400700603846546c1c4104901c0e8517580e07010100340b244001d4203001c1810041d04a0440f1900340400403ca0307a901c910b4107000d6229408503800c8154410086e2444a07018000c01001c11420200e4032620812450404000060702c410b442200c018040d620310740042c0030607580d4100040c80f40c0401180c0b2172410070444 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 321340521 1250 321339271 321339289
    0x2011506090e010e040503120a09110316120f0203010606170915010303030905100501080d1d0904020d05010204031703041e11060a11241311010e0f091005 68
    0x20340d0401200e020300344500e4041c001c8542c115041d14030044080e030703100e050050844c0602c0c030300243c0c10000700c2c007440b44491864110b207140c06c2c090f2143c1090300c4c0c03d01b4205681c0f0070300e082c114800710810034020041070340f400700318056260042c100990801915400242101c4283e044000401c20701c00200040d512654502540010034100502c0c2d084115000300707041c854144001405c044d00c0d25902c00400c00107101740d1750191003103a800c2c0615610741001c0d540f90100c0c44000d1002480303640748802d50390b44c40c5083d001e0507070b0042c0000e0b0741900c468080c8003410b0540c40d42641c03030359020000040003031030b1544d12040340d0aca254185a16070074079180c14195504158000361041c8900d174441000b0410702080c0e0010143e0441d40c1960720345090700183d07208484031114500e00e0203a40c0c102d8440004a0400c3d03110701c031840070608802e070f950000707111039240c0c0c8aa02800341082a18031810139409060031019002d40144442c5c0b42c2c1142e0070024001c00b00484205a004005e070390100040c0c02d000c201 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 321341771 1250 321340521 321340529
    0x3050f0a1e0f0c12020a1e03020c070b22030209150a15090311060c060a1a060f0a080906090d0507060b030a110907020a110402070314030a05060f0604060f03050903130303020115 78
    0xc117620740040785c0e40003402c00070417030000c0c07064031030f413002441806005c0e0b4110740d043e035a100c05590680d56507a9014146410203801a00f46a01d400310b00702008107400e8101056035030007810511103445e000b80003013201400f0b00c10317a900300303150101c0402c0031280c00111032101c004c01d0303031003412140c118544541070348400c9440901841090280c4941c525004c6142c40e403103c0c1c1a40c0009400001402426515901540860300654002444a40c204401c0c0091900c044c01e81c4400d02c1070307140c00e511580c1d81d81c4211000c848a8001d6a401210544100001c1c8900303401100045442c1c0b01c502d00090400760f9581c0b045901c4014072100c0e60050401c0358030240d12881c2400600074080440d101c40502d299803561551003140e001407044109400b034400c0c280b00310314004080b80c981c039106800b04000c00c42aa1418032441c00c0c6000c0302440e15181040342d06503207095560340c1c103180b21070b40e0940203450003a004141c1d80c001800380c110590061034400e0011400791f40042841d4010407201c0d0004145908 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 321343021 1250 321341771 321341807
    0x27050d08011401081009181a0f010306020a0504050406180c140a0509030a0506070507050c0306130f02120d050a031503020102031605030f030c0a020c0103050f0a1e0f0c 74
    0x4100400d02c80e031031031080400070b0912907510b07900c04c002020708403907075041600b10524005d8142c07880841180d444c0d900c07038411082c407070045002031600c4c1e05540c82281c400b008001928010320000f001900901140c59042c248581001d44030030025042c0d07540d5400080b0003000401140c55550918000d2046980460070240ca0034600c01058a0061165000b104148080050001250f40307080103c8007071260054180d450030f0410341d000802583c0050001e032228418a507503482d640c500440c82501840c0b440d44070b002020441e5a50910302320224409a030b2014030340c04c80d005603c40922458030608040c4d40e0b060740d600280e91000d0200e41c54041c1038030110003090030510050340c00004444152052001c10301c100007980c030b0900d1840c813489090480b18800441070084010358000588a08542034003a1040440c80400450864004443c445040c103148800b00709502403d40c005100089400780004007030800c00900403e80703001c1c285d40d8001c95550b1a440400590014000d106880071f00703 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 321344271 1250 321343021 321343037
    0x15060e04110405060a0b091503070504150503060109030b04140601180e010b0f0103051008070609030c09090c2c0c04030308060a03151a1306052403040809010327050d 73
    0x40030450810480c010701200c0500003c0c000c04581d101c031132030232902006401845e9a41b8080100600e00c0e0000d201e0040c21024910040e00010f00880a6030711030780341070f0349254807545161542c2e800c0940240054443e500c0100301d1294010082c0090390190074080c8241c0406650608070781c0441d84031090080013030745058000c7c50240d4400704c0c04109010240703008102c9468440403c0144051130b801080544280340c8002925600b1002c48011640260000710741e41d580c802c140000d40b01c0703044004003001c0d0208030501c241100381a1404000300d00c10b01307020403180c1203020400c3c155425560f141d0340c40b5003c0b8082040503880190503900c00c0003501e000d6501d52031955402081403100d82210b01c01d44c1c0301c210f03442114901d035106101050006001030402c0c010184400000e00441c015903000b21891403849002c1003043c2004040071004030342c03161031956540c03a20f2034141c01000d502810941c80340c1d1490b20410038000041e415012510220074048070620f0907510b0440d03002d0b01002400707900 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 321345521 1250 321344271 321344281
    0x5030712090c061e140c070e09161d0a0e0708030d141803070f020d0210030c0305090c0604060810030c170d0e060a080603070509070e042f0715060e04110405 69
    0x891299210303030317044e41082070311001c9204000f03041140e0b40d040451682d140c84100103140d5000610603a4107450038120038a16516022032803c00c40d04a0492100c90f4000700100703804042035071103170583d8210401580c1304103440311311003421580142001100240c8600341c0d1000649034041c030a40040110720707684140305202049a80b28021040060705140040110743d00355141d031600090040c0d40100181d034000103007200035004200c0300401c000000d00d000001500381070b001600c102c0100c0010101030a06240150490f00107000820802d00894010030010001d4502c48206000d45240358030380000820244085103080406224581000b545a07031900103625508200c5e6080700c15031800708000d82c1c0310303000700c1d25001580c5d01c03198010002000b085807030382d40100c070041048000c9406204840041c1501049440c81400e03003210010000e0700405020305000041c00c40521423415610703900b10020703003501140c1d641d52000801003103c804000400a00701c0c5101000201100e04001d14104 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 321346771 1250 321345521 321345527
    0x60e04091113020d0623010c0c09150906080309180c07020603040f0f08130e010305070b1308031c0f052a07020607140f0706020c0105030712090c061e 66
    0x1054880700d01560300c01d00c6032061152103404480343d0b098040828400150340d2031040d0700804144070b01003220600c5000a030310700e40c414403603000010740190014041a04200041004210301c6120f1b00b03020b000d10301c000814961038050440108060300c041d5498903031031414001044107407032180905541100030480c900442009640000da01610019140d544c3c0d4500000c10b600c40d403402520050301542c12008200711140145441000c1e805ca102090355120a140d0114100b8000140560460a01403113503110020141ca840031014031040701260b6a00003040c2503900c1441c01d80340002440915003070240403409449900d00d4014800c1102d4642540c0310340b20f030901100c0c42011b034900340000315000c0700c804040d02c0f00e01c3e0300141321550300d940e9480c0c50000b00083d21884030321400f44c00c142500601c0046104004c50380340350007801c4454408001114a41c0c00204003900348460f212042008100354400c40b00c2c014070031200b84400a040c00c40141480101e014a88404112140c02c003480e107034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 321348021 1250 321346771 321346793
    0x60a0f17060c0a0f0c02040b090f0126030f0a020111071203050609060f0f030c060c03070b01050f180402031c030b0103050105030f0304050f060d0c1d0a0609030b06040906050709060e0409 82
    0x41403920b985c2c12140780c4001009088070052030b039401400c48c2d09002c0d9040003144c056041b50580d0f200103030107605524184004503403403100c40006400620005450384001c0000388000010f40c07000180083e003210350b0800b550880c2d8001c0c1da00c807900c5030f840c40c400342d01840b8042e00b0500441f100061450010001910200710804050140040f40b00d405160b0700d00f0040c021004070000c002d56198242e0500656480e0480ca00640e50308003200000a105e09040c100c480203500d0140946a066003080d68180d84c003840544201c1e010312440003411009410000d905591803c599400319003210114001800d580041e0041031294020642780903a00f4000000c0360112041a2840c12100c1c50700c1c40018614090350b0100c140350303820300d00086280b56105061a1814000410f00803890f18810705111142c102da02801000c00c80c0084140f000c00c030311010030360380070130000d2010480013460f58950082d24000d6a02c80301180c14204c00340702c0c2640003543d0762200401a1400c019420054640303902e181 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 321349271 1250 321348021 321348047
    0x6150904021309031205090307060b091e0414030711091605250206040807080618070608060616061d011418071a04030c0e07090e060a0f17060c0a 64
    0x99495400c281011700030000243c1c40e0580c5002000940fa240c5d1076070381c6079030101904882e020f00d003a00440c0a4500304442d00e01421011608000c803401040c0f014010380409401a22003001c05c1c0c06d00c5030080c20030401490810311a02c4580744040325001030054400025051103241c903448003110540c0c6504c14240ca00404140c078000f00004070f020079800c0c520328220b1019400500005021858000009038034040b1144101110403554800e482980e038401025018029a00f12440412210348074907945600030700300a005520746660103800805c0140150f2003102c1d000d464003214643c1d42110005d0740108500c440081c8011175040000c0902600c4c000c03d814180d012142900807030702c2c8100325000181c00e0601080d1950200f00396180c001d900540300850318102d569601041500022003a1405041140c807441c44840c00d00c0c1100d45004001404a60003541c80784001075200c0442e8500307c000c0400903001c10102410075030301801e00c00d005240d4020f6040802c5030085803a402814003c42c9 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 321350521 1250 321349271 321349309
    0x80408060406090b400b09030c0708031809060109090f05061c0c09090f0f0305030901050106092103110a0303021e030403080c0705010609060611151021020301050106020615090402 79
    0x401c404903203125090890136014106c506900100007040d0740020003000b055031048215402e16650343c484030398071701c00c00c040c5d00444500740280358a903003020714041c0d03004103050410340c4075240c07a0f030003909c200d500a25030842815203a60034400360382040b8802e008290b0000c01d0740c0390540f551f5201c054024240c2c0c0f0a18001980d508514000d21041a159a90607a40b1400709000350005060041c03036a0410780366030002c2d529080002804071302030300c01c1318100c5201c0054002d4840720038007400c81c800b100380c0c025002e20002401d032125194041c8600240c5134400d48006864030030b00c41801a8000d0801800900e175502002031001003900305000c1070f807002e0050b01c016540c1c0401c0c640280980b010354000001603007001804030300c0300c0c0c0000c80710317601512000c100c6105503410110340c030400c1310940b91200341c241885414400520b070b5000c1c4070031480c4070803004110b0083d254046402c64009034094001600030301c052081c41c102242d40ca01c5070354012035400c4803d040c550000351806050700c130141a1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 321351771 1250 321350521 321350611
    0x5060d0b090703020d0b01090b0609090c0c0a060216060609050402150705030f040f06081015050f07080328060f0b03070216080d0f021501030609080408060406090b 72
    0x71140400c103900c09981d01030460000d030302003450500c82c41364080c0a1880301500700031074034501c2d06080040d210001d40003000c4504c1900c030741540b942e003a80107100d140054040c00300ea103001300c0c00d540002d10308114441e0400b04000101d04188080b503ca50704440c0381681810706000c00360359507640241803182e80012983da198142c0c0381c20781c55441402d4507003121550110340014429803220a084c00c0b1107450711091825a50412a61005078581c044c961442034885d01c0e4040b6188030300050040c0041c000400c80c50302d6000d8a80d55803580003104c8000c9001119820b5200b814100c0801410402c220f031018040541044c1505840c012580a01c074005a40800007500c00d91080000380890700100305541602034460102ca512410300b00304182c0842c00c1854060b0740c82e07100154074044500300060180181e401c42d602d407005420101401c0d9001e01c000e11001c1228001884400d014600c0b4a4000840f03000c189004001240001c041609007454000e00d06004480340f49004440711604540d159 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 321353021 1250 321351771 321351781
    0x4020a050706050f04031707020d112a0f030d02030306010530041e0f020f010302040b0a05030415050903070f061b1709010615030c03020904050a020a1205060d0b 71
    0x203007802450005068203060800384040e51104c8444680594003c0d5504030319881350007403c29050106032201c0340103030b000300c2a6151340c1c3d11581004400400c080180e407003900b841d580c4241018120300304842d56017481c240e0304080b450094000d04070442d003039003d04908100c84202a46900008052905000b000541039000d03007101e08102070828450035507840301c4004034022aa5002c070440701107803501490400080200703040740c4040d62169000900360003117000f0b5400e10050045070940141450703000d110108152003600c020340302d180b00c5a9103107500e07440c041c00c04514900c5c800450200082c0382c034062113585000441199443c030f4121801d00d442c5199440e00c10001c0000c01c00c1120b03003510b0703040710b442041c3d4060030701c0408401d82510f03441103403902a8518201c030594413a0000c0c40a0303214904800e28001e400854481d4a241401400c00705158049019038030b044401901940e4005202d84e64150088001c424203001d03c04104811300d80180440c0c000603284c01d01404400000b40018 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 321354271 1250 321353021 321353027
    0xc1215061309030302070201020d0810050f030a06140708100e151302040906050a0e0108060103030809030c1b030d0809120c0a050a080310080a0807021020031b0109080904020a 77
    0x7490221030208200720481c42400c0040094128407801c03030040c0035130010f0740704c054420038070300b4002c2c211800750303407402403400d400c0000c1c05042e19211501030003078441280200e1018882d602c405081e003401d00b4102e00d0310b520000c0502900900c0c3d204106015a802e01280b2280c810310383c1c0c031402c1c28804a901da00e0241c00286000c41c04204900064000074000c00d0591654001100701c2c0d00c1510146100c070b031540a0407050003801d02039080306a100c0001000468803900041d83c000c0c141d60203591900344488402403d003145031103200c400c1125298130140b1401c042200340c40c00401407030700014600b060450b20b502d940203040e200c505240040380a0780c00305401e0040c50110b950050031504201030031310b032900064104550400c07558400c0d6100150140011a80d42081c2d5440790140345010703e0343d0708000c1500a005800410000050300850700b0518821076403440c205c0720001191241003503404a51070111120070070495034100002440045c4082c015920b50707820480b0096140d0102180c11 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 321355521 1250 321354271 321354289
    0x804050d0e031c0e010e03120708070812160e030a03091401050c0102040e040606150203120c0f070501051501090602060402150c060a020a0201050f011805091f0e0c121506 75
    0x1051000e045200d403c1d10705400646590701650281c84d02c80184100004040d201d1044101e0800740650801500c0300085482004103102c5215a1603d42072032200010030f218100111743c01982c3e030700001038903500144c11000c80310f501130084000304002c651942c0c0052003908244203501c003030140380c076140301c90360f0203001500c000c0562440219115035440b042c040d510642503505a80c41c0d0715210700818800314200c20600942c24580046141c058403c10007284c1c0c070402415641d04500511142c00d810340140010318a043c0110000729036800c01c60108074003010178941e940e05100c0f021004000290300801e005501680480b51040450180b001085d26445900c21844050041c1c2080040d440090743c058001c2c0b5032150f0007001980c9d581c0106a005950a0082c034400e14101c08010300120601e401140e41300311540280d80380c15440814a4414220000d40d00b80e01c03e44540401b60600b000300040441d01004130303500c8100d4032260b00c140d500d507003090705801e914441c544001207030384d2122019 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 321356771 1250 321355521 321355543
    0x90603020d110f0621060303070c14040906050c1e03151201090c06091a03060d150605031f0f0b010c021309051009030813080a0c11060d06150804050d0e03 68
    0x598560400c0b40c0c2c901510301c00114081115980740202c1c240341000000c0c1c1e080c03203620031b003c00401410b200bd02780340309061404550f0301c19100c00c8071000003029801680d01800c070294403951a6001074103072804001144041800c184424000c00c00c07040410600b0314940382055030182c81c004c2810326003502524000130003901038690700e0000200725034040c40706421500c54100c15235001c0b03160a42d09559103c1543e4146c3d000c113010384601d02203440b20010760801000c0c044005030050b52030700400d091200110383d0703c400300e001c0c12103080141042d00540410149800301089591421400645018a0b0f02c201038091220307202c2000d0780c0300480c0c3c0484486900f08003100e0006005080031005803211000072000944684045010303550007002003650580d03c08000c80c1070003810541140e41811076401503800c400340c5000070101e40c81d04c1e0010000c0c0307400c003040484c41900342100c0e01400300034001111f040181c054104030101b01c0c04120a085000e80d0300d0301e03000c901050340001340b1781070000074 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 321358021 1250 321356771 321356779
    0xd060905061005190516110126042a06020601080c03010510120f06090b1005040b030a24090804050306090d0504031b0b031801050c0702090a020f040f061206090603020d110f 76
    0x1c0420103001103101c0c0c0380c87d91a001d984402c09080303100c4101e81c452001c210f080d11340803d20004280021809100c0c9040c03009100f65024002400c110301003d207440c1c9038480030250700080010700003100180029455940260b000b80030303504100da10401c0c103a00300c1c8101c42001039032103a000c08205010640d00c4142d50441d0050007142000d0422550902d8280c0312180c242d43c506000003400d08081c0214030741070100a014181c0c0c1e083c1501d0b000d0810490503600810035400000307082030700c0400d214100145014140107a1503030b0415050601d4584050400ca010354008010603a51940c0041120103490380400e040400e032040718108031600e0480c2e00260f9032020701200300480401068400200c500c020802404240c0714003001c201103126924010350004164000100021200d800601d44c450752680c610385071680d110103041d111070300703a004480081c5d40c45034112050125070282c2d00180c040750404000b41d0349140c0c0025107006505600504046072806141010364800e080384800d590090 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 321359271 1250 321358021 321358057
    0x6030f060b090f16121d07030204051005101b1211120a02100b1c030c031106010b040504050604060506040909030306140d140f01020d0609050610051905 67
    0x2140c040094020140960300411840001449103421140c00901030fa000701101e05012401544c100c0b0b04190324801c0c07580240d1561032031750190702e811003c4134100c40300302e018001881c194410813060701e0003c0d0000804101e207120074005030359014500d4141c0c3c0b4440c280308079484a08a82d020343c4446400c40a0010116000c0404100d078002800e400d40d0100707981038607d0300e949441c01815500038031043c0e60041c1c1c07056240041c0321000b680131190880008048608015144105805110381580c0441c00140d800442e2001c040e00a40c18080004015000c0c1c0a550b062104a5100c0d00592003114802c0e41c40d00080340e0262500e50162002e800090b084c03540c0c1c1c0c0d4079200048c0103823281180480c00a4505100001c0e00c00240400010b05500280800309100c842c0c1c035540441002c1c50484100e0740120890005000030034401002d070410402c001150b01d41ca408407150858000601090090741100c0541c03004680c04000c03141040c10211032508201c8071140115100d00402541020220840d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 321360521 1250 321359271 321359273
    0x121308100b010f02010c0509121501120218010605030406232a04030b0105220e0c0108010503030702010807030c02010b03030f1819050d061e0501030302070609060203190306030f 78
    0x154000031441c1000b03803680180361544000480c200d81103172143c440098014031540034a0721b04008010711b0305c4118001c403140680e00400742409039030280d00c4040c0b500402d1001d4000c5044c00d541d1042f080745c8900c55000c0b0f03580f6201c0c014217513200c020300c0144056070350042c00c0a441d001c0e920b224075000108030b401e080c6150a070104400603105002c843e20b0220090f48080042d940142202e05580d40a1010301040e4071349001d1003c1303070001d50302c01e051400c907c0e42141205402441070003540f0312107800404091042030000341003c2c0041e08500e003c3c0c2c100704900c1e405070360840003481d0808482d180c006603941d0780110480c0100940d40d00180c1c14000042c400003105070742d00c080e10b0011040040b00b080b00700204104090700c0b03101031030030908081b20380c2c0030009454600c41a20000d8050768000c118111080100d10051145151018041d0382d600014001c8c50390410505002d42160300b0a240d08030304215010303580b405144442e4804504400000c030302e56102c0e0b00010011641f0240c011483c11103 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 321361771 1250 321360521 321360553
    0x304080d090c050a0807061d03070b070309140108070203160201090503070303030207051c0c060905071215110f0d1104030b040803010e22080a03060b0c1b040b0102121308 75
    0x30703c0c4035035803181c4003054020428242c003041c00300c01c45580d0340f142c5c0e03519020000d031070b004030000d4819035034035000d6032000103046500540180310840c17081d60382002c41810218000c108030b507601c0200d81041660401c2185c400d400000700c80c00000f84540180c3c0003070b6180f00407507030b4003414ac20150301070080c8074000080641640103031000d1803041c0242c0e10700855540401c070070304050303111902c005422140c1180218915510800219000d44107a403140f544449401d03041a01c160b030203e442c03500441d842c2d2088000ca2044d054500082081645022000301e0391909600440040d4150baa581d00002450300a01000300e8000b190722a551444901d02400d1101c004e030800d208140e03501c1641d0001620074200d18040e107007810100400400c0080c04c0340ca850005400c191101e00a1542d42d40d80031500111840240440c0380d20007000780403554400407000d0100342c40490850166040000c0004a82c2e0041504030342e051075050059150704800d8030703035412242e407039100321400d0003034070311b11250064 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 321363021 1250 321361771 321361793
    0x20a120506090109050706110c041a040c02070b0315030304150f0807090503031207020f07171b030309010302090d060c08041e05150901140907090509060403140304080d09 75
    0x1004906480007540c0b881201403e03200c84030b900804c59004940c007406494007400810401690003c111007403550300c2c0c8042400c9898000203550030b00403451203c515454140155802c0d40704900c042d100840c80c00c0a51281404043c01541c14004001c0d4941c4c500c0d20100306a4000b03007041050107401c0340d50f600000e0148440720044400007081c0700000342003079001c1d881000446074040d004500e0301500030920040000058007900840c010b0707904860031180c04102d400c01815001340101d05101e03005000030300d84120304121100078001c0342c444442541d004400c0e00c0000c5800e00700960f80f4074140001500442c0038000090401e450104084d071043d500c030741860304c1140328000f54001d01580100c100030000140c00014105c0d0300422401461505000340c4c1508101060b00221741c4101495a04010302c0b0116603131070071035105101c03c10840580c1d0041780e4000d4803600152504d41001c0e20001e0007010032114880740400c00001080030000171704100c9002c040c40070005c000c850b43d0b9146c00c14400c4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 321364271 1250 321363021 321363023
    0xc2b14031c05010e250c021c0309060906020705030319021501030614010b0c21090a170111044e020f01030b01020a03080603030d180314070b22020a12 66
    0x6031000001a05c2100d98100c3d88010b01401c03060540883c031080301c201e0f4080c010410172a045002140300d202068413441034581c055200741c40fa146080e0400900500c03074801c030342c00350003198050002008103460201c00c81e41c4048a541c421030b00e83d001d0141c180d01d1310b800c81440c81c800070016000002400000c0e031003201c4d40820070070207806a0f682e640031680b240c02170035010300580d0480100d460120b084000303035040c0c42007104540307828290030000003107803801d855200400c01c032862000c01102c82000e21039410400306c8228820b0409040805101894039150180780310f42c00901700d40030901b5200d0504901b07181c402c600c6903c4052480f1104441d0b0301c03202d40124020340070001c60f2074580d0f0181c0141030303001406900505040516803401c880c0500090040c03601404100200d42d6445a0790098441520b5050800c003030611017442d00801d02c0d603c200315480300304818004400083c02e41c0c60069003005203a071800a400b2802c040080c94016010301c000e500020302e82d4001400c68070307050b02c0b040007 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 321365521 1250 321364271 321364289
    0x1406010b0c060c1c0506010210050702010209090c041a1b030417190b06040c171e0c0301030c0e040206130806060f0301020903071509030f03020c2b14031c0501 70
    0xb515804040c02d41409613000031420303030021032018595070030141d10495011708148102c40c801d4500809810451b0b40584413400103075000241d01840d41800c00103284c100c0e0300c20030355500d007074500320304144411071203042000b9500d07000a2038511541c0c0310501c021001184800d0b01d83e82d03075407051316080120701c40341d05107054060200c03d51001c66410707030031152880d04115540002c4d03440000b080014200c0d10181d41c1440a04980c00d0754108030710020a02c0350b070780b130813240212440190341d201a555004000c00d8540104100520000303100c060000708880d0844c81c561002d403602e10001d000c0c0e01a00e5020741c20b4000e4820b00090303403000010501d02440043c0e80700500c1c1410001070500340d200d003100203a05944418001c0181c4034082e44031030300721001858500e180075140c7e50381d92044030140e039060b0300503400306110710110716101102101009203400803c540b11140485d5079000c00c0e40e80c0000c1e04400d1154510000c2400900840301c5c104644040d54200c0401d00448000901080c0691300803 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 321366771 1250 321365521 321365533
    0xc1103220b19080f041104020c010906021902010b0d03090e060f040222080c0a0e041a0a06030204050f0744090f0d02030301140d06020d02030a050a0c0f05071406010b0c 74
    0x104e280c4581c82540100e40015030644002c4104c018807029500010103200d503503680755035080c0411054400303002e01c001881e140e0000c100890b00d0090070349026000346071003103000e0342c0705000103a080320294080b65040352088000343e41d914006019003407644446900030707000203110480350384032500e02c00400039210070b0741241c60b4403606041c4c1c1c1c60a0516440f40c20040001083c4030b805040b810103a4070511541400c52a10740e510010a1102c105550b03603c803040e181c100500441c50b041c004c480d4002c0c40d4010320b140c1442d0004004005401e0f41d24185170f08406c0b228060303007c0d07800d640000313000c05070100e8454100c207980492803030015041f01d405c803081c0941d0724a40307a5900040b0300d096809200391b0055040da42800c1d43d400301c40e0020b20700240e110051055500000742c2d0380c0050b001072000d02000584a00d45200d9000c10f68000038004038030720b0720341403a007401e25420400d8100f941a091038036075125803aa00c0c1c0000182550004520355200303100c000146c9941a600914000400740281d0301 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 321368021 1250 321366771 321366781
    0x2303011118100906200a0606030309090c1404090c021c020c120609120a030b1507140109022209020405010311030706140a120902220c1103220b1908 65
    0x180e5030f40e407405071800043c4001604143d001d0501d0001250380240001d4500c06032443c3e446c7d0040701d81c2540704070f0204243c000d040046581c0351160b01d104d41c40c507041c40581c0c0310342c00300d8100e07a51140740a40c5196565a00703400502c10303c03c000d840140d04504112000c825401003020755642c0d091050309100e0301210015014400340821078034080c132840f000400e00601e04070442c581542200c41c2c40e004040e541e41005134556075411100240b00072046c4200d59850b0103040143c1c2c81d100b00341d9941407a070f0604100c040161070383c2140303a004040d0821001d0500c5c4000080102904103070401a40c02820400084180001c40501000d80841201142c2c1d8180d0f4818090328582c425007402441e0081c02c0c80201c2c011401058664a100014100040e50740d034280d00240c050000c0e8040140042400d2641d800c581c3c1c40c511480003061050304200280012111140780d03644107002c42d01040314000601079016094112503180944100c4020503140c002441c00f018200d106201800c5c00101c81402141d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 321369271 1250 321368021 321368027
    0x30b10050703170a020c1b241306030c0e0303070209070e010e1818060f190204180e0705060f0301230a08010515040504020d020904110d1109010f230301111810 70
    0x847d44200c0a42072050320488400a107105103000d80d0418020342c0200b102030385a150f19001c59000c1c1889032000248080714010041a56848201440c000d40c800c00241000d40d807401011680321078185484249905c151004a6020360035000b050f4000d10b548409650000401d40d1551180c0c1254071030b103402c8201640c000d984e5100a950f00400655500f000c02e1510620043c0d04004150740034000d440c0940d03541810103d03034622a05084042c3d03a816000500c81002c1c01908010802110b02a080c618658804452440113204510000000d040c0401d0300030440301c0ca11000000091852005d15aa0700c10785000e4207040362101490a0680c0050556242a100b094026900685001225901c6609200e82040050b006841107008200c002c0f90680c1c620300381490080c03198840707440c084144c8040c800305142c180c0140704501803007401404000300c0c940154451202d0152125103404200d0082801001d2152042d00c0d02d1400041e40c503005d5805804c40f0a080005450440459071004012 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 321370521 1250 321369271 321369313
    0x1505040801051015110123061207080c060c0708030a08071b03120902040f1814010209030c190308071113140a0c1707110706030b10050703170a020c 65
    0x101101031015096070044c1803069610b4203842182400014444a60040e4007a10340400540f006030b01c21003a04205150512205222680040e140103050a07418800c030f09807500003180e1310078054000400c008650100801080008040000030740e60385903203002e0010702a003000c5031003d004c80c03004070b9541f122101500021300702c95056078a2403c80042ca040d00000b40a0782a41a644641c0f1000c0050035140e40c0c0c45100c41648d100040203114003280c1c030b81207d948012007900d1850340d1040c8244122920040b483c000080d008881880031711b82d9580c1130741d4611040d034001805921022075140b04015904420a101c00c5045a040c49003494640d8044250703041c000d0400110304c0907001085600e911900990840101414070f0203e43e0b180754640801c150040302d03004c0014940c01d484461514091088801500c500c2c41c06101c10040e841c04a101d002c90003c620081110008026081c14400c407940342c0c50300100d21141c055800c1242c0004065006000c40c01c040380100020010010006021 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 321371771 1250 321370521 321370529
    0x30909010803070312020a030e060109022101150e0102030f03101d090a080d06030b0a050f0106110307030c1e03020a120c11090705041212020c0a05011e030615050408010510 76
    0x607104817240801c0048003c0c2d00302080c2d040a00d901c40917001480c080500c0362a0103001212001070302c0d40d000c40e0170160415104041c000c9101501001809818025981c0c2660f40c0124200380140c500807100407407445c85094401c11034003c011080c4015003124001d00c204890f050700696150403500704903000314103000c0ea1824140d6000134100d5000030210030143c0910305000400060380d0f81d90f42c4410060b80421102441015511410001050101c00b2160b0140400e85401480300003020346c42541e134451110041d06011301840b882c001c014054a0083c48400441d015070a85401c81c98065540d1140a40c1124541504c042c2c50f5012449100328103107ca0700310768017402d0700c4c2d4024280107441d10081c00c40410042c0412010843e40c1c2c90031651000740d403281c07095000e10410310340001d0502e211107000503c10301512004015070380e84025140c0354803900f1549440303c10321011065004060030741c080d03e291070502e80341303401080e0000d001e04111042e6900911980d62585d403043d43e00c00003802 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 321373021 1250 321371771 321371777
    0x15010519080c041211040513020616150e0c0108090d210902180f0108030301030807020105030709080f03071a0108150c040905040c170c09180307060903020309090108030703 76
    0x4491030010303104101540c0c210000080b120f14050304c0702c1041c40074248407138080e24201c0c2d08440343c031a50706007407113130300d900040d040440c03012007034030f90300040181c820942c1e4040308141080f031100c14000c103411800c98407030220004101004c000d81d0074a482d0491200e4560229107040d00203010280e001c11a01791140307031543c40f150f4441490094000120003060010b00b880d56030041500140c0710405109450403134003141406d070349480300f10401d000e0070582002e400d9030428001000013551500640703128650900740180c40f90b403821070484081c0c4041d4071500d02446850030035070300180301000405048c1d0007040c60b104e040c0940c040d4654464400c0c40380019540c40246010007403400c03440001e80289502601625090b0384d2030300c0c0c4040c0c400943e0150b400c02001c50081007240042c0d852000094902005004410281130000320040703400bc020202e480c3c038075442e0f00c020000c00c2c0129a89690f07c010300f002010118100203640e81c02100d00b144c055030700240081070030103001058a20365079040d9 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 321374271 1250 321373021 321373057
    0x60f0405102015060d030201060308030c09191202010323040809011b0b01270219080a09020d1403040b0304060f0605010206040b010b090609030d0c0302010b2d0f03030301060206150105 81
    0x7000e001c0c02141480e070075021556501c2000c400600c01038000c40c001c03446640dd10343c9510160041014142e83c001200d0143c080e401d0b01000704c00d14060690701c180d502400c5c0010380003580c00324400075841203800c0c80904840c0f40e08010410500201805416000707a8421803505031180f0030703140c220a440400f9000f02010001040940850503903180300030bd1840d200d9560035a80000c0000b80d030801e10059032401a011904000164400012903002d11a0001806078ae0080d4010603184084144064980e05860a040c1e8121750104121401800c90741505a0703203140a0400400900809102da410380e810020001080d61000032a54043c2c0d800690000c810f03407078816018190313070101c0001030700014203004c2040c059500f800001500d01507601e550b07604d00500d180c02421070310f1011623180f05041001c251140859103039000108491543d081308010b1958000240c000d550181c01391740c1c2b41c4030001c008500c032079001c01e030503004011100d05060340800d10001510300c0d00032503802d0517050a0031 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 321375521 1250 321374271 321374281
    0x150103060b060405100e01022a01030c0201110d05011404060602061f1508040507060315030204020c030706021306020d020114040b0414030f220303020c060f0405102015 74
    0x6501c5001404030041c0701600e01940c030070100c1c2642d03101118210104903121000d008650301440491020300e034a450b000c003040d1151440c000c0b103801446090741096a68041c45100d14000d5200c4c1c441c02c42d01704550358a4026104203180940030900500410b404c103034112480c00c2c01d00e030050308155200354020b08025540c21142c5001c030125464050f1001403d4070001030321040000c0c1612040b60301e550751900307510b0681480d0345009400e40c00300040516110000c0421020701014000f620790460300543c0d40c50b002e04443e0724501034040050121440050440d000b103481081a204032202c44d0241c2d100703682c0100c400c2c1c1c225441c0d482c0001003582500001000640040c0c899540300744150050200201003030502495034001c640d0800c501080041c000c82000880884d40743c154120700920f041841c1940e900944500100310030902802c0003007111100007003184140c1e0090074003d005500c2480044030014424113003d103200111031101c2c8050782d07000102059407041e007a020303110700c4241c1e112 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 321376771 1250 321375521 321375533
    0x11506020a030c060b130506091608011703090424140109150215040302252313020d0609050c03060904033c0801050a0810050c041707090e150103 64
    0x1100743c0c200e440d66500ea004060070354840c03615a0b450861100c0014a502e0400140729a040000d851034401c0c20090301c2a940445c0c1c407401c690f0550300410207000c011840c0035140784c5503008a58406500a08003ca4540d0300c0c520784210080c0409400c0d004021a66500d1406c4040b0307002c0e07048140000c2040c0c0b01807012003800c480007000303c004c038411500403980c4000b00f540c030302105031011001030700004503121400003e00c04d031180000e5801b1211100d140b801e20b0070741003800f1520340d030220100740c0c4201558558902d012000d142607045001c0d99540e500c000d82c2e40c000d002d81d02800703120030700d4000840d1314041c0c46000e80784903040c0944184d540381ca07552002d50740d500c0307600e490840103803075002044290001d41c85100301d040b810074603038440d454002e0070244c132086d0705030030040c0a040c8212080047d00000210300482c1d90112074006141d4546002100051049410009500724885800394042800181c00d0f812542090400c0080781c0d020811551500001c403038620b0500d0310f5100500210310 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 321378021 1250 321376771 321376787
    0xc130e010b1905041508010810020f0d05070c051c08010f1404051005190302090903030f04031107090c020d031104080c010e061605070911070b010b03041a011502011506020a03 77
    0x6441c2c100f95040550310512200c80c0401d44014500007858200104106d401c01c01900039130141d00c1d40158104048510050543e0041c804000d00d45a142e6000c10005801b82041c5040a40c002091b83c4112618403a12031594a52008120004140c0d01c00003c540903030324038440030b171001c0c0c2840c3c051503841d220810010702005880d180b4a254110000182551142c102880c600d0807140c049074141d10394010084009002000006035410400812800246079504207600070340c9814001740c00d400700c1c06210300e00b01d02c40c2c00c28400b00d45061001d09280b41c00003142030a00080341e81c00e2051725461500c0c060355005074400c0c00e00315032046048407480e6000d5104a1a500005070a060400603454032070101040c0800094444e500110020f03c40c00445010300580910100e414030700c4c25210f03580c2c00030008014403030182c030800c010000c42c0030804406465207000d07250f8896151996150300da800440c55010078088050f40ca032680000c0410110f8400c4000c03a072507900605030981d80c5860640d0203075 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 321379271 1250 321378021 321378067
    0xc150705030c0a0e04050907060201230402090c2208010e0c0102030d020903010f0c030902100e0f01080408090a0303020f070f031a0408040b07080301090f050610050a0201140c130e010b 81
    0x204c2c100b941c2c40c510b82c449104151146038114000d015041c0341c00742c06800c40e0048940c1c0319400244140210038a000100d089c0d40080c0e050750641c00999074122101d40300d0065150700c500c20001e08030101058001e0090078016180950020040d12482c080f40344c1d80c1c1c10750b03200705a000d81c006002528a9400e50760140009102c0580080382d01c00d00320344600d00312541d1a010001003a560914081981401e1421200c04401420451407100e03001000030304140802c140b480c104030215000508100504c019a440e900c030186c00c4c010082c2c0c0b42d2030702a484181200585602d4403e6040c000b0b090050352440303004407500402c8100d00c070f000e00560800014001401904e2000c7d0030400000c400f107542008210b4070307000d007001503100e5042c000610251140403880712a01e0382410140314545e620b120803110000c1c1982030069407210050f0081c4c4c0507000940340d10350406052400c00c0024004500201803403103003141d48400315038035a6500d2503004400e00130b2002c440401d2242e007100c0511a461180b0340 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 321380521 1250 321379271 321379277
    0x120c01030c031d0d020601052205072c0906010e0a03060b0f0603070f0e040207031b03110106090501031202030c0a0305071704120c0b04120201080604020912030c150705030c0a 77
    0x804400042e203c00b1400100c00000d940c080c142008205505000c52405010101c6001036100071090000702101d0207007034004202c6540ba00858440b03402036601a0f172400e4070900c0c2d07603a82c0d003601c280d4407a80b0007100c1809000b0740c5408000741c0950701c51144140040300081a0341032550031358640300024a41600f0315500007020700b105100a44c0d99130f010758800c1e0003541d42d006140c0d2250f8001082c0c400080f00980c00307140107101210009400008040018103801009958000745050031200b5101c1141e004400394a403240100300c80f01d054000300c1c10b0340e01038203a13a1810b1000e00000ca903684610701003403403240c10407424040043d00c15030003001c156018900c0c01c2c1d81c440b06584021610b41c466032001c81c9081e503201500c800c0081c100010402070024002450070185403000e02c07800f150010340024100300740d0b03400160b90769640d50705a4000d09006003141c010b00000c0c0f1600c3c1d030340ea80002800700310b80c400c3d15189580d1200200401e4070821446e6174640c01c40d103d22406c00603c1e0071201810042c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 321381771 1250 321380521 321380531
    0x61e090f2102220b010c0f0b060a0b04090911060f0406050c0f060709180911010c150f06170604020102030d09020117090303180f060126030d0b0f120c01030c03 70
    0x25950300f614099104035600d100b054140718050680040f00c442011050500000c00b0558001ca005011145001600400d05240c41d41d50500081d42c501c0c00c60300005000c10000c100881c408144c2d61000c824144551041000090310b082002043d01429010903550501080180185407240c006002101d44440445502000c0c00c294130741403200c100c0b40ca4000a800417003c02800c7e1049010012a2051540400c250070054680390f46003400003c9185c14001592030344402c101ca040c0d554044564002401c0000400c2d07104000c000d071640d41325013038040745101c81499070b20002041a0340640e03030580003180381401d03079000000038040c000420b0b8140041594901e01001c0324911a0344035511707401c081c564902d8041c884480708118070b00d400440d50301001c0752181064001520074150303441031a6580380309000c5094030410794407250f12020140400700310440e0803405500100b00c080c20442c0c002c0c0c1840700c490140590040341d5880313094039600503c00c1500c51b5000703034000441000d0714a40419 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 321383021 1250 321381771 321381773
    0x30c1202031e0a11100c06150509010f0503120f0406080c0d050f091b030703020f120d030b010905010e0108040303090c120b100e041a0718061e090f21 66
    0x1040a035644101d04450300603898043c1004507200c8014040d0b034013205c00c411401000c0c0f03c001c082c1d00072010001c2c00f41c0d580e035030380c0c040000d14440d42900030079004000099540e10341401000911281c0b1a41e40a48582083d15032980b4205059500070544132030414185490150100d40804020340302035900c03201040504081e41c0341d4000c06215880c420042c98007820403603112071420341d9868030003421011102d2906c0740c40c1e81c00309280b41120340448165000d07003003813000a401950035440326182c9210f250f5124440c2c42c1c064014a840700c4090721901d00c00e136506d400544000310001c0c1154002003600c400100064060792040c10352501560090002c03030740b034007250806100030040580b2000d00b51010059404072123004000039003500d03a0b162006041c01d48d110521083d1107968400a001004005061503108201c1c0c50882011030320503d07549695500c0182c0449450081000c052a100d11161001c601408409046403a80080042c6452411301071401c0114440c10854410281503075502c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 321384271 1250 321383021 321383053
    0xd0f020405060f03061e060a03110904020a02070e0a050f070309050c060d06091a030601031203142d010f09020a090b031024021207050a0c0f090e0601030c120203 71
    0x1016222483e06540303051500411600600031101940908080030382490b068850900b031302e555006a00300403072100000f03071107940c49000b0380c0310a94100344041421401264005030101c21111100d00c22943c4c0d469400000081d10b00172900110688442c602160200d4882d0303000858581c09102607c0125080c0c00010300c4692041c01c01c032000380c2e1900c40501401001740719000225402d519058801c6401c580840d031500d905100241c000c2880035a5550664025007244841c1481400c1881207440c00c010900605003004020380c14400700c000e1500c2c0610564a00070703058030500450b00391011301d0291010043c2d8030108105080020322403000554804120203980509416085000d4031803c02044000881031181c071640051207403005498000c1c1c021520148940c1844441a0f892426007042450171001075001400c07a110300780c0c000340e1915128561010380350196410700c041802400c1e002d0b035a810038040540200f0b043c100c20401590341c000d030121147c0c405015a03030101160351440c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 321385521 1250 321384271 321384277
    0x30e030a02100504050109061b0b0402150c03030f0906150609180c0403031106071b060e0307030f0201050115050d0e1204140901050a03080d0b04060504111905030105060d0f02040506 80
    0x3900110f240441c09101c190380140903040641803a140000d800d4404820801c400c0488202c05400c10031800c011400359210008101c1e8003040501c586031b80d13082404901a40c82e4000c44408034054122404221900c41c0800c3c0c2078002d0032040400304a41003410100b00081c2e10136071141d90302c402608004145c1412000110b8414911040c1082e00c542c59414050011000e02c0608059904002c0401140303d80041e40b201565412000800b40c00c0c0603450400001c0040c2c14502e02c5501c00441d40404040e4808001e5201050581c000d1220f40d07603882d40131035000d407669640302c00b03e1018030442d001302e81150304c800428031701241100e07995602440112040c0d80280c01c02c4154898410109840d82440c0c0072450061000360b40c240e0342d16246456060343c0d40034246001d4030054130381300c00c00150742d00d0750030050103800014010448040c41e5514803406038444481c80052000402141c404d050164054a0480f000504090714000c410f00b0850000c01614200e016520340c03c1c040030410b612100c0c05 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 321386771 1250 321385521 321385549
    0x15010806010e0d031709160909080708070f03030b0a0f060e1c05100e030a0c02011b02090705040503010506180c0c070b0316020c040c02070b070602040b0d060f090203040f030e030a02 80
    0x25400c61403001411031100170401488a001d0342d00c8010902c291008070340c01082183c0070a03000044480307483c600440035114141d0094251100490030206204c0ea8901c07601150303210707803003c00100c103000c0103001c010301e0b880c41651070a40e2004002c11001e4051940c400c09200c0040040f80068120042d0f103c4d02d801107401a1074136400919000c903101058410150b105688000660404020000061140c00c10290080c100014003100385821408a9864046158002d05038491458043d000424581007441401d1096003032402080a44c14803110505850401050b0b1646903070b1030142101c00c1c8d61229043e01c5807071040b0840024491081000f0f14041e6500c20b003080222140d082c0001d00e441d245c5807010784510324002c080607445070001411411181000401030301c403822030810f400240100e51250701c0800300020070310031b000101d51001d003d40d2031900790014003e4413110801c049000844008140d0a4800289004240108100241070000804440c210000355020030419407250709 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 321388021 1250 321386771 321386777
    0x15040b07030206130f0f031e030c0906030603050a080c150103050307061a0306041b0e130b0726060a051e010207050d03020307110105270a06050315010806010e0d03 72
    0xd0a8820998144041e94001104001400361010162078801525032a12402406400500d01000825004044040349800d08001c0001d8400e011300c03014000d444542c00d1000000d0044001041550003881402d0503a600040203160500c4280e03209131480d4403601d960201d0b440740c80c5000302c1008e99188410b020314868406951203541c0c5103416010795680700141200b21810400c00c0d402c0751400165185e006400860300c1a00c05948410815001516000402c550028104011812152801c291025403261000c0b241541c0c5d403002c101c0700120b940040d22005503040603166403030340e00c0620440d044000180b07980399540c0e940d000a26603141e6080411601858a410306c00d840d03070103105440c014102030f00e1007690360340107590080d1213103e040801421126480c11282c000d922035000d507020b000a0492200c100006030880d40b10b0002c200b51180c1c4510042440031030320a10450659000f44100220101101140030055925200090566041180d802010300456554549004603640251 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 321389271 1250 321388021 321388027
    0x1060302090a05041e0c120302060f070201380a17160b0f0d090512030a0e01020712030221150103060914070c030504030b1005100f0f050915040b 64
    0x22061040e0354000400d038500e15803030f200810000c80c420074980300d0042c10042c0f140c480d04c411441d207200c0300c0b80680c00c8252030b05407405081c2d0400d074002071085d0103a1408402c250007a070710100224240c4881c8414010325020218102d400b80307120310300e00ba0070243e2062060322001c4603034010038840000c44d407100304280d12484c0d02000d4608180030502c00c9801c00c4452200703150400c00401124415181c3c000300030400054a4180361a0581c88001c0c26580141600c03001c0c10240c078082d196420507500d60000c98501590000c04220510845141550181e1529036215034504198008d41141c50809418202c12000d00102c03c00c450041d40308180c0d4000d40c15001d51007200040469410b0340006441d01c1c0707449201c0c40701c11003000c0281e40c00078140c0f801840d0180d462034200c403c1d02807030f030004100c07400c8242407141081204218205840d8141c0302100200300d00d03001202c41c1c0c14a40e54036000700d1840440d41c02400c0c4500f0042880c034501610b40c88048140380c0003600b0650056010300301c6c410000c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 321390521 1250 321389271 321389273
    0x51006031505090105010507061d0d12050105090f04061812140f070803090f060c030403030e0c0109170c0604030605060a0609080705012105070903021906050301150c0b09010603 78
    0x9403158110303801c09615500e0425040c070000c10269801800f030241484000309010040200725048030005054a2001019000382c00901035924103404800b50049400c1496111a45420788101c60480d28000c001c058941c6a40f5041c0e44910b8020704282c0700079131a00c4601c4185402c01401e400400d1091160300c800c02c80c4007800070712481c2c0c101ea482206040410201119a034410151b441550304080c00c0e540e2503d910060074030f42500c2480748445801000c1c10005c008032244051071046001c1d0314140228249640c0c0640c4034812004014041081c01038180700390401141c030660103401040454450b05010000100c0c0f613000780e8411114a6151030800c242030030a916010000c101504100740e1190410f0095500c0308268016203040002c0758000c1d03c00440d84c0b00313150801c0a41c500c02000b26007402c11004002d81514003080e0300910b42d103500d81c020003680c50303090300455400c0d41c0c9460569003804142d10070341000105903410030030f410b40d241d03012070002c8960600a40803d8000203071241340d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 321391771 1250 321390521 321390527
    0x303021b07051002010b28050312031b0316030905071a040305160503030d0509030f0c1014160809070302180a1a0a05040b0a030501180b0a0204031106030702030409051006 75
    0xc888074503811641000f1a04081c0d442d0007d560368030307500750052038602d1140107400b1004606282c0c4015071511403070403e103060084400c000c6008090f1040750f80808840c00341301c01e149210503600501015180c0f0080d100341c5200390b018400f91807240c0c0030380b130702166142e201c1e6015030b00e03644100540000004003003007040400c1203681d112401c43c0b0444066180b80c040000c2e00c81c010203ca0b00c2c0d99a803100700150021100303200300c4c0c6411902408180e15094a886010703510301d003d80c01c4d1913049140c0079280c410480920307012446101e600c1c0300303042c402d43d02410883c0c814201814064031845400804030040c1d40e00c5030308042400f0748a81050862500140101c01ea42900c000002404100c00c6000b13525100c450200c020f0341c00588010403040e00800104182d02030961018245502e13140c150321400c1490480034400f680200740240b030688a10300050704070310452200400d84000258008564240a00a9640040e1a0050701e080503907030001d1205590084804086048400e2018095660 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 321393021 1250 321391771 321391789
    0x50a05060414240909011706010302060703030e0a030c1a10050d151d061b03070f020a050d050a0e0f0d02040506060c03070c03030f03050f06011809060b040603060e0c0904090303021b0705 82
    0x1081f0110481070050004510351603002c18000039008960000d22a414140690401000415654100c0c1c5021040d41001442996000c03004c503010b03000c501c0e5041141411580783c0f40900e07820110049074a1070320082103012030035000b0448211344622030080c0c04010901c60b103d5041c1c02c06190690303003120030030041d00b00000282030444007103001030320050300221441682d0380407104d410074003080d0b40406c44c103138580f8504004c01045482003043d841003007684a0003824511100e501c0d8400c15120510821004a020441182e005214841d1a9000d460f003034218940019000e00b41a00d400701d82c10f07016003103512805095a0b0700418207001c104066025026401120b0306107810080e6042004400c081c900703019203030740c0c10040320512002405400260020040c00c2d2141d040142daa03a441d1954410b401512035030020034030b40500043c00c0c420003003d1a00c180f070201030940c50560114100401403808110580c10141e003441404c0480500381e4000303c041401c540180b24041c42e120421214076 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 321394271 1250 321393021 321393029
    0xf1f030c12050115320603040f03090b180409030302070f05030304020f1e040902060d091b05120a030c0c0509010b0c1606090e0619150207050a0506041424090901 71
    0xb00c4c40c28100149900211840c102c107070042c084a4007001180420028040801c024903442640041071104101d034090011035020300c0b0303448641816a0f11005911756000721070724690113550000c00e4185c1c5140c41d5004844080c800e050050502c54141c441a01e00030456504440651000042c40107514100468008610080300c185505080703040c0303402000404d800d200c1e4002c54458040008540e610070075078200741c500f19810040c149250510801020155402c514401d500100210b5213081440e0021050503802c80100340034060b6590856100206400175110300c107031480b003c6032683e6010001070080010440340c03900c403d80c0f80c005034100a0000c1140b4a0300701e075140200700d15034002c0c0140c030441e0f1422128174000d680d41c1e00802d480c584803006038a40041088008136103046c12000f1400303040c500d642100d49054603502801950180c0780542030348640240700400c45500480384070241940064880309403140d403002803844041c0d801050300d405800108140c110340c1846000c542c014 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 321395521 1250 321394271 321394301
    0x14060c0705150417030a090b0c040518060108041205071205040e0601080103051903050c0105181011190201090c23060906030a0203070207080d0f090b030f1f030c120501 74
    0xf070074150794250244400c680e003481d0724003021000440445c00c580c000121290040981111440c3c4000700c0c40701c552150042031300c541c00b81203040342c0304014a030300144680c006071107021080e252601c4555814002500751400c0044c20461013000500c205a150984019034840546507820081e03711101c0d0700c0144803e0404c0b50f11ba00420201e080010100020002c011042c005d141d5141411290740c442e840c3d003c0e1315903003850140300d0310041071105907102103901d2081d51f09050884001d50151641201c400201d01030038003100080c09024400001454298000000c807181e00b655840240800303544090b00060661420541e401e00c62150401003a008880c01880e042c0341c000028600d020107840b0b102a603601200181d041c0303000b00816406456140d0884580b0000c0f000010040c0078400000800650f0541c00020780794892030540740650b100d0380900c0b031103035980c03040550010b0700224070200d03010081e000040450588031584000c0d10189900c801d42184600b850fa00b5110043d00ba0546 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 321396771 1250 321395521 321395563
    0x140715030209011205090a0f0506060306070f0e100908010e06190903050708030a0b060c07080d090302030607080a06090204082a01020a0f1b060c110102161214060c0705 74
    0xb9a80e1300601c1d40c28500c2d114000098581c43d4030742541d10388455000d00408801c1d0710701d180d00c00e00000140c0c841c802c00c8202c0840b602560b0b090343c1224200112848032002c2000800c02904900c0d0011401c08109054a4000420fa81d03a481c07090039a5035100b40440590421401d0000844000b1200d103104011001b0038840d11045942c02055407040d2640540824000b0000c01c2610090390401c103030744c2d000140929211000b1889054840c8428460120309108200000494500481480007143d800802822b1503654a0909481402c0021314881c2d0302e80d0f440301d0208060341c083c8040d1014000d0351000701028190440700c108240d9140c0481c0b600c02442041c0407175903030303400203014078201d911116400704409075141c0b070382e4900710500040c2405041440041684c0383c2c41400385841c00e0060500070415901c44006a03103440e0005280007401051800a2003406a40e6884d05201c80c841c2e018080604024540340e0304140040d240440941e4000801c08103022003040f45010800c01c010111032 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 321398021 1250 321396771 321396787
    0x7030c0203070b09060724020406180509041a1b04060e011b1110030b03060a0c03050f0601052b0c0207170111071103030d050a0b03010e0309060d0b0a031407150302 72
    0x180d503019014000701403040d8554803240c0c01d00305140c7d0300d03e8000709071300554940d502c808001d055000c0381159400c0340c1c0c00310307100040e20346459108203009580014030060301e42c441201c9200d0440d00101042021240411000907080300000100001c00c4245c0e80e42d410303403211000041001c4046041d441100074002e20b0301001c03422008241c042900219801821481c2c1c05d14150043d00d104509560326000d00d0081142d10344081d003100e000201c083e0350030001d581d00c500401c04003007010b43e00d00703000400600103061410301c0c0503529281402d5080311072100020720a0410252040780b45c990740184c009041c10040c0482d00015a240641c4000c001d20905d4240d00000c0b0301405003543c090140c4e0a051092a21034400303004882d81d520103030406008030700d442400503000c1c00e01182301d540258a071040044410b1800f0047d81c05042d80200100c0c54207807242c101304060000c40701c0b460b6021415100c004001051410754810103502d00e0b010b0303c52140307001e444136140c28451604c40140740c0100320b00d071 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 321399271 1250 321398021 321398029
    0x5090c0d080d0e12070302061006030c08040b0a09020d1a1003050c060d0f0e010c2007090e01020c0616030b0a0b03040303050c0408010f06050a050a1d060d0807030c0203070b09 77
    0x401034041e24100003000300e904a401884c201e035482d0784404000c40003501c401450b80c0072510511801d1080d001c8004265100401c8044403804c1941c01e00007540b4501280014642c040915008040d505020607035089a40004008045441c001c81e41040441e03130400c40e000020103159880f001d841e1078868244d2960f03c450751900c1126000d9441800300190261041c08281c0c032130859440c0b0800104180c0f0681d0000078000d0100001d040007142208200000c00c2440c0e07080c0452030b100d0784000d04107403442c2c031945c00040c0c0074000710b0111039502488446655041004214030810300e006085402140121014045920000c8000d01a0303180002c107105c4030b1071500890b0b800c66071502e0002101d60b10011003481c80c0c0600c0c2c100d44065403d0000718441840d03641c200c0b00a88004540b0200503d0f030760070812031a140188a04074130150300c0008100c1c40310f1084034071648620b01509410b184180795885000303941c084d100490200760008040c0013035060800c0140042d01c5003814683c54000110002 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 321400521 1250 321399271 321399277
    0xe0a060f021c0209190801090b010b0406050a142503230901260c040305100c020613060902060304302703050307060207031202030c16030e1305090c0d08 67
    0x3140080d600058041c106484a4150080d2160017001d050300341511a416140604022003041e200c007400d210002c00c2c2c1d076401d10103c40c11190503407140f620340f07812041c00b65203c541c0c100715424001418080c4000c0c48440e22110854200c40c1c106030b03682400545006066092541b070038000c01c600412286036a0040c50007210000c41003402d00080d0492050181d00300d0b10044415010720350401c5081c040306501080140059a11403011761b40c2c40c159452076801100c0c1801ca003040182d00c0000421514400310001e90f403581c0c09030a0226081c50683c0100380554801ea80c00c5a02d40c151464180c0300303120301283c1c068a490f000580c6001c4d0b04440310f0044c001400100c1c0d0303281c0780b0300d500c3c40a20880031801c1200d008640c005d0980e511084a820840000d410002c019004600c0e261001c03101c0e00c1040c8200da2044800b2040c080c00e0142c031034494103a22090020813010300810204040142da10540da06511200340c4202140515002008031304214406d0843c6004110100b12140003c0c007503070507 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 321401771 1250 321400521 321400567
    0x606010f11300a0212161b0501020c010203180f03030c07151101050615030603030c0f0303150907090612020d0e070501020111070c0e042303040e01171b030304090e0a060f02 76
    0x4117548422071248643d8103640c40c84402003100130303603092048102c40390222440c100c43d000d0b0251140400540d006980300d04c11080d0810b80c01080c200c08094a24007007001c031802c1c0788050101c0b428070002039082481c02d1400d0700300c52121000c0d402150f1846030700442c04018904410000d2180c0e04114011605440c0d001500711900c4802000140c0c0c981c03400c0059945860b120400c0b208031007a002e261545a0740250740701125400707166041c6616052142c0428040d05150b99410560307803810b942222401070011405541039020081c0641c0505d0600509001200c20f80142414520b0500007a085801c0b028141c82000414403d0401044c4250010750031075032080c01c010280d59591411000d0010103c1003100411004d03c80b200c0380320720010151098803101a0000b4040e41c03220003c41011240303c0c0d51900c103030b00c80b007509540380c00c440c01440300000000e400c40c1e04041e110200807044e22115060428250b02984601062003950302a007a400d4280100441ca841144541512003d006041c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 321402877 1106 321401771 321401803
    0x1b12010606050a030507020102160510050a1a061b0a0c0f050102030405091302010c120507061b022e09080a02010c110606010f11300a02 60
    0x424181640c0e01c903256542030041500085014020007006001155000c0c0544100c4054550500f1403c034801c6000d0300e014074480603001c0c22500001d1020715a10f0800d801400410ba4803152420200001e0762559598010012400340860425280c0c100900c00c041c00903060002e10b00c0200e041e45c42c4462000c1c0d080d95a42e004a03030747d010703c3c000c8035440010200403030480212000c4140d003061060404411200d21922400320401e41e044551011a000090320002c1020703031702c43c024001e001401460417100c011040250780b0601883c407880600d1400c2c00708a40c00c200c0780c041052080c0744c01c4091002318003a2516007255044840408050341c00c003080254200e0080c0c034102003480e217607001860940d507207034011103902c0864482d403014417040310510520154184a4000110070112294100c0500c601906038040303061020b0000c0850140100b540c440d601160349450b81007924 = true := by decide +kernel

theorem cover : BRFrame.Cov 321223021 321402877 := by
  have h0 := BRFrame.cov_init 321223021
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321223021 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 321223021 ≤ n) (h2 : n < 321402877) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
