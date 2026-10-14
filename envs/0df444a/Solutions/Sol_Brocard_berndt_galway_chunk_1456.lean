-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1456
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:04:43.520848+00:00
-- url     : https://prove2.me/submissions/43039cc1-cd88-4b50-93c7-95c56dd6f6a3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 261690647 ≤ n < 261870503 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 261691897 1250 261690647 261690679
    0xb042702130b06090906031906090b0604090c06180f14011106060a031103120a02060709050103021201030f1a0c0406020f0a170a0908060c0702040b0d0215070203070b0315 75
    0x7107070b00101099000408003c2000a41480640d484d40680028141c81c0d41d00d00c43d000008510203078090840d03140e542d030088001049062411607412100686080220644a60751a0165032050082c0424000905184821034042d004101c015181c06200440816501d100000307450700750300714080c0841c0034a02d48145001c1d00241e103038866800100364152407840c41d00d594030702c4101c22510907094010401c019403201403c100428040030a503004000c540360a16006010083d036820246c100740c010840c0c0c01d8006070803e1082c1c1904c0c2c0281d6a18a242280d243c03001034000351140c032220f036010300401c000042407128054030454503542c0030b03a00c40d8200c1c060643e4480540c580c0043c502c240809004400d101040007419510905090100441c0d1703ca80010346449021200703583c01c0000080d1400450501d07000341c0341580400c0c1c404400303c812542c0020000354040804002c0100042114800d66a04008031801404c0a81000382e4a05100788cc800e1000c0041e44143c6c0a04150314a83e400 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 261693147 1250 261691897 261691901
    0x100605040506042702030f0d0903120c0302060a020306061603020d1214010b2a010615030e07090b0607060501030c060e0a150305040c03240509030a0903060b04270213 73
    0x5000c54aa140d5184c0702c40c5031aa02e500c20385640980e0103104a000702201150304003c1410410901c6c1c0f1422000c3e441c51422001c42406d000010003081890455031001a8001526581046400074096102c0c0d8584d00480e4407070146500e0382141c1210340891106050700800c0e001c04003011030351001b60044480741082c1c2551401d450050142103808010403819980038058011103c0001c002c040b03105841080304030200d2410395085581c0d558a00822500850100041a04515003400d1080403041003080348c803a4001c3c4950146030342c5506905c031303d598400c0e08650340e443e80f06408201550b100e0410840b401802d0144038003045d4031146080d840d29040d0075020407030b500c4400c0c0203084446148210042c0502410031104015408000310001e48000c0c80b020a42341100341d00761002c41800100c0c400c1c1d03031000e045290503410802075038a181d540804080207583e008240880c4100c0000c0c081001021070103c00010000900c15034200da0040c0800302120b2802242c01449554a0380f2080003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 261694397 1250 261693147 261693161
    0xd2402070206180a03020d051c1713080c101d0a0c120201050f12090c010806100c050a0c06091802040b0a1d030607210b0102030a05180310060504050604 67
    0x1610460500c4814010f01d00451030030f05412004c0c0c4540000c56507640400c440840c840c80840740c1e43c012a881050402210803040201000307480c203074110700400c7c04c21106924000c2d0540040142000080d01405124811195806403801c2100d60094030b4801d040002d048280c0700c68400f64141100c090500000200006616000039000560b0340ca005840300a03100074110803414010f051101245a44c11100a0078070480042080c0fa40d40c90b10368403150030f18401c1614a410f2049407001d00c803045d2900a04100142a02c0c10114503208807410070500e00000004000c150001100c0045413040d070000d0880b01700d800c400724800c01003240706018001d9004901400002800910a0070b007210f103e610b0031501c13090241c581600051203500402e04040045030b09102141520304440c030b10a4001c21654001400590b08000e09001d5400007500da00c60803140c40100000495070038004459000b144c030305080c1c0107044901c413000c5c00b9008005050503103d8a8441c5191400189060607c1d014010b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 261695647 1250 261694397 261694399
    0xf030203070b031b0a0504051804051e10020a092c1603023c0903070308130e09060612030a0806041505060706050108010e0a03140a030b0d24020702 65
    0x700141c00c00e1a151000c0c1c000a243c240700900c40f40144c60260100320050980b0b100765a50350782d81c1c1b0301300002c4c4003240c00d0700e08155140724942c2c0304100210300003141d13010101e01160b00480f05540928005842c1c142802a141036407440001c01c0809140c014240c0b904507402c180c60203030400345005545015039a000d0000c1c21343d0b440f800000c1c007504400302a040030416a82001814040c24602e001c454a0514025450b110b4620f9002d06002094507240d0081c03040c1d01c03031030902e84144400425110310b500d200090100c040070586c01600c080d2007020300060151140d0302c3c5610700c1d18035601c9942c0c240c00d45556020b41101107108000c1c0d0303404421075403e85640d841d072210320b8846a0901001342008480101e05c025040ca02003015520320005040c04c0307014401c081641d50410395198211841d02d500e0340c103183d000603950301c0001e4100b01c00046840c404e0540507140c4111590950190070100400740d4070004842c480410000400580f000300c601030f01e24100e401101e5480f40c8201d218200010b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 261696897 1250 261695647 261695653
    0x10c0806030a080909071b03030b010207050a03080909040c0b030c040e102402011d0106090f090b0411040b040e0f0705100c0204110c01090305041802030f0c07020a051302070b010f030203 82
    0x42c4032170500c01d44640d00b10015180840511f810b00c88058200c038000081180000e45541c200c54156a0401010010344011601040283c1c65561240d01c507101d01107085000d00001000641444989000c000003805400400c0380e99190903101c0034050791140c0107140108400d0000326175009000c403018420f0310241525170a5401c15a83e0034407038030340243c13501c0342190340341c005040004900615460b03000b0818400891154106581102a500c0c5034041506851400151030b0210b03100891580e000703500801c9c0c0c92008140030380482e02400c201d125464005d07040034500c5c040403800140410201690718181c0c0c56040d141c2041090302407020340b5003000159007004003000352901e5400706892002c0d40e01054908031541030f4103401d40e86010825000b1072004281003004901d000c43c0c01c19011550b620443c5103140c416848160340c600500545c91400c000b240e80d404548885081c840548402002c0690340b182c02d410520203907004140484800d885c01c00005500c40000b1035000590398002d002d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 261698147 1250 261696897 261696907
    0x2103020f030c07060902040c020c03060903072607020306040b042013150e0115110c0a030f02010203090312090a0b030108121e04030501020a11061b0d060e0108010c0806030a08 77
    0x1038074201e0740042c3e10a540640e550015940180d070f4501c524500300a854024200111030702c01054202000285801441d402c02c01c402e900150b0101103c4803404a15107003c85080003103101d0f0030f50307409000b0000390103106007810f12040c02843c0341c200e0b00c1580324805c8480c0258220f400d4100c4040ba074000d039a00042070054100918402d90450075640b801340c003070000c41694544c54442c40312030a80c841e8112800301d088503000030f507010700ca2031f0a044944d002859a1403189011840d0581c0a01c0080d089282481e048403c580c030a10841d003036044000d044030004400000001103d6000d5080709205009007000007580304251030030303030707048440b0500501941e5003809290b44030f44d403000a041100702808410400c46402c800040c10240d40101300051300d030b912480c80a487c4090301001c1440d640d00000c1080424000711401114039814908207a407078420400c0385c1d070013425541d00803020450004e000801c04000543c0078003144200e564a48007152035210500d03445040010015000071700401c4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 261699397 1250 261698147 261698161
    0x507050715110d0609050601020115060c02100c1a060f0a050307140607050601060503100f080604020d060608031810080402060f031302041e050f190b04020f072103020f03 75
    0x200a0300c020120360b05803841c0021040000084035000c2d048140229614400c0c0400355034244180c142138264504030724078040c02d20b4809062045101e200134410950074140801c8140700311050001e2b1a0300000c2280c19500d01980008400c030100c0d000740c040c6400f060010207615140700150101c910250140c044141801e200d101100569203000760420340400c03291300008c6040041d036008003180c1d0b0390191282400c02d210202c410309544540101d0304000c405004804021400c1604642d04440079104141a40b030540041c0103954001e0385180070200344655840720891082080c21405c1b107410034211024541911036200035140690481024800101e4001640c0c006680001c00b00390740d1100c01e01c1503400541615804259030340e9a03924007090380c410403258050300d1340040d49000b060306070f1714100b1140d21440d01400c00c05c0c040c03203072285800600703512180d0440d013081c080d59011981d10a40703420490002c024048010906200d50644000410305c64802e6581c0008031300400b91460311504 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 261700647 1250 261699397 261699401
    0x10b030f2107080403050f10050c0901090605030703060510090305010e06010b04060f030f090609050d0c1e170406030203010f090b10080403020123070228420507050715 74
    0xb101150b01100401000c00465020002003d006401000800000d401c0f440c1c20401d4841c003626001410381e007444414440da0304605a181070302c900b8549143c8035a60030100b1405040c0a5100c45d8000704010280104640e1011101d41a07a0080009002c000e0390300b4a00ca81d910360074031604440d428140000d111440c032070304400650414628000c252041245e92001c121610f64404907401580d03216030800b08003041c08013104080b090304101d085110146c452654000110040c002d0008602c519001080200d000c2500350800305a8a540c550307403100b02c064000d40c03003070040c488407244801c0000380004543c055109940c0e0040d054000340504a01e00741d9540c84040c1044055540740d05941030310480c1640b00607520810013007000024104468041e050009640f150102150051444440c2c2c40b001c0c0c13000b10240d0380c801e05a40d043c19146c14010300c01760860914849000180b02040d002e04038620903900c00b03100a105c20041c6031a12901540c1c58491300c00010009111424951609000c41d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 261701897 1250 261700647 261700657
    0x9010509040219060305010f050607030212030901020c0a08130e0403231b07030303050105030106050604050d0809270106110d0e061e07110d080d0209060d060305010b030f21 76
    0x50500c0710341d2403003d8400780c0348002a4020000080d6160300410281410003032180c018007080d90b01d0b9143c01425203002b502c42e0005071911805005c004086003110740250704a03003d4210250595255001d42d00d010402c40d4840205000340d03010120000c1208246000458001c5601d6262700310f04030f440c0c1031721400030000f0240c00090024180b00345191174041c5655038013a040c03440040c0014500710300d409400c41e80103800c807074080d84c5001c0062180341c695200302c9064840456188042040d2480c040109104e480001c0da000000d00400e01800c3e101541002c2c0150640b56100c0b055a0306d9a1044800071000c1480c02c4c41644464800e510310b0b80034250100350760341e0150010b07107000d20450481c2518401c90344031444c41400025504180410b000e4045c080d180115200c8038280d400e03803103480781c9025000303030b220700c003a400601584103545036004c581801c0d50003c410b00c8903940d02d0520301d00800050f000c442c028051810b682800010114000d0b8048809888441710300700122a0a0301c9a00b00d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 261703147 1250 261701897 261701899
    0x30605070c02090f040209090606010507030302070512071a01092c070803031003052107020928320115050c030304050708070609080d0c020409021201020c12030402090105090402 78
    0x102800000d40c8490f000c03030f071241d5402446209039003001e2040c01880440245041c901e82c00c0b01d018000a80c1c0d01c4821901101d4061601680300c01803400d00a09240d82c94440355031440000403100d08011814444e1540000c1c08001000140e907100003000aa49985192030040e04111070341500c11203010135078401075a485e02c101c1e403c040e103600006141d0ba00c00c0c0e802c001030144112003001003280030001e0101144c4001c00c000c41c0c1880c1903003035203054045c01000a104c3c07000b41d8001850314444620303011205141c039007185880d00b024000c1c50024000c03c0c28444422141070b4018542d10130141240229a1204420352416031030846464030b400002c0c80c920301005402c0000200000701000654011800f41c006003420b01c1c54500d0300707860078195070702510900550401c204414000851000c40707420032410118401112031001600600d01001c009611024070b511050041d80154050700442c2803201c1141c00002c1050060201c90100f101c0c0207600400210040c805801c2c511040c03900300b44 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 261704397 1250 261703147 261703157
    0x70c0c1e06084c050603070503180304060306031218210602030a020301050307050312070321020d060e0106090f18180f0c053007050d0302031305030f060103060507 72
    0x400c2150f029140700418011603881410400701c00d42c0f50100200300481a2464019508914a454003044003400018019000d00c5800b20016010000d91902d00300c01446150503a569141c444c8000b5009100d580001d48604110303425201c0014040d00030850307042d08049003044141c2c50306080c1080744150003003142c60352000f43d03220000203c0b140061801083c00b40170140c0c0380c0d0305006c1070501d0700b0540e6100c10b22a07030017510f206010360101d0f8100c40c500d58041c90618518160240c05801c03c203070300d402e15a0058400151030b90524200c0c2d00403070642e49045405812644d0b510000c94203903c6500500c80c1c41032a6140c200605081c110a28200045d59100860050805600302c02889511401a603501120030140b1040103803801040b0050308044400c0041405503040c21008129049507402c0c5014041081e00c034074400805c9624000c02e001045080458506c0c43d0080d140d41000800b0012000581c1003c0360b81d01d8045149541038103080f00426160786542c4500d0081c22028040e041448 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 261705647 1250 261704397 261704431
    0xa0f05010b04020708090f2d180c07030f080603030405010c050a0b04080a030c08220309030605010f06030b150a0c0809061b100614010f0504090203070c0c1e0608 71
    0x502c1e0390014141c07480c01880301c01e4641520303009205a90382c41c000a10311030320090304e0030780d109500101c010b1000b035440407004a23541c0c05000428001d81c0d1141c00c5182c1c03072500d00308225036460403038001c22245200c0d03510303001050641082606c0700c00c42928119410307002400140001c1d4032590200080c58080c00803580020200c0c1c49507011890300340c1d010b44a00d400000d200d85501c1c1c050040c440400200d141c050018a81010780ca800448006910740d012040b107032140003071601c148911005160000c104028550b5a085890b113801c0081c4528400300b401c017000a44945811140207007404416801d03203180c90030441c01101c0380d490390b02003200d00060038810300700c3c291114005030425170f05040000124401d4030007c0c80c90984e918038543c41c810f007811428001411826481e0303004020070f083c102c0801c1200e500a0f201303801070340c01c88100148044100003a60354000c1a50a456004101c01021244ca800d030600c2e031554601020800c2100c0100104245031084500aa100321120241c1d0141 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 261706897 1250 261705647 261705649
    0x510060c110a06090812030103150c1e02031911100b1c030f270603020d020c062707030c180914060a061d0609090a120503070807030c020a0f05010b 65
    0x200b4030b4100c5000264529018001280300700140303c00c0c01c05440c082070442d895580c9080c0c2090360f661076009480e0304c0b07809100b400b41c00b49442224200a034802403080360419240290380c0d400124484856620207070300d0442e95409039241014608824019001c405400c1001c4c0d000b07000174180c0b480c0c02666000407502d2078900d80140b4656203201c1d40d0f85c0d080440350f815004180003841c6200c0f502000e40102145000020741210800b107070064100562140001a0900e000b8021005070b1542402201c0c2008454a00c0c0341c003030018048010768a0710003c484c0c1e003205640e95a00e00008040501420341841542c242c0d0b83e54400d48626008003180001d0960b951000e0000e50030305000d0250b11075400d100781c0320910b0080c1c00c0074042d41c5801f41e030703c1651441c01040700c61000e0707c10390151080001140300c00400b40300d00f0040755089014002e1980b42c4280007040b55104440d03810010b001103000c6032102d80b00740074071728083c1342990041244281c40d03121005014800d02080399103643e99005401c40b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 261708147 1250 261706897 261706909
    0x10206060405100b0a03020c0127030f030b04020c0c12030a050304140a0206070615050418020108040f050313030605060406030c0506030603010e0d0302041e0f030f0515010b07150510060c11 83
    0x485c40d00d5a01503150580403d04d01d0070759140704413458a08191850212413001c40500c03145416401d031502c0010101c40d80b4058005110303c882140c1c0042c00014104d259490006041d98040d0080e6808046420b03961841c035168068400e41d02c00085013040400c0208040c17100c2c2c400541035010a40b004050594009811944411011a10710741c0301c50440700e0707280401700303940c00030001694140003215510381a030400311004a4000d050041c20008070301444545884481566401021030780d6850900000c105070703641c0c0303110441d074003070600c000203c0c035040900a450480380d0001c42c43d44c07054102410004640c00003882580c2641d6070790302c100000c11080004801d0305845460040c1c3d0380381404250059000413010610a200d1050f404010032006080c0f80300c1100c1d00011090314140040c0740076800d15281220701c1115148550001c40d01c00c50400050210030f20031544480000c002003501d03c00d8440c2260149401c0540072002c010050058481c44205485250300c40c00c410580c50010301 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 261709397 1250 261708147 261708157
    0x302190f110610150905030d08040203060109020f03190f060e07020d110607080408130807181808030901020405030106080c040e120f0912030d0905010c030605010206060405100b 78
    0x20408510159441d80150801da10090128094022850110402c1d01844400e104540c160a5282515070840344a00e4148024003001802c0e07c800b010301260040c05090191001d1744603004500001a10318400d108603440c811000c0519807d5540b10300c6080814004900000045a02c2d20711100c4090303d20700c58140a000c85020b0900c2506040c10028a00000701c032600c000e003d40f00f14001500c000c00200941e000b0014a4401180d80c0e50746420340783c500907a04c4412860421180120301090007181d0181030302c0c89819181910840c42d4680401d81d59441031500c92400c802043d40c020035082e10007107500031100d41c00545000d59640c0864216030b03241e40004030b41c5c5c1140103800118500750080340041a0700500074001100207021504207413080285900c0a0b080014030114541c0b10034845d21080445082540e0311201d02c0812180035003040308041b50075519050001200307d0180c0b00b101d058070410b900405c86540e40ca0140001414085c1941c0c60030b2186803400a140b001c03990042c5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 261710647 1250 261709397 261709447
    0x2060f0d0c080109091104180f0302010b10050a120b0a120501020301091104050307181413260a05130b0f0a111f02030a060807061d0d0b04120302 64
    0x44000704020018030003541070300710103165400c220b00030340419407103118668800000c640000300d40058005c0e02e13002c110f07109801090200c0d07010040c8245034040d0b002c1c85680000741d03005c111580c8021403c481911890010340e0224140641c2103600c0307006035004103e69a0040d0281da4101d407107009010001002c0c2d4404c44060f900000148601e40d05406a00d54000219410707070700705401c00001a0f102e88441c042c0300d8006505000000e00c40301300c1e40040300409650311608406040c690345509604506220507110798071520400100301c000070403072092540481e4501c41c02c211310000700b03d800d0b81c4055000d074a82800400f001ca80400c2d1400184051521050950340d10204000050900d41041304985c24503000f01824208100c0c4407811100034804045005940703540b0000382c60010012904912900c0c805e1600204919401c04200d03510442e01d8400c90f0f010703012038400c01c204445004001040018072401040c000703440c0c1211002c102c42241400360500c600790364040c17684a510b514103 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 261711897 1250 261710647 261710651
    0x90c0e040e0f010605060c0d1b060c08040b07110303010b09060c0f070e01090203010e0a0b1c11030f011808070201050c03120610020105061008060a081501080c1f0c02060f0d 76
    0x128410802c24440d10005040980c1e545041a0045c03100c661981203130140c0100340426503c0b841d009844e5101d26039502c5038004002c0101c41d510000040c42084d048070111448014000400c200da402a1183c90000c02d4242c005c42c035507800e1154200c05a0001c1800c0c0f60009010311403d10780700c0080c05201030210400c401003250345d18000b01d40607001d1041c2d00c00809188100018022201c03064000e50348003005280124650380000d02188140310016082d0300164203c007400002c001944541082901e000c034115800c0c1c0ca103112103142200c40a0440042c405403001e0110b000900040c0079003000c5005040c40c3d8280100f0820003801c690140c40d802c10078090b480300f000f917545001d4115a0464072544020031091810101003181c01019001c1c160904c40000001541a46d070f8011080c0604001815503044406049d64000054000c2c000c12915000708002ca0000b800d085007000b805007600440003020000e100000d5800680a90003a60450020081241c000c51540018800c1210790040 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 261713147 1250 261711897 261711913
    0x91a0d0507030210020a1a0f071103122e050333130c0e0912040e04020915060d091101030b031e1501060c11010f0507020603090703140a1205070c090c0e040e 69
    0x32308081914020a0541480a10903441c50045000401e45404600c2103c0080042d00c501d81c5044454038a040f84040070360918003400c888100700c1d4035440c02c4450a07400c0303031840b940c01d92910001c00c4240707850400d0b68000c042d8100c0050900700a194119501d8031180720000c0842d05d6170825201c0c503411100301c2e0302203403042c815001030401176006640e96000c40181094201b20345040161000b50010744101032860203c0d0203c900160b0416030401c00401c40c0782d0f501890f808100242465000a0741d1522030720f800c91a5650003401501400d0a000b0040c005001078a181a4600a08100403044500c9800300e0031100a01900c040d602030800780d1110f082151311440c003601418036084200e8100f0500b111031420b241d4201050b078a100f5412500390383c036541c3d10b414075442c2104683c0003400fa00c1900c00c0204070164085040e903103c1c1d00910226140b444031107415203080c880c10f10002c01100c6250001c000c0c0c445107620429141d640b5160604115600400250035208a00003c500580102c84 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 261714397 1250 261713147 261713161
    0x306060c030c070e01080307030906031a0a12021203040501090b0a020c0324071d0105210c09030d0309050307020402030a090b0903040611071404050619091a0d0507030210020a1a 78
    0x11170041c0f060100951030449290760041c80c1c080c10b4450b490a16480301a0413030400890f2032138680d18040030300104543c0e030743d03148a03c0202ca11204180c0c040d901200071549082404400c9400780c6406840707203561a864089082c0242e44200326500071400740e62000d40e51540e040c400e1111004492901c003050182d140d201001000d030241002e0248112644801544841c0c03c5903a400f500003404c03c0394441206002611010842c42e1407104ca0f092450104210790103240007802a07040182e0841e0b1541d06500029003c42d21484030280055105210800040c50300d50001c1d41c0c00700d5400ca011940c04c807603550740504500300341e550103c9904007040502955030710600607541070444c40d0051203440d1034a585000d2401955400d6400781d07460f01d00042e840d4640c034090300010000d40d10806000340c4d80e2081b01c0001d00c00000c060310760000301001400f42d440c0907603008402c01d030002e01401d0030a00d145d0810000c10004607081040d40a05114000031402c1107400440e0b6140c3c206900c8660701c0c2c012 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 261715647 1250 261714397 261714419
    0xf0a06211b270513030903020f0d080f0322030905130b030f010b1e13090611030106030903170601081311060a03050105151c1e1d010c05030c0a050306060c030c07 71
    0xc101c500052071901300c110109621152640c112901620080b01c0b140104c8041000080d03440c80180c51300750006107102015003448000c42c171a0843c181c654000d01a15000c00901078229200030313000650720801400b09140590b901c0e0100c0800c0703440001c030071480c01d006c13a0030280b041c42c041005940d50700b100166803c01d08080b844034002c1c1c51034445881d11030030005c0d1201c07074040c0250b00703259580c00b022000c1019942c041002072000f007820b00e41365a5120030003009441041422030000d44800b400151103550080124050385050711220607943d00c1e0000041504140340e0b043c0d0f000b000303001c0700c2d55242d11890010204190b2540d0042402c1d070403e421701a07005841c0310b1507030100504200c4010340d15482c000f007040c4c0204020001c1400782d98145002c080740c1c0020a0034466030b16140c101300700b8102c02200c1c149940c0d0014000c0c00340308a80342c4141e80ba400100c68000d0b90349000c0050382040d0b4400d200969015000274016401c02213900c21191540e00700e6a00c0d10b40d0f60b40001c5050000200d10303 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 261716897 1250 261715647 261715651
    0x1e05130c080a141207031101020409060f03050d090f060e15130512030403021008090106030c06110c0f0f040b21061806040c12050c03060f0a06211b2705 67
    0xf40010444804c03d600800e4552182c5030740541008800e00c1c81407100c030000e4044030014082400140950394485210242e400d90b244411a01c03445600c0c07000e0543e5004035011001c17180030540711680e03549072000c00e40d0f44810040f042d60340b00001200280090300007001600c40511000306144080e0b042c4814003201071039001c0d140000354000d0204100507a00e4107280040503c02e454030410549030018010f01400c41c0d03170002484015079090109140740d0004900c001050340380c0440342034407407100a002c003503070302d903613007650441d024030f18410b0b41e82440d030051324402c003001d4040040a400c400081c100c401801051154a401000c1401020415070800910328038804000d485141055541c0d01400310b0248514800e011180f01c0072030510105011146080e0400303400c2d04c2082c40e00030f0002442600845071078582d5481c0140105142030300080c21810321218121200384002c0b02c0e100c600100d414100071303c240d038001d02d20100e0b0303030b41600c18a9206103403188400c0c040c529130132510b60300785c071b0380 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 261718147 1250 261716897 261716933
    0x200301090e07080d180f0801050a051f05150f07060b09090d0801030b13231908030a110c0a06020a080a051302090c13030311060105041e05130c080a 65
    0x10210080c415480040b80d81d11404405060800b000740f17140c040c003501180c0c198081c0301c5c0b103610000d00090001c0706401a1b4454588003070700308181d5403000b10148140400041c542c8441d035600000340900e0900400f02c550810301c00c00700908005040e0100000c50780041e00444105880d040078008600b842400700350813164105c090910780c1c42c419001041800c0c1440058822103064020441c680003101091540a421030008200ca0030944034240054910141c0401a4440d0412445021034840050014140c3c4031291919540b181c00010000d00116081e92910000400c1503c403051003c0154140e071a02c40c0740003503154521078201804010005003030885450030241000400c519080901d001241e04031070036100d9464002c110709450007240c541d21011082d0030004401e05410442001c6c000d2000c8089900c03980c0c0311402e100c156581c5503440010415902400304198000d50000c560015080c05500100c1c0c034140c40796011600703a913109080940041401d40c090014514880c1034400c5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 261719397 1250 261718147 261718153
    0x120f0d170109020f16030504050a230603150f121501030c050405160305070c02090a0b030613050703030f020c03010921140a0509060f0705060708180c0105030a200301090e 75
    0x1304802e41c1d15014420341e648018216071145040c802c05000d4400e4030040e00001e41510402a03c0301102c00710a024085c0c5142c0607241224a5189864048100c0b0303c01c0c40103010f468104001c180501c82001c0c48012410f0b4003481804912600c900100420208140c9010803081d5951443c1402c0c1400c10040e00054080c0e030611082215850b00c2c00201d03045000c50b49000511599010b00842d1003000c6150020750001c0e0b418140420100745400a401d00ca02c100c00f50784054468201c60011105c0d2843e0042103900104810400300340207088200b44034a403401690942d0500400103400c6444c007a804681c2c440386000c4401210021500100ba55980c504284400c1c00c040421101d02c2d000d039900388c80c100200050000c0868680506032410503620201e00c6880d807080e490721a44404045681d000001c170201c002407202c0b100110101200074080c5c2c0070703040700140c1d0001181d096000a24081d4170a4640306680c5010030f03411180543d130302441e41026141d50400b2104d405960b0b1000982050368 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 261720647 1250 261719397 261719407
    0x903050705010f0210060305010204080c030601140f0109120609061103190e010608070305010609050c1e031b0c011a0103021c0f06031e170a0e120f0d17010902 70
    0x1040010810107949090078031001c01060f280d801c0b8600b03201c402848600c5414850300000f0440d05402400964101e80c043d40d103000d0f07d007002c0c0740d0744d090f003440b0354112161081201c40c6941040c80c8410180e00061411400c065200e4014070a2007141400c100d07103190b6079404413428421b0601c43c2c410010750341003001e45507041c0010400916800342c2d030001ca0265450141c01e00800c02544030700d0060004000343e5081c03d90340e003015402072074144200c22515090000042e01b88804400f251000f00101400702c0c0c04c0d0000f00032019854000a0030f5000e06000900304102150340c4401510307000300341c0400412689490641c01c200b5101f40c0e41200d05040c01407090002e0310500000f40f5801d103d03019030010382505c1c0d924681d8007400341c41e030020345030520a501110f186903007201c0801c1414010b03107030945c2ca29480d200140d403600c5003100c1100005c00000e440b406600d041e08880c0d500e016000c0440d80d00ba25441c04250a0400410460700890001101080514050b0b0f401d14010105840e045081c0307 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 261721897 1250 261720647 261720653
    0x21c09060b28060305161206080703030503010e062d0307090501120303060b0307090608060d0f08031008031c02220602073b100801110403050f0c01120906060902070f120903 76
    0x42c610710a915010700000d80710603000b07220360f640007400030840c4000302c62a2b59564103002d40f03194000e0081a4080201d1030001d115410f01809a40041000070101c40c0e0100e020036840352a0b003502e07465180e00d8002c032040003c0c42d45440c01218060205034414a54000861802030704880040c0d22a60a60030f05000308003807140c2013094803007219803500b4003403038680d1a4000101502180d40e0018550741003134096200b440040303406140300d0590055280a2a52554141950381c051840e071250903082c1445826850035103500689201d00c07002c00c100d42c18500c1c1c9160566551456000400143d00030413041144503001c0b5001c0c00c0700782e0460700c2c4007030010261802d07030036401c0c180452503480e50120010480c4084280301410082c40194001c200c4202c0a011840c0d00d0340c4140b00960b00c07446101c1c4003902c0700b00c0c081112020010161200c180d00b200580340503000c5d0889020a0780c0091395200c000940103140d000800c0b02910591056409401d03501c0d18980c20341d101d102c1c800401030702160074400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 261723147 1250 261721897 261721921
    0x110105071e05070215072607080c03131512060b0403030509120d030c170f150a030204150e0c030c04050402030a020405041b020709021c09060b28060305 67
    0x1506800e010101560074070110a4419110b02070000f50400c0340c0340400101c0303030f504d64060112a44240034000c03a100ca100c200e103041d0042541c901c030040604001250015582c80014401094206c0940b4189078804010802d05446c5a00c80c01010840700c0885448581c80b501411000441e00010000c41e41040780c581300e54007541c000107051200010ba6810190b884d002f0075010010071104491070110604030050190003030101c0348cc082041c0d03001054200d40d08480680c03085d407442c1903644040d079810140c880c2c881c07a00803142d1b8010380080c10101c0581c54500925001c1301c4412840120186850001c901040307000303003a610000d0050040c001102e0181c0c00701c40440714200ca001d82c59844e540100d5001344030b41e602442d8403600c0d1030043c001c1c9607900420b003001e40c004d5409980c05155520269001da200d0030300c6082410b0304004903405850540c1e4080382a880c00365400180e050344070004039800c255045070140d0001d070380403880d2240205111000e0050400c928040c4201e06064048200c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 261724397 1250 261723147 261723167
    0x30b060105072a0b0316030b0f0603040b07051306050c0d140409050402061b0c031605010c020d0c0b0a05131a030411030a200a050a030f0b330111010507 67
    0x643e0216002001e5a480a071418409082035603a201d03940c2c24071000e040c01c44031015995401190420185958034034040100c0e05125202030901d520b943d8480d50f8035806000b00a1481040c00414000780c104a10099008809481541c681aa0300d901c5190068506604914000100070314007506180e00c6c3e154900350f80c1280d102c00d2010401d602d031480060100c0c000ca100454000050002d0315616500c001a0485e40d928154195035a511204048101c10933090007582c0c0482c54143e40c000050808006509005006005070740d070080d100c07890000b1541c0088800360000c0e0740411413184400e0844101c00c000c021040c000e1840d5048407000701581c0c00f006001038822880074400c1c04541d141488070b10340d11903020070840c4122400e0513100f010154625045e40c010b544881022030745003000940481900e4020001001a29a030342e10f0480c4040000d0007000c11020110a6031403a480c0003091806254014507020700f0902c0c0100010311171402090031b01c815a04010502000c241c2042d1440 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 261725647 1250 261724397 261724433
    0x30105010c08030a09080d090218041113020d15060f03021e0d0b030706030f150810050702030717030a05091b1302071a09010c14030c070309170601030b06010507 71
    0x6442c4d5075010000401030151180141c24000005984180820346500c0441c406108460290500e02020818194035104880040825211001e54030840c900102403003900d04000501510340103082d25154103803140d0046100b40500144070600c13209400990350903904059250440c01c0440c1a04000444460124001d12800700010044288205600b082510341d00184c219107400340e4448004000b010a045c00f4030041c4d04e4400d80380e1100003601111012034600e000240381d285590000c400c000c11000c0ccc4440c0661100b0041c0000240480400700503107080d0a1120b9101e19120300302d00e0076039400401d0030120381c0044402d0414541c842c80140103a0106440301d00001209a0198000f4400c014020303140100414151a91911150503d407040f4001c2000b400503915565080e501c03aa040b2410400f261030500000b01600360104c007030704c103a60007441c112400e95510b920007001d881d10b00b40944405d40200c40107000348003001143d290020f000b80381080c5041c03041c0e1030700805459403031981 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 261726897 1250 261725647 261725663
    0x703080f100902030405070801060909030905130605090112110108040201021b12030d051006020a0510150506270a060909110d1d06070503040c030204020304060e0f0d0212030105010c 80
    0x80340705842211024030240c80c2c1604210740d030341400c1c20895030318161885006441d608241d40803078810740d5030049441c2280d040c0c03074100d140d0782000c0400c1341052234204401543c5070b80b207000154941e81c0c202c549000705140b01c824400c0c003409081c00400e040c0d01018803030600604506010061b6400522102c08500d007003001020104840000f61280741c000c40b1810440c4008541180408a5980010300030041420748a0007039941340c0c0300f41c0c0c64210000000c1c0c026040202c443c06100074580120040c0b020910b9100d60781c0751554000741c090740080340240c03091441c05991040c84003812801103c010b02c101d407540400ea151540041221000740144084241c4451400c810200c4400030f0b90300e1180400c800340085000d0320301241c90710030300300d480c00f0280c4a150081440300d8003603002c0303a014680252000303e0140c1540c0900c00a03510241080b500981d4420051440c04c000b402001d016116100c090302a0700c0e0305580084c6011400b07001d0500d00e4400308010030545e80c010406003141907001c001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 261728147 1250 261726897 261726901
    0x3060b0103381002071d1b070503040902040303050301032901060513080111070c060305061f050c060c03090c011d040b1f030f06080109050703201815060703080f 71
    0x50b03004880c21014242d080740c0042000700d4030030b4000c2281d60903036001d8030550032040c0089080c500084400d85070081a8110100a04a602c2034440208002c81c002c40c110b03840c1940d1104600101c0c4d01c59401607000960100c0144108200c1000c1d800c03080c1003c0214044140d00e980c1c200f160984188121428000c0000c0c0c00c40c4070012a488081c0100207d00080080b6424036804000e50747c8039400449010700340710000f14549003c5e00c00d060061601404071000c5020035440e00c02039140c0071200c102804001d2050b422180000c0004610030b1050401d041e0f16410540340451400703034000b2525040c8121100541c1d03900800030344500070213404071004100d103101a004103125500041c901d114100c806501d00d20035a4040e00000140000e00200f0400f56950701d1b01607003221600d00000784250403144003000030424841c8da5004108c948010107240140c1c3c103000500720504d000c10905801820007c101000300301e0905500104000d0340c40d14541311050b90014540c2100a1440c1d03038043c10800 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 261729397 1250 261728147 261728231
    0x31507120f061a0a09030312090b0709030203100209150d02091c1b03080702040c1407030c020a0e070c080d02090d0809030c0a0518060d02031603060b0103 68
    0xa00090000500c841085880740031200c400c0500454016001011186810f62414031807401c210384503008070303035100e9030510300b966411252420050b1900c0b504a0b00c5203000f5004c500183c4d01e0500130602c944450f04000c0c91841032500f00311407101740c1d41c41c0350320520410100c0c1d144c1480c0f10050030008409503503908103c00d010002070040c405102d0308000449140c40101100c031602404107801840760008074400075104101d40801400018884038040c800140141415082242c06040701c0c1000304101051110001c1c007078000d20800d50024007540b05980035800c00610b5140a001d4105401c1603d02c3d1010000e05102031000e0020003035040064a5014208070354142c1f660003000902c03844050360942080007180d0064880d040c803e00600c00b08010364035102d0320b5401140c05c082c240e4034004040070a81208506e0080005410558092082c0010b030780911001403007040380005654500d0450801000312500d600c00d05050510b0180704042d880d410160f16021400300300940c10031040780303036 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 261730647 1250 261729397 261729407
    0x1206060f120e060108061b160b13061109010306080c0f0111032b0b12100e01090c03080a0f0e060d0b06070b09031801051602010806030a08070606090e0c031507 70
    0x103100b44042e00606002188003800400d880740240c002c911080d26030212500148414441d1000c4440464500040b0b103000400f600c1c1099800f0036603280c041d42241040d1510010340f4104103400602150000d41c01070386607014407030f400140280000030155001e1510202c0c6000c006901c1c181d05202021203144040074040080f1402d01c1100107900481070074800400350550442491100024101354105845091041c44903090000d03880080440003038802c5000003d0180303c01940c1555200e48034100440c030301a208000441c824a0070740d41c0c07941140e10082241c14202500c504000c0da2040d0840b613952020181c65510000c0c1e0800505440d40d0000505140704100f401040226542c0800c2144440400070302000d140d509002c102000c042001126144103064540d03408203034040b049030140d441080090340c8142c020b0300320b4809080f15220f80e15540c100d8101200da03561112001d00c0107a1481c000c01391013080550060080722510000240c0703401021240c10b0794a05844001007159101d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 261731897 1250 261730647 261730661
    0x360105031807080606010f03020a0c0b090f0f030d1b0f030531030908070e01090f18061a090105030607080702160605040801060f030c09090f020603070f1206060f12 72
    0x2000321120190f0300d4008030f469040032a11a804588280d0030740061901074000c548007018140d4680c045002d4a50741c40c07101d203001512410581c494100c004804001c10008104c103a00315030f00844d154220480c030030083d40c548045070182d0b02c60130f020400e00c06030807080c8404c6e4400941030200702a40da903041502d95001500f08030010091811450014005080301e400701140030b5680d600d4100e0b21409121780d114802c2c4a5551402c0008004001412443d4400d85840c01e0012010078410042c14208882e01251032065a60503036643c01d0300307504a1203c100c140040710030344009909600d08800a0380310750b8000c1400081c050020000341100d07100b030000e101a4804440100b6407242c60f0701c0c0041050300079006001641d840d120b404501e91142c561070604480d401052041d0803814038034500050300c1c2c0c2d50011103110345119404801641c600c00510300c1640a40c1e10100a82e0201c00d00803c1900e03600100a07a0500e4144203200b142e44c0082200034011003410154515409600d00c48018800 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 261733147 1250 261731897 261731941
    0xb12090a0b0f04030f0504050a05040207020f031f0e06071b0c1707061211040b0a0306180b03011b021c0225050108070207080c040b04020702090c36010503 68
    0x324400300700d8848a02c050450103140030b56200110444072010644452050b4040d03942d1043c0301c604100001d00d4681c00501f0030501c042d103020540400900440c1c80d10500102303100e1100766880404422002c144200380503080b100000b48424108000d001d8860f10802c03c02000340c01e4079100d8401801390303000b400b4004101f94582c001641c044000100e40340c1c0164000e480004011000b4500310000c9405401141c440c9118143d01e800c0c070f000c0b2062115800002c081080c16110800025542c41c0c0004c042550521000017081c8141c040c01094219a008a0798800d410090b61001e200c880c1e0019084001c0008015075080810600300180c0c40e000c2003101d02550061788140c0540c0e0f20501410b407c3c1250030a80340c000c1140c441207000c5c1d841d080d45001e86101030703001001100c403d01d841e82210520b0280600010700e400c0864010414105003101c0d09501c04c40005000200c1e01d01c6890810344003524004803a951100111300c2d40d844016201c4024104000400400c82582e8400115101c00031 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 261734397 1250 261733147 261733163
    0xd0c0218100b07260a03060e040b0105010f0908060a020d05010815150604080a12030c09030b0a0507031d150c0f0702041d100605010f0f020c12030d0c02011409070b12090a 75
    0xe48000010385c2d11031006480000d040c0280000d100c1c441841e03103801954004440c10070b0346c0c2808011147c540b038955100081011281d8001517580003804410300800d24004c0150369840b02c00d925a00703a42d0182d0000745598403e2124140100c58512290740002e02c42409081c000074103400603203d4000c0303402984950007030030045810816104455900403d2a403001c6c02460401e04042e500100b075444041d02500303083c4000b0308042d03515031180e60312582504000900c81111503e0341c0500041007546101c0e030388150381c0e842d403c1c00c00091407940224951415460041520015002c900814a00034083c61300c42120343d4645208000c1c003030f01c03001b08404481091052a283c030010704101d02c5a0307030104200300d4601010900c02c0040e0784025401750014900c0c2c610321300c1800049602400511254002400603000c0800c4c5170180c20000c5030164008107445140b0051083c000401409140c0c050340b00c842c040260b9006038050301c504203a291069040369a0b980d401c642444106400200808 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 261735647 1250 261734397 261734453
    0x111203090d0e010221030105090a02040302010c0807020103061a030702010b19090905100e061503031303030825110601050d0b010b0307181203110705010e0f0301020c0d0c0218100b07 80
    0x410f80080c60423510b00301c030884115100c0301e410008030312032070101a00041c1c6034885400030600c00c500820315544103240000340240e5490395460b0fa01504000141401400818031140310350900a01d00206001c84010325450981c410040c0c20304a140b0074803502030b071101880d00900c901400240e0f080000440e05101c1010102282030f00c0d1201110041003407464005401482c1c10000160b4000c0722040e41d42981440c25620b0990b58402c0041125030341007400d10001c0303964150096010001c240301d44407051124002a20b060a0100c160005d0707020b0700a00002001251594140e10f04403140c0442880d40c0740c581e040200c40030321220f078604140311800e08000400c10307445661000340d40d00030754030b503440c0220400c0c1080d140d500c2446034038006040c007a551055860829200b184c1c48000a00051608030300c0b40c026414001005500c4010582172201c400543c1007000202d4400e48800300c1100c2c00d440d14150b150505580c5000e00c035401d990104080d400c10940300081c10303503591000403a070030403 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 261736897 1250 261735647 261735703
    0x31d12040f1202090604050c090d03030b030d02060f1506130b1806030912210a0c0e011e030b0f0d0b07030b0a1202040203060303120403111203090d0e0102 68
    0x9038424411020190010340c000201685001c911440c61a4014003446440d1102803c00001d004007500c98030000108020f150915601d1101901c10103209480228030b8071030420405050003600b0040f0300940d0012010464002d00d125401c0782c2c03010540d816242c2110380d29010818034015060400903800c00910013080c9903942c400075000c45003514400d641ca580d441c0080c007007280800e8848429030740c08003000b83d02c01c10601c8044c104041451041031300980703144d81c00700d081800540c0c40070102560ba84800b41d5441d4081c00f0104ca201c0282841d4001e501007090303c04074000740504003802c0541d03841c1d19103d01d40e00c18840310000305008000d041e01d45418107003481c0c440c80c2540ea000c0420b140190b2440c0ca07003400c000d070740101c1d0941c125400703503001c1075000d02000c0d6100404c01541800100400a041c540e158140e40c0524040d60300e280d05a10728001c65450014000940030786150280b003000207c07040050080051800d62408180f401e4520780181e19040e44000e0740c00000140c1180340d056 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 261738147 1250 261736897 261736933
    0x4031701030b2203020d0c060b220c08040c030311120403120207060e03030d02090d0b040807050d020303012709060218040f05071b290a0b0301110a031d 67
    0x400e040f1a4806022508501c622401c0c4081d81004001d604090304c0449294001c20b100343c00c642c090000030800410440009200c1c2c1211300d43c000c070414400c650342156240300e11541c0e20040e0b81c0d007401052802d250b240c80ca11020107110007400c02c050850780340d000d030209000500b121110b95103519203c90712490007014040d00c5582c000e005100e007c40000d80b0502c920090711200d18090302851030108104250b0740a50b00c034a00c000d40007000c010a45000801802210348202d001303084d025251201c0e49000ba09055401c41d0320400c44d4018001844008040100a91507030602c150443d891060030083c40c001c0c2260341d801a024620214001035500074410f008203070410101c40401c14804041a803500f110403d8440c0c40001d0902c4180000346034000c100818203d0285944d820300b001aa40005031100d4000c0d480710400440f9130170712045203010f0044048410040f002800340b1044001496090300643c00028105502c954008403d500d034140c40050071500101a5403d141a180344a00c0b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 261739397 1250 261738147 261738151
    0x71202150420190e0108190b0f07110115151e050f0d0504080a0311090112020d0b12210a0903080901030f1805060108070605070b04031701030b 63
    0x940504038140044898040e9514401d542c0500382100d5000c02c100c400408900090324160030010081209810a06240360764008204083d0030402ca1360428042c01d0900c02d648407040c51070145104043c5c0000d0146044507070180101640506a5880c0324040380c00018903544101c80b0351a1042180e400050241c06e0360a0f554680c00c1c0c0f960140d100d050441b4440031020541c500749880041210704103106000400d20781e40c0711902503061500d1082948111902920f040fa40803000103040110a03405001d0220300c0c1078206003ca003000f40420001e0701e8220303025034081003154005100e10069003154091600048058410a044145286641d0b07603120b002034080e2148505540248903102100d040b0351801490780d0300e4683c020703d955070b041c41c190004d49850341415292500c401c0f0344941c9210340c040d07000300000403240000043c10040d0500e20182c2080401d03801105007404401d40207011504a59406100550240d40b030b03003411120301240c543c1281c16000b41c0000002442080030346c0e03034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 261740647 1250 261739397 261739433
    0x2040b0c0109060630020a03050d050c0c0d030f0e01140a02010605030c0f0307150309080313030e01081e060307080f0a0c09050f0c0a090b030a020a0e0a060c1202010f0207 75
    0x100043d1915184540780041d2466849a0703100d20001017140102c1c08280503040e80f01405d49a04140c0f07030350b5010304002200301244001500403600c07002070b11040201940e040350654000304004025100202500c1c503004245041c00701c00c86c01600340b17911944d080e62944140004107500d4445180e0000e0103081c5a103c0d5510901c2254800d04032450b1403280c020030204010000d02c005403420700b0840600b5503000510060503a1400d840c00400d00c690001c512803254500f204600085034540940844ca09045403410086800c3c02c00001c60070001c080352445d00d08414040141c0e0301c2f000060724004581d007002016005c2c514140541420001c1e05c0542c091103810840580340e120070010301191021074000b40d20700e880601117003042100500900d445125498041022601c1d43c2c5410215881612002101e0b580000d001480c1c5900204040c120002203a101c031074946400c2004003043e556220217804c801c1c0101c0c030344c03250038000d5101821419010386d055481b4006428070b10002203460a0031 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 261741897 1250 261740647 261740651
    0xf050301090e0a12020114011a03040222090b06090a05010e01090207080705030708131d0609040204090203011109130501080705041107050a061a011e08090114090604030e1210020d02040b0c010906 86
    0x401c0c040889c0d140512940c40c62140d407070441d90343c0d4007040040315201203280c01403c08060018140c00b207601a007c000740c00b5403d11803080c1002001d001d00302c5070040510804500e0040103100c0400b00204144c110751032808090b031203a0881c00c048807184141d2100030494480003a0280400c81030b440a4800c03600200c00c0c02d01290369500800426510f482ea03032404c01c5001100242d4a8584140700c0380d00140041c0000038028041d0340800d003120565030280a20200108814074a868214000302d0745010002c0c052200b5450409210b641c2d012500a07a480b42391148180e4103444c0c800f0080c0d9680030b030031400b10f0b03480e0340036400e2400040101800310a40b00307000c41c4004a442d40105c0c07800e02007407402c000740091b50a61307440407510200c0c0508160f94654070b41c240c0120340d180907200507006507000c1014003902d040c90b1402425841c081c400943c0a0040460358120360003010802855900000501590350303090780c0044c000a218581004614031000318801402100550020b90403074861801 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 261743147 1250 261741897 261741899
    0x90106051905011808030a09030204180b0408030c070b0a0f11190e0307091d070509190504150504060209100504180f09140607030c0f050301090e0a1202011401 70
    0x40c4111010300c014940100100607400b0000b5521810030486500d05031482d07034180c5510b400c00142035612a802450000c0c003198001d00c154a0320307209045401c800902c000100c240c06139281036299000030809031801c40080001070200c00b507103040f2000755078050001d450510b016844480100810485810340390700d0051464130154159040340d545600c00005821200085102142c0800c01402c0841c1c0500401c0c0c00010101c0389030060003404402020700d94883c3d400c54411501e0120254003a5101d49044018030890801e50010300030b99141858010800703a03210708291901d0003506012045035460501004107004295014004140f41202c18900b00c25019004807528001c50254601190314400c1c2d0070807a0b072503035000c1c5450302c001d2040460000800e0312008003900080b901a00b5a41045042005065142c41031000547c22405d02c001070300c5405400034400d0105000300a00103a45100000c00000200401801142d0054005609000310700c8000c0c0030304a17402c402002c2d00c4d10400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 261744397 1250 261743147 261743149
    0x606010207031104050601020a02090a0603060b1008070c260c01140f0a0b040902040513050f07080d030b010c0b5217010e1506030708150102190b09010605 68
    0x50007504036500540b00d6400001030380c040100503c0090030003419840740712007030b900580760f20100c5446000549000100725143d42015000c0e6540c240c0c4861141d0400b281c200c4420750400c150b203030404102c2c500604003034503628081e944e020600c81c0001c0401140ca00714442c040d11301d0000d14584c10240d00a10a8030034480502c5140e200540d05034103a1406100002d010810650044000c440020400702d000e00003034011170100c94064035031000500c5101c4008040c003104200e82d1a00320b51001c020001e161801c0140c075202d0701c1800b600030800d44c0300c000c4143c0300e82c0300f40892841d0b9500a800b200d02c90411102404141c3d001920803e18070341c41030900800106040c0c0c030ba006c540041210306200d18600c92441c80030160940918007406000b5022030101130711415024081e244402e880c0c40ca5080030f907103072607020008a02c160301c2090b0030420040160f0f0321002d04c64000000f14008155120500d0043c0c0c10410368030b01d208911186552000c003400081c50203a402001e81e84004c10413161a00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 261745647 1250 261744397 261744403
    0xf0906061409011d0303040b0310170d020c090a020d05130b01060311070f0501020f07110a0f03020d1104111206040b0a050105070b0703021603030902010905060408120c01110a0207030506060102 85
    0x802601d0100d480340c0d1303007000d8414520445404042004081c2c0c0c3c13170552100c00118103500180c0340007800a80c884014050345034420a03108080c1c070320030001c2c00181c040401c000d54075030b458612607024040c00300100f1405081c9405580c1c031982081014802c9141c80060390500030344c10380e81501c4a00404000007180f50081c89818445001300172a00d19000003602c8980007240107400480e6190760030090000113601c0782c0c0140c5041c80c4a204105018a484010490f48807820b400c5889440400c440400050307a410082c41091b641c003079001c40300300740608000380050010f12400042244000780380c10803062060340c01c030720a02d400c6400700000010402030000c020310342e0280601051082003848081130b1405107a0303500c64000e240140c5840e0a003e4403010030200c83d00b0441c0480c1e1180d91315011980c0041d01c0034064041920380030309062400c444103135100680450706110071000524002010f6080d08007001e21003500460954400724804025540c2d003c0d44000d481c1070082d039010601a40c404 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 261746897 1250 261745647 261745657
    0x160b0610050d05060d020d080c010615050a0e1f0903060501290d0b0a0603050f160915090b0c0304030b072609032109010b0301110d050606040f09060614 67
    0x9076940d00d040081ca41410001094060140c0b035100345042144401079444c50070021100384903c0b180303038840c20003044036402d503495904005d11035500e89a281c8143d56100042d90617034401480d141c209001d02c00f000c1269082080781c19a04400b200e5000b40b00d417500420520700703da20401c01001030381ea0310510000301c26142c0c0c030529881030354034590004e900c64860250042d9030302043c001411042000000c2c0e426520380d4010f1001ca901d42d0100180ba01c3c01407803142d40003501c04d0000100d100280c100801d4401c550040c20a00800c090941410901c81d0380c50074050188a120303182d41300805141c2590307130341007031100b111188120b60001d00464414244040c0e542c10402420185804001c069174100c1c10040c009070807880140501c03807510304405080504010300c110003000d1410500205425510100350042c000d80c1084456890b110b28141242e092040520000440d51107010010304248140e900c0030100c9490b2a1010a4008035035202d00c0c202c41440e26541c084954004400356207000e0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 261748147 1250 261746897 261746929
    0xc03030c0c01200105090d09150e0111030405190911040f180e01020d0606140f1812031207021603020310050910060303030b1009150c0215160b06 64
    0x548041e003140d406810b0030041d84003003d5054215220b8004a03508403082100c6841c1039074040b100041040e40c01220840c05000040c05420a010905202070700d2401c01030101810001d030744048070402e40b810300548014050041c80740341b8024494850403c80c103221b00414810518200a02c5111040b00c030480f0115001e01c010205000d2401240d4000c420581442c080095210321900340c50315001c5c0f0082050300c0a0110005d051402d010004003030100c10560144643c00403c0a0348010503403070241c035029250007542e03510702080d4001060301c3d2074900d46040114440070540c0b401d903000c03068584c0c0c450a190750071503000c1d440040384000b000746e040c84040e403d508040007440040e04c140c0c202036400741b10641116211144220140200c03000c6500540009036200030b6075482d444d040d5200f4100d1000e6250603100281031580703140c4180c0c41318880030180001d410061046449080c5003044c00c2c155440d200d074540380c4d84103031052011828002100d4000b0100000f5005160120b100000300d20 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 261749397 1250 261748147 261748153
    0x90f050f011413080d060e1602030405031e0703050f0321011d071403010f0806010509152e0906030c0315060c032a1406061e01030e15090c03030c 64
    0x200c0000c0f542220311601003d5440950810695002000c503004000c010150688268214900b1050b43c109110b0340c1800c10302150030030001004075a60000b49800012048242c440707030042d60100052402015900092041c0201c0d0509003d10300088007410b40d8040d424410110700d00720b81111101d40a00340200901700c80342200c0c6e80202e1000d64503c81c4d01512034203100f41c030606030308000101070f04242c4c04110080d100520601800c07009120050040500751010b12042c10100315075034142c0112034125000e0350030200c0070150f0341400740385e40500400842c4184003092803920028070b0750950340a40c0c40480e09120900342030b54880c1c8208044d201000c20407a00c1107040c854100d80062114200364200442c40203940c2c46840000b541c0d4030510100c0740c40721080c220703d240200f00340b2020000120b050b00300d1001c206140c1c9424210080300b580e6010a0a0403035040401a00201400c05200c00180f05000b20b444070600445c0c00c0b1409000048200c89a00d0720f40c0382010350741e00c21459040000c0d0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 261750647 1250 261749397 261749401
    0x705060a030e010e0609070f0e130609020a030b27030307020706050a020c03150106030c0504031203020304063804060614030601020f0d05030609131e0c0504090f050f0114 75
    0x1611a900000c42c540c0303210008a200013580d107103585000c0054901e8407417074122000c10014108806101402005c4417500140c80b4034040c1020301c902507103400301621294a403400e8808564900d00c911019651044c400311560418034120807183c540d24079aa03130030344080300501845080010540384641800d900518016061000803030f960742040d812101984148242c10740c5070794051109290340840d0f659400d0a5614185004003500d41101060b01031210400c024808145a41d2640c1414aa10f040160303030ba032510701d0007600401e89502400c00540c4a444660002c00780000c0701025110010300c0403c00c034000d0750400084804603c03840004ca100c1a000040e14004071018581c44141401035603800c1608003029801c06081550b40e4000070b00000c20410245045045c82c0d8114245da41e0703460355034030150f6807110350840d00800c2520301d6807032407144410064051594005014060001d0240304014a45a1540e07010b0728000c48103805449450300074940144511a100b211103038001c03c5613 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 261751897 1250 261750647 261750667
    0x41b0b0403031121190e0a0324050105060a11121209060114011b02030307080408030310060201020702131d10020a030e0309010905010804080c0613110a0b0d1503060c05070201020609070506 83
    0x1d80d640b00048030901500c1b07a803840859035445a40e40c0114041c0010b805882000c00c000c088840585894800c005c0ca010014800c0da00c0d0074042d15030643c840d0626845000c5d0095449240c9030711414590b035440c000042c09a40d071075101c10428001d201800880c1c80390390f281c0c000c220b40a08001c18460024401d41c0c07040703071140c00c5010300506040c009401e8929101f180c1c1c90b034001941c0250020b48031a400081031102c1004920054001030626100850030b1484560014054005c10b2a030140d940392110700441090301c92420400c520140c10080342c3d0300101c0b40c07000d03401035040008084c1c0464944410300450460100031111581e0f8140d448040f8581004015900980040e10a54038a0340038400c081050790304121640c084c440140c15445480214a008070300d072103c10500c2405031050f244100302c450700007001d603403540c081c1900100b1039948a0000d0b1046155550004c0c01c0d036030400700c40000140d000030041080ea0b0007039007640c0c020b0b070313825559076540e4119128464010800300320313078402 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 261753147 1250 261751897 261751927
    0x903050f1612050702090f01030b040602031f180c0c0203060f130b04110f01110c060a02190b040605010509100501080604180c150f08041b0b0403031121 67
    0x1580c030030140d00003003403000e4031541609481040c000b00890000164403042d49001518154018107000442000b9815aa1100b6550601800090101350080042010f01c20545140000d08002d0a00004900e9880203000200c90744103800c0f120382460140318000ca54414410810055009070042101c0d4443e05030240355410001c01c1620007901441c10180010340000003240210300400841520007003410801103404001c52081d8107100944610003240d410100c0c0c40b0b20085421540c0ca0b4540c8541102641002984610050800b9110041104200d408a001d80c02140030f40340c100003d03030301ea8080c00390b108000d503400b41c00d1a81910007000103600c903040030743d80820064004a01290f24070b2040c0d44d03003404840200d6004d9201d09017485284205049140024070614040b25070008ec00c8014010741c0002e000a000101d20400c40c1141c810079803000c50013058840171565031141c0e43d0070010124058180001520b001d8000321240601d00c00741300514698030034034581d150002c03401520003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 261754397 1250 261753147 261753157
    0xc0c08070b0c040b0403060903030615121109220e01021309020a090e0703020711030c011409060408160807060e0117041109090309030c0409081605160b0405040507030903050f 77
    0x2039040b4108800300c0d1551059020b080103501c60000404e14804510300941501c0b540d821810441c100030810a0407281d02c62850f10721000048400110340300c110f00003c00340d20a010110b500014810081cde21021244110250b02194003036081111800d8110346e90f00781e00c926035101d10301e1903551700180601126a40100f1b440c590909002100c01d95411040707031704c0e0704202c0720400070950105420303041c0b00c0d812071100920751080f8050243c2910a40000c2c020000c03018002400d02c5010074041d0903a22503000700e4001c0c0c16108100e58205940c003e211407022514001c25807d40a018800a0b0f04c5019550b02030750700760140c5442d00c09a0490092580b032050042099910b54000c640f480b40c03030307102d0400c600d0141500304051607443c10a503080c940303820550051640a81d00e0703d00c98078041450309003916900554011410480c0c500303410b14034905451181070b800c2d10310280000040b41901c8500510807964103032420301c0144d44400003039003114900c40303024001c07940800c00080d009807120f00401c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 261755647 1250 261754397 261754411
    0x803030103030f120c030209090a09170904020f13170303150904061b1d031506041503060510170f0a03050a050409060e0405060615071b1203020604060c0c08070b 71
    0x2031005080b8240c0e91040d00c2c0c80a94174030100786e0006d6070601c80e043c410000b80d8080744000c03083c400041c09030355000e8010310184001402c5c0b0400300700c44019903101e404036241c0359846513200b17465140d07120103221401824441d0548112004840950b19400401520b22074004112172403103e80000341031056941c4002d004490381e0303030b448d080e000c0b150f802e80d0b80c1c91003a011035a8541c50f90400a800f070040c801a001a8203100f40c3c0300c01e20b1710910176280c4d04401d07804401035501042e400000b08403803203540c0f86078100a1919040c502007001060528080c076040700c030358661003145030030504280e40d1109a0a903884200790030042764040405e020744000e00a540507450300c0c40c68207642c0d180c45d00446010307800c18074683c000c180034403051080401515400890448603010662900301c4a0360540c031030220002c0a02500002c10881c3d0003183c2c0c8041c00178442d440210159043c0c0345030094403221308540455200e45400d240030541c1d4414050161031a6000b00e01c1d520300540b50300c4401c00840300510700 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 261756897 1250 261755647 261755657
    0x1509060d02030d0f090603090519020118140312040608130507170102030a0b0319060b0312120609150114030411041d0c1c060903020f06070e0315010803030103030f 72
    0xe400103031402c000000404a03141e59070f84008020001c002c113001d0440d40031404150a00c0c1800003c81c0c000700d0712208803605082d4888203504a4801660100e02c942915284400007000c006900c00c0300f038130f983c00c00c00740031402d41e20303044624035112140340920b000e041d00080503000086c0c40c1c1d2800c07241c400480d138000c0d000c0b41e400e20759915904001100e0309508103003994000c414001c800085024101c42d040c012400350001144d01030101d81c1001008501900054542c590889580c030300b8041654030704d5610000d06d0381e5429040c1c1c11a03009405444881c040c0e81c4080005903031101e41c1c00c800c040040140c8d2210480e44400075411240d800c060070070348041741800709942c400da58600c90036648881c0c800700c0c0c007031401400d0901d0341041d044450190140041c6003508910051411485001640c011000a454030300390908906d0003550800c03048243c030138842030011707440e009081d81c080034408400300d0300c1d41851421012605c0c0b20030310400d40c1d554000c1c4010310000b8010145039007032450610704 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 261758147 1250 261756897 261756919
    0x201090506090f160e06012007120b060307150f02010204050a06260c0313080d0f1506030b061602180a02040e010b03060a1503140406051e150906 64
    0x549003822000e9802d299103500002003015050f40078040500c0d010b0440d608024000d00e80349005035240320017000a410041d83c01c03200c900711007100e208542c24050403000c94000580310503229064060001d010b0b03402405200004269244c00100801510301b0b40700201e10148145a09071030305c0040030b14a4040d03540034032001c222078583c414604000c0c07400756640c0303907007111103284c101050359824031340c481c0c58201108004400c1c500c0030480e42c106900e05401412002e03181807100384c0b17004110001c0355213818241003400302e0015070454415043c152028941007a5600400d42c22145e400c0201c6400803024040c0d20340e00c555003840035410500160566421100b152404156403404a03010218030781d01060511107007824540140c05005c40c00c116529504020001801c10503181c40303000700700380c01d6000c4840d00741d120707800208064406002d170541c141070a00d0198043d040031950400500b100300c400518002a1030026070041c072400304448098a0020284501c0002c010302e09904580c0d03000c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 261759397 1250 261758147 261758153
    0x9050a0b062e0f110c0607060e0d02010b040c05090306060409020402040b0d0c0207050907050318120c07140f01080a0209030118050d0e1207230301060b0309010f150501030507020109 80
    0x242d81c00ba0490b04004100c8010300c5582c09001d40740040c842c00c007000544003619000440000350034841400450302180c07501114a0000064454107442c1640b90103000b040c0c40340d8a405404c45400104200e1b0140700c10040c5101c04c81d041d0040c02740d442c1c1d140d8003500110b000303420554401250140040d0000d4542070305c0f45400c0d81d03158480e03504041013360351074081c49000c0d4180071000140c00c04076050f50b0315080100c001051404040e100c00320031050580f201707211550801c44040403510403420039448480d50384002c0d07102d280b14800c40e07a0f01360034140b44203614500103018200c1142e0584034880543c49a0640d40c0007900800e039030641540d030b944107200a14070070705075010f5000d22a0000305504106c1c3c100040040351404007582c0252401e0729144101d203408101041075440601c1031100d031041c2c403049656165481c0380142d070594684100401c1480d01c2000551041c0c00c180c0c000c6c840507240350440d1084a540c0c04410030300a10122090040d0341c800d803c443d4020f02c00d840003160503000c5407 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 261760647 1250 261759397 261759439
    0x200c0108370b15040b030702070f1d0109110714100513110301090302060601030b0d08070b1f0518070314270613020d031209050709050a09050a0b06 65
    0x711414200214071000584800380b801150501a01500d030504414680408400d160086000744240108081300103401103100304124801444a0364084803202d64034800190340c1c2c0d00c04441448041041c00020800f64103038018002881211000d0b18031341940c980f140c1c615409424941c130454050820b50649c0e10b68507001c2e0030300685103407408990066540c034060015980d9080e80f280240d051501c010042500401c2c0c3c0c03640a00c00382404100031150700d0000d0780e40c0c46200d0008009002c04560013091160181209216400d0744001007010402445015403004a42c45160303800b01c01d4a2800014400445502e500949141404924030011100108030740c0c2c0c003141d0b540c11024481c64071b1141e541948400c814080c10420191107141403480450308884000b0002a020307042c0c2c10485c0c400c26120340c00d50201070b0f06c4644c081242c800d5524060392a4001d51003042021801c24002ca006054584100b0b041c0381e6208000380003c4419940340f8030188002003885502c80307813102010f40004030f45 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 261761897 1250 261760647 261760711
    0x1b010f050d1121060a05011206030203030f070b010816030312060801051602010c0302090d14030903060f0105041b0c03031d0a0b04021503390a0f200c0108 68
    0x81180a8036101c415084078041c010030f40e080700b0300da0004400d01000c1e840c2d0b5031074007094810a18040c00c2100985100001614183c0d20007501880001118241c1048080103815620322804c03040c60301341d907903500c295564089450b1007907035444003000410010703000d0a8490a422152080815000e64950907242128030450b035030741c40b001500d0040d60169174284515240c1d800c00c0d080860800c100e410104070b05001d5000010408040c4a580c02d001481c02c10640b8400c0c1030040480d2500d01d0001607000170490300b841154051810003041c0b020660b0802c00a90012110b5507800410030b045071412000307001c0381c0c115008200b5900e0005014024240091811540104041d1141c0d08142c8140700c40d01d81010360b0b5048082040c02442011021310300510030442c0303034412100360441c1848092a06070310601d0210404980040d41d100090b80045071084413440326140c0740600e41c1c0219040c0104603c0c40300c2d0070a150042c480002056001c3c50625400c200b8030301c1000c0c1301d041c014800041407100 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 261763147 1250 261761897 261761921
    0x12090c050a08101103090a1401020f0703090906080304050d11180a0905073011090a060311030111190e0405100e07030b0d080307180b040501111b010f050d 68
    0x403098843c1410000d00078083c241040d60842c40c40c600d040903e039611106200c2000f04041d024203d41061504250166200303032420709841030b6a940c00f07140c00b03004444148156864141800030000d035059000c4281c0d41101c2000c2c0501c00304400c03503501c00d2070f1029003040710f80d4082200e0001c007080c8004210405d00c00c0c00311300c0001815064600304545008504d03442802015441401020703d48102c001400c400b2000ca000c0752a050560f10300500d0500c07808040c0381c1c01032609410801d00d50400c3d0058001c40340115a07044a0002c490300f03240c2a1030801c040008001020401e80100c00b1540b80390b0b00d40400035280402004e03411000107416600140c03402c0c03041940c440820300031400440007040d08954181004c2100c80e42d0003010400703c508400025140c20030100000700001c4c0640200b0b0445829841d40d60000707038403100310700724980107401602e000429915041d1101480003520099039842c215180300c034021030000445200f6031409000041003000e12004440a1542c09041a0002 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 261764397 1250 261763147 261763153
    0x602011808071401090327030512031b0307030603140307030e06030c0405040f0203100b0304120e1201150303022a0d1a0f0106020606100509040c02120403050322050112090c050a08 79
    0x2958114000303800c03c3e290f030640c0c2030000c003802000014030001d00d01c0c00911811002d2074403681d8191900c500d1533210400c8190800c400400c10541c00da0680c441401d03a440340407820b1180540c1c0c104c0c6c43c0d40380501c420080100d03003584164052407425101641e8060074503035125180544543c041001d84d0046008404102c0d0040140840046000c1005000d010329070605400d600d00b0b5282c034100c20341440c0051051010382e1020030256111518003042d500722003002031103072088012401100e000244030590040c041d490b400003c00091190030340111f001503441c80c078803400740820045030503d10702e02140c003601041036030300c0810151440288181c680c82c11900d16589040350203810000300500d118420000c00c901408402e03001426900c601405031030010321007461b07140c240d10706000942c00d241c828001203070000c00c212000004004624084410b54019044071012440d0b400203405441d000c41c0401840344000080b036403240c200640500100700f4903940e100c0114004402907040210160 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 261765647 1250 261764397 261764417
    0x5060706021801080402060a0507020d0c170105060108013f0f0303050606090a09093003110906160303090b010e0708160806190f06050301060906020118080714010903 73
    0x140c200c11141c02c1c00e0300213080404062816034000b032814411400000144440030503600c09640f6042e051104a81d4040c10000b403036522145c55110511043c0000c400b50760030300c4000341c03d5521411416048811100700000400ca00c2d5240c03001c00340c50b2540140e040d842450164000044000c20b02000c80d0007a5542c8405e5001c80c02d0040a4840050007507010704000c1090b10130303039240d0070445001c80d14004000902c09140d407500c00c08070080b0f1040075603030750908403095294a00030040900810303546e0f201040502c1805613082280c4c0507140225910003010f0240001c0c1241401420f5200ba200f442c0001d00030742030307944003001c1c4002071304141c840c0304140081040d4503410420480d00422592100d0780e034421105001080c105004298900421601d61034802290941100341c01500c0504460b401e10f50301e6000052894002f40b0030100081c00740714000034824010b2007140392003150203101c441c0f141c0168607a003c85500040d001c9901903103440700300c2c601e80802c0c030510340c0991182c2c1c2c40079006 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 261766897 1250 261765647 261765667
    0xd0204150815150c03070605090709061d0c0f0409020406020309010f1e0e0d05010609090308010f031e020d050a0c1403150105040f0204120b07090605180f0a0506070602 74
    0x7054020000326003444441c1e40d4006680d01c00001004010624942d990340b0581d6003211415401a0742e4024600f50500b001e1082640002c00c035241513420352801004040d03a42c004100d592500c21403a105816525804100c5a0f1001c00052a1140760308451500e02943d5400100480e4400c0d03004c0c07030058001140f54066507901000d0380c40105000e140c02c03e90460640120360464046a5405003440b204215415464a92a04105841d60844001c006441d5111560400b0b05031041c01140022072440001c201781580d10360340e4055a40001e40035100c01c1201d0b01078034100c02c0140081c1d07400030318904da410004500300300501d0280c0c412103007001500d14004983c0c40c900c500c500c04a10a0b004070152441d18424907181d5411500b00710fa020484505060a60000344216000040e064030070300351010610101c3c24a0302c1c0101d41c0c0b681d800c8021030b554030040380d690091102d030044480420407110300074a010078184040c201c004007290045583c500016045510145040b58155000b02c1c034400a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 261768147 1250 261766897 261766907
    0x12060d0b18010c03020405060d0902270405060609090a0b190203090d03061505070813030609031d0103050f0c0a090816030311070b0405060c010603020402270d120f050d020415 77
    0x40340340c1424117508190030a00001c006001e448050b24904e56500030741030540d07a4001040300c201d000070380343c04000c004496070003003942d808403800d9030070703100b0003010507c0c90400c05042c0c0e200d03241d65000740101c4c0e005a0749600c001d01c030142640c0703010540040d11150070321079440114084c400070070040110340d0007254040c09841d05680160510609440c1000113690040110380d00d596004171001d64409400074104080416a040582004d2078070381031001305500300040301111045040c503d1a2401a540110199a4200d4038a420001d03000c000c50100700c210710181c41505881e050156806072203041180c070303002c004031420f45d21117a00c01e41001490380103144500c440826001804800d401d211521886104034031585002e52000200707142800c0d030a5002401030340e401041559a4598559047c10344807101030045081004050b4800b0345241c02e40038001d426500c00442c0c03030044420f80f01682c080c04001d070751a00f44030741009040713052802c6100410140a85209500c3c410500c210018a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 261769397 1250 261768147 261768161
    0x19050c040302011b02090a0e100e07030c1205100c210c0e1516050715020304230907050306010512090a0605010b0f2502090a0e0f010207020612060d0b1801 68
    0x800301ca6100c40301300c0540c40e1100c68503801010044082a040c04011003d0b241007000444522441d01e00722400c8032a01001c640c2604890003900b50044543e29a110010b00ca221450000c1c025801130000165100181e04040c0340ba40310f60800e299045440c80e1180100034007501214285585d600a00010300d421803200284004142d51914040c080516044024810750650181181c0d480141008000c01009441d010340030200c2c1e20f248030683e28030047d641e50420300801010b040030486241d0380c0310261405e44108980102070035080d41740c0b500d0948140d40007a1072141003080070442601d00206180c02c040c000d1400c03000800400d0700760f003820381c01c03280b048c3c000711a1040d0070071101281c0b440c180141c42110108908410305455180c1450f1000004160001e411004410800c40c0075080c130351000f0803000b40c00d4240c03404074808801c0e1f00e00b01e216103000290300c4682809400000e05541031030662040d4003824600c84a8820344882e0001e000840310800d42030100a030f805000a402e0041c50 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 261770647 1250 261769397 261769427
    0x90207060504172a07080a050325020d020103110d02042d0518130b0c0d11092b05070b0307110d050702090a0b100c020f0d03140319050c04030201 64
    0x35080c51a80344110f448007045a104013003d07000710400e50400a02809100c0043c08814100c2ea0713070340c69034508161682c2046a84500c2c8400c0d80101c00385002d40c5181c86440254018192280320380740e0307401074004002c05071600c094594288a0250030402510080000d4040001d104480c0d01804541d0340c035296084888041d400b8404200300841d031100d0382100b0034a03080380d450320701c0c07a1307540b0303503590034440a944001e0180030700340c1c2c1402086001080203068407800301c1c1080c003021101744800005480342c0b19180360004000440c08106c087c40b80c0007565a95240e4480700300010541e1a540c1c6490780b590012040c4101c000280024207401a0915048080d0900a030100f0405050040d2043c098064080d014500c60800540300101170352018105880003407841c4060101408d0051240c080044128010615041d5079851881d203800300f8003809501d55a184d41900c803010001c00315400103010320502c00c0d00126491600092401084c0c40350000d02200c0343c941e869400010007041c001d41c007070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 261771897 1250 261770647 261770693
    0x2011a1509010804110a0e070e030d02101505030604050102130e0403020a02060703110a050709060803120406021e04140a0e0714090d0f060507140a0f0c0c090207060504 74
    0x14044008142514007141003400d100c0764540d210709248009582d030301c600ca644500320030307070204a1400c044006070282085545118030380d4211410305940740c075080c1080002d0303070202c1c1e201c414580e682d4001c4a208081000c511105941d2900460b01c2c140c01500c00325926500030560f41342d4018034068a86c01010915806601c5087c951800303034946124410107030140328006601d106050048401d05c0152807070008031507194545040c000d0700c440e614095000c44500b070210000c1d6940000040e2200d040030207802c5c1c0301c0c0352186c0da43d1000a40c010410b86130a0944080702c281c4d0904a080540000c00614880008079508102003100040050f0054050701d01e0a00074081400c1d8070400d480d84103081a081c03181d0380c0c86082c00082e8a20018000204060355400c144e2040204582050f0f0181b011900c4410404445c481d020b4024065880010300298060a0b100d40c0540b29140c0001503074011b21401c1e01c80e940b034541c0b150a9038084202610305645a00c01d01040100c0c1201400003400e040c020 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 261773147 1250 261771897 261771919
    0x20304030b130f02120a05010b06121f03050601080c24090d150c020f0106050a15120f090501020c1618110d2f120103121e02011a 57
    0x14203100c540c1c1c040d2051402284028209041000c0a445440e40c0c540080c80d90802c401c0200e00c03030785c0e55a03c841c0111815428030030100305500307222050301e003800300390f0444200715540c1e1040d0403080c000b8a80690902d0200c1c55000001c1801846078501904003400605841d107501c10a0212145004c80d4020400c03068a14081c80000602c050f6000400102c07130050150074941840b81d8000b40c982121014185000000310905400181698102480070003d00003590b50300100861046580b01d4801e80c1810b6000256200340700d030405036075034008140005003060301c4940420440c0c1204200303e500341c1d40041c1c00240305508100d80e2002080b1405140205070612040340b1071101100040780c0700d10344170300300030007004c802105840300303001c0c42942040403603442900c00b54001820810510340f07441b101200b1401020520840750f00e582d0303807a0070744490f03445e603945d1207845054210341343d0820a80c0e281654000c00c03110500c011701342c040d031300121b00c242103e10366203030100704212414440c90394046 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 261774397 1250 261773147 261773153
    0x3091f08130c0e041119031e03020706110f0a0b010e1b1806040503150f1006053016120b0f300102070303060506131a0f0310050f0102030403 62
    0xd882d0190342c0031015848a82d207981c80e00001400ca11a45140e004882e141a1031401201104880850340a40c0170b50180b012503a094000030754080d5005001a00940c1c414860240200c4008401c400020121012075061500e00da05004082c2800c803000001840104640806c02c4a020b401c00514541d5440c2d2103949080069680f00300c12048010000c441502070555803030748280c800901d03024064811040491640303ca024100722507580c0e40030a0f01c008201514041c1c130410061b15010f407100b5240070441e0200340c00ca04144a070803004010600c0c075400d04a03411000c05401480e21034019090501d042101a104072190030803424414030b07081e400d0240766a0072590702d41c541c1042d900d41c2241705141d59840e06400004241c203280c200c401e00500c0b54200150300500c0340324003a80c1c1c10000140c90303d0401c80d25100310110180308600d074032001d02c11544079042140d00404405641803502c400f4403000300c0e094204450440380c0d114100d404002c1403c10707401c800307400d1009102451500341599 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 261775647 1250 261774397 261774413
    0x305010c120b0d1b081b01020d08070e04020702060409090f02030606030d02030702100315170c0d02130c0e1c05060c0f0a05090d020409051b04060f061103091f0813 72
    0x3c60050f09100c01841c0e04503941400f0b181e040003078440007081e9403200034007030811402124010b00c0d507401032040040e16803605100d52030703040c0035100e15034032a0702c10a44c0f041000b029402c8003400341da01500c100000a8100803d2141c1c2d40f074544185031044001c07203a401007504004004003c507000b038000c00e250f00e0516501004444d82150304032088040c2c80c004031811002014040010941c01c8082c050104200e0401a190036140180100301c0381440000010311003014070445009400050228450403001280d4011582c0c2d2a0b047c54a000024402e50008042d6001001401c81800d50445150f0a11034140440741d44200a170500c58904280044005060301c21802841e04029011582210554810310051001900208240300c1c0e540755050580c3c6540c00c4007004064400034595a5825003090b0040004586004810702d0290b85011030581d0b2034141d981c081e00032808100a45000c03903599100d00c841d01020711050400c1d2130701c10200074202103009400700d940d1700000b9001c000020320340303 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 261776897 1250 261775647 261775669
    0x7111603021c1b03050d020726010b0411040305060604051302010f0c0209040b0a0c0806010905060c0307080409091202011e0c02030705061801060605040b0d0908130305010c120b 78
    0x103681c035007040110001020070b00707020000c00074910aa030480e840000e0604070500ca0580380104180c0302c000400850682c0d440c00b030380c4510b10a10304444c61001c1d950000081940004401c4000482c0302003003040024100d07190ba04500207510000300e02030050210821859038003840503038040005062100c44012000440c55000f810003841820b85580e40c1c1c400d00000606a9003c1d210455506051510404044c4100c0d41c094440d07103490704403100e09101c1c120039401090180c440148032030a000900c01c0540c00044000d426101c100454000904000010002844001d000254140046c507002c030b0100960300d00b40d011a81000120445800c4501c1c40ca030010036035001c00216036400440681c00c601915401500300d0280004012400001511801d018a01c0c203008200c2c40d6114074064443e0301940c01014034a81d0240103074440701d58950300195949001781c5000382401144c04101c1200c00407600103c0f1140d444440030f02805810060350040010464400c0c080b00001c80041a080a15 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 261778147 1250 261776897 261776899
    0x15030c05040209180a020a030506010f090504051509010b070203012910140a030603141501090b03010902030d05090a06050f0d09020f0a0303031401060903050303010e1b030a050711160302 82
    0x20000b0500815540d00c2807040c4c0a91090102410900d0403409400082d08110303a030b200400c1c1070400180c625803081c2010745e03911800e41c0b9185001c6003090140402460014513800305c10404440c8140c40340d492a00b620b00038541803403103aa175501e503032040c10b00f9100802c195464002c990700b1055038030764107602c028201c29026156003030b6488244804036004e180c00003180349260000240c111b5000d50581040301541d00580b044558284140349407070b03a5144600041901c01035040c0148401141ea42203054200001000407440c440c00e9000603007442c00100111000c40e034000b44040f081e0910340c125000906860034664144449220341100500c10310200c500b59035600e10021301107503620408072280d0000600742ca0f0707120383c0300d10300680200060b03241b64400c001d2500000032554445d0301c10b40d003030300d9200000d10306507481c1030040003103007070060700c0d8504218007801d40c00008040d40010707504c5228107810120303080c01e00c0503020b010032100c48072900389608100c03c44005188000b41100440b64 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 261779397 1250 261778147 261778151
    0x110109080a0b09210d090204090c17010b0109120b13020a0807080607030b0a060302160b0a0b030f030f070b0c041508070315030b1506090307030c0314010c090e04082a0115030c0504 79
    0xc0140300160080041e4803005018000ac450003203201040713080c0030715541051100030482240304400544001d107180c03150305091860401d21030000760441070a41c0d081400308002d80b8a1072800e40c00130310840702c1d9422014499003c0b00c000c0200300380400507a1f4004019080400844e225407001c181104c0c1c1d0b43c001c0209040c5c00150921400c0c020214007801c154112603440301a00f05001d000c0f0242c103040074500d00c284240d00e0300000c205404803c0740c10b191042070582d80703004291b5407450072400005040e0460b00c2002c1c04001210301403200b03c0400400a5900c910342447d000c4000303021699240780281c81f00215910510004520802e625040341b02c440510402043d00c0000403858071518280c0d0350140a050350000c02c00c0056140c40044d20300c00c42103450045070b2000c50600301d8810fa40d40300005a50302408201c03020745a0001340d001402007604c0b0307240a00c1c42000d0042034900309800c0c0c1ea8043c2281d00c58058402c2841100d428030311004d0b02d1041c8a140d40c41c1e1001c8244079005442c0300307035 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 261780647 1250 261779397 261779411
    0x619140c071109091006060305250c050f0a12050715020309070801150501022a010804020607050a0506040c05100203040b090607350f07110109080a0b09210d 69
    0x42c0340c040c00401d150006016218900d480e410341900c0d6014100301c600c80303c0c02c210020620600a0090342d10908195a00404000076080b41084449000d0480b009204030a09a180030a03003d111030710515a07442c0007040c0544544c81c00c521009166050082000002c0c000d5034001541000d540307610960581002d43c50740c9502034810b051005a03030000c0301a602e04500b28541d1a180c29243e01129001d8080c0c0e290501c040c840e9001103c0355100501b1060b01100b265492580030fa07607900c0d0014005001141448040d6440c9890000c07511410313126035000b070040200300304800340380c00c02602d01034851595100419001135500d0046e8041d00c87c010304040741f900315a403140026105604d801080803818810003046001992480030b022103003c002c2c239a51842e400c0b00450031286041380d11840c0c0c0d464480e0640300c10403400061f00f0410704001582c500060950810060fa1040030700900040d20725083c0200f115142040c1181c03160748000c20302d14140030302d0030401c044d0b40c03408440400118541c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 261781897 1250 261780647 261780653
    0x92a090902221803080f0916030b0903070204050903091318020f03030f0a0f14090901052e020304210f1e08030c0c1e030a030e070806090619140c07 65
    0x6480d08101c41c6030300914800c044400c1c0350348020068050314000610300b0003921f5100925031580c126640200301807003030310070800010380001c0e40366074071a550000b5a410019182e0010301907031806d0f1069010fa62010403105030f00d16001c00b000e50018410401080345a900c0c006032000c080d005440a4800c1002a00d00b5501ea10300b842210000b400481c2071aa40d6940403401030071022021400c4030003c6c1c82c1e000c8a9480900710021625250317002805180560310f0401005211030103440700041007010703241112039200149015100b042030076005940c072181040c40400d0850b180803005d40c1c0e03824801484201140f038080c606901c0c0c5030001031303d106605035801e003000b448404d078000500d0345070b0010406c410814414040e108003030550054812401e81c0340c40300c10040c0078011442a541d00200132201070f590180d40882c20111015066031200d9554141050610904644005090300450100a00c890360840c2400841c03448280030003500c05868504410b03148001c025202d540703000642c020074 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 261783147 1250 261781897 261781901
    0x3050702030123070c05060a020a050c0d110d0305010e040605060303121f1710020d0e030301030c060e03030708040b18091504060f080c060d092a09090222 68
    0x8026006030080c495a40092100300540d07500f90050708510810030042940540310310740410b0303250341080003400c454444a0003603009601c14141a0140041042800c41c003101c1840007403491f0509485003400525079a04090030001601c03110810945403000620401084d40c030400d800903000540090306070b5030304000c02d24500c52802031240407082c5504014004420300300ea01c00d00c100030600c030b112440c0c0e241d2544110785822043c20001d504401c40869000c03c5960140c907444c2094400031542c940d000520b541164401e070000e4a00d402d4030780c000c6c0031035500040d5800403035900740d00a520b8001c842d210301c40180590700441c41c140100061503040001040c05030000410000c2030170503182000c488492600303030f040140034011806c001c0d0025000c400d90000000f01c4206802070402088074008205007580414840c4601542d60010400820303130b441c0d4040e59440c941849041c8102480c01c1c03e0040500c1d40c0d2100310041d040407120001030b06e030ba031110a444809912074154001d641d10507400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 261784397 1250 261783147 261783157
    0x120605060a051314060d0302431a0304050a12090b0c060f070e0102061605070204020c0a11100e060c030408010c02030d0b090c0d0207060e0f0102130e06090c1c050c07120c0309050d0305 81
    0x51944405d609c01e91402d00040100807140c4403400c0194034075080070300c00b016020440e070191807500b00d05600f034003180030415443c600d0145807411001881c2c8038152038805410805085855a00503410480d1141441d80d4481d0004007038103121074104e180c400000c0d0388a50013010000090303a42c465426825009800342c03061242c0c018415911a90360154981d038641c0000000d85240380202c03006501810403058001c480881580d85484401240d42440400d81c4180400c2c40e6911003004009990700081c898164101440c1d0b014550b03c104503080b1409440310501100e20481200083c41002c1c003071f043c116000c03c1490040542c42e904142040c0300105928510074065000f52000c0e112050410b50041011075640d181c034001c07068541d80900c00450049419170307040507203900491070000c403440c05446080d0503400c2c40d02c03004450700343e074070b081c0c1b1425140e503030f514280402c0e80310400c151005510b601000d50310705041040ea1a44000f803800c4614415036000348003400c081da0030300d8841e0080f10 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 261785647 1250 261784397 261784483
    0x1012090609060e100516110a080a0207060f0207060801050f1f05040611010e0d0c0c030f050705040c0203120103061805031209060907120605060a051314060d0302 71
    0x10740ca50b003090000703000884064a514040d000141d07102c0e154600c03c10b8041d1044400c6241841d110f041d0988100210600340d22951182401210006d4140c10080a040c203031540a00421883c00da400b1344640c4101c0e54105c10354114403424044107034051a0a81100c00407542a007a00c3c0b0000003154051105129a0700291100200034801982020050040f140725503074008850030b040d0515801c90f8100c7c65001002d8100518810320644521052070321140174040c20700c2015030700e81d14100314000268048840750444c4900b04000e1070b00e0b00c1a00c80d003c03058000b075071906807441e080f1001100c050000a024907078071014464111040c030128042542d101040340e0f034030700034400358003c2e1034801c6031101c040b84161000110a0840882d00008880f18500c1004030b000c803503a600d130003401000f80100c1c0c00103d400d038000384646d11006401c851031020f190000d5400603210991051a01c010401d500a00c0c45c0e186403000654001a00050b5685043d015000c205030500a0141401011655 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 261786897 1250 261785647 261785651
    0x403050709182f180f010501020106060c0f020a08030307020705030c040b03060628060201021801030b01050f030a1b030b04060e09071a09091f0807030c150e090705090315010510120906 81
    0x24a403205405036600d405031406034880e5030280e87e01e10049080e20304c1d41c002c032400600b003070300860f000410350350b100d618a40c4000c2400000c60348a0700000e166403c1141c0010069000841c02c200c107060501c40300c00d100310255418081c4c1810315001c269503080c003611041c0a6855102c4118081e1607084685403600c091842003100030790b0b0389030003e020350401070030001181c40f00050001a9030183c4150141c980044c0c459605011211400b07201681004048801050715242204588030000740c012207245882d0f01c0028014410784144422184a6004050101144428014030132400940c1c2421550451070a00c0390040250444d0014001d96520507000a044818021046016901d0305404000e10a202030f9003941c038091681c0c1e4041078840600b000c05116000e011402c0c00080c00d1081040d0707814401841c502c6000403405400d0200c0305c000001c2c0c00468000346a1806102013401c900c265004d00000354106800138940b0442d080709001403010345002400c1c050126000a04c07004e40101d41 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 261788147 1250 261786897 261786919
    0xf040f05311409010605130911101809020406110604110f0d0c0e041a0c0301030818090705040911070b06101103040f030b090102030403140d0f020403050709182f 71
    0x11440c00717402d1030300881e0300c40c60408081092160b8940300e071450607504201071002402146007809240b41c40700b0000b9081215240b000b15400510084101c010b0a903000c00580e920716104005120300b0b22110f54030b03000e13080041400003040c01601c80b00007000003155080b0a04400c0070000f4001004c41000812004036890001145480d0076909803107240901c10750030344400b04032500441c046046032003210b000c00078001403006c2440ca0014042d011081c0303800e070740041c40510008450000886080c030000307000140900c541c142c2805501244452400a9405c240a17076841990302400180740c1b41c00740300203800304a44070384074560f0741042580030400e0340c0e42c407610752a108445d04c0060105451b299a4000442c818101c1403084a106030b4150741c80621014085010420740e81c80100c0d03209a26465442d000c03030710900c0307100a10003103100700c004040c80352401c0c80700402c1c1ca5808014407000034003a840000890010514004082d14001e0700307500d048203a21030300300840b0b00c404030302d5000714103004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 261789397 1250 261788147 261788161
    0x31005090a020c010506190e0618091612020d14010605060a020d020115180e07050a0b09030c040504020904060504020a0b0309011505030d02120c03040b0f040f053114 73
    0xb004045820a0200034803440d52480180070080c0c44900f9103140102105034104545130134012000d4009100400c040c60b03103246080c4d0380008140903201b0602c03a81100030b6901281c0d480141000082a244400000340c0c480340e00069845198a0406410404c0c1c8451031284210b0a510010281a00414039030b21a0a0700c94000d50f540c1342c5081410156103010707205c0c2c0400119000c040202e40380582c600b900302c20303201d007400094800108400041d1040348404245680c85a00000c0604040e180150301c1d90180b200309490f00c200c40040070700032481c3c0428080940c58907040300ea40240c000c000424542c880d840840d00d54000350740980d20186e0040141302d01140190000c1c080c01414820b1684840d0304c0c0d05c2090788030401084401c01503406040810342070000800640a41d5080341c0540e424143c0d20380d503d140e00e9124003400380c00c0c0b030400a01072044204490110002e0a0b00f40d683c1850407460062280da0400000c2e40914100c2e814600003820b0b50042d0090218101a40c0e41c054050034036039 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 261790647 1250 261789397 261789401
    0x120c070f0b0403060605041b03020705070906060c0303061706040f08120f010503060f09030a0c0f0c080a05060c13060e04021606050a060e04020907080402120d0e0108060d0201090b031005090a 84
    0xb0104503401824924002058030b00f03070040240e230344282204400c104402000a40c002c0d4081c0808440ca07004d42c0500144072091032090341e0013442540c889120000350391500500315030f080d0b008002c01c0b160003460781030703e0600001c005500a501244080d000803035410104010700446c0f0b07d00da03c0d008100700300512a0fa8458109040b10390607000c03241d940e06d41d0408045403c0003141d503807040c3e0740184499201d05201e06200d41708a4015154030354038034459100ea0b10b0084940c2c010129662000c20981d0400104000ca580d0109800c600c1c1030404e44507000c1036200360228801d00b820030041c1642d003801c035521035046803c800c00300007a0495800403481c0c45400740500301c500c24a10340c0340980005214102c0307a030342807095500801005c0d055840500030b0310b64000240c0103907003201c42195030035410b8500300318010172200d140c0c0714111101e0300c2e400010302c20354005001d84e0185100c031144900503608140020140c036100070182d034983c0c0c0c600748480004000c541c4401c0c1c0c48500101817102c04d030419 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 261791897 1250 261790647 261790649
    0x180102030903131508220602220e090c0904060e0f010c02010501060306030b0105100306030f2001210c030b03030715110304120311070b040b0f0612120c070f0b04 71
    0x3503c0c0b940040d5500d5070000a050300305034540700440c0e02c201c00174a0001b08480a4600780c42400300d0081400d60342d803668000c90f0020301003c42d810481070214400d144515034040014031301d03881040b00310720702200ca01e80c903001e2101c030207030041d040030300400c04004854008038008000d071030480d490104001111070280c20794002c40700144d46400000f1507064401d005107010780e40c000100301901c0c2d01e03007810b01c10444044c0304840c040665030200440041d508404515203c0e0040701c2c0c030040700810501800207085541000c0303041c0100d88450007c56480340104d0344030103032282400030302e1800b00c0f0700a4018080c46020725605010014080003000078010340c450b68410311403410480440080042e2155100a81d00a810500355080f01c01040d0b100e9080031600c0000c03078000718140f4419a0324081c1a04090317404942803d490001c00910705007201d51030341d220404035085400300c80d02d0030003591907085415400c00f20307280000343c170390b9a48410803c0740d005102010002040d159143c21000444d002 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 261793147 1250 261791897 261791917
    0xc0a1202012d1e0e010c0501020f03010f08191112150703090c080d0c0f060b040204030807020306070c030e0f030c0a0b04170705030706030b0f040501030c060e0a0e01030b180102030903 81
    0x1403c02c0f03d0014400c42e003120b403641200c54a888100d10a840015150160b91311400c80740756408015900042020801443c001e1142c82e43e202c51641c07c00d0a00c83c184038641054005040c2aa054500407584903003944040c46029a011300c03510040c0ba900c02e09241712046d0f404149400c520a10400d01d80c1a84078031400b034050840c6000c4107464807000703030b1503900f10700118001807090182e080100d400090742d80c44603881102d00060008125021509a0f0080d90080d10b00a801190a40542c10705101540d44100d480c80c0a50b0000c1e044d9402034240b8415007217003401041a0a0f5400d060f032030800c1084450040144640640d0795182080801c503072180c01100100e00d074400b542c0e41d81000000f0000152640100500241b0342050301c00c500074100e0a01d1243d00c24150048a12280c031148509400386000e010700200d41c60410001409151900c9103940c0520002081084540390011042d0f041d20f0b40a41c1902039900c2d03941b8402d00c902981018101075520000c103010036903d0010003001c564030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 261794397 1250 261793147 261793157
    0x2060601020708010b0f010302031801090807030f080631020c010207170f03240d14010501060504180e01020c060702012f18030f0708010603060506030c0a1202012d 72
    0x144400b001420b0307440350b03d172140e041340c882180c03000700d980030b0340282d40d1080b0303400401c8001c11103007010300f401d58000c440705446000c000244d00d014181d00c40e44034460404141001c4500781088030100b00e008076000801100805003c2c0450800044400d0b0b48191504080081d074494840900680c002d5100c0308085420354400b10400c1560410780c1d003620301e0305d010326030b0301400c55451880e01c81c20182c000d040d06500c3d0180084408481e03882844c40b0070041d0040441c070b6a00a482c50b80c103400c480381a04a00c06005040c00b0801501108a80030508040e4000020646000300c0da00c081c06030081d0400918140107a60401900b40d5055206540e44e08003581c2145002901070b08102d01c403010040c40078082541000013a404641d045180c3e0510140074084601000302202a103050540c035130040400c82e51907039002c205206407400303010703000360084018100c0700310b00c4030008a410f5110320980c01a07a920750042425680280320800c4c404504590000e01060640303080c0240d0034a1069190200b0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 261795647 1250 261794397 261794399
    0x181f080a0c020f0d0809150a0e0606090115030e071205030c0c0103110403110a030204020406050405040f020c19060612080c100b0108220501020d09031101020306010806040e1903020606010207 84
    0x40c0300003140b00b1120344402c058101042c4c030307080486064000800c1042103210b405d2140043c03150020702c0501c5144820000202c111142d18a01e0a041001c5c05051182c1d0f011401071001c80d04a2802c801a0100340c240021509805075420303040c8003090380040e11008004c0c444500b03000e17001c002000308102d85019100c0c0304035003800542c2200c19274488404641402d000900c00107050044080c0c006100030004641c0d6907480c0c0c0018280d0f40140c010400280d0046001c10403804d0a000300d030f0b50620b12600c25410911501030140d80c44406036007444223249074801c800207000050b40203001411200c400801c45460700d0034042d0865002c840004400c1c45100d1850044003910700c00c0c1c90a614050b0740306d81c2c1913203030048866241102000040d880020010b201800a1001d00c018582c0c0801c1c50808141c6511500b80a1f084241e0650800c20310b074010820071100742c3e407050340c10342e00203402c40300000c86101c1c007411030303103000c103482c580c030010700c40e111106404c0c9600051180d200301002d908850b0b0103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 261796897 1250 261795647 261795671
    0x3060807091509090c03060903111006080705010903052113030b01030309061b1205250506090303070e01050a0c0f2004060609050d030c0b070c030305150303181f080a 73
    0xa4102c044045c110004169003070000070f800c3c2d000460501c2c042d24008002e103011000300c0382000640d0400485880c0ea9038010040907000388010340050030242010b1502a207143c45031510f0b42c142020301031481d080c0c1088420414021000e5a000090342800f04001c1d5849103080c407100d2000380810b0700400c017182000501584038100030b60022620091a8840018a07a02d01c00f007846101045005e0050900c2102008400d800025002180c450008446034041d0700b000341c205803018003900e03142e400400410034803a40008039001c100d0b03002c3ca0314544d03c42c0905400c99400d4080c210041c076020201c440803090024492420512010046c0158181c03084441044125941e0344525404550201c408014520340085525842d0340607003010100c1c940580c0d02c9203d02c1c0000c46250000c182e0240840090691522030141d01154200004e6008416080044d55078001c1107200d0740d412110483c218003548400c80c945400101c3d80c2252039641800240241c18000210b40c844005071420f02c2c48109 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 261798147 1250 261796897 261796901
    0x20a17040302061605010f090c0515340213020a030c0513120204020405040507020714010302090109050904060f020d09060b03240405030906070602070605060316120303060807091509 80
    0x210303030307005001134506200b000000101e80e0880c2c00c02c4c0c0c1d03107550302c80e6030174450400da000e01482c00348281d1415406a0906c01000241f1030300c4441c3e004c24500c24071055404032883c8400c04204c5030f03d00b461501d80b040303038190301c064440406002034015030b0154000c13020303640c107801a10a01060713440c184415224280101e56500507511161440d403c194404c000240400d940e000c065800a040503141c183c494021400740c0e4000d82750080140d00c400c4040010340340008040030b1940003480c056161584500009104180c607000e401e00c01c04142012804000181d80100c080c401c0411b025034564185a60107002048007400954445082041c0e0310010701d008220010307081f0f01590340e455514a115544911002d008004403003622003004a1941ea6a468002c0c2c20704600c1840096074958061425405a601c00360803180650300a807443e0b1241c2c40411035001c01c0d50b44004a038600d48010b402d045008d0001c1c1c0c0d2111055004550380420441655080b12500c1c540c04c08941c2c407220740e11000581 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 261799397 1250 261798147 261798149
    0x2103060f0d0201080711010609090b040209131104050a090c0324050919020d061509320c1e0a02011b020705010f0e10030b040606170a0216050706020a1704 68
    0x10001d13590b100041c0090f40204c166112107410800001400e50311000d24008840440c1d00a82700c080d500d00c104421071401502040d4000980225100c055141d507540205c42034000e021580300d607454000080020805500214965811243c2c000d0126039a080c86c9105540b103d00ca9000301e17410f90b0032180c1c01800e038010b96020701003a60040058074030b20810b08084084800c0f0403640140d5103180d00020941c1d90161000703440c03c2c0030320f90b015586400307090f40032105100400014850100e04811400e8440d90030251003100c000ca030900d80ea40d80600c2600240306070305400d204415403048001d00d0803020300181c100c2d1181500200300c4110103214601d150089000351f4401139009072810b0000d944528058014407529080180b0079104003070005007020f6100d130300b00002954608041e600ca241c14090701004180300d0400328000d03d2088440030341d01030020f1401c0d144a800045011503000d0040c140c1044030303009416904c4036600ca1400a454400e604ca05441c103a28181c0f1124031040100100c070 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 261800647 1250 261799397 261799399
    0xd1401090b06071b030212070f06140a08100b070b01090506040504230102040b03070c1101081014060702060301080d020106210b0403140c0c150a0503010b03092103060f0d02 76
    0x1d00f080401d5640360100d90f400c0d140311403032000960303001005803200d4030810001c141c8400030f80706050070321403a07400503081a803100c010001c0c41c43c9520700c410120070840d41d00080500d040800e40d91590311341508400d00b40e0050310703034034030004e07070700042c05000d004403410703600c2e80c100031b00840c0c441408000030f4a4094030064000c4d20352001e9141048184040c1d48080d441030000541081d680b01ca541c3c5141c0c008442e001c001c940c901044070204045440282180c1c40c090801a800d4103100721041d00c2e03004a40038004140c4503210912125540d0803065075610b55000305400e64943e101e4004640b5080144000c001560a1800c08288800c40314007003607800410801d0f0410000c00703074460600804d4041c01c1602849180401075103007510030b800610342d600d908401001241c035146c5c00e0003450300364401c0280d0859018000c5040705680f050032a0f04560b000c9203030315103a44510a440d0b0428282e5800180006017680041015640210240d44608000c42c0c2d490110f4011809124641020002c02 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 261801897 1250 261800647 261800659
    0xa051c1509020f0607030c0b042901030c0b0c0a0215070201120b06030a02070809040e031b19022404090501090608030304030e0111120c06090610030f06020313080d1401090b 76
    0xb16502d42004c1000d03144090181c031f0039000d40d0344251039600d000070050720300350394666900005980d260b080780b0090189074124010f00c01d0075813554a40d00c02c12809030180c2e00c4c6a2a00081102d058403040012484082c1c0040440d68107040d0b4240000c5030b5030101c00304a0214000d500c03441d0180740d152042100241000e801c0e40e1842d9180c480e5617009510403001200c00c45400d100d184002d4030307244118809206050011a41d85008014400c50b440a0403480201e070f5210503180b5211a4807400301d100c040341d0540d480c907444024010004c16070100b41d03c44030200c29000c10000f880c02115004141218030340d100401a00c0d03100c1c0c00441d142d110444015001c40e048000161240d44150079007030b03400c03100d0400e0b41d64503507407c1c2030360186a0090b5100e43c82d690281040c0040304106214440e08801c49620002d503070340c510364800a0303801c64424080d19056000c00015008101450406055640982619900d8810030144001400100900340800402070008100907036544a4218410030050103 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 261803147 1250 261801897 261801919
    0x705030307030203030c0304030912060519060317070602041a07020a0f0e0f09030c070605030f060d05100e0313060315050f01140304020409020405070207170313140a051c150902 78
    0x28001c0c03075510160042741004400d002c0000c040030400d420855651242c0b5010036242400910700e0a40742c00e480781c0350420380ca0310000308000354910b52080c14000000010713644488560030240024010f07540300744042d500c81d000c1c2a101451000083c1091071089030b1b01580c280d190050644107401601540000100500125144004146903140e110b42c003007007120714118402c45241c0c20000b10381c1c041c0022490200500411000d03204c1110340c0440709a68000d052101c03a01c0b525640c2d030310041d0b01d0000319540da403034000e100018403c40e00d03029500341c10000710039658040113004010003004d403022061902804581d030f00d005071960b11801e00c16560700c104c00d00011820b4205a10103401213074400d0355443c4403001a12203009a03486941c954000e000c0c01c41c545100c5820369411060382c0342194008200c244013981e140f17103860303081c4e480e440040c032400110b441c04103901c50030642004d540705004680110810a0310900c0201c1d10303115461081c08a4001000b04054a00c4510020751001c0d01d520 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 261804397 1250 261803147 261803161
    0x1406010c020f0a06020c151303032a0c2c0105010f1106040c1502060c0a0c110306010e0106020d0504150c02010c061103010f140d02150c070e0108070503030703020303 73
    0x24403900d030a000908241000081400194110f14540e0203030000d0381040d490107500d0300d040140038102c540c20301800752a1510f130403030540001d03c80f404000c091080f01c00424100300da01142d161290740c031030203255958000909103d02c41079032134420118040c9020313001c0c0800380c03480e51142030403200091f00c2c6a00d5908140c015111540114294410480742d00441d00c0b80b4078003000000e010340e020b941c3c0d600c01c00303007802c62101d410642c4d403804a0030340d0310050901c841e2440c601c040780c40200c0c1501d0a03819203e414508018091445401e482c0d05114800020601000d610030050484905070200c4d1804103407010305403110300540c480c210811145100c03604c101030007041aa8038262051500c1582031003a580c442e412200d06068041014901200512400030141c050002030891a4821041a003409001071210440400c00a00501c0090007007005400100c056820b041c02040c140c4095503101c104c11100e0440911400300e103442000d10001d00c0d0300740801154407003a0164051072556945407 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 261805647 1250 261804397 261804407
    0x40e1605060d29100206010602031c060801092f220b030307050312060d150e1e0c0907081003060b0d080c03070c061b0b060f0405070903120201140601 66
    0x10202c1099281e000802c480d107081040320401038580e9005461070081da8043c04001072031807445506552142c001406815000016114042180890b10301c2120301c2081074400f4110b1b03644100b21660a00c20070208001b5042040f03114029031151640410821040383c8807030410118486420645440032402801100e0300c200134545440603001c82c4008003d00820700e0341d0300a02c03007503a030f5820104260355003010718003407541c214004840c0303601403000985034030141e8214a40504800ba0b03554a201d02090070501c401c40e4040640300016152000300c2400603140d80d10101c485109489000014055602801c0d403240103064484054040505503603609006148000704507074082e005219403000240c2c0b48008000d50600c4801441e02c2e4081843d1031044807416410010a0080902c4009c40c801042220800f01c2508005070707a56584420010442002c01d112400fa001410b140402c00007a41202c0c0c1f88085074400c00c0c0d46285002e90f8042203003260210342c0f101010007601070100300e07a98410 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 261806897 1250 261805647 261805657
    0xc0204091e0b070305010f0e071b1203090209060a060503060d061401060302041403010b0f010f17041202070806040804030308091501030b010f090204050306060105031f14040e160506 80
    0x350400e448022031040d2204a84140c8100460b0b01100000801c1405039044c01914010320002203440074403424007600101c100c00c0204510b0030402d0440701c90b813007441080031180c034107a00042140c008682c00ca400030094510004140c0c0246050808103103a400c00e075150303d0441300956111070a5841e443c0810250b00100d800c1902d04644440b40d1001c10b440c007000313950091000d40c42c01030f5154580110302da40b10305078281c058070a0b494451114160380f9254050314607608240381170180701008020a0782d50104c56a01d12a00108840c100810001c5000d1541100d0b02141c0844041c0d540d680e02c001d44e01c0008480c000c3c05141c4c14441000040c2c0100e41d01500028690240e401400c0100707109a540301007680240e4007201d0fa500100015a48142c402002c0d041c0c10500f9407078681818042940c1d0200030f085507040140000009249c110410031004d000c0f41740c01c1e483d41c0307480d644105801510900940c42c9110741d00d0b00142030030803200060708a105545d00b20071229002d00d8074080014075008 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 261808147 1250 261806897 261806903
    0xd0c0803180a0b0a08061f0c15090b0703050a02040e01180516120b040b030d080402040e0d0518012307120302090d0321021303050f0703051903020307080c2505010c020409 75
    0x7e03801015407003000700c0c03811001040c80c1e68580c10001450300b407818041030703280b100144c49840e00d605170002c1006000200c8e8040068100071500d81c5492450000074426540411900c0080324000b0030017100d01c0d03d112004002044007844540c4425110060305d0217580d42d0200420b0003c031541d072510145820226210704014000140c00003a000801c1c244055035400314001520780d0100702c1103240c54030071501c111034501c00030001c030501660003a140c1e04c40c0352409422005404003600c0d450307200e92040c002081102e2011602158040001180c1e40c0203141d00325600301403612450b610a200303100380c0721401c5001741000105582c5403001d0314108090f00d100d0b51048010308462419500340c0c002410036070007a007107150303605140d410f00c2400c04a422040b002c0c41e4101d10404c00116400040800d03c0829902d1403403480c04c0b072880c1c05e0f4514441d100c00280410300220381c0241d003480104100194080700c4400d030520000881e412100000c19002d443d0200b107a100085003d41090303800b050442e44 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 261809397 1250 261808147 261808159
    0x130602065e060e01060b0301150809190302060708010501020d090308130b03010b25050601150e091005040b04060b031303031d01051b040f030f020d0c0803180a0b0a0806 74
    0x41c001159030340e00200ca50090310402c1d03c0b007401c240d410009100b54802401d82025540c00c650600015a00905024510000300902000414a039603414800d0b4022503020343d905400c140d020303142c0a52584001c68441c804140b80307400006245d4008640318031401c1c46560381450450841e03541d0070705504101d42c40440000605000301c1d2041d440300045018203c4030400d551244504c1406c1004034025040307541212403e06c3c82da0002070000200305055803901c04031810071404612085a011803089069580a403043c002e0141c103000382207106094030030554080c0305001c034250903c01610440c3c0700e8a000c1000800004140000c2e4001412483c0d100f0b00e07001c505100c954141c0c01102400494005007a55a14103001c200b0b60040c040b582d4071b07151b210b10981403900c0d00b43d12500c806030602c40606024295001d043c21941c5400441c0f40b0f8640c4808803003403050702d48071407a540b0781007491070f86814440a80091118a03040c07540208841c80034240900d8446240821a80c030074000d400d03560400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 261810647 1250 261809397 261809551
    0x100e03090301060305010b0f0414160516080414030a050d080c040f030606092304150f05041101020706020f0705040e032107090510051e13060206 64
    0x7580a01030f00000718050000810b12600c800104000a4200d84203113104500d01240c00710b9110300305500a510207402001e1840e401c0342c0c044191030b94490010310305100d0451080007410000003130040c0050340c00e511950010b0b403020106266031404017402c003130a551301074051039103028851414036500c102c0840d400fa043c20741d100c0f24080709600641040740d20b00d031210070501c90540c591051f150350029400d2510120620801034035000c200181c400385c11001100250302401c10503401a0b4102e8443e01c10402451606080c04c00d007001302c543c2e044c1c1c0103010300c80d0000b9056100107a0724202c0741281016080041c5070008000084c444922005102e00040c00a29100c1400000c90711441f44030441c5c2c11981e20f0510002844d02440c1c0d00310610400244040400321f55101060b5003110182071680a003501044510009a00994040070356000040d0340c040342071a40440d40034000c04e4170052941c0c3d20b0340c0548140c84000c44880042c503d9041c0d00743e003e0a044020440b40b120342d4440303007241480b0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 261811897 1250 261810647 261810649
    0x60e01061502030408010506090412030b0d020d05010b0a090203060f011805031f06061b0b0402040603052406030303040b0f0a0f060603051510121e1a0102160602100e0309 75
    0x4225542200400350b0404a000c000800317003800707250362098044a070b008692601d5501d40c0c207420340091890040541e1040030403083c2c5c0300c2c0100020101d40003042074490b040189485400382444048450080c1c044d07410024003086107000f41d0340512002440f609038440440011280a0842c1a010513504040140054692401e00101940351401622122079001c91100c180c15200264851001c010b036081c5000d032140800e000d21142180c1c8440c4a2245881d207000281c0a00503940020f440c501904480d8100d070450f10304068140c2442d1210b000440d039988017050b0305c0380821100a00381403040300c0024002e45030b10307401b82e5001c6048400000c601c40341c25248021111141c005038003103603503901841707072003001aa20b400700e186003107403440c030100303603d4000504900d070111081250903211003581f07410103014a07620542c05075500003005a405400442c0d400b443d00c080e0346a0140c001c49000070988440c1c02a00c9007680c17004d4005214160010300c984000740310b0b40142409a0009002080e01 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 261813147 1250 261811897 261811919
    0x20f070302060f010b09010c081614031306050c070e0613050a1d1b040f140a1508030307080f070306090c0c020a081b060d0b0303120f22060e0106 64
    0x50038040d40c0140031a103884040f00c070501c80181c1242d12160428403201c419aa408050242140e174054030840e201d04042ca811b8404c08061100240040d10064905c20211000400341c0b682030a1001240d010301c2c1d0f0359000b81e41c580701d6103130060074942052100303002d1214101e04c1da03504120003804501781080414a000201c50055440342c034203d4940309400030280303280d0090446040080050722810141070103a410036986035180d240120b40b20500e91150052540c000340e4a403201080b4090b00e8940060120018002402400c48000800002040804000054900c6103005031503044890f02c07225600ea0a11500400060030540c84032404039411000340180f19201d0a10b40f55690380d508648108a884001e035040001c05a104403443c0c06280040042210003074010396000d541d400d8110b00220217403807090b034880d816200004d03440c0b040540718000765104400014071081143c45400c04940c0f419040c90344200920111700c1c244000c94005c0c1d00c50002d10000e10000690703603656810505c1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 261814397 1250 261813147 261813157
    0x11090303090607110a090c020c120d030c1103040306020c2407080406020f071208060402180613080601151704080306060c010603060c020d020c03010c02071e0b030c0702010e0d0b01050f0301020f 85
    0x903299242c006580391f40340c040141c5044018122000b10101c2c0c6c061014540c1c980c810203d0b00201740c0c40d12074200b00c03103004401e00800030b0360900a0365030310360722810300f81d001c0c3d40f0801325000355128000c2100100e20502c1007450b80c00c489055691060380320003100700d803020400b50040d50480c2d401c10280d1600e108690080c06005c8c82031021404094070400c0260200714020942d078010360040022450103138020484081c50001202c240361542da00c0d46003014611403a8200c29294401c01001103581007450501d6400403406035105040388407500b00c03100b0003120940d03000b4030400d007e0011500c01c1c83c00c034000d455944940c500004006a40ea03d038401030301c81101c0914090b8015603801c4100a41c14000031084002c00c0d002407005a4038080d0095440c00c60b03100c3c00c103454540312005c142e080c0d540001d0340000e1001d221410b0316420710302101d8505078130000040340810190802c0d14414180715003400a00c0c1e40010030032501c0e86c60882402000d040c01044143c3c035550804c034181145208001a103 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 261815647 1250 261814397 261814409
    0xa111609050105040f0501080304091d030a020f07061d04050a140c03071b050a0803070504120c050405070e1e030a1b03020f010c050a08090109080d080a11090303090607110a 76
    0x100d16545494113020440340303050a0f0780061403d1900500c00d240000080740c0c1118903203103000500c41c0481400f00c2c60203029a8008034039000c000f500000003a40003d441c0b0700c01450000b5150344564400c81900c1c07103030316a00500d2040d180007401040303500d450b5010f55803100c2031440120b07640300e105440315100b6208813000039034000080b0a0000423580080c0a445214504541c2030700030b541a06c9244e0707603a410140042c00d0041c0040002d01680c418400c3e0b03030060445008985000500d071501400100d8036016480c0102d1410300018481d81c491007140c1c28900703000c0c2c15260381c03941602540820040303180c1220b41510860007010002414808440c13451540400507401e21800c52040020454640343d0290400c400e620145000c9400030500c0d081c420351010315145d844409000688a4851640c0000440d000b00c08203201c180341c101c5100c41c49500b04035010420b04581a0501042c0d02403450051340541c0103120054080c20090001c0c05d0440c010300900d0a2240c07100b0004440d03506a81140d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 261816897 1250 261815647 261815651
    0xc1b0106080c2d0402040e070c0203100b1c02210106080f0102040608010608041b0603020309010507020105090c040218030a0c080f03030103022b02040c1713080a111609 74
    0x20400c8440038044070032032100898203a15105001c940c50410301a40c100c803103c1002284070380d107441e60348a174115802054040f007403025525003024082c10703052031100164045d00401c0903540c0383c41400c2c4513403104030100829891220f00384c0c021042c44000e003c2412038000c144052140708400001d03640c01e03494201d4000201e00141072003c214181007080c61000304581c0148070900c6219008407444d4155442840e1419040d60b882c202464903c08002d000008889003410200d0000d5058000b14458410b00000740402c4c0c503101812401c82e40101c418100d40d80120a02e0282ca28280e0010500d07600520103080082c003171980041d06000e60000100c40004d11000704000095050025000416850020314215891030b004900040340180f80082c1d0300d410315119100c0e81d14802c03103090f21950003600403c41c0c5071500380d0180004000714000d020a44000b03000444071a46098680070655100e1130345400c161640600765000d00e402c002c003091380d0080544070103603003003100d00030002420a0640 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 261818147 1250 261816897 261816899
    0xb0402030129031618120b04200108012106060b0a0809010c0f030e010e0d09050a0503060103120318050f0102040312020d0207050f0301020904020d050f012102090c1b0106 75
    0x8002036190a10000e90140d020900c100300d50345a60400003d8044c0003030800c98400d0b40d503513100d22041465504040c0f502c4801042000602ca8110101485544100400400140c0c81c0c08441040d402a01340d0500084c6c5520060003002200c0c1d80d9008041100c4070117880c42d1203142d5030710007a00c000303411a29110317501044010049500c440da20b600000c00c00001c00400d00001c00040c9002203121140c420b141e04c130301441b45554002d61003031034411401400e603804246042001804504644071701842903117031407000700311460040f52490481e50300c20312003038102c4040001a03000d03154060407c0c1c0a840d0060708800841e4041c0503036159110200001130b078580c00d40c5060006003e408545004560045030341000c200d800181c01e400761901181c19802c03400301a0006406841030207905500180003003500341074a046a040280103032100c503211203140c0c1e2030b2017800c081d44d54000d84451003504c61003101d50140c00c180c0309098000c03110050040c038110710105a0b00342d0003211004815a6950341e10 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 261819397 1250 261818147 261818189
    0x70b07030b01110606060703050408010203090a0303110c07031e080406022401050d0201030509030c121207051c0504031707171f06030b0406050a080a0c05090c07030507060b04020301 80
    0x42400c40028090070400f4100840c502c0e43e035681e580003000e441c003514001544106241c025001e0f40c0c0244050300081d55249003607000c6a4988481c581c048000ca0b0030114903400302c209480c181d070070401080c001803112900e151180000301f032140284611240c0e03130841d0f40010613030220041c005005142c00800700e0800d01070001e000402a03446000d01c2c0000d070b0f00107004641e0750940940b0120740901e00030540b0b4544008503411031040366801d2001c4d104124007081002881c00107400303d014101d000504640d180381060f14144650720b07407201c0c404074511980411240980c80b07180c00901078681103115907035085030791400e440150740f881d0100701d0562084201201c0e840f0802d0b405040c800050324507500495032082d90f001c1c9800b50a0605440300c21006c0300b0b4135947d10030002810300811034012569a11180b81d1200d03d07410043c3c440d401c4910020a207401c100d48998090551070400604d449507940301181d00e500724a1040b54040e443d80c60003030307040c2d40c1da0000d135010344070700d14451001d108100 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 261820647 1250 261819397 261819401
    0x60f060a05010f03150e13140d020307030f0908030304062702010f200303040309060810050d14010b13020a0e010c05190c0e0a0b1e0a061209050102070b0703 69
    0x14855841030040150501090340c0c00844081820564140842c5240f00328000c02c5800e4095042070a01c0301441080002c0d07038928a1006090901a000300c1c414400b0018029490b54810b6211f82c026920401240000a21441100780c10044511741020721907125030456007982c0c000d4405541c4940c48603840c05610f80348041c90b40010120700b22103615400986e0000c1d0031103840014030300610803071801100c1c003140c203040400c4202d64042c082d6552450940b41c05424213001e80102ca0000303011600042c034180c0c0c100030040950768000c050070500c0080f030b80e81416410508072526102d5407104001c1c0541e0311400d00582d1092070920015032501d0003d80010030684030f0b01c851a04022800300384002154021600b41c82e00101101c60032860f10031410050610300040d40404440841c20f01046034096195100010129044650604041450031181c41021807850451740c0700d6842e24040020710300485d01c0c20700c002e400c50030215030446151a0907003242c000c84802e0b00c0d9170203401e081101c219458 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 261821897 1250 261820647 261820651
    0x14120d0f1109090c090d0204050a020a08070903260904020313050c01021614121207020a0510050316030b060f03011a070b0f092b0e0a14040203060a030c0602060f 71
    0x6400c080e81000701d0b480005045039400381c5a01480140010403c2d102d4503408180c4644580250003030100b0304003003c0540c020340c450900e0000046201c1d01151059100304880d508413900804020700281401c0d070107050110070700004800c441e0041080c0c0e6425125800918410162490220b8204100f0300b40603003840c569400e002d0464001800158040750b02c1d030a440181c1c1c00180715015101c0f90075000c0343d200c01c545038607040c0f180300f00407210b01000c0b8040000c00c60180709840c140011941c903018841c00d00030200c00400810014070004428100141e480e1407091654500468504e400d45c1c0480d1b425408003060141a64000005012120041740d2083c0040b0080c8013051800f070703442e118403680d4900034207800341003a010b0380403a800610810090b01821400303045004034589160b42030204d0300c000c2a2100c041000c0d02d41c2207502d440c015046d0821180407002c8440b1030348580701000029070009013071641c0445c0c00000800460090041c0c4400f503e4150018041d9080608100c8043c0e000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 261823147 1250 261821897 261821921
    0x4050706020c0a210222181104151814090a02061e040306020d06060806031c030b180a050f010b0c0a150207052b0e0306010314120d0f 59
    0x42019004241c1d03c07401112800ca0f44003c00c01401060700d501000b40d0740d8050840030391b02180b12640142c10172011240c2824040c2406000c11800b0000c0307a2100302408041e0010300400862680c56110381041e8024079042d0820010340c5560b01c3d1100180368040f0441d43c9011017150362003000c411300d45d00c0d8100194000400500810f032500c50741c0c2c0003d03c607124101108444011124403e95000c59071825200650b40c421002e640f03540641d42610010316151003400e00051041c0e01069050501203010602050f80221581da4201c40d03440035005401c10115264004040b00241407504c400d226502d40a4010319201040c44d09210402c007135443c4041c0c005000a007810000501000c10014581d0000c84e4085840b54485d05104403a6000b400343e0040a026401400302c0348030350b1201c1d02000c82d40c651403502050816420014121a880d0160020a4140c0d01c10300c01400412803051003c4403804501003100c251045609203c4801d0300b11010101303d080e1607050021009070305005544ca4265 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 261824397 1250 261823147 261823153
    0xb0c072001020d03141803040b0708090424051002031209060f06011103190302040504021201030b070e090a050901091b050a15050306100207080f0a0204050105040203040b04290903030405070602 85
    0x5809207008850175024010a1422400518000c1191824402c0d680104408a1001d0300c1d054241030080113603100881540c41286031001c881000340700040000c00c00c0300341c2c8040c10001ca04007003e00090520b10506001588028031030020303020b002d02100d0340314842c030360302403c0a402c0c0000603080b800d502514041c140584105800302030400042502e59041d840d800b00300400e540001e05400900ca00d030441600180001010041c8100e070f04c032100d040b00d10410042a540d0b40300320080b1148032001c1280756210a0150215002064603080541c00003405000015080741c903a41d000c1c42c075849412144400e0040c29402c001b10b103041120751004040100f03158504500030780c0000d1003480020030481c444c0c48040112050b480c400c0110380040d00c05401281e28191054103550b41d200c6208104034861820080081041d04140c002d80340903d40c0020245065100e954402020f80c041e03168486101c6210b1a841c07640888440741c2a004404507006941d40f4203017410954144005500100e003554 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 261825647 1250 261824397 261824411
    0xc0e030d08060d030509010e10210c0912060f0213090f0c1e12020418060b040305060f13050709020405120601050f10120608011e06120b0c072001020d03 67
    0x41c0b688044107a01c0b81c4e05184c00d660b1030382c0d007000507148040004015900704a4600b8008022600450020550121a001c1c16030f2042c070400b407842171310307200e031178071030009502081c01c101300c071010062100728510840010900b80c0307000351114103d0f0008107219030304c1030001c00100b160351424418441e0101d0316213020b04c82d1414001d4007030003e2091080010500052004501030603104081c0ca0501c080450000c2d55901d03079030003079007213400c40d880c070b01d07078030300c606e81380c40012049465003c480840358031402409180e81e840040801001e00144008005004038410b9000113a017403001c940508400880107848900301801e10080502d00d000c40d0410341e20600042c0440e40d900d82034604004d0b41204c070010040564042122900f40c4110b113103a5039824543c010811032810b41000482c03043c1d00502c251810124011a02a52483c0c4902c208000c50310f005603010403003c4c3d210952000c2c00f41c1a2a1400c002a41d41082020000c030b890320b04801280c411a01fa5039060002c100410303590318083c0800 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 261826897 1250 261825647 261825649
    0xd0b0907090f1202041b09050a0f0e010b0a020f15010e0a020711060a02030d0504050601050108130c140402070812010f0f0503060f04020d02030f030c2407210c0e030d0806 75
    0xc82c50740074001d84000b1403040a0110340d00ea800a03240d101d01c030348100ca07040b0850030000e4012103160080750b114440600020a0340414001040d040360301841d90f40c0c0c5280d10b00920025207501030b00d550f800b14003406e055a0400078041168a070b25441c0c0301d603589045c1d898140036603052071000c0e1240500e18010031980c808121581ca1441000b1000c0310791581c0c503080a4030982c030303600c83c070707403007203200358100300421042c0100420924122602030300d0701101644caa5288180542d60080000c100440e48441030044940c40c0e000c0624032400544018580104c80e101c8034542d4119883c0c070814610303000d0051003075101024103000100119508040844c0c10000040c1e2541801807440611400b01400501556a61a5000d4540d6005400d442503650b1414089071294030580d00f24283d03104100f9a1280100c0d030000c2500068415012150691100d20044903224003054038510f01c01158600e1013181e070304621071b182000d03000742c0703a0950b032030703611420f0500f4030624840038020300036107c0c01c200503 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 261828147 1250 261826897 261826919
    0x11070b0301060507120203130e0603010e030306181504020301090c020f0c1302131a030403021605010806270a020705100c020a0201140f0301180e0a02010212130b0d0b090709 76
    0x1a80d0b902054804845c12420360403840c500841400036014441da00001a260705140f14407401490300307500a014000c2181091a038a11040c0c4801d034004864949a483e4418010505a0030054502022020303070f414800007000d80c0c0080e0040454ac580d54124031280d03a804001401d0741a103020f0240c4100c3d0305100009400351107400c40086229000246025028036032401c44000d40303140c4241d402c1400490841403640c4c0c208031401c40261040c0000c8291490300d114645049030416964018103585003424485900441600344032500e0100203661031601203c0d191500c545e500c07540c0140c9802440c149603281407030410f03d0910b035624050035044c3c09035002c2080c0c99107030f8080c2404840d60800540b480381910518029118008001c4004501e0040c03644441d211950026020700c001c450798849591113054000000780941d200e105813030054a40309000c1c20182c00030f5003044204540d5200a000d207a407000000048150703a91212002c2c03494140001c0b60007000510f0017a8046060401c43c1031 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 261829397 1250 261828147 261828157
    0x1401090b04180204170106060210020310140d05071e1d06040e030c190215030622020405030106140102161514090d0b180d0c021c021011070b03010605 66
    0xb0858040842828040c150120b500404160200385000e00c0540402e5000344040e01556006008100c0040190446170090320300901c0b655291b1544149400c0c0300003c80110201d0483d08611228044e5010520500c001c01c000d100c0000f070440c80001c0c11000344040482c682000e030b403c40428a0360801d180703202c1c3c085a402103003070b240007458854207601d540c41d6005072019078500d0310945400d000c445146034600854103200780e4a080b4210360f90518001d51380011510039030403c01c000a000c49098450055038003101280c0c400514142e04c031408242501d0305500719800581072005244001e59040044c0300080c503001403e00f0406081044091000c1c00c40f0408a0802c082c4d210000807480c2440126030341e080d0001e202d600e4902c00c601d00104240001c981240540c03c061045034100000400c400d03c180381e40d560348512031183c3d0742c20425101d140b050064102c101510721440117841e00321006c00b0701c02079038840007914841c24502c0b0785409100d03085580c0810042c001000b803d031304a41550 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 261830647 1250 261829397 261829409
    0x1401030b090a05060106021501050a061d01110709020403120203070302060f04030314010e19180b0c040302060403051c0c020f010c11130e011103060d140c090403091401090b04 77
    0x281545410180d54030b071610308035014000b0701a14000180454001440f6203030500d070001009038980e0398504021b032901142c440c81010846010001c2c048004408407214403000504082251100d0540460301d44515504842c14540d4000741c10f005000404040d8040151140700941c0382c1141940e0094807510050701c000f5034554000301040401d030194014081c20800b0780c042415540e5501080703040d000c1d00752182512072a0181109100304090f00841d50050086140001544210f07550040320302401480001410000d000100042e954040140000c5006030002c00da8502180c038100d14214174802c5180501c42c2d82e03040040180c1712807100c251364810074240101640d0103400c120151003072001c1c25641c400300380b034078034181c03410300d0f0740020340e094440c40081200c00f08400036601e4521042d115217a00a20700381c03e10002400d9604164081071181c000c0c0d6455071400b6011500d400c0081d14218003090701c90209210042150b10010000079091030721842e52f40c0f9112088032680b05d180030349 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 261831897 1250 261830647 261830663
    0xa05060703030f020d05180a0309060c0201050903010603050c011103030717090a1a0115031509180501060f210f080904060b0705031e07210c02040f05100801140103 72
    0xc0001d25010b5884061180b01c00e110942d9105005084e52000b44004c4540c3c4c5915906400c1c01c4041c04000600c1e490b03601c2d0306407104c0410034240142070b10310300341c546004c0381000030800c00a0b000d502c2c00c0c0210f000440c460002050460f103000c0001d8120451383d48440d2107580700744204010640e0280a404d071980310109424141d8030b845924034100203200d10003518843d51030310200351840049000034104c882c0f0300842814090182000c400752a044d041e01141d80081c4541070103405600e510814142c50000036504446140d503030352500703503500b9510002c04209072500400c0280480c00a06251180c15200c080212481d959401300303c42c141d84000c5c00003003001c501c1035403d403600d620101c054420000d9507525400545001582ea912010803407140040030300074880406088019118040e40c04400c2403a00440100441c1498400745410010840c0b020403074800b6890700c2c441c40c2e00d403280c2280003095510701011680f009a41d076500200b0756a140220f152840304101d250181580d90100b14 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 261833147 1250 261831897 261831907
    0x190f0b0a0804020d03110d0806090a020408060c0a230c1011121b0c06160e01020a0807030203250b010f06050f030901020f0f0409050906070f1b05030c0d030b06090a0506 74
    0x222080c200c444003d01047c45280206a44240c201440c079201d5401220f80309401e81d03e17060340000340e01481c480e651680d80200081581a0040009401e01800ca494016500044403c00381e21007000c10b0254a6025400915114644000d0010100c0403299110500418400340390b803107428481c010140901801c220046441040f04084002c0700001010841d51038049145c42e03661556000c0d690210420784a441558681c0c2c01041103c4004005801600d40782c5540d444541041d4020744003141140003c101e410183c002c40c1091865103a04202d14400240e91841c0c01c03d240581a0030190412120b21020001958001d00f10f41080340b04405640d00c9803644050640640980c124001f001ca0020980b0b40d50054180080d0048076070508050009803192450310b502c0399400d4403e44009001d00490b0490180101820b406115403043c0d9010075043d5602e50320704507000000307450101d4001e10040d01601354580a10281d00c0390440d100740c64002c4600c0010001031903841618011100460 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 261834397 1250 261833147 261833153
    0x19031106060a1809050c100504061d030a0206480105061507030306030602070b04050723060c15040821060d060903050d02070b04170a08060f0f190f0b0a0804020d 71
    0x50003816016150801f1581802c5018103036401c980034200000b100000035030740c4e0707101480300d16203841005000360081c00c01e503800f801280c0d8409038515010003134002e50226650244a060b0300e012402412340c5510b0f04a40109080e22041203080b100c56071304100c24800307a6901c98400e02c06121011005580d542d51500e4140c0223880c003a800605030910100e15181444881301c401440b991042e81626555a203a021b50307110107030080c0a40d40d000000352510402820020010241520f01d5003c031200c0f01546802483c07003070002c560407038807210041070b50921501310002800740d117011182243e045162800100e1440100030201505903615502c4202c10b150240044070a2000011020b558441c82d6013400c0842a1081d01c00712001f0442c16040040300c1c980c001500c0c000c521070f560340b94035030721960b0412148006580e00c09600102881c1d1084a42d600c01102d0a00404040c0709810880c0c9880c0303808401c0003040d44184a8904204481e030003071940300701d495520a44c101d070400a0a100340c1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 261835647 1250 261834397 261834403
    0x312010e19020309070306060b0f0301060c0c2409051c1205121006021603081606020405042405060c0a0b0a021306030519180f020319031106060a180905 67
    0x500c0c080a2480082400015240071a50401381c81c0221401d0140560350310342c0540502c241025403030342b0b180600040c0509841034441030040c50050308030840054560100144003441c541c47d00001d1100145a2040183c00c134000c1e01c003c040031500303692000c0c1104d190b10201d50107041e009140840c81d401201d410b82c012000d581031010300203128034131898102501e0f0f2021549004880151051b041007203425940011a071b426250700c00c0c4d040741403858010380501d20004803403003111840d13000d120100749900c1d144500903022080103000841c0e10301c1c0e11b103400306409840c0c214601520b003c0000f4000004006580010147c1c05410300b035403a40c0e00101c5800038010080034442c90071652100092541c0d06800c640d00495000c50084044031f407031011503048469201040600301d4402d80a01c0100b0003000e10b0b203000d075001a00752107107018011917411406c410364004401258900100462440003000b50350fa00c2901504d030508802e0501780c0840031070249810320403d698880b030503041080018 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 261836897 1250 261835647 261835681
    0xf02040305070e01080f060c0d0903020703170918011208030703060b070819091a0a02241602010207020a14030f0106091e021602060a1704030201020a030506030312010e 74
    0x200c0700741d6140684400c0700c0640c0d08030a1081041c540b250b5800c4140f424000b094150150340b40400322442c000350500841c020f03000c1b2400c240d041d07008032000040802c00c0b9008080e0403107407000b5601e644484050401490070700c8100b0f44040549480e005003d4444080b4003085d13043d400820950711ba69075458114041d01180e045a00c146401041c018204001c400c081c0010400c004a020a1251120303411164010148603040b0300c0c80c80380c00c04d102600c089400405c4100c03101d02c10794141c020014000e2204840001c10400740c0e80c01d06c801c2021980700e81c141801100c110b44025490240607030001080c8515034040e018031800c03440102c880343d40c1d0811502540c0803084000f03002e080d03924400c001c0100003201080c0591201200102c0c010f2045108a9940d6035202140c1ca048240303a40912205400140f014010311141007021101c1ca511400b80c00c0c0301c0c46c4240d0000d603907081c01040084c1a0760003e03110383c1c0243e01c2404900d401008031300e090342c1910a010040980d40d5100d4035030132036075541 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 261838147 1250 261836897 261836903
    0x3192606090705070219060503160c050606040c1215060206011505180f1c0605090a0b0406021605070b0306012606120c040c0903110603010b0319090209010806040605150d03030f020403 81
    0x20403000928a0b8000019520071024ac020f11080c15282c01d00544000901d80c50041840d00580c2c0001c48a152039446164200d00520b030411401c10545100c1c811140c144c1301c2c108c05040e030100104002c607810030100740500b03c41d400c641d81c101050070014003a030145140d030b00318104002410589984a001403e10500401801c00e00c02000a0001004415451001f034400b241080b0010b00c603d500000c01e00904c80e4846124031403070f9500d865200003034220704101340c61a0340c191150743c0464010480d8a001d080c0060000760703242003100015190141c1c140b104c2000b6100701184690549248440943c440c50070f0324407890301c0a1041c0e826080840300a000d13a803040c9032100f04a02c4603405085402900d2080d000d545911440104101ca00d010901c100d220440e01000003504a0859130507202d07449020050204540b1000d5001801d0f0000c00d80028040d540100c2c01c020070300886020b076a0300f100989240350105e0381a00e002c141000b170411006001c2c0f586404484c420040203504440003950 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 261839397 1250 261838147 261838189
    0xc0a1101032910050301080a06020c0a050303070921020109050d0f14031e120105010f17010612051303121107020a0b03180f0703030e03031926060907050702 69
    0x7441c9034615011481c015200380078480d0a18009075140c050001c50b4147e0340c1180040c44d01c1174031640c4600281d4880051011a8061400c1e514000f80080001d14000c543c00d40390f00c0360301410544010300e20680e10607540c3c030b03980c0c4d146085000350740c0069180c800da55065404104590315030802c606c2034100060010b00000f21060200103110000c4050082c0c001642d003d4a0504101c940510180c0500b800d904c00d00b004a40c0104990340c0a2803135180d900c01c0342d080005044a01c12310602c11403509034050740110300c901030b0242800d01188521580008092841e0f402d10805480081c180740f000240381c00b41c41c0d5140c540001103c55001510300303070b6a000f800043c04607150f80c00400030341c200741e0b803150100e01510580e094480303002c60900c465400e4030000340003442c0345803012100074500401740d80e0140020025000c0322182551100d002c00c103143c0300d070030449038812081011101c1441103811820107150921400d6602c10071200d0f0040c040c0d103030031030720740500307000162880142e61070060083d4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 261840647 1250 261839397 261839441
    0xb0403080a020919090b09061c02011e0507060606050c2a0613140d0f030e01031409010e0606040e192a0e060f0906040f0b0409031107060201020c0a110103 68
    0x208130714041503030305031803090001d8501101406140ca0042e03074441d51080044a420404003040d04000b00ca4500516144482030b041491024515103881c55010004034005078410a008140c056080180030902d40a0710b090700c5064860b0300e07500100348410109440d81c0c04032804201a6902c11140c040091005986183c0500382a608104034890006210b2a48030b101900d8076060104114440c2c00000c682c00060b0f0310f640c00c44031661041d080394149030b0b492188990501c4081000c52041e0540310000a84440c104a03a5260403001461184502d04140552006040104246800d55010b05e074800580d9298035141c0c1d4158002c15600800d00743c088111011480c0c1444504125011304014a810381c94031421f109604000030303140e503044100c11010426a00381a03100c8441c65800c0300000503130031003000008050380e901c00801d400044031901c54610094090080a0082c22a40001c6140c4890384d03000d070303131603101c800400f03000000c407940c0c00f50490f4042c0c4c020340b02c05070210840a11803 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 261841897 1250 261840647 261840679
    0x30a18120327150536061803040b032802120a020a0905120a14031b0a0b070c021306090c0201050c04050a1208130b03150f06032d07080708090106030b0403080a0209 72
    0x8011405d012004510880003c030349412484000c4401c00c80c1500e001c0d601d007505000900c101c0c0ea00c064000294801e2100c01d090400c1042c0e02d590107018070010015130b580e2404242050b000701c000d4040481184100300106102c2c2d08110030b441104c00079194110310801d1031003a00d05058085c0c3d4080c2806440006103c03560102100510700c440b0703646040d041c81104c03540c59956035200303a480100100e40c03400104441502600f0b045034841d100034030080c4422815124801592460752200104a458410a151042c1c0a0190540c0100030041503030400b0700c4c003800540c140304d252190300400d61800001d401802104003c03a5666154103240d4000550303680b119486641c4200c07102c1e40745050404420b02149403003030405030300c210000c1401e42592103081064504a001031b202160b811403002080400c404140075292003010b00b03447e10f00d042c2c80d140e54081c10400e030042c0482d1099151840600020703262609850300181c041c40c02d2005036941d82d503c14024801d208229a21203550a840b14030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 261843147 1250 261841897 261841981
    0x1020316030f02070e19110c12030901111c11070b10031110080708130c03080405090c0c07031b170c01140a0203030a181203271505 58
    0x2c6045181d00716070074956640b10b0182084419140c0d050f068402e46420841076000d40c0005001840750600c0a00d0854151007041c5006519503140d00b542e4000720810880090a200c0c0c07004040c100c0100c24940740d801500510108411050400f42c6907075411a030b00c20810000644070340c181c0c000c0008105080c07407414084a503c3d00c0c81704440c0c40c01903000075452170500d01280740c0c1a03421511907036419102c1b100d09942440000b03080355100d200140e0200003041030001440c0040d402012881c0e684c038181814080e805100802c1404001402c20001911110014908086980158035140681e0880300141c001c007529a00209a607003c0d991002c2e05920045001888124240c8911420000c142004030003401041d0042015800c180002413100103250040440304200c000241001c108a0344d419004040488a0400196984142c14000e01d110100f401315022000c2000e0072440c041e548058554000b0810080d905449801156014000c0c842030400c0403451019a00d2a0703500808200fa = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 261844397 1250 261843147 261843167
    0x106030b01081b011b0f0206090a030803010905060a0807180204030b010617240d080c030f0a0e0a1a1612020c030c040606020a030c050708100606030b01031104140102031603 76
    0x9200d0351041d000f01c4290300034000c3e08002d164201178004480d109440783c00c3e08000e501c5059810601c00c0150548a9862006050103148a407182d1516541003804100889500030a10b03801091014401d10038080300003040822110205030009d01e00d606072078081c020340101c1c2d00040c1601c4602d80007040c80c80d00300e00034444161044182105a54440900d00c00004103a41f8120400c1c00c0c4008200342410a0088500443e004e01c4040b45001c4020800034590750141c020140c041a007c10521115984600d0100240e4011a02a5000e07824150484035002c00e08803419040340f800108141c61002d840303954004039030070051110000c80804006034030703a02c401e040a40f00340201402c4000b01c0c81c0510a08068030529070051191015035602070314210f0000c48241d4151150010004601c2010448544501491100403c1e0b0510700000682650340c2c100344141414206084c041d080c01e08041510120f62407400c44d28191419030740180d0452041a00322846031032400001000d14be00406000c1c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 261845647 1250 261844397 261844423
    0x40f0209040b042a0c050d020609061b0406030207051011040515030906060f0d120e090f0f0c130b03012408010b070b0604060e070f02070609060e120106030b0108 71
    0x3100010b841d40812044584299020350761440180711080d0f103082841c0b2441c14840b10703040000410150307888280c54500504000001a4429000c02107414405d00825400c06a160b41801404010b03503400d02c203074015405041e041690226036032043c480c6c104904100801c4840c020040c3c0c000340808142d03139a102c0d0141c0780c00382052140780c01001c1012802c40348180181c4000c0c01c2e81b80c480e503041100080340400b5041c1e01440494041c40401c0f88520a50224506a00e541c00b10103403c0080c05002c2c00020100c00006411100304041d4020200300c540c1c2c0141e40752030107a5540c000348407100760740407241c0200b85450400310001c620600038400250700a5460f030182642c511031502d048406000900507807409010a01807840001d141c1120150094001440031840c2d9803220074000d10244c040360000700254401c443c01c1101a014081d000241440b4640130700c00c1030402a010b410b440765225114040c081051b03140080c0c200c02e40c400c002444c5d00c1480100035507510140b01d40e90390301804840d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 261846897 1250 261845647 261845651
    0xa020c03010509151302010c1b06080610022e0e031806030403090303120b0904030201151406390f06070302040e06100908120c1c14030a0b040f020904 66
    0x410007600002401e9200440540c4d034001d6240e83d0f01980c04c0321000d103944101e061043c0c0c03210860005002000e9070340314503908810b14810500d0050010034242015005034002e035219030300c03010100d601140c12842000244948010100c91141070304202942d200c000b00301c0c500d0520b240802d6140840104506000b07001e8a50b13803103003020100a000e01c41500c0080108070b03c071408000080c0100b0300c005c068100202e00051600189004c5074140500301c8017100181d55030024800c400350184100c402030b02140340c2e90b035100810b40012840c14416400b003150403410883c80c40481100782e20107240300e5104520041142132140b00b13820b03038400c121607e2040324011a4002007a140c0301c6d1090310101c0c0c01c0113480c004c0c41e46036103090160540c01c810b0841c1c00c2145450011031424001c028030a1040f11311421103503100000419241454000c603403c48840211070a004030503940070540000105240703e609a882d00c5030b4004500520f00250a2030b00f0500f840d86c4c3c00d214294550203080400f9041e901 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 261848147 1250 261846897 261846901
    0x1203090c0b03070f1107030605040f030314010602060703150f3503040909020609150c0c09010b0304110d210e010309210302130b0405010306080f0a0f02010c080a020c030105 76
    0x2184120380000c4610303c00084000e0240c140301441004e6070440300c00c031171081c0d42c0c0f90340e16601d40e00706541e0122030548801450042c02c0b41050f0f072611030440319600303484010404d54141140251a090050710440405845016400401103035840d40701c0140384540f1002c07101070b5280d400141950394403134441004244242c001001c1a000c11644c00d07142c00e80030286242500307004c0f0040081c018400242d0300820184034140e000e03103400380c8540c4c0d9000761840e0191103091000260786815241c1a480313014000007001085485d40c13110a903034005520107030614040414a01040d1418644030b0041c14140f4030500c9842c161210311140300402d440d9946e9400307200198001034040c1ea0703030b0316030080580e48480015440e0700b82032042d1500b40040c9260240c90140305494845444400d81c2120844540c0068200025a01489220004c141050240c41d2402103440c4040e11030600c144058407003180c451044003160721818128500580c0324002d10340b15040684001d54441002100a000750700c0c0c440 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 261849397 1250 261848147 261848159
    0x12060608060610090303081b1804060609081b1203030a090c05010e030c01300b09011e140301020d050a0c17131113020f070302070b070f0b040f1203090c 67
    0x10100340d15071581300e84200c1469690201d520300c0c00140502150a5084508981101c45400920b9800d44400006802801c1002080200d55040e0700003420b024880f201040181d0000c0313285880106c82c10101e650610916000c120041d45000114580303000007c01c000000f202580b1058059000d4030060b1421900e40c0700544007000c02a0069600d60311011342d044c0c1c40d621440f10210224440c400c403080c1c0d20320988101c0000e0815910185074282c07180707840d03402420004040c0f401001c41b0490700c01180500600d0302c6110425002c1c05003031140031107004681c1e07102501251018103450004112618041d901d55000f8405030a1000c0059070f001560703161003800d035580c18054901200a45200b58450b626200308403000905213802080b10005140105028405400f9851054454695884c501c0c64000e0038882c445d002201c07170070b030300740890408101d880003220b010301d512110700d0b480f6403200c0c20810800c241d104401070240100491499403641d254110111046c030442d444807603d40c0b500 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 261850647 1250 261849397 261849409
    0x120e040b01120b01020a052e02031302120f03030c12090a050c0f040b030303010602061006051303080702010c170a3011070c03030e010f0c11041104120606080606 71
    0x46030080c00035202d1800b002072408181e104000002d01401110f00d01d411039910b550501d00d002e052001080380f2070308100340c1d00d245460b9061903007e004008600d10f14000112600301c0c5034025001c7d010301c800c0b1001094900301004540d0310041082c1c02c030713a2245800c541105655103d030004956105501380410f20b03c603c00102400f40c07a41c410007500009084009125420165800d04c5510070349460a0701460f0300c09200560190a04d580640350078604802d1082040c021a8810010850204484454003204038040c0094030341c8004070543d100c44600040320400d00309100a450b8550844080710b90702200d0700240020800b945410340e255445645002104d5090803800f0b01680507803102001441c020f501c40d100445542040300d04148203515408200c0006400440c082015459a51129a00140d4100714400c00345403d07a2040b8095807180040445c0c0d000d940c1c040c0c3d0702e40c02541000c0c0c0d0500c003070382d002c1c0041c03c4142c0e105801078103108001c1c11b80703485a501c0f01d0044402107080c44c1025 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 261851897 1250 261850647 261850661
    0xd09060b010815090a06090f09050c01020f030301091508010510050406050301021806070201170c07020406050906300f06100501030204051c0203030f0706050702060a061d0c070501020304120e04 85
    0x30b102101c1e400700b0302004e21244250060401c40390311340c1c0d5000843d00702014414584407030001600080c84050f1450018074000c1c02c48206415907000845c1c60401d42d00000459054800070300e00444c110348240030700080b168164200329215420f2500300180c6075801142c480490701d0446040c8807260390340050600700d10800c03200300030185895070b42390501d060190091241500c10f2418241d0150901844500a042580d03110610fa40000ea500e0540c134081c090038016060807540040503041210004644022140060450442c40071961111401d40c84a103502d032404101621b9050300190102d540328001110030085040e051400810700707511078400d40f0141c8001a007842881c403c41796503d4a5503a4411080340c3c1032000b004034200c401c2665018011541c8501004a01d506004101a09000d00242041001c6140006c100110400d0407000707400c0811861040c442e43d142c002d8841d015200700000942075600000c20b100400514071a101300c203942c03c0d03461006034055181044295840 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 261853147 1250 261851897 261851911
    0x115020703020f18131703070c030305040c0e0928050a14071805070e040b06180a050405010602060f0c0f0405011407060501060509100507170319020d09060b0108 71
    0x51202400103041183c034220690b10020000f0082e1100d15030b840c420380d001100c241d00004030302800c0d001005880324031180030940c480c4c050303411440d207031000400800381b820b40a0105500e8030041000c1c000c210b440c01c0c015060b01e500501c1e0518000704001c5d40c9004810b00210b0407803c7d100d03004200c14914417180c4010740c0c00405407010709020f4803448644a00e0301c444200314000c4080009030440300c00b0b00704450410304440814540f428030030260421550b10203281c012411701e21045800d0340c496085444050414405803a244880c5002c640f81404036017025800500d00800484c04540025140307100ba0901340d111842c40d900c2c000c06036214098150050b4680d00705120610142d80100650552400443c0010f4104030840e01e45000b620001c1e400390300450400a04e0180ba0b04002c454480b03414214141039241c000c040d601d11582203540c2d820190582d0020000c19000c92508410011121240005540b40c044901c402002071074000c1c4129412450109420003a5014029203032041d04 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 261854397 1250 261853147 261853153
    0x20310111c240b0d020c0f240a02090108160c05030706090209010b0f03011401050c010f0b03010506040603080f0a020f06070e03160608070e01110f01091b0506030109020d090c0b070605011502 84
    0xa00030084070180d044041100c4c80ca008a07e4600c00c0c02c1d808010180940710141c6c1c600750769aa14904400101c04080c054038401801004440040e036001200391b508845018131942184100000488081c02200b400a005000000d201800e024481e000441601e008503040345181e42d80e0545055244030740c0e8490806041c0600040203440c82d0302c040180740340010f0600514007a02030300750a08407100003500d41d000c01d40d6041d01c845c40d400e00f40700d5a507201d00203407402c000c281d0564031003031058001c00b038000c80c400c41e001811140740c81c03080c014840c400301c0200c211950343c05c088802500c0b100d024142c2c24024851008071500c00700c3c1c21300700d000490b090b03922090029150f205048552010000541d818400040d44054a40400b0060721803109845030000511012914003500b4200c86440760f8152100c042c00c0c240242c2e40e03034104480c11681d02107001662078401e20100400b410b0400000b5091809202e030000d480860a0000c011240c8a84010405aa01e850120700f04400006614005034 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 261855647 1250 261854397 261854407
    0x1060903050a080a020c06030c03071e020705091003020d0f060c05030403050a0c0f050d110f1209190b1201050916090b070201030603150213060309020310111c240b 72
    0x3c410f000206194002c1d4070581d0040c00e4030002282e040da0080d81c41f110f8000c0004100404036500440100307c111703002c1c0301c0782105140340500a40e80c0304280180c41c42030845002041542d80c80141d6600203550281c105240f0550750b00704410724800a040640b100b605064081048512030340441c1d1003a03901d03446240c28001e92020403200c04c2c41c1000e04031482841100b1000205408000c0701c0280707000ca80c1c5041b00600108a043c0c02c0c00241c1803420080e5102d8250130007040401402c0c4c4004480688803102490751190701031144030000e5005c180c0c001c43c0041c01004c41030f180b9803010f0586a0030b40c3d090102d9207c1d070864081c4920b403001c0703003000100c00c2c010034080460418001c1850500514000c00ea41d42c80e51900c001c4000380d41103c228060b03000070f0900840c221000c007a00100200e040802c2015020340102c1d48481e0030071016504241d4a100d0102551040c00540c0c1d052054020a000102117051000700203103000a04d0701c020186d40380d40700d884810540e05030000d440a19509074200 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 261856897 1250 261855647 261855653
    0x50111010b0a1203030e0f010b0a06020f060f09070f0f030b061e01111608010914120306010e0402040e0406050105130b0a031b0503060f010e0a0c021c050c070b0c0601060903050a 78
    0x10f1601c00504600301a00c5100710f441c1100d0030002d440f00c4c605008000079801c0e8120080125101042d0300000640d0060320140c10548808030310940e0140e4002076500f0666140d104050070482076030803105c0900101c031004a42581c0098200045d64441c0404408648500d010016042140c4c5498103102040d43d04d00011544141d1f03100fa8802c00090403240e01000d8010060100135154000c66410b0713648010315403d005030302c6122244190300300e02820451040d094061181e21005180c0b5050184816500300c03561102c0e411100240070f040211605420540741c4031028240c20b1003202e100f42908800d01400a585200303a4800440080400ca14289555203104107605200c3c190841091070b804005002c0d1010b01c0061b00c500403e0045810540c109408905074000182c00e070340e03000380f0380041007503a1600042c403600e180c80443d450341c00b01c2c1c403100000c448610403840c4200883c082ca280001703603035a48101a2856840400503560940c1c1c942c0401c0301d540300d076444003030110360244040d0004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 261858147 1250 261856897 261856919
    0x1e0f0b060f070f0309050d0f0b010605070b010e0714071b05010f0f180e0403110d02150723040909050c06090109030209090f1e1507120e031201060306050111010b0a 72
    0x54403034141109190791b5000010006920510207441d14020b94108204102ca04542e90f4003400003802c05034103154082e03c40b0111032070140991034001d072600c00031444403030043da1140c0c0750303000d806109135641441c1d1074889007003900c101c3e0704d1841050889001c501c81d07000340400b03101400d00303070396810280ba40000110340e01440e00a00341e00121010001040c8200d000d05080c0c4100d01940f100c44c21041005944c1c2c2c038000c41c0310710b51003c5400c800c0014208114100d03a80c0d4003d1050702c0c001841c42c45c03042038003625060031020080708100010b000101c962a50300300c100c0003400f540c00d48000040300400d2040910400c3d024a0008400701e0050006280c40e0b950b0382d03040701c0da030381c11510036103400d6901919141d51410440c864080d4407024848140e0104a48100c41501e21805400d50804030707801b030075084805101ea51055112066a60302d048100140e850060045a05540c1c03540e42c4c502c00741c010184c5000ba80d0001d28128480c807408401409580000d030b03406001c61226516010200741 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 261859397 1250 261858147 261858173
    0xf22180209040e10020c0d081302101209030f090506040e0109020307090803041404061502072319032d120e0d0b0609011406070f061e0f0b060f07 64
    0xd441640c500f50903c000104001e40e000d42e0340c3d00080141d0b14042c1c0c10380c3c83d240c119081e014000700070815041101c0c0302d038030341c800c00c070304c00d605580c1d44048100000c41920300c880c94141da003907120b14011554060503030003902d04c1100011612490085c2d504d4001780242489540154070440781c100d001040070301c9072a070055038131041500e0b2604c8210303244c1003070030f047d984168404a038079403151902c01e000703141920980c80280341d440001f15a04075011006926000301e84501c440b0458059801d407180110001141e00d41304004146007286085e00300c40302002c45d41030000395034031039003609101941e42000080142400c0303014001da0a510066542c8214640400a44c404000000780340c1001a00c3d10758203082040c0c0701b201030740d40524012092000402050703201c00c5005407004d8607015031f038032114102c0750007982011000030080c0c2e0500f40320b00a00300440d1300741c1c0219040e00f001e8044600b20317400b400e4180c5503020140300030440c0401b08070290203039502c082000c0c50100107210000c2c2c05801405 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 261860647 1250 261859397 261859399
    0x9082406010e0a0801020904050109091109060a05120105010e0603070e010b070507150203090f0105030106170a09080a080a200405130e0f070e130f02090a020f0f22180209 75
    0x115a5101c10b801007003d10320681d106040581d00410290324600e440c2c040d050141c103800d00200075030006a2915030001d8040d40c81e0728045c0141001092894031050800009004081c1c0b05880f240c03c81c0c01124002c0c0000d01c1602100750072000442c4003454082401401c07103038000d070303a00700c0c503401d148c1404129030055000701e80c0c900c1484c20018039101026104000705240350040c549803040401808803030006601c1287c100041000140705154006031010138502510805070220755418040070010079002202500420380407603184070055100c241180304243c00c40043c4190001480000200d200c40c07000811a4501400140010700f0314400312501c80c1c01c0d00c40003180318401c0c181601d003401c44100c0d103984550000081031044441c0601c50a80181d41c0034007a481d1600c00340c44030034a119030350384020b00c103001800110304141210f40550300f6800c0126100ca51340d0a03c0e11010001e40d03c44d00340916100d01009102c040803051103080411111041e402d41c001d841d150170305e031000754000c2c0c7e003007 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 261861897 1250 261860647 261860657
    0x1029070209011203020c01090b030714090d05032104020a090c1205070e0312041206020c0f16050a0501020a0203100b030f03031e0f13030503280501060908240601 71
    0x8200581c1c0d86007192030080c4200c8070001003510803414000d09051002100305d0500c01c0e4104200034100550007280d40c490100e14020700b0020f902c0c41110580e110f401c8586c0d40c0544034120810900a011005040038184134491554082415a003000c4909040300c01039400260b02c0c070300b0844001c007a00302c11140b950928000d00c202000c0c00f0702001300c443c01d03525000090744901d20011941010000c4001107001050428100b524100d10352482400f0340400810494010030703107100040301003120790b60b02003841c415101c08140903040c000703510301984142403285040c1d42c00003a840d40003081d41d09006070090086d26071404401100b001030100d00c4c5c4040d0f018400c0140c01041c9035014009107000310410f14a0301c0d6843c45400380550f2803200030702124512005101485071030480d08222a14403030340350070825100d964032010728500c1c0c0c400038a01c05820051015614001009500250694a00d6151500d1640d201d041242d9900e5400c2c031143c1d60044e0102e07020070003590140d100d50b8880814541 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 261863147 1250 261861897 261861907
    0x6010f050403080310030501151a070f080a020105090115030f02010c0c08030f03060a050405010807091505060f070201030e0619093009051804031b0503160303051029 73
    0x1e84043c9500803288880c1c41262a8400d01c10810280a01034140e466440d440750203a04207281d075070791807443c0e402c2d0051400001070b03100c00b04034020307031002030140d00000c81c0780d100d410048029000e460220360816aa500e0401c7d50807003100741c20305050907203800c4200b081141d20240e00640d100540f0260070390300c8045003800001c800c102000280310134824688180d440341462020701400c1c41d599001184540d05002c01808916000039003501102d00e0040040b400010268525000740076170303005140c001c0700000b030002c041800e65004090140c401e80c0c0410402c1c0b90180b143d52107400a4804a50031880311020a01200c010380011413018011416043c070030000341c01d98000c40060000c090303106a29032500e050b1054100d400c1200416040d81d8201c40d41904d200c103110b0903031000700001e0901003a40d804200000003201c3c2800c040307070300000b181c7c0c0d69880c1003201d030808001d0320001c0300001d04101c0090100c41d0f040500030210381c0c420300300801c045846031500742d10300d1400400c0181108e09001c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 261864397 1250 261863147 261863153
    0x7050f0306011404080a0b09060f0720010c050304020925120608010606030506190602031204050a020d0b1b160611270a090c0905040c020712060203070906140306010f050403 76
    0x800041000740001c200d030186c0340c42e000d041d42000030030840035034105500b00700b001601d20380b00d9544003017a480d00d5100314101078950200701c0e520081c0040700b0b600e40307440004007940200c02035000b103000b2214080d5550741d803c1e9110400c249002c22411003001049400305140c05180315100e007401102d0040761460700c80f0f1065013141e03a180c1c00140025180d0b018450507003000c052000780b4080600d03208100780e0800c0300c069541e100e0305603080c28858801d000181400402e0004e240603e41c020148030f680c0016080c80341c9283c600f40c505541c0e806030030081e04950180d0000310740080c108040840c00140180d02d50100034201600e201f00d10250030030119074040d949014118042959040309039080c1d0b540028000c00002d80c0d0041568a45441d503c80011a08007044000b03c61044402081200480c0000c03410200290b00820001d840c40c1c030040204100c58000d90721464156990051040c2d40d054221503200001c0307030100c004181000070608951148401710a1000203082003403a141c0d0340e079 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 261865647 1250 261864397 261864437
    0x20d0e1201050c0904060806040f03050f0405031c09090c02190c12030306180603081207030b030f100506060906031605090d05010c090b090a0902031b04060c030806010807050f030601 80
    0x1a01844624000921304015140a120340000f603c0501c004080c10700d865503d803100b2414003580034003841808261441035181407c215000341a025041d1079602004188281804211f02c1c54000864248030002c240c2400394415282640d10341d070f00070042d50801c0002d00012084260f4203036454a200760011600074580c4008020780b600c80d40d0002013840c40c010304040780d114070300000d00713040d070500b107041002c1880362040d60a81180c1c040d15080c50b840d2070b40158010410003080c0c540500801d0460085d80c03401050349003244910071018890707580d558081001c07a00c00e002c0e64542c0b024040c0302003440081c805440c042c0b0003109003006c0f440d040322400000c40054110f0b100302c5246e915100c14448031765114007100020080c000001c0e0501001c2c000059000100d4014099030960100000d0009030a0704161480d0a011102c1540d46a8513080c0c018034100300b101c001d402091091000c0340c880e5220f0341c0b009104804613503404d424030400d00e01139001540081d00481c100205507141d100002d51003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 261866897 1250 261865647 261865651
    0x8071416140a1b080601060306060807120b04050c040306110a0f0f14040e1e010f060c02130e0a02011706060304060c0e120c0307120809010807091a0703081303020d0e120105 76
    0xf1902807242d19141c5034038545440070507003104040504281c002c0182580105002d500400c690822159809414114400070070700344022580c060300b48010b020700030b94004001c000b1380780500c4040c8442d134081e41e0a0070103403190142c0d0200042d2248900302401d4031030026140314894030f16104425208560310391f2a15006074000d01c09140d040c0701400007030500c1e00c80d282000402080b00000302d624261218440185600c41c000030300c900c4840082c115a0381d6a00a42d858003050800c000701d04811594681c0c942071140100d001c24081000c4240d2640030341d24041c46558000c0115117161b82e0b0780d0b510300c0074084070b142400c00e000c0b00842c280041d54034040d041c0544400c110007010443c00f1f60040606c0c04c002ca80c4202a0320404a51a101180c008802c03241e41440c00e0a0040722a00c841e24100c840c0b50b60f9901640d640e010f10101c0f2026080900e0081c10800d00903560b658240e15608503030f056110001000a016034030551100010074099400b00c0603518004041011414040318110b00303403202 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 261868147 1250 261866897 261866933
    0xa05070b12010501080402030a08130b070c03020102010c0914060a0309060c0c0501060f031a0601020a12050903100e060a050603100c09030b0a06060801060309050709090308071416140a 81
    0xc041030485040803900103103401031100b468007001500b480d8011945400f2411800f9203100d800084071103000110582d01001441400b4807582d448000342052407040c1d8603800105c0c0154244184086da0510540c10751042d94449002c003407181a2100402c0a9076011160390401e140d00e405143e00400d20f284074280700d103100e54844030718074907003850141d007110060340101d40f148003039440c14400324220700383c3d000440061a05680360381e00c40e000140d14201401500921016042c0c05a00045500501034009858203600b01da44c0d000c00045041e064400400da0071040b5401640000d00c4c4604d070383c04c200c1d0058000b4060740d4050740140510b40960300b454a280021400305802001041441c00e00c2560102c1d1202040003500c2c20104c0003010504188110020540c503500020140040dd01200c7c0080041c81d00411800b0424075003d030600000703d5600020803008151010501c1d041400c81c0d01c80c1c80560440001410030340e85950000120301041425403240301440c200003002d00d00b100c02c41d021 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 261869397 1250 261868147 261868169
    0x160f08090f04020319020c48061c1d0706090905060f010f02150a0b010e0a05030712080705070603020403023a02030312070f0905150301060e030a0507 66
    0x820340500c42011000800d00d4061441041001012204441010b105625403032002d40d0350f075984040381d0300c1d00e0410481c00404110780c40201c10504c2124241ca202d0a81c5420f07199812420316000041d06000a88800d400c0303201008456803040c503141c030211000c05400e0001940d1380c1c0403004080e03c4080c5038540045075004481c02d111040c2c010032400001c2c088884188038614007800460001c400140105051160100d5180c141c98005c0c411080300d85116042060145072591184010b0a0100d0341540440c840441e6031038281004a005000e64001a00510210f898011902d03211100301034140c83d0300d001030211400003807003844100001c2480f650050f0321242540108480c9032254110034661000c200d400d8071420350440140c41c0145481c0d00700070824103d50011904500c10705844891581c0c840c01048045600540c0081650010b582d0b03112900e034486d0240b140c05070000c0d018105901e0144010803104c0d1064190030307101980a0305480028080c6d5480b146095020380000e12503035 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 261870503 1106 261869397 261869407
    0xf15030b0714030c030103020109170d050d0e100510230103050703020706020307080708070c050613060b03030f121b18061908040614011a160f08 64
    0x10311500340e891401c6a00c070400e561007401304070f0100c2d040c44004a198982f40e240441040010001001c240640e22016036154101c4003d0002c200d8980501504100d402d00200c0000215804040b03032909041015500120740c2d50030080041e0944803180700030645c84034640c0000b403000e0a00103416120320710110b01900c5080c4000d80380a00000500c04540c0e481003009120300c66a5433030002a4583d81e034210b40d45010208040c2885e4002000b01d881c4031080620411040c1c49944c00017120b4034070388046411604691003007140c1504c0070541340d800001c1242c040c3c0d4484045000120020b20b0b9004140070b0740141c500d0840302d040d944482910075101c400c00c5811401c4030505440010001d0840241201000c403821203c03d400c22180c102590b42c9034850030f040c0c43d28a280c4150500c4100c02441c0c0c15000f0050403a030382803031112080085400d01d000301d0000c60040700e01304d5580c = true := by decide +kernel

theorem cover : BRFrame.Cov 261690647 261870503 := by
  have h0 := BRFrame.cov_init 261690647
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261690647 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 261690647 ≤ n) (h2 : n < 261870503) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
