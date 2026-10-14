-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1665
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:07:44.334287+00:00
-- url     : https://prove2.me/submissions/8d25a499-be99-4a17-bbe4-671a5c513522

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 299280575 ≤ n < 299460431 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 299281825 1250 299280575 299280581
    0x307051e06070801151403071d0303090d0b18241509010b0a02010f06030b091504020609040903020a0c03060c0e0303072018150907051614160b0d0e071404 68
    0x109103149000e10f000c8680224101c100d80c4150f48202c00034000b1340820441c03503606608003509c40d400314000c614004540010030102701c642200503000840300d03000074200d100d00c13141d20500c90390844d080da40759103120081c5240d003d00798201d44180d41103000010304405041164072030080401050215107030304c0c004092070180d0003000218119502c0b50307641e0f10062034034026034000d1072064418440525003600e110740f400b4000300e0312550036030f00031042c040543c5480040714070f01182941c001c40c10340040c0c241a450b00902250041c001e41e1181000802d000440c0d000c9554011a9655402110308513002c1690b6801040d50191440d2541050714080350880d0824411044010304a54029282c409c41506100c3c0106d42c94412804002d000400c00c2ca80000301580c840e5039400c0003801c1042c1c960a0340e007240090440140306030700d44140a002a8010010803030540081c0301e0050000392a100203031044d800c808040381c0e0a9041c2112106601c0300440c001302920790f1051a101c204403428204006 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 299283075 1250 299281825 299281859
    0x5060309010e070803030912072d02060d05040201030605030703050606131113061b0803040b2a07050114010321090b0a02011a150a05070809030307051e06070801 71
    0x220341d6124480c080500c2c0074030001000b013a5180c05540c4900d000684141003004100d65403200a904000c0d0500103110544151643c3d207a28880800841e40d01000e21038811220801a40c449000300e10004038a41c160070652144e8403c0e80c00f88134980d610720525540301000d00005003180c01240c0040d5040c18445400e0035081c21815010900114ad2000c2e140d860b4010503031290000404841071040341e0b0014280002c1c10880f110304003020740ea80d2034410303c13800042c0c802089880f107000031640d81c1484004c5400901c1000c064207030050201010310910303500062044440d9404c14080300048280200e40504885c0c00800c4084803111580211218030209500c920034840e2640000c94640d0140c401340100c149541c00004005c03102001084903c800d99044901c10400729900400e034079405000d443d5140c1d042d041132317034544c01035103407101c0103000c4c080c0a039130140300105400f4184000003a01d6000b5200240c6404040c001c0f90b0b81154944004841c503a021076000c1004101c07481040d400006 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 299284325 1250 299283075 299283091
    0x5090c0603060d060c0f300e01110301090b090a06030201081609030c03060e100b010f0302090a09020705060612060c180f0a03120225030f031803230f07050603 70
    0x10100b4895a1344021151152000000038800fa49117010742c640003000149403e062030340b14105035807110344c42c54210074070184144100744c44810412840c03001350004031042c41d200c20811748940e10b401e001d00060602900d01442054076401040210040348101416203030180c0d1500d01c0f5650318401705c42c01e11803121070141001411080000456003003407200010714468480851480302c0036000c10b02d04100080110609483d111112001d0380e0090448070306103056003800350710350401e400007410058050740103080050000078400304000e07001c2900c070701c11082111100e031810700310018190344101c111841c1c90350100c10044404bc01180d1800c048a040740204154040441000415040200f90703108591195450401421003a01071210485049c074114001c8000d40c403142c0d045801d01810f01c8003801400c04910043c062511840083c2100c2141c0c0003220710f05a40c80c0b510f9044515800022740300b40703004920b0480303900004102801c010740c1040007404401e080c901040300c25403021300703004 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 299285575 1250 299284325 299284339
    0x60809070312031a10020606190f0b070618080d09020a05040207050d0306140d140c1c020310060b0703030b0303192f061506090a03111305090c060306 66
    0x5020303a0701058010070140d501041c034445100342d1641413210000814455407080440040c0d840c0c0c001026540104201d810f80410fa103041514008640035800c0140443c00b00100421445568001840104e00c28001008001d40488840b040100682d5000300807000400c09844041c1c001d800c10344c407803800142654500d507039641c0020100e034003403902101c0396081000044101d603007600c01d84000b0f000c40b07840d005e001c040e900000307041402881c01c020003240081500c807440c804200440b140c4040054101802003040201a800c1c0b1907820008922a00c512440301d840f50099002d0401150310004c0520709000103070344c0613000344c0040451560140700c20f000400e00d550a800070481381c5980e649441418031a494080780d83c5101caa061560b051860450601d441240011000d500152001c0e0355446112441e001500500c68100d00b0355018200600200500689500a0344a4203046485403a085810072440040d1403045440e2400c0b600421040d00e042c0c00c0040c025544050028848 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 299286825 1250 299285575 299285579
    0x2190f031812021003110a110a08120406060b07110607030212031014040b060919050303040e090f0c100c0309080105040b01170708070b070f1202160504020301050a06080907 76
    0x4100492050740b226010300c0300102a10154106002c0001d12500d80349000d010b0a842910010040c2c4503400300c500c104110407a2090182805002c0100c10950008031982e5450761003041001404081e00d050300c8103403601c03600164040340802210f00103640b0a1444041596200401c00c0981240364203401f50300805401d001e00b40c1c01072000310f00c1454112100c2c030405080075080d41d1001c60141032103008130300c0e1602c0b1102e15507070f080c16202158400c56101040300300c1d0f844480c0415502c4e500c0305814bc48003240210329141c90324909841000d8210444480d1025048915a9100300b41105600308038001c1c2c140c0f01180c8a1b180c012129406403e20000c2156a80001400c54804403070640e041c0701d102005014244c88107c008500b031101400508800e8140500c103500e0b9001c1344122a000c0e08001001020003143c0300c040c001854010390703110901890300d4406500d545965803c2544440784005c085414035203442520706039507029043c5c1001500f0184140c40c400b00140c4065402c1c801c441e00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 299288075 1250 299286825 299286857
    0x70e0301090507150e0f060903031b06071b02011215030f12081f0509061305070c0b06060c03030f0403030e06010b090a0b03040b04032a03180602190f03 67
    0x500e00300340c0c030840c02080c146103402e86400600491030010000c0103443d140ca09400e41d070b80402c88500b006c0031a0f02c581d49003c00e200003865840344042810011920300c0c01c0700c42081022401d0352007084940c407180f0000443c410010140803640074000e000c1508807034002d40b20742135940819070401035161155182900c03078658056600e807000701280c071041e00b070815140d103503405662b030341e04004c000c8540c3c20010481442802c0b000d03030a000751401550307414000341140d60340820480701031000940404c0715041c00e0038010140078140ca0295240510313600403071401d091500c00c4076440304000d0701540c210388503000c40f41500c08015100750201a11390035001160306040c0b0256008151100d1003030340d070f40307450301c10b00003511020781c8901031040c000e10401c0301059510b00441e40c4641c3c18584600404000c001940e603c4080c00c1c81200340402c00c000741801c168019030500110740103031450101d0329548890480c2c0c2e9641803000d0190800c81e400043c00054510010a440184203052070001c0d80850360f1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 299289325 1250 299288075 299288081
    0x209040b0a2007170901020a0605090106030f150506120c040914010204060809191223040602010e060c030105450103060e060f010b0f0f040b07140d0f0503070e0301 72
    0x10718402e07001000100c200821640c0004034441c200e03002402c5040c000c00d100042e4850302081d2000d0300380c035260030000b54400820f5111102565110901c1450800036050181001c2e0180048041952030500800c0381450401d030003284500c0441c00030708210341c4041c188800b82210400c1181c11101c0304042c10040302003800a440580b0082d50f564010f803074035640c02d515200d0103031201500c0307102c5420800041004200d29220070396460074020380d64401698a41d10303490604440c8800000e000c0b40211703d0381c1d03043d0407458406454074110740741e6860300021042a40310030b1007600d90061010882d03050349554030813546840c05061090310100c4480305022520141811228962131001c80018420082c480c4039016110b85200010300807850115000d15144806000d420124000843d907400ba000e048001c0301e1110f5520700300c0d552120740d59000b102d060742082c40111003003584100d907000b520b440011001e8035040c00384d45a1101000c89041036640d5440581403c00f007141d00d150035800d03910b00340 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 299290575 1250 299289325 299289371
    0x905040c050306030d0f020a240c03060f0b0f0a081b03090a031209111903140105040c0b070c03020402090609120715020106050102060610021f02030105030115030209040b0a 76
    0xc1c6815549140042c10107080044c0c03000f6060601113040f40d084e403203940c00221030141a600c40d51032502a0303250300a0b04400e840d0003030b09078605414000b0000304140c1c10781040c01280c07030481c0300e118066200e140307140d4513024030400a414200705025441e10305225070560354000041c2d00250f0001c140419209000e039004590101e05a4000340d01c290030164447c2ca91418940c01d4401081342c0100d42d0340e5000c0070590685641d216540095200e841c0900901d4140c0085a00c90565030394544805078440c00303010100e0b0140c4640005010008160840c0300031101c03010b0348004100062030a680c20000250010201160400414007d40702e031621540c8182d07101e511104004d0984624010402454510328160340c0c1c216410a001003007a42d030002a00e5411440c111401c43c83c80c5520b44c4100d1030311481940369100381030550540d550016850303000318145e90301603000f03000341d01501440803580c1000e40b1000b50413104410005001c1000c50180d00d0304051007080100384004130030381e0050186045d0f = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 299291825 1250 299290575 299290577
    0x6051203090901060305040b0a0905100e0c030c040608030a050f19021b0301180222020f03041e020a0302011b05030a050c061803040e090304080102030c0d05070309021f0905040c 78
    0x250340541440c2c00080c030b5006009900d02800145021307662055840d1002c0c03c0e0006035500ca01c0c0d01c80405c03805200b43c0465560070001042211028021590307144400ea4085000c0d00441201e11058202401203100ba07031821b400551500120010440e026032086011000383c04060183c000b02404410300180100496401020290005003440c584e0022200006210b81c0c506541848201c106106841d0030301e8040f80e90040083c004405044010101d003020040c4a100041c0c090190903990040c5000d03d01403800c001038502c14500014044060400280d840b22001d01c0030401981303c0c4070b1201c4001c1c40c00e402170204011a0f91420300d5a04500d01c0342c1d011560200f20b05580c0d0408010455100c0c54401900c0d40b01c5c0703843c01c0340380c0d12442503000c0d0f03141380300d402000684414400c10450300204005c5000315541d2a0140d81039070503400c0441c660355540d06103004900c1782c911a0240d03181190300285550110200041d04810741601d05099805000c1c3c2d40c0d40c005110307622403081c0b85080440e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 299293075 1250 299291825 299291827
    0x1021206031b0906060a1b06060314060106170705071b062618160303050403150b0f06091801030809044706030a0603050705030d1d0406051203 63
    0x10034101400d114154410792a0258150850002036030f0b40301c41c00c0c1e0003500c1691401e589051014044410710814141c0c2800c1040d507401a10400905a0210049a005440f0803612816410b865611a1020310a0300005010120501302ca0405e0040d41038002006040c0070346040c41580d41c440e4030f00901d4002441d051015a42000b241e90040340007090390307401c01c441c0800043c541c07141c01450b910181c88141170403079441c600481c0c01c41c1088480c102000f48038120302c045580c0c1c680208140c3c41030008583c408040300b254030b456200343c0100703544c1090003040342c07109009070028046c454001e80030081d0301c8200804480268102c00000602035809410700799595050007040c042aa86035150088207103240101d21140b440302044d0078800060829504942e21500070a040c0d0605103100740d0075030103d0000140107808174942d102c001264840c005413044c06941e0810180c0341c580101056010804c00603100f007140107a1042c62107000402000002d009803610080390340c90244403064042940 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 299294325 1250 299293075 299293081
    0x304110d0218060a150530040506090c060304020f0d061b050315060f0f18040e06060301060501021b3321010f17010603080f0403110d03050712030b03010212 69
    0x410780038480180030308100000f8442d174402c0c0014164401d050007180e6900c0c0245c41c620f4400c08401c03800d80c0c01e6000362002d400740c0c2024240a500c904081c1c036241103138859054410401d0525a081e01e128a400400581514855109001408845000480d40b9603500c0300b04060941c0c1c130211034414284140c0e1601c0c1c80e40350501c103500c030b0b80800d1550b803031041c00c090110340e540b0401d0004450304040600710031740d11101503401c020b455443d05900c04d64080c1c10b1060001450100080603885403000f14000d21440703540d0b00059031550580003a14082c120045000c0300e4605200c03910300101118000107003080c068001c3c0c03c0403981c01e02c03041915003403000100c01c206c0e5104150b016203c0c3d80883c3c100f8070300b545401c0c505c20040d0327100d1140303403802802c902c05114070b03140a500010055030082c0a02d56243e0364428420391650060200303d03040c02c04c0403903581203410030601d50f000c101e6154440700d141040b2600c84c07040700d804c0d0120010030180c4a00301c4807460f8500b0300242941b5034010541d040c1e030742 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 299295575 1250 299294325 299294329
    0x21615061d1302012c18040b010b1c062318070c081306080f0a021312050102130e011502150403030e0f030a090312080601120507051605070510050703050304110d021806 74
    0x1d42003000105107103c031b0414003000c1010b1101c150704460512101070783d18040d6400c00c800e1461003049801d0101d01d04070001a2002d880400303405d1416512102c00c06840300c0f0400c024007a21904c1d0302c006000c800f440010400f50040880d10080c1c0d01910324241001046510303900d12010640052000819090900c20049111699641c1004010340b095041c0302030740c0d14000a858540c40b801500445001e1000c00b0b00a0039412911508103204a9003413203512024001100142032140d000c100240c01403c030030345032020600358100c0c40103460500c4580c0300c5440071800352508019a00d00380c0110141c49194410070001850a0080f82e01c03064a22481c40c180946400c903642151002d01020340b0030420700c6d0b179000e58001110740c056a03000410342c46140b07003102c05014092801c1420290035400100344130001960604950003210a15a000041b0904454034000c0c0b510040216000b840424001060f00c9036504c503260004e424402555101c0c3c0014105004141d007860500908a051001c1c41c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 299296825 1250 299295575 299295589
    0x112060e0a2307170c0705010510170f100e0f06072f0d0f0e030f1f0b0109030b0c09130f05070905060d0e01021615061d1302012c 57
    0x5100031000da00345240000c00604403200d420405510131030391000240c07905064000b62080c05070050000c100d11701e445e03e01c0c85071080850181d1081c4100c1c036100c086035048000741c80c00d510340082c00504210030781c0440e11401f0b0481c0da80910014025000f100c40071903010003d4500c144090350300d4401c1d0ba003e0a4100c02440c50042035800b84074040f840002c810500083c640c45103c01510f00819602c60448040f900c0d60000b290090740745c029461501480c00c40040d00c00c0496004614218035440110300203412a040390712024040750014108002007801981d40c603901c01c01825400e8a01149600081c1140340f110b00c14550084e621b615010350481944a41c0e603000080d0701301140e125040c080014110b01544203900342c09600c0d051504100c3c002901907a40680d400c05a5003000c1409103030003c5100c0c901066a82c0292500c075000514264002d0200e0300c40d40e14000d0305241d5110820518954011154141d0603c070114074410000b00422054000c122009c407440f0000e180e03250304001103 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 299298075 1250 299296825 299296871
    0x3062404051b0306040b030f0d090b040e01060c0f05070303030203090d090501211103040305031e04080a0f020102070b1801060b091e030a1712011d060112060e0a 71
    0x65150100308180c00300d02c0d01c01c01261061090720a03469a60700000540600004c900d0103030103002c0d0703807101c040e001c0d0000713200a0001c1943e00c800c115951200d029181501481c411000806016001080b13030300e00440240981c140985203910300c00e00700f0b4607060300d4203000740d0045002a50000c1013000d403c40c180a0054541960726018101e41e140c003000074210900f11240c988038000205810b60500b00a9100c0e0f0202c05150b69810380380e14003414058501e8108840507020f003e8a52402102010500c03902442268480b02480c2051440002120300f0614044140c1c150b40d0b00300004408034191005561240c101d40c10214031034882203105500352010b030f600040c4a0745042c820f007001130340e80c030b041c0404c806407c1040080c0c0042c80e500192506d0080c85000e0650740480c0c20000310440c00c071009010a80303400d20052074a9982d1070031031400d03446a0340402c1c00a5107071001f00d01103620409105043c0b406040d030102d115502c4044800844d03406607609480e00e56540040c030166082482d034140 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 299299325 1250 299298075 299298079
    0xa05030a0209010302090a140405010506011b0305031b041e0612180b061f0906030b0909031e040b0f19140f0a0c0c0306140604051005040b0609030624 66
    0x3000c08555020030080901030000a100c0c403d014000b0300b003003009070300c011440c0102d00c01d8080b02c2d08180c2804c60081c04c0643d2400d0024080c10002d64010b001d2101e038580d003513415500c1500d16540c040924072018250030702540c1d02401004000385a42c010036840400303500502c25810014a44007016050f0303045550030001150420350020b5501048039480350455400c079140c40e07a20390720b260000305565525444041c507503454409098a40d43d201d43c5450a07105e0380e8504101035070901c0200040d010044800f070400e80c1c0200144e640640c400301050543d99042004d40e4201500d4901040340381c0c0103113440f2501c00c44081481c14580c0082210104400b982d81052940410040c080c01643d226540400040394000220084094459600c0c014069040301c960030f00306850349456800380c8100c134285c2c1c064010030381c08104c491409101d00c034040c495942d041c9040529040c2404041d00030320803010340c40310090082d08101e45050100a02c1011002800b0320f07060b80307007441e041c4040240c1000d03074 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 299300575 1250 299299325 299299333
    0x10b2a030d02070212030417071409150a1503020c060a0501050303040b0a050f19030e0d0f0c0809090106020c123712030506100201051b070503040906060e0a0503 71
    0x806280004011107441c15070001c0096a0b0302541d0002c90b04101000c5400d084038400058001750b58102c4403889000030b083d28090700c4225a440c04001c98114000c06200e42c0001c4400100c1c1907030f405040300d035a0500014100314400c0c1d90f9488000740c00c400031062403021940006011951100500070680c2c441c154940410155040c440482d035240503d01403000e02c004002a04000c99000b2000e680400c408401d00319901c0b644450001c1105240104020100c2d052120f400400c0c500170a42540c1c0025076aa0305010a14501080f501143c40140c02d0340c4a410070042d1002a86030811914040c2c0166002050b40b0f401d03400074041c80b5043d1050150140d00240d1109907074120701d135407180b021440c020038006415032440c1d807403520800405000f86100d01d00e090321951035826800140c8620021503c44181c4242d62206900761402291481410503c1803000d1303141c24a4400a80b030400d00a5040300d0411f07803205010b41c00c1310319641011000c00c1e40c9003c1211140340c018580c0c0040e10068000d0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 299301825 1250 299300575 299300647
    0x501020c0f0601080a020607031808071a18040c1110020a02060106050a0804080901030e030c0a020310060e04020402030703110c0609120406080a0903050c030f070c0e0f160c0209010b 80
    0x20302e1700c2e02462003000784100800a500e0042c10300ca00300100030400d08940a0304d6855130b90301903507981d8207140f044100003500110254410b101c440242c82c1804007004912001d80d41d2078003080003c16114108105119441d4103071403a085c0b08108400198220100c0181c1c0d600d190000680307441c4050f0721500030883e00700810314189900c04d40c895046584080382540354a064401a0007812010522000d00e202c0420016421100003450144050081c0c059030005040c10140c9403c0d10038034065100c0f25030759200031a005051990085130700080e1460b0005201001c0035411590f40d0080051101c0c9a12800600401300344c00c0c0702e150007000c5044281e0b4079103480d000d8094111203000384010152561041500241805002210503814440040d030740d0b40ca442a1446001e03410010301905d54415444000c604180805860750043c08010701b42c04081e46c40c1d684401c4030f80084424441084500404440140c0710006c40740e01030b1910018058551000f07043d90900c5059800d540e0042d1114441a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 299303075 1250 299301825 299301839
    0x6110702060a030f0b15190801120206032706010303081510030b030c10110f07030b061005040806100e0901050130150b01021c02060a1e090501020c0f0601 68
    0x4440c0c000142e800c0120314611100c9402c0000e20496110540028809030020100402c8000502c14180303e2880e01d81c08106018048920b09400d009114a4007108075a81c1c0241c940760000d95840041103650f0100c03c0c0c0c01d4a1484808855030701c098010b03500035001402015042201550f20409008031410407001c0d4030005414544c0f0001d680e0300349035490109142c26201400340031003084000d08003000302c003007002c001410740c11b548000b1300540c05070502c1e01c034085801107001811a40c004811030079035100d00303040020041c813440041c0c0a003c030801c0000b810080c2030046511806480060070380240c5400e14600301c0c544020416030050345000014800085032981460154030003080005070342d50401ca01c0d20444810311780c080c0040340c4921101d01003900580181c211b408085c1d09964000c1441850784600103851081035000d6044580080d1003110340b41e0069000c461207020796103607045031700d0202e4120703101004140c030365940003d03491400d40006c02200004007000c10042140750300d8186 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 299304325 1250 299303075 299303077
    0x1e07030c0f080c010908090a060804021509190e0f070c0203060712020702030f0a14160504090c03062c190f0f0c0807080706050c0d1202130e01030611070206 69
    0x100141400340301c22480701400341c5a0142e9032105000380c000c11091440d0704040d1110f812110f40d0350310404031100c000c80e41e5803003109100d014a502410440140700078405400c02c9420003d516600301d450000c107640c003495000304c0240140500e520811040c1002d07040301c0b0b41088014010410b02007184100c40040e20001900b950000071444c00c20f40346424950f0b408064840c080c00a58148034048003c1c0076040049800c5045a00c41c40141a402036801151500e034440010001c580c0e850100d01003005080c41e07040403c409220b03101c510000c07a16607a4002c1100c0007a008030080600070340004500d120742c0490710580010500003000340c20210390360510f036224925002404510b1004140e01000903c480201c00740d0b500c440300c40e42d01c0d500c0f000502c0e600e0402c1d224002c07107031160fa600065070318020300490b400601c0d8600604080c0d82400c3c415503000300319900390007040703034200f007014070410369070101d44050306100800181c40d516509009003640c100d03211174004e5450130000840182d807510 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 299305575 1250 299304325 299304347
    0x10b01030204080c09101802090a09050f04030f020a06020304080c060109060506040302190b040305030c0d0503010f1e230a09050708012601020706024b0f0f1e0703 72
    0x11100c1d072890350784d541ca21003041b0443e0f1060488081603581c0d811071021039001351074070607000d80c3c00b0b1b450290398180046c103880c0d064540d1400407840c0c0001c500480d2060001418146450044901c601440c1d50303560101c1e03000300d0341070b200c080e008900c41030445010300c103007401040e8002040c00410b09000000d031551007240b00080c1300781340d03000796001c44540c2c40340e0000080480031991500e860703590030070f5030f00ca911260018560b8000c0510684840d40901e0960741622840700c2600640c41c28003081c3d88840303102c4a54280c0d10b801116000400e180d5061044144942e20b000b200e050308403400900841d0078054100c010281c2c2480100f040f03041d80b02d84601e04607a124139003020741c0024100381c00030440340c1450b40040355000051000600105400070062010800340401d0049034503c803681a40640d0300c00d0420703070150540010b4020469100501040c00e0030400a0301d030040c001400200c640c03280011450106010440b00d00180d907184441c03996a4030b0161035460404240c0e8014803e403220 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 299306825 1250 299305575 299305579
    0x819050607050c0a1707030801090920042901181a210106170603210903030408010905070303030c020303130f150f0905010b0a0b0306090912041502010b01030204080c 73
    0xc1031903a81e1680c208440e0f000c8030f41002c8620174826032134040d081c4584c4144002d40108020000000e030b40c20440c03188908898202c01440f9050301d880c0c568101180f1426411a4002d0f16401c0201d90700340c40c588040c0f0040000300c00c0140c40d0112500160101c0307503501c1d800c00005900c0a007000101072090301031005100e0319080d1680c0f0310b100c11350720001040484e1001e081200d10000824550b803c8070440c0c0b22041c080d51441c40c1ca60703400c0300f01940c0d00c003010f07045000e056074120784075520300302d00e80540758030a80101540d00f403030b40f201003627803c4070514030059940c1d60007a5810014140c00d031159426143c050303c00b442c5540340c81d81c00d10400d10400e55000b014004400d0410090020b411075901d11888800350a00c004141c070351504003e0f02c001d2000751144e501c1e0400030380041ca40801004111029540baaa046540d1442008200900100205554000c0c6007594001d245148001c001a04c103841c2141b0350401041402421200d0703405406040c1407040200788005640044d111001d8882 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 299308075 1250 299306825 299306827
    0xa0b18120c010504170f0303010e07030b0604060e0907030e100b09070c030807180b0d020307020706050c1b030f01111b0111090918030301060306091a06190c0209040c081905060705 79
    0x303070b0417071030b03290203400c0310598043d01000c00040f644603580c1510780c0c024100740d6001c1c4034414010082119611942c4a000045200c10141d2031080c1030010820364440c0b0079041c00100703544c103c12000e0800c104100b080302c859507508040e01c82d41c0303012107089401180a10b0130030300140d460b9401070002e0301d02400b65410701500c11100b562282c8041e8011020302854061702d51500700c0c40c00c9440181d00160b80e2880540641c4001040d00c511410070b0b00e0100f07640b0f20082a035603015242d1504034039102c12800b5014001c040c0b03c0c5d000c00009018100700b4409040320070762307504042202050891440d04210815905101290400611080a07556092021100070003140c4580c5000c5401600029111310b482c00080000511543c060b4402d000700e6420385410f012046800c42246414540303e0b40c8a94003600600c50026042c40c00b131032810981c2ca180c1003203a8041c7d15500002d842d031000310b034102c0304103180350010b0100220902480c07580000900b040c1c810140190341d40368503004000c00203001c200d4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 299309325 1250 299308075 299308109
    0x215011508091006030b0f0a0c090902130906060f0809061b1c0624030b06160302070305010212180a0b060f04060b0403080a17040c0905060a0b18120c010504 69
    0x10040c00070880018403c03808100c120358a1510110480081300c000b81c2035207410000610f82c403001e0091080029440e9a0420a18102071008000390050821003032907428100003c0f8000b401489100003070421600d0700c00103124401c000910844004040e0241a00101c0a00405010781807580042d41200d40c515619258100f0007100e0403120150224205400c2060020300060344290300b100650900c840c00c603400962002c15019030720b10100a50304141e0801464205406280301c010b03840b0b11910581c1e803005d90b44c1d01d520b800d81e000000c040c1c0e003540d401d105000902c4542c1004400b0500200c01400b1580741c25194500c4848009111a00880c00744c2c0740c410050340d5650101019014a05016484070344030706110302c00b9081031002c0c80200e000c00582461699100302d901e4400d0f81e10131001d0840905142502015007000b81c106500171641140108800207a5009844000c0003140e019000240501c00c0121a929030406680190001c01e41400c683c1d80c408200c0f0140c8083c9030100150072 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 299310575 1250 299309325 299309341
    0x42f0c03030c0405091b12060f060310090c0f090b1b0601060302090a3c0f090902040b09091e150c180f01091215020c0709060503120406110703020301150302010215011508 75
    0x804840c9e43d800280001008036910f01c5e0142c88096030804801040003c03400002038a4441048201a003c110400300030070095041c0340090140340400c0da02100185800a016850000c081c0c001e400841c1d0080794140072401c00505450040803502000900125500000301d0002c0340104009078400c0860b0b44030b0503803180380c501c9100901001c0f80180d4425035540d11b0340010000b81100300d12450030802641c00f98a40313820824000e103845d00107001840300040c0c19064182190340545820301079200b181d81004802c8042034402c1224200c510703507428800590814410900003d04c0c4907105181c50042540d030701400031004d64001b0b03002c0c2010b18420303060101c005880403440c1e041050000841e840e45400c003140c0c0e00215a041d0400344481500c40c02019140ca641900c00c2a640c0340900c001c002c2c45225403c80e1840410400a440d1102d889070042402e40d2a11600c009008408190400c110359040150b01c40f9010304503920703010f41d4104682d00c01486500c84181c0c08100280001c11021 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 299311825 1250 299310575 299310589
    0x40204120308074e0c03180209010501051c060609051801080607030b030703020402070f0209010801020a0507030c061d010501060f0c021014120a0605040506042f0c03030c0405091b1206 81
    0x40c0e4400e06a0700840506219180240800f17040210000f8240341402d0080e09540902d81d00c12a40101580590f0307091400449040d00540c48004038540c1110004000120343d21400c1c0252955a40d12015a8184024000000e600c0c030f00f4007410000103801002480c1000c918a5003114203490701082c02011400028540300103a00040c2d0b10601c00a6030804108074030315403500d040d2082d642e10b01d00d82c5c0c0e81c10b00a801c034010b420401c00484c40420103000005d11880d080100c051240703e0002d20720303424480b103120f51b84400014840c0c6a566400500c0095000f04c041c0b242d800d05450220100d10707160303001c02c0040c540001100c06100780da40b04a9a810364800030390710b4880d50356040010074500300601202520140c840d4030300a42c0340202141090400f801414000d4010207141c02e2009405060380003200205480d4030310f00c5030b09110030105041e042c0029405425860304031500c3d681000c04004c0004400341080c0004001041002c55080c00709080d034050004d40002003a250b0b60310301c04035500d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 299313075 1250 299311825 299311937
    0x207031202031b01021902031602010503060402211801060f0b032701020711040b0619020705040c0801090513030f0807030b130f0f0509030f03090c04020412030807 72
    0x20000c0454000f4201000550142c0b021190840083d41004420300040c0d807070741b20b6103254072040d07600503540c0c101650041d0003d64000102030401841d18503060381c00240c240d801c0105280806840041c80001228a0614422211800d0003004290318018964000304c0035441030114103007020002079059803003040f404c1c900009001c203407170824004072040b9001703501882c000c942c031400da2200300405d1b003420310030614051005000603103046100446140f05842074840714045105e55070000c2020f80701c0d80607000602c40503807500105541403c60071019900c00400269451f00100158004070342d004026981e038031f0b2142011101c5440e146c00880207007104848640d00402c0300c24500c1440c4a195009801c0510303841c40c100309000001540805540041c3c0d110600d0b940700380000c08420384848002e51300001c03d0070851705031503080c5020030f003a41c0055000000c404501a103607010f050f004021141d0114840c9400c0d034110444010b000c10b07003484041014807281880200c603240d0101d40380c174104 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 299314325 1250 299313075 299313097
    0x12030e040b0306010803190318030509032505090603030c03190c050a0807110f0307060323010f1a16060903020a0b0f151509091003060608030307030e0a03020703120203 74
    0x4a0b42d1786070151280e0300d61080c0d2000b540e0369280d04007000340b17502c01d101d08500311804401c1c03440340303d15075201100d06401c05401a0781c10701030711072281d510640100780d8000800049901d034032410310381000c20425407001064203000707410070091032200e00e501004464000303a210034400945441420106c80d0341c5d28100c8003c156100d0302c00c5040078005800041c14a00c0e1183d52518204074840c804c0c800500300180426030982e10000003440300e03034001d40240782081c217801d00c400325030341902c0980c000c42d003070a03800010071543c000e005100741c116002c120358203403100c514540d281c070400c2e01122200140000d000340c5803640c1e46414104140c0300b440b0358899245c04c034045181d0340c1030600292204020a8400d64083d1450440d00320080c14501000c104c4159140011405c10844130284800884000d0400d0850a06200b010000030041d21400016299000c001c545a00e0b01c003501400300c88800108000c1340d4444a1801c0000e54009642030a03240e01c01c055840072141440280d145008482e04be107 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 299315575 1250 299314325 299314333
    0x190b03070816020d02060a1d03070f0210081005040c0c08190f230f070f05030d0506011707030e10020a1116030506071107030602070b1803030112030e040b03 69
    0x300301a544118810302034289218501d20741d00c0001d000382c0e9540a40c881c28400b580111002500d0318040754099690501ea10020600c41e1040354421421507104842c01c2341e00302c00c6900e200080d4241b5116081c200d2016041030351240c10516010071034a802c52042e83d00c615156640102c019218410211960340d0051205454169140e00000510320340d0380502d00052503240c074001c440c0e21844a40088414031700101000442d030780c80c0702400340d0006603030310740c449400c1020900182114840002940c001e10140d80c42e918068140025594080c08940c1000209200300040480810019810005604000441c02106030f4201d0505503003210b445512440494424010b941045c3c1001c0c25560705001c1e1501d040c030300e94564003500c2c0300f40005000355000f0000685950300a40550007807251420849581d00d9681e41c4070001e0340d100da94103c614002c80d00c140944002408042140b1a0020001e513082d5030405408081040c5002406810480f00804c0c2c62440c0d1115032040701e030648c0140540e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 299316825 1250 299315575 299315581
    0x80a02160b0702090702030316180302180711010903120e070b13030203060a0e0a1b0305060705120a060e06150f040801050f0a0c090e040204021c1b0509090402190b03 73
    0x1c190425241030b4003072408900060440c52010003200d10506080000c122806c84c0210202c41041040c012408141c1c540c40c40800540c1d141d82400741e0348000307071a00801c0c5180c85680285035400303641b0008410b030b0500031118002030f007007801ca450403800584000b5a03c0c001003c0f07285089500c0d40480c104007400204a0710b0036843c25000c1d07043e00d00940481c0d185803a105003001c11074900c0305004007603401021400001444407417041c55140e00300000043c0b09900d84e1111414480d0a0340c1d05008038000041c0c0c081c3d071189506031180c0c84070040d00c0802040d840c14001103090348009052521826071091040350800c520300544082120140d0049d8840e900c500180703000302010386008030402001000604038a52034040d082c00005d440c0e944034a01454089610207082e40070b0000c80c1d000c1d80a10211400708031403000416102039403000869040800c1916040c624040c2101204003e401c2212642e10384034000d40300d4101c1d505031500c104000c4440ca41d400311031915000420b01e00030000174 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 299318075 1250 299316825 299316839
    0x130509100903110f070b0304080327070f21080c0a1a04022d040902040e03030f060a09022505190308040204050f07020a0b060f1503091c0903080a0216 66
    0x207400c0303d00c031200315003042c007200307141d40e96540b410b100781e403031200c000c10000b0000f07200d020195030401c80c800c43e505a10b601c14280d030f40348a40c1404808d05250300c8203000b04500b01007009a2001000c0207d081ea212a08601c580451146e50120223000c1c50070005446a00002c1040f01541d45504a2052a15007003066a118410001034070140e1044a088580c505040b404c8440c3c595026004041c50700941009014840034080c0850141d078840d80d038880c04140b0780f005000844c495031000c00186c50070316051082200c041c415400c400c54061040c00003103101c42c0d0b0140b034003a2800520001c000c17030f01a07a02c0c01c240b406a00e440c800c0300302c4005020300401c254002c0070b03503400341e48210b50511095581c5100140c1e180c03001c503000401640b0003a800b0020640e142803054200401501c0f102141e8281d00214001118000b43d6800c117210010402844010074010b03c1c0302c15503183e80f0702a1140180304000c11041d058040602021000035080000c0c4d0b0007040b42190442403031041901240d61191 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 299319325 1250 299318075 299318087
    0x40c08160806010f1d0403030f11070209010b090109120c030c0b04061209020f0607030903120e1c032007030c0b0d0c03050c1803030906030c07050708060105130509100903 75
    0x481c2540910428002160249981980c80d06940c26500742c40c4181c950500182ea021401038800c0e4141980c507258400b215245001d25a6600e00307000c000c6e03544040320302c148010342c91305038406120b000041c0640c07903d0f0307030740813003850219200003482200500b0541008aa292100d80c001041c00400000000d40941c4040152003112180e407581400e8280c418055010740700c1640000390b000151070248016440c0c50350203049001d002c2c0c41c020300e41c40c1c0c4bc1d82d1098241d40120307120740301080c0f9070304544440e8070740a10408061a440d800c44070108166580c00780001500062170f07481e10a603a8035900000a080001c0e200440c0c2000c1d100c0e450326514505240c56501c44290104068100204030bc00180079004050003180c00e030000300d15000700101242c1820407070408807685400100485070981d620500554010740001c1060fa41e90902892b000380740c0900c0354000c02d1250420b4004029681e500c003420900200149000324450f0750340b410070b9080c45480c01d1005c441c949030196907404d02d42c0c061 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 299320575 1250 299319325 299319329
    0x1c0905030f030a0503314209021807200312060103020d0f0609270b070302030a0e010e0c010207141c030212160507120308040209040c0816 61
    0x28080e54103120381c0140c0c40c2d80740d2048030340c100c010030000c001040034022000312200c85a4403071000d8004520852441c0310004440701c10580381c0b81c20030034645200070004010008001401e100202c038052644044001e0980240440d1131041d41e58110102503480c2e4445200705084a50300300035091070b242001400b40010310782010740c1c01002566044201e8000001ca585180100140d00301543d150350046020b0b52100f00620503060301c40c40025041c4866004003c054407040d2400318402c1001482d2404e0621a101c0002d503003c20b440519011600c007003046908550305160150344d0707507101d1513148058084002c17844820761801002c401284408604000125400d03400d0358009980e61402003500780f00340f8955a4440407045070709500740c507a002103000091180c0107561500c2900300200780c0540040e1007040d5503c1019078104104032050203004d01800e01441c92183e102500c0d2030080c0f241600604c000d02403203040001c1801e005408103490010040c0d10212a10b9030700c02e004c10f40b100040c034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 299321825 1250 299320575 299320579
    0x4030c0e04030f111c090b0705011b02011b0c0204110f0901020d054008060a06060201090305040323071409060a05030a1515031a060307050108130201021c0905 70
    0x10f0f0802107a151007070100b0010b62500000a1503001131800b018040d01414803011024404601400141d61041e0400f070b124480c00740e000080d103042e141ca008000035581100036004c69141881c00001b41064124440d0100100d00d802480610f0341e101040050646a04d101044031b0003080c00c19044e02403c00510701442e0a900f503a08010410a059403035020f400c180e2012102440b6040c1c98040c242c1192840d2501640409640f44c1d503040c00e075882803002600f14205641120703042090401c0203000c3c8000818080c4020072107a216610003e08601440c00020580d4112040400102e80c03030034001c00c0140c2c005001e4900484c1d0311199405a10490140e84d40210b1040700050f201d4501500c5990403148060040c1655004a969280c62440742e40040d4842c00d0b500e510303540c035804585003024003851003010300d80178641104030894503551000b071400380729900041d000d005e1039a0000f94076402c5035802c90030000500341d40c4010f070f0034910080344c14002c00301092080c801c140d1780600480100c0f802 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 299323075 1250 299321825 299321837
    0x70b16030b0303091507150501050a0b12060603060103290118031a060a030605090c0a090c0f0f050c0619060f0308090105090409051c18030507050d020604030c0e0403 73
    0x44450258152010524103a501d42c00504c2614568240300d0300e0454082c44030000c980c503040e6141c2d100301d2110101c601c8007000559800060045042001c031000162204802d4241004840e800f182040040149024042c2c0008804282680d010750440d20039241c0014507000b00300c441301542e00030400e07088061400500c00e60003400794070082d0b04907001500e40281c2085003d100007480e440b02490094075581d001103414000201048042c468207010350981e0002e4402c00c5150805c0207500c4d405900b0031843c3c6880d20428020880d0065865007803940b05040030030310110440b400382d0301401502c0c1d50020a002d04c400b04400c0e504038445080d508600b101c400c2140070307114071001c9810340d09400000c0981d03000300803602c441c7d8003a40180180c01c00091010403407462647d01c0c0703410089000c848030091000740690500d09038014440e401340d1000790340e01c00702c0d40f0329540391960ba03003a03588a12400b42d816001014190b407039210480340030b581c0091000381c5085d0350341804800048110380c01d40000d14 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 299324325 1250 299323075 299323111
    0xa12050d02010b010c0f0215090607050106061d1c0302071a0301180e100203040f0c090c0e0f0a060c060f0509030a1404030305040b0912060a150e09060f07050708070b 73
    0x1c021804078a05903040b03010b0300e001b44059400d0060865121034804400581401000c0555130740c60000c10500e07203c0c20003c54401e1400c0c134040c100720001d041d258040c0610b43c2c1e180d08203840d054940810902008140c4103040d190741070aa0a00141c2d4002c100c49068010b0070190044e20322004504881280c1e84c1520283c0b854840c230f030704841740000008032a8020f1071440002e40d0b07680d0069500301d8000c038000b450144565440846250807580400e103096195400d618517141c100496203800c0e01c040c1e80d40344401d01c3c00300000d4034a161030301401e0144042c1e420220184021940000307050300507400d0410107801c1007201190760340c0000c8102e2000510b100d8111255401a001307407012a585034490f5810242020007100241d004180d101c3e40144102e00c103204a07080400056000310356411000680b00109134412101813110740040d0800900c01052041c0b40d4400242c49510084440c2a0092515211412140b600c6180400380c01c81d50041085024842b201d0756090040c8114080f03d40410 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 299325575 1250 299324325 299324327
    0xa050306011a130803310f1203050706110403021002010b060313140106090209030111031e130803010f230307090b03030708030f15060304110d020a12050d02010b01 72
    0x20901034a42c000e80140002c60041845101402640034000c0c0c00544040c2c80b003c40c10700e107030001d0450508800700c0c400c10119a824806800001c10511654501c0361402e0010221498540740b1820001942210300001030512500541d0003141c1c0c0000140070034507200765040719980240c00164440d40ba0400e10043c4103005100d2401c483c1b01c06001b0354119038031124a800c4040c00b00c3c8044e9120389940e42a519220b40a20070740026000c100c1d0300681342c0c17410030b0a150071504141108100740d0010404d1040e1080d88520103410020021021116640e414600d410b0b44210440004c04060003c000441c180036000c00c402c1c1035a03400c2c004111595202440b60441a881803005a0507410601081c0048000b0b500407034809800a41142e01c0e02d00207650760720040e482203800c4c45070010f441c828800c0c403182d600d0110394441c0088501c3d60444c2030680700c0050200c0e0141400d4414900d404014003103480d0120b03c10014000c290303403a0800f0385a0b04140c2e0f00c8803804103014005510380700d2104025 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 299326825 1250 299325575 299325583
    0x60714040b0d0203331009031209030507050a030f08030a0207020603152731031d01020a08040905100b07030c03030b1f120608070609030c0b031603091704080c0a0503 73
    0x918410f1017500d4040e06030380244910400b0402501c0b0401640720408404120013aa00da407100b80d81d0354074000140d2a5080c070300e00308640d58001510489035040100003250901d90202011604060301d26901d80740c54000c00020f105072880250008004420040d034070755403000700c030300e07014051721450319040071080e0541d074106802c0c1e0400c0e200040e50700803580c52901e4483e60034036514081c1d111503180c0c0080b4403400c020007410008074000781400f10218000d85086c8140c151450007030000b0184104a6649c0884500a90003114003440d86d50740018284809540010010400462050741d1a07900381401040808100301c150082814004d0f0100c2c0c0e410001508103010f4154854180d440c513801004480c000780313020781c0480301ea442d944013044a1b030302408614010181c584561089504c1c1d458441a080f03180d078019180c080c014010081c0c4440510740b003005004e090700e80000c40c480f061815015a00d03000540a903501d038082004a03000d040045d6a1540110440b00402e1156881003050f5403 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 299328075 1250 299326825 299326891
    0x4060f18140402130e0c0301060f0302120f07060f02010b0a0e06040b1e1011030f12010f0b0702120a0f05030406030b031903110a060c02010b040501060e0102060714040b0d0203 77
    0x1120104407503609507844c582c0300c401050244001e0740e107a06a02c1c80020b00b0340e1280c0d045801316007084007041085150050b0300304e20504924000d4241e092880c10010784030156440303500148041c6100000c0410310039442000000001410380d500e40b900c503207201d49202811100d86003e5880c4c584000a24580b02810a010105440300030b0104260002440202c082d61441d101c103100030302c0e21811f9050b4080c0b001d403010038802c3c044e00d6155a440c901da140800740c1a070103000101070080052060019000484034000d8040d24040c00244290080c1460151502006408941083c804008000e0301200030001c407070300c955042c04150808010943c54011500038a10003000c050706c9540000d0107004034248125045064505030086a200c90064400d24108080140d65a60110040c0c0c505803282b540501140c0c0741040c40c911410b0004be40c5c440000d000403003402041c51020300f021034020119806416035000c0c0c0358a0b40070aa48c0e00c8043d4005850042079010060401c0704e40444140e10031075 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 299329325 1250 299328075 299328079
    0x709180f02011809050c030a060e01080613082a0c0604060903060902180403030504230d08061302040303020f071415090301021b06061302130b0904060f18140402 71
    0x3040c52580155003400e03503000c0c0540502042c03540080d5180340c0388101403140d041c94040d5640d902d024510001211025040014420204130051101c03810006010f68019a00b001c1e41c1300d800f407030341096039190090050303811032015000d208500d03050510f5020b4102c40b900c1d01c21a050f1921000c00c0040074010380c000c04d4000303600d85a04101064541c2c00001215001804040300701c840f407110010740850460b41038000c0703500d42c02480700700300544a410316600c14441e000d040c54131a060700c16071685a040780110800c6903100c04500240e030340301c03141d8000c2c1050a200715541d50790b9143c00380d02c944021440e8840c03030048902c0000e90501c035092410300c814000b030a4020000c07000344c84d10111782015050b80d070159424003510034004041050310300c4208181c0002c0801d480c002041040082203440241c007500d005000c40c0620307050405818041e1918091040d07214800c1001242c020180d03944443c20f180c50500b4000303550041c40071216001250010300b80404940d01844a030b0b50602524025 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 299330575 1250 299329325 299329343
    0x103e07020d140d120c120b0a1d15010305010608270709090b06040204030203120a0e180f07020111090d0f060501090c020d020c1c030c0b0c0d0e0c2b1202070918 70
    0xb504c00315654007e0101000c020400c0024580365901360402c10030902c2d09042010b000e00602803003a846901c0300180b40000d1806118035810400300400149020301044030740c0321141081d0004030590108035249124801c110341000e642e0321810406000000703010340702c42501d0b4007c5905070515000301d809407a0089c000f4070b000018010400200e620811000003001044801085180c1c2d41100b40b0208078181c41d80340c0c3c55030030460715018004202422036015a0b14000340310103460720000644909120482c0c0c600c0c00500f20741000b550b202c0c07218074020308492030030b0004146503103243d2001d0f140c103010383e0864910400700c180c03d80e600d00d034034807020f58030400100805803825400c0003da40128820b14029894458550f59044130b14019100401e02120110b050101030301c4602c501d0341c80301c1801d40100300c103240d140082410380d540c1d414924081e10040d801d40c841e02424040582035243c1c4040c0350b59418109000003500c40744603000d07511006061100c2c080380701120702401c1c0f003807030b420100712 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 299331825 1250 299330575 299330597
    0xe030c030c06070302030c0703030e040c08131202030909090601030b01050108091002180301020c01140c04050612040206210f0609010b0a08041103103e07020d140d120c 74
    0x2c040c2e80c00101c0c080301103102c01c100401001c0c0c024007074400218400e441d41840700145070100030075212300401081c01c022038541044032071846c4030780307880002d40c000022514006c6491822401d5200b0b290149802ca0940d1060180c031a400080d00760480c0d004103203847c0d4590300ea20045405031002ea541400a91102c0a8001180302d10740c0140010004802d01c4414106007002103070980e0072055030907400d6507451b0318100020050703181710340e88032a044585628003030400002541d1801842500c00078800600001ba0864890b003040310710850a442203060780e0203000050401c1e1001c00c0350301d0140f41302c5100200e2a0360800c001118142c500300c0100c54140106071504881c0000d004000b6113412040c2c0340c05550031f860030b000d090030700840440702080d1824140503104040140d010240c54607184d85802110101001c1504070035030058000c0c06a8580c007900004004105000c009041c0c0d210303541c50b40585400000b0801214185500d607040c044003004a9a4122605211254081050504a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 299333075 1250 299331825 299331829
    0x1806020705030619090c0b030a050105011e08040503070f0c0609080a0201050301060c05120c03120112020105030402010c0c05091602060f091b06130801020418020a0c0303091415070e030c030c 84
    0x420b04041c92481300142801243d11040c040010b603610101d6a900000284485002c8900617640501800c4c200075198401d100b9050580d203126406000410a5071000b0604010050084075080f54121640344021a030034200100302c8095442240046911210005910000403820000d400c0c1c050315158290380c80c00b2425552100703021812a02400f400c0c0c210501a81d0001c0540402e569810045031110251745d1300039141072040e00240c00d2003050010311401030780c0c0181225809603081c07901c011140300c1854076020070303141908117a51081109080012409410055110f4040598216562912158044840168240d841c0f0a4a80014200c8084403201c00c14143c00d1040c041c28240c82c02c8102d0040310019902c0d6004201c440c0d40003e42000040c0f103150485250380180071003145001c403e102c000e48110040c4e200107040c5034840c80001e0500100c9491503681a811000340c070358800e03e845000c07441c20030807140300b40840c030f81d10b0b6203600c503007400245044030794001b6001344030501d40802 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 299334325 1250 299333075 299333101
    0x7270f052b02130902220c050403080d020f0f07050607080a18030302090613030c081203070e0907030605120d2c0f031e0a05060a050609060f060f0a18060207050306 72
    0xb02c3c1084203500e403580180107032503803400040e04020b4000340d04a05162186d0400946034a4044082008000d00c018804155148110b810034040f50200603900c9140b0001e080e0940642c03c92440010b0010950b5424401701048041c0702d8241a60341c000303640c0d54000d4401c05c07034003014a05071041e07515003080000680664003d0264040041c20301e1705103444071404c20008600b030742080740c003001d101c40d00b084402070800405c0c618040c0d054510303080d80307400e02e8010400c48a88580300c1c460404840812a0540603503c50805028090441c080b0340d1080500c4507a1004ea18200000064026401041034203080c451401180d80200342401e206180308104560042004051a418003c1d0f07030202c1c0078113488075030001402c3c1d40c0e040500060140e50030040d0070010005c0180041074145001c02400356221004254860b40031135000c100e40b03220102140d9a4089e00c4049503000070b001940040c40341e007001e800054401164020100242c0f1484106d032900c0c40d0740f003280d801d54484d03004208010342880e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 299335575 1250 299334325 299334349
    0x601050a0516020604050d061406040506031b13020724060f0306052508040605090601060c02130e1b040b0d120804060b030304150f0201110307270f052b02 68
    0x108003c5c2419258000503415a40b5400115500c40d13550000ea4a04180c11101c00e41c000700450b8100400d00d0b05402180e140d43c0b0751a51408010400e142080342507851000d10500c0c81e00b200300464441001b46001c5048a00c401540840c255480d442420a00000c0c0180c2c010b03203032920040781603d45180c0c0d400000e44405000e80810b02c1c810341c9240b000150f05070010b04029000c0e621041c060400e4200601110405050300400b50011401071001c4c58100d406a42d40030381c103440b1802c0702c1a5840c03000000b000c15045105030b5000e410115094042d1034841d005030340f07000311001c0001040d040204928060142d200911341d0300d00c80780780d0321103500903180f40d40d200e40254002b0520800240c0000d08540c00b641000d0040041160158642075201c208040442d03030500003005002040d042c00c0383d807408010100000c03c468440e052030303050b508006009408000d084440c01c0d05840d9242030321000624029a8061100512522006500700741280c40c4401c2c00800e0305200d81c03041e024080f18402ca4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 299336825 1250 299335575 299335579
    0xb180f12070b0913092609030d080c12150a12120e010203041716140a03021504030b010b0403062304030309060204030515010320060d020310030506070c0b0601050a051602 75
    0x41003403000614500031280c5940c8a06c2e04440c444801e400240d44d211104041c02c03215030414000c002094500060f121020320440c100142e480c0d8840c00e2010749440780c039180c04d00190110040c090031807041003182803030500803209258001c1d180d818214040300c4005001c0c15240c840c0c01104501030203a440ca5980703c0061050745c0c5020740304d6035082c40300710090a01c1500d560102c0b5491078400d02811a20016048119111560750324500c0080c20415003404060300c10741000410b64041c0035480103e0700210ba0100c1908002e42e075941f07054010f82c05c240b009a843e03600b8022041091038220281a00070440e80303041040750348690320120002c150700d28040300c0c6298200004001b003501001420f4007200d4214110400b5811850301c01728003030701c103404050405140c0c0503003400c03035544a040d0b84203a00c0d0314000503141e95030600c0344c001e901000e600251030b80c003400007808051584188807040807070299200b4803540d00d40400450303162148110381400640280512541001c040c4400040c0c0703400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 299338075 1250 299336825 299336839
    0x60b010c020915040506060903060f060a050a03060603050606031c0503072307020a050a08030f090301090215070b010e041e0614100501080a02040501090510090b180f12070b09 77
    0x10a602040580406999500010161125800c01031600c1d005d003591101003587c0c054100341d1048086a9211000380152290741081030000d84c40d610740380a080001c040091219a011742c1c0c0c2d0500d0801011140000d9819000f140c0009815040004091543d1074041900c40c0305042c0c041d40455054101401c01c208000040c14a48525501c1c1171403003000040420059a17658614410031000030603581c4030901450806034100818100031081c1c804091340f50080c4e65a034010721000a0041a501070025031242c0e55a83c042400c01201014080591140822a80c0c0b0f1742c0310046d514401c2e030205c60050102101c0100d0380e0b400a9104070500c8803030b1061602080e1182022901c1c0d0b08498100e850000d400d6408070204119a4070141c0079400001c408401c51410707081034002800d0901702e00039a4042d481188649156074403403215000100000450780da21050521400c0d0325003150104424818000241c004a6034a0480a4030700d29000c07150092060a2030181c5000c0540c01144c0425440360f4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 299339325 1250 299338075 299338097
    0x40c0303050c011e0605030f06190902030a02060c0123040b06100314070e130b060a050708040e0a09060c02191121010c1106040c05060702040b210d02010e0a060b01 72
    0xd003502c0301218030f4440641c085030b074504000516150110b0141410a151b00270010f20150343d80d0307030260806420841030003082301080390001c07915106581070020740000000400300150305041d402110324085114000c0f080429001c110381107900d0945019103050981c0d400300e0240d02e00095401803064003410003246058060781d803180d589a04940300c0d004501448496003140c07901841013038403012141e03406c204a0341118041061401b49100740c0090100009007071090101190545005041d0388002d04100c1c41c01d15105070240041880c12aa44c0381800d000c820740a0003c625201075050211110b10840416142c14841000e1501000e401002e0008120302201c0100003d541c00705280f0004035160003107150003000d10080c1c8440c02c0c8260402c10601002990060140041701da0440b1480c0e02d91065000240041102e00c80f2154000e40c4210f10790107090b07040320144615803005003aa030000c40700c040160b0999040030f003a02c8082c3c2001c14072900180556000e0040b0690602d009000c0d48 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 299340575 1250 299339325 299339351
    0x10807150f05070f08070f020405180604111807110d030924020408121b0a02090a0e030904020c100c050a09050402132c15060406030c030902030d0f080f040c0303050c01 74
    0x1b03401904141d82c885085a0b9640540c00d190060301e810032486c00450000c82600e11007152907110291000701942d08089500005964420110305002c000c2e2056040c3d40c00d100744085e01d0940c281800034100e004a038001c282d0b00340603104001640b80c01115041d5101c2c0c040140220460509541480d81d039424000407941c11001c02c081c1070f4030406811000d81e074512401204688008908081c070265001e0b80f01034006813618411281c111841c0d20f40407841d00301405145041d402000c04a6070424404141c030490144005100c80006d17503c0d8208012105407041c0032540c52041c48824808200c1c440c10400c00d07824031b5030003801300007444c0900c405c000d5112203280c903208804540c0e0b0702e03221250031803402e14160714a030082c0d0008400b50002084134601c20201300c09002794451007040c107540c0c42d00c0d0312080d4069040a04650790041c240c0f014861100c9018111a00d2011100b00084640d03001a00018240c0c6026004e070743c101100030202d6255680455040e40311a000503815501d4058890000d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 299341825 1250 299340575 299340577
    0x12020706091202100605030a05030702060f0904090c031203050708011205071a12070306030209041104091a011e081005070c0609050c0f010806010c111203030a05010807150f05070f08 80
    0x10304207590140030903500d03145461045d200c4581100d8800c0d003011030a60000b400020448200a0381680d070a81c0720032003101455a5030240a02d0f141d0841d04004210003006181506002a03c4c803e6100142c00d0b07640d0f0100b04d08441e400c440f0382d804642000d0052003d42c4602d9500f0740c0c80c510440c00c44040544400f03442c0d108824400a906d400d00c8040b0322505843c2001406c9a03021421f484c0c100103c81c0785400280c0c264102406c081e01c2c2035166102003800b40c80726008081481d41160300410664040250180290400d102d103061510031780c501e0a940e0507d07821541d04030344080c2c00502401d20041e21002c000c100103010700b0b05000f0340500c3c810000e07080c1c0c0502d65002c1c0c050000707041420f40305810f0001560280401070f04000410081220580e04228900060b81c1c01c107514444007002c00f0041144031900f0580d1100314400403007001455929500301d0703416290b0610a032540155280401313a695161401c17140081000c0340e6a01080c070b0311420140c80703403c3c0922010f4041400c1a00c0380b03041c03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 299343075 1250 299341825 299341853
    0x90604020d0f06090b060c06011211032406030c03070e07051b0c01020d0309150c030f0f051b040f1a0409020f070203060f090c0103050c090402030f19020a1202070609 73
    0x20b00741c44070001c010002035403143c0000e642c02906c405241118103d09607844940502890358610516130020b4180600c842059100c0700014080716a9207020070048107011505120b01806107650000144203802c0205800720380c42c20144c002c204442c00c0c2101401c00d0100240207504001d418000000c002c0361418a00c0350340c1d9021fa000d0166070b10303d8070009092a004200030010726081c0034444001807112042028190711008001684088a8404a001e8004c0e1805000154200300315411501000e601c4075010b00c200ba2450000e82c0040456800c141c0950300c20b20000703101036002000403601c40c0e240c41e0300d5651400501c5180c15210421642241c2090045085458000c1010030450030104a80f607084005c0420316102890601ca07015921030340200864101078442000c54139880d10b51081c0c5d00441c0000700f007551030746402c40c040851144115200400d00381a102c1d000d004140b035101b251030003602960362043e6007024104c0c5402179400b14408666003640e032400c441c0814180900545 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 299344325 1250 299343075 299343101
    0x4020904020d1d070b030622060b040b130f140607031103070819090305070612062402100207081204030e1f0e0312040603180b0a060608070806010905090604020d 71
    0xf03d4401d0444401e45001a0354009412407035041003402802c0d59031726a11400c0c210b0901030302401d200e9448410010303004036409080b0940002c42c000c80e0051402c0e01610510905501c84036a040c0d0f1002d246d80903250310709c40c03c1078140368400c0d02c0380241007540052045a000b410f2400703001043c0c00390300346164414071095448000200c0d5100c06c1190b043c01e0f03007070a5201443d280103024116200e076034458800d0f03c59002401250900107a00d40c0940d04008000c000380229400408003400700703503842c80c1c1d00f07031030b802d0050150003000f10300a03030b280c42500e441a81011005048c1100c441141d41d003c200900140c003030082500389214107076105038000c00c0c0c0c800c0c91003d4107401d900e0300102900c80020a0a840d2007500070701c154004524004040d6400c0b03500a03d03021071020f1046100c880c1c0758802c644060500041c8030100a03110302d407604040c08941d494ad49800782540c54036811210a0f4084d0380542c00203460860400c00340c5800c003d95500050f0040c001840c0a00304281c0720308407005260640 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 299345575 1250 299344325 299344361
    0x2e0311150c030a120507140d0b060d091b12060c2f12070b150a051203040509010f05240c01141801060b0a05071a040305030f0a1a04020904020d 63
    0x809413588285410300d8040000b078140442e04004602038079074151120440140c20010820301201a06504141200c0c4c1014001c141d40362030103614403020f00003241d0103690580c0050081c1c01013000349900d0314210340c10a441c429501240c0e03903455000d0096501884c00300020045655010b000c44c20000600007078040b0101d4840c4980950036007000c20002d0250401c0b5010311040d03000c5a102014a580400b2b2662a01c1004145a00049401c9040c1d00b016400c0414000349076011540003000780150b0f9000c440303440e8070740c0c0e0300d508000b03010707885010b4107030012031050380110300d00d078410284641704500e1a5901d0803c0e00307040229084a45070b030341244410381c0c0305003409503540104076410400c1103101d000348501e5052a44580b658442c00d01d4032410084005907141c244003002c0c0c9610000301c0940e000314460300b46424003d00d590002d6860300703608400203010424140701481400c80030508c0010440c6d05010200804c8001d4201c100c030250010b80812840d1100481ca104000380c07080e8291881c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 299346825 1250 299345575 299345587
    0x30606040b0d090812240d15061715012c060d0803090a03170919030908060708090f2a0a03020418120801050d02060d0f060e2e0311150c03 61
    0x380e150709814440b02e900c92149080ba000f031503100c54141c0d5004a402441ca000d8415a00400c0401049c0960210030040b400320011313841800c0c0810f00f2100180542031519071a602c60350901032800a60005500b0000d41c10362038003c0d40c03854014240e000c40020240761021440ea00d8000d0554811103410429802055002c002c00d43c1040182030420b8240c60b040866103882000c55580d200700d068000c240e010400240d4081500c2046c0d03031005450b0343e905990660401242c007a010a00a403180c7c80300d80141110303000c01140001f0561030040216140b0031680c10800c0c04100c96900207000703140c2100c0c0110001c4050b0f01e95004e0085030403042c00d001c4100703841e80e0501d2403141817010002400c000014004100d40e5403051214104907804440450707840f0340c41509180241943c4102e0003440341070800002e10041601c45e0b192203032400d100aa1303090900e0910141085920100c42c044003030b6015024808656110a0b10085c8203000c0c0000c0c044c00210444841560440065034a2720b031700000e42 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 299348075 1250 299346825 299346841
    0x1e09101505031009050c0403060905010510140102070b0c0c0a2405040b0301050402250b07020c0303040308041206060e0c0a03060902031303120209040603050601031403030606040b0d090812 83
    0x3012016036100d191560460a0405500c5401c440920904142070b44a8022031480c07100c140848005641c000402c02c42504103140c0300b40030b07000c221070040b080d0440300000280c800c04208203c220150507409009014204961401c7c0c035000042d0800e61481a680b10480c50b40300c1d08461005004070300100310403d403d22146840300c8100050130300410105210810002c43c000c025617041d9202250056210920407103070707001200c0e1004030200414064901c2c1e0041c0302040155502620440e400d50b00904954420b06959115a10004109600c200000c2080500310440c040c1032a11030310010800039a5181c40c4c00c0052005da600900d40c2c00000340d00761301c49070503108030002008000c1081d4254600181800c00d8000300e00c0014041c0480c4840c4240d00c0344d49941181c1012030000e1003081490345034140303581e884d0000d02089911095607400001029400419641318120040240b8513050602480702541c0c1c001c49084a019034030ba0394800d00081e007000192400300300c00f070104040b03403800c01d007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 299349325 1250 299348075 299348099
    0x219050f07050f030703030e0105210f0105191205070b0a08010e01121106030402011e050711030a020d2402030109050a0f0c050901051c02030c0a0914030703021e0910 73
    0x1204a100f100c150000d41020344021400008507505030401015424481c801a58544507a00c0f5441182002e000180554012134070f41074040d1282c581d14907013603a02c1d10140140c0b184000064507181d0400c50701080121105082060308920031019900455035440400b05030741c01010351100442c000300c0042c40b555050940c3c070340c01041c021500d8041c05840b901c400607800c0103042d5060080310008005425039004254001c0c42c045110f2400c0b11900e0608001001074005d04070859160101d5240ca145074500001c00240c0030740c006000604000442c1d5a00812402e4019a41d5144007991407408401c1850300c0950b00030444140301184529080700303800700300c61454107100e204070310f8a10084407d0b913000c41034401c640c1c03080c20095542c0100c8920320401103849040e481e100c86c000000c120f800c2e034108001e003080c0b40c5031380c94070540c032520f459903030703215007002035071641c069121a00801c05494080f041c040024450003c003000320000300d01080065204031008440e810508004101c0144110 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 299350575 1250 299349325 299349329
    0x22061e02121b030a1a100306061202040f14010c080304030306030c05012d02030f2d0c060c0304060204030506070c05060106140304020f04110403030e030c010813030305070219050f07 80
    0x3803404000801c2c00004122a0301001e041142459510100855040f43c1031900d41c03003046004200d080100100c1c2d8009020300081c0c01500001501584110b010460340e00a03034040c1d0f101450620591410724141c84003515401c40c3d0541002003640c1e000c001305e04070400840c0214041d036030101d0400d06604002c200c00f651a400300703040140103002d5210120400c1c0c290120414924034903501e226501d0030032807860290900034542e400e0001100c05290080c1c3c039116125052007409401c002c250240d5104c1c5500407130f900204a40c0004c0f00180c00303407a0405c0150b1b1702c64820240142400d8071b81d19400d107001c0085a27003401043c024132880081c84020080d16004081c5071030640840c51005460707200d80d00002d00000e00805030317010b0103440f5a4843c1c0180155000d07503c0704640f5581c0e00d05008112040d0441c48038040d00441044a145500c40c00c01d8601c10020240c0940c1446003a64085004000046c240710441c040c5111801e4046101620146900e00460041c404021385072040780c01c0445503 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 299351825 1250 299350575 299350591
    0x907050a050d0213090312060b1914120c071203140f06030a0305070203011d0d03060b040506090f040915020711041a090c0405061b0f0622061e0212 65
    0x42d000040c01a82c4e8001e103880d501d04842804149a5a50310741950425940b1080d00c0b400b50400502080d00d110180140c84091901c0f0f0740520b19440100d010b4407000b01c18403800111007410051807a01d44132004d50581c2101c1c125805a140c0800c513210540117002c2c85ca15500040e0721040381c1000154140f00003900300f00340c80c031038600f64103055000130398030025090010b00380000030a01c1019980c017940000304140003062549440e01681042c1d54030b90541040301400309140c0325000c40d0070419070040d2815204090161031428030446d0400030940040c0340302c1941300380c9410a0200242c00c030032402200250722600961240e05614284140e45086056640100d10301001c14481c0100700340c01d108522001d030b405000300d4481d823249907610b108580205810200010b2000003803009091102c119403298026268501481450a030301e4070420307a0032908a155400185032031414050300c42020a10540300014020b01e0004440054000f11014200702e50b80407440a010032101e05030701d584103002c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 299353075 1250 299351825 299351839
    0x3080402012c0f0f03030408070e0f0106170c070c06031a0603040807030804080705010c0806040e06090d11030405090114040c05070503070f020f060309010905071e030b0601020111030907050a05 85
    0xa000100701c0c11003110b000500c03501c0388080b620b24644800c440c40742184405829641d03102e48492145580d80390911501c0e8404400d82c0004400141080105040c0c40342640c03981040349400d2031544801501400300d503a1034608101000001d82c0c24040300340100901e4a0108290160000c4203282c10300320880d10340120810000c01001800c103004a032501503041c2040c0303400307480d40e05104071305000f41e1b40010207543c6080c0b5a03061141e0030618281c4a0741040314140f202c0010a0f14050b2103403019540c44040d58081600d1058090007500d01003101d00303440b0210f03402d00f655500068541c29003a0f1240081d50b60142605806003400e02a082c10708040c0d00340103203807003099076840d81c3e03a20820300081d005440883e005011561007640c1101c10060041807207840c3e08041d8507160007024106011519881a000b000441c8642d11404a620104190020a5a501d551520f0003000310041c110307811075580e040010b044001c0c80000e14040c038650300c01403600c3d60400042c00642e00040d00400d200d900 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 299354325 1250 299353075 299353127
    0x90d0c0f120503030f040c0f030606091523060d14160203040605030403030902030c0619090509010b1b07091503060b0a0f0306020a0c20010806060a080c0c190308040201 74
    0x24008102ca41140368030a042140b5511404c142c44080c100e90496012325068010000901038aa080340040e564600010010200c50342c01224081d549881103803484a2001446080400701c401e03c0486004040c00c43d07864000e4059420003212100c009211060913104288400d000d07040804581c03103046800190315050500364050068080184000e040603101e4103443c0c11502c05108007100c030345001d0404c0c3c0d211040303a05c2104500c91000342e000d0010b20910000907051500b02181030403a140107000340e10304060220104a141121203110809205038480000d440403d4452002900b002c510baa800307d900f9480c00d4003e550310080034504c2401142000e01420190341c80c090100ca0380080d00690b42d0070301c40815a00e010fa80c82001c0c01c201100a07a000004540b200c149c010351800341d0b80c240150341e4104c10404c65000d20350607500003411b0303500010801c134070050080ca0841440d000f2940406a07180c055000d21130300000482c0065910010f120440d6000004a0040c50328840f402200352 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 299355575 1250 299354325 299354333
    0x7030809060a02010912051b1f0908040807060504030b0a0605010210090201110604060626031204031e02010903090e06031515060315011e05031605090d0c0f12 70
    0x8000c14150511038580010b51580d1603000f5031110741c0e10b65020000740c031000c02000000d0a590000b543c0300b04c4400300da50021054000c00302c1c000345800200c0c03029001c0d840b1a512102c004080f107450803074100204020200d4000b00800070080140085d90301e00e95100e055140180b00303d4009009000060304010081c0416a0040340440c000c07800c0140000740e560080c00102c50030180e01c4880029400b411040c4400d00903d0b402501c1992601004210000c4106119401d44900c108480400f5041840b80840c00c501078107101e038229001f40741024941c113218070040e6090401c0840000540c0d035900f01c2c1d1042603000b0303001c10001e11100c074052103103260000100b900d5880c000c4100300511600303800602d01e0705910b010200c0380a0007030030480d140e2402c007a00b50040703032065140c50b021a1920100040d051450445003406000681e10350342941c5917020b0349050103000391200c1c4c080c401c05009150850711155074a84540d4080c048141e04580340075948850340d01e1a0700100120380310040d000000c1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 299356825 1250 299355575 299355577
    0x603010e0f0a021005190908011b0c060203060a080f0109050c0901030f03031d0313050405060603130803040312090f0605071103040e060a051519051206040209030c0909010c090503070308 82
    0x7507406440c000010160f03403004170780074861a1040e80c01c1a03440c4184030003e81d4001224815180c119000300706960601424031145044200500009200d80600c40001541c5070040d40d000b440c003401d404400c503180c1c00030034103001450100c040703c0c1c0e550700e020703405000080040144000080d01c00341910750450b102c60604950440e0040c06050b150034001d59802542e0003a000d2000a10003030360303103c41541803038007400100352003400d1145040c40c0c0800c0003131410400701c0b17006881040c0360b6900541b042c2e840c8021a040100300790103001d0042c0c0e450300042c001d070080c1310485d849202e101111250078a0300300c0c02c40e84050050000c21060190014404000008a506680368052a002c0c9503584400082c16030f0150b41256420640d100d0b1405030a0180c50007400c01d2001000110020482aa508640600801c031b998600c1000410208407181000d41c01015071031b030041d040e00c120090800c04698100c170291740d0610031360364901d812190154026a0200a05800c034080e20f1400c0c91901c419000e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 299358075 1250 299356825 299356843
    0x151103060a0e090c030619200913020d060306061e05090606090a0b0406080405070b09010f0e042003010504110c0303011707121109090309010c060209010905180603010e0f 75
    0x3004030300a02081c5840e104100d0400f0b0404e00508403101c61420b20546840181030904050b4014106445054514a00ca1288000103241641c0906140508007045604050020f000c009150300b0400d10321095000e00940340074500030200452014a4205802c2c20208191100d02030300c492030341d05109560720094510340024040754015101c4418000244905503e5441070202010024000401c19000011b0512a501840954040d903682c2c55911100b48a4001c1075400101b01d41e415500460081d1a40d2044440142000482c0265204046902d4100100c6152030144c080300422a610782030017061151500040700d542000c0c0b08049450750781c001030040c0304200d106e52035003104a56040100d0301c02000e51746221401441e8508154450b0001142c0c0326000b45550800501c481c00000122900e100d01030390f0388014020103480740c100a40250302c1c07190400ca8461030004040d90307581c4480c4070010060b0385841c5c0718100392081500b1141c6800f600c196a03000035072001240d001c0400c684403 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 299359325 1250 299358075 299358089
    0xc0e01150e220204181b020f0a03121806151401140c0a0b0408030411060910140f040603021309060503030f030a09080301060c0506062b020409020d151103060a 70
    0x55030088580840282c0204e802011080d50540c691986070411500030302c1030948100d6420f002c02e03524986c101d80f10b1024000210352a40046004000a4400c50030406010040200002c800410075407104c2030300741d030002c19580c01da15001801030720346080200d2002042c217000c000b4046564540040c00704030031b404400c00f1440b0042100300d1141c8050144606840c3e006480030050301d402d140c0002160816a801d9505a803070305a1000582800811a82220001440c86907010303074000c07040f80c0c10750f41d00e43d210423880703001e00144540391704080141016001c90b440141c0ca90382d40c5441c4000c001c0903903002c040d449007000340030000c1c0c0d1800700454411851014500740d80b6920300d4564009049880c02c002c2002500200021782da561100811320002e224905884203074941504014298000644014004004103854116190900800341c40c0900c00b8201081442d07a907000550309a070a050103442d81e40065940c1407400e101803150001502e4031380510350130f500300701011450244203801402 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 299360575 1250 299359325 299359369
    0x504030b04120f0302311508180625090b0a03020406030506030115031515030b0901180b01050d1a0f0603060901060e2410030e0d02010204140603040c030c0e01150e 72
    0x70700c841008849070000b920310700507030700501d82d040c0740700a1402ca000c58041051070182c040d92704024001082180c06001180315403254400680350070108901884004014400348940008131800e002c0c01078150710400e52001a281e52408401401362200242400e110307900d0302d041202a0404280305409980d0040e19585003c110148904018502c8400b04140280c100800004101d00b02d500700f4400c126150080c0551441000304800c0844070340e000910180700c0310014010741c14409071003903c00d801030707400b0031030080440b108000c3d180341501c0040101c4030070300c00c0280750b05040000356000303200741000700502e42c0b8040c0440071101e409004c0888020403019031800d0709080b050f454807681b078000c102c0341c44c0218014001d401400141e00710010b90146d0350b840484180107100356400c441b0000f5503a0b14600c41002001781d541d00c02403044034040f03945007011000c11050186030b000390243c0c0c6003030101c039410300310080041c0508214075002c20103400018006c54982200c0b1000c2448160301d52 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 299361825 1250 299360575 299360647
    0x9030503072306091c050702130c050405040e0309030c10020a060c11010f1e02040302030a0809180708100b04180903020111070b0612010e15070504030b04120f0302 72
    0x20446203541d002e20502d03200340030034801c0c114070128150401440e80d011000c2e480140307880590340b0b4001d810020f13602440505513441c40010031f07004038112440c1d5180c810f1403e0703250400542101d142030044421980045000202400c0812101c803032100300b1580c0c44080f004480b0001e640d08120400100074540301c0f07250090719409070f00c8810900b141180284090006e05002000800c8241404090f03120028148050343c8518401c903400d998000d000741c01499050340303860106507c01d0b4680e42c1c20401030402c0c182c0c00380000c81c1440c005e400070b0340c0300502c40c00c041c0d019034203415042d0032510720480704210030801914001c05851741c2000d583c102103104203150070141d0040c40d003000810000e240c002048010018803c01052160300304482d1500341035070003410316003220a042ea4100c41d66000c0f405880d129200714101d80d501241d5032038282e1074562a0364903003000c080140c904580780c0c00c800130b0748840d80c0e8210120a0004009260840c00c180407009084182142d0140400c0070352113802c89 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 299363075 1250 299361825 299361863
    0x24040f0615081909020316080d14040602030a14040e090604170f030609060102070b04090e100630060204230111061b120903030115080108280b0a0b030c010903050307 73
    0x500c0030710801d409201400d569234403500c4d150007046402900103401c500791110803030511020303241614240e60045040c4a9548000e446004104090100f01d00052000240b607100d029403061144082c40081d00f61420203103000c00b42c0840c141c020158480050091100c3c035098003040d2a401202100c2d0456503490b01c1c40181c0c00c011b030a40206000940024010a030008a41c02c003501810351501114a03000701600c600b012500c1c2070040d640c540645903448800c0c001e04580403800e01a0000040400e20107a0352444100c2c0d02075844846c640401c41c072100c5000030005102c15134503400307003040c04140342d8007a503598994000605000e21040d021008014a80641003a1000303950030511080383c44c145450010340d81d030001d124180d962002207080d10900340c46500028100ca40100041c101000c030441580b010006804001c02c5480b0040e01103008034101400f5503016140802c0c001425122220500d42071041c86050941400140f000810004100104a034102600706c00001c2c0ca580007664 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 299364325 1250 299363075 299363083
    0x304020d02060904050702010204140315150a0f0e01150315030201050a02010f05010906080c0a080c131b080f01050303040501080a020315030a0302070503060a0507050324040f06150819090203 84
    0x1203082d804c60300d84001c01407001e40540c0180f0a840800c0b5480d0f0403003640508040d03941500d1201b0003400356416002c074103000d20118001d8007041c4010002280305444105610441241e5030000f0511400f0a0040025011f5100d6103410141c40780b07400d000080f94600c0802c810502840024100b110000740c0b01c0c0c07041d100f90300c200d220100a6205002d80e5035103908070710181c055406014001c0c001c0b83c10b018428940000358900311011800034000c4000c00408000321160900702450240351911030500310400504083c0110205907110040d9508049003116101401604614000d51041205004c0390ba041542c00b40c0c800400b5a026033f07255a00460b42c0160280384224582601c22884000101500428040280c80c0183c0c1128600e030b82d1050b1180030780e0410745001c0081203042021629807040d0303c130b59038484031684c44a104c040d02014081400c44034480c1c0003c0c00256100130a002d82c8e550308444042480b0315150415150610711805c3c026070f0580c4000c031040680c1e03101c02d8401c546040c4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 299365575 1250 299364325 299364337
    0x912050c0f150f03061806011b020109030f05010c0210060b0412140d020f010e01050f06090a090c0b090f06070506070c05100203010b0706141614040503101e0504080304020d0206 78
    0x2082c05500c60350304420288440e002a640c0d18800c9001c00c0003911078440344000c1c0c0d03100d482e0581d5500708658014070400c0031410703401c800340c0c10015650808008a00720015685c9502d1054000082c0580c844130000c0c205481d018814030070900b0071104100901d0610f01792000d65100c0e441960141d00c04d4502488055165a411421030040c06905840e458021455090041c2000003d200855a142c13009017281d0080300d06106c40d440321400304d41c440c2400320113a40d200b41007800c006029116600c55401d11601644507094010700014816814200040000f8501c9400d4030603908161045c0d4a0b07644a02006100b0030410010a91071018800200081c0060200a1200315902d584a14248929611003d4107950107414800c4403540c002214031114403481e05030340e510041c40814842103501c1010083c0031000040140030108141c0d03002c2c80701da480d900103194005169910344020041e8550858008a000b600d40010003020412607011a07a00660459200c542c4401c24070000f90b184c000c40b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 299366825 1250 299365575 299365609
    0x18010b0a0e130b030d0c050d210501090b03150c03071412041b050d170a05040305060f1f06020a110a0e0411031c140901020a0b0403030501060912050c0f 67
    0x18205180b100c28a9510000341e40805905481c3c509070102d000340d030300c04110384e0018403640c81001c030300f184240301d01302c041840d10700c2010454600c10142012800d550007a0400a030b0385988880d080040d207002c20400401040c4100c5031841440c090800a5042c0001003600301800703100301c0003500c0003070000100c070403c43c030140c8600c40d02d050a061201c03000325228400c0e10000c44030b08001c81c1c40d250054100b2409036108595410b10400c526030300030680c002d05086000d0107001d010210002c0c000340181c4d44174668040700492545003c0c52860105400c1c640801d000002810088c8803295005c40c1a103071194000310514444d01d0704201040124499a2000c11107200020070700080101800d4003a0480d1001c0381100c0b142e9099940240701d544951a03103c0203e104050310f0300a10540038090100c1140500540d000b443c2540c94515903510219001c80000c2d98400061082c0c64008265a010301541014200380c45c0c441d40d1920743d6246002c410714418481c0801041f1681d03102c01c030781a0310143d1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 299368075 1250 299366825 299366839
    0x60708030901020406020d05040b0d090809030f030c01050610080f0c04030c06030f060e060d02040f0b1005030f0a06030c1e090c1101050c070f021c0204090b011418010b0a0e 76
    0x110326038140c002d41260003045d0040c0142540c42082034800d100b620706035803c6a02240ca00740010460070300400a2840c2180d68520600554402c1d5600744034900394035090030041d59445441440b407030308441000b07006521503070394285a40b2220350701c1031904c0c0d84034079909185032198070307503102080700c2e8012030b03100074007102030b42c01c011810b264142c002481030170134107800b070200503280c000891113241c04681f2183c028040f07064840c05498a1f0700310401c22020103000290352541e00b0007250300c0c21101c104c42c80c0814000030a00280000c0601c19980c03040694604004d40360944c0e0390f129203501203101d1521000101600801c0ea0b00c0c03560b42c000000c010aa0781007000c2c418040001c0c101203840755020215518040c0080c084074040c0d01120417840c1d201080c1c0f2445441a420004582e42000c4956191400584880016200c0d841000096405a2200e2a103580751103095050030303030017090f0340e800781c110341d040586510742084405040d101c0e888441074035502007010440ea502c4c01000040d40c0303c10 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 299369325 1250 299368075 299368081
    0x2a01080a0b06033103050f0d060305030708030f0a05010e0f0411030a0c0510021b011b080f04030605010501050a02121e030408070b010b04080a110a05091f05100801120206070803 78
    0x2010380150648004d820304602e0802111102d142d07101e090440000d400700d902005450304401182000b001807440000300051029100d8480c0c0b440c68101801c100c0d10304100200340400503c5000302c0320b61042c80302e40c0034482907041500000c5242d5010786007407040400e00012404100040c40d0341422448090b0454121020504083c0b144402c07901c18240590015000c5034002d41c4007003170407400381c1103140c011781428441703a00458034209170400307a060b00000381c3d40d40000900484002c01e402c51003d070203d81c03100e003141020300444070183d0005060040c10031441000ba500825112007803c070150780144c494940781c00f01c060200f10b116403800c404030004100010019040050000320b030150b012401280e880b2254080503110328001c0c0d617002e83c011401d5000058a48a44a01e09000a03081c0c8030495540e50200300d0a84040c0c8070380c5544940307a000f054280c189a203010b4000c080403a04420200c03007500010b09400c006001e105221a00b4007805801e54039424121035032554040c820b139a83c2d107 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 299370575 1250 299369325 299369341
    0x30c0d050a031e060e15010e10090f060207050a2c0603030d0c020a0515040203030d020c0c100f0806030102043005120403050d091802030907080316052a01080a0b0603 73
    0x29050007002c5001c202c003c00705483d0503442e131b03004080700c0042e194004522206400c000c41e02603840000c8042081d02d01020602c0400d605580004040070307001001a2802e0070100100d006164000181100142340d01d031071a05100e000108810581d0f0000d10140d0700d03080007017821441006841c0203540d0515200f9601e03240d0000310042c03050302801c15154000c20282c0701100c104400d4502941c19841407104103410046a801006860074490071200145090800b14003000d03d0002140d02069961500300601500948003e50004c0210021450705d030a01882d03800c4007030a140e0911111540c0c400340a2a81200c01010704282d810400b15000001041c601d01183d0f8894042143d11b4096503480300002401445191f06496214202e8840c4684180e0504029040100460400d212f007103400590400180b0040c9030405840c54410302600090504510f46900c42c0940d0565000001c260b070603da951070404c1c1005442440c0c102c42d5919100c0e0300c040a131850700030f80341c0d0121002081c0304c214 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 299371825 1250 299370575 299370581
    0x1b060a09030b01150809010e0303010e0709030b04032715030902040e0102131503060501050f0702030c0a170c011d01030902010215010902040510021c141b060a0b03030c0d050a031e 79
    0x20f8049030764034022659460301503400e8408e070305000c1815510900c010b1001030807000100341d000c2510700c4d180c8051981c1740c96090281078140c400341c0c041655405981c2360203010000d040807003030800d4445400c1624002040e14800201c0c422802015a0b404514085540e1904000c0b507403401100295202c0d02da041d401820680c592055052644414407072400481c00380c01010129841612294140b0303018082100c1a58000841240e140c050a09140c85941c2d48402c81009486030101014000610070310803403900f00d400f0324940c1841400c1c0c045c1140c0986012618044510a18002c03070a5419840183d24000740d03120040d100d40c1c851800420061a6640501308564080760b00c01040000105d00380d03111851982084202000b5802c528001c0d8010000925010a0085a180f40c510426808501c9001d13581b200700194110800b44030024140d805141c01000045025603c0d01508400c695a81d54004110005106000c40d6002c20740c0d02950002260114038440ea01c400300344107240c0001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 299373075 1250 299371825 299371859
    0x40b010225031b091b080406090206190e12010917130e010603020702040606030b181005030d02010e210a030c0e06071a01300809180403111b060a09030b01 68
    0x140c0341c17500c806590790ba0700344114078600045540b00c80000307848584940d0701034980340038203981000f410040000805a580390b920018a026980c1149105c1da982c200010000e60180c9003200b07a05016009003c82c07030030300041030300404030842c4c140c1d90300041d40c111049400f10350100d0b40c5102030000001301240c168008111040c42110308001541d2140030a404540030010b850742c008076450f90b10400e2008a89020342c0102c0c6040344622150381e1440001d2800c02e02d640c007080141d443d02801c81944208100e0030804004441c0e0042001000d003d40114501550419004240e00e035803508c008680914000030300a100604142d5948815003800340c0300655403e00d01564101180c0002a07988220540381c00708a000040c1d560102c14039400d4844080480d0010b44506c03008021050440d030718096044e00c4080400c0d0400ca862a00e4100501841d450070140c40380c07a0058a1010b18200641c14407004066085030384a84807005081e08844020032500000e120001ca8800401c001c07500382d0007400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 299374325 1250 299373075 299373089
    0x6040f0618050718152a1a010506070213090210031409010e0c040b0f0901030f03021207020303121f06021b0a0803040605090114070809010e040b010225031b 69
    0xc80da403a244002c450050100c0e1006001c44070f8058140002000030b00c1081c0b09166514008164400342e1032008000c2ca0f2542048024462500b10301b0100f0003400c12841c3c0c5040c3d4500310244540c50600490580c2c800c0b510000e04c5502d40c02c40c5621014010382c001d480264000d0200c9503200e030740c550050000c00568490501c00719415000074950f550502505424604120141c03c0e0001082d0602015041782a40c156029030105281811515200c1107940258060501040c5010003030602906200d281d4005041800c0104451009600c3c0013003218084640004001040e07a20500c007008580600c881c0c4500c90101035030f00048041e400038195100d017080381070071002c00038800100210380c440e922882816400c18801081000d01a501410720000d060500151542c1c000e110980f040e4803101d01100e134a00040341c014000e59000c0c4071f40c60003800c00c3d0760411400300180000f0b035590100000d14155000d000030558000707818414050700a60303010005407800303036041e80c4109840c01d423409101 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 299375575 1250 299374325 299374331
    0x9050a060609090201091802120a091707110f0a0308030405010605040c020a0c0312021e1605060c03030f0406150e011703120f0619090209091005011706040f0618 71
    0x45a03000081c4070f48103010394140c5070b1000c40b620f8214181c1c0a594a008101c00079030b800e00410300603490200005203d0745207400700045006041c58090b140c1103cbd0b6103c1c80c00c1030702c01d00062000070110100005003c0088514a103c1c0f1028130028440342c184d5040140025004020300040000540008059401c00c031424044c01807032544c1203030b5540400c00050b0a403040803030100003003400c800000024000d01c3c4155002c2035000d400c10400c166501c48660f00030341c0300701040007100c070a54040b80c0140ca0110340e45c919021034071419503503d0101402d5000700302d00c0400031504102d241c0d800748070090f2200568802199880042e540c0c1e03800309109140003403041802e000800d4030084111035401800000d001401d48944400143d1000024400c0e030700562508001074010b03280c25018001401c02000150f43c504005041c003e1800002c0c00e130f0003a1408000707017070040c0c2e0703004071803032051910381445c014250f9240300004001d0407010b07140c0b01550786414004225002e0003074551130b001e0030a040c24 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 299376825 1250 299375575 299375579
    0x60f02121513050402030a020613030b071b060b130e010b030f030a0f1d033708030109020a0302090402030103080304051608150915010803040f0614031b0403050109050a0606 76
    0x428034210088007940d03804204103980c5504151107501c07254000c0d00107400c4440e1603042e68040342c2a5130003e0344006404032550003c01c1049100c0c144650702190038070b000f41164240800d810b00c4406480c10040ca482d449030400c1803145c41d0b01d061000d0741c1c541032074148a4210681602402050b0603072500c0d02a0044840454842500004130741c441556a82e807011072841003a001c03a070780c0c402c0c451700f9481e03000e40007410542130381d08100103068454003201502c201d40d0045507095026640a01c18520000841210004180302405490441c0c0807030a0240c1e0710301880100301c0c024400c58904680c4588040008002d00c00306c1c40280d4400d0344075008507024403107000580c2000d120940301d1405070b80c0c400602c10502000c1080d45603007055074002210500c424200301381c0300c00e130001d1b0080c2a6076880458200800140c040c040c400030f00150520811181c0310103c00c800511004001c40c41c2c01c10260440924112050100c0c1e0085821034020027030404280b90554a41c0303181392007a580c1d107040c4140 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 299378075 1250 299376825 299376841
    0x1a010306120209101503061d06090c0a030f1811180720030705010c0e010f02070e151806041d0a03080402030316030207030210030b0109170a060f0212 66
    0x40c00140e803860340a80d014001d403a4204180108003c05001aa403c48a000100e805501c400c0500c40d41490718046145030a2410000552141070001f40d8100e50380020b000c10713031300c6560185420501d500f14040d9904800340c42035015200002107005101d01d01044c040040e9071448000c18a1881541c03a11201d02e418010000c2c0c0300495003078401e0107201a404032308a14001c0c10740959160440898110380c3e00c00c4204142036800502c8107072030f50707510748044200c00c550000c9011a26035090900d2048a030341800025a80c103a94003440d04000b209001042c040466200720340c8410000a0003040c0c00c400b502901580c164003542c140e401503003804460700440c2030300702120b2144030800005013000f0748107860480e200392016100346c1e05070008100400c40403641c42c110003c0c1d58020380080600e1891481404040b0782103032289000c1519040241c2d46507039100c1641401c542111468400c032901c0c181540742003443c4800e0043c2481c1c03038450401c00e00c007060340140c245500d1500c407240c0c9503502e82c90f03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 299379325 1250 299378075 299378081
    0x10605032d0102070203190f020405041101030e0127080910270501270b1b0c0a0305070501050703140d0606020c0907021e0a020a120507080a080306012706031a0103 72
    0x8006d41c950410070b0414100000601a118024061314a04214000035000300b03044031b005590507208192050342a500d81d5805000340c900610b41c0300000c0122821110b0780c01210000302403c10001121007030760b4802d00c040d50081d1180300b07000410a048503c811200078040f08648516a0110229480c902d24920209101c21044800c1a15032500080c64200103007100c00034819181c0080003001004507128020102610382100342018071541c032620890b2592070000b0503843c5a1041084060a10000340086a1070302110700c00c0c02d0030350b00e4003010302d402d40700300e9891082819140008680d1000581440e080b41007181d013140c01360342e0201d14050900817042d50440d411405a0320541d40465911081030004019000042c16509440000d6001489a00c9503074010b24110849040341410b10500307103d00d00041c108000204200c41585d52440e009010041580e07050200c00e80c2862005905894a6080880e0344404001c3c071035280c0102500811540200c1c025030143d48a5aa00b04e5010744 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 299380575 1250 299379325 299379337
    0x30b070c0b0109020c0307060f0b13060f030204020705030c150415050907050603180f01020426060705070c050d05060a0509070501080a11041a0705120703170702010605032d0102 78
    0x61280718103a09080a0f0b01c065400103043c942141710030803503500804d04e01d10a05428105a4001140d00c3d002c400410801044200540589520300f003800c02031a00c1d1981da010070ae982c15100981c07242484c1c20030904602400403405003500480c042c2440c100035040000e841030744281100442c000005600e002200d008441e00c0501d0340c8403590030f06c99850164045c55000f800c00d80126041003070800002d042c0001104002e005a40124090046407080420034045144141039642240c060708078080d1303501005001c000034085c00084840a2220b540450006028003802020f014504c07880d20f00c0c4c0d1039808441c14070030189481c0108800303120104445c0c0c11a032050352200041e8460040440080c002640c0007821078a00f084005883d03c107a200100d0200e0848014030348039a40ea041042c1444448110744540f00001c001c07000009401c40ea841c01c4c3d103422026240d003550350b00841a801845a604415418800c40c10850034010240380180d01200e00d000080b0301400741120030074282d000d08 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 299381825 1250 299380575 299380583
    0x201032304060e07050a0f0f05010f0c03030c0302120103030c1a0601141606050c0a0201150308030f19241505092b03090608060d03080c131a04030b070c 67
    0x103a004100402d0880d00501e801c000420140d500e495034a41c001010702006500c144a452182e03201044640c0c04c2c4054603000b41400e0030718001c1e03002071040051401c0e8501c040201030555806501e40824825410b0ba004640012054070302540c40e818060000d500d410000c90703021074580b09200c00e02c0e05040c0e4141c094181030b1900c0030408085101b030552034000560340d003421a020b4810b50041240390103400d0080c1c910920f030995402c0301980c0207080d04d107003c100c40b509a00038070f010800900c61404803a8840240c40700082151105400b60312000c0403c5000b4110700d0800040d20900d000840d0000c0f0180036000c041c0080719030700d4a81c01525045030008001040e4140886c074001e0414003001103009003c07c03090045100c0d1450000c12110100d032080e000202c0c0383c0d03418407905411082942d000f407000c031030280911147d0b0341c00801a590003010510b040d0070201c2c580503a030342a060740b807010784012517000c0c15840315a840f080c196001440140e80101d9400085404e8030300451102c0305950300 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 299383075 1250 299381825 299381891
    0x5040e0c25020f01030905072303151008030c0303060103090602071704090e010b06030103021002030c120d0c1b0201140d05041506050a0e0601200a030315080d020a060c02031b010603020103 83
    0x600750041203004454184103902c62711000c0c00c40d407180e60a100c561030000403040d05c0c6405003428081030700e01e09880c0d08446066841005010280c85001040c1c99000c10f0901c0c001c900c00c40c4034500070011740502c88004102800d41900d045e03001c110100a003003642c2001c0c00070440c1e030903040301003402e0383c841035192a0481c03070400050002d41040080d41c0030007001030040300c2c5442d54244e0300500e08108080000841038000c54513004400d21401003540304000b602c1c204034403400b6082c07218206450500000d0500c90710070001d003d24a0309000361030944032400c00402032854541009100d80b900c01e00c0c07110805180001c0880d8074a42600c1110599400c00e80b541c10b20342c6ca850054441e00854207051440c4000c50405001a940400110002038440c0e07601140200311042e840b12040c0c1260441c41e6075400c001d415400c866400214401d001e50881804545568652800d03804c40c810006031044000040e00c00114054054010004a0307100307a8042000014080104880c1c0c66119070000200304 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 299384325 1250 299383075 299383079
    0xf010c03182411070f110d020f01180b0406081008150109090206040f140a090b0f1509040c20010b06090f0f0301052e03020105040e0c25020f0103090507 67
    0x41448002c03020030030760071000201440d9581d681000c80c2c000f498201c803011303042d40075501006030740041a50404002d442040c41074809a000a8000b014a103065041203214005000c0440c0640101c030300600c4400760403540c0f6a100e0500501400003101c40c0020340c100c5c40000100b0101c0012032604000c9280401d41069003400c0d822805885030050680c0e20990602001c1910001801c1240042200c80740464035068040244048110f451f48541d00c518038044410b003154403103491400d80c10908072980e4942220140c52001c26004100103680c106183c42e52151655800543c5c0c00202008020010300c1e40600180c61401d8980e09002550018400d04c0103032070a003403068131007a0300c8400074059402025200c0119007124000c03034020161402d14180003006404815000c4a144000600c0095031400e540011b08140300328840c01c107000041000244c141d4104d0401d1780d851503a803071040c05082d00b082074140103403418000b080e882002040300b01c007041d60291281401d0244d0220282a80038 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 299385575 1250 299384325 299384363
    0x10b030403090e01090c03140f060402131a030417090f040b04021918080601051804030216090204060e030c0a05060a14160605060907020304120201050405030f010c0318 74
    0xa00040e00450a01491a501180b100d030079003c0c01e8060076080e880010380700c1202e84014103580248082401014441c030a0050314000016001d40c07016003901c0250751004200703420a0600140e92000d800c1c050300c1d0300040407140480b4011406140180418001d800c80344aa103c1e81340300e1490159402142003207980322505090708413889103c0010001400c2201350b0303006070202e8a06100150016100040348400c014001d006036014000c440014501581132501003200d0341410011400440b4030000042c3c20588200403644c3e00340d80407124603400c3d81c0d603004524003a40080c0104004221607078030812580c1000180c0c550004801031808500501e803030207100c801c0d0300c14200103003003207040340624650203800c0f00140180900c040d69510203040c6801e28104581019100510619600050120883e0b0000548040d00c0d0040c807141c3d0400c10030710050302d5500c120f03408150580100404c0300c1388400103510040c4e841005840074003034118240e020741301d50800008001d108800c0e075004602da031 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 299386825 1250 299385575 299385577
    0xc020601140d062f0c07150908030d0b030f0c060d02031312110d08040807020409171c0b09282d14130b0903071a01090c08100e072f07080312010b 64
    0xc001c02d08110285681b1600c420b400e6901a003a0b103c0c041340c07030b22200cd1450900b040280203004505018003240c0d0070b50000110144102081c10b4540c2c0d07008030214048005d20784103e026181d1018900440c0001800003410f0450711090790340d603901803100829403040c021500780344501e50001c841031410302513908100c01480c521105580c2045c40c6440b24049114103070050003000400c44008408801e5150900d040da04403405072400b036a424009d11040c100c0c401e2060007031081030820101e40307180000c3c8840060200035109003003145400d00c81914480c07500240b40d0401c82280040c08030511071031200307995407010744a03981c40b5824415a1000310340c1070215141c00c000034070146c0303140400c15120703003112507c00c80c1c0c03480c0d84944820041118125510506546a40f503041410092400780103004c9421030303920508880007002000900720b248203420100e041e56121441d800e510301d0302c0d03502800201e80b040050302203229011011441d24000030a5844405d960320303044400341c1c240840c03c082 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 299388075 1250 299386825 299386859
    0x20313060228020c1201020f09011202070803040c080c0a06020318011707020607020607091208090301020d11040524030103060e0f010e0c010f030c020601140d062f0c07 74
    0x1020200100e1501a00020b0303003002a01c0e0499004241402c0d0f03140400038481042a0510600c2c3c2c0f040101440b00401b83d81a01c02c071610900b84a00c2840c071250300b1780080d2141d4240200074940c004104010492802c002c0e60a407403d6500f240da6400d0b5003000d0044201c0e642c0502030242e4001d0065800100140000c2c91040d0010716003d0800c088221010651b82415180c1170003582041c8100f02e031141d4104005a4070070b800e860300d01c40c040e2038590310407185881d100d400f400d00100007404100305d40b0309404032030a14940e00d2003008420700b040314484080c2c000c1c0c0a05071185049104415a815060128420350302c14003019038556441d507075412008000c01c00d01e1100c80e004080421100d248284034041e0640f41080251850f442013500040c1941d000c85610820315150907031800c0300950008034181505c0c03000006072011446500000d00d1100b6002008012500b0710351040c003080801c8402550010420510300c0d9094085019000c01380510007800d0203a900c00c3d9000c00c1aa4001300c0311240d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 299389325 1250 299388075 299388097
    0x501110a020618060304050102090108250822030c020a0504090b0c0309070b071505070507030c030e0109080d180506091003020f070f0f030905060f04050f030123010e09010203130602 80
    0x400400800f000c60a650000c88040e24165404507028025580252003168000c500003100c1c0341c5010011401950040c030702c0e03495000c0212290006410004522030b13918006104040c10310b40d03100510340140700c1e501e042c508074000c1260703800006003402c00d8040c1b00c0d8890381c482d858580b16074418000c41101c1d00300901c80b00240c42080000154624103a005016803030080000540209141240c2000d1310005040d8004201c1c0c00c10000003c280c2c01054841c2059051400b80c005d1031403580100d82d030b04540c2d0024a124004c5092002d0b5031a080002580a1082d00b9690920250b540b404c00039030780904644540c01039000d46100000a03c03940c01022181c7d1000c1c046410b20002d6121900031002421003110401c00c0c0c101440d00703140c2c0140e03400c3c4c000e02c001c4801515004110844030300b0341c02a440703800d000e600c8042d004080e668080d0000404415406801c0010b0640009600101c0c030080c411345150004400200f8051401030080b42d22a55240d64008186240741c1e451900a51044d18440 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 299390575 1250 299389325 299389357
    0x71b030804170606010207181802090106050403060e06090d0f1412040605090c012a06050a1409011103040f03180f14010e0d020907020709020a180501110a0206 70
    0x11000942036005840908640c007201c41c0468040821680b030250003602150555009130010071000140300700800811143c07410109102c500b90500c038491a807445c400035803181681c0004181036900402400c200d900840c01485443c0744011019220007080d039081c601500b000c65950540c0b07010301c10000c4803c055280004070151038105c000701a400c002048105e07a95048140400c2c0040c5004807500f04404002800c940144217002030407251020200540910310909104012040c9444401c00d0340e42108003030115240a48165008243c15001c03a41350b03401080128003003500500c11a1010f54002000910f5922036407164901c1c0c03840031100320304102072030b460603d1028800102000400600d5507190707040f420554000340a288000303103641040750074552034807942c0e54005982120740e01580c451446441c0c8000813030a094603a0000380c1c80070b000140070300380140c1c017000c99221194001034500b076141d283d40044507075421901c3c4520095100744400c8000d0300c0c0250040010324140b245071 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 299391825 1250 299390575 299390579
    0x1608040804170304170312010e0c0d14061002070f03031d041a100e0906040f14150f0409080915130806040606050a05060703031517060612070b071b 65
    0xb4400e480014150304440e0404074081088801003441581540c000c040a0b500300400c0c180c485c4a5003a05109009400030700001166881006400b1100362a009250a11650390346075004c0340482c2060b2341d050b006501c0d2200050800344040340150540b076066484108562a544040740c00103951208000c0491540d0a01d42c3c03260340300c1c0f00d0b2001c20500c11041c0c1c2e103400004c00810a900420136410010312140c5c0006000d06c2c0c0c0c911481590080d411213000070b0300848014550020030360502101c14201446042c8000e9407001070a0b41d0000400f1540741003010490f105002c00d4580403807008002c22821700c5142c0c0e05240c008007000c0e107619040211400d186890003401042085035011803110f03000720040c8000d010440c0540380203400241c402030b59a515010104034284030703218001d03080603551051020880c41d8100020014400102c4071601e2203220304101da180c2000b5500035101d081500c83c22b2a03000001301d0716908540c06800518100075250315100c40c1c030604a1045e00000010b0703400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 299393075 1250 299391825 299391839
    0xa0f0c0c0b0a0807020c0a1208180a030521090d0b090a05031b06060301200f0f040b0301081b01020d05090112050a020903071d010909140a0302030d0f051608040804 72
    0x908100c90b0650b5a00c2d1050911403c00303802c0a0110b45041d0144040d810203100e000d021041562041d0361040942c1d540341400200c0c19128103c403010307580c0c0028a200c000041c4940010303800c0001760030300303c811a00c0710030a600580d203118440c8042c2d0408020b010160224094011650740141050141c580310046543c82c6800c40c7d0001c025050403c400170340c585138400c82000003607031044064000f0003880c0b0a480d41c01000001c81042407502400c0011110b43c0b083c1400d007075404107003c0b04000c9499a445022100e4240c0090144445601c1110b80c1d5512840c1e01340710140c1c01007010b0700900400419680300711401d80c0420380007818803807044074070310400f001032040901c10007046400603201c1011400301810700f031072070b4001b81c000d020b84d400d1450441c1803200380781d0444030356200004040f4002e10308680300c0044410b280c60b01e0700546403c0014160007200401c2d405519803001c1100c5c5110310f034080111881a02c0d0400031070f02c141401d221040c020703524240c1060241400600302683c0d0f541c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 299394325 1250 299393075 299393077
    0xa0b070c0b0c07030c1205030106030e06040b0f0603120418050c2701051b060105031207080a0f030f020c0a031107140d020109171f0203060906100306181b050a0f0c0c0b 74
    0x40404001071f0000010400184c0c144140702c84081240060017241c107080e00d460305c0b820b40c046c0081c1e40060108001c22aa9541084008003160700c16882c962504da880010f0b08a100b03180809600640c14580015071494052003201c042250345503130000c22140141c01c501e03010301003808040c18040c00b00809000d841d629088038801d950b01000a016941c10001407504003445084d60f0030007101c081c80004001500302050b1084006a450000d08195013058120041c01013014001042840001c0c00d04841002003035880403680640c588840307801c02011075940d0341e107207441100201602e04206c19413500d031660060072854014504101c10948500d6400c90300d010302c20f803039440c03a406840d525108003444039143c03031030802d4902d0450441c54181e01164010200400c02481001030350003241599000c3d61204018201c003454460a00c42c0210f29100101038010801c0099035107024404c420030712440c2203500551881c0d5a640d03103803c2240701612000d41c800c1084403188605000070910340c00b664 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 299395575 1250 299394325 299394353
    0x201020c151803010507050406031a0d060c0f0906020309010507230703060e06040b0127020301060203090f1005041e0305030f090f01020f06012d080a0b070c0b0c07030c 74
    0x140401e80d035004001000300c0c00d8600880464000d9060034100402aa0080e05a40c101c0e071032414081011001e8000e0f504032072149586160744400807102e01024846694031020302924503072139141c4c034801d06c0c3c3c6042e60161032600c180070069008114100695218501800c0347c107100e00751800c0307000c82200040700b18030030061ba03902c002e0317210b81010400c1c40503034002c050380110740c10701410007418075407a00800c81405004e0b904407408400b006e04150107010344a80d40b0f0f9015503104640380d5840c1d4100075201c2c3c0c05012881d20420782c0d5084590030b80760410000d2405e04058540528040c500300140031210350002c0000a00b00498030f0000c040741e024001004c4007010510390b280d890345502c04024143c502041105d0440d40f103003c03c031079503200024017141516400c044400807a840380841e81103440b4511190070343d9680301900014a1701c000108443c401e8071030150700c86d099580a004803207503074590202500d80f444843c040f403000318134a0000c010690003450070304600c9003942c03207500005e4514 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 299396825 1250 299395575 299395609
    0x409060b1c02030603280605150f010302040b0d150305010207060207060609020a020a1106160b04050d0f05071e06090309090f0204060e04021b0f030c01050c0a1b0201020c 75
    0x203120345000207808805000030003041e000c41c11401c1c108003107641c9140e204540e4180403052030300c02d0300007101440c00b490070640c4880180841c1ca42940c01d03c0342070405604150040e0000c00918040d50b0182c026103040e10340100c079041c00e008450007010041c2c40701030030b0b21104500140c80480460710030300040c1201401060003682c0c03042c091920304102c0360164800e402092051001800203030780030818211050b0806600820702c00750cc0001803003442402c07400d400350180322100208210010020a2045000341d05440c40e41c9100b05c0c0079204100c0aa000388001001006024000388013060804040e050740d52101031051150355441c411035071408000c1c0c01040c11800c0c00c0191040074000c10406c3d1200b00030035801e0070b00d0010060007001c3c103014024072954012940810b41c20a440702c0159000d412000c444c454006181096140ea1001c072a031031055081c54000b88005030b22004860640000703564101c0d07000c1020b01440901290802c0c104e0440c0079100d0f0440e150340c5c030380904c005c42c0104 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 299398075 1250 299396825 299396827
    0xc130608010806010b0c030a03050c1306030b04140103030804080c010915020d06061d040b0d0b1609050301050c0d0509070503060907090b090f04080a0c1e1a09060a110409060b 77
    0x41040c02c07890188160300c0301d01031000400c80880314000103c25601d0040751810045010703254a41070300304034002c924403030540203090440002c031a60316400c6018401c1054408000a50105104154411007408090b000ca0114404103001440080040401108c00000002c5014440c1c4d20703451984201d00d42f01d1081c58021441c0329480d006840390030000d0a41e0300303108c1100060041c50000341d0510901c503a02c40d070b07503a0120b90002d442d44988150040e9206c04600c4080c600300e4168245d0303180030f00740d400002d0200c10021900d82014490f590081c00d55000150906e0b507a84200c0001d448010700d80705582c05241e8000896403002c101c40341c00f0307041c0c03903000d010000d09007078488045586400050b4403c1407940180310011013481000782d00260040b1070503030789440f810320a890110145c3c100500d404600c503050107502c004400484019407140c011b069905000c0c42e031641080708280c0b094081078009001095110035103070b218002d800d184110941c02c0959959840048450552005006441c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 299399325 1250 299398075 299398079
    0x603060e070c0b13060f110a080c180d020102010b031b12160b070311070603021206011706010e040605091801060501110c0f0d0b0901060e01060c050c090c13060801 72
    0x49000080e55000300d035072400000400281e01c1d0b80c01c0c2d001014101480e81c480c4402400188003050f080801c1850680d80188850301014803015600c0e1300c5111000300140600001c50b0140880c0340495200508070307a00c01c480716007c1c0301008040051807a0490543d960782800603201c0d2002e0201110b8210408400351100c0307596010f021000c101766442c0d03059070300024400400c070f8150f9180407003a40e002c0c1101c1d5846940c0362400303441d06810100c0c1a82c2c248a01d1400084143d8181c0080480b40420404400300b500d60000560f050469841a0a12048018002525544200b04040004c0301c0241f0100b45d065071600403e900a00950b104080c140f4003800c0301009070350034002d04000705000c0c80d116035000c0d102100d190311030b80780c1190350384075101216541c14255a0880c68214860300404041100c0c07d000d83c03140c4c02000644100c0405d403094000010b41d041c001d50000c1919034001e80a4420241c41100304030745440020507102600b1401c0c000c01002e5644512520040c066648495040e54 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 299400575 1250 299399325 299399339
    0x131a0601270b07080c03130906150e040e0102041503051608190903051c0207060e060c04030b132102060c1e1b011803034b020301060306 60
    0x114151401d040c0c5140d00c112402401101c01210116250302d1a81519401c082c90112110322a6100c40d04403444041042102900c4046c0600d0849100810412500d40d03503802c00c5009515200300e4802103044c10310210103a040c15000003241000ca035000614082c8c0b90b146410701005510b1a2400281e95141040402c603410980c0b0440300c0c01c1030034042014500140f065005550701000852003d803100644410540200207581180000d0ba41e05041c1a1400c2c0406c8002c2d0040701099515905041103600c00c02008200304c1c2c082e4940f40364007440e1504540703d80045180141c103c0100c454500200004039004002209503061000c424008018900c01c000340b5199010b04000c6401074100003c86641d0b0000c94680240055090b51548032441d00c94216900840071450790b00315401e003100103440c8025060100e0900f07100351000c110100603001c0c0810320030b001803040044001e0640c20038090440c40400e1120300050400e01c0c00c04005401262000e98000f81d00070b0001c00d44542c800e00100c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 299401825 1250 299400575 299400587
    0x90f091a0103020307030212071a0309251401020715091d090c010815120f010f020915130b04030803060f010201020304150c05070204060b040f120b0f131a0601 70
    0x4180103480100365410b42d00000e45030700c00d511000344200c2e80e1440030041500b06011090040415190140e000080501490850ba20441d04446c1e03a00407000c40c0114407c0d811a005c54091064007460030301270038801b040042c40c1c81060018190310030340d40000b600b9822000820024151695084d0069103419100c40600316120319218069000c8000c10180d84c038000b07650780401400f441c091140e40c80d041d094901088035001119000b00e1a00c001c50f8201e003001a0005c91480d030b01c0000c00c07100b0a111000c0c0102c1c00341c2c00280e60720844443d07101102c41f00700c4002e4130baa00c5403a4441c01342c01d6641c1c0504081c0303038410340c01243c48890204c20400701d440d02c907802c500c40081c280002d52030352502d41d0b1203d0303181c443c1c114054405566000e48030708452080003507039192036001e00108412501e0b42c4801040303800c1485a029001d815000100e01d14951080c05865140d11640450080d11404175030760340c8050052909000c9460485c0071004507090100080e43d2410130aa80354003418084001025 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 299403075 1250 299401825 299401853
    0xd0e0d0809030a030f02090603040506062704020909010b0a06020a111c02090a0e010f050603060601110307030e0f1806150f070b041b0806160f050d15090f09 69
    0x2440034140401c00c0150000c011111002d0041c03a0001d818104e0340c00001c000c0c0190303112660808000301c100010080002107513402104121042030020840180500f034004544595807442a441008100142081082203400181a200201c1d1100c000741c0072680102d200d50003d00141e1004000d442442005000300c40002003c4e11807400c4149010380c1012405080071009000f50b90000002da040e2103142e010f0000400702400921080c21100d080f10301504042c3d9006100c0d000c0d0a010038620b6001d1032400807890061406103041980f00d88040e600c403682c0e0000207820011030080040560b85402c00d03090422056003c0c0e103140d080800c14049440790f40c0040103459001040072030420180c84c010b854445510800048884c0c0e218940007999403288003000140f80c0b510070000c180040c01040c81c620902841d15283c0b0200910170b811581041c079142280c0c08200c0030030544d48800c1103604640c108001c4000740141e143d82d00c0078074000311030310783d00040320301c5a540c21903a0800a100c580d02007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 299404325 1250 299403075 299403077
    0x40e0c090d08070201020f0601120c0801020711011b080a030504060f0507050d1509020d02030106111b0d050c090a020c070614030106051b1902011103120f06030109080d0e0d 76
    0x81800300315004038400700700320940601000d00100c0c3c240b046a10030070440ca00134282d407054600a5a594030310b0300803015095000c44220000c548045103c140501c01d4072505908103020307100103030381e0400550b0383c20003400d46200c115a20052201c00310750140000c05101100d030354001a9890907040130b03812a840d64494000d100e0600080c8a072031988442510342340d40055000040980c3e5903560080d04224130750100345130030300104954030401c80c00c0c3c0c040c5040311300719215130103001d41c0002610f886401a4880c4294507817030500100d01c0c0d08001d044920038601c103208540501100400003030101200f142e80e103040d260005603440c0b40c02c50a0000c24018985814805a16940708403645002e000c14000c500c1001030110f8140310307402651200c502d03100c1020b010354080342122054254008440c070020790214422a00300502803034000129100340c0b24582007040c45499400d80030007500c0c0040c02c03107903142d0f40b1443d91070045803070301e40107202d61031213440f00087e2090f0400429082042080c0c100d4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 299405575 1250 299404325 299404327
    0x602031905070e130203091501030f020a0602190b0411130e010b0a05060418090f0b0106090609080c0904020102010b120f1005041a1009020406180b0f040b0c0a0f0503040e0c 76
    0x2107003511070a210307003411801040301507100d558804102340703447c03010038401c0c0d20403040000010038041c1c1010a010380a000360703842d8403103945400050b0781e60342400040511030070039508010041a0300c2c0f09400e4010744034142181d100c80955001036090321841f4090060140e1b03400d80b4140524091080a90385842503c5400d001031802c40010554042d502c40c01944042445440c0c0c52425242d00111080b41d1102503403606044500b080030300d01c0320900405001c148454800f0401c1c6005a903e50b084900010040a44440040034880240c0010f40102d041d076407500112f4099a45980f0080781d003200000003400d540300e00350041da01d030110159186181e51318160900001c210301407820040c00300d40900070f580725124144082c00e805404d0740300c481c0f1140701083c0441d4043d03202881d90700b00310b0900c1001c0301d000c0e00d40c07102070b001e0b12580f2050368800070200000c02042c01070002a1215044920640300d40321043c0d102c5088201c084901140c070303900700040c140300c41c0e80301400a50704080054192 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 299406825 1250 299405575 299405597
    0x220b040b031e0a0203160e0c09060d0903030605120a06060e06010c171c0f05160503071413081509010501030309350706020f0c0a0608040f060203190507 67
    0x719840d8180505030311039210814124880c910810031582180c603601400315024840c0c0c00c40c0320224481c4600850000c222014049050369100c0c0099807688a00180850301c4d000e0341d041c0c41170003010085801c609060325004d001480b66a030b0030380c200030044200d000c0d000c7c0300c15a1034003d085815640000411120490070321005991107641445070325485900c0c00d030b0b18202d125100c403060180c0b24070110403a40145580000f0f6995030001002a0104401440191900c1002c0c10000d680e06650000003007060000601e07c3e44550040724001d40c035445501c0c80e1402006d212070040c0130365000f2400701d0b400ba200c0b480e080050320100540c03144801000b00503a50559400170b00d0a0000c3c0320780070602c0700c5a1002d441c0074240c031219402c0c0c03d0545145038000a1040c241c2a1280014880c0b1005405002482507400401091002c455030004200136034090800000f65980800903005407941090344000100041103440118040c2680e00540040700c48550840c0341a0307600206418100005c010321 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 299408075 1250 299406825 299406829
    0xe011505090f0c13030605040f03080c0309100c09031a0105010810030b07050706020c250602070303050d05040807020909031201050a180902030f1902090916090911220b040b 76
    0x2515800003807043c0300980d1a5001c07059880404150703000071342014034090500040182c00c030359084100b4441c1c0c90340f0710720741c2d05d02d140d40100c1d010403101d000181d00a8510030300040c0196006000d901810f050910b880f646030348824047c0c03400010114452803103e40107005a40e0400c800329800580c46452481442c21559071810440b0098240e00030b100012412008000c3c0e03d80590f600542d4041c00c0f1240d11182e031107441c007160722607101040d14150184e00800d041d480841c07035405490b05034031002d20341f100c1c9082d04002030000a1040c2c4421f0307418050b84006a07281c040c005c1c014800d82e402181c4464010a100358403c506902c0144186401407007001013400402400180d0607001d00700044a0900c2d0021030701f4690f26100c6022607004035411401000d403034404195005000340c501813140c0e6a01c0103841d56aa001e40c0ea0581000f4841000300030044c0960420f0788503d204504050400c00ba600101c0c1c4000311400301c0340f444035801e040d00192015103124418080800312818444170b554400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 299409325 1250 299408075 299408101
    0x3080405120f07080c0a021c0b0114030304030b090a06020c03040807080d0801030807060b04020a0203181008040b04060f05070504080f0105310f111806010504180f0e01150509 77
    0x382c003c09404c008610589000c809100b4059071903009022044414083c5022214114102c2812108800c03030600208030941090005625a0300c083c00031841c003411138460504e410b100074a102050300c1a0f01c8100d0001d134150000d0412490503030300a545403424407040c58105201c42c1c02c02006584545c5000c0d8850f9401010f0b00c0c1100d40100b81c00345d80d415581469006880008166900035000089100c405903001005000340d030180c001c403001c021481002c00603001c141400c450001000200030902160812000c0d6401c03511400c400200842d0280c0f400b002d0342c03001c603200800710700c002c64204515581800034103100034200008100c00c1c9414164000c1480d00402420b4580c0d4a9803000310b42041019140030032560009001144c10f02c052070044109010b0a40d100d000b0162402040700c0c21800310b500a00503841612407a0178181800c04040d00b45001c000480c0e207041c0c0b68500102124007503c545400381400d80004a0108103000e040800140f25600050240207002c1c00c0041c0051505 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 299410575 1250 299409325 299409337
    0x70c0618090e0a0210020709060504050405101e050406140601020102030403090e0601090503030f03042a060302090612040b0603160e1503031c0e010b0901060e040905071203080405120f 81
    0x10500042008454030741e00c0c6410f0a1801c025001a174200202e11080c1d000590130080f034501c09001c1c4001e83d00c0350305100549005850042007507102c9075034061440c03451707004020050000c50f06041c1851039901d400f0240d4800355410303984c03070340e8508035451414080f0400d00c1d8030070f100707000030740c5142001d94004101d411544118240c180914022401580c800c1c80c8400003080018212501c3c0c0c0031607070518000754000c4e502103a518034640503501c600d860f40d00141c0c140005080c036005201f4604070080d80a035020807003450303202c1802c10803040c4203512085103038001c50203002d0308800351070040141071074a0011b42c0c2060440c8030314202088803010407088598403e4807002103000e895003410100f8075500480107041040c1108139058420100a41c0c050795034031100400038025240d0342818400d03508001c0c000e41c0300181012440c14200d0074590002c101240c4104200c402e0b40359942c1e410100c0c142140c60407400100e000c01031200340310082207521054009405010724000075085032203940e02c291 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 299411825 1250 299410575 299410589
    0x10020702010e04111e19020d080109230903030403021623030f0106080a0312061202041a09180105060307050d02131b0c1a100b0d0209120102070c0618 66
    0x54201d02c0036040480054130400012994140f1509045000000840d0022141c019001c1b203028440c03040c851000680ba004440140c940449913420b042c601c60181010f0490700b0011808460000307030b2101d800641034480e41a11024503140d003000d01c0c009007411a04c3e04004103200d09504240b299100351070f04480660890640241d0254035500400d0620301c0a5007120718a520700080020200700118082903224480c2e07942c01e200d01c2c13140b02c0c01d01c21905c450181c0c1c540807544d8030014005040c150302058101031081d80c1e82d0803907240b24000a401c0f100446860381c20104044441c0e0320407a003401034030b40000d400c40c007070030303a0314108008682c50a8203910040d210f01c0507500d180f6110103071503008400e010002c001400c6030b5446920094000304031603500311641c421030804442107c1e14056014050070500b241c0d541c8840c642046580d0907044a40c1030503a444c2d081007040c00c3c81e641e41e00d900b44034403010000942c03112414104102d5101c400d6010b4070078000502200a91035a0b40b40b000c0d401d941007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 299413075 1250 299411825 299411831
    0x503012009100c0b070f08070315091a0d0c140a080c01030b060d060e04030f0e0109140f0301150e0f040503030c1e0c060f0106050a0905281710020702010e04 69
    0x20390b403c403400d07096500c0142c20010000c00303014a83e5030005060180795115114105c060700c403044c085040f680b080203400c09612405c030082c010303106035800074145203601c00c45090304c450b2400c00107580110040021108481e42600401c001040c0030950041c040048411500042c07600584079160b0320848013082c101550782140500c160b46407001e48150420500d8100075036602c0300d50740b440c01c5405403000e901180d180c072501003d8920070805030540c0d070410b035030751045646040b843c4c0001c0209042e21944c800b82003000310350700d0b480074400ca000680448020300101450040322800d40b1402605101e036070640c6404000c003089000003180d81140d00c40300802c4e503130810250700d0700c502c59a2040380d62045100180c150107032007000403150b0240c094408101340a980c0c1d08030035a021b11901001d240843c145540420240c0341c50b5008807090b0020410080d0303405920654a01e204a2980043e00b50300c142058030102d20b40d081002080d845030003030086141c90380640003c0e02d1501006003103803045132 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 299414325 1250 299413075 299413099
    0xc0901090b040305010e0105060a08191713031101030506030325080a0f02010c0206010501020703022b08180105181e041109030111030f07050315030d090503012009 72
    0x4414040c60340240301800200b500c0301d407286005800b0345070003855050a50309000200e4010b141c50900b06c030480d401c3c0002802a80070f0001c088100c0f949541065803480e1011904001d02e5600c0c20061030030b951507180d46010f4600f10314003240000d00c00003869040610b40000c00010f500d0020881d005240c2d884404015000700b801d0800b044210302c48010102d0300c0100c0e07030750360311900819411224107154000744140e61500108a954001c240b040b41c0c0140c2c01241c0810140c10a8500088107000c915a1030300c500e151000c16441c103100b1460704980c41d29001032a1000f051581c4190100d0180901c2d1a62074281e40200c0e00302000c2f001c491852180100090f420b0006d42c0e81120b00c0c100b904d001e0010701000d200c40030402c4c82c541003403078854065402c0c080f0a17440302601c9400c413441041c0b1994580c0c041c1c2c03980f46c0102d880d038200400f010202a04074142402e0303580c04000d40c420001a0ba03070741c8600719041500341030a440505900e2607000d0b21083c42d01410141030303016144051400c1e103512102e08 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 299415575 1250 299414325 299414327
    0x705060c03040c08010c0c0b0a090308190207020405070905100203131a0c2a010525021504030f030e0d0c1514030a0504060501050102031303060b130c210e03030c0901 73
    0x1d0b0b641d0340301031019846c11008507072850f0400700f5440c044d401000d10340943d03624140d02c401510a07001000340040c0c10400001c03521003040300071182003144000d00609000c5c1584c0428202d500507144000841e0400e00d0411241c5400c0c6454000e01800f84065410506011402c1c00180c409000740c0d5845200c0202801e81441070a0a0320003501d000c4048034001e005088080e841c044000f055506071540e4070040c115103500801c220f81c0715290100d614442d003202c020400000f1030303201c00101d0f0b021340f08800c20504105d40394084c0002d14041e03041071002e11590b19002e441111031500040c046c80c030302600340e000726800e5103d40e4129032048010050030000c180d03084880c41144155001d00340d8001c0148040824aa400300344118800c030303801c225690f22000107995170f00400c011040b0a00783c000d001d10002da080c2d04281529078024149101200c2c0c018044001d84201c180d5400005800c0341048011091a11109542060035034007000010103413a1119102c1c4001000e5040200d00011210016 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 299416825 1250 299415575 299415593
    0x30f030a1409131d010e160b07140607050910090503031605070f08030d0605061204290a0b01021b030d0813020415080106090b0a15020a150e0f030705060c0304 70
    0x1401c0c074040800c0301e00001214003080300100e0413002c020790f01c2d18160000800c400101141012503800183e901c4601c0c1001300080b80c1d00c56102129013500c019040c7c2c1040c10b040040e14041c03002c1d070312926140d660740002d00115001d00d06070a0100318103803204000b2528048120b0782c518840003223540b010800c500380b062034030586500c40a02404000000240942c0200c00340444103842641841415074501c02c01c641070286d4041300038102c581b68041000505006401c2c0200c80d62688048044203004001110b0420103c8071041807030344540401d20701c0c0d82e041c0072280026044001241030700c24080c0209a8a40b6400c01e09801d201001010036010310703803040190907c9500400603c0001c0c0c04044207174500500e803042c0700c0190309050703001c0b81000084c040c0e1504140302620000489103082c0f04080144e2080070101c0030f6019280d00c10300480c3c80050b1040742102c0000c40850482038900721289000d0070000d0140340c0d50424003043c4001140810303c141c01c10b000d4500c1d241c6a80707550501ca811 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 299418075 1250 299416825 299416849
    0x2120703020907091d010f05010f0314011d0f240a0f030c1d04110603060d212d030504020a080f0c0109050d0c0b0a0311040f05030f030a1409 62
    0x44450b4880420003419070180c2d902d002e84402d02600e00e0b40c9010701149828017036081c0140518202e10381010300582d4461004000c45110f103240100d400041d040c0c1d82e080d603030340c00e8015202102c0b04200500400c81041c6400340c00c003911000400c2d02d4a4052030b000e214407240d0b032881407099440c07640c10035656220888840540100700c07040c0320303499803442c0a295010541c851641801d042041a08066541d1684c00b4881c54102d0711400c80301503c1000c02c503550340020500c0358421f82030194440850055003131021384400c890100c000300b800703116016009454040e000f00c2d040889410f0388207600340501d10001851041c0c1808220383e1150f00c0003030140a0a50840d2200d44117210564040780c40c001802001c0072801c0e2200c1019a496030180302e035443c00410040c203000c090300c80802002c15030030010021f01c070203031a0014000c840b505140d200d0342e00a51000420540480e428007040c83c080c0500c41c141c58104000b180341c502003c0c80074040700120000150300403c0400c00401580759900c2071301c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 299419325 1250 299418075 299418079
    0x40603050106142812150f0f0f02091c0201050906070b010f05060702061c060b13080c060c121e22050301050114060f0f03100315090305070212070302 66
    0x400240c442d01e4102890b58100d071242d21510503403074150080d0055184c2c00300d040403160841d0909600706034880300c8a14a080307049403074140345420304100446a00c14100060020f070b00200307039070710401504400d817521903044508440c03041000181d1650b80d00d09110605245001c0e2400c010041c2c00180d60034001c10340c500750401130004181041040000c03c150507544481c10301100280c94605009541c044c0000003900680c0c10000c1003811000350b0010310140910010110b001520f50005d1003483d04891225024581070711020300c65500140410040d01c0c00645080e41064902c4099564540c0003a0901400c180300049440481d04101031a036800d580011403181c0d103000039845000340310240c1c10080300c1180c41d0280401c40d45418010a8100c0d04426001400305412a00b00810b03640300d43c1000c1c40f100b4003041003214050307250000c0c512411000300b80b61000da00c0c40c10a2214221321102c0200854581351513000040e0700003042c0c552080d0183d54400c080702000322103e240171f0007908065 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 299420575 1250 299419325 299419331
    0x3030705030f0310091808130f15030e010213051002250305060906040503180f0907030b010906030c14090613030b180c030c28140f01170c03060406030501 68
    0x121100c1c0700400150300804c2608a40300c245940e5810302002c454003028507a0100e00001002c0020a014402504a4404120404481d16510803010803020b04c2c507840306c02003d9954038980d00d095054400c425852003083c009500d880e4400c00c2200c41da4496008452107148003294030101075100b04152100d5641c040e0080c40007040071100750b8101300c610300c802caa40c1d10403007000600503907020482d0350146500c00c1c021418002000c68401180c0101d44100e5041805a55164000d5482c05400c0c0d0065005480008905410b400010110798043c0c1013403050600388580d200f45581d211030500040c0e04030b80082501d40c3e1845002503503600c600035100d925401081004000c0c8407581c01c0990042c03008242c05000c1c40350041089444004082d000c0354550801d1294086d00d08004004c1c09070564800030501e088004e80541d2010513405801828098000d041c0d43c0580303007400c482255a84d002401c101201c05112010b11015210040030041002c0001c03000c00c0f120303241c0c0c2d00000b01955003c3c3c024 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 299421825 1250 299420575 299420587
    0x20d1202070b03070309060b0f010909270b0a050903030f0403120b120705010306061b080a030b030d0206010303090b2703010f0204030807061a0312030402010924030606110c0409020303070503 84
    0x1c5c0070b08040c51040e55030a1a20407840303824504411034041c11241a150018001d02c0c0004040051807003825010807020320245c035003d1403418440d9850001c5c8105d0302e613556800d24a103082d08480000340b501000358400c00c18020070900e1002d0351940030b607052429400d881c5030440e6800180c02014000fa400034801d0344141c0d000240031074624107552081e41c007080740369602c02048850b4980307000102c45008000b074420010454400040c259034055081c08a01e103d0700344046864803060914907001604004014020035030700814140c02428a03043d07080c2415483c41c0565920714004020402c0350302d00340c00d00d0440d51002e42140f05921410407085484965030300f00b98000e54000320088800c1c80ca410103900404d0f00d29411603049040190080c44000030149a05000b40c0c4081c0059061100c10480050ac24140e0b0b040001010441c003036a40c1e90f10a90300f4003405844071a0000700c1807080c580c0308202c40400018450740440d801b04e0300840e034440140082415071040c8000070713102f40400541 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 299423075 1250 299421825 299421827
    0xc090903071b060509040b0d0222061a030708132f0402040807030f1a0106050c10060501080712021312030207090204062118150e01050103020d1202070b0307 69
    0x600030340303409811030007104180b070006940220307158015240401d01c02d000401040c02d10303910451641c0300240000341c0038490703600061a41182ea456002000a1030101186541c2c0c59014140080c8844241043c0c503001600241c401d50000500308000c00103040d0000c3e05480711403010607003241d00710342b184807881d010044070b0741050b04041440718402e1681d034654000703041034400c0700c0464a641014040b460700319901da00c8204a242c0007654000d161404e511411518003007180d0003051281c41c0d940c0c0d142d10788803a0906154080b1032450241c0e1034a98200270f0f590b000310600398410f03218907001c84490b00d0321102034024003c0c0e205054000d840aa0081000d819072100d0b0300c202e50094088034a02030707807410300a00741d00c1240110705c005001c000c8106075001e40c910340d1003c2e0110041c80400c2c0d203072010190a00c00e64030074500341c0c0d0025003420344002d5080103110304800900d07060000d1020b98155004980d0340c0290080082c110502064414001c501c01c3c081c2c04050410703054690303941c0c108410 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 299424325 1250 299423075 299423077
    0xc2a0312051b1c1514030c090703110f0f040f0506031e0612011517060403020c040207080408060a050a0f0b0102030f030a0615050a0201111603030b03120403060515010e0108040809030c090903 84
    0x5420080c14060301c90015500e400101f5414815005043c010705a880e500c044003e003418510044c0e0b6407001744620a90381140c0c50190000350220403050340c80391319219030103003180c3c0203900081c0125810428040300205c9640744503c0d045464603204e041e901c494001c10052a04031002c2e1495520f46403d9214080c05091814102c0e0030f17102480002d920409100358603400c0070b0b076004000da03100d1510400d0314245a0081c00c41640956581400e144d0383d4030f000b40c1800c50480c0c00d0440d10b80d58900300b1103040020300c1814180044014100040004200045e54070303c500321140500365004800254042415041500506040750240401c3c205110001d0825000310034548055400d1102e44d408601c41c2c00250340d002c3c05021b1011410260030345041e40103041c0d0549194250003411042404a201c0d240100011881030b0000920351a040c00300300d0300c4404400c11281000405214000260f90014610f504207400c040311a55400d50700740020b141074000b59840303030403101c6141009080e0ac4044 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 299425575 1250 299424325 299424329
    0x3090f02040e0c042a05090a09090302030708040605031801021801230c0601030b0a02090f0909070e0903040501121808162108061f030c2a0312051b1c15 67
    0x1030342001c0c001d007040900380c41d14000c0c01c84403500108e031180c0030400b40d1216001f0124103400307401a2403a01100d0f48410803940c0c02500f00001049000081c0459450825402528185d00070021030601820001c161101c0400380301990410510031400c070800455101c680ca626410b0180309580c40e604040a9501c640c0240b000707039170080307084000a10704a074600031141100d00c01030210000b412007604018618002800b038548a118240000c0741c142c040c0e445c464000c0301c1000040d603d4500d40000140506034031920350710b529050000141880c140c0c400515080c60388003003d40d0f101d4425440030007003e1202d45c0040c0070110070307510503140104c0f034070319000b00c400e042d80d10000c0f2540c9150130310142d4542c02c04009030304664000f4403202d0610039440035500408070700e0944000340c0e010002112410b02001084a6075810142900130103401042e0505c035203240e0301042c4840d00c3e100c1042c0030a810201d0004035001c0c0700103407010440d40260150046110806000c016030750000c02075882e069824 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 299426825 1250 299425575 299425631
    0x3070506010608070e090406090f050d08010503250521060a020d0614220b04050c0d0507020d1e030207021003051503010614120703021807080703090f02040e0c04 71
    0x41c3c2c000c2014103108483c02c3c9440100a418060551107039503640008000b009010349418054406040004109000c4045903028a5541c1c00d0345506180800d4100400800040608221410b80e03d1549500c8681c840440d041201d04080f001056210540030a0340702030400c50038000c600400003001000d038090943c0240d2010700304001c82e00c1d0040580da541402c01040e0f8840c048a01c0f603010104c121041c0084403c040c880407410b182d001d00802c1c00c1d0354043d5060010108081480090204948107842d0700c0240e0344000c040907100c0c0301c1c029016400b0640c204164580351007405195900a40481d40102d5018049e85501402a80001e00401003500c44420018800d505d0044a2505005880035210707101034104418080070100001c8613524541200f0320b004002d130020160383c400340660030300030052024805500d00480c0040200600404402c181482c0c40001c01c0464034003030f40d4200c541d9060760001400098405040d260048040c001a8032a040c2005a10401010452202c00d451b030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 299428075 1250 299426825 299426837
    0xc0631140705060a021506060c010c05071a060a0b0306030a0b010909020a1a18240705010501080114010306090c0801060b04051c0f02091e0c070203061609060f050c030705060106 78
    0x102c00c10055244104401000107038070a0f80d591605060184000b5000715001707001138a040c21614800c3d003580e80c3d0340d0260001c110081500018007420803a040b00740d8550070b00c40025490074000140b400045030149001208010000400c652020054078610075000b00d8040c84569413002c4400142c101c20900724050300041c907002030400603420041031b0108103180114100b40001141000a03a500340d1020742c00703840512135440c00305040c0800e84a0b08100042550b0b1020035080103825624180d2142c00e040c2e02d00030041b0341803116000d00d14151b0ba805100824003c0740d604060820340ba5641007a003480d460400001000f00c8510014811101c042e101e2084000340c2c080c40031006002c5000250508442403c080018507240c480e5945c0a0a40300f00344056401c0003c042075010800c848220304140005804000d510701000b40a9002e20517810004282c010540028130754503070340c420b07030050060491003000b00394050000d0781d035403080c3c01c07007202d480c0d43d940d04281741ea0f01c20a100c2c11000c205 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 299429325 1250 299428075 299428079
    0x140303041103240601030207020102070504090c0302180c070609060905070e07020f030f031b07120306230f040c020106031704030605060105040f150e0607050f0f01020c06311407 78
    0x35241542d40b05800e43c0c00011500c0c4c3e9621401035010394031580007241140120980880c9580d118810111402d002c0c03901510300c18150300c10b000840c2540c1e095001c55465040402c0a244001c00840d003183da842103010071002030501e007a1014118000300103201c0e004600d0301103480d1400c545803d11600060b0b084074081040d0b01511b98903845114600c2050300c408000144200340c0c40c2c04621401d060202d02da6107045642d8035103040c480c800ca5034a1000075114001042000f1104021503032a00c91170f00c0b0740481e001040f00141802484150007030003181c480c800070821134000e42c031000095800035841440301140c0c148000c00c035446404212052440c00c2c01241d060351054080e1410398401c0000300109171301703000d801440c65440072101410090816481e12140e2600c0000d484014403500003000403140c1d109203e030400c0504641e14a540e0b1050005d04121107000a21940040003007000d145a022482e2301281d0311080d07401d5040c50b401641d0b51003800c0010207244440c00d07000c2d00d404d4442540e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 299430575 1250 299429325 299429353
    0x206070504030b0433020c0c0108090606010c020402040506040909050601090903090b07080f180406320f03031903111c02130807080708010b0f031504140303041103 72
    0x300840c0000303030243c5100d800040c00203c4007043e0035400d40c040103002a40000920301080c80e092413003090724189402299020304a07000300f2004100c00000d0074103116614044202940e210802008241004409203142095488941c102e5016000c0540802e40c0d0700d03250048070300940002a03040740c49100714400010030031628807503400195416696542c0c00d0745058403402054005103401d49006c1020800003032110320f43d000a101c1e4030959245036070102855005c0000301e9200341d000841d401141040c50545150000e508440750818401c0e80002c0c98402c00451b10b1301031901640b0b0742502c0001303403601122801d044803884034001c55805008009003080c50384040d004111403a50f00c3c030260328000740445c40c144c010344070100c0381c28000c0b00e06954800b01c2924040071507024101c0e580002e0b4041c40304407428064150442000d9501610064410011981e589844001c843e100e4180300c000c079080018007400b0300c0e0980504000c99840f418a4102854503180a005d0709220381b150390b000108003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 299431825 1250 299430575 299430577
    0x917060609010302130b030a0b01030203100c09050d261201140f060d15030303061703071203020304050a060207110a091407030506010c0c08010c140705030a031505091602060705 78
    0xd410203803040700142d10303513400e00040c4085500c060400c2600d03000d00312940e4404110549845000d03403810582545940181030519166054001e00ca0342004405002c29401003000700c1140d00c01d8542a0019519090a0700324801d1010400d00c1242050341c40380d13480c6482e03c0601640c00b80f074005079400781da880e03420088040f413000034150805007507800c1440a1905c0000382c0b600c1031009c0d02c00b09060101c40c4078010150720075041200440e5461200f80301140075003a0041c8100d9800d002945800c1c52601c800303010091000d903807010190000300003403c106082c49131800155002c1d006644038820707440e010856910003840c007402590a440000348224984c010102c008620040d19070450303d80110460281c04010f0185040c0280100b402001940c1c6100300e80042c0f450074000903801089903001031000d1900140c15008040c10f20401000c50b6010040b01c10201160070001a0816003208144c40310b9135903480241d0040d172715000c000310908181d90b032500303c2c0090703400c0c1c4a503966500760946003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 299433075 1250 299431825 299431831
    0xc0c060a090e0c0d1407030b04060311090702071a250f060c021c03060e06030f100c02070312020604030206180709020705010b0a0f03030e030d05030a020a090510091706 74
    0x54208401040480d0b18110b5241c3c002d200041654902000030b14241d00780c9400c1d071007801c504002d940030004120b80c10711900301410b400701d80c10f1240600e15110784c01c2d01d000e424032491040302e24001007100300d070003000850b000340a0401f440f0801850309600f0130168200b040070b088a0751365180003111003d40342110281059200c0c4070521103c41d2a101c1c2d000030000c0d8018901548204420b602c408030708080d010840215598021507000d00380301c144000260080c00d211b0281d800200d2081d495074020600c40e600791407014000820117140002245001c1055001074405000581c140d101c50743d01092280c801e078001d8003154de81d42c8031251601001c41000c416441d0350f800ca140203200c408902d400429a6500035000403a2030360355075000509403841d540c010901d520b648501007007059006041c90701c030041c088000d0040018103580207031091100401441015a0000342140f0f203a0244500070060000034158002580d800310300034204807203034082d50211035001c10300d501b15410002200c40c4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 299434325 1250 299433075 299433077
    0x40320010c03050d0b150c0c040606050f0c211b061614071a0402090705030609060f1305040602250503040b1303050d0507121106060919050c0c0c060a 66
    0x1001c0020751411106038102066414500d500c8081e20181551010000b00d9041c2e0b1011510b5030b600100100e03140b074589840c65490140b410840e003000140c0d000001d0b100c6000b030b4555020380d100c900c28441c6007800101144400100f01c81c0b000170000c40342c403002501183d0034514075002c44003034645003642e803148202c1d115502190014007c0340100d00c40d50b04040ca8004400b4010304040c07003591600d096014841c0c01c2446444110100801e40c6080300c0d96a41088090070000d2031401c00801060303100300d008116a0051842c50200e01c12503c4060062091505c480400c00a0b4201841e004010394412001c2c0408411070400e040901030101c201400500d9020008602c2d151810040c06d580350011171801d0b07504920450000081030f001e003c590b9a0042540e18595541400d191500202260320074002c100603120391074030312113840094040d811040480b0640100d685501201001d007411050161081e814181408103122200010344845025a0203641c44903000302d00b1301c212402401c03072000c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 299435575 1250 299434325 299434337
    0xc010f022d0f071805061005160c0509132310051b0f040e0f040b070c06020c19140102072604170307020109091b0e0a0302031204032001 60
    0x5101540c1c200c03030240c2480c0540a80700e50612500c001420461a0780c480e201c0340649603800710959000c1e205907540710200300e980e46248032002800410398022441c0107e41d64610b00700d6901448075030040e4400802c0014038100d401c0c0b03840c0c0500c00b4020a01182200c10441c02c0062910020a440301009220b404030001c21440125060010142c90050807401070600783d41103e8001440c08002810313071001d005059507132207140c04458021000024514500d411031041444000381c07901e8981c40e0043c5191508070941c03241e078103200c00244070384080420f00340b148900c4480412070070260b80ba102d501802400c11001c007982006801d034400d04e500100f405a40e1030514034189140c8021108040034044580d06154540d80381c2852102141440341c0d85a1000c140d88045680c844110b10103041e20f01014801000710805001406902c40b44513001c0c00110022103a9a0303e80d503044000a42d0000d08441d84d082c5802e4035025203610900095071280c0c441c2d86620302c8070140d102018210181130b9a05 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 299436825 1250 299435575 299435623
    0xc0301050c091c080a0203030702070506030124092402010605060304050604120504030203030d06050906030c060d110d02040e0711010b010f12020d0f0219090302030c0105090d050106080c010f02 85
    0x4154071400210300307920f00c41000b0020000c030700703007001900700b82d03466400865690501150183c0f5141041d4005d42c0700340c80c1040140441002e0034074010812899945101e0a26203440c13041e00c40304510f03003041803411244c010031403a81c01d51140800042600e038000b04400c41c0c985007805514401114060042e51101c8085000983c424148100103940e40c54414245034403540020f08551208014603652910b804003800149406200e0030b40001c0c007100100015402200030a0340703402100c455800b110341c0c0b200d01544034081641190806424694115591901c0e01e08138508500241c0d0a000010203926600740f04000c14401c10819000507110a0403041c1d240b502100d001c5441d82c0f0801d580e0f038080c0300880244600d8000e900040c400448003503252040380038103a0b00721a00b500d00d0000c00803103208c10005614003043d106a2801c080c648a543c410041c404a5070306008020b0040180d880c0282c0020f446c00085803400d64071030b00340d990310182422040c0480e500c9201c1d0201c81456000c0c1918 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 299438075 1250 299436825 299436829
    0x50408030f0403021c020106150c0c060509040605041d0d050f0f0d090b07080921181c0303091a09060a0f060801090c0806011508130201030609050c0c0c0301050c09 72
    0xe00c50780103110340b040303c070081d0340c1030601d00030881719014503000760303444020a00254030b03001c403080e015844601d000410320a0316180c0740109015480703200103001000801c1c240d00c2d121904408090100900b00f0f010510315010f89100e0300c890314201c4030f43c80c0107800000c0307461440f03039040b940c0d0300c0035003207101d42091610082a0641d502c00207060064645d108255070010740580d03403030f2b84680c000e03440d82c0010789440b03001e16003070034580da1000c00c0c841c48000d0000420380c0c1f413506072049002c240715024507011800b000300f031a05081151002c17016203444140400c250381508400c1c0094401e1200210140b41101c040e40c10070b000750b03402c3c406904140009082001654003804194104002c04520700e580c0383c019078211904001c040d01c903049429802c0c081c0326820440107004210001c0850400c68654500405400019201d10b031110030f801d40d520309580c800e400c48009080380d074034100405c0c10b28440801e0660b01003c2d00d070603607000f04226a8901c0c5011310072244601c2e040041146010444d00c1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 299439325 1250 299438075 299438101
    0x40218070c020a0312110c011d0d02030601230402071a13080d0c0e0604120b04031103130602011d0d03020c01020c0607030b181909030219110406080105040803 70
    0x240c040203004038640d8050303624143e61500860240303a19007501840050020240108008070040703503440003070306440ea81d07407242200ca1180d00040b8050b04c5906080002074000305280d00203981846244c002080e0825184100c045030600740d481e00c2501c400700410b0006a000309140606840381c082e030322411034a80c042406501415070b00b000e03400e07001250340d8007030036030090b100c0c0d0324940c0c0d92402c50126450f040582d0115107441120a181030504d4000c15040c180340e120402001d81101602250800d4000c60300031411701002e40941c3d480d40002c403082160790850b0b129150041d03080110710340b80e041103000340a00010005016050341070041c54241c005c1e5001141c0070742d1a42d0308000601080c0000d1003054010305255038046500e0301c0500401c4840d03513540750702100040380b02061142e81c601c030b090031500b4a1841140410308003c2c0b0306090b0b040003800c403c0c404158035229016010807502c020030306046402190100040c50712444241c2c220382d02110700078154182007001c06d010700040701c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 299440575 1250 299439325 299439331
    0x6030a0312090606031506090b030304030602070314071b09050702060601030e030c0303040506060a0b031510050405120703020901060f0206130203070506041806060309050312042306040501060e040218 88
    0x3070700115000040d540c8a0040b034019034401e0307610059090303070b100f603854050143d48000c0c8440e64050009442030170009803070303201d1840014201d46c0c0c0010740c902014010100590320f6180c8100090315665a801c20f407500201601b160403001071121804200e240040c85402e002d8405680107000d26541c07400190002c2030b07110b03c008405e220070f00c8001c054050410003548150310a2020708040d04040c000d100c2e00c5203280d006800340110500401c00d2484441c900c840f95131200712946010240520000c2d5000c1c403031904066040030880d807240b241da42000a41408580c0300b07030366003034090384d0380c0701d0481d0311030761040036040140c0240c004918900c0030440d003420001c3c001019980d045980d480000c645034061307400000651450810381c00d5104691207880b00406450509210007081955425140d01c0381c400d212082820303460105041c42a4014102200c81000f01c601d1111004c5056035551200d08440841d101d608003c0040780013190440028040d940c090410a0000321720004c00d0b000310801 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 299441825 1250 299440575 299440607
    0x6060f1b120d1b020106080604080a0c120201021810020703020111120a090906060f051c32101d091002030c0702032104051021050106110606030a03 65
    0x4414150140c50610042000480e00140001c440d010f041000d110841d002c030201d81035902d050302c00c004191700844c18652095215000b03a5480074120001c0d81c007044030700300260100e80380d01031044550790154010f04d00c0c007007425130071021220010108506161017000c0b084c010b8101c0b0504000550283c040c48000070400d40507503c44170050b0b86114690b40102800302e0001c0d1019508025851030351003500c020b40030343c0ca4141103001c100803010f40035202d0a84007502c050503005000d00900103907401540034102202d40202550703090980340c080e044810201526010041c004943e0941600b1100c0003103809001500207034a40d503c1503802c0135030000b41845400d00a4804080324041584000c52244104583c0c45864104030300505182c15800d040100c0070302080c0202e40380c3d130303207184040e42c04848040340c4408211040c600f04954900f211480c08a503035166041c1d1006444141d00001d06a440b0382d650a481c107414038501544d20101542c0c1c8035015048001d04602081c4180c01c0040c140c841 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 299443075 1250 299441825 299441833
    0x90d0f020907171b030f22061a03011b03020304030203070f050d112d030c0714031501061e200604060501062c040b1e040506060f1b 58
    0x52500072aa030039600715400302c000381c41d00064a11800c006003c00c1e41044080c29025040300e10424501181d20020340030009008640c000a503118000c1398001c0c86040c0c2d80d50340014041001d16040300a08400c860303016840484041401d898141445054418400d43c20054803181d00c030b070400e03402076002400540850008210502c042034011a24240703036407096009141045800c03500421001c1040301d16091608941c00c81d0301c4a442d9110320f041c00c0d5409016280210695600042c514450f0001c014901d01420200041040c120a84000c0000c429810344800e4016030300b83c444400c00900a44022468448404601c214221030700b00100c0b0941c20301c8241c0024190000440100610364481942d0007a000c0000b0051140202c0f40104440d0505490300850345050076050300070700b0410300700c1d04410058619aa515034116061014003e45501c1d0703001401d001041903004030203403072402541008041811790800c042251000c5141121039070078919011410704441d905d0103008076031441 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 299444325 1250 299443075 299443103
    0xe070504080303011403101a10110f03070c0b0f0d0f0906020f130e090709020f0904020415030506030c060315010309020312070201030501050609010c1707050d05180f06090d 76
    0x3100b0030066019000c5880510049403501081610306140c0c03490b030113002030800c0307400710642104140141a01c0c104039502400824105001c54000d80740298200140c428404444211100400144036142c01000c52400b899103903506042940303e20381803180e01d04006c00a102a5440c5a8002502200c5c040808030b100d0070b894590300c00380d80100b410000001070001d504001d4000c1110000d0080c640ca0383e00c0025880d04004241d10340c101d51180508094002403204144644503040342c0e840d8000401c07c544850301c0b0080040c01d881741c112400d01103441c04022444c03601c3d0004452001c3c6000420f01e9185944a0300380e02c6010310108115414140c03078000940050307a05004502400010040e43d0b42c4682d2640001415280103a001600500c000c01001c451640e000041c0410380c0d4000f001c21514001112102415200382c010103410b6009205910400990100c010442c09240e150240000c1e52650108105d1840003140603030b01c1001048200900c2c18500d40e21803046014807151a1202 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 299445575 1250 299444325 299444339
    0xb030405010f05101739030106030308070f03020c0601090902030a021e040b0f0904020418080304030f03050105120a170d063b0a0b0609030a0b0a0c0e0a0e070504 71
    0x40d600383d420001c0855003c8060100c5c6041030440b903050901d2030300518503100d500b0300d01c02c0b011141c00d10014228078a000e20f0010340801d01c01c0411414401b030001c0096560342c0c100182602800c1d203c030000035060408061429110380203903502992480d002e040c43c0c4e482c10302160b005040c407c0c400c0380c00d0701481e540000541c0d5250320002500080f032014003440e88421f003c000c200e5412910b490f100380c20410910f083c83c0c565110a550140d816a400074900da13061384022500c1000d980020207201e000003c100400d9842040340d420303c080358400f40700513600d0742e082000c0c0c040c00401c01c18141e07014040d80b001003000300c0b54a50038080300044030392030103030b0200a2006480040d040715034000558003c10450824441c00b0342044000c0840307005004502404070b05031360b080039101c01042511568a041c0e2903585008603560244004c08607003a030b0541c0d186c5001d01100803a030b07454115180200e070b10490b50144141d04840d007801000b55502c5810400c09046259002d804a0304002092001083c05c07 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 299446825 1250 299445575 299445581
    0xc0f020c10120c020a060c020313030b040c0b070302010e0601050a0321030b0406080304080d0207060c0f0c0e04031101060501020303070f110a02031f0c091d06131a01080903030f010b030405010f 85
    0x40500d134054140c0140500700740c800d4403040000c0c0c0d41107603c100180803200300c1d407044107820350b0b030b0006034941203494a050032a40f91007140c100d07a5140400080c0e94082640550207600d81603001f00941d1240d030382c0c500c104010300d08036100181c20000b040741900c1000044508485e01290b243c180090700100c00c2c0b01250450300399802060107640002000e01005c00100100341d074402140c03005040980c00c25400520320304004200a10480040806c0d0040010120f141e00141040c910160348074a481c0c1001809400d90b488000825480c0c4040807920754808000c403032080545890350f00c42490513520845190700c586000e040140030ba4080c883c0141c1e030900080b50141e0b6900243e51103058480750f14021034551003590000d0100100c0200a034200915804042c01914031440302250307101404103401c60010301e09034548510b4030000001c40c0b8040500702002c9582070765031141640e0340501c520758911040c1c0b10816114100001007124408201c011a0301c81d104d00d00200d030908d544542c0070f041d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 299448075 1250 299446825 299446841
    0x8130311010e0c090c0c030f0f0403050a0b0f07030b010806010f0e09091510080c13150801020315040203040822030501050f01060f030207030e090a090f0602040302040c0f020c1012 79
    0xb00303030015030600d10645441403115801c591010116480d04035000c0c1c1c015078038810b6481c628000103010802c0c000c1144000281d81c0207607004015200180c0c224030b0554201c1c40e0484101c0c51402484010503c2c0030711920a800720054180c40d400c1140e102c0800548d080000c0e10410000c001aa000414281d1a1b240d100d03401035001c60000c1c90200543e40340c0001c498802061401d00c00d100040810201000154148040e82d058a0340c8400d000c0c03140084000d0030951080d901030a0720500c1c00212440d0540c0194400c400c007003590340850380050f0402003030380b20580d03001d44900c0d0103201829144190480307a1b14021405c030344180c1d01d665a682c0f060300390b070801c40340781c0d82a8600794010012141c1080a4103886050f0703240452400360180d41c007401c0c0b402c1c494070260046101d030000480b02c206035071051721026080240f2031854a107c0c40c052021b9070044c0000ca0040c0d00f040e02c0c1c0400e0901441959004250710f40103071131012046d10500171200780c8020b481080000030f00c10310400300070390710a100c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 299449325 1250 299448075 299448101
    0x90f14091e012304030f0807080a0203041103030a020d03051003080904020904020c16050f010f020a061e06030818010912030e0409020a062706090605030603030d0608070e09010c0813031101 83
    0x90f0324502404c3c0540001501195401484009030801403141d83c0120529808101d030100142ca039107450519a00d601e03601000076405110015440d82c0594001405502916003990203205a585100c402030503c001c03440300504088060010241c2071409070060008464050001800d004040484910b000c40e0500214610800460180031a0610044030b2582000c00c2c2880a40d015140710000d642c0c1003001c002428140d034030b142440c4141d01c10704441d032a040682d50144079064581c00c11078001c3d40620014441501141844280ba500541c9040100c42d807240c134100300c180c1d20341c8095404003030038a9240d40c49580c40f034a00e8010396500a000703000d8031203079441200e03008421101006603201201e26540740843c5040400045500c04011001d844062504c03645a44442000c20b145018403619400341500740f103c041903090000540000302d45004850031aa0b03122052814201c840311041308000400e00c1d0005503903100300d81c00d00c01d00c3d64841d140100b0b5031a12100d00c0d60844840c0d0000b10 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 299450575 1250 299449325 299449391
    0x9060b0d0c1e0b09060a0c05030c0d0e0406080a0311010605090a020a0e01110304060c08121503100204060207060e011b050105070f02150105150409020301090f14091e01 74
    0xc081640300b8420a418401900c214040311030a01d054038100d400b0b204490b91042100007820704c052841886620354250340030045075100e14803c41500c1d00c5902c1c14001100080740c1917200c121a00c0d1030302603501211380c4c0801428442c1840e071001c41c2e036400380d89204c01c429900c0b80c8002445403500986a4440d942d070210050300c034181c8040041070403030808ac150b4108403202c40000308044c0d0101c11030b000c0f1821401c0c00c955588903454003051a029040c10340801400541c100034500401900d401c201c540704070140d810b51030340198070804a004501030701d401070384941c00a0060b640030b01e8403081032200c14100340500002c03d203403040187c500c4800464099445006000032290081c0c0c141e408003105001400c440c01101d09161000181446040d04c078602c078000d030140c641c0b959011a0090609210295540e6850b150040040c250030790260030a10b107000c12040e00c0f0b08040300001d00801210300a04040c8001010700300c0c20303a0313640c0049586da550b0307142040d81d00189014603500c0e440001d8814 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 299451825 1250 299450575 299450579
    0xe06041a1303051e060f1807120614060a030305040e10080f0d020105010906030206160f02060d0506090f01030519021c0c1a0307170a0f050c1210120609060b0d0c 71
    0x120350034842d04c2d00c1030300e155441401482240d0000080007030780714540c10b2529403440092200e480c41c000b001e91041c0c031205d460101400c1482843d4200445d00b11403949088115240c02051090000d458400900011014030083c03055059003400c140d005160840c0031840c2036260948032741880c2943d04110403960001c00b2008000350207010302e41c01800d8081041090030710303680101d0424811200c0d4142e0014015001604004015200c0070a90340c0250001d80c84049041d01b00f001003005450240c85961070700002121101d030148d107035042e268440084d241111003a104403c420010040407a8002d94501c42e010761030102c42802c0900c18051151944407514029a140401d10050380303182c1c0300142041000b804940040803440c44044036000d18055940d00480b000040001d10202420340307080030244074510001c1c1000d030542032039080c602070300c0b915428842625440c0d24400d0b9210107490f5070320440411002d600840586000e1580402d01550150005603007142900c0c04030348182c004201 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 299453075 1250 299451825 299451853
    0x211b03151a0703030207020612180c06032412030d020a0e04020a0c081602030d0306080c0a0305070b0c03040e071112120414030d090605160e06041a130305 68
    0x4900103220300312489030381c040541c869149a10602c1009411325130001003040031034480c04100c5940c00010140400d1506201c1900c000200c03241103840305612450028001c0d40c90014101c0780229000080c511854140350681e40d030107918111901e5104480d0049603008140030300c0206101000c01d200181e44500900018291420941070b6900403441442403801e940d800042c210891604400e03001e03118a40d10582c001d14002e6250001d4150084881c413009140d003680166003a07070f240506440b0b0340381c40601440703259181444090a5580440c0301081440c98010040040007032503400e6038a442d4813100e80007042c220680b16100010041c0c00b44c1c0d00f0382d80342400200100394007201604c0c82d04d401100c0241003158090070242c81a40c620300c0e0b1082180c4200121012454518001e100e44840c3e41403e10091400302d490100c8403503071000303d40749580b0410202c00680300003001d10342002e003400384110b11000905020411680308111008002050000c810015480781c0b0003004602030241c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 299454325 1250 299453075 299453111
    0x1d01170307051c090815040b090313030b0103030305060409110f030109080c2d1f29011107030c09050402011119060c0503070507030e0f300607211b03 66
    0xb0005c0b40340e0b000300f04030008856541000540107a0080c1d480b18203030711520042400d500c115695002d10305000c6000008004118100c18122030080d241000255110414170050702d1250100808036254170a82d841d840c50000c080580c3d4203409000005c111800c0d035076035201540445040d440681c405280d0314040f01c0c1c06601d144601c0f0310302540e111030300c07882d0586075034981075090440c5244501344286140c0d404542c0c440d00020001c0c1d9018409803480b100c41c10f1381001a60300c2c0074001540030482c06400c01c400900541201ea01404041015150a41d51001420040c000b00e0400054030302c00441340408000340764a001d00d5000b550b41c04c010300d00e40602111030801071a0f041c17040c28001c1000341900721054522898143c10642c240c81d0030140000c85075421290303121b52001e0050309600910302024005103159051090302000040242c0016a603204c04a442000068100000d505002c0800411010b04001d028001c6005060446807030060760707140d00201c0020781c0d130b848140c003d4810b1030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 299455575 1250 299454325 299454329
    0x50304050a060201090302150c12043c0206090d02041103190b0f0603060d0c08070612050f060d05010f14070e040515041a03030408030c071d01170307051c09 69
    0x10000b04881c059580c6c01030744803031500c0c541250010040d800141e00f16591b00440309251b40d50390f4800518501480c2140e0318009108240d149400701e0284c80750400980740a1000350310381010100e09050081e802c20001d98402c615513504686260054001070315140203500044025000264032490203000c0741608189403010005518204100c521a83d00d03060240b507449281521003a50320b540c0c03040030501c442c8550030020118040e295000900301c2c0041038000c207030f4144d940c81c00c000c003035206403010a0311000d0700c040610070b0096021072414904422904081882000046000d0f4855001407045030907440080520071400c5040280302d076030000921001030000c8808000c02d042114140000410a05805000b19518402e440c001900341c1c0e031041c2001c1000f41180d03560341e1035100c200d07225080f40002d812540f00b0b0241c00700e28840e0666070a122100c9440000d10740743c1c605010405002e03295028101c03e4001007192801042c420b1040e4852880107a1800100c110300142c0200100c00319 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 299456825 1250 299455575 299455577
    0xa030626060a02090a030b0c0c1615020a150b0112090303020403110909060c0307022806150e04020f0a081506030706051c020310120c03120f05070f050316050304050a06 74
    0x1040004a81c0d503a07178a40ca01034175003020b60700700c01d980d4805000143d071040c103821110030310985440c07150314004080e03600141c5142403143d000c2840400f0041ea40c455110b0700050501c948040c0e540d660800c039500004c11800c0502d002d645903025542e5030001c0b42c83d200c1c41030b00001d4000a0900522040125081032101c0039550304a4915000d80c005888900c00303040c002400c3e2001002c90301d207a01c00c01c01580101506c130001c001000340c8100c541074030f500b808030468496007040e42225100d54240140d20445260070802d0001d5601c0d5801c03c03003902940f118071b6512120185d0049000315007000109001107910416010505014040600e4424580d11030000c001040103c20756249064100e154490002070b40580c5a131110701600300a06004c0d0881184d001200713887c0320500c240060a80100c82c00b41c2600d095080001c02c0c101d07116505000000c1c003098041003528000341e108080400054050401d59061120050301c507020040510000d0b03815500100d01800249482500d40008040d1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 299458075 1250 299456825 299456827
    0x50301230609070315060908010e0705030a080c16080a031205091f0b09091b011812050f061906050a0509010506031801020a030c02060717010b0a030626060a02 70
    0x10000345403451090060215000d40c89140100d01d10b0350203500312051003041039030071010480d100c80000b0004280f0f44070b0901a582010116200e0000110355941a50000f4018112040e19915100955440426071108500c2404a0b00b45454070038003c01001c5d0031000060b11038244207050050079211183c0802e40e001e4a05801e0014500300014046c0070044501c082e03c003e03144514410b80100788002849821115050401c20b07104008142160126504081801e80550400c01102d04859030180080405400030050007084100922103101a120b40304903501080f0b1100c5640c1020f0050321101404c000304010201051240e01541d405441c05a4091100501e00000580080c4061241078040c0e680000070505502403601013600d1140300000942d951110341e07200074000d044000405c80140900b0012134003071486070742c106a0145888100380540c4c2d0a0002c0f1040359840407c80c00c080c595980400640d800e40c002c2d44034030318850051060504d14165402d1410181c004181d40b82c1544 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 299459325 1250 299458075 299458121
    0x60507030c120816031406040f021201260c010e060c0109050a080a020f011a0f190609030c0909050a06020309070e011d010609120807020a090509010902100c1505040f080408010501050301 82
    0x11060303951981c05202202e010468202048000008bc0300c3c21130004a1940740d80c002107414071020303a2001052140d00d010a0000344900c441ca40c40c1d2020b5840f25000410410201c959403a0a01c09000f4012a03040005400e0b50a991814600428588111045100072500d442080d80621042e0508840080207009003803484204020600c0c1c00c2416071f20400300200c104040c2e80351070500a401038912020030250359200d03040a0b11580b0980710403a080d5030a0304011450140c140101040d080d803003801080c002c440da584141c06504001c0c402503940c401d440d00080e08041030300d59a802449110300509000000700f0031800000f5050704200240801c0080400801001040c161030094000c1900c03512034203a0b2001456006041d8082c540c2203041000344011840c0c1075101060b00c5208598039800c0c11100300094440040d60b08003d40300c21151609032000281e540c004c0c0e07a10510484405010b03034030b5627030345601981168005554580d500d03401401641005d225110200444900d8807010304 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 299460431 1106 299459325 299459351
    0x1020c15100b0c061b091003050f09010507120903020c0607050f0105010e0709050d0f06020a05030106020601140a090b01020f070803090f04060b04060507030c12081603 74
    0x740d100005801003224229078501c80000060101540c60743c1d19420584c103428208101c00d2804c001104466546aa84100c040d00b55103001030242030000310302011840051052000340c2c5800c00340080c2c0c54018024148240c2c2c1d11402050400d02ca1400324104a682c4809980000c004554881001404240344100d001018020480c81c4c1ea42c01d081d6031007800659880b00816148942440315040c4a900180c02900900103602000541e82d03810040381e104c0711544000510200050040c1340d814490b00d401004c10b51041e400c4410300c030700012058203140c440c14080664804132a08243d000b408500c902d40c4800080d5100c160b030702c485c502c0c0c903907108610140c030840081c0d0f844a118601840340c04166101010107a0400b81040c1c02179450f03034007201e019001d00c00c031a449403001440a503240701c1c00c800d066076840e01d203003005101c4500c1c4003c0e00200000340b60500541003104 = true := by decide +kernel

theorem cover : BRFrame.Cov 299280575 299460431 := by
  have h0 := BRFrame.cov_init 299280575
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299280575 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 299280575 ≤ n) (h2 : n < 299460431) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
