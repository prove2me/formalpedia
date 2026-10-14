-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1907
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:06:46.550199+00:00
-- url     : https://prove2.me/submissions/be63868c-73b5-4e8b-abcd-e6594e08abc9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 342805755 ≤ n < 342985611 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 342807005 1250 342805755 342805759
    0xf03191b140304140f0a050c0303180904020111010f0b0111060f01061b1b05010f110706110a061b080c12011406120a02090103200301060f0915090608070216051e 71
    0x107883c6045c407013030585070100c1c0c12047e1054841d10042000078a00401150a8003240380c02038601142000203001c10350074014426814480c00d000b1443c407001c000e0180c2030b4800300c4040e0001d442e1004c02c0026000000280c00e40c0f1031940100108031102216601c044c2c15a0400d0910403c210a000d1800b222010800f00007041c0e41d14545511401c0d10244ca901d13401e456007600c03022610090fa41007103030604a03c1d1542d41413503204c41c0c1c0c10803400f8054125814000c4060040d2002c603991905c412042e100b242c0011016081c520007140718840e070288481d500f010030440110b1900218603c01c2c022000180141d0b0860540d200d400c5202d0f545520441e110882d001014003910716009000304005d4118402c2980420f0512804030b041c0560400d0010100510030341d058216403c20100300d030b00d4040c1184c15410b10448000200e40d203500020300000ca084190b0350844250f091850003000d1200260003e4295400075050a41650500c40500207550007a2849000e202007290006012110300709569 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 342808255 1250 342807005 342807013
    0x7030f05070e22060218040204081014151c0605040615050105041a13080709020903011505100c020402190206060a0b120c0306060f03191b14030414 65
    0xa420410045105021100c54644400c00d580d00c00200701c061034821202110100750109030303a4002030484c0d0243c110784048005d1000103500e03010203d0226801a000b40c10302d50700c401110350070495a0b002e04181d000705481d20908d2402c0401d0b05004000c01d555669124a10407101e0041c0b01102c269180c5200740c20000a000609050070100000d01500403a0f41100c030300b2000105240d401030040702d04843c0f46130a0301500c03409038030082c0b115401510300400b002413003075000528000c1c1040144040e00b000b8100507645d2105004050864188441d100c00b00d01c9568000c01040e6260100e100c940000c600700641800c510303100050013881001011069890444107d80815600080e520f215150943d880305131103880303002c80c00d41d600481140c40d40100440f000503058030845006145c0040000e45094103103014005003c943d500102c5040b44003079114004562503d223a8000c0a0820000a1030b401c455080c0c010024a511068000781e100c241001001c0b40410080c01c42500352101020b081c0c03 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 342809505 1250 342808255 342808283
    0x507120515090906010b1e0f0a09080c0a03080a030c0e0405010f051c0b01180e03070303240506220801090b06100305070503060409030c120e1c1a090703 67
    0x7401010420110180c080c034a242c0c002988035000164090607600c0800c0a1401d003456440040c01d030000c82c0641501e00401404884c10f041c1c40203024288901c1641c80f080107080c20040c400d49020100c101e4a03200b070407400d20030808a55501d044030b810b060707e4580803c02840010065481d001c0710115907800c14034060001a081c1260b40801d001e0700c000315200b0142c41000e200300b100d1050145809401102d41c44010420918060901240d000104201141022005000074150303000381b68180c1c0440d46170403180c002210070218407400c0b40f05000c0702e09030042c1010302144043c000c101c41645040003d540290841028920010043c80b45500a202c1800310340b5010503481d00580f0301c60f0040845601000002d4040d014040c49100659286d41c210307500e03074003004040e04000e40f060341071100302c1382c12401040090303070b0320f07500140c443d110840000c0d812410301c190243c8084e1000c10b01d07850303800100300140724001f0a00a07928000c010502039258030346400d04200d6282c6c00180154900c0c0a4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 342810755 1250 342809505 342809521
    0x60d0506220203340804140105101a130315090501060f170304140112020c19020109050103020f0d020c0312090609011503050c19091a031605060d05071205 68
    0x440c4500b0448080302c100004004c0c44940e5000e54800d49040c14280703401d80742c18940320b01d041e2540a4010b0024903500c05d030004c00a801c41d0720a40c0c510b00080c00c0784d0424022090032145130a80d00c184150740d5071910700c0a0740c0b203c4107062140401816503d4003541402050440c3c3c21180e140c540140c001c0014658400c031007410303080c135032040003248001345644a0703050f4008010342d01180c0c80d01012050401f12140119003a01040944071000f560911815480346010031020804100b03c0103030201842c903900001d008900036600c040d0406004100c0704210000304e02c180d541c6070054031009038803203c43c0c94110703041d4011141144080c4000034200800c40c0e00001d0081d0051440703400801c0080301350102c00750004440c0c0009042644500584442c6040ca40e400d484000c1d850080300c0b807501e403203d0094040c3c4803644c0310025407003030803500d03080d040c9414402881501d280001c103050031407a00010400c07a02031011a00b40d03559484002070080c0c2c2c00344007402e4002c4e02102c002c0144d032030000c032 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 342812005 1250 342810755 342810757
    0x7020c030f1f2c12070f03090b130b1b030a0c061a010504060f021e070518060d080a030609020f1b060f0c070309120606061b02060d05062202 62
    0x310030030361580b2030019003107010354410f50718040e1410090b0360341c0d00c110001c0010400721104490f0000e21030242901459151000034115540c42194420400616401e00610141054002154004080140401c040314941e010401c541c0c0c0d00085030b0b03c0700342e400c107800d0440750400900d0480340400980131b50f0003980070344542d0146100351070401070289071500b04056482a607a0560204008103c2230100c5c9000d00a0904204094411102e68149081e100c2e109411b02000d000c1040e07120305001d1143d031920302c0041d500b00c3e6250380585000e1074001e0000c1c0c144e400b94000a00300388400111001c070242303e90088000781000440641d41c0304039403800454545c1c010081490610580b034014950420f0104640c0d025102d03603081c200700c2d0f840788104050540d100900480034017404402c001554440004d4440c15180a14400601da80c135113034000e8a208003814096400440519a400c0161b546409880c0b03420541000010342e9510400803401850701055003502d2152049800308032103505030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 342813255 1250 342812005 342812023
    0xc180312030a15060c030207030b0604090f0b090c0405130f0302070807120c050907080708190509010b01031d0601120c0803180103060902120606090607080a0503040c1401021507020c030f 82
    0x1c185589804e5507810101c0e160030b04100000c0058012507000c002007001006810f4001c1002130001600840300c1d0380700303907203015541000ca4254010400f041039a40060000412401d4152014071842c901030700191180000e82c40d00514202212a10707000b40b52080140350064007840341140d122544440c503143c80c020095008403610045001d02007004c3c24201003041c000c0500b0340721031059450310078041c0d0b1008030040020401a1605a086031002c0e9207006243c058451400009803ca80c0741c000181901c20750040d805084260310040144650002003480c1110303466140d003140e40c1d000340b510201c20003650f80040035511000c940d2900c0d080c8002c820403d1002c0980b801c0015580d1000b50205034001ca85007a0111811100007407200e040540c024106103400400081c540407960340c03109202c0d088480c4805c0014008410031040000d140c00e444081c1044c4580000b15460140000390780b016410592981c860f80c2202144449008003c105080940102550481101c446010342c1d910980c03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 342814505 1250 342813255 342813281
    0xb06071a0c0c0c130e0307060b09090307030c060e3a020601080d1b020d0812091902040213080706020d081317160b0a0507020c03060c180312030a 64
    0x309022607218410703182121540d18000b00540310b00c50386042000700c80980301e500340200f15110304160503107040a200034012140b0a1400185a01a0030705009180000030003ca83c954070812200c1c3c0884e81000301680801da1050700860701c8030b0407070903d5003848908003880012741d03141c00c1c2d841542d40c10021000340c112920b41e52601d001c0004413049944510a03c110032072600900260000c80744203101d04201540303441c5261625042940c0460104010154280c03003460340400e811341d00d08501060190030a0081c0003c02e007041a68107181602c800012009104a50002c0c14006030b04890300d07600010440d0301c2c00d07540c50300c1e50b80901a48a036840c2e900f0078000b6820800042030f90410442c1450040d800c110a17004012080320518003a44c8180301300c4401d1496401000e0015042c030381c2d25403080c1041e4070080780d03508000002902e40303003442402034441c0e045030040065540d4400c090310240d589003080b2140900ca071303901103410240e0410008003440340c0041002001411740e00250341c0f10f40030b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 342815755 1250 342814505 342814553
    0x9070507060510140d031b0f140601081c0527030601080d0f1706041e050a06030606060c020919060b07060902120a050303010e06041d011e0213180b0607 67
    0x90800308464101c0c01c5c00000d0108401e90000054541c0303404104003000d11072041c0f441c09a5058841500104203014030044640c4410014803000d40c080c00341c9402c030408217061010310404040050450f019032117502c003c410211a0442c50650003986001c140366019080c0c1d41e95507150b0030140e0f200e51031200c00c00c01142415032407800c0c040c8507168181d54603039400300480e0300e600c070ba000700805404648005c00e4009c446000342d0101d81010312440e03000751100440052510328526010003521055031144051000000c1490003603190415030b5540810200381507115000d2a0001000504184e00014203202000c00e041c1c0402280b40d22182000e4005c540c2c8007440401407480641c0c4028204004240c0c1e0414801080360030203001c10303160000d5004001180d0143c503143c010084000e0303440d000d1580c1e03454014548440c8865100c0e41c1030341500c81f50640c80d05910210f002d0041899116045a07030b00c0d866205d0b00040c05030b605c103202004004013890766134521804d02003042c0700c2c0b216400314000c01c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 342817005 1250 342815755 342815789
    0x303050f130305070b0c120115031d06070e010318030309110306070c06020702010c0b0c12060103020c0a020f06040317040810090f0b040201111c020106090903080609070507060510 79
    0x40c000d564019440d81581c07064940a000e903030320f00b880e40d409400303600b1b00030741071004200520f07200c1004da01801511032701d0350750103030782c814001c007900c201080c084d0440002c0e810b02c0c10281130200712181e0106090400b00c08444103900101c0085c418a000382041c144141c40000801d40e00d41c101d10880d60003000748100005d00c3c0700406498010a0360060080b40603c480d040c0025015006441c2c2d2034014107000300c02013525120034411038012078448260307000c001f4803000300381c0f58110b0341504203d003882d04604105840fa205075894580a2019200d003501d401403d07259620141105c01640c1d010714201c07441003904943c040d6079046405051060b004020340703000060554030424001c250042c0b400300d105105500e8040704c01c4e03005001a41004240300d0b860602234000c01040c05030310201055854002410307003000f801c44059811120700300342447d00b408c0100e41d0101c1c1c3c1c190802012103000f1a0ba84842c001621144242ca0004015a0030101040b07402d00b80c0c642c501d07007115006c44031620090 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 342818255 1250 342817005 342817021
    0x101502100614010503010e04060209090a0b041b09090e070b0409060509070201090c0902030402040e011a0301060602070e04060209011e0e1305160e0f04020403140c011409060f160303050f 82
    0x8040015030b40d0000d070007440100442450320002c070340c00c180103010040c030740030986001c01c0c2414002ca400e90703034040d1500f4620816003000c0c8100d00d402a156407403410410000e030710040031880d083c03046030715054560005141d601c02c18001d0500a000322802c403544c035903640e00741101805191003003a204009a800003a2001d0043c0200d40c1d0250340301c00210401c81c100310205009400240003a80c11507522241004120401d100d601c80c0380074004044821100b01008060a6400036000902107401101c401c0048100b0044225000341e480140583c8403500140101d45481c98103000790f0416251500d101d00550704003d00050728501070300c081d12001d031242049019170307400f9503103a510841d6084a540c0d41d50f200e090381c07112410f0000c200d90004244480010300740d8101d0b40007070b5001c5802c64100c2500800070800a107000700c0070b0030101c1a6214045040280d8080d1041c0745008810001c1d10f8403169056030111404a1a82c1c0a480ca90605030308006000348411100910100001000302d1140 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 342819505 1250 342818255 342818279
    0x3060115140421080408010906050a0e03091807031103070807030c0e060a030b13020c0105061e010f0c05070302040f0c080709120f06110a0507110d11091015021006 72
    0x1558509440343c00c80c00041c0b0402c0c8898200903000c0c0e420407003c1c07001180c048002e00603410310f01d01884003c5807900705001c00e981120100742000c01a9402040b03143d070142c071084100145c4104009010602e40d80758074065000e0b00702039541c113131141800004c126140740c00c0501c8a0195096550030010882e010400f503c00402c0180390700c0d44482d061104220300c070301c40d4200041c00c2002a003100750b6000e800d040300d0107a0700403810034141c42c1d441c2c10030001070741804441848912a1010501501100240040c08008070341d80c00100308180e0003412010f001003001250011a8003820401950002c01540703c02031841d100200300007440740c0c010400c0d05114001c0003094034080c0d10070100900c0700e40d44c0c08848040e00c0208556040e03d5413481220201d1040141c842072050740c84030f44d07888100b031402030110341801c18980d1141c1c40d80900e40e00491341880c000092188103940c202096201c6100d48245444583e0117100f084184101100e400780c0e0101d581740010f000b140041c00070359201d80742c1c4546 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 342820755 1250 342819505 342819509
    0xf06240f0804021e03100b12031615231f180230010303080717010e0402030a0f200409110402091801030605060108010b0a0c08090a05030601151404 65
    0x1e1007110215000d8030b44080c6440700d00700016189100d55014034003180c140810980849002603503500c0011080c10400120101914031202030340c507020320080d1144961030000005840d2001f9620704015290980e407200e000c2c003019404421102d01c0011241c40389020071940c1c00e80100400302d100207020080c00090307090310340d8800c44802c010320710a003280080d0010341500750f4808402c451018081030085910401c00b01411030b40c400c540c11410050050700000e000c4000f0400200300021110b4404510309054078080c030700ca82d101d620b4500001c2c0c64450034a40c080e2449066084072002c10041580c03103070301011400801c000c01c0d00320700208000c840001402030300c95140c0d940c84441c64a0254014821404014181101e403c0b101d17005840111098100b1203000380ea41e010301c0701a41e0810a02c900505c51000317450718107800381100500942860740c00800e21040400c000e40d0650300e1041d014081c28000d8111081507a5070300e100c4d95600712040c041c2001c980040c0042c0315030786841e02201c0c1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 342822005 1250 342820755 342820757
    0x50c1203040c080118020405091203090304030b01062102070309030206180a09090201050d150b1b1002071e140f0102030f0705090d1202120a0305060117100b07060f06240f 75
    0x3440d05c459000c1c00040d04000340064164018007070101ca042c420f000145004994800080d500c0f207003145403011080c4010380100d4140900410441c600508000d9808048440c40c4030141e2201030501d400d607408203140d080290300800120305141407182891ba580f042c0b880486011040301d0390b9010601c00c40b8070310000a40002c0c020015110380a504e80c001d95514007004601681c015901d00c540c4400d500000510010031914030400e00801c4010003140040c8408040214941800c0340c0e103e0310400345021308001c00b401c50b180d070042440f60451090b286050300400ba580c2a82160340168001d600c111007150240d0708200101e82e1091050303042d9000c120b0060200001c20300940c8400b0303000725541e00303c0b00031071184c401d2490303a800d40da201a010042407038038082000c2c28141d0000d402450f10404140302084444108084e00a10300341050464801c2020301d56a403602d410302030058807aa0503903000c02410300b00c2c00a0350401080c005d11039180400300c24006000007031021500404a031240714 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 342823255 1250 342822005 342822041
    0x6060f1416082206140d0b0f031002070510230408070614040b0a050c030a0903030e0102071b0803041202210f070801060905010f0312050c1203040c0801 67
    0x54450328040040c000060446801e10400c49155a20007040c2c1c0030112011500440003182c090000f003821003d40a0803007820000c10118200c5180415806100c164048064403100d01e84040e49030390340d040001e180f019081c3c1e8587c08110301c0c0c5001951004500303c1d0148141c070b03800c58101c601807040d207000c4000c80813603620506801d0308160800344080c10580e49854200015800110180303d1000b111014040c900c0c0a4a040c0c2043c080000c401030245210b0b41c1440100f212200000d01120b50102c1000c0700000e014000d41003c070010248035041003c0d80d88001404020b02030360402d42d16089030444a280c0c2c3c000d44942000b42c8901440c441d000c0c41d00d04000c101e40041c540b020406240c0b04500c0c0202807008041700030b540c5003400c1d20001f603005030440c500c10300c400e1100b8002c5d07501400000c0000d000d6545001c0b051900c2d90654400500140300b0241000d0807a8841d008840380655900c0495403003018484c00c0e078005a005031012074445a8060000501d07140600070324415070444107540f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 342824505 1250 342823255 342823277
    0x906040306021e0c0a020109050d0c0306181a18160b1804020d0e010b030f0c1908062d01080607031505030102040e0a0513020312070c0b040b0a020106060f 68
    0xc0c00203508245200ca846605011043c1d04200300200036100401d05200101080d851390f000240240b138094024500401e41080132001041d00f1041c007800301ca500ca41d0004050389036800540c225501508024486060b03607048416211f81207001a02070702c625007460b140c100ca0308000780d9881144d2a001c400c500c040355810000000f80001900361590010305a000342020f0400113070072a446044a44031217a1b0365030030081e280d9401d101d0b602d080b00d4194010b08444450040e11075684080c41d01d450300c0b0321141410703030303101030f048045c030b90002d0611104540450401c141da803201c50b00a658108a0701498070561900c0d11045c032292412a5801c4015003440d031078201c02100540082010b2110201c4444c1e800105900c00744000c0000b80405402000c4130b04000e0080420b03a400644058116130101e840304d009a500400c000f00e010540d044607641d6410503251210400b54194010710f1703913190120b40080c3d01c0441b20010828480d40c0c0e80200301c110b4a400c1d00383d6802c006001d417000010460101c07 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 342825755 1250 342824505 342824513
    0x1030b0a0507032c06010f1a0c030706020a020d0e0907050a0503070e090a09060e12120709050a030b011806061d06040e040317010e010503060f0411030609010c02100209060403 77
    0x400d607001072440c60f01040003124007040080808a0381e1442d58403070a0381060886119090120a003d0044a100d4407140c0d850715001d0b55a400140007810b151001c0014445080a0100100c4241540c01441592603c44d14075010f0341714102d40d400400480c0004e04031a2040c0b83c02000e8512424094076500d0500c9846c5c0412205504010025030912070700203030b82580381c0e0b2110080303803184610705070124410381145080300a881c001d07440640380340c3c0900d18401d0362190070710a6603619481c8080c1035080c0c3e554044200d1b027140710b0358412508004030328804020303ca039100321a4181c50810104041d101620415801290301e51b02c06d40c40000c1c00c14a00080740d05003230111525241c40100054206038496010004006c0107031002c50104401d100800d0801090b000c2c01da00401900c040900c5a614110200303844440041210098042070310001d82042101c9800901140c0c02600301c402e58030704240c145000700010300000b00035106482e800c80d00d40c2a94003c455655401a040e030303050a1075591 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 342827005 1250 342825755 342825761
    0x30c090221060d05160906060c0c151209030804030f05070317101707031103030f0901120207211b1a070e030a081e0403030c120306170f0d02030301030b0a 68
    0x1101590100000b0f0882d4007007001040b06426000380d14480001e030b180381407501401c0302e6842e4840018480c1c059609408621894411001c450114003044c0070244100c10072600f04910b24650704c0c000345002e061209041d80520120301c114403d45885804480c2d092040e901405110402400275810710300203440314000d0085c003608140750340c01503018280c4030403002c5055a40007810714130704c0e484881c042090000d0110700c5d0000d00403e81c040c601d0044034001ca160184191010141402564642c0c00400c0001d94112020941c2040312010084001c0f080101c0b01041240220005005812440c91405841080c0744605501440c41d916650181403010145400100440c05004403981c1090007520148222400703140700d0208595602d112509444000501d1030312041d404e14240001d00000e904040c0745881075820003100c04010361000000c4010b030000750012140c1c50741000c02c14074a104c1c0020f0050504003020300751a9804060031b0b04030703500e003c24400a002d41140c1c0e80408c0030003c0c158 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 342828255 1250 342827005 342827011
    0x1406031b03030c0d02151e1501260a06080106061d060706060b03040b0703020a080103060b2404050f042a02010e1615030b0a0506090406050d0507030c090221 69
    0x107800d507420000303003501e0380303080805005144001d07070400020201d44040d28041d89070701041c0c43c03101d041400360798003000c20a44002005171146e00403403a0b03100c01d980e0007031074220f655400c3c172002400d251203124900d0503e010142d9424402c541829000b041000040c042c01c0d080e540300327590b46100b1301032125810740c072030005515407034126100700400070126000f4000c01e4050001d280c5e01640d20300b07141c98404005d4400070507090070940b050010861181d4850001c034110f0750840c0011814098120000e0024030a0702c015a140c100308459041c3c103102144090000c40718102d814081c00d0b180d0710b05110684d210100c850a00300c2c5501e0251800b004440740d1444176000380d00c00001c920711090304540c075200740240705256403505800204130460f09a10040c00713102c96450300380803c66030b0300b011980e400d07141e0150500c1085c0128801003d510780381c0c0800001c1c01c0080030001a80c007e800d106884040380e020555401c100c4200120f50014240200d0f100a00021a21301234964128511020100e001d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 342829505 1250 342828255 342828259
    0x30c06070602130806042a0e0a0222050f0901050d0201180305030c1005090c10080c0c0a120e190b09130507030f0c0e0a0312030605060703121406031b 66
    0xc1c8140916950300003602c1002e444108000c09142c1400d08110b103881c47c45182906112010304213801c01c02046282c00f030100ea000d040d2500254440400c9440030380201c4950f40600f00d90800103491180303000701c001c001c480064903090644800724040c8440000c09015160304034132015a00801544503113540c1400002010001010a8907540c80904691040403110350030740c0142000d071a004401d21405070007883c2c0708010700e024050280810741d50310340141100309001c9540c0c0040c544c1c2d44107204550880d0040702c141e070388925045c5400c0081d200c04581c02030000b00104140070301d03070500d090b81305000b50f046010030000310b183c15945407195018440c2c1a41042402403040d4001c241401031a008403941d480204001607580b4840003200c0c4101c201c3c00c00c001c42185110f0306a110601c1207020f86c3e81003001e04480c8038801c40c0c1a0050f014660025410203000111f0303409055004443c00b180540040003406240b1142c0c40c0100d100c50155007240e4141c22030000b140102c03031601c800c00060080 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 342830755 1250 342829505 342829507
    0x1050907020f0604050a0c150e012a24060e01030807060b0402030a0902040507050307120b1c0308040c0e0714030901060f0b07030221160c1a040510020c030c06070602 73
    0x520141c600f0b114050710111119800100044100003c600c501e501401c0f107429000c0002c68100707c010b0800080521150621100240c00c1c546181034020312080291010301610003006503241c43c00c0e02c20088140340c515032010744103d40c104010b5004680403a07124254a241e56400d54980704070560085000301d0b8219502c802e0a00281c441c0e00146200742c0f001240003802c00c8450050200b5100003e10b0b8904000b0b04200300711805800c1050700090110300d11000078241c188401003880900c2140c900a22440c2c0c0001e403104060380004c9007440b8922441210038159614444004115800d49005002c2a518446020210710000103542e00100d50ba0021440640d266081740004040307800a0104400008001e81030680411240c5c942d06603907901980345331404c1045019a0140745580c0a14031109480c080a01c00078202e9a0040e01203015030005101c1c11b800894115406481514009c9003090341c0d0002150010034200c280500c0a130191804032440d404100c19070b4488603080382d01d40c2d8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 342832005 1250 342830755 342830773
    0xe01033b030c010606050316020606010f0c1a0c070312050609040b071206080106060908281401110301090b10020d03050a020403140706180807061b0605090c0906010c08030105090702 80
    0x1d090207130500a1a950312120703500e04001c0c000d207400d540c43c010708009650043d0709010260364458421200350341680b8111030001420300e0700b4010040300c51401444aa80b41c014010300359040c00c010000280310340c03612005008015801c1007520f07422601b082d070081007400010085641011000e60182a520345903100c201625040d030112851900480c0061303548400900801d0b42124410014060b10350080000a10b02c800100001c85041100e580d110b1800400700300304090421020201d081000080c4a04030a4000707404080c0c00174403808401c10f0500c00412143d05100c00c2044045810f42e01030041070f04100740a0700035100c09080700c1d80c015800c00001021800d100c001c880800c00c03100240c80802c1c5081001442088401002141440500d00c00c04c00b5500000d115804c9400500f46a04286480c8008103204a0b041801600030360a000c00c000081e000412108102c2108850038a400c0e01e51100440e072040207407400030000e07002000103100901d4183c01c4903501080301d2040f5031b2540 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 342833255 1250 342832005 342832027
    0xb060d0303060918060501060908030f130503240f010b03060108040c050303210f01050d0605060301150308340b13050f15010515040b1605010204060e01033b03 70
    0x14502240445205500c240d0342c0041117000e00400d07004043d00d16081800a040000c0c7c031752248500030500346402400102c0040e07070040b40382c0344001404001d040c0c9101031405004030b01d0411482d240e00035840c6c921400960784411014000c0d0588108520060860350340c4001910780b440c02401c241c59200c650100042e0640d0100014001401c03840f0510940c104070015001c1c00000280c100200304621800501c001d4541043c4070324419040782010445445130307004207004088010104000e004a400701100348290036004100768a0100101482c1c90710b10f4141d0007941c2d03500c6010303840c4090303500d0480020881d05150140c1204032254000c80d06005a0354080c030784418080c0c40447d07608030703140b00c0300102802509903004040550b0b02c501e1804078140710811920071406090710a10001c59401400e45030b85140803145544031300219903039505c0d8071001c0d2109507884030560000f82003008d401d42005010400160402d01c5115440c1002600c0083c0c002c4584054981500c0e80300901c6088154 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 342834505 1250 342833255 342833261
    0x9040e010e0a1b03020607021504090207030306140928020d0912110304030512030a09140115091116140706180602010c081605090402030c12130b060d03030609 70
    0x31050070009084030b071070700e03c3c00320300303240e021420700c2e4034180381080070005a11080e01712041e9650446580c2910a0f41d02440711130390140c0d8110107036242c8040340c14000c1540541c0410141c80c448460203021448038801c003c40c00500702c80c09403500c8031920124001859451445009202e603400140c18000ca01d4039440c210713a03880209440406c2e062082d050b441c6c2d000800e01400000c010003841c5414150744038295a40709041400030085800400a60700d00f46a60110f448954407000c035a0203c540c8003000e6000e8000c03490201034070040400e001a20b00401e209001d00382d0040002c450030b00b0403064416600c041111800c4d14030402c0c030321201454800038070a00001e0402c80d1940b40f14180305c2852102044015081241507a1500d035240c00c489070044611a4400c10f0300f000f000140300c00600071940782c041c1380031b65500075002006200c0350f28080009040b40e41490500340d88190783c0c401c280001907441b044050030244a0360080389850038030005422565009050104d01d06036148540030407 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 342835755 1250 342834505 342834521
    0x14030709023006040506010801080d05180d032a0302190521030415110d27051e07061d0d0c030b0702061609121b150e030a0f030509040e01 61
    0x1c000b040810080d45041d00c00c040d088202840d001c0f25942c1450324061b0b84280910240c1e040c40004903030035640c011500b04005c1100f4014261403c841c60b24a0091310b0b5240c00e101d100a41e0408000c0c4600d44006802c010401c1501603000b020603503070b001d403204001c84400c10151918002d82d1066504080e480c032450152144010086a0341d02d0141051200d0050a5000c002c40a00700704030b0b605556001c400b66a000700104030005050140e880c10000000c4800c00456040d44501010406206000c5221030f810752003000d0580346024200480c82e10b58105000e840c002c5006802d810b00301401e15134400b0018880584030a0100019480e200842c820a03441260002c041d0ba0400143d154180181a04208440b8044502c411031400280594002c1d0084c417064140800c021400e100c0c0900c1e102101180b582041000581c440c048411030007010003002010131031312408036900741070004903405a65048074100486440f0350340c00b00e40c66486602010b5009407280940003100c03a00f0302c54044c3d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 342837005 1250 342835755 342835837
    0x5060c07030506060f060714010608060c0d0b060a0203040b0d060801021603230a0e0114031005010810030506010501050c0307120905011d0a0902030601270603061403070902 76
    0x40c010328526040f890184002c200c1ca025441c1510070500d15241c000075184603580c8400344820f0300f542c54200c1d80c010b12155000c0d210728030400c403e020400241d200141112041c4060500140c20f00c0018856103104000c641c0340164010041002516520405031800000c6544d02045241c0d841d01d00c9401c2e41c01c41c0c0e12001520900e20058010103030030071509501290400c406d16501c803558000c40003140541d9580005011041c84485116841030713041d0a581c0c100c0000240d00c90a00e020000d2a60920b0300419010600c80300110f101240ca11202d4400c803a8071a009050030303030a00380111110340142c0142003440c4002c0c490320340040c8003c02d00888a20407a580c5100c1d0178a02000100941169840905180e40c00c40c140109612800120000e42c2c03201c01e400b40e0380c0e440f40c000482c2c2818445074101540f2800c4544480c8122549400b04200c403096602442069210000c174030204281201e040c2d455840700f40d0400010109401410740d80c10481c00300207034500c87c072601c1c45008541d81c0d9105 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 342838255 1250 342837005 342837013
    0x51603050d090602011505010f0c0b10030c05010c0f030c080906030f06030610210c05090f07080f070c111f050c1606081f0b0d0b1f0906050c01020405060c 68
    0x1c80c030036809001c10004003401d1000f1301407050300c0328210b000664180112030400131115400f0000f02c0c0120151104c0c6a40714106030818503194854242d81070003808110b0f08000307422000101036100e0048111210b0f0010003000405889680644000c4808071080380d82030403c0c80702d490f4960321303a409140b0803003c0c50181c500e030b403a11000b01418010001c0c42c004c803020b0b814005000c0d040c2e0002615040041e42c144032600f04e80b4500303004c620009181d101c80d600049a00c200300801c0796025915002e0280c54603818456100c052007040204000c64007240000d040040300004928140d160100c00c50000d00300550f42010004d112074802c06000840021507000a40d034010500c0030050f014005503520030441c2094240100201302038005044a103500d60341c1c028840d42d00c80710050349802001513003010b6039921103808a14014040885100c5e2048285c2c145040c1c8201444440005540d21030340c4001030141403860540e050341001d14000d000d90350038000898241c8035440104070101c0b89a0083c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 342839505 1250 342838255 342838273
    0xd0801350a0512130b0f040b0a17060d0206090121151e060206070c0501270b2a0d060f0b07020306010b13090b030a06050f06030d050909040f05160305 66
    0x902d00fa60b10300302030f404450108020340840d54000822400d0324034804500d959485001c600c443c442c0180e404c001c030104000607035000342d1a008a42050840c4900003010300c943d603403808001d049051010043c0d04040d080024007025881003007102c81800f802207054149031f00c22404141220780041c1c102e40c00284520341400040e0020801c49003580030041c0c1251840c1c245640251100c0c4058015400e00600c0300c103002c02c012080d04030743c1c540e4440d500760020103800d8002903136004c0041c65095440208180119040c20510044628500030346002a5130322000800400c010744d00c0850044443d0355a600c002c00c00b940d00b0300915000346401122681ca414683c01098140030301a8402c1200e540304220035180e9200c0c05a941003200c561403400941c01d075007040801e040104600c001005240b811003005940d840050101c0c4c0240c50580456a45a40390070003901c19218844420754401404030000f00040c1d200110082e15510a8080d582d2103210320050340e0204c8081d400460340ea0f0040101 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 342840755 1250 342839505 342839513
    0x9020a210c1709070e18060403050306040b040c0c15110c060412080106020a030e011e08100501050703080f0a02070f0b090c180604050c0903031305030607020d0801350a 74
    0x6820701d8000b180024085904000d50003556452641c415000c0c440c1e2142e0000e11190700d160009800e44000308107482640c1b8107841e0081840d0f000321810351250b89005000c0c851800c00303206801d000400384d1035140c0310041740d440f02c940c415041d90030318000a0b01c0c0c030215800c031840a0058110b0843c0074005041905091804202d5520100686000c1062001c010001254006100c0d6041a01420500c10044c11000101c658461040340031000e40810f2646421150f8852042482900744220740e805803510340d40116007901c5140380150000b541c1502144043c0030030000700b40c100c0d181844c010326041466940c5000002d4001081d5107070b41c114010400104c13414001c2c07141e0044d0440f400d80521843c02d40786000003c0140c412401507940700700184103d007142c41200c80e8060000c040b01d840d410030f1080704050003101d0140c02d029001e0a00401c0e0700e6800042d01c140c042d500b50f225000c1c141c0c240031584512801c44080200020254080850001550b94075110031160000103402c0078203603410 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 342842005 1250 342840755 342840767
    0x8072d08070b0f06060d05090118030c020108070315050402030a0e0f030301140306190507021515150c030405120a0b07050306041b0e01050a090302030708210306060409020a210c 78
    0x4412110b9500c2001c00130241e940c4c004855001c0340c503c40024858503505035150050030707406195030028a03200401c2060680100300d40c14540d1007603030381860b65540e8610450580310083c031010029098040103008916081c0c01541e4000b02c0400005281a50444c0007454848034448404140d00000014040c00e20001c0c0d0307141c40c24100350000c00f91801d00140e140c1103142003076420800c0c01d59030360124042600c24081c3c0240004141c21445c590308298204205030300399240846c0c499084103140440d1f0107001c10176204103451a030080d41c101880c107410f00017a40c211040d40c0425000e2a98201c5c006040c80e00900d00643c80daa8070302c1e0300e074134103401400115038601c05008107401303285141701156640032103401c141d203000b032074102c2c0c98001848003510f2a00c21508000e41c503005100303020441103400151311b80c48c10398400c00b103a00490307030b00700600d10742c4026940b06400200800c002e00c0000080e400812151603580f800f00654142c070110400d0380c01665007005c0e4403548450008126540c040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 342843255 1250 342842005 342842011
    0x30d0c11120c03031521010605040c08090a0201141e04050f040b0a0b090a0905040503070b011203090603090314190206010906050612090703050a0303091a010308072d08070b 76
    0x1e0001e1600c0c920050a41e42e03800014505003452039011919031140e00d0740c0350040c081c6503904140e1780c02488040034150181c0a9406039501452030003600c11726152250801c1402040f050b009810781020310b400440e0040785081641d03844400c20072603401c900c032040c1240316440c21004243d036120380c1803004001c0501c002c1d604051049091000310180b0760f46401852080741ca85005140c2d032a1904000720304a50300075449084001e00d070008020034032001000500e896480340028404907038984c016074485c000404c1c1d024000413181e6100744003040c001d500014641d802418010820041e8080d041c084e1b41c00903d00711400451400c92000b05901005118090841900300f80101420400460454021207441181a0031500003054180b0b01c01e008940107160004155228284c503410050301400980e0011505a080900712085110051314214142ea600006052600da015100d6098800010501000c50300b4140ca1342e2040c0e4003644401d6500610504c0312985a6001e41880c0103080303002 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 342844505 1250 342843255 342843283
    0xb04020f3705060f0d050a0e010f021c050f0a18060513050f030301060219060f06030c0e0f0103030c060c0314100807050607051e0a020618041d0607030905030d0c11 72
    0x600041403024001d04c240c44180194000014560340c4034030005010713003803c4032013180f00e518104551303c0e1b24105400a000c1884d40c60281d00c1c2d1400b1903d20041101c208641345006403044401003500b20030705070001c200c42c074098a5840c5503058a611280c007103403001c0c3c460381c640500301d00b080b034108141070007110240b0201e18091419980b403d41c1c081d40302d2601149030100245210241c604004240d408040d034448014000c0100b280c50b490301000b100818040d0792a00c00840000400c000100c0c195907050b2645130b1b4070040c0702151540c03520090b21056000c0014180c84820b0080850703044101c0c0c51041c00083c569000c0c062034642050b007000007035008617029043c00c1001101060000403014401242404800d298480c10a8520300701501448003d40c48440003880845c1c804070030700a041a03920860301040050545003e54891910b50341318102140c00040006440c1c5029a02040902d40200250b03803801d401300c0000c004850110b42c01401040f13403944035071624601005110101508 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 342845755 1250 342844505 342844507
    0x40902041d011a09060c060a02040501021501060e04091a0403030b1207030803010509070525020a09090c0b0a020a05030d06031208010617070c080a091e030b04020f370506 75
    0x4150a12001010a0742100f000e80c00004407074030661909411545011071050a507203c60424022030300207580309101e06401840741100b6108201e2030882010304a4070a07844601020b44002c080c00080c0403040300c1134640800c2aa00001604209403500d445544aa9000940d880c0740d40708111303035806c0c010541d17140340c0d02c11703a41440010083c06c00c581c15580100d490b20034a0b41c6200d000c07a11845a113004400f141c0f52481151000f081d45040d0480140c422640880c6060700c4010110407141003070300141c005819450100009400c03a002401031714a60310560b0201149502c8076451030340004100d10b0b0256075091b0410501c0a00d002c0303600c88414130300e460780c3d9075450100f00421000b840140000c0034084000442c0b41280540c540180413540807803000d4417091710140151004010b032046a0114540e401c14500d0089001e1903903054135031080c0046415102c0340c0034080e40f43e100c0f115058020307500308a45c000740c07545e111042c5841c0c5014401c0600c101000e49540d00a440349a0160b0701a80d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 342847005 1250 342845755 342845759
    0x60e010b070b06120703050a050d02011a03190302011b0c0506060f010c08030709031a15040b01051b070e040c0317071101030504110405090115050d0b0402090a11040902041d01 77
    0x1c000d008960486404c880c90707080f504698903290704114066000074058420b4103141000c04c100850380315100000c1c0d40007041380c1c01203000c102c9000310100000039810b401c1070921342e00e000c0740441800d00990080c800024001e602e00c1d406040c05041040340c2010891504480c2d042182c10800c460b844903061307034540780100e40d020010317049003042600204080004030005101501c0349964030011a040ba9031421800318101c2003200d101400e85560048480c1d400e441002410a401040e20000040e50782c2441c140e189582e440302c602e15a041d6100a01079100001040601c1502080c01079004404046000c0c0c603500d8155070240c84a01220040c0741d05110078004140c2c1020508801d450a003004a011340c5c8907e011103c1900407100c4a91044ca484280203207804150b00000c0e1203c1d032100503074403c43d1280108801b80c10415801841f000e90039000900505000390310701d801521805e404648ca640941c40d85080e60010b0b0003140d10980d011408000201105010000f40c504421200a043d4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 342848255 1250 342847005 342847013
    0xf1b050a1505092103070b04020f04060503070504150512030903100605150a0e030a030513060212030403030c0c05071401030b0607050a02040b0609040204080a0302061f29030703060e010b07 83
    0xc060f00d20b01501c2612600440e00d0342e003030f200c200116010103000c25a0b549000c00d02d803501e1521000d42d02a80503140010840c01301e0f040a120315010745200a0080482620781030400019180c000e080c0c610629201000291350349a078030b80580203400400142d40c0b504085014503141c00c0003812400344803410444100000d03110021303c00c500c0c00ca1400840c3e980d220002d41507038440c1d0904031140d0148190001c0c0000e00d68400068214480000d01a0080303907580d0701c00b00d039030381107a10340d0924640381000030800090196101d54101046400c003400c880003240c0311076040c40e40c25071003404101588486000d181da814840d40302c805070110780050030701100b9110555981c1c60004020701070303a03403105041015070380c203401d0304c2c0b074020000c00c00d5503116218591b440c2c81d6840b424045003d4402d03240440c0c8601c08540c415004424040c5103400308615040c0d842601ca1081c0c0110001c102c1d6907118030303201c020000c000b50300ca0202030f240031400902c0e05000ca40342d5101640a10044001130103440001 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 342849505 1250 342848255 342848257
    0x302060c0f0f0d23093a021504030305160c0302090403020a12081303030e0304210212030f071712010303110705030d090302061810110c0406050108040b040f1b050a1505 74
    0x120741c2030ba0400e0016070300e07000e080d212100c1e29205442c81b0004003145560801050042c0d10428404d48803e28100030011210320b4034041d901004011400078001443c40708032241280d800a03000380d00c2c242009036290041082010156401d0300160004441c0c0414030040078480e29000c40c040ca0702c01e01e01c1c90508680c1c00c9040e103903200101050b0b03c5039140710103188100b0aa9019010240400e000c400c0d1075400c00a1000c81b03440100d00902c803841525564100102c00e9803042d1100d80d07905440c0c03403582d650715050481d0303642548180040600c042c0001c24480c08095010b18441e8032154914044203040303520f070642903032005100f640b02e804001069a0b04c44142030480354190b40441c1c450108411055160000b003541070303044200d086255410300d41c0401a00d002c8110802524500441c0005200036a0b01a014282c00f0405050210300065008500e0038ce10900600008002c81c0c0c2590721403840075044034045003081801182800940382074440300d801009940001c0c12104144080a026 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 342850755 1250 342849505 342849517
    0x4140f06030d12050a060918050714150705012a020f0c010906030e1903180e0c0405010e0402090310051503060405070608040302030f0408100605030a0c0302060c0f0f0d23 75
    0x625a220004501c0b880c8203504440050b07c9000c10a2080388140d070382404080d4614281942d06115407500040d00c0315240380c1c00d00002e00042d00230092003120b01c0380000c10380e00800c0200d80c550341e41c450240000580c0400320340c001c0e20b154540c054040c000f01000b8500302d80e040e400084e5800c01c80008001c0d1781c20206880840e0914140401ca0782c01701d90340e0b141880e00e04c6507621203021f2840d0118041607440901621515281040150030301d45030070942a14580417120159115400c1205100760f41c06000003091020006101610f08900c5501013800c060041540c80c00051b1204180160b400c030440f045500030b001500241400e2403d500c40c99912503041c0f2071036041c407142402040a26200b80100e52045040d1010355031f03102d0f80c442d01d0a5403203046003068109903160100210301032402062590f9480d40141648441904540810030345a1207140301005c80c0c80b0b01d6120001c1c0b5401440522148501d41003d4150700740f1011b030203810000c540114010003000f540881e405055040c0643d15 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 342852005 1250 342850755 342850787
    0x1052d0102070f08030a17070e010e130218030118020307090c0522051302121b0d14010302121c08060420030403140915090a030204140f06030d 63
    0x420020000180c1c01c1c04039a4000c081240c0002801090040000008065201e480d6540d44041700001c002c43d400202e050b1650000502181c20303400031036101c1c100c0c41c10305100c0100b50700310140d50303400c1c0c0d4022a80080325010403940c40b500342c44502d103020300c82c0c64503c0203021040e0038500c9032940042e8448102e4090100a10303500d100c00300c2c00c83e03c588103890070001074141d071004450343c600c4550100a201d100e460300c00ca040b50300140c60160b8900a0ba0366912a0403030445154542d00302d80441004c03030f0420158040001d001403981e1031089c0c0108e00200c0127030040c8068950441c01488031849110420b480258001f500011802c00050795400e1003003d54a071003483c94540380001030141c4001e28201401d01d203011442b6450f5984d1000450245119842d1480440300680300070b54540207024105500420748045d00c0401c0108900800c41c2000c0104171260198880e0300080032603008c0c50007006030100d0941040401d100110200350070000440041411a02180c40200310002c0420910 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 342853255 1250 342852005 342852079
    0x30d021b010605062a0109170c01050c190e031c0e0301180f020d080c06160810060f0309080702040f0207031202161410090308091b0f040207140d0e090105 68
    0x801701c0080d8411401580e02200c13484400791840e0107010700c0d410815001c40c0030351030304021561300152141111100502c8901c402e8140810350b00c103580c602c40074241c894140c0100c3c031507501c000d08800c613025000320003510780200c02c14030300e41032508440808182c05000103908a1141c045102c03081c01106099040701c0d03580d69141d9915040c14203004501a00a8521400080c0315054500213560766080185036998032a503076a15200000349034582c0b02d95400701720040c076800507491107a04223740e03407401074084525101059011804481c0340c400910001c4d5404646142011762091902e9442c42116000b0b5040501030040c1c1109088440340003400070312900e444244101341401498122070b80c0c42c1e020444c800c0d56040c081c011204c12901d803100d60003201c440c0c0c080b0313802c0080e0320314030800064500020142d50070140402035000110542d5114210704d00440205410005040139200d10343c1e80d01d05169203002481176410040e009a4860300c0e8030790071400342d007c000340c2001d000c9510070164 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 342854505 1250 342853255 342853327
    0xb0d0e030403080328051e06121f2003190e0303040501060501080a15031b180b03010c0305150f1f170a0902010f050309030d021b01060506 61
    0x18a1035403140794401400f40304048104030b12441d40c1d030340203840d10324007040d01080c05400789107110803100d08540c4101d40c01000542001c2e40703110b0000041e44000c0182907a50a280030002c0d6500d0400c6a095410103950120410440c0e01c1507400b480b50007204140754a410b001241a541416010003400b1241a842c0d051458141500540001210049117400c0e69524100303810454082d107010700070540071038681030106021036a01e129440c0f80a045012003c03801d07013982d5401100548218044280d083c60182c0420303600c02c003942020010541d07100000d00c48c0010002d0600351100d18001505041c600f0041003d20388903540800102d0300300b1548003c90344101c0d800034601d103d8103904801d50034010349031080910f401000b15248450581c280d96880d90b241800385d01603403200c0c1c0d402400a8901e0035801e18060081014581001c0420240d03400c0c41103c40500040b80c2224401343e00d801031001c84249a4072080c0708601c06050f09603403c2d441e00da200214010f802707910100c4a029101c0d10840c03 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 342855755 1250 342854505 342854531
    0xc0a031101050405040f020d060506130902160b0f1e041707051c180b070203150c040801051006030c030501080601180e060f10080c01020c0f030f100c030f05010b0d 72
    0x455001d04130041c01000f607001407082c448002d402001d604684545000c2c2d01281da85404015515031000b207440c2c600d1185d050442c218041d4000318030848520400340700840020b18040d20213031003488101040c04071860700c81080000700c2d85031480b003d0440400018007010030b04503003208880b0341c2003062180d03070b485041c40c105140054034a0240040403900100c5094558405160042841603107103035407000c0e440d5040f4202038441d80d40001d5060380302080401c03c000d00ea0039816400800300c0801c90034590b6845869080d1a405c507400008882100d00610020341c041c454000d20503c9450100007540c1800d0406a80740380600940185021101000800155541252020310f07195010f80e1800e05003242c441401c020261000c10f41e4148502c40071400c0c0c4000036403a01030002c144d00034003c01440006020b07050401d500c4076501800ba1002a90b849002081130704103692004000240f0030303149840040c11182c0041d2080030344d90810004000340640342040c0c41510024480004041e00c00d015 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 342857005 1250 342855755 342855757
    0xb0c03130b1f0906080d1106011202010c060501082b1d040f0e03280203090d14010e06070f031503082505070e0604090305070b06060d02070b090c030c0a03110105 71
    0x810034503004210b002c00300301c03094960405421030343d081045405241880307006440300f0380a010303e06c0e000c0d80701c500100b110824820076111428018141100c85203421745680d81500c600342c2040da510707481198100d585445e034030042e100c83c121a2070340d03020300b800c0e54600401d1650f82d0110013840b2000381004601640d556407190a03000d9a0f034800700840342122890507220b400480203030f20120300000b003142001c040305100400305c0c3c0240e400341d403501240c5c204100044000e141c0c140c9903401b4890304807100710340910410194200503801000c1d07500e4404001048501c01844a90815061043c85803140034007481c001c00b642d501c03452007519a104140140701c00031220702100c90100708400500d00348000410080160b8601041c01209951400188002e6411a0500034001441000000c1c0030840c1580d00b950084c0c4010b180c1c80c54140c005c41d20300d0aa800c094016a0000d4035203041c41040b50342003240d8000941c0540c09428841250b000007110150075100140c00003600c441c007100241c0c4504 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 342858255 1250 342857005 342857041
    0x105070f0f110307080c1201020406050301091e020d050f090c130e0a020306041401050a0605100302090102120307030209031c080c07051204090608010b0301050c090f0a210b0c03130b 80
    0x641101c80c40c1e40e036485c0803561181c030051031901510b05907072040141d550600071134080e02d9868880518691800380298000d0003108554540b501c8061100b48240074140010322529074a031601285504014400d4800040040c14100c3c4541c000481c10344ca6498a400011403c004410009482e690092400341000d0351844001d600d0b00616081200300511b2400740d03010480e072000200569135070a1000b90443d046030144030390055000032501a510320903001010003440c180305a03400c180010300f1000c4e40d0340081d070300200070940224424905007001c1000e9100320380381400303000244d603004001900c24803015241c508410400a044c100744041009084003007860440395941e529a0b600312000140450702074400a5400e00c9145002803070140a82401000d100301c44038504010f00b0700304042004012040d50300600c924a000030700e450088209543c49000c1d002d100c8080045180030202d411004020100213401801400080c001409104445e5070340140030202c0c68595980d4003010b140d2074 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 342859505 1250 342858255 342858259
    0xb01030f0c0f14070f05010603031101090506180f102910050f040f030b0f01060810051e09040809040501050121020f0904050423030702061213051203040309050105070f0f11 76
    0x79000301001b605501070011a8020303990b010121522520440c20384e0b940050107005a030203800403c4050014114421b60540c01c40d0407151540011100319090491420303181260b69030f2a481d070f201962601010f0140000c4080701104040910400030307140031640f18552040100c0403c034240c000c4010740481740540800b83c564104542d1700e2030300c0d00948204550941800400c4400000e0040c018207643e0f001c6d05118080e00000d40c01c0030f05000c82017004141c0d00c0300c0c0da4010010080243c13038480c24140205d000d0f102450741c942c0b14106110903103a040c0c0c4807504000e58040140e940e020300b09044d244e100540311001d80d4451023410701c00002e001d502e91003a4041c3c03030300341400200001040030300e443c0260400c030b01d080b44a030041d1164482c00b5404020b508280c0812070b4004150007810055480426241301c0707400d500050700c41625200c244140801d0040d00003080c0424550007004001c0282424038009242030f00c0c55650207000d100441d0000c0986da0142d01c402c041008a401c0c001c201100 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 342860755 1250 342859505 342859523
    0x50405030c0a290115030b0604090614040606081003060e24040204050a1a090a090f0b0106020c03210c072c1302101d0a090b01030f0c0f1407 62
    0x410b0518080c40d40310740e510b280c4440e0710f81030b040400341c011200c0b1604036480759411980504d0035035410740c050800350f08941e034044030030000490880344601c54000075203084069203d108680704144001c03285135800000500240d035080140d03602290080c0d40589034400000702d03008040c58221460302d010f0440e980f849980542141007646112101d59200b03500849080c0000c2d01d501c0190320455804a07004400c40307541d040340111905002858035000303003e0308400580414151a441c108485d181c030102c4034079056000410040d5410000024101e0003180940740c180d0500c00a0201c0b0407a204a4485600c0003003041003140d0018800013008200180d074801c500c0f103e44c40e44919041182d0700e043c2c2c2d80c1c010680480e07034040702c41d488940000d40c0130303000740c81e9489403200c20355403150b025106010f01036075414130684548a000c0b42d2030040c06d00c0c900204a6100d01e20016041d12203142001148618241400285503070100d0407a4a1042ca410200c0c1c1880d03410b0032540e09880350450103414586 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 342862005 1250 342860755 342860773
    0x12010612023f07021e072d17030403062301180e0a0f0b04080d090309050a080f0d120b0d0812010501230f1c0e0d030c080a050405030c 59
    0x102e01d5114820b0246004030400c0e502254010740741005009446000c01644104d0140c1c8080c0454500050909640800c4660040d0384c3c008075040503042c0001c040300c0c07032000340c6c804c038444141048403000341c11700d0206c00101040099a555407406184000303480180c486895019000c0680b00b01c5161004e002031110303480da103d9007140080c1441c0c82e134460660f454a40669042ca00100b481050194005851502074402d41c55402c40c203d4090000c4e030b4020020030145542000034496800030078480c5d256081c102d860841044401000d50703100c0142c40d009140d00c00b4aa1401052079031241c050350034182c0859851001c03000c01000e410f1122508603010b041c6070b40074401220003a00d40c80a50000d03040b9a0323030322400112040c1c1d83c0c1d400410a002d600e046c8601c40380e08160301412550800041c01814401c641d4021960103064610350840a5921071000c1c070442c00c1031114420b11110703070a0074020301041d18001001076a004002c01040c980d22804101004414411621010100402c441c00c0013 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 342863255 1250 342862005 342862057
    0xf0f040c080708150307030602090103020f030403080603060f13020907020106080709020c061f0b070609020d060f0c030b1c0f0c060810050102010b0a12020a0906060504080c03031201061202 83
    0x1c1003078908034080f0742010300144948118140c00310103e1805000b83c880580b0716030f9503001035000118020305064003440910314038240480514815070123943d0f0000241040d0007414105507001e23002c00c100e4090f0a0030018100708600e0710740302c0194103941c1100340303a50b003207070403801400d15070030410060242c0d880014003200e43350054040c000100741030f142103840d84042081c451442440400c02c1c42d074a84001c21845005001800300c00d40604400b0824080b070b94001004c81e800d040080f10032a41d40e0911248103000703032160003c91070340ba0604100154503903001540c81c1e619003050800c10440450399404110a1050609071281d01031103c044103500d540303029081c2c65085980c600710101460000400358814003a4510400029111400b000e052070041004407840240070380c6c124119031310010300410303a80b141100030201552200d45540c10102c403681405101020702d84039500c107106012150000c684814116403450600300d100c1c0741240c0c4204064081d0005610403201040840c01d040 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 342864505 1250 342863255 342863267
    0x6030503030a0e0106300c0e10210309120201090801050c0304031b20060c0f010506190f06050306011b0308061807020706030c1206030c0617040f020f0f040c 69
    0x143c0700307000307110346501d40d040305070440b28046101c50070b40060250850031b05000e4000820303c6016448181045444a81d17081002d4400c5e0b078101c40d0940b1110080205810400008081072424000407020003070302c7e10010580492801515090200b00d0003000444e8054142c0743c000704402c80c000c1c03245251110710300d11590802ca400f503003c5000c964040700840e406100d5808020b5100342010442c0b41c005102101d01c107260b42500350060703420405d920b4230160410100d101420014000b003141d02c0d00320b0a1080000740010381c8412007021440a108044948402c101074075014613055403a076580100488050322900d400c01e04003034468020b01d090642c0006c1891103070a00f503c011421603e003086400f40b44804980d80030042c0c1212109009a034400d40085841c1142443c0c0240c140c0c40d40c1c11000308880550340100c4100c03840301020004503030043d0301b1040c21419001120b01c10714140d100d154188540d518024030554180c1e84294059076010b500411240e0050010018054201c4000c2d05c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 342865755 1250 342864505 342864521
    0x61b060c170408220b0d050a06270b030c03191703040605061c0b04111201060b040806060105090d06050606280201110c0d0c0203070305010c0203280504170106030503030a 75
    0x100c900d6207407440c01c00800609100300c0b1510000311b07140034001660100200000b400041d0380d16118540002e525044281160b00c81c120003000341e2806110b20301c04011030315640c0d00c180c081d0704100e1b4814181d42c6c1c0414108207003081418202822855403130142d800c1c049e5040c2c000c19000b0040240400d100541c0c0c80f00303104080c04e49c1c2005c44581d00d4403540440d00a0400000c107100401c1c030000d000120030407180000c82d040178003000d0480360880e42807801e48003540c10855003090040b8080201c01c03420042c05410210030300704a4980000c15001c243d0341003000c400a86010346581c0400c0650f250801211256400d0000700ba68a074070160a00e100403a1100d2450015800c8c84001090b2100d214100d0348a240b4a10040c09819208070064502440c003c5041e42c0c140140701c40040440d0003070080409107282a405150744010030150211000d80720b40c84003030b0f84088810301d10842504401101c0c1030b01c40c184800328109103404c18103405402941c00c0100140004801e010100d0015003150704 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 342867005 1250 342865755 342865777
    0x70605130e01061e021f02071106160201031d150c070c0306050f06040b310906050f010902392d0a021806030a0506010e0f01061b060c170408 62
    0x4000880d40f038101c0c1c2e1076006280b6004070807070762401c11100d90842c1e0f004260540c441c0011419020745140001c614bd00110268030360015001e91000466a041c40b4500c40c00710b5055070700141c01140d280346603403901c910101e0184030356503002007850071081c0810b580c001030344605103c010949904c2d041c40a42070541780c2c12044010300c2c0100d1042c1ca0f00d402039011016014006841003180d904214854401404074540b8030341e8102481212041c5a018090030140507142c040392501300614130b00600a41684118041441413200322001455010a046444080d0403010041c41c240d8048200c0c88190300300c4140c062050390301003005420304031200051240f528031100c0e00f080c1c3c509400364070b4004641000b507200043c10280351292040042c0d19801c440d010b02210210045139465074a0075000703800c50f8000070001c00c10080f0701c4406600c030901615552170540c1e042001481454584e44809100408580d241c08107100602d02c58481c46420110485002c0030509050030140300c56030100341401 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 342868255 1250 342867005 342867047
    0x150308030408120604020a1403070c1a070e090c03011e05060a0f0306080a03090e150a03060e060c04030201020d0e0312161b0f0314070510080a0f0c02070605130e0106 73
    0x44e100d45000e10079200011880d44482c07910303a00700a9183d1441d44018101c42c14010201050008640c5242407854412071042c0c1d00001c1d400c1c4503c01408060503030b080b0b07a100b18110b0b810400130003102d00c182c9044848080744080e0384218101e03c05198001c603000107030060404118183d140744d1020581d07d02c14044c2d04c00308040e50f02c1d03d0039107491303890410f0050080341080c9420003c0301540b000c801e078000314461410794040c0d040740014003d13101d1923005591403a1280584030203d6000d03c013240c1c10400503541145824130716800170303407591a50010402072001010340d00781107444c2485100400b1910f0190180d0325148400d00d42e0190071400c8040c1d031140352580004410b46154000c40e000e80d200c41c001039204602d5a0307a14902580c0300080113070035014604002410b0384408140a4044049856030007031171916159200458020320000001141414944590950041070342410b860b41da103400c41c0d6420882c1030b41c025040e004e500c407801211008000060156000c40160083d41c10f4901c09 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 342869505 1250 342868255 342868261
    0x903021c060537060f0806010812030f012601020a09031a01260309130605090a06050604150203090306090a051c021b010e031204050a061407030315030803040812 71
    0x10700f04aa0b4001040144491407070807000d80440315640c0380a0006603488003094103922542000c8180c049940328800700e074400d100512407860144500318158003448039085c00c500d0000b01e91080c4020620500c0e502032081440350401100c58800c400f110b40042000755501c00101000a110807102d1009079826110080702803281003801d08030504032041c01002072514804501014031000e40748a210a99100401101d1199100c0f604003099180004000007481c500e080e0070302c00c030701400400c071003d600e04e007050600182d5200c1094030207507118052410041110707a2000d0b4074600c1070f64906c46d45445588200421a000044c000507028821020b80d60b04040000c55a2030100704031100c0400f617000000d07544200072441c42c0c0c41961840500d80501c90700c228030046411b0401d880005682880000b8062002c0d0912441d450300600d082c1c83e001021860300b0070b1071500d0303004a440003403c064541d040c507085611412a076101950b00502856928201881c3c482c045900c016254a4045611000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 342870755 1250 342869505 342869521
    0x624150201061e140102031b01020d0b03010212040303020306040605090109020406180608040b0c07060e0a02030c0a050f0909010b09130b070f0e0d0c080706050909010b0304020604030f02010903021c0605 89
    0x40983c2c04054103000c1c0c0b04e051900b90307124000d1407141c4a045100c24401c14840d00782c20207080b180d6070412000143d4031350354400b806040d507104030522402a03004121b0000c2100007a24010303445601132800580325140e40b80010041c0900341d1000d50700c4404c400011807201d159500400890350300391180c505100c4001c110000002441c440e202c08a6410350014011501410f5a5035102d82100d404d10714043d90780c1d9805048544000d507030080c0d648464050021401c0030030489000110031108841c4840c40d200004081c41c0b07208140b503000300a8070021540300c83c02500201d6003240010907121a0740f13003060401000d000001810758840fa80e040200d505907018900300c8003d000a50784074407846d40010241302080301c0f489011102032980c0c100000304208180b01102c054506542d0300c03031b5103041c25410010740c1841a0004103841c1020414000141c0c1c0f00001c4508495002d0038200c3d40794500d0005840b070301515800a5040320703048904800c4800d1003542002c00d188980c400f0003480e100e03000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 342872005 1250 342870755 342870779
    0x121902071505100f09020f1620030601080d1b1a0a0f0b010f0c020102101e110a0e010c0c050907080412020c1c1b06020a0512070c03062415020106 64
    0x108a0b0030458000781c0920081d0121b40003089003003002c800070340c0b0b4280c8031000017280880605050341c0e203c3c0025000c400101c0000c03850f0313020046c114002c1a081d4100030070941c0b601c040791900c2c010f0000341b4421442040c03240c14035075082a04050201e1030311010000003507118004644210300d0b01c0c42d0254014422905100d2804e8420060703485522000f00c4450944080c00032043c142e065100e2212038100d030802900410010302240044640c0711507e0502000982d00c0c04080c14070805000c0c0540e5040543c050990004840d00b4a41a85d80310042d0074a8001a445900f1507600102c2c55020400301d00c0d080064580101d00c148004081d40314403400490b12083c0c800311032130340a4450154501d142a08000e0001c440340035055180020100420681c0c0303540381d1740c0c030503405a0001c600310028004103100807842d410703008950b00d00d020110350740c200400e2041c2c000100b400d0703500c1007101c294088200c01e041d2380014080403012400c1e129414507868a1003031030308400560030f1000110786540042 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 342873255 1250 342872005 342872009
    0x21002041202100c02040903051c180209130b01080601031505060f12070b190f08040f06090c0b070f0210020312060f01110d03020301060201050709060512190207150510 74
    0x1280d03241c507440039500708041016400e80c58810040d22450381d01c0569124840c01b80f500d44a40c450a0744d0745602102d0401c5801702180200701149401c1c1d03021400e1800c00803c0f030780307070790f0485048205507141010b03203406841c0f18102400141c4c2c90390000c525004000350b9141a03e00504030720910249545240041c0d5100301c1c0e1854000c11034401e8a544d605104030384110048800c130030340703801c161610914042a000006030030381000842205e02c010726041601140101c03410701d81504e00d03203040d40703c21300c0400c0c1e404001040030741e03150b041405006403200b580c009000c07042001507a841c410f0800c0d034080034401d50180d118800a60090500e10300000c05c443c102e400c01c550800301a9220f00c104200c00c014195402d0505c0140f038000c4081003814011f07259150155200140c1365410100002c0c02c4400051003242403100042d0f0a10000781c20005590181655a00500440e610030b402d940040c0c5200520b82d03d02030001c56034204000c51000080140401d00e042000b0a954007060100820018 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 342874505 1250 342873255 342873269
    0x180c090103050414030f03180a080a0804052a010f091203030e1014041b03031e0903050f012918130804090501030605062e02070f0308040602100204 65
    0x400580510394042e42000350b002d4011a00380800c1140007003041d085901804108542c07020000c10002e418030f440c0124514240a00300420b00401d05554802c643c2c410b000c80034050007a91400141045410049540d0390400401d10380b004814040758444100c00c00809280442d0001346501601817103112041c04813683e04009000d4154181c906800619a404682c000d90094994a0781c6291144c020701030100400000c1c80e0035494103050a80c2103181c1c1e030030012041c071030313000081000c2540100c0c04800034144002a240661480209580016a0b03a00062030381c020344440c0050a2819404400c0c0800e2042441c0813605851000c081501c4909160795800b240345040c2d1264506048140c0341c0c0001c5460481d01001801e888900c0a60020b42c80841c03119150300042c41007009600805401c034009860602032243c0307001d00d203503070a01c14201c03201000b4001500d06408500c04c00400d40106064810990101c0c1c4034141034801d03a10900514025110740b030700c8114030307400b648210741c225414 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 342875755 1250 342874505 342874507
    0xf1b0d09062c010e040e120301060210020f032d01090b03211617280203120103081303080d020405150304030507030f03110c0a06060b040f0b03070314010303020606180c 74
    0x21100c015504c402c649000560020b541d03c4111340c9030300d4204003c687c0d8441c0c03107855940f00e6141c000700900d0000328080c21301626005110311903c04682e50309a0390455007041c809030140c4881402d1055810002c103164030701907415000005c030b5000c1c40e409412580c00503002c2c0e81030301d00074140805078001c60030300d001e54090041143c040c080044e10400300b000c9210710254844d454190442d2441904070409680c5640e20711010804001400240140c1e488858006141418210310600300007080501c40075000760b8000600080040e102c82c20a000380d6444440951903110070600c00000350041e00810303028507139004c032010015030108c0940e0300c900c2d419034410b458802c056404440d0003540ea215101450303162040e42d6407a8080070701810030b040d1903800410300c0e200e1070b0500703000707440e9250310100040600b000144061400c040050040c2c40d02d198400c0c0d940c0e251408224014026126010120740343e03040013000301903000c030b17000303004100803241801e020008021080c0d64550030b545455144d58 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 342877005 1250 342875755 342875837
    0x2070f060f0c17060a0e0103150f140610030b040f200702130b0d0f05030a090603061409130b0f041101030513020103230c09040609020a02030f1b0d0906 67
    0x2250b00c803020384c80300020700701550303455984074112942032081c2c204a611091003400b50b4a5508944100701d410b0032540740038485d500c0d030300600100c4007501424150154036504c64220741c03140250043c444070a4094410402c5640c80b039075150051200003099460f40c4150200309080540c0072042d50209a0000c00c581003035000140d1004c004e007a280c05841d000008000c0d81e10100d0f80481c00148098001e00140d43d40d900c04000c003c26030074664200c24203145c581041802402c1a910001198070000d403400d510f141ca0342c81c8803c0b81d101115074010070f00e41c24541044010540d9113031245c02540306140c0814161140401582034071400c03184444030300c030001e55000c059803280e08042d0f01d0308c0201011441803040c02d8005040d03100c04440c41041008001400459414144079400061110800c214203042601c038000b5228403401c0d81000c0c2203440030400001c10560340c1c004025420001085604a42c052403005d84004401d101d0743c0c1c003040403141049050b0038207041900b9000d003031151100c42a9 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 342878255 1250 342877005 342877037
    0x1050703180909170301081509011b120b0d0b0a2703020109020a080a15022a0304061403101725050a050d0f080c0a080c0127051f0f02070f060f0c 64
    0x1e00102500040c1d901e07040d000d51101034510391503c01d04410342d618082c241c041c000d10405c0d91201d20026024000c040cec030400214000b135180d40e1f0400301d40d20005c507119007040c4489140c0c803000b81112a1591000f07002c0b030300b00741c0c05500c01896580f09480501c01349a0302c1e084551a81080e850103402c04007146514403180081d68000e240c074102500f04a0365008652640050325008407480c40e02c55403000500380900c41e0401c0e5882d00c03400303203a026145907152103c280c80d41c4102c584910041109010405104500140607018001441000c0700b6050fa0391141c040302d00c419144a0b640c0206003001e00422981131401e60010507036003082d802d8200749190381da21401a8000c507603030916402041810b00000700550000c08140e00340c00004586051040e0850441c0214035582c0001110825040c6001401c0130481c10445081c2420002c1c030300440501500246c0126000c0001e0107100188003410000b41040b403400042c003d800030410700d81c0c0c200c401c80445804150070740104003031080030326040c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 342879505 1250 342878255 342878293
    0xe1504030302130308030f1504060501200123040606060302161203020d1a091e04060b0105040308031806060f1c290403020c030303150105070318090917030108 70
    0xc00d02d0780c0252410740d0740c1c5c403071041e0340d0004ea0346108400c4400060202d80c0c03200c44410715a54204903000c00c0031510300710003e009141700040480070b0b0842c0f000e10f9040c00d0001c0d03010803c4540d150146400c03925100d00c0500341140c080328220340840c0303805008100729120b4400d4907141c0240c0b1007480c0c03125803661140c2d61b042550440410030180c013004041005100c9c0d005000c1c20000d2003020310846568481048000500280301d540703c203100071107600021040f2080301c0d41080d0460782c0002c40c450204012241c80c03150f47c0000c0e00f0500e000082c09545510034240310007986c5010f0a80d40192100e4040050307002c1e45020441e030180b005146600003011031440d82d00c4892042001e0030103440350b4841c812140c07800044642814140108000c1415014407800000d8001180514510b140c0420f4194a1880c54003446041110103d080010140034040d59441c400d0303009600304042d0358070b145840141a4074001102c2404103081800e03200c207800c0040c7ea069419010103040c1c0c00300c0185041d0701d1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 342880755 1250 342879505 342879517
    0x20607090b0406210e070306110f040e1003120503010501020f060601210f09030807081803180409060e0c0102120304050303010e07050d09150506061e2d09040e1504030302 75
    0x10b6000d05040c22025001c1307921500190b980c8401c050000f00e4a14240201120942c07520241c0814081080e5091140704204540c10346d8201e40b0a000507403260841e50021840d6a04000e0801c010075612082c40b94002000d18100c403403d03402c50f01c10843c0540d00030346583c41512000e012603999040d449401082a00402d945100001c00003410540460b0240030744640f2042074020680d058240880c09034401d41140c0c0c440c060200400a40900031481a42c3e48215416951241152100e8105030761322074100c6000b058124a0034400300d130003c0c0801c2e84503074814100b9405441003107900165114150b050700e11968000d000345085a103002100015280014074030020003000300322405040300b4910510740518011603800b0580204040008100d034000341c10284105000e120000010081d9203116482000d81c4185c2521174102c03201031800d2049460180c0c140302041d221000c21070400b900540300e030361800c0764140600e104c624603d503111105c41d01c0700c1e004504c6120026021030f000c0d40040403 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 342882005 1250 342880755 342880787
    0x50a0c0209070e03150106090b16080a140d0c110c09040212070302180a0510030b04030f2109050d0c260d02030708060a05010207080c0f0303070f0f03020607090b0406 73
    0x16003001c03d080060308185070b90001c1c02c0c03520035090050091030352040007100039042900031289040700d0609000304202166000500100c00051070403181e911442000b44500040c00300903440c2c044003071141c4041c107103100001c00066481c41d440e076860000024808035102018003076555507200c0307400f400444407089041c034100e4460100000300680b075030140d6017840d0784804695051803c08401500c10386402822091000158400510110710700c0c2c590140c015a241c01e1080c071004030200c1c1a10407000c03480d038000d05042035035110786a0721000c1d004480601c1c4204140c030140f041e00c1401f52500d0310324a0001e0b0114840c1c0c0ea80720b0800104071854070000c410901542c1c101074410001100360b9000700d440d103000070341210601803142000d031100b4016003001d0016084280c200103005a9460003500c171188661045180503000d80c8040c8101c03015217401a008003c0040c41d0300b0701d100034082008044005204000c009502d00748200121403d41e0394040b0107924052030440b045602e881c00c2d6907070030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 342883255 1250 342882005 342882017
    0x91905010c020411040506070b1509070807050a030b120d18030b0106111f092303160c03050d021501320402120103031e03020f0301030201050c071802040e07050a0c020907 75
    0x200c0d4642da1a03022342a224032075410007c542c58a0340350f4020002540c4841409084078071700b4018400e0300040c070f1903840740d61850281d4480072003071000c40140070030525164001c08100c0d41140d5102000c03501c020580303c180c980e24039543c0e8802c1c180c080218644406466011200f005006052144080380e070b1514216040780c06e184030441800300800c120011000810380e580c00c1000030840640c00351541004000c010b10b140700074610820b901c920a03c401a00017001114804003004400900389000d10313044000c540c1c42c2104060042d40c1d40c0c0c1402c40610400c034a00e0000034110030f01080e20000c8006ca0001d01c000c012030300c1050812107119801c55540203400b405088000c0ea40210414000c502a944400c0c1402c0488844510300d00c9014184007050300400c450150508407c0c00c6130304403942842c1103591a401c001c07041d0b08100703040c0c015065490720305400550581c05034010b442621a020051407564403410402e542900c905092000800c0c0c4540c4104054544000400d9205107142899 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 342884505 1250 342883255 342883259
    0x7030605100902190e010f09090c21020d05060d0f03030207030903080c1c0c0209060d0203210a02010f0501050906090a02090303070807050d08060105190e09040503091905010c02041104 81
    0x1000742d8004c600300c5410741c0300341d8244d140940c3d0300000e5094040000e003003d0309407903a041001002c8041d20b000300b48866448280c40941940308440b810804040c01202d010303018249120440030394070095501020078100310110f42c2d03518103c0305180840fa4401c8401c1581c400c6030342c05401940028405030207201c4001c1000010407508001084102e01400240c92030003885040c01c2e482c2ca10101000781008911050540141c82d112040d42d00704000b00c60005200c152440001c0c0780103000000480d6054103d000b01c4035041004010309200380c0107070000d00140c1444840c8208541c424403805a00c50f00038004290f940c1000c594003500070140c0200545800d02801c0400d00d990310081089980540000f00380d81400360511501c4d50345801840d05120360f050803c002001c602409441000c0c01000a03880b001c124060400d121030f040025005400307600e402e04103592039802240c030f498010321915040c5201000c5201c1c080090301c2e01610307102940000c94084c4402040400f0300400450010000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 342885755 1250 342884505 342884519
    0x12071518060c0201020601091a04110f0a080103030906021b0906010216080c13090b0f19060b07061d070603020c030d0f0e1c08060d051501080709110c0703060510 71
    0x10040c041d0105845480c0300d501540b0009141210507406000c015241402e05a255a604194140640300440e00410340721080041d280c2c0d40e00ca0a005401ca0f8070000805454040d001403040e41203d010f5200e1040040e039a03002642c4842800022003000ca0242072004103600c0c1c503103c59504824113104440d00b548083d170549100030800c4c0c100989a501c42180714610785000701510342c156051041c1030041d0307112552401c644090107071035130013564410000240040e044151206ea400c115000a218455483c0c4102340781d80d001410540d40035080c9031150400c03031400b64a2400c1c0c3d80c4804010541c040ca000400c400035000324460750325500040008400074449402000301407249403000299510b00010750600d801560700c80717a812105886c0c44200c1c0c1d203400158541d8080003c0e2a0b00381366028902d00385040150001d90001000804400820341150015440046e039502d50003c12045d00032000201060140070410060390b031110b4410700c0040c82c59040250850326230204402a83c1e00c800d1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 342887005 1250 342885755 342885797
    0x5070506070207090e0c0904020409020612010b040501081509060f0d05072c07090303080c0f0711030f150103060f061208090a09020906070f031b0b15120715 69
    0x100700300141d00c004420302c0003040c3d901c504c482103012440102081e8030030002081c240740c1d0040010344140c0d0366412400070f6407a05070490b0712090304031070421900d41e112400c40b5145d410501440e40083c014000050a030a41d007601c3d44159074005001c03103016500c50341000203180a04480039081070b4690765400000703000300503503030161481c081c1600c0700044440345c0300c071515072543e500324100e1044028070070f0603a04102c1c5c0605407a0140340603412942d40c2c082c1c11217180708010010300954000035902042c0706488150003403000086042ea4103804601800c03995941e510302c0f40800140707800c0d0040000414079441300d850070300203070f402041075550350034030142c002e00b070013015604824006a07101d024940008410050f0038a02000c50506048101249490164034030042420005c5c042000502d03006422038070340760a900146420701c901e1b5180405080209490480444080300c45071106450300d032000316103204a07000180321359881c0149a1802822800c40c0c00180304180000d0082003403641c07 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 342888255 1250 342887005 342887011
    0x30c3903011107060b03060a0915020a0201020f0a05120f01050102030409051305070f0e07050313030302090a0506040b2203030f180308040603020c1905190201051201120218040203030301051005070506 88
    0x254000503441d10174024542003010040c20000811b11300b1208c1000125040003540300b45102800041c1c80e5107118000381d0081c810f084080b08481404a04400306c45e502000901241000016035146c1c0e03140d0311011340b1042c0081c0980c0c1d01580050209000c0208a40c0c40643d01103026100303c152441141ca0301810040b598000301441c42003840180f266910915003507030032000e94940145145415403002258045500c030040415800050300c054540d1403103e0071000cac000050048c0d60710fa9680c1901c1c44940c1c00300c0c102a00d115a4028581d081c0c83c1e1111800040702d0301501c4010726000c1100e011943c40c1105500c11040306200d2380b02002241224020300301074221500c00582c1c4062444900380303013402d031117140152042a4038000340010004140001110f58040c003038000c1070010310050749c0d1405180003240300324804400009a0f80b2001c0d11201a8600a036070041242c4090728451102040031900a50140d20070030042102d81091a03000c0d4104001c0d103031042c20711007907641d074608150041e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 342889505 1250 342888255 342888263
    0x19080604140a0201020c10030f061404150803073215130c0e07050c010207120329060f0403050f0109111008040b0603031b030c3903011107 61
    0x2010400c0100701c9a00720454800c00a08001d111800c8140d000039590701210004901a40401001d221a18000c2c1c10072144001d0603681884481d8942c103c9003008412021154411418880e05104d4a8113101409082e104520007443c83c1615548400100031801c110315006441c0100c42100415194440e40c180751040c280034107a60010400d0004420f880608200d0106203610420340c0002d00801040c4200c0780c503084107801d00d50f50381c00140d8440c081c02a4a01540d400001c2440801c0f0400d80c032700b20070407120744007000b1401c0790b21318001410448049804030306050480f266001d140007409400e034a2403a15142d45050740365514282000907035494850280e4443c000c0400b04242a4802c281c2c20030142d412123022040d5110003840ea00c8090710140c40000343c0c00201d50603490900448182c0d0700e0001104516601c42c551096403035101071120401401a05130400343c1c45500b841c00016502d04000c004d03055249041c1000c000a20780c440d21f0f41c075640c0c039280740141c60306e1040035119803406 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 342890755 1250 342889505 342889513
    0x120702010c140d030b2704030e041a03100219050f07080d150602010b0d030513030b070f030f0209060d0b03100e070e060303030c0327030f0405040e010b0913021908 72
    0x31520081c1c195641e0b0581548202c4c0ba0100741b05000d4080d90000034407100b01908004151902d00b000d40f9a05584031001d504642010580d0f664074862800f110040b074025030451b90554001c003204c400300c2c010101100b015a800ca0b0341040300343d10a401400d0b81101030311034945881c500b5500c005039540700300b43d1102500d880e0b000b10b8002c10406502000200481c2c00248031550726000020300702010000b0090610801140c039040e200b001e0090300014561040102c0400e041c002d50240590702a0030014000034140308002d60380190034020344131055000340000b801c010042ca00c10380600400ea98058240c0b00b1404500321003000b0b401410120301d0b26601134090103007000362000010300e0003454540264001c0050000b00041ca9044983c00701c1030192007130540203803010203144d40340d9581f0050700351b01c0003080386148000711000034011240212410002c16050300315850a8411b00300d48154000704100025001d100654503902250384024040381a00703100204c144080340c01c98100826680c8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 342892005 1250 342890755 342890773
    0xb1f0e09010e07030302031b010f0c08240a170f0106030c060e04050c0316020f0312060901140102071509051305061503090a20031005060a06050408120702010c14 71
    0x30a1140344051000c2a000e8541c503821928042e650740b003544441c680d548103503224108001020340c0300020300c0110441c280a4031454a20003894a01305951012204170140383d600c00004142c14009100c4a002d401c05c11424603200e000c030310390200182892518010510504025003084c031486010303600c2601c59000381d60401c1001024000d03580100741c092072802e41841049110071050365405105480100d90702540c81008a060011109040025100109002d8410503050b4840342c40f41c5400c3c0c90b6031240d13030b0ba22031554020034503200a84c2c0c00f51f0480d0909110b0f94902940120b03404c00742c3c0c02c5c120300c080c1c1d40d00007044001c0031044201c1c04080d500c1d03040c80000d14007070075080950060140b8040c250b0a24a40c0710b030300d9001d140c40040c6440c420000c0740400010301030149070f40702d6005007552101403400c1c0600020344400c45280e4030422a480010540c28042d1084e50180c0b8802001042203000200100669610080b02641840070410318440026040c640d202c60740c03031801001d000400 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 342893255 1250 342892005 342892021
    0x315050408070204150f0906061409010201110a1d01030b0f09061207030f060e010c0219020a050402040305011508030316032f0c07080304060c03080a0b3105130b1f0e 73
    0x81e1550b0010b0f03c03024240030007001650350103c40038002b6055550300c1d07541c0700020700c0140c2c0100007506491800000100f500e0220030b401c440601c8014403030301840040e119036500118100c94480d54003d50001c0ad441e00401d0324101210015400500600083c52045001802c0c40c5003041076841112029824400c520401169008071701071a0030400081c0203140c000b000280d19140c441c03058000800228610100755554003013a01e00800d4040d0046550ba626400c10700d000c2c01e1000820b40811001610008035100b0000c1120303c60700b102c0d0b944d0714944c140464118082e004a03c074840c0d0340e80440481803806002e5014510344c00d54850b07200d668035010005440c0c1804a5548000c0c22a04203000c20020240c2080c226201c06074140f40402a554030651b003d0001d000018819070450000c428104200300c0284282c80303200115403503803d40d960301c00406810f586085881c00d008000c1c884913000050184100c0711b81110b41e10000700501000c00c03907003901e0342641c0d03400042e0b581c450005000b426 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 342894505 1250 342893255 342893279
    0xf0207030e04090b040b04081210031e08030a1d01020a0e0a08240601030e011514060304080d020c0a080309070e0619060806030a0501050f1807031505040807020415 72
    0x45041680c2c20b00004600380c0b0f9460241c80c0050024040300b001c0400107080081020894003800c1c0176080d845d40c0c1d0304203880d01400c0c0c103005000449600f000b10500da9286e070151070440c442258001c0c4818515904c1451883c0035041002c80380d05c141080614000c1400005c1c0060142141d443d40d0703a00c0503150b41d208020041a890740300c10043e402c40702d6020181070b0360424031f0298280e512100040790300d81d0030040f0004d081a6900b01481e510344100c407801035044494140494400d0310003100144810010041d81c0c0c80103550013406203c04012462450300e8980181020002c210241c0c3c418082079200c0344420341c02199040680d030803000703041c8441c1000803001e40c3c10080554111100007540036401c0d500350194000c00061141100000d07030650b90400042030381d160701400030701203420000005004400191000d0020711080741c01d180716882d002503807a0480341c10810034492102089500030050a0181c41a21004804c2020b40c0241c0c50301c2c041d1400f120122054540c4442c0741c40c45030409 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 342895755 1250 342894505 342894527
    0xb0901050618100c12030f0c03022d091512011a07060b1903050f0c0d05060708060406050d030e100f0c02090a06030b0c0a1d060a0806030c040f020703 66
    0x12560341840701109481c41c4188481800c0401d039600403128062a83c00d503800c0c00d00c0b10004010390030312150303656035517810b800c0410701000c1d040301440000100c010039010390254a03c8807019016810710b42854145210000c00a0810001961300c5c001c031090101d030910080704203190310f0040004001c51510951900e80e0f004001054984000c040400480c0c0c00901c038408c8090300080d1118100b9010343c0c0e07060001070b40414580400c0025603900e14000c0e40384d41100160ba6100e024034035207840d003401d1200a410405074003001520007070380ca185c81542d44083c080d121340e411654803040818281c4a03041c0c01607641e030180d1680d83d6124070f0b91040095101c1d04003004400c001808620705155508000801140c0d0307411500b00f5a90790300c0880c9071005110507400503200241890500440ca41031b074004124410a56455030009a410035445184441900d449a007040c0304010f4007200f0351090140d40e42001c00101a120141c400c04001340075a00e841d06481c40403030340011160100360300034400d03000b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 342897005 1250 342895755 342895759
    0x10f18201915080c090f01021507111501060203040618150305010305010b0d0203120f07080a0801030c08010614011d150421020a03021203210103020a080309090c0a09030c090b090105 80
    0x22482c0b50003c2c00f03240500501c0026030086c0751044090340785a0080c051034156000c00c0700074640350700e03149030014604490258035003498010404910401151982e40d107040c1c4074541c004503c1c0c945400b104850019409106c21102044040b01046440f403804a1000c140e040b954082080d50443c10540d0855880c4c0001511803138484d15140c00680b000300b02003a0065543c1c2c0d030281c4525138150710742064412410000d14099001550a07091500660181d050b64096645001d025860380507003400c031350329070145045a0714035039401d6039070350300c2100030a03246403002c000082c4084040c4c0105005034042e9a284952500c041410304c000e801c8404251000c00300c1c02242410384400da00855aa2062800064041d10b03584099121a680800460301021040940c0c43c0340ca1104a510a0614000780012441041071030b1000a11090010035154400070040001d9080e8a9500c44001964416203044c0c00b44140d0300000404502d442d0f40310401800d8140380424611a11010814003450580007a4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 342898255 1250 342897005 342897017
    0x318030702011d0d02120a0501050105010503090a0b0c0d050f01060e06040f09020d090512030603010b04050103050c0d0c1a03220312150b0417010f18201915 69
    0x100076030b80c8201800f140281074054480742d100180046a0342c001035690117900280f00200385490690001100148140100020000c590b00e540045078944000c1d11343c80180d42c030841682000c519426003164000c14020300061402001c620b080d019030728222166503e40020400403c01c081c0c000303c4140c211841118594a058213010480c15200e840d0b00640da50a640440c4506000e030543c3c0c0580b00c0300d074001e801c4651f1b5800c044845d5405500440f4401d0081d402c0070f454800506080c00f80d18142d130751100c09010854486024444042003251058400c00c105503800640303c0c070541d0003020b001d000c0002c4680d4914241103500c11110907a0304506130b00c0000200140401e5100c4000311803c0c5604501180c42400e10407000340d4900305800004031148000742c0005c07490070f42c040e8078031180901802480b060100041e6102100c00f8034201142c06c80b503c0700d45030001102c4000f612888400340303040c0100e171200300011540004403c11410340c1d0312030b4041d00307208243c9842001a8942424a440 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 342899505 1250 342898255 342898267
    0x9060f090605060303030106120b06041a03040512040f051017090705031903050405090411180f0901140705090a0e15030f070f0b090105120c0315010519200a08031803 73
    0xb42780311031490000c00305580e51301d07807412a80d4400b07040300c005005038032003501c0e501003a843c00c070515403094800310342a101d45c10203480e444101e8800d950454002c620511007072413810040c8003038110a0000e120410910b031641f0130203c074140403c10f008502c4c14006116007410a02458034280a1556840c0202c8205480c500020b80c4041242c0030703501c05407107e40c840d07140d62070800c00131b14841092a81c03101010528441c0800c1c4003119a00c6940d00e0f031900d80642c0c0303481c0b598508840096000940781e8035001c00046089005130300404003810060020900aa66600d0021209005449601ca100c0d002c0010300440d24003040559080d001d540c014102e6580303000341d10b81001c000d40c82050000840819120f489070301440a0f922628003408160300e05181002d00c929071544112014031040720100d000f440b481d4404c0d42900e00918800f0b60004203500300030421360b424000d02d5030301c5100fa940c442881d4800d80050014230030052041c0942a10f0b418000043c0c1101400403c01c4a00ca500034400 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 342900755 1250 342899505 342899507
    0x1170d05090310180b09060f070c0c0905060f03030d020d1b0c11040e0303090d02010c0c050a0605060a120f02010f08060f120c0d0507140d02010c0b070309060f090605060303030106 79
    0x70750b41e00e9602d0303003800075040345000c4c1384511491000300081e0541d10400d00f0802d074800046540e0b4480c10407480c0484099884000a5841d556490400343c20004580824072080105a00c81fa03009607008105000540028000078559400700d181280344a8000c184155804a1405901c12041070110006088950420000c143d00010700020708880b003124028049516a035008281c4c42102d1020749549140195000d95200840e100180040d071031301007806030180c0f05440b41c118080e03101e805041c0044075900d498019060103000070b68001b030302041c0000c2d00c202560040c20750360700c41c1003020048d0000b400098400c00440c1c1800d014480744100700001544c0710b880070042e4131402c5424900c0006203040003031a04c0d6040c80b405800070300c00503d96040c400300207a21001c0b03518642c0c402c0180c03c208018494400b0501800074081004181202e002408042020340c0c017141514000078042c1164840340d0907118001d01c0c001c03030203503a1b074079010900c1070500842d6032000c410740c010352540d49803100c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 342902005 1250 342900755 342900763
    0xc100c1e0203031c02280f020313060c06060b0304120306090209150d1b020f07090b09062202070f0b13170901030e03220806090325060501170d050903 66
    0xc00e03400340380103103243c0304010b14131681515065160144a40000540b062000440882000c01e031404940340d404100d039054070000071501c0103064008521400d030300c0c104040c4c6140360480000c840c480c0d201c410104000b41a4000b0f5403140e402800b039980344100491000e811100240c00485d0554010801d800040c0c40d11800200c0000d032400d2811351384d034060203040009050001c46194040b070740c042c90401d0590f0010700280e03010011429909410380d101030000c211a0000c402035080b2461000040103403511221442401c1c0340d0301c3d01d141c010b4101950000880e80325200c00ca40b001d48030711000041c000d0880c4101d0703009203d210300000d406002d8403070290b11340b4050400e069582002948100c2c1d64403e80080000001c03140c1100c0c0c80d01c2000c9101407094854401003079090900c035000242400d40010304502887d40720014510740095905008001d03280302441507410182d01100380000f4049114481c000d14003c005803403200808052a42000c4100d82c0f5081001000c0c000c4c14850b0350082 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 342903255 1250 342902005 342902017
    0x708030f09090114031c1107030b01050f040b09041209030606080d090936020405130b24012a03110705100806091317070b01060807020307140c100c1e020303 69
    0x100701c0c00c403072411780d1004487c5401c040910000d18080d15030004204102d0340c4541d8140c41c07040300c41100344480300007030200f11041104e00070ba2003c010004540455100340c40b200384440b292130060202d6899444240980d000755000e080541c0c4040c4911000c03a6214200c03402601e143c00d018450b40000c00442d642045a902c1070ad01801c21001c1700c1601e500c00324013005982640608180030394904a00004c06011201000b03840d80c195600c0024240281e84100c155001d41c1c1d01c00811144d04030074011110444d4540c00042c50424075030506141ea00050303d460403040c82a51401421114811080d0510400e50711130f03400340c040340f17108072105600720405590202c0c1c10f941d040c010740c2d207541d20a00b00340420703c00500030000c01030b00c8960b02c2080e400204481340c00707009900607999070b40c002107401002c212010001a0002e004000011340c81c03203043c2c4440107038070048030601110380c0c000484644460102c0c0d404200400d031480d0030014450a400030f0700f0180141d0f41140c500c2c80d00861f8480c4541 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 342904505 1250 342903255 342903283
    0x30b03250f081c020123100e01060804061a1210060b1305010e031c12050708060d080c010902031006060201050a020310290304060e0f2803020708030f0909011403 71
    0x2a030385083c0c0840c03003503000702e551441c0b11079003044106003203211141c1c400c801c1c0c6d06024020202c0340c0201d0304c504c0c6018201d040b107940d55140ca0311550759495400040c1203245020340c803094190305000c03050352407403041c00708509140c01a04c0c1c40303284001120101c0b505540034030030914091101a150018201c1c00c40c2c02c0722401e00780790014204507000a4144164100d204c00c454071522070013880715500159a80e0300d014400020040e5444034072095403094070442e1081d901042c0c0508010020b00f031800604800c105040c0003103112005680040e05044100300780480041d81c90a0411440b81c0c240229a0002d0001200710b01d1401c003018031411500c082d0140060b86600c201030005140a0480c0341003100c0c14804250b9100d042901c1c02202400160725022a85d04ca6101e0120201801145e452304030b0301880040c41c000c2191900d8020041e000300030560944c0605400000d000e40b0920040250307000740d5030b110b99114007000411259030410b0304104191031800142c9506914001280c078401240 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 342905755 1250 342904505 342904543
    0xc03020909180613050f0d02010e070603020f04050111030c011d0706091401052104060c0e0612040209071211030105030106080d02070b0d060312080405010f0902090c0703030b03250f08 81
    0x46410030504c0c0c060210040c4045100e0b030f10100ba02288e0641c0240b032031f2083d840580e81c146607600000c030b05034004e40412010b4000300704410030240d070151405001860420044d40c1c1041542e01c5203a007190011075080c51240803481c120180c040e02400000040c0c40c172400e10040c914144201042040c000141c85810b024001070061b103060800441e070f02c01241214011590313450f00340340220180c4880c013000000700e00301c49454541403510382d040d562410240c00d4040c0c1c840d91369808010312400050103080502c4080802c2c0040e40038a409141c040c0d82000009075034035494042130608584403075110154640048503024402903020402c1c40807100e8001059403540c50502c1001c000f0725150384000c0c03894200c00001e900c403a402202481c4160701031402004030b20f0000f00940269100c841000f9440100301d000120b40d51a644040c141446c02440c4c00a04050360f83d003c81d140a4090445282250350034a200d00080000d408a5020b4500c0d0305100100a2400c1001d9942d04104510b000d55803007 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 342907005 1250 342905755 342905791
    0x90105031207060507180b09041b0c12030e03180306060a030201140c012304031103031e0c041208030411040b1c02030c0a090b01080114030319120c030209091806 71
    0x300c1048003559100020000d0f00240e0f0347da841190781503128070740d110b00030342c180101c090082480070403400f0608069140c29405a40070382e246078108000500501c1895621101d0b540410310030000f811070744151050303601d09226900d040500d4030400030b00262042044210600c0142da02c1400c4050108a944c080b0351204000000240903250032032a440c0780c000840b0030004c0e04440000d000303006030300984418007a1501030341d1a54491100301c48840001c2010343c0001d80e004d60710042c9943c000701000c0802c1c1401c0d00c1f502c26003202807450f00190348100011050006201c0100345460255504481c100003600402d004550b1415a03045e811440418800a103c02d46d202401605428600180301070300716a01d80701034070001c00010181e6070000e64600c0000c60707030b0f0b10202c83e28000d181000380103608040e14200c020140414800a00003044034072007034100c40c0c5125015003050b942e443d07180075803141c059809102048100500040c0b61b43d501091040d40c3c81c401103100741d0002c1c0c081b00b000104607 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 342908255 1250 342907005 342907007
    0x403170a0e12070b070b04060b0a06020d0f02030d0c0207060206010b0a0c060c0509040915060605030f04060b060c07030809010f0e30030304051b100e010509010329090105031207060507 81
    0x200413903011000d59480042c0b400c08000e02d60700e04501c264843c44081100e041400c051181407030aa00440d00941c0c4204000d112650203650030500b14a22807040b00d1410006052000590b010302c5206400b5921051051105540510619006d804002c00310313030508080003401460906400800f030002a615981c9442c11485a021100044005003090044100904d00101000750003140a242140f91000c046001c9115804880c001c041469010f00c40d521151100001462803801c00d580c0110200122140110248140302c0118025020307551200c3d01000007402140c4034224580420034090f246c1111070351280901c070b540d150380300404070840e030fa003a500309603120f8000b18006141c80b0100800040040004130082c00c5105800025184144081032100b4514a880c0303c0011420b290005d8055520810141c0440030052501040d0a0074050f04604000c400c0302c101541074003416170040807800d0074003049005000035001010b0a0100c604015618003848000900301c5446902180e403407 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 342909505 1250 342908255 342908263
    0xf090609040920030d0e0f0603060118180f0c02190206040b0c01050910020a0f0e010207030f0501050601030506010936020a0207060215102c010b0403170a0e12 70
    0x31562104444290201805002c015424144583c9109200c0c80c0807550407a403240c4c041411090000e1701c41d030fa2500c030a90802c0001d4100402c640d040002c27040020301e062041144490082010030540e08808c5206211442511350071444682c0311810408510101030740028240f030f1809a0814810005130700703100042c2144583d51001075204000700704007101d444194480b038012614501140c1160000f1a621800c0c0c0c0030310a0903401103950150f2814500c0c0c02952429281a01441a40d5000340c0380e5407149900c09600a0507143c82c1c1d0364900300300c080d58251044c1034000c1f50909106102902d0071150301e69666800c030301e0030340d11084009401d02c40b00c11000c07403003490100c0481c00e544442008600940d20a00c80c869080144a0350100f40e1070034000b0884d007401030f10800360b05000d10342010700c0850403c040394030a0316184813400c95852a80c00d003070190750103014080e10080d5207501c2e50405080c2001000300d2003e403607000300505400ba54024149809000d029204907480301000000382d410 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 342910755 1250 342909505 342909521
    0x530030a0608120d29060a03060515032d010b0a0c060c0807090e1b0723010c0f0302211e010603020304021e090f090a0f0807170f09060904 61
    0x1c1d5100f010701d1200c0c00e01c1c104020340134180c1802000c110708903408807040c03c00c407644840c03121148040550390065040c042c0c01000000080d04020079040d9039500403800b60403441c09540c3e400d200c04000e0007031040541003152071035018295441060409a50b074000c43c00010b100340280350a00040b4820f09602a203075018000f6041901003009204800c030103014400110b070081c0024600b00d001092013080329400f5402801f4041085803810b0070008000c401d503100803020303100c180740002c1c1c0e1030041c8a01c0d072070b41610024850001c80c1034404142c02600140714942c00c2c2c0b00341401408080341c5086018404541c1b000507111140035074a6a4000510912000892240c030b01d10400c008240d860700360300110302070342c0300b80c55a50b07008864004900d6000d012081c0d0355030100d6080042071450442c2d1000c0d540003000d6405a074041521569030800150403840c040701ca40d0004603682080c01b17815a241c0c00e02c20105141c1c0da00e0071400c51540d5085102e61080e980c0b05040200c1c2c4603529031030740d0b0b0100314 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 342912005 1250 342910755 342910769
    0xa0503030c0a110318040504030302092d100c06090212071d06040204050303070f0819030b031005040b070c03092d05031f050c09060403030c0530030a06 67
    0x903a034103060740d4501c8540c0c000c1d0040c0001c01c1c54406198614400001125080b030404032007046074041745402c05c005050042e006400301a028088078030180d0356000140100f440c1c0c820020b01d5407404964000070b002d03032145c010313110361412080038001682200540000d00d9000400140001c2a40700140d01207455100803044c9100301c0c03d000c50011079100010080d403825008081076503030741d9810070041e445940943c0d41c15400500440002401c0c00e0003540040d845441d905081c000c1c40e8000c1c1d0440e503926000c4100007520342520204c2030170144580780504820101c02c2c000c6180c20740ba04200d0303c40c064482800c00035440c46001c14144101c0841c00a40b0302100c11180c084058a884503d1020303241c000c2441103400030700011145400260700d0401103110152001700d0b0b11a00d00361001302002003082c03006280030041509207640383d10003040614030989446d500d100171801c260b40b6248020041e020b0032116119440318541d2401c0ba400c06289a10f105e03a6036a60b40c0c90070000181030564480e030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 342913255 1250 342912005 342912007
    0x703020a05010b1017090f030c03130f051f03090804030605190903080105130207060e0d140306011e0e030a050c03302503030f0b010309051e0a0503 65
    0x406a012603080302560044000b4001140f5000402101d4080e8800c080c0100c0d04080415804040c0c18101c42c1c1d02549044c140e9011410602500c1e0450b40f000040e14100d4000064030303001c8100e444c0442c03003d04240300d00c1b52522420840403604090707494807044100030500005050903403207504107e614036030004080ba10b03280c0e285011000361000f41e401c0e0510b00c4034900c1c800522000b51241c9504c198040d640c2030010703460081440800c1c00c4c01a40019113507002c00160010600034000c1004228007400201000c19800000030001c0c030059003c0c03081070004109200140c5e030b10961050034104240b07103400ca002400b15003070310102500d100b0700b0340500a103840e95091000120304c0901c0c0150a400381c0743c000344002136200c01b41c6242c10300b01161090405a888079094140040c114131a06505102410000e070000769a00200d030800c00c40c0041d449190542c0c00700098041d8081f0b6070002c1c2020b016050a41e61206e0b00c480c803c1e00a060300944103201e0f9031502104001c0c810304141c10809803 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 342914505 1250 342913255 342913267
    0x6040e060d0c080d030b0d0f0308180303100503070605180103050604021b0d0206060102030a021902041509020315040203070806150f0a020a020906010c0b0106180f090c08070f1706060708 82
    0x103503100c4c085044550b011a2412007126039904001c0b81c044111075106456584103140c540d4159075582014205850b4030091110103650341c5c1040000314000d01c000100398030014035120406140c511907400aa04201c41030094640740290001c001101000909000c221552240c0c0820003d000f501d1244c2c40342ca5001111a011003008180002005296800d8408903a034650069940c0d1169901c40e20040e0f02400c0c00b60300d030310100203080640c070348000d00216620ba40128000d4440c901c50b048440c4e8540e0000078460f50b8040e20304080400754090764154103601d4605c0700500001c1004082c980144240a403840c0751010050459594a4007c4100782d160210440001d503a0100020300724018401d04011031a150300481e652512071350b0010041c03181d0703030074400100c50350440c3e200c18005d6604845804650607001a0b0b018020303140184000550301c214030300c01040798201130300410600111514402080303900c11280b8000321009024405c80ba26810042440c80c819040003a011003800f080d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 342915755 1250 342914505 342914519
    0x9070b07060c050906040b0904060b0405030d050c030f040f08060f040b180f10090201090503010612080c15280e0304140f0402070c1d01120b180609010f0f0b06040e060d0c 75
    0x140001c10016601001402d45800c1032f140755200700c0c02070302c0d07241c0d1040b0042c0b503466100380010182c1c2d4101009903401e1080c07000c1100e03c5500542c0109598a485400500c0b8010701040626841200701d144045241050b40716600380802c050001340d8620030398601d42c0c050410410102e680340010804403036422a48154a00007030050350f00c00c138001171071a1000201c134a01405004280c50072944071040400d03040e61040c40940c01201d0000c0d160040760648040600c840103106d10402003c26202d8180b622a440020110010f0403a20201850450003801c010800420384098039460002000203002d40000511000c0c100c15105910500004d4800c041104000c0320a0485061400761050002291000107981c0800d0007032446001c2d1303014500300403402e40795200da04241031001020000000300769150070040101d030900d0342a9190011085111024840c1c034016240d8180c00700081420a40090403500c80c52240101c0c4140807000705d0042d40d030f20303548105095444080b04072403c2d51082 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 342917005 1250 342915755 342915757
    0x503030a0e030903030d0221070e0907230306031e0a030e030a120c150e06040c05181609050d060b030106092c070801022109070b07060c050906040b 65
    0x115400c0007810616451958003000065491450005024506220720304040d80000d400c00c020403071184185142248401c0c00c0c42c1c00705030040c1c019603501d500d080c06403810b0086810014006c0010850349455882070840c42c0300c0c0160101017244041956910b517200024a00101c0d4100c60051082080841001f0f0f00000754100c1d11601c20384540c00b000b5070703000405030ac940360b070800906651085206401c440c1e126031600031110384103c00810864100b000010110344055071071150550290061100b0b0140d503240480091004442401103541d5501140340d03040b0b00030704410700520726040c40b040c40c45d000340804c2014000182107420075484905002014200243c00140254070b01940450030300da050080000003800d80001401b5441c8003030426015080742c034640c8401d0b014803030b07001c12000400c5c0020001a4116010741d00d6200c060600f0b001c245001a02c10360300c95003c540e0030401b400c01c0700191044a900b03e4000143e180b41500280d030140702c1d91504944c08180007801160136080070b4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 342918255 1250 342917005 342917011
    0x90603050c0402030709060806030a0b040609111c020405061f0804060e070b041206060803030106120b0f1c0f0c0b070b160e10020307020a030602040602101521050604050303 76
    0x80890700d038811258280710480c4020785c3d60700d00140318440f0a2184a01401c0030303640119025040740c1d020300281c0c40e0280300c0170301507500321030320303500d5600c49000c2c0031044e18a20b640d070742d0442d90601d401050504040310a104060028002c2d44c80b04001143d5a5902485441c8401c2590340c41c81c9042400720002c102c5034003101c1c02c96403140f818032203030130317440d40040d0b01c2c8107032044402220701e8a400c21802e8403a015000c0c0003190010f403100c0700440d007024140003640c02480300c0c0c0c851460051150020000f6a0700075107500c1d000d03891040c000c28082e0b40d800d50346114000c00c8841c4401019042c00c00b218032407100280a810285404400660380c0208402003074081d000700e150001c0341d1214101c00c01c0d405001a83c80000417080c000c21203407440c0060018403503807603d004403440c0001a0340801c4511100d83c0c010341d4110350200d0704220b8190103000c1d5a406d00c600c88020021100d185c06a00780c8001c650155071240081c0a00b84035012090f4a03040362607540002c02c0b0780e8580342502d00702d80d0b40d902c12 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 342919505 1250 342918255 342918263
    0x905100c05010912120b01090b03061201110405040e0a1728170105090f0f0a0225021503010b0706090602222102061c1805030a0216030206030a050405010e07090603 72
    0x2d40040302c0d00307060910501c55001016035901302082d181052704110341e040506080d501c040010403120707004009204440700c040240c180b9980380c1c2e1070300c0c08200441d6602c10005690740c200241c4100022040b13a40c6209000095644584070365400340005088250958000c46652003400000c281c0c1d034000464011040c080c1c0c80f414030a81c0c07a02c00f8015813810943d02c81024030400300108910401c0f0100940d48003201d6140141041e0900800c0f80000c010180701020440c0317191501425800c0441c5081c08030501f01021900e10f5141c00001281445503840103040350782d0780c400310003c0101940490f10010550100c0d40284d260070901d01c070702c4101500c00c00d504c4203900d01e0300702c118020f031039084076103103800903c42401d26000d10f224448246412a0110b8500c1c0e60b20301000305410b2989921704820b018000954a41140300d00181c80c15a03042c000200303100ca800e40410040c2d072140100d0382d100310010004240c544961401c1400340a0881801116004599000c200000c00b607210408590103 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 342920755 1250 342919505 342919517
    0x203150f0402210903090a27110703140c0a150c050301050901031707080d0b0a080c060a03050604060b03090a03021009110121020309100609180b040807051c02010c030605010905100c05010912 84
    0x8c0080344003c85c2d440140c00982200180300d641c021030b0203881c128000c44100140c19107005040800c680c108505c41204070fa4055041c2e450482ca04441d1061240540c00c5081c142c5c82c41d414600010b0090b5414400100340079980d42c0010900c0410030191220540d0104281d9240d1054803440301c0940780303940780306004000070103001450310400180b2480309440540301038942242c910084010303000040405400980798200090300a030154005d503c00d1001901604440d44a407800906007501034807825000d90503e0020000b256440c03094a401341c8090a06003074240707640d003000700f0f11074440440c08419440401040900e20b4003103060381d640340c840c2c0d004110950302c4008220445600c00c00c0102040b049008610010b2401e40c0c80b550072500414655040c0109a80c0b610302d0325110748070308001c004860030005203ca4090150403200c00e2241030a00c070032414680001e040c8403007441440d10030744900c41102041402819055096500000244402c10003802c040f02ca90031811081800580303 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 342922005 1250 342920755 342920819
    0x60c091806050901050d02030c060f07150b10050a02010e1b01020f12070222021309050603240c130306140105120c0d14010203150f0402210903090a 65
    0x952441104240c030b1004100e00c20a90924081c813041c0c10145904a07058450714805000564035034010781009980c07451b041c0e03030703078460f0b40303040c45404c08060212454541400140c4070390341d440d00c14427010700d081442c0c5140c88800341c543c124017505c0c214903109d00754003c0b040507a82c401030b00300c80342900060030b03001c8070f09521210b00d40756070f10104828100750001d001e100800040c07400c21101300310900b0300c4000303501000740036000c0b004a074405054440300c41207006080140303521501605d5400780c02100500031101e50801c0c81001e05003078035004241503200b800041c40d860141c105503070745c5040c90390000150300d403a1300d071003001405c495a04034280e005020000542d8644010341543c4442d151010f00100c020b00000d0119030701030110120303000710506240e005400c00034805548142d03c2091520402e80314a0b00f0b00103945562207a586c0030b9801000010155070074031051051b003a03000440540555a02e141540c1180581c4e00d83c10f6010b4095500000d100080d1600c00440c000e00d000303403442401e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 342923255 1250 342922005 342922049
    0xa0512150312091c0c0e07030203040204050105090705070b071b060e01390314090a110102011109190503060f0f0702030a080106210e0106061209020d0b13060c09 71
    0x80140302c0030503889110991444d9949502da0002400240b1520b00501000c3d26503591030701d00c0000b00e40701030010b60b01000300404d40ca0135008440c018101500c444000d0709003840010001d1041c098040c12641504021800301d81c07055021600301c15800181c4200e0700300c54a010700c060001100c90300d016600300118915105109100000760054010f2411001c40c49101c44641545040c6156407d06079244178220100400c0481c03180302e0000c940140100e449140381c0054441c0103101143c1c11680340c080c92000d00c81c4c084e0101c50210380304880c00100880f42c40b020007030340c02954110030b401d070088005100c82c1f984c25040c1c150003000040d1a1648580d1101d0080341c0e640218140f4200255166004002c0f19000d00300c03506410007225543e5001c8201200a0000e8444071030144010303a5540e281000407030b40c040c030f501c2c0c90018a200b080c40703461101c1e0001503c0306082400601110340500c0031807403010300c0b00b0b565140d4039400a0280070082d51100c0c00380c27180082d845401c0003883c3d00f40d0921509 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 342924505 1250 342923255 342923257
    0x21c150605030106140405060708070210230c0a15060e1807030809030a0c0e06040b220203130c0e160f0807050307020a02030a08090a0e0103030c080a0512150312 71
    0x5180c555403414110307840c1020403070b40107003802049405040704100c00305240c1c4498000b441a140902c41080d0785214601c1880700001054045000b04214080c1462800042c07410041b407016804038007a03126000c981846042c03203c8150018a844948101c61440c1006500100c00303c841e444a0840659030301d41e40c02d1101180b009007079036560003280041c000501424060304070804064112141c0002d0365503030a0140d10a48c00c0b07509510403010421000d460940100c0c0310b0741d40c040e142020b142c0e448008a0110800c00c4070800a8260044000340e41c85005100b510f00703c0760001c0f1540780c02583ea140340383c1042c1055520710301c1d461714803045982e0140136006c000d01c101da031681d03200900d40c1c1d200402c4901d80c001400d5102107000d03501e003210150303800304111443d50380101070241d5036050710010800042100d900030300d9020460300040002c40e0b009403c050900d0340005131180d0322201080e0441e40751140300d4250600002c0d080610030320501c0000032030113030b100c00c0d8116501151044079003102c03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 342925755 1250 342924505 342924509
    0xc17010f0f1a09010305100e0f04060c0201110909090a1b0503010c0806060a080402060921010b04231e040f020f01030501050f01050f130806041e030c020103091104021c15 75
    0x90003c12000c8801d520a60029905c405449500c0e41c0054036620881700790740003900d0900d582c00c52941448207002032445904090509400200003000c0d407003506190034050150810b101e04440800283d00400503c0030b01c19080c1c2c081d8031104407400412074aa0004507030b0045600a6180060301d41042e40201a941c0c06180000c3c062130520540e40f1088039440030082c000c80c2c03c084244400070094842d0b0500d040d6400319812000e0911b28014007a908682e00d00c1d008900c03079400e180c141852040b000f004070288164031600e1a400c3e684040c2412914002400820712802c001810031080c0100c0c1804602120304c01c41d142d04600980798011420340d04203001c1c1550201000c40030380b84a40c0240000d010303450040150340d0a0032851001e5440b40301d15a800394181e40c2155080104102c0103209240080120030b40100d807030001070b18001c0518140813002418540d503600803401744030010004141c2c410006006556680b50070300352a0348141c030f0b003c1403018035003050312894070610901581c00c1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 342927005 1250 342925755 342925799
    0x1509080f070201030f0c1715010f1206080312190902130b040902030f06070f1d01030519060b090a0b071104110d060308090909010506010806040c17010f0f 68
    0x400c0c52103500518480d0760048008074107165807041c4015185402e170140c00010b01d80d51702c46607003913070300d051100460f800c00030841c100b41c08040c00d5004c21a07030011015842c000301480e1207950b0030b01351266080206400c0d001042c1c130f44008110307201d5509a018250748039982c00d28141c40e440c85100e0018080e0385030034000951100c0b80b640854405000c0d94015103912800420100b81c004658001c241040f40910400343e0300e4110380c041040b0784d40c108044c0d1400c048245401031459221001d22601031040c0f070140742c1010380b104003181070fa030000110711851100351802007010070307a03030b02044080358400050b01d401102103010014601b0b5940d02500d084540014104601c1c2d40300c10100401403201c0c2550711b0780403006004070401d4804a1040700040e52160301100d076075024020400400c0a0018114601c03a8104020009566402a0405d400080c2030341c01207a103195a60095070f05010540e445001c004006000181400c070790603480d0b049510003c010126a038840d01d104040580400381c0407 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 342928255 1250 342927005 342927007
    0x30403140313120e090414061b0a0e0a08011e0c090e0609220503040603050c03090c09090709020a05030402040c14040b030c07060e03130503010c020a0813050418150908 74
    0x14010640040f0041410009490031100300d00d96000065a014400ea074191403c6102c5142403880d402c007084040e030032405504248c3c54805429000025900c01c2c0c0b8584002c200090f10b000b07a0f00d4036080d08040c0500010303c000c0c400408611200c0700c7c4d296052025403440c40c1480090418031b8042c9119009070f580c00d070095401d6582d03030b80621101a2001d058603800c0c0f16100045087d00700c605030a84643c0b44200e002c0d6584601d4081c0c002c043d6075010342015100302082003805032440700001c181c100702d00250f64218040c0d03104501541001000e40c0500030180c00004c0c0c3d0004164000c00940c4120310850b020010440c030290100c4070111038404050510404100c10f20044107500f0266622001c904d4071513141c003000d070340c0c0e02040d150f1900c42080d1590002c40c0700c441010040114001801c825002040f210503d180020344d2841c00310000303095214000b645003030346106d00b81d0f0b50780070f004050300034000303001304070122000c5000140e01510f009000f0340e42c0490148450082240254002c001310b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 342929505 1250 342928255 342928291
    0x170c0703030209030705120a060b042313150603050f1c12060807090b090a0c090b0c0a02031b0111030a08010b0a03180308180c060a08070912080304031403 68
    0x80d80290f00045200341d00d8440d4010000700b66a982e4001805994400d001e004680c1051401205541c1082c80192140b030400b900e981c0070300401c82001e9145082d051806c0041e8599803000010a4460308003e854800020840d10283ca0300350042021288200200c4148401d18000c0035110111450300381c2d918585001c5510348a4424941038082d8072000380c001030015543c8038450310b811400d070321980d80d29441da0607501e40317440d10308185a0301c000d245070240aaa40000d0000300700c1a100c2c007604e4101100445c1c0440c0000702000414000c907805011241040e84602c60760100341c4054800a00262120300154180310004c000d9500911850721080a141d0800e88100d41e10380200d641c140406070754038141c1d86502400300c14201c00c04d00940359001141016021001e0142054200b181c8590001041207a030344c81d0361040300c0b689207140c036050020f85c5400808803092901035210a12144908140c00103010704030008502403407080e280c001341081220601c003001c0c0411201403560490310149 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 342930755 1250 342929505 342929507
    0x50606040e0402130f0f050a0e0606040f020405040908191e0503041a0a0b0307050a030b0103020618061b010b0d030816020c0a081b0604030807080705030f031303170c0703 75
    0x11a0b0441d10090202000107001d480c108100e6080c904007510741900ca0010500707141ca03034401c8641091709035400340402c014640c10b055131480c0245c40070b4004d9130380b1281e809040c40e981d41540d0292400801c18040c2216a040803034240d00100015080640880700d0490814061051900e1540752030700c80709600c40003901c0680701070700002c00964940310301c0d4203400041001400300b0b03440303a40803d800049180e6800b00781460043c21303402c428024079401d14180040f555820903141100d5045500320754846200c00441203000c1448401138200001040c1004010360404680381f008003903a00130425a10b40904228051124001c0035010620740404980000980c14145403505000d004403100080340c10049114126103501c0030706241c21442c00751714038610216034144c24120407580c035402c0c0341c1562141d9103580310304000208050000942c160030040c0500554000144802e05140c032413901510361007a0740c444003000c800041c074010b00140e2410000d01ca55010382c004115a505003595554 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 342932005 1250 342930755 342930779
    0x1510030f06231b04080712060e0304030305031b0a090303110f0717010f2c0f07030c0503060609070219021c0303090c060f140a0512010b03091005060604 67
    0x301912010b03110380d152001e03680800e1207031800044203118440309280602407020104400400100c42034010041080354040c00100c000c00d684066aa0755029226454460f00030101d080b081c64450002080000505d9046409544070362a821010110f4070406800c241c402d1044071070f00d40106811032000e01c00700380b11b4800f141c0c1401d0b1500c1100c0c50180700c240c2e51480c02e1282c1d07000b2180c81106d13400c0001c01070300a01070344898a115240038000300417401030400901514a080560000710303e05100c540141c100016020803240d00155042c4170707280e04119111050078010300b4001e210b4240070a10320309000c07070300c03601c2020303154094000d2141d1120014451401048103a03402024185a249400e0b0007200d040a901c0c420703100040e08003060301e00030520092030b901107002c0c060b0040810b1120b44d00f10050710b008040d4803842c103507118a14034060f0742d140039916003032400c41c80c3c12002198500303d51000314019141c11044403a80125080d000d42501c408032080303a0030040a010400c0003034480a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 342933255 1250 342932005 342932033
    0x5012d05090a090615150e01021603120207030c090914160306050a0e030c0d030513050c090c0d0203090a0c0b09060d020a0201060506120403450909030908151003 71
    0x1c40f001c07840e100e000115000300d2003140c008000380081100220506d42e00009841c541038001c2c009000c1c030b181104c809444c584140d2001602c02c400c0d600641e02e406100344800f002039035000300325414598a6050f241d004201002c81111484003941c0e1916600100203100102e428400c03d4000d8550b055603603683c0684405010142c805445100c10320080509202030711810410034020328030304800d81c10050544001409140c030700d101d0309542d800811000320354600300160070b8a03080510b03140e1442d100f0302445604850102c880c804418440300000102d11040c03410700587c020700c403040d2603e020b030b43c003407241424580c0d00c802d0400c640c80d011603194006d081e648506000000d10f40f07550f1004280c0c40da001741444514490014200020103421002000040381d0b880b102080040d540d104000c03002d16048018000420540b000144440040000d20083c0401c0c00043c0300d00f8156180103071074540d003802a030000c0c1c01030680c81100d0304c000540c13143c880d1030441480007a2510310b490b6145890a91 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 342934505 1250 342933255 342933263
    0x120c030316120606020105060a0518180a02040c020328050403020f15041d0702010216030c050a170717070203030702060a0c0b1303021005091c09030605012d05090a09 73
    0x303140100d050240c030703c9030381c008085a40000c100d520302902080302554154101d40e2140d10160b41c4155a482903001c160390001615050340900c45020007038510740035031008001d41c02810900d082c09601e5011020741003122020b003a0001d82d046c8034121444e54610000d40720006001400b040026140416207030034641e1000c1c240c1c0030b400e503040001ea03506522580085189910490f09014140c00e07105059921420520085003021030f1120441b41501d01084081c0030800c150002405008061085000c100d60260340441e400c2009000405142c00031003050314400030100140c4100758604040b100c01c264000e0155141c5500e0380d08010300c42c1c1200c0005001c001c185041e6030000764141182da406200c1a2501610801840c0b400902d44101d01c10b8400481c1d0400061016503507001504558a5170804007186903050000005c80706a603490740040c100383e05000000508002010080c0d00c0ba0b20800d044002042224004160012252042940140d074a02c00903000d080b0590105c00d4107449 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 342935755 1250 342934505 342934517
    0xf090c130905010204090b031b010f03021b0d0e0a06090513050c0c06010603090204050a2906091806120d02030f09010c05010905010605040f11030103140a080c01060305120c030316 79
    0x160b11100d0880c1c0254004121a0303a03948807581c0c061408201e04404010903101504245480500003480003010954107010f00d50081004071036125500c40d44440315503105c0881c0d01c09518507000501054038040c500c0d008940c0b64502090300da224840300d400341c0b5800740c8a0070487e020b100110000341030040460780300340c0d014084250301d900d0502c4114020b00d141d07500410000031030f004100403550007500c039542a034a0300b210034646690004131401d80300c41c9018101e801c402c220010480310300c0741c0341c08260700407850070803a03810203003a170303410780c01140b0548120f00301c40600a0156030764030400a00f000507078030912070f2600d0040740f5401880c0180040c0741400c10403215549690948958150881c1c559440b241d051000c3c2c2468030642c03000c1051040148800c03002036001200301c1c4811f0101401c00249008118a801c8007008046407035036003e40e05940e07503004840840d000705190b000454443c00740c660001c2c1440c04003c25900c5d00ca00e02c1e03000c2c40c51a10703200c407121907140216444000b4050 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 342937005 1250 342935755 342935771
    0xa110d0c080a0b0103050105180d0e040b040612060507030c02030f0a0c0c0b2205010f0804020a0e0f0a0b06030c03071107030209150f1014030c0c030406170f090c13 72
    0xb8041c403165580f1610010840f0350452500d5400c0d00c0000703210401c1003030240401450014001742041b0803014034181200c14180d100701140c05080000d1030a078104e807c0c4040000e201c400798081540d0180111010000c03034654500c104e05850703031802e101005910502c86011819905c0d00100400c1000b4184084d251040343c0d21404c0262955000b04912079001c41e0b007000040143c51940c205068080809074818184400a400031641c84803074010000c10b0b10001d0215103a40318030201800300441020182e03d000b1004048464044504141ea642000b00600645c1001c205a9014012150701785007142e445000071176500045d06141d0740765105084000001da1950350710680120002e04450280180c4401400850b186c2082e2482c01030086c0b64441284541c05400400c06000500446549031030341d84d6404214081d09118850ba07010004000500030b41000507100388591104080e0965550340c4e00985030008101d9100c502c81c0c0101e0f42c4150301e45000250245030101103140000d91076 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 342938255 1250 342937005 342937019
    0x50c0d1703060a170d121803121e052e0603021c02040f0f060305010e06040903200721021008090a15050615120708091006080c090f070e040b040b0607031d030a110d0c 73
    0x9000840c02c0e0000c4be5a4400d000741343e43c03503880551590304207410154086100445682e0303032011503c40c80d010907501050800000035003803c04920001d02820039521207483d444540d406209034441d03940900b908100c00103d0a000380a418101c4a0031100c003012075856405100141442442c00c504003d42d2000c2d07601c449488440c0060b0f00c8800200030601035040c880301054042000c1c449003148120310300c0b2200160340e119a0b1040300920f03441c05040c942c030303000c01191600190700002080e00b00c66030042c005030102075000c903210313a070110b0b038110340d1522030020680345100c2c1c0c694180c101180303400021030840c012240103810085080c22507070500c0c004120702c82144da07250404c1c0301030340101c0c05911a80c07138071800312a0031080724a80e405007820041e17070140c480d440d50780c00c1034000ea44030001c0c81c3c8aa84c81380d00c0b078065004090602e43d580c0049290042035000100b03d44085001521085100c5041c00907070800300607405074212030403c11030000c01c40d00c5a240c4104540080b07481c640801d00d6 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 342939505 1250 342938255 342938291
    0x220905010e070c06092901050405180a06020724020a02010506060406050a1416050a0203071d0412140703080f1f050607080f040f03050c0d1703060a170d12180312 71
    0x702d04051546c031665410001003005844003d481070102e211184801c075094075001c580e1594455012000591b245880d00d01120712910307402e0308045c14178a141410001c2200c9800809805000e58002c0040340d40346401c12480b4080c030f00850000510500c04000030074080e0380b0302004442c2e901d44150900c45100c00b56240482140c0003166150858521103045080400c4640301030030481c0c035022080e03902d04407943d07a020001440505103031803031166001441e01454482c00020a403102c0306035500791900b80504042d10075501c00e0301d00b01420b4001805150401d0000000003800141c41440a03c0e0000700b06294010002c00d90b10b0305000c0240394810404400184000c00d5283c508610492a605000d42000082a5418015420f50728404000f811200d85c00001c40c014415240d1291030750000b081c140300403a00150300d0750300c00c42036601608400090360f55200d20300e9a40c0106031001301c4280402e987e4064440c201e00c5078400c0d45600003c2c001c1181d80000001154005005080c119400a070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 342940755 1250 342939505 342939563
    0x32708030307090303020c2b06060902030c1b0703020310020c030409020d0606090b031501032c0105151801090b0d061503020f04050f0c0906220905010e070c0609 71
    0x2248043c1d608004140d01445941c10f189000c582810320610a94404200440d034161841460661203400303c003049401e51011000c1c10441901319120b141003c0c0080c0283c0c4000071b10031442580401c0025030603000a00d041c1500e5005c0e0140041c5075141d407003a00a50440341001d0150300050001107070614607407020f8800c04c0316413100401c15030f140c080e0260240c805034021184d5a10304008021440101c900c068185400030710300058505540c0311102e880c41102d11214100803108601095403850540116001c5c0000d0301c0c80c00013940c186820040306407002100c880729000310100400014110317501c02c19006902600202c3c481003260f0b520030449d40001002a492001ca54040c42941080c1c1c000c200806402e440401441c20400c0c50703141e1510300184038041100d4000340341241900e525090f200f50006103400602c140501007000d007131412841c06030b091000d180c5000098000b1036410711a01827201901c2c2c003099021162102406095420401d5500c0f00c08a40340341c0039104200c40c5440 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 342942005 1250 342940755 342940757
    0xc0603100e13120810030f06090b090d0305011202010207210c030501020301140a0302030309040507030e0304061119020d0809010c120305100b0a090b0705070801020a0503041b03032708030307 84
    0xc1c040d20107103460030b86008409807940402c8207113001c004048000c05400000c0d203400c0420040419014034041000d00302d200c40c014040310300041445246000043c02d42181c440c5034605101c540c1c1c070b5141c2d0203c070441001000e8010790220381d042050940d51000701c0d107012001151481c10b0300c5952209200303400d242c0c1c0200c815070750000040214a4054054180400d000c640d40545240355400003641c078050341004510690b07650000c0ba608500075070103005000342c15003c0e243c680d5590304025084103a24401e04400e4000c05c4150017030390308081000c0c400d4030b500420103c504101d40d1103180554000d698014180403e00d261080441c0b0030000c5003060300d20a0b5070210b018070b8000d814603e180001c0d84010340000b0140070324004240c000404400f034540300b608007515441c081c24554580001036109107100d520004001e010103500c00010f500c00c6014111442d050403103909801c4c001d005510014000801c00c0c041c00f40c19078507242c504001d010001c001200040e0326070390400d0070f60740b05452000c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 342943255 1250 342942005 342942031
    0x2060c1e09030a050f25061d12010b03060a050609070c060e01021602010215010602070b0f0417060402011103040321020a05010c081e010b03160c0611030103020a0e090c0603100e 78
    0x501030301710400c07201c440d80c40c0c41c0c00c60a4110b400080004010b102d5070080c81d0a0251501e8403410f00d282c070040e4a00c4059005200c0340c107030050390841030b00170810440360501901071880015074441840c0159409020301800c4000e00b0703070394020221043c40300e800088840c1c5403603032070134004035600b40050052050504101500b0040500c006807811519400c40c0711400501c90040001c141c010560500319039035004840e40c0d400b06182c094086106a0304452002115403881c03080e2a0000208180305500c05c0c0c07200400d80300300b03803449903580c0101e04c402024021084000706050b001207400d8081c550360b43c011a0070051550351010f09698088900f040010303141c00402810100c0608039030107031408081c1c40c009950410440744007a200c0101942c0044030700c5a60b014070035208403880008960040002c101c01043c07401d240d90141c0c030030312040e0f1003280c2a00f804260380040c44606d60040500500500360801030070140160303904018400421080c80f1000069200f1086840340c0c4941c600d00108 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 342944505 1250 342943255 342943273
    0x1c090b0705011d0d08011509050d0602090a05030f07090903030603082107030c02060f060a08030f07060f0507122004080609061806040f0501060506070303020a09050102060c1e09030a05 81
    0xc083d20026201185900d80d001040700e00d40250092a0103054500da0601804245041ca40558103e1019440b01da0440130040c450414014103034082d040145c02161002c50b43e80d56501015030b070710030b500004c0b80640c00090041200008990041c1091440707400c02240c001d599403100010f90700711030040150541841800d107a5050744407139103035000c90103040c100a2138520841c025500d03203006019840084c40e02c40030480d550758258860300144086030840c0d0380c400307002c0845411078003e0074045900900b07041c22410141c2150050074410316556076540d02992981e09400040c1103154601c507071121185807205030703d41d05000100080e00b80e6100610440c01c00d40305040c0b401e08010002207154582903070040d242d54011070709a800940081102d4040d030b4240c04c08074014000303680659809100012810201501500505400104c5899015000e03590300d0041e46c6404084420504c94801000010456000812200c640303046200440c2e04000c0c041c00461304c0c2c0000c1c03130401c3e5010780c052482 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 342945755 1250 342944505 342944531
    0x3040c05060c282312040b0d050a11040609031b061e050d0501030b0f0708070906180803070b01180615050d0e0a0b180601081c090b070501 61
    0x40000e04081c1da110b881e204005800c151500c40c424842000b514043d0201c0090080c4000032030102500640c802c0c0408903120301000c2540040461102140a0320103c0d00d40f003805081541e086520803500c05203004c0700004103000810006000c0c29105035104104086481e44002030000340c4200e1310740c01029803c500740041010101c00d07011032001032100307060142c5070740110003040f1864004001141c0b080e074000c6c20746490044001010b811881c100001080c0240b0380ca44500030a0348121020454035800b1044907000070498441020400c1c2c10b1007040105d1094003c810b00d0a404413038207017441e1715414003078219031002400391051402c00f03005000c14a412080440e0701c0c961044100885444c08040325201554040c106081c00303000300d440c001c1d49129070000255010760340c082c0c0d08161964502000d104c1c2e810750b100080e810605584580a100000c0e45038180c3c1d07441e00c0180303c6001030700e1810010382400107032030041203000316000495039184400361514500c14000405c0340300c0c801c62 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 342947005 1250 342945755 342945773
    0x618030d0c11120c030702060a05040305010f0c030f050f0c1e0309010f0c0c0b0f1026010b030c010504050d1106070f050c010509010818031c0f05100302010512150a06050304 76
    0xa24542c0f03a8100005080c074003001045458003070781650141d0300e031281490241d815000740c1c4c2c000b5004d0b50a11540d402c42c1c504651141524280c144c80400a4101c405600c9044071012a403680e800240300703000c02c50340e181100241c10301d408001d400d4aa52080c400c6820030b51381007660246296911840c902040b00024014080e4120070740ca800107101d45191101d130316100b005803d03800400c08d200042548100c9a800703481c068021124800407a0002c0035045118040c0b00c152040c2c07035480d011002d04240381c042807460001b20140e40d01400e090602c2e08102a0500300001100d10050003054400b40b5121074006d48400d9000b04060503248190381400c89c200645042c0c050b040140411440364241e07008000c56170040038811074a14203400000e00c807440c521aa1141e4900403010300c0300c1080404150b040031421000d010420700031a143c1010a00344c40d07005000c001d0120b141407043c5142b50644403032880c0d00c000514001000c0c1c0c074400c000306034100d0b82c0b50882c00001d04000204010300048078 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 342948255 1250 342947005 342947023
    0x120a030605180f010605090f120a1713090f0e0f031306090e13050a021504050a0510020a081e1306180b040b0c07030b010806010602060109020c0618030d0c11 69
    0x1203110010741c9080c03d24803280d94014001e0406006010403210100d4403134141d44568500c0141c0307061400d0072401c10540d6140214a8100c2e007400c0c0c0c40340345d40300d9205090140c0e042c2400b0110103141060800620101501c50542d00079409540c0b036511040131007040003801c00c0d03074171660080c0d90b480d64266055220404550000c0e800d2100c01041002144222000240d005c1c0400d968000c0c41469403608505044100c10060351110041c0041052000440d000340b08891049404801184d610003c0c4861818807032006409600042c003080c01040c200c00003003140201c00400003182a0124001ea4526002000746001142000900b80207042d0000032074180d412131140584041490852800038034401c038040c0300e0b03018502080f01d0349040c0c810040d540c082c642c03045a419680d0b86403006540e07640f00900c1803400600c03542000080c044814421146440d032424054011551000460f415507150055149221700c000c02080c818804584a080c0703025446a45c1c08041c0405402078a250200c0c0c6 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 342949505 1250 342948255 342948289
    0x20c0304060324051f212403081b070f03080a1218080c1905030705010501050a0612200c0606030d0906120c2312070503060f12120a030605 61
    0x440301340400d654405000c50204510410b05804441d00f0300d08032000030f40140300c1700342015441039541030002d480d00031401c400c0070400c800032000010154810103440a1002030146401001f0405011624031010441d00400700115010345941d60001c1052460b954415501e0711808103100e0700c000e5208401c88101c08611005211100e0350003c01244c0000040008022250000f8103a81c0c0315018003442c007183d039048550600750341542c10415241d9025440c01c41b055442c2c500007082a01c0c108101c3e0095502959641c0030b0f89006c0140c00b4010541d50304000d283d00011010020b01c0a00f007401080030132a900d0107000182006000d0500d80340c820040f441c2480b1a5000c103002c06a4421225807000e42d2400b0f0119030781445001c295800b1809401c682030040310a000c40801c000014000c0c040801d890864031010b030354641d0215031501042d50310592201c8000084040391810343c40402c40440d52805407501d81d112407501c60981c0c0c0c1b00f0041900400d456000c1080710f46080701c0b0342091080300c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 342950755 1250 342949505 342949571
    0x60403080112120c050c0d0809040e01021903020a0504030c06050c0c030106180b04150e07020d210504020a05041506030b1f0f0e0a03030504140f0f1003020c03040603 73
    0x30b10703603907800700741c50b0190311104200d0000c01c00f00c00d2140821041526034005820380c21402030505048035107500c00704031240110b0a0407032911a45005101b120301044a00d070070500b0608504008401a5115424040421106002c04004503030000030544c010400c68544683d114100004141801e04403000325120340d14004040110304946542d01038500070416001500284980018000b071400b800e41103003c06440c030303001c51000020358809014a642c0d400302e9680a10000c012110150031080801c50182200f4880b040044550005500540300401e030f445515224000300741120002c0c0f6011078420703200c50301004001c2d01445146041c60301078a029024820b400045800004e990061700108484005540030152041c0b0f9803504400e4010503e01320142ea80c10014802d8105000f000000007918803030840c02d1504507041c80240702e020b05035000c1c1d1081c0004002d00f10b101d100120781416020440301200510500050020303141c240c90000344031124400262003480300c048088030000d0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 342952005 1250 342950755 342950789
    0x50c0904150e0c1e03041109220b04051e0d0e0402041202090402060f0703030203010501030c0503041a07050904020c07210f060c0e03060405011b020313090213030b090604030801 78
    0x24640302070b0380c40107010203241e41d1080c04415030f020210108000d9410751a0200c06d02c0704000380c42000e01d16019084508142507110b0004005030502c09070108030508d0a102d910500040340c460303c0c0b5910038010400d0341d44c000c880214405d24180d4042412405401414003100038a410904910b50003006913400c6060600f00554004205403625001c5d1040085e00c0003e41155103250448245440e401c52040d2181201d14018000e500f0a01a02e4041b80c00c3c8100c41c0742e09880349007600e00c6940c0007503408002084002040e2044040602800100402001b420f20543c565000801d660304002009140d910b282c0100c4000650a0400148081070301c2031510740850080c49210603602c0d00320200042e58810400d054681c2100c201040f03030180100e400b0003003440b00c19404200d00c07001d980070200502483c20812a02c1e48199407c500180c580c498040c0243c2100340d02810f6070300c0c5401c0c0403203032441c5c981e01c40035023a401c211249041e96010000300800c05503c80d100c98018041502c030161000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 342953255 1250 342952005 342952019
    0x11a120c030c060c0a1e020a0e040305090108040303060f0e25091a13030b0702060a0203060a0603051e010320060403080708031f15020f07060e060c0709050c090415 72
    0x80301050614410707100480c000c04136140070f020503104c0f03d034441140845c80250303900000000703801721010707842102d0110340050090200c20309580b080d40d0681d542480d00100000564000c100648103408040d0350303243c0410000444039035180a4402e080c82810380d4500401d4011207090f924a244c0e080d81070f4084640500d03600050550140c0320a4010148100181d1203c012a4020707502500032000740d1080003c02d00455004180c002c4002e982541c00170303921078030032409903c4250b43c05904601001400c00c001c911903400143c00c0800c1e50210381083d485245c110140701c1081c1c0060716035244031003c4007080c810013050542c0d201000c2e1441400d142c80c61301c0d59031460107440d2018248481c000005801104001c59184079051590750a0726002d80718016003118103c44401136015209184401d101c03441c0003d2a0800c03070390144d0b1030941c40c1011005008061b00180889080384c03140c1100420f01040350301509224000014050382c0702c3c1600070411040d60140066a4220718042100b84050 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 342954505 1250 342953255 342953263
    0x5120a0b13051207150f021c090b06041503170909070e030a03030209040b0d030e03100501080318060705060f15040c080106051608070c030308011e09050601030e011a120c03 76
    0x440006140c02c0d44800140c00d00c014541580311600641c5d500c0c1841c2c2210304c1142d68050000c1195820030b00d400041d44020f02c104403030b0b030000c02404926400001520b02d00e0240c004182c8600d1040b0407061031552940c07128040c441000003199407074004107a04c2401e0814a041c40c1d030080151030084280e08040010030b89828500c04050105900001c0e225060b4403160001d010900d0007806103021207601d4240103200004000d04070384a03004269841250031400c1c024103040e44e803400003840c41d0980011091801a04690006400070b40601c500c1000c10300601c0003502c41d41100001402d5480d10b0400c1c09000c2e00814003051295140170203101c4400c0d4014003140c15a40503007022640c944000118080c29840248000c029010001d404010400e5480c4001d00301c074440d07280d04a0b280d880705024076240508106600000c0f80c1e90608000b243c40035042180c00c040181400601c19200c0000d403400d64050001c614080328a2007140001da080501c41c052203110a1000340c0002c00d03c541c0001e8032 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 342955755 1250 342954505 342954523
    0x30c07210503040b15131e0207030e04090215030103110a062604050c060c0c04150308220504050108011a030f070e1801020c0619021e1305120a0b1305 66
    0x6480d0800066840e445c090745035090710b58002d158200e0034032030f00d1009010302440780b8440c180941c10002e840a044030f41c02034503a80743d81070712140522642503050000501601c01d060382d000e540d140e00c8210141c0f90600940c00f0394068070081a0160700304091245c03000d100c2e03000d4010820314860a02a8011000c98a400180c6103032440a05440b507040052801c44c0d9210b03080c0c5d1000c00025014510500000d54842e00c00c000e40b030a0042880c0386040c42c0c0304c1030340340c403020742080c00401c40942d0b10741c2010002044868a9007045401645403c04a070485000360003900c85a0340d81e050120f41000560f0702c04c0301c0310004a006040984180c1546621201248290b5113090041e1011803018101042d1102d011000700c80210b4440085400c91a50341c5e50907603005820803070022a100018242c0d00841d03a844410310a031000550082180000c2c1e035005e0460302142a21243c000b2446039507081c20109104502001060000141d00b03103610320145c040c2c8440c800400c440f403080300152012419102e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 342957005 1250 342955755 342955763
    0x30c331b140318011e060f080706200d0f030b09240d0501151a07030207060804030c0203060c03011409061008130b070c0b070e0d081e030c0721050304 66
    0x82c40b0b4079085591030202804203c2c400d01942000a020000c0c080815090f01c1a40404400c2c0081c0c0d45d181c0a02000d8004c9000e5080d043e04484c0c0d0500800307000340d01d550810001180303560505a40b4500b0a0700f440400703005ca80000e0250000241c6e119818000e0042044044036100064141151400b04141d6555040010f130110300b1070102e0700396928407c020082e9081402400f00031400c002c030b07900b1620240150a002d041030055510281d00d02c80c103031030180341c0c507800130701e49241401401e0742c0446004000700c04002101828130010703101408603034004c00c3d408113100d40302e5060a41826005d01e1318007165000d0403210301041000d84c0c8803a06010441c3c4141044295900e5045c401c2c5400f0103001005004054244d00340086154410701a03030074203002c0d500c80c5a198407400c20032600c00e070700402d480d940110888065008100c0d850010540e488101d05a0308219030400c409101701c1d002201c085040040105004c410710104002c01144400380700409a4038000700c40001d41030340001f50004d8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 342958255 1250 342957005 342957007
    0x603011a040b01020a0c090902010f020604080d110903030a11061302030303040b040611030705091008010518070225051806060a080a150806060a05030607020a030c331b14 75
    0x1900d141d00074040242e1407508952065062912607c1a03000740c95984003ca0000c0c0880c1c0702e402c0c0b00c030b06c0032400d5070007103501030160741c60b002d5040c001c44040c1040100c4086030b030900304116481c569007007008100100300c540b01d010700040d0b10300f0704a08280b0000e100142d00c06940f02403a006a80200840e544640e01034291001e5440303500300017000340448002c100140c2c000005014049400202601d440c0720112030000381d01c1d20b80307202122241001c0c440c00350460000048074842c0e19000344149c0e0b1001d050300c11540c20101c01071030b4a0168951145610203905401c0040c45142400e4411145402d40300843c0f010390b04107500400c2d4940b042c11160010000e020002c00c89160300e6400511001039540c00e1007079800d0311085010303100e860603202180f2034030340100005030504000ca001072259007140c014281100780c41e00c3c181c070a410160b0040725102580c0c607603c0c001c4240362200340c2c0e601140c0d205c0b40700060b0082185100b21040e5180d403440d01c284000600c010780e94891504001c5585900001d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 342959505 1250 342958255 342958271
    0x1203050f04030501060e01080d09030c0b0a0c060230220507080604062306010f121404030f0210021201030611070501050c1c02090f0d1e08070b0603011a04 68
    0x440850149420041c115400d0100000786d26001c6031007103059515100c00e45011400002081d01c0580161000828011441e0020020600a0400340002003414103151403803800503500c044c04c0768802c40c1582e0040b56801c03001d803007510342407204001821840810b0116400c1130568100c900c40d030325040e000c9440c0542d404e0350810a09200303c00c0100205401c49026040920703010002e081404602916510108100110403180041036805100b042e154885120110031048a072005c1d043d51400c00c01d40c0300c0340c142d90800c80e6103a00c60b01c2607001e580c1d051030b581c1c00b01c08000d082204980341410114014418068011790166070b1904483d0301800004181112030b038160580d001e02d4101074a01e510b040e080005c0000d10b07100800c210940040314210348544c0f00c2202049002e02140707260841e801810b20106818003021a440741806050040c0041c8010252503101c00001942100d040d08049605000c000b108055150003d0044000b40204015581d103011440748006c02c20b8403d98551141c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 342960755 1250 342959505 342959527
    0x4051918060e1303120c090b0d020d0e03040608130204110a080403020c15030f04021f020f010605090c16031e020c1c0209010e0613020c0610080304120305 68
    0x5980040c0061112410034561094000d00280818850b1691118181000500000311080240c010561640f6030040003407169030418000d0603001c0380d801c14020740d5640811000040e00242c00304c118403c1d80541c0d1f8940101c4904191054425078261a50084c0400d0101d41d4114a04d42c1c0d201e056143c4640c0224914000580541446030884605200020300406407075485040c15108078000e80840d258914120244542410b01780701341110318078280301081540d40f6114105030024001013801004a1020450010501c40c440f8050301582c04806500c202c14801c5c0107501c0244000c17610040d6602d803e070140b0420388a0191000713001c8400009400415000e1640a101601c0001d85515a40e01d001406541c4040c2000314510465201c8003550380c007081407482e943d040303501400d00c01c000d0346050043c810070007000d042e483e440410320011590401a900c013600c0e100d024040100281d00b4a00d003540503028490b00a0030300b40d0801c100601401a042141c60b1490b641840c0c8a0f69a004e6000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 342962005 1250 342960755 342960799
    0x3050c0f0301060e0a0e09210c0f0610090203060603070c141c2712060e1914060108030a4e050106090b07050c0a08061006020309060405 60
    0x30140240031008000440d959610418800c0494016107000c3c0d00c244c0c41c1c445040e91400100e41e1b800c000c2c5c1c000c520010784600401e1214400895480b50a41071800a80c2e41f1420004000002a4542c2c0084100071031400c03c41c0c2108024405400110325604107800803444a02c402800c80041c0080860141e00b0071020001051401c901c1c8000d5580344e15500b2401802d070b0030726200c1900050004500b002c0c505080110b00b00020300b4a22501c140c452800b500c0d035000703075200e074001c2e61030740d544400c080d130880030601c54a401603010446410758550540307404925091040f00340d8110b03906c03000060020050020866200d04928100101d500b440220748406103801d10783e19000002106c0c01840d156031402c030886062200c418100040c4c03020903850754084500c00d100d1a000078210384001c101008008e0001c3c00307814050001d07110f102c3c142c2d80204620341405d03804904070380d00a600300b141981c0d100b60410094400f0744007442c40e001c0002e0004107503000c2d5014040c410041d44400e50403040f4010 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 342963255 1250 342962005 342962017
    0x30203130b0c030114040e0607140d02030a020403120c1106030c0918101505030a020d2a03060801020406091404060e070507052812030b03030408070f06031b03050c 72
    0x41d00844051910030034805054000307100d41641c000e82102c00f40c04a15280c01502d07002d06000c2c0042c0f072141c0c0d0709401203840c2c02245807404c50020301000341240c5096180001c501c100e00000c2c000d030360f03607180d03140c1040c6812103001f080d400c0103408400000012907019508584000880b10320340c40741c43d4103040b06481d10841e0b1016034011102c054001c14071140586a41c0b28202c21480f05001c0d540e5183c007401e400b04403c00b9003002407003c00003e001604141d015001c224450340c000103460441850102d0503a04003101e034183c29003800c20750f1481a50601609001d00345490095040500e803036009030400c4070502a4440380715a2403582c80c140e843e40e52001000b4804412410700d00d0504402c081c10f00e90041d1001d4407a03008000d00710510010440c58a1034180c8060b0400a05450b07540740e940e103100b050140c1c4410161503074658149603030100040c2c0040d0117501d0281c120b0314585400d03004400010341c44031041c14200351108044d62115480007a82d03c031607060209155403080b800f04c000b4401c0e2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 342964505 1250 342963255 342963263
    0x30a050a061502060a0509030a170c070210080a06080304120f11211b09040f02030f030408030a09080115050d03020307020a0914060118060c020d0c0303050309191203020313 76
    0x30b20801c0101c0c0380d00150301400303801c1341d110401681e2a0b01e0501512031140c1d083c0e040100700e405044400c1e034004103d105510540ca28543e5003018040da002038500c0403003168000000740300d00180030900000d03120300402000703410019403030702c1d1410281128805683e80007500d450380228003207091080342c44252501c404014032001282100c2d8900c55100710070810414094403a4103e4101d40b440b00d0041081c04082c000c0080384c0d2507a55a840c10246d01c0c0412080342c0601800a14908040040003c1d2016041f0400559203401440100600da0303411075203e01c9807a810070b410b03107150b015a00400d04c16505e042d01c140b09403455038181649140b08031a00250031590384040080c0840c2e10758002c10f2809031410f482c00090301c5250045440c0300102080c0c40c01c01100260400c0594010740c03146200b184060280b98201e815621601c032204e0550340140d0209a001080041d035100911408007144c04c46e0348a51002d1788141c944c01c50134040d1280034800e0540c00000300b6001d901c8840c2c00882d02d644 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 342965755 1250 342964505 342964529
    0x22805030a0503101508130f170c010c0306030f02041d12040527150a090212040c0f1d0c04050d0303060302040b06040311090a020705030307020106030506070f05030a050a06 76
    0x400c50018000c0d40115001c2e0683d40044801146080340f405d542c00140f5119614a001a1505285a50040c0800c00d00b12140401c800340c40e00010800c2c104107003550080940a52034031030001d081804d441c440098a810103150000c14000240d0401c10140d003660141c2e800500c41d85c0650308540d0046c0c000074805028818000112049502d090003001512020398036010035240b000c1c000d0000911015000429041080018189440c2c4110680c01904000d2425940568403070140c02260f10a0030b0481c48034040c14200070920084200b000d0003803140442001a41d454001154000034100a074400c114103404003203404040c0320800c1e036014000080034990242d0462601400030042444100d0007079003020f43c810154075048060758101d0381c011811440e0171046108101040c8401006940c0d02c40d420311261020503c200084c520400e00b50b00001840b80c00c6040c13161078103000a0001007088180041c0031000c40d40300060307a03086102d150b00803a03191240075010001d414a504080d003501c00c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 342967005 1250 342965755 342965767
    0x10915061706040f0525060f170402041e0207030c060c0c20240c0c01090609140303131e09050403050405010305070c0227100506090922060f0c0305060102280503 71
    0xd01803641808846031754031030440740d0f5244c1030227071490b0580c1034141e40c0d041e1000000802505264002004120742c4078a400420380310512084120380041000b40c0c0003400c1d0800001c00c1021500c94503107050101c1c00e01d10241742c40d42d41c800c21245d415910350600c0444601c400c081c0c1d03807a40e13117040c0030915624641002501c404aa41c0c641c41d08000d90035000c40c40740d1424040d89502035169a0107542895590343d04080c142041100025444c0b0304458145c03108000c528506603d4003000c1700900b1000801640d00d4030a14080501401c084d00302061562804c82404006a003100846088620070f0a010819544486050340c2117803c2e0358010f5001401542000c09100c0a028035074100c0040c9036541410351525000c00da240005402031325000b5208104941c510700c1c0038035007140e0120141184030150244408070300c1c0c200c095050100e50190f228501c0c680c40c601d56028550300400c8500c2c04029034039004000035929245800100e041111008003080b11ba9007020003d5081ca4004e01140d940d20 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 342968255 1250 342967005 342967063
    0x4030602180f101107080f0d0909020315040c03141f083d020a0f080105060702130b12010212010e1308030c090f03010915061706040f05 60
    0x160004031070350290015512100420b1804955420700c0b00d6000e402d6822800c9030f500180c5164200d0280c851162090800c000b404900070803e41d000f84403a10060600100c0c3d41901030540b0b000c64024101700e80c018820000301e2843c20582d4440207000312004191151080015001800030342c07000d80714a0624002c2110500034555046440b503400d907140d00440f03136982040f6886056400c42280d500c0d0b005002295242d120312950f01c0050040c9201400005241051400b242d0002403403030041202d1030000144150403050b9a40104001da0300c9238540007590740020b0000c60b450b0604a81c203995900100300c2e0340c41e00c030301c0e06440a0403503008550301c90842d0104a03200d0002d208550601c501c5400003003020310110b10417403c0f0341e844400142517803540954060507070040002d103508154100032980a030782d024041c034500c450045100d18060500d03014444140e840580291515032000b40d4083d03440303580000c3c9140d12076004240140790b0401854101d0911652100b01d10100301620140c540403 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 342969505 1250 342968255 342968257
    0x30a0f03060312111b0f040b0a050306011512060303201e0307060b030f0607110c040614040b0f011202180907020f0607030b0a0e040c0b0a121d0a080708070804030602 73
    0xc40101021903001c0c03419041c1701009420041d0759140c200d680c980340c0220324100b907002418201001010180c881ea00e510100740341480036807000004240c000024058103800c40c86a11442d0385107501404014150b44000c0c000700d1417070354103840c0318550040c43d00080009100000180c045044400d81e01000e80300c086a42c1d8118000030703540c5900e071094482d41071400040300c482044441c4087c121b10341e60000c0a450342400100d00c18041d0199450711212560749125030005042c40100140c0d44010034428802110455203110340282d07000f00c5081516170b00500740300c04c0d40d01030000240e90345241070960110a100c03000e8054025525009210000d500450f0855121710342e00e04403405035071a01011002c0c0d60140c154590052401c0d00c041c0202901c40e030040d0742c0180101d40c0851102c3e0340b0585030405a0260888000080711a51b51501e018494001c41c0b4085802c050324000c0020003c1e4625143d402000300201044800142c9804029083c002c0d5100c80d600b011440f40c4031540ea04011010f = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 342970755 1250 342969505 342969527
    0x9020f04050301051e060d050a0501050f180f071707030c0306050402030d0527011803061a010914041e15030209241e0d05030a0809030309030a0f03060312 68
    0x80b950800c0001540851a1051801140d10310383c5041c800c3d0b10303500b060000b68150b228080c1d130740703001780540d65011640c24003400f4010511908106041e24120241040610b0f861083c4500d075004001c1300d41c80d0100c0040c1c0c00e410b58061007076064080034030044031440c000c0c0540c0010a0060300d10400014011180d000c80d100c1e500940503502200c4401720210f995105240b443c003880c0d02c455600194505100002c2446480c040c100202500b04081ca08400440140e0088070801d847d800240c40e0414002e032000b40701c100a081c800301d03e41c01c1c044014038984454082e01e0181c1d80e1a0a080c4101e0400e85400729150040b00d42008480d9030601d00c0d403a980718a0006a005164007800f044201200e0108068103681c0301401d541a0b201181c00c000c0105440c0c0300004114400c200041695681d40c003e1130010751080b401540e90b4071410700050b2030003200501c140c6407504144100000c807400401110300b2103411b0325205991880c06c560a900800703050304050407045440c00c0e0403007000d030404900c8079 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 342972005 1250 342970755 342970759
    0xc020d0f1208011a0706180f020109090c080109150315060e070e0d02090703022101090b030a0c060e0a0e07020c040b06030105030712170a0507060b040912080a0609020f0405 76
    0x403681428a0082d100c1e800c0c203104202c510301c890302c108124806420003400b20144103c8001c2561a402c58450746030100d05007003a10014240350380c0004540e0060b040750b00811051030140701440440344042c0214205104481e200c40c0c80b03c40324201034010303000e4140130710362024a80f100307242d141c05100000c1059002d403c0d418000403001c0307299240209008400581d00400040c06c403c0c803a0b0a20500074005410300c01856020310a04210002103100c1c1c0c8a0400d0005003411650314141c0807000350380c192a003050094000359500004030b2b00c421000c409a070b04505111030050000d10228010f500b05070b0002641c2000c200c00c3c80803031035000c910184611400c48041c854844448100300b81d6210a10495505030f201010030803500d1021104c0640c990300501c00500e43c038400b041c20903010750080903008000b500018400f801c00045124100c0b0111054030b042003202900d0791502c03260310135442c0080500c080035000400440054104902802e0440070940d20303808507040e000010340050041074 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 342973255 1250 342972005 342972023
    0xa180204090206040e0c030702071202210106031709030c090c0403020922061d06072309031504021504060503040822180e0c03030301050f060c12070c090c0f08070c020d0f 75
    0x264bc0310341e641c40c6050b860f0b001401d090081c80e070380201046810304803190300c0c46035496583c0003000c6100240080d80c40300340740c0c401c1a503845000c1c2c20541004081c0e6540c03880341071035400f8004d010796050152400c2d641d041e61403205540b10003c0307032000c1c0303043d200b070b42000803850000714001c00600350080b0f80949a1403201640c11450814882d448800445550000030746000200901411b03210704480c00c0007502942c207240025120201e03040604110f003221103402544e05000440c2407088200711380c9604199124145070421400034118480500080c1c941840440c00d0081c1d81014054240030a1011400c0f9181595a405e24040ca940c002140c03549240f800d02e0380c1141801c049141c1440000040145241d40e0801e0108a16a480c11840301c0c0c110b8014060302100c0407040140d1065012801d103503030340702d000910309400d9910240d00302108050078003202124083d00151400c070116040d0601020903615000122101b10303031460083e40c041c03c104070100912080a0010003900d00a004103 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 342974505 1250 342973255 342973259
    0x1802040614011e0903050f0102031b1602010f0e04050f060112180816080f040f0605040501052a030a0c2009040b0405210d050a180204090206040e0c03070207 69
    0x14460109401e101c550214043c0b00d5192010f04192500d65142c0701e5501340200032946076140e00b45002484d541c0140241e40c00030a00092040c1d00c0900040e00d08442d10b00c0e841c04942003d404000e480c6400024140400c103000520a2800703107040042420021b07008100b245015400400361150030f80d01036010608240c18190840501d019044510186864151007030460b940c0360500c03603000d894010b51180c00c0340f4440c0d0000c0d94613401032007131402000025071214141541d8a80c6e004441e8445014031501300000c00559810200341c4000c500741c2c401071b440d022501080c0449074071480485091034040040c072402403c0e0024420303880c0351702440026041102c6c1e00d0700e03a0200701007040c86980c011280b00c0082c1c0020225040140d025201d4001e851084401c0c0301c101da0141e0b01c00c0e07040c42681c1d00215558210480511809600504011082c03204060b2601c5074000d818040c1400f90045440307180b9142503413140320841d8018440400e00700780700d18101c045404a0341003a01c1840c01400340720301c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 342975755 1250 342974505 342974519
    0x60708060402030c0702091902070308070806041a0405060d05060c0a09080303010807030f080405190e0a0b090c0a0203090a06053c250302031e03011a030403021018020406 75
    0x3e5901c41c1d600c0c0d492035858020941c0810010703540040500c040e00b661502a11003070880ba00107403045601c079803908100c50500c028042d10040d002080705001341c2c80e180e00f02110300c041c00c601c2640b1440603030300058141c480340c02007100360b510351801810714400d500601505240e40d41c0100304241e85c40e0360304c0c0d60300c2e5181c14945860780310a109000880c2e001043c20303c081600074507198081e80c0314040552034542c1e101c0210354070102103c40c0e5010301001810130013031440005a6a644040d14980400450b13030010000360043c00c010f00031200e104400704691054600800864040d11001003803219410f0355601d00030529406030740340d091280c001507034a00c0403080f5260b201c90b0300381e1103201c0b9401014014941d20110b42050100000c14a28108090600f8042520700d940c1d05000c0c0d4042d56940100d40c00701c0b0001001d8121000f1410f0013040100034030700a0009a403c0302d100016019603e454a0500301d2070034132121402e44845180421a08035580c01c00b801201c207074826203080c00415602c4074 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 342977005 1250 342975755 342975757
    0x1080d09030c05060307050c10020319020c071814010e06040c090f0506160206070605070e010207031109041b0b040317090918121c06050a050d0311031b060708060402 73
    0x100c010681c0d15200403d102c80d00c2c100c00910341c040c1891605904140d806c0d01d0b1145414900c40031051803680c00801d118121a800c14522140207884505514003204040304030b540e65494480e071060001c1c440c0340d00100c088076802c00c2044081300c0e142c0074042d507100e1a440c6e4540c0c0050759440d100310300c0c2c100c00706061401103403d1000c407800f005034400401c1c03800c024004140e21107215210650414000c3d8001a60b44401030141c15002e00400036603450310680c041c101141141e050341c155404007008000103240c241e100e18800310300380c4401da03182e1036070710380240c02e040d504000710003072011080041150949070300a0001c40b409503055401d8078152a00e8000d151103214540d81d0008481000160b40d001c1c00100d81c881034180b8421240780b800201982c05068201c2030485103030b450311141c0d00402c00d080303010f410301410040300c440700720314036007030016501c2191620003d0500c203a82c481c82900c4401402981c10848421450502c0d506d07040c07e41c03517280c801c2114510040b41c1000049a00d609241c8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 342978255 1250 342977005 342977009
    0xc11060603150106030209061b0a0b010906180f270b010b13031202150106090e090d081f030f030804260901030b04020409020c010c020d030e0604020d030509090103080301080d09 78
    0x403204034420f9003000b0049002c0c1d401002001d40080040108d18020368400842c1d00d80740001c50050701c01305909280060010300180c0c0020b0f0700743d00f80f02c8c05108140100c82080d255031010a00014070b222200c51031000381001e84840380000c000ca10307100240341181000c81e04064070698809020b40c0e01c5506c9040c3d0750140741310070800620042030503c0012a60007904648801c14011602d00368151003c50554920980180b000980071030000c1107003051500009401c5200700c0040c00a0001d040001000007a006009245a180a42280300c40c854030341a104040d5800c0340301d0012552140c00c0c05060024161021907941c031906d5990b071244c0034503080c51900f030b900140400d0b1074132112000450103401c11044041d03111383c0c02c110008090815100034800b1080d40000800d03640600d01c1e0103400c00c0c12503648601410305110301002000340c04185950320940c100c529584010341418201c1c1d45014200c11103400c48110800482800341745000b841c101c8404100700c0b156201401011a0020814 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 342979505 1250 342978255 342978283
    0x4020d27031b0312060f06030605010c0818150a0203031e0f01181113090c02150a0f09120804020301060b0f18040207051009061503080a030f020c010c11060603 70
    0x20aa0341c0020450416090307070043c024903004030503c00500480c0111441580400141154014200100358160241c5c2005201c02d003807080710344a02e9240c0c0c543d141720b404122240303174144403128551039454841078030300c2d504400403058585906000103540c03a442566641e1508900601c0404040d60000c0c1c0588100e00303402480140d6480c0100c2075405e1014200f55004858aa64405402422400191a040002d00d143d0248145844881e00c200c0b44100701c4001190031942c22000c1d4441d0042d000c0e9003208198200143d1444c2c40b84805000384003107c001000c0615050354040e01c140c0c4907902c0750085008400030030880d0740d11450362445102c3c445031200005024002103000c81c44084801c1e91004004e0005490403103542c0d0380e5818203840f0000c003a41d09039240344801c180801071107108003241c110140003541d241540c4900146010b030001c040101600c448a1006081c03082e0140c54030a49980d00034031a0400d0300c0c0b0054548030301c484c0b1034450781c400c000c0010081e10300001c0c1014030000c1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 342980755 1250 342979505 342979517
    0x7140d02010c111f02060f07031401060e0103060905040b090d050306010c020f0d0b07050c010b060306010c24111806030705042d030309083904090204020d2703 70
    0x843d5901c0b1400d0001002c8158424109100b00041c0315918428088600715503001d040d032460840e00800c0e0400b00545544100b40c035041d240a068014150003c2c1580c4440c201700035280204c0004070058600c5400100c8805d040c10140020480680c005900540702d880c20395243d11500701044a0b503000803038005001550007420f040c0503003090b025000302540c0103440c01484c0340c13050b198054503002c00da90000c001580000ea6810200c02885280048041120980c0c90f5050030800285000034545019115903291181502400800307490b07090740101110003400440340d00707010040e0b507800110280d00d14040c1100314103100d15081007101c0c407801a6407103450900b0f041000965544c140060020341007611252441d41620805080d00c000b1803082d500c00051a040c2031b200c034204001508420307404c440703040c2982070300448001c0710b10005410340040042010130800060140c84c05040c0a504240f00185c0e5240c0c4c070440ba0404051b10785100ca00d00e80c100b6891311080551504204003130000380c0d07 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 342982005 1250 342980755 342980777
    0x30d0206090709020f09040203010815160f0f11010c05130f260307080f07120216030303051906080601030218040b190209060d0603032c0f0102120c07140d0201 70
    0x12140d003c0d1117000c40c4c071400542841500c4002c01c1c101d0b40280c008002c0c076441480e2565414a81605e0181d0003210345962132507403ca64440904a0394181e076289082c0a0414205403c4074170460101c2d80d0114040001d002e481034180000c0d01d0750340038042c4006901012880441c070f0080c580400b030202c4034002d070040261090a480201010944407001d6800d000070080035000c01c2810010345883c0c0341d54590190f84c0c103071a02c0c1114400c400d180c0d84d90250341100710904d41a000240d4514122038050901290582d150707030640c51142044000642c2d002e241080104405100081c1d450590744281d6000f44004034104c00040c4000048800070a42003e003400981203041c443c3d25407041e800c110001508012489000501f07980020b1510f170425a5210820000d056222000e86d00c042161070040c014a1200c00000c9510307194a11658013130313900c504801c0c1d81c5e64820000340c41f448680c05092600d80a020207104d803103030074610510b44050403055180c0381514043c626020866070584404003429 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 342983255 1250 342982005 342982019
    0x1b0906020f030c061503070e0a0209090114030a0201030e1e01091101020a02100c110612040501061a120c090307170f150106030911090114030118031709010f06090b030d02060907 78
    0x21490540c5c2d90140914100000c1010307417402c40350b00907124080e02503140c3c2c040c0411b000741c0001c140e004a14150141008c83c3c042e480c08110101c100d038080c40c4c04540d14410200d0a454400300215408a01c40851144401c00c4010b501c10911944180c1c009440c04602c03500492390750391400070195102345903a0710170803e140644000b60f90144240143e01041c02c0d200300082158004d5802400d00110b55802c0000b00442032040d40302a01502c406110000f80c0c4460361252801980320300940c401004022505060391103090369803952004088071150341e1629214800000008080340702407045140d02d0990f5007022404111090b849416008640c1ca041c03004c6000d800e03000d8041e03c144981c2075803d030240d01e030442c0c0540a01a02110074007040300c00c0040c1070841b420801e140d440560a89040300c00a80c3c0102403e0400344100c0b0242c8040d29002a000e004010311010840c05500e084400581a0030b2608900501e0508070107603600ca0000300f00c16a210b64007141c00d00810f400454041c0020 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 342984505 1250 342983255 342983281
    0x1030f11040510030e060a06060f0810180222030c061e0e010c02150301050118050a030323071a01080114010e07050702040e011515021f1b0906020f030c06 68
    0x41041c0f4900070a000c1c0c5c4040500342050300a03201d001d082070701c40030244107154001c280040300640d50300e01201186011501942111014018100354820b038008080200c2080d4041e40c030304218003422450305451841c1840100c2a0b1440102c99020f102030001039110300a02c6004c007544c020132410117404091120403585403804001c0281804440f420110141e200e510606030006083e40c0b28075070307075410a070014003207040000541ca1030b40e010103002e110316168003103a20104e95142c00c0c484003400180700301402503101e20320789480450003c11400103003e40035032042c3c1d00e070388140322a07a0140d0b200c00f050b90036960881942042d064080e00100801659032003190b03889000d528000b824049070f40e00080c182c1c1e0b104004081180c1d19100100203682c240c02c00348004290180c086582074200005c00ba4450b03021f20040c404943c00040c0300003003554107800c500c0c0c2e001c81001143c070f03c6060b2140003415072907041c0101c40052140041058203104000f0480300c01310341c403400900695683c0e01d00900781d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 342985611 1106 342984505 342984529
    0x10603110a0903120225140d0203060f04080c03130f090605010c060f06030204090303050405011104060212070f140a050d0c0c090f141501030f110405 66
    0x205030040b035280120390b40701c428000d200e420a1401e0341003040b5181e1141c00c00c104c0000700c0046070984e0900380d0955011405c903001c80744442040c0f010000b6001d81c004d415074014004240b455100b0760740c0e10341c014403813041d072441c00c1044401c0c182540c0050020010f040900d001c14031070303000080c28640c003410000108100c810320340b0000a26010855001801041e5240c00000000700d0640081018680140050004120b507150080080c0b0003200e05070390f254030b080c01c80d1650b0400c0310304071007c8816030b50040003010388040e499a2540e0244808862850340744149900040c1c0c0140180c2c0300c0c182c420003400180401c0c0c1052400c1c84e03000c1907480b080010140e038081c002a610b540500584080500002d80307003c9420128000f05000c0c00315401802007081040580100c2c4102402600d01c03c2e68188070010b1301d2000034040d158145410310007204d0504c000c3c40740d0b080c510074a0035 = true := by decide +kernel

theorem cover : BRFrame.Cov 342805755 342985611 := by
  have h0 := BRFrame.cov_init 342805755
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342805755 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 342805755 ≤ n) (h2 : n < 342985611) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
