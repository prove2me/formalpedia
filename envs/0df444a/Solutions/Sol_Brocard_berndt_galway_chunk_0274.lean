-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0274
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:53:41.63228+00:00
-- url     : https://prove2.me/submissions/7d933bc4-a510-4b9c-abd4-13ede9ae54f4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 49100723 ≤ n < 49280579 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 49101973 1250 49100723 49100729
    0x160f1208070305040b01050d110604080709060918080c03070f08310b0d06030506040803040b0a060501050d0203061903030305150307080c0d03050708030c07060507050903060f0c041a13 81
    0x8042246080c03031780702d41c8210a814440d09103d43d1080340a042000621880d0031800d40001d00042d460f582c445140d03d4840545001c1c11424901d001000038075441070b401080480c049100c03000d5040d5045486080341c0703502800c40c40c1c915100070001b036000030b44e0000032110401d0050f137515480e00020501d03590700c4400360441d60007141c2142c5c0207083c400011200c0100319140180c449646100040b0000080c0c00caa41c00540140655001c11040c8001c5030002c5200340d100386508000c1d07945506143e421500303103001d001c1c0059014816503e030f104080d1300031500290020481c5003101d0b20302d030403400d003400b00390002c4002940710b0060160400807401400d1540c0011405841101e0030a19401c3d900c0c500d40b07202a200c0c4444880d400c043c1030040007160002900501615070f20300d8040c0008080c1c0d48181001c65000307240a0000346800e200b08159160100b0003006890b082e224a000e0b1404080003a01c08000d0000402c0300041c4100b51004082002c102e6080301034030b8800e0b007a86075100850303e41c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 49103223 1250 49101973 49101977
    0x3050303130b090c150a030f14041b0f0e0a0902030d020d23120709050a0308070c060305040305030a0509030903161401050306090426070302060f060402090307050105160f120807 78
    0x161440c20117940701c12500b14156080040c40b038035a01c3d6900f089010306a0404500100e03890888580c410008600700d491140380103280b0110440c045c80301740c00c0c041c040303441048491200d50009000440880c0241c81e0801072441d0040b0f13841040385c0019007440240c14000c0c025070b0151400c0c0e491213411803485083c1c89590450540e908041c1451720b03645100c0c26a00010003402800090300d1107000d90721507400b600010f040b000701c0c2a100c0c03030200d4003648501e10917120f40184c82c00000c2c1396072082c003850f4421503040c2d41d45811519250783c4c04010b0000034141c054140000d00a540040c0c90410400e60500115403013884d50a28081e0344c404180a0314100d01c1c1040820000c1107007588030400c686801990124080450001c0f40e43d21006070800248030b6104c5240c0000c0742c0c814140e0001d4894021101e03d43d800d6000c1c2c5884041004901c640b04110744c040c1c01c810010005580110b02402810030203d002c3c1e150244940d0320720140003070f100c008844100c0030003203911007158410b503120307446030302c0b4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 49104473 1250 49103223 49103233
    0x3090b0307080a06091808030a020705010501031a010b040b09450a05040515090f0d0c03030b030601030203070b090a0504050a0e100c08040609020111060f0115020109020d0209070903050303130b09 86
    0x215803240380c00e1003806c0549044800004220303812120381c12502d0440d0040020451943c60b8030300204500100420032003d8000a0008520040c010045a0840b861300c0140c9180004103020300c40912200307200302e40200420103800104054401e0109407404001c0c0b0002411000d0040010344030300e000c1c1c4001d240703e1070a41040009070000407001c0c2c14440170ba030400c8040c0d840d00880b614000d1003001c2000c01c3c0c01100c11403082c960b0440c40c40c45680d4440e49091002c04006c0060654030f41d800d10001c1e505900030300d070070001000450010031843d900681800740964455000c80c0a40b801a584000c0c0156240c1c002d0107c58001e0141e44034422035500f05210132090310034003d0901401400c0a442c484c0d17510240021603014402049940e4098020b48155291040300414030074024460072070614000f41c2c809030481c0c410310903078003802d41c018004230700c2c0d18103034003440000413000307000e502440030008000c00410010000703140b00d5490b6100c0101682038a180c00421100d025204922303039401 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 49105723 1250 49104473 49104491
    0x130f03050604080903070b0d0912030e061801020f040f050f0a0609030219080d0e03010510030b150d02210c060304020607060902150a081807180903090b0307080a0609 73
    0x1140c0710741c005410619158513030080000290504020307034004201900c0000d0081d00088081d0419002c0d54040c1d03401d4018800c0e00380c01175083d02c0c1941528030070380d04680c0008400000200740d05000503254800141001c103418040f201e82d81c4540c01c01603112998040400852411252000500d03000f46c03040704505240c854050505001c901009108100400c080c41400034820480030082c050074003200d13814045503801501c405c0410704260301030f5080c440003802900c1c5801c80003040720ba12285a07006030717584065860703401e503c5207001503111070b040065802580c5d41e2448200c082d0a04c0c0d408000b900c0b5420090387c0340401142d031440c05210107100300000340c0e0f42d0300b0a40d44030642294010039010f4052001a000602c03004034280d400e00c000c03c0395480603a118030181d109002d2241041c4007000c2c00301c40c0d01c0ea107181d2031041d14001226001c0034402200d19800010034035210382080c04805032075841c403030041c3d00102c0c1d92070001040c000400100c4074250140400400d00c0344002c20581c10f03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 49106973 1250 49105723 49105733
    0x51605250503100e03041503021303080705070504020a050a050702030705061306020f06130809040f06090605041a0a030201140702100806090a0c0503060d030c0b07090e090606030a0f08071205130f03 87
    0x14601c00d1f9000a0103894030803040d140283c0440d010b104800c200031942e40d44030720f8083e003c3c1c1c101c02030070f40d454403079480080707100d050910803115042d40580f240382c200041401d00701c940d03500c8801c040780c05004602c00018070783c0360038000d0454001081d40c44000c079820074400900d03285e0780d20040ea01e43e90000060204014141418184098220003a40e68030f10202d004180a0a01c2c02801003e06113010b100166246030707907018400f03543e400c907401d000c103441c01102c8205d010040c0140e194803201ca1a0304100640c06503861446c1d644400808900348655500050484815000007030301180c407500c104031462910100080d4040040e040401c4602d4015030001d00d5030100418650080c91081707400d00501d8010b0081d401c0c40c5a01c0414800b1616003848000d005007140d01c200f805410011001c02e609800128280344542801b5000308003490550f02c81d9003145e02c0b11b19040e20034070b40820500c40415510b040301441d440c202c0d00c43c1385c2c0d10041100310b0007042c0d01d2030703109640b40c0211a03000d00001e4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 49108223 1250 49106973 49106977
    0x10509010504020f090d030e0a060e1c0c080109080d1d0a200a080a061103090606040c140a08010e0a1509050a020f0309010b0916051605250503100e03 66
    0xd0300c10b82c1c006032944669081c00403580724400740e056105400500e00d1040640c80703c6c030660801c000383d8407102c8041d601d040955032410a00d02007a4040ba8071240d081c03060f8050400c100049000e14203102c001c594590b941d03400c5940041342501c80c074200003a030210751801d5010380c14040c0100b184105200701c002c184c054880d1400c0c0d40092140400003044c500300d04030b26868a040d4100101001200703030b0380c3d0b4222580e4005982e421a000c0e03044c902c1c1c1da0146c001c00016a8400c1c1c20660140c201070b540c4104010090641d5030180080c040d821000044456112004e8004a9203c0c1c54800c80d0354108050b40140910062081840c0ca00304080c851500b207404249a0440742d0412000c02c494803a405d039000070780500c40e05901084400301c10171041a0054104000344081641c1c8501c09441d03003215800516448151080410010810300320003d003144840364606010754280d4043c6185400c40c00380303a54408400076000302d00da20381405203240503c1401c04c0c0d00e0100e101001503180d202c400340e49134 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 49109473 1250 49108223 49108229
    0x160503060f22020c060703020403080d0c0309140607020c0f03070909020303120c04090507050a0c0b04020109090204060527030c10030608030d0f0b0f0102060105041515050a020f0601050901 83
    0x20340c492100c107605036180c24401100d01c503031510300102c90080c003200b814002c1d04503203ca2459440303120080703134100740648225400e494001400c01d140c00340d84000400034101e40040744082564030600c5101040100c00d25100041084010300510308040000a181c880b400110311310071004002059141da400103074200460311403800114482907140006419405051031040d45050f10303004201d00b1a880070010b0083d01e119000030002512a01800c5a141c05900c03221804038545500c0301d4041034005098075030240c03051500d1040e95407503c0f60f50007681c106030b20480100300c01091003d64881c0b81c498103041d04003d0f10500c0310722681900080c1e5078215640ca403c1c0604101512194468400c0e048003000d00340c140c04580c0d90310300400152005000300480c1c40a001d280c07520310501880e08088424140405034020704150342040e00b04001400c0520310034000320703502d100001e03640c0d009e0b049615801119031102919a11003600103420204083e100e11015000440184603e540e0900d841d815 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 49110723 1250 49109473 49109479
    0x3050702060f011505040b0c0a0c080309030a060203060f0307090c02070b0f04031202120310050a06020303190218030616090f0e0a0c0c140c030f12030a1107020a0608090616050306 79
    0x811546005d491074401c42e0440d080c64040061503c22060000a03d011414400c0d5403400d645a0381e41d2415031680200c07040d00f90706400101c81c0e58003040c01c54002d0760b007000000300560128900100024a0000158404220a41c0b6040c941f040c00c0e0b014441d0034000c04061211528281c0301440a0b0710900c1240401001030a002903450085482001140c1d00f61f40305c0c84884e0355909183d815030005202c1481668032415450002152091001c001e407401414045048508080d0011001303000e0b40100d483c0c0c100800704110b0407140d030b0707900b00310b41ca0068070b100485402d45a50400010f0068816801c4842c1d2200341940820071f04c1030954815501400144001800240320081150800f44050010304084d00d030b04880800b494002c1100380440c0e000b01d00300d441202141100c9a1a01302034003508601400a00004403040303616084900011240c2060600d0510550b00181d02c00d904d617000340c4005000d071010800000410000d0310380103a604010494070000085d00101180700c02480140 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 49111973 1250 49110723 49110749
    0x305060102030c0a0b0a060b1b0c040c0206180c06041404050c070b0a0218041b030b01030c0918060806070504090606030209060403020409020a08012315090c070c0504091203050702060f01 82
    0x22550400da40700c50013410300241c2d6180d40305022012412751401c0b554000900d801803c400903110726082c4664034400380503401400d103030f80d50104903c0e0b034094280c8402403036024802c1c046034590b03070780d1008001030120303040c2e00d80c5800d2084003440b00315040103203a05080741e02080300c4004039001c4a03013154042814100903a48091401c42c0303510314041001903980003030418000321074017042c04220b88a9580d00365000c0100c030740100300440540d00e06022040c003140980d9030074080890040d020200040510301c01040e2203a450100b00d203810001c0303940400180c40410240f1084c007242c02104000e048a01e402d41c1820803120010300e040c4035610000388100c3e03550340e4500440d202e00b90544c0042164200801900c4a4246d401d090b00112100e5071040844403000101c00440d07512100320070a002400c1c4003120707501c00403880c005500051091300c4102c01030308001429910303030181035a8a0700c00d5900302101f0000c1000902581d03409424075003590042c008000c44410f024008904480807101289 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 49113223 1250 49111973 49111981
    0x1e120803091006030b0915010e1b120a05100f0f090e100906060f08061003060e10110403060c03051306150305030f19022125030206070305060102030c0a0b 68
    0x1601d0300e0300d11640450031a06000002041c810f840c1c640501c00e0443c6c2e41522100b9401c07003002000000c2c24010070001d0280d80c004142e110000550380420300c0c88038230304549410a554583c6030004000c6401b0044c403526103003085214184818484020a441c49480d0070386414482e500104119a000c0c51417465a01e08066803007100410480200082e000b20410281d4558208013001e0b09040c0204503d00345c092a0000b120400000d107070344600072a18005c0349c00c80c2151f036190090850126080d60a200d00e0300c0007542105584501c010741c6510a540c0745e81c540c0340d8604001914251a005424545001d081244658107948444503856024400041020a02c1111451090345030000b404034400407801843d5241d1200040c20910300c0c40001700d18848090000300c0c0d5425006080f003142d07201641405880130709a001400038030950209407000d41010110180016442d281e007500142d20010510818940520403984c00c82c2c002c1c40a18500300032904003559410641e074005009884250000d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 49114473 1250 49113223 49113241
    0x7050c0409020f091006020c0604051e01030e0d1d010503060d02010c030504150302030109060803040f03030c05010b090906041109130201050304050c1009090e0703030816020703080a091e120803 85
    0x2042403d0003060300c030640c2800400321400540c24000e1401510802c054000d5614007201500c0440b80c00820400e0041d003c0c80c00c40081c040007092075414540c450404075010300c010320511004403015587d950003440548050404000c98550f45810302c1020000d01a07a078803002000c190003502824900c0814109107030486007031082c5e034005506010305a0b00e2503c6154950001d41c1219a00c5c40148607040e111740d0341540340e1150b803080031254035481000b000024080d66100c028940a400005200400040441c2a0030001c81e02103101b50482d80070001005000703074a00c0c40c0d0060643d801c1800349007080b5524404170b45100064140107010001170200b00c420485a01191406044151402011700010381015024068404954141103000c02c01c00400204101103c3d0103a0301c4022a0b2a03075a00c9920440c4007048250031030060700b07400700119171020010490b5410b20342e51242d1a80c6842440e09001e403183c0b9240882c150100750400000320030040300303a000b0340c002640f1a43c0c0d071100091 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 49115723 1250 49114473 49114489
    0x140f030a050c0106060903230c03100c091a090d0c0b0304230d0206010506160507060801060f05091f020f07030b0114030a020f040b010215070305040605060f0d1509080f0304030e030307050c040902 86
    0x201c21f4ac07500c1400f0501d80f54000303d4118561180d5292141c1c02c40603100c0c50710315000f00a0b002c02132054032091112642c0d40c6088000f4203181130103000e0070300580342c5400d4910700551046805441c00800c102c6803008983c140c41101201e0a051800b40c01c0791440d20300000d44600c418400c15114100116800e0a010710a148500c1c840d5072200840b01525900c2c032010340303511000d105840120b105d00310031f0407a250143d03013103650500c0e008250044042c80d21f20440c003a95444584d05c011407284c1640b403a061304040118001031802000210300039890401c1000d0b800d0201c1169074061b0b0003113940f42d00140c4440c8c5121100e00c1c0206c4000c0391800f41500100d1030711554400704210560038500380805250540d0200d400b0320f020740014091556204140322600c5a0889a00c1c0c01402107034107031020500e1241c840c07169100c040c0010541d400d40780c603a034031160003080c1000030048000051104240d0040f42c0e002d000c69056010303504245040c0c4945440d120300d4007809000b5600c0d6500c400440d40c804103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 49116973 1250 49115723 49115743
    0x106020105071b12141c060602010c020a032304150c0210020718050a090f03080406050114091803040b0c0705030c0a050a180b06120f0609010f03140f030a050c010606090323 76
    0x886103c0511a46c1145d010744814424000036510300008011401c0c03021440c2206075401d600c41c10207804a0840c50001d05210403140a10000240404182c401802090010346416503640c0c498095950040114041c44002084159840907004000c42900d0b03210b4178000408180000480f56500356804015181c882002004e05001e0020082050b80248a042c01940664020003040e80c072410305c0700c103c0c0048640986e000e8000c10002d02058030030f03880d03190000741000a4038180342e5110303540340140d00809484551500b0095041c48681000c000301003d9500844842034402c0c60403001c5400c800090203a42501d1000b40c1c01c06601d00596000544400b5000c0e00d155950803150210030034030760040d10240c7d809408040071035200e00c2c14a41e03580c160b48a6401d40120540b4558880341c0c3c01d02446031100082c080d1848020150b1420b001070b0060703102c2921043e41c0c03030074242540d60071624190401d50510030300400c2400441c00090b002003070b4512043c142c110310300c070541d0341c0c0c2c0c500141c0030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 49118223 1250 49116973 49116997
    0xf180b03011404032303040605040606081603050f1501030f0305040506040e0108060702010504020609101812051009050304050d08090411040503150421050c0102030106020105071b1214 81
    0x200100c0e50b07000011034807541c002d40e00e0f45d842130b01600c5032584003420a01c07500741c0d190301030010401158242d442103030020320425001a04960b1039040505000b00594869000e41043c441082071080078041d40d410610940c0242502d00c04103408040d1050381800094000d42c980340e0701c94101405841141e000e454000e0005403100d540e0b05100e40d400c0302c2400f4860041c041d04020501e51030050040500555000b0001030030300e4010010302c4425900c04245000f0041403032049010b1800d840c6024010b04082c05c0041c10740b140714200580350422103c0328001d1185000540302c04580040259003e542044070726000c003e0390350a01d024140150502283d1051600e4070b0f048035180728200070070450314194107507000e5200700980884208402c490107800001040840740c00d1011075000c5a2200e1a141441c6080c050303454409030890b0000d030072480142c4e40d10014001a41c0e0401d09080c2849103030010030314145483d9441d030548001c0c4154020900c2004001851000d842c513095134a0704040c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 49119473 1250 49118223 49118231
    0x30f03040e01180504020117060d06090f03110a0302030702091b0c0a020f0301020f0d15030b0c030a05010f05060a03050603010b0d0813060503040803070c081902010e060705040f180b0301 82
    0x681ea1002041400780300d0304440a401001c5000c0d882c243c1d0088601c1550140c544c0c440007562a0703001070080070300503d0590306c0f85808c0c000d0390024100d0700c14a401a409440d00d10b0000105103006089101d03c076000c402c0e9a030116042d8030003e5400800c07142140e070305503441e1859444000740c280c00c00d00c0b4841e2558003607a0100303002d071181400241c1210300d14000c95040c4400304904081c5400c0f8464440309518081d03040200e42d4a444098020407a104440100d04014950741d4665408a000c15201c140c6800e9000082c402004254018039001d0241f40030b070803102d545000001404c1d0300c19010508281502c0740000b40040e5020f5100081e080c0006e088490011420b00d0051178551001440ca0360501c415100440c1e418401d03000c0d00e1141e6031024016140d510303104010785160303071400c1c0b00301c030002000c010a00108010b44483c568440c2c04c0e80022450b407940850060a207000200320004102d42407108001108103480004226040524031010940701d22007450040c00c04802140c0d019030130 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 49120723 1250 49119473 49119479
    0x30f05070c0305030a120501180b0d020312070501060f0b0a0f0c05060c250c031b120b0f06120601090b0a081509070603060503100b010507020901060306090f020306100509030f0304 79
    0x4048000c01c501700159039005401c00052641703204843c800c0c06547c2c00084031510300203a11a03258890110040010f00c1082c0ba04034650000740742c00c1544c0045801c0d8031010440d5010440240070b943c0190400b034188820311402c0c84004400c5000e0442141d00b048044458103280ba030142d144003400e03d41001c259103561400380c0110030341e42e000c02420f00b0004801c0101c03070b05090082d00441c080961000c1c9100c1e0092661f210b60341c44050324860070700c800084007400103107030f01c0e00c00e8180259440707182048903902d0200758000142d54001c100d540100380d071030b9980b60880300c0171511a064446031100025202c440601181c45240e01d504404014443d80302c01146030484400070903c9680e071841165021510f4a504805550071031241c80d4255200e00714034a6074898640240380c100d0010b160503801c16000e900021b016001c00c1e030090b400300340d03070b00024014070320140038604101303260000941c594186980814440120110280d0403c903001c0f80310004c0d540d0602064409500780000c481d151a1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 49121973 1250 49120723 49120733
    0x3020706090507090516020c030705150d05070e01110a230307020402070f02090601050a02031c180b09100b0303071e08070c051009060e040906150306020403060501080f0604030f05070c03 82
    0x50b200e400c4011b18006441440f9480040e444085100107405444920714100500264410f03003004684424400d012285408000e481410701c80d00f8145d450050010b038620014010182520303d1035080d4125665100c0400c3c0005000030010b03014204822203e460181e60f18118001d0701070083d072040c0005095000d1014506162899500855050300c41d1f45500c8010744040c0b151a0b800c0300540c006025081c0803ca2400104030a03034411240400e0352a1403101a24040c03001c00c00403900da107124030074011103c508111100e0000d4603d041007154496900019640740a401001003403025403020104020b28422104010319500c00412504c0d01743d14941040c2801081c0200f40c054901c10140d4400e8520501d1490105d075180e8844d404030303001d50341c01e00010381810201030342c40540340c0c000800400900d999a2000b1401140c0050300c550840c81e160701a034034181d001d11841d51110003109031068020aa40780c000364503040034007009151400c1030344c441c012520301070700341d492640c00042800 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 49123223 1250 49121973 49121981
    0x70e1e03100609050109090515090106030b01080d03050106030b06040522140912070b13030c1407050118050604290406090602150f06011101020717190c02010804030302070609050709 80
    0x2c3d04101c090009030380704c03001e050032078100303040150035035000003d281d20340d09281404540110340c0310004511306807261141e24041a081c0d1100c0c12550040880c4040300303515100351405054a45404c0c40f00c019207000140c4140035034055144148122920140c1003005d68103c1130011074014002c1c0440007030800780d00b040000c1103c860f080d46c054452000040700c0c03003104680b0740c00d5010101041c0340c2c8400c05100c155002c6007008800b80f003850740380c030b0b00070482e20710a007036040c07002d20700030301c200ca00b454001030420854408040e090b418084041c07041d6500c03001a142074480e00070914a01c1c400c0e04074007081f2160320a2124414980004010541660000c0c40d50281e50482e0200c411409101c0000340c8404811901c0383d2001510b0004110298030800198442c0c002c444009030601000d502d841c03405028450301c2c001c008000184000d562072841c0004040d801382801e203011564410b80001e819044014001410590700090907802c10505900800382036030404101c411041d1585601030042c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 49124473 1250 49123223 49123229
    0x1009030e091617072610050906130c050d0f060f050d110103180b011502060609070206011a0d0c090303030b030a02060d0e011808030601080f070e1e031006 68
    0x42103400d002802d01030700000311482500301075440960303035090300d220700f0642d101c003605034000c004411030080e10302400754154103c103c8000684102c0350425410f5030b00c9205540c0c3c882c50003001c420303003004810342e202c800d00602d4100c1d07a000030480d10780e030840407160740c8903442c40d1030750042c40d01c0b000b0403042d90640e00a1007510f8440000d01c11107130700c8038100056900c001c00300401918080c0b8080300654806e820681070300d5481195600c645150390307a49200c032602600060950020b01041c1508240d0412806030404070a550103012424810342c02500c4500500038551600c190039085c5401d14151800c50314040c6813444104102c0705101d6000703000700110f02c000c3c0c0c0040d04001b0b0b201c444e498042261003915900800740380c40e05d5001d00904010300030f1509104459581d510029241400659403107400f5403168408903542d10340040090130300c2401a0050307040080c0042000321141c1c000300d00c11a41d00c4112042d42d0070801524035500401542d0030350680501907000e480e0240c050130740003e015 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 49125723 1250 49124473 49124479
    0x306051c0b060d2001140d020d050105010c0506070c030903080705030d05100b1e040504020c0d0f0201020301060c030e0a0816030c0b130308070501020409020304150c020f03040501111009030e 84
    0xb500c80c00100424a103150f1409855400c0f0f0100d129075050240642c18102e400c103051120b0610042049445107420109200c10119000102005110401c1c0300d00c3d4050582420621100c9560b6101d05541e0b100092842e814083d001c0404414140a0048800150f500c030000c2c5903071792240d1030990344a4101802190003a802d04000c20703881025100003030185c0300d100704035a040261a1104280d1081602d0302100440c40400022640d61214002400c030041c1c03181c000c0030b203010b84400c0103003000100e084e12811644144018008540e04c00800003030b094043c900604401401030000b050b8004075440848244903014009001510040d41641142c1c007402c9480e80880e030b1807103842030070710030003080c1c109500341040d0503c00200004080c0013124040c200040c01c25445100300c00483e8015501a6601d07041100c1c03000003100d00d03000e02c103002a42807003d0903c0c06072403d016941c0b40905d02440307050021a40300020140ca0401c1121035400a07100300b800070440d07078140640101030f180180c40c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 49126973 1250 49125723 49125743
    0xb1c020d0513050c1203030712061206050f0a02130501031d0a03020c030f01060f050904210c060e0d020c0423010e010911030910090314030718090e0a0809010306051c 73
    0x15183c50200c3d40320045c01c404001561455448050488408900034220342819656000c0030618000007402c014a0038810880050642042600e004803c00c0042548202500400401c85898210901c90303049800030309000c5110055098440810861906030308002d1290328021014590700144a590085c0280c050f078007400504070074513082c3d40050203401c0120031f1014080007a8100200d005134410b0043c200411641741d0081c004200f602072000c400f00003213180d000c80092112501c5080180e02c0720301c0042c4089032000001075110071540340f0340303841544d4540c0d0700380301058092000400c035000d40200d021990386921441e905d40b41b080c01040c00e030b60300e40f01c01d034000d00d503200045030701401214004000c0745808880f600c010b082100b20440400041c040c14032802801040079501175070441d103c00c5d180d4000c45603840c10380d4107164010382d000707030401d481e03000340600220344000015004580240d44030a108016000f4000990001e50003c107040e0050002d50140300c180e84500e031080100345 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 49128223 1250 49126973 49126993
    0x1806060503010b2d060703030209040510050315060103020d060603020301030b0c1213022b0302010e03040b1614070602060403080a0b060a050304060f0203090a0b0a060b1c020d051305 80
    0x1500303d40c0d280ba0019000049540f05403c80b15036504041d494009900000d440801d64001107031300307600f01c00c0d8200c01080d0041004644c07464607000d91f13684590707552040e541087c60000003d43e070764414641c4803e101041400f0a00991083e01240d00320240020240181a07640d20024029402480103850070341c100008139040c0540c1c0d40440ea0500d00d80341c280c04868036065200c14070b94458410480c4d00c611481f000d410030b0301c1e224441c091660705150303120302e0f0002e0300e0401a094843c220a1900503800030041841021000e1094030590b0041958030f56a601c080d2800030b48008030000760b4011482901800910194001941480351344070340da4012242e151841200d00362480c0a2503c0d034400c005200c0c5d0308840b03102d07a02031766100c0e000300d0011031a8520040b071601284c0c0181c1e401402031300016030304814084245041600003649040401010303161098518681c002d00f5000c0301418184020452100303242d80603940c5103905080d042005081505c548120045005812501c6c0d0262403d10 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 49129473 1250 49128223 49128229
    0x708240a0f2426030307050a0e090a05061201050403140a02010905011b140406020601030204050c070b04030206090106060206010e010303110f011a0a0602010c0f082701090c0506031003120c0618060605 88
    0x40c02c0c00d820f202004506603122001d05449940120251900b04450342d02004419900d26060350300401d166000019582084400e2296541d4010440642d82e8100028000003d40c440c8840912030a11411252100301c0c4410072405402014400b070803543c200500d5044540741918084082070164071420141c021510072602c0346e000b46c1c45008007580001c8010005030070181c20030b50b4440c1001050300cbc039040e031655032161101d030305640a41c0140e00440820170200002d06c1148080c10141c00104002d601d002c1c1e21f245510340c140001402c1006032040b4010041c0100141030f00e400c0500024003540c15060f000316180e144501041c0d1090940c0c030b00c00145607006100c0c03a05507000a41c0e0301c54003071218800694080001814580314141c944c20202c4c5240071360b03405188040d907104008918000c1505000c03c69106941140c3e101c0d20040040c006414820300b00310048171360240500c3d42d400c013501416550f2080004002e070000b4140300c0820241c181060780140c20310f10902003044103a45038018 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 49130723 1250 49129473 49129529
    0x20c010c080a051b01020705010b030d030e06131703091c050a0503060405090f01020408060a0e16030f05161401080702010b130f0902030d020708240a0f24 68
    0x90700003603007005092600c40c030500c01451139401d030000340002c200e0407480c4c1e10f007242d110301000d85050b55982d03011611071505015000c0b00e00100d1800b8170150b90280b45041c2c5401001e4440c1c04c80c400c401c1911030800076000031841a060305103040c5602d074a070103402d1503101c910b8422000e00300d4010942c450405400391050340c6ea03003101c6550700c1d030950740c0300400e2200410002d07002400d00e205002507201580000d0004001078041c2002904050422480b0001511035140e0318a646400544c43c1810040b1406826021a034200c098040b0f03050305418500c4c1000c4c0c6981a40020140240001c541ca1031551400803608400baa5007003d26940c00354100e089902081c0d0896011031700f22040070807040a50054040411400030000340c09041e0343c002441c020480d4499009a04004010890b640c014400c52158103240b90200104040030404919140002070240c034415035103401482d500c1850342d10100260142641d03603e408842e0412841c40301500384511030030b4044904d0419408000040 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 49131973 1250 49130723 49130747
    0x10905070801090b040b0301020a0306030605010504050405210909010b0306011e141e1210240f0e130234060e1603080405130e07090e07090615020c01 66
    0x15030801c0c541d0900440c000542048226103a1254442e02c0c3c600e201d0f80c0a10081541c5540350320300146240c51850281c09032a0141d202c0c5200f58238000802c808640d01245840e050f0002110848a0500c0880c074201e090080042403030300050780b50000f06201d90064011030140da0240c0390060b010b101c0b000b100c4260812004a40002143c151061151810803400341405001c5844a01c44014808142c98003d80020000035004411f907418094841460581d510242c580c40320b00c8044551194991107003103110700c0d81e001c00c001c61500b41040151090a20801001005002c10a40f007488054100039401c0b03004080d4031946c1900031491013003648288500000b10a90f5440791061950700c13400010100c0400443c00d5003d0b02c004800c20030848200b140c00395202d05035281d12507081c80d081c03051200d07107049442d202c02d00d0910018101e00c0001510002c45000180104800304901880760501c80e060303000008a506001c0003054860002c42d4000250b20107508403074001c6d00000045880a41d440 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 49133223 1250 49131973 49131977
    0x501021b031819031a04030e010207031707020f030a0b1501020a030c080c160602101103010509160318050105040204110906041701060308041203080a0213090b0301150609060801090507 81
    0x4440c1040c2c1e81014050943c10340c96031850308600365500e4840b17a181c01400d5020202c030700d0200d002c110801d40c101d0007c4150301d0080c0300a041ca10b045035106021451052020070340d000c2c0c045481411581d80c0d044007032034150050186d4403a5070152410f0b41042000f40c4140e01e414a401c0403202c0203510001d1a520416010761307941500c440c180e10b4411559006c013031900158050b0300707420f0741c1200a96440c50000c280700d0b0300030002c01c0003003c020412584085807985901d241003004011a585145146030405003c5035880551006140d05500800d43d0000c0e17822019600141d020a1000c10b5000303074401e034000c1d0b4042c00600f4240084600d180300e119085540002c05110511200c040702000c80040c85092000069854585d01c581900b5000366000b8090020320190380420154007102058102081030015400d01401c490781c00404c2409000309841d17903684499200940c0d03400d400800c070403440500801700c2142c40700c0b0700600020071405502c010980a400005943c0818401c55102c1c0c00c090b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 49134473 1250 49133223 49133257
    0x60604090203040c09051303110106050a15030917120105030a080304030f02070f0909110111030a030c02030f030a021306020a0b2d270304081203070c050105040501021b03 75
    0x2220400e0001d42002c0c1080d6011413007513001007400b85d10303485218040ca1a009100e040c10b40d4500d0001c04030000c108111620f40d04000c0c0810aa031201c0c40c1e054207640700241403484049554004070300a180c01350f400740a861680d10301c2e4418488400c002c040041c5400c500c0c3d8610313a00c803c18940e80b9080d80100074000e031020000107001c40d109201c1d92402030740c00e205035601c0391764885a288440449c0d800840d04291745035072490802c890368090014218007824030040c81181e401001d40c681c0103990041c0309051315044000344c0e0a10900441e028150420307101c0b41ca9060000d00c501c025003210807141500050b0080103d1014000180c031341ca5654000b4281c0c5640e9180880210000409502251645031000800000c0d00d00a200903100f0035000414070700d0925240f100c1d4080c10b8118a410050307800c100818441040e0101e00310003008039070101d4607601d072100101141c991652001c060304c15460801030008002040d001003d101c1c14002c0c50481c0c106510415035220320a6000070100080340e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 49135723 1250 49134473 49134479
    0x180c05040b250c06030b010e04090b0103031202160606060834050f030a0f060f0305071502120f070302070f15080402060c01060602060f010902040e0106050304050a0609030203030f0609060604 84
    0x141484400c403007030320700c0c045080529683d4825186100c160843e90201e40c49045c1c0c28000d5030320008110884a04a030203000c42501502ca110300c0010601000c0e04104d1000868604505540c044961701508000c82e44801c610504014000b02600d0003001e0006840700081a030a0520510350007220070144c91441d20038089010400810203041c121324144041444540500207660002c1c0d40b0540c0bc100c404144414002c1c201421104180c101640c0c22900d003605002007940003c000040d50490001030f040005490340a030b00d0161002c039440303007032400041c101e500c9001d503030050b1a030740e40300303070200d400c00c5440d104603080121003801103616030440c1e20021405103200303890041e007090000d49801d28011300c0114042c03c1d85c043d508540c0160380014103002e810590740702403500405a60904508260404449005135a01072046c12b04011001c0301007810300005000007496164800c4c0308200030a103a00c1c004e500d0350012503c130589681400b000034540c3c04e040c1400c2d441820020159413800382 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 49136973 1250 49135723 49135747
    0x120f17030910090c15050c0d02060c0d0f06050307030305040305010c020102040501050a0806040f11121501020303010302011103040f061e0314010510050702060c0106150507020a120305070606180c05040b 89
    0xc40f0300ca0a8550ba0030000c00060740c208042251003002c02c641d070700d890b0740c0c1454611003031a20305180604411503008604100302801d04e181907131002c1c02d12010104080f0380c0010f6000c081d0089801042e814000c01c1c01c000b0415405c0002081141d00c540001e0050306807403017041c0c0c200d001d18461640826070800030700821030702c915400340e03008100034000690f900380b003816402110240f0320182e125910000c0d6020358042c000d05200d0380b03e2401d0204840ca60f5503400001e45034003041c40000e051003180b8030305032541c0c10305005440c040c01507808030250071035a03104000e04c11200d80349400044034444c02c2d2040e04500c24010200d0542c0c251410003003a07403801003400882c900d060820390401c0300a122490060760340303000400c1e00e1081e840010900504208031a024100e0070000d10090081c10094040142c032900081e20480d05803c081c56100310403400c0c1036890384201d400003001c8034074016001c12011500d041d11491024244010003141e240b00005440d1842180070311000d841c0c040c41103502600b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 49138223 1250 49136973 49136981
    0x903020d1b0b0901140313020405042406030303060b130e07020304031b1e0806040b0402010c02040f0608060a021219020403020307030b010e0f07200106120f17030910 73
    0x511481c148203803107044403407044410000d600000c541101c0042e006099690040c00365002d0a42403000c0b51560078002890fa03000340d003030040280981d4541e00002c0500c03c0e0300000c0d40d0896100404003040150a200c034800800c038a01085011914017240420180c040718240e032040001100011803d40c00d010480d44c00000041ca00811440b0402003c000610400740044496002220700101d5500b0200c4003401c0d0007000004003520600c00000700840600090500e40141d04150809519299400100c1303131840307100780c040c0d0402d00f04111141e0000d560340c064000c44411005940c4e1980741c0806120076440b5034102e171010821403001254824000701c803420354108040c0801450039540781d02007400c28046501c2540c41001e01d4004002e562440d98200d0361010004892201c1e5182c0500003521140d00b0380341030040c464002c101440001400d50041e0042c205400100e480d042040c9001403150607000380031100b401a01000c11100700d002c8041d00c0c0544210f0001d0300100b555500e01c84014 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 49139473 1250 49138223 49138249
    0xf140c1804060b07050f0c01020309060d02030a02070f0b060a0e061e061e220501140711090a0902031c0905010c05010906060605040512061b0d0e011d06090607090302 73
    0x495a10703040056502403c030014248648030b14041d01c183c0d046001158100500d55880758103541003005421100e5440d503080710a03d00720700d1360043e02c03511380744450002401080d400405c2c144940c0c0340902030002c1c1c0411a440f44004071818070b28140c80e014403409524064078100d800c8143d4100101d11062030300c4640002c85800340c40f250402120766006034050b55041026145554006174280c503105440c41c4a20701c050071136a08a2410b031400000901c800034040d07000034403940c0460302d20100944a01e0351100c004005204400d42d0400340840c1c0020046054224440e1148014459003005003000a0f03900f0b0a0548854200c4c0b4a08001076901e07511030340b01140c03d5541c40c084040050214828100500742661340d940d12241880240b005001d0700d1a4008010381c0b01c030302000400c000e002030b24400b000150361107946440c01600360394040c00351000c1101c140e50900c0f0144509a2003032404081400c1d03038208403a8191200d0f004261038010640d8984c3c0019404a0140098184001c1d18042 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 49140723 1250 49139473 49139479
    0x9080607170112170703110d080108030331080d0605010305060a06050304030c080a080712140c0904060512010203100b04030c120206071b03030906050405010c12021504060f140c18 79
    0x401e004c0100042560020f28201c001c1413030f90707010300c19100042201301c500c2c07546c0341055a4607505115406580340002400b08490800316200e42203c10100141d904c6500001006c038403c0d0862850001e40c0c5030803070b1640c4012240342c144002100c2d80f09004443c0180303070117015100c1040c00d022040300d5640c4024402d0b014410800e5849001400caa00200040415956003510a090a15004001c482c1042100000d60b0604030b10840c031080b603084039600680c0c0c210090707541e80098000303d005002550f00660380841503a14a4445000640041d4032407a00c410348291081d407940210340640c0940e0102900c0b6030000301082c4401c10300c114001818500052446040102c140c0d6800e60102c21000c0403074000c1d41c0e5200400c02c141c0c01140d014054086810058106400d001c00242142da12a10240080e0307507041e130201c202802030140d51603403c0e0300c60b400340701e86c9860705000f80070f0441d2060307401ca61854600b0082075090707000443c5001d0585081800d141c00e1040b85041c4008004000d0554 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 49141973 1250 49140723 49140743
    0x60e0301150b0705160b0405090106170f1017010506120f060406020d060506030403230c1203060a0305060c180f06040308031009020307031a0a0303090605030405030c03070309080607170112 83
    0x480c0007518054001b000e09042c1c2c03940d6907080c40207125081e40103a005200340240036528100340d0350301215a95011b401c8071071443d01581c81c25034601d10104954004955480d040705c48881c009810f400a40c403522050321400300e40400c00e00c105545000300d110140307141d000320000c6400100c0030f80040180c1030103200b0101b142c5480d80000b07041548165003c50104241d004958543c4040448401c444031855100a0500c1c803a88001070f01c40c802c0f186c0244e5510000800280c40f9600c128008020b16001012690145800c0c0c0250b401d592102c6000b039141e0300402c504100700d240144074410003c1010784960b040c2495a5070308016030700050103003003141914030404174540c110b620145210f00f141d1343e004110017120b010010f0500d00c0e9125030320f018110522007030003c42d4000503020100c99052401d40d41d2650b0f01d081c13450541c000c00380d021003c0d020004540c0d0600d030784104114251845041680e032603885032030003604c50100c150003204140d100007004000080550010510345801160450 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 49143223 1250 49141973 49141993
    0x60403051c0e190302011415010e03031c0c09090c090603020a02010207020d0510140c0403080a0912030e1806031b0a050a030f1a01030308190e0d02010501060e0301150b0705 76
    0x260400d0b143c108107030402401d051101c8241542401951800380b0000d404480504100344041541800000303818144000c00082441940341082103401c0001010300082080c1102d90303004001c0e0218000550000741002804200f8242d0b520a04404400d151100d40b6041d191a209401035040200d0038001e556081c00441c003da100d40e01d0001d006481440905114840d2410ba10100c3d04070b64180b0761400d001408111007410007108850546c1e810440b1251901400c000031540704c025604413440058011549004040c2c0122100380c3d40c01003158200c180304d01d1580310780301d0101c003200d0841e4507a01440c581c03d41c0c3e0308041c1c44d1128088019090000d01c039111400310310310300c1081c1d0080340c9030214080c1c40800e000c80c02c40c140040040b44400c000055141d510000c19550014080045041d210361781010100c40d95407203a00c1da1360f15082555510028500d010b4000c0c2024810107004c180c0f06007600249241c188a169400311809010749181403c01003211076076042014200c40c03c1c404c0c43d481d4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 49144473 1250 49143223 49143251
    0xc05060a0305010504050a02041202060310080f0303150405040201020a110a08010204060203040807060201020a02071a09040501061205010504061206020318011503060f0908070f0c21050f060403051c 87
    0x3084101416107022480c2d500d094144012950001c00c00500644103100c240225042810804015501250090707200e440314a45091900f016a00000b0b5900c550010107200f0400400614420300701500030303610503144003090009a8a080310001d0050708400301c01d6001402c03010720390000f00000b90010074032030703144c051441c220fa2182e000007000da8404a002c02c0040d0003000241c0141c00144025418440c6081c0c01950b5175469002d841c0404444410100500e007110301516546c14000300244100e5a440740c0c080d00040d44504001a403d040c203001180314101406964100c48c3c8940c41d1100da130025072100b4009420250105a0031040982d44010307030442401000c51899100c91a03048503491403400d13004035185007200700ca0003070810582e500441c0d940c40c240c805070758001c04041c3c80140b0700d25014001060542041030000245a41c1200382c40c4ca014145c46114481c1d41103038203032140b110109079130b202d04840007400620100190310000d0a204104103640915040100b0800d40c42125 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 49145723 1250 49144473 49144477
    0x3030e0102160506010503010c14030910020403060911040c0e0609030a0209040b18010614060c0123180712031808030a032703020d050c16170d110a0f0c0506 69
    0x810070441c80302c0c0712801c1c007105020031030042c4411402080180d901207406008410f090b90b01001400b000f10000748000070500a14840da20808000c5646580764a40280141183c40c0283c0751701e1042d0b00005647c0c24980b069107800e91040d10303282c850102c41410040141c1c0020300710741d054091603107844c5c01616424001030141d881051b45120b0b41c07414082c034000f2040ca8041c0b0303441e2a8140181041714010144644c45480fa041d11503e0351003c0e41c10b0401d014102000040501002c02c242d6000301d1203000b00444d0051034901c003e5909900c440c4002642c0714514050300106402402907400000e0060410041c1070b0450100030842a41e5030f01000d0071070300301000540210761500050012000c54140c500c4000503d0717507011507044195240290340b440d500005000340728002a4001401108120140070a800c5890000102d51110111000764808003411038052150718804a0454001c5103105841054a00140400030310b645034100d0181c2d2241d0123488118101d0b00201303440c2c0368080 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 49146973 1250 49145723 49145737
    0xa0c0501050a061e0f05010f0c150c02011a090a02071103060703090506010f15030e0717010b030c03010b09150105070f060213060906050f0309070f0e040614041502030403030e0102 79
    0x580040c2031490081c072041d0082c100505104210095801801941c4134221700c101640c4080c600083c0800a8030360503204120151006455400c80f030300d45051340d8000e130b004916960b076282d0088c4601030a40300740d4011942605211988009160005110301c50698082c2101500420042400005c0480480c0c1061030680308200000e0312141142c007400810000f8031300500100401c007000300e2800d00310540107400f00c0440d004054454000300c1ca41d1004100da50082c21641d21940b54910704041c003680201200d4003154024028000d030890145418401c00e80c102c00003070001410341da035613084201d00301d10f5202e0321414010306000b2600070500d00380004003254850071005a5811000080c0a1000d095500030f030100260040709008040d4800241e8414068110069441e5102c41848500b082c21369040b001d10501600d00014601c09041c2c3c1603030085014101c200103848880d212850031020442d0040d011074400c4031112121400e40e0f0055034458024a40007605d000400000ca0980c1d00c006 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 49148223 1250 49146973 49146991
    0x60a35010f0e0a0c12020603040b07020109120203090307080c09010b1b0105040f1b030302121b06040b07120621030201020d111c02030603060f060d050313060f0c05060a020a0c050105 80
    0x41d0310308080041039190600540102c0e5041c5c0c500c1c007020340c0007550302c1c840100b0042184810f54007240f0054000d4209202003a0b0100c9500c16040a00724001e50307030b4100c0280240f0034420344c1800110f901d404140c00c80c4652025180c0e41c1160f09006011845a0200303190101200003101d00d241d13080001e1159030700461240c03071202c0203c491410401002150b0840954014103000b00800c0000e030002007000400500d203061a84036941d585075801c80f8061a809894507002d48010003081110782a4810701c505203075110b4441c5069910150002c58609004440c58400011200c1d003051500c1008141698030900c0054600010344088500b52900c181c1d9501003060301065440502c019010308442c0d54540110844c00c5140202c00aa41d421001c0c1c800550081c3da8030100d4010789401440c0020203411000301c2c0d680e01d03684980d01c0e84203035a5102c3c940001348103480d0700e61068808e44e1070301c110907040401002d03d5203030600684001e5008044650512a000c5040e0300091800e000341841a2005 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 49149473 1250 49148223 49148233
    0x1080106060e0306100302010e0301090203030f0d0e06040f08031909030c03030b030a0f0204090807021903030f0e0306070305060f040c020606040c0905030312090a0614060a35010f0e 80
    0x1010700a82807030448401184250004c10401000d60010260102102e13024607051101e41c402d000480c0c010800c0c01d00107905070000140665040304400d0007405044812481003116000c040c002e5a1500307015070b270081c030710002c0c4424140414201d002641d00840c4105c3c1002c080b21a0510200032910340c1c040450220b103500105006042e0540700f07140c0c9860082e00603017403105950351111040c1ca06920002e00c034036641c5113014180030700d0000303480700598003401d0300c0c221400729040d0184c526201d100c1140041c0c1c00e926411a45885075032800c072300b06406001081c1c140c9802409602074040102016001515091417000540e603d0080881900003030f009803515007000014002900d0100c0c02c0c4105000c080c0c2400c02c40d6071030000881d00307082482204800140c840c040d0742401c0503031241000e0582401c25401c0d1641e88100d0080700c0c00b83c04112242d43d003490fa1000d5420444504a10000d01c8099213101c003291129a202da404450340c40c00e00002d0305219549244044500f19617030302005900c8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 49150723 1250 49149473 49149479
    0x507091803141801120f11040e1e04030305060d0b0c0c0105060a030f02010f050724050603060739050607020f01020702030c10051e0309010b0109030f020d1a01080106 73
    0x10b1903071100c1050010814a40b0100409000c4484150030303000e4100b1091642c88840320030302e40c1c4140c5c0c07083d403500418040c007503804428003180e400600404030265251030200b2680d10a1001c440428440b140d500b8a6030b9940e910242c000f0300004202076003003600711510300c0008140c0c0212600c40d202d65428152074002c000c4000f07085480081c105405805111018402700d003402e030100e003031140e09103000707580c0350175200d8200c5081c0160b00700244100035480d40000c81a88040000d2032a0000c800200b09603600c07181015034171101940c5140214609002034181e030003000c010340c0044585d40c504c60210b80300a58400d55010f480c55000d9850b40c20800030303c0003c40d414030258000f141c00c24001d6080003071039000039445400f0032854a00c11040e40c01424921401070060317802126410030080e65040f812100403045030f000300c40f04c1606520f841420301c0b1960240c2e007004140c0c2d400980c0394540709041c0d800d1011010080f41c091f104d00d006070840b41e4a03452058245c50207886a9400481c1c0545 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 49151973 1250 49150723 49150727
    0x1002030709050a030b040204020c030f03010308070b07030506010804120912080901030e0a1205180d06050708010603110f0706110315181608040c0b0c070e01090603080a08040507091803 81
    0x26468000b14810203114500b00702040b860840943c10640450700144e441e80c035800f00c00e03c0c51003121880c4042c5c010100000081c4031010019107000d034080c01c8044034568076070104404584049074020b0101d030942000c100460740014040d080f001e61420a808407580b21015610700d10090203088400e400300190109143d40e15000d66100c0031400b600071f044c000303065910302a40c0a035000c5420100003000c9203140e10084540011529800081c2c1001c0c03501c1c03220b050103070161404407441c1c2d000c00d40794000022018030078440d414114421003001824404596142040d5a20005040c2d030501d444203480000c044c51031006600564030021700e10b00c032a0310142444003251042c0e04181c00c3c000d01104114440402070229092001036203003014440c0e03100d203410700c5800450b4105058040d800f1072809612440010244151068403c4c1039045a1ba40c42034202035910a001c000c094800500c22400311501981819810138132a90542d407040792100180821100781142c1300352058490170402040c03503 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 49153223 1250 49151973 49151987
    0x180807050d020a02030d050a02011d010903020105090d0c0f020d083c04030201030c0909020c031b0d05090904030e090403030203071209030212070f1a07020d02030406120b060c10020307 81
    0x341c903001802440f1107030b40029459850700d0244406024001504900311031007984100482401e0050340800c02247d000400d0091544000480156113420007165071080e00150034120301810303641c0e0714140d503a2991500c080c240b0411040760072110304504c11001803aa50094072150181700104400e242c01d481010004004a5030b801c0420b103104030005850740020340032902502d0f020b007808250f1142c0401c08480d10308542d8444101207201140440303a0040200003030260050600d031243c41c503032122150301e40356049000641c01040e81004050402e0820303084140d84039000e4103012052180020100c1d044800440e0101c002a80c000300f00500c40360003c06519101d103141904020340c4400355000b0b5913801c58071281705142e031004983d0008015003c183c08035080e6028048800290351505914091001a1465405030040110005031903100106550840e07140340d84010000fa41080d1050082117220342c16900000b0030001c5444100082001310740002d81020016a40c2c5000c8100500003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 49154473 1250 49153223 49153243
    0x30703050a050712030e04020c1e010605040e070503060a1d03040801020406090b070c053f0c0d0803060103021810120b0f010210050a060f08060604060b2b18080705 72
    0x71342d03000c0b014100400e40c404d0120040e4101640c0060781c5161161529103000c04252842110000480c400c05003050107401c43c1e41220010388080c4240c3c0c032100c4045440e0202c9000715509940600f00044960089800100c60801c40304018183d12403040d540506680c82034200001d50307034001404101099000451000405015143d981800c2035a912441001101d1264034800c0001c0885038044607044025051072000150310302c00096030004103600102c0400180c12a140a81007411801c4c3c1000c0c00104041a4030070000c619558540005400a400502d0ba0140b00b000b401041602030b203a55860b040c080802e80c442c03d507241e0042d00b620041d40c000c101414005d03e41c130031409a82e640c000500800517444000b01180e6a6141c0d2001002000c0720350021100d1103074505d001902c40c102140c401d000c1c2506507014080d154a6011020742c9100b05071030090144903e041041c403c00205050740c114074580d400c0800c000101d90004056010106429109005c0016408040003010016a086 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 49155723 1250 49154473 49154489
    0x30305030106021b030312100b07060504020f15030a0908040e01090e060705090d0204051518090105070207060c0b091e0c0102010605030d0206060d0f02090406050403030c02060c0a0f0e030703050a0507 88
    0x150045080102c0e03247d004480380b1007194082080407501c10b081d510480d10103003029101c0103850300c1c49428040041c0c0300c103541c182d000302d4028502c1d0300c1c035090a605a54010094458103455911101d0303890008018a070800d681c0590301384004070f00e5540345901c0c14000c0082110104107016040b0209003031401c040c00410a00408011300030303032502d800001307070082501220001b80c1544e80041a000315401d0700300c0c04c1c0d801205c00d62548001140c10000f140641140d00013000155903451080ea5605150f009001c04200090040f8000483c00300010341c0c0190030740d003074070780210101100c0a054880381c403240c40c0d02d40142c0160015542d09210707440042000b10014080188032410180d25110060040c50250307a00024420a001a41c01524001d99020740011403915181c14083e000304000d484c00c90000e8103003d9460a19880040d40600602c2d03240401c5180481041c0c0544d44070120559030306c1030100b0b60030020303d242c0e011b210f907200440c0500c000c0c015101c0b00b40b40480c10803d10782c00c02c4e06 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 49156973 1250 49155723 49155763
    0x8030901090b16030c0c15020f040506160c140d020409081204060501080c010503160509010c0f030801031109061e0102010f140711060106020307120c050a060605040507110a020f04140103030503010602 88
    0x10118142d2000f41da5100422440143d032849d41d448003c3c40d520039030b00640d0708020700085100e903019004048410490040341102d100f6070302e8445003032003031032809851580070140d4004000585403d078080c0025501c83c070560342c901201b4409603103108400311002d4640f0b99480004004c910010b00040301c070b00c07500b4070346039245141071041c2d031000c1c0211200354420824085140006640103000f829601d50f04400c0803141c8000500e001480904240012103540e40f8545000c0340701d00b81001c103039003c2d0341c00914900b0b500c00100c41c00105002c042401c1c504664a40b815154405501c1c81030000840910a5941c00e82c50101c002810b4424121412030081d0700250041007030340d41c0842610302240d8015a1000314240307411007115040c2610001420f203000354001082000030a40c841011980c043e90140090307500e114003541c442c0c41000900f0321a07001543c2e90b60051038040711079007807070310014400220441d82c200042102003090300203c010443c000b0042c00510340403ca0302030031200c0d41c48420 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 49158223 1250 49156973 49156997
    0x50a0203030109050403170f0601030f020708090d03050f0d1b0e091302010201020d0509010c020d03050c0703080603030d0513112e0201110c0109020906030d0c08030901090b16030c 79
    0xd40d00d10051040500055030f91001c581050b2140c05045a039050448400d04642400000700d0100b15041e2001404a4641a0038000719000c0b8001d860041e60024001d40c245031a81c0d05201400c9081013080b410003a0800030b522015180902500d005a281480000d088195995401266000e00c2d03849040c00b845055403d01540c0d4400c0342c5074000404840101410b51910050b40079001d60100e0580c007038100010807a428005601c1031402030b00c00c1e400c548800d0b500074019022038070700762802400c0440402118000c640a0380c0444e07000180541200c1c43d207201103c56000711001a240c920400104421010900ca010f018440807500101c8030180000305c400143c298003e099045e11004100314400d4031a5a4000e40c80620002402d0203907640d1450000c102c94020603440340200e00c03078294200410102e0500040d0fa552001242e1114002c140d105c5e03c85149a4200034443c642d00e640b030f0f4003d4400206a2000303076016400750090083c003400164005810b0328102c082c1c00c820042044100 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 49159473 1250 49158223 49158227
    0x501020c0406030c0b1e07030e0112140c09060f0705010501180e070e1504051906060306080d0c05031c05060405071e120e030408031b0a1106030606071e02030c01050a 73
    0x70204581101c010305a0320020388000c00700c80c5403504890385031b402010454009041c0c110510a41e008030990301d019560380c0c00e89103001100c8003407401c00b000380c49420025045180d407000400c03103450010300c0c203402c1080c0c05c44a040b85034007c444c211140e945410040084803c1c406405000340240c1905100b03206100101507074a0019200d80d02c5441d05080100752081c1101c0c034840c2d0002c1000e4800c0c0100c0c601046074001f0b03071180b0300e0069015071421800003611807080c070400d03013584d250002402c007030030b81003030210703400012071500790341c05d02040100c20030145000d982c5000e17013540703002c0202e418506a42004202c0710018840400e100181310f0b05504a4135805000a002c0010308101c0842003014000100030445502140c80034840040c0201e40c1040000150503240002c0350300c00304009021031103640391800000e005001c08480f5145290358a800000303140d0050020341224105280c0d038403480c0e40500741c0c40344440d00c0240110000e055080c01c1c1f141c0d61500c1000c0c03c007640340c01000c50300 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 49160723 1250 49159473 49159493
    0x21207030503061c0609050c1e09060111101505060711010c140304060513060e0a0b030403020c0a0311031c12020904060504020a1106011a0406030506130f060501020c040603 76
    0x10080400c8400400622503685404c08103030940240c040309081d411103031a02c00018400c040d01665030b80f0a44a150015240c110312400c0720704c0041c440a64906404814000015405402c19040c0481c08040f001d01e1101080790914042d49000e0100300b407803130701080009a15107900f201d4043c000070400d000228541840c2c41403441c03000c0c41d00d0304a4101d5424001208080c2429030781440c0400940010001d6211018207940c0e0544042002c113075681d0360341503c0e4070701d41a42107600129450300c10000000c000d809181c0c85030007401a106041d507000f0010783e10007055081160b051102d8244507401d81420018540090404540200c4403400468040c0500d402d03452440d1000e500000d12500b281c40b0340d08079000905024009540791302c00800c1c0a00510f000b40402d10892190038000941c18003e18410100b80f0100607955140a08201e01100504001001c041e040141a1760f00103144c030b4030344251070102010100008290341014002414100030a42c100d220703d00344002400810800d0003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 49161973 1250 49160723 49160737
    0x19080109060303080c211017010b0f010c03020a1a0420010e1005090d0c051212072a0b04181a0405060a0b070606060f08090a02040b03070503030c0706020601060212 72
    0x2950544900301b400941c201c038080b050780003003015100c40900070f48030b402c0d105041c00c2d40d202801064085904130744e024200c0e00001c0d182c035030040600340101800e500842507a42210301a03c15240741d60081e480d09010724040085662035400900101b1040c01089220400700300d01c80c8000502d111180b2000900007159801200d10035000f1411075240c10f401082103400b481406414441c03000180d041000300d078440d501c50075004e10070081c2403052141c070109404884001c1d1030300385400d101c2203484100250859041000141c00c000000810a01c14110010018291140450354460400c2c00007030003d45c011030600401424107030310311118004079010402e18002540c0c001041c2d524000040c0c060003403a4828800000c000a0a50900590350404016100d0a8403821030102240100300e64819084909402c00d81264040100524264104601d5030304028110340003d40c640d400203041d03501c06e1003104029030002600f0812107405000072401003a1900280000311068240c2c0c07040c40c842c2c84 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 49163223 1250 49161973 49161991
    0x9030c0b180601080601080111040602060a0b040f02070f020102010b031501181401031406010608060117090f0f060603070e010303050406030b0a090608030a03050f0903070212010902061908010906030308 89
    0x800290400c1d20305441c01185004001242c0075541c0d240f200039141c080a0050300c64035402c005444054840307081c01c44041342c031254001d008039030340c402000c002004e0712000c5541c856160000886501018009025264010040306100d252940300290849003040716480c002c2e00411580000d085015440a04482804182414030400b42400700300078600e002e0045201d29040d0008424081a141411400d000c580110303017150340c91722815694004116211400110030340b8814518403220545613402c050490100d6007210070504100e4201a60007000b140329034041d000700813180ca42000302c3c80c010b00c82100c5c840255415518000d00383d1145003d10002c0c0360300da0750720702030300d80354090650014411400c04112060f2640c00b01038a1b68002c6002c40c0000b810140820280146019414041e807900e0700114600400e541c01d0000d48040c1409a1450b5580c8a40280c050b0703d07460001d00c4448402c41c848141e4941036500a05844010b030001c2d02e00300d141001c1840080c1d0448107050b0006200 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 49164473 1250 49163223 49163243
    0xd020d05010e0a03020a0515011206020703142106060307050f03040c0810020c010510080c0f0103020909010b0a080c27030c12010c02010e1c0507020a150518030109030c 74
    0x140c14540c0c0034010244200c0038a02c1200c81c0c210078180d0209500843c103204000380c0d00403c407034075203100340b88500780135410755281d9150700a80060f615074002e26a02e4032905148240420807020380e5281d030010850080407901181c0041102c0e540b410605a200d0300c1154410700710b0900c940001d003203000300e82c5039042c03890000012600744400c10744158010560322045400c4009042015000f03500454180c82e425800c01004c1858143d0b0181d81c0800c3d200100d0080490302501c50402c8040d001d124507403418541c0c200f100c42444d840c3c1e07609440c06800010440c03035844444d07500c02040041c004040500d42c2e5014060700b240030142c028801c8180c2482001d10900e0004100003030700741103804204540c0308040703090074580c0c04410b400c01808244641c008010341d0000d491a80e0b04c5203201e200001103102c1c00c2a1910f01580a500504020340c0098200c50300316444001110030103100e846c414002c04e0b804245540740c1207850f09030704e855410030b030000e1143d01038aa40240840b031091030028412401 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 49165723 1250 49164473 49164499
    0xc030f05100507020312070206070c0204050a110c03040302150703081f050405070c020a0b091503280f05060a05060702010c11040c03050103050c03060405060a0e01060302060d0213080c0d02 83
    0x104001d90040200881400c2005040c00d0300069a039030b0241003444070050340140003412060010900c640724500c15160040780c680c2c2e42d8200002410020240509150f503200c0c1d030310b080b051000140000000b140d0041d95a41e084d401007207003804c004010300c14a0a82041301c40c0029070b00c01022504040d44055080340101e81140c9041051034540049402a103070408010510380e11000181c040c900075540140315645441038040c0d10300c241c40465821105c04540b9510038004c090003541d0005100b0a0751400341144100b070b446030348921080c060160349580381c40307038609200e210302c41d0040c104540f598400c0b80b41c00040f44442c05003a1000c0c0c140060208241c1c00d0040706c1505943c0e0780d400600c100651103450202900a00b020b0000766064444d10700028018200000c204c0d00031504070008052642e240c8000038040d003060014040a5500d411b00040103071500030280c101d02001d07510140c1c8030003102582403514142940115042c1c2e002c000030b1052070300c0d0012080141d5405690300040401 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 49166973 1250 49165723 49165733
    0x12001090609060203041101050f0a05090d05070e041a100303080604240602070b18150d020d0209030d0201060608011203270e0a0212010b0304060e0d0305190501030c030f 75
    0x190342406495603041010700310411a4682c0214030481c450311111922442d0000115580d002d0307020014404a001c10404500c1400741c406450000002003221034261a540d5500f810080c1d01d07400b803d240c807a8203080c0010040208030060760040340c000910300911346000000c654842520000d4184582100880c220303486d550403513246051015001c002101d03507505c00c500c0b00d03d030074030070840103018846010608009000c211402429041003940722504500c0821610060451503451400020004803901340041e00282200c012407100061301e40005000b0305080c00c00f000d49141c21645441014060150000f00b0681542c02450150511100340d14041d607031050400000c0500c004492400081608014070140070742d220b45e0720300f480a0b11400310200603402020380c1c0491b210030000c01800010b407642c014560050180c2c40c04a401c5480601c01d40c20141421101400617440300100151103515003003003041415207502c104110762568443c61624510360100a00b004004e02000080c80 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 49168223 1250 49166973 49166981
    0x10f02010216030e19030b04080f0408010f0b011d09040b09010207021320030c0403200613050901082b03060810021315020a020409031b030507060608030405012001 72
    0x450302d58807510410202e0038040c1c4000c1038081458415000c031160300411201d1604003100310307039104400141d103480703540c0c4070481ca030032603a441128500c1c1031000007900c04007406201500d01d046d400002d2803090304000101045000d0107901120300c4030000002ca561640390712558441c4d00301100f03140355213420581601a00c641c00d4007940c085021066003600d035000780c1c8145820b50600700e402c071070382122101030601800116218540244d0502c800c1006c60100c69001103000e0120200f4040201c85030b00003001da40040c03060b841d855941030004d01685c10025600c5000d00b44440003045005400b00422a4101601c07034900c0c0398202d283c42019225003e03812980241c0b40d15000c0d951065003c00102c002508000441441400b00d41d40000d80e031000301074003441a000607400b60440311035580901018040e035100840810400145002d000031070415250f043c01e200380c0e030319903031440e05003001029a0b009070007004a50b00200010000b07030780c11400c48150024001500044158502c210034018 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 49169473 1250 49168223 49168237
    0xf061003060b04030c0e0708090a1103070306060b030a0b01030510230406080f1903050d02160c2c01050102060f07050c01140103060c03050108070b280c03080106080405060402010f020102 82
    0xc0b000881c021082180c503642c0c00c01074607141d00c0081416680c44008890b0b00380b0940c0d1039030703868210201c000c0204200c5074440d20142d5018040ba85150b40c0ca82e65102200d00395844031003181307008800d1065003800390040c5d000c00740c02443c003440a42002d9801c06040c0d0442d10411341010124030800300c42c800301001c1c488005600410030007480e90744054a94a0314160403100d241c41c087d0408429015143c0c1d144043d003290903503240d07800d0056110420000354071032042200f400c0191241c120010703003010322400103820403000130380c00081c446c00400851407508411544090781c070340c014001030740c1c000344d00d541c13008100144880704d858400c000d40f007a209102c42400594204014404003a5408000c103048a01c2031000b04000d00b4148421400c40700c007800380d1401034100d081c040059410741e0000d481c0c0b091180804140d01c0100348400485156841030038000b03d916503107007070281500203000307900520240c102203503540303031554410f502c0f0341c4d00400081c140000c480035a0040d610035030540d1a0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 49170723 1250 49169473 49169489
    0x171302040e0a05010c08130305040303050904150303051908010b070b040206190c030e04090c052803060b210606010f0c0b092a0f120a0c09020904050f0f06100306 71
    0x2c0520907040c028007a006448084000c6061000819140302209964917142600340e0f45003401c0c030381960f508544580c0a2210594402d0700c460801c491400b008ea41c032001544a81c80303650f540c8180b0f09903004d10b0204801d1035000e200340c0400401680b0b080000f218002544080039031070740c5d5940d05c00a443c0b4002d2100c444c0a200d00c01c9881c410b216006107101c400c50b40030762200302400b4180703030802081d00c400c0f0304010403403405510100300e1400c2501c00c450070404042648000340855018405402c0a55441a5003030f41e20740f07501001c4c41c10325001c43d0200142c0001242085c0201e00d04150307841c040501141e041105980e0a000100e10403c0b29811555001510340c11504180d070302c16a0722402c103400803020064035104040d000300c5806881c01e0f00600600200b01c410442d8040080035043c0c04012001c9010343c010280026180d191300c00050f200c2c802c80140ca4820700c00c01d0208948006201005c0401c564050110b071100080009030311100480317650044503400301c01200588095804544 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 49171973 1250 49170723 49170733
    0x30e031903060f17010f020c1b03070506070c0e010b0408070605090f0405090c040f0204080d11070e10141512040c030b01120302160f0524070c050907171302040e 71
    0x700c40701400300080e40884d103000240480c0f105401d40c2c00c120b10843d1028062580030034650101c01034001800301224030020140c40704556147c0100d0020f5210740022594107050810501294508402150150460400160400c0d00380301e02c0c155281028028882172040109140c01180d542c1d40d19181c0030320015105201c0c504003084801e50300c401c0014035520641c28002c60f00f004030100d20940d811100413000400b5000c803009003d0b40c000c02845940d041d10b001d2a2400b20b0400700480c1c0b024014110b0b025a03a0038180791500f60541d200c01841c1c0544640c041021403042c0d1540c010655040810101402c215500c80e45480143c2e101f0b25400245102d030200700006000801c0f00045849a00a8080d286407440031401c07810b50000314026201c000060650a10040c1030030f0351221512803120600d0681c101034102c2c1348107a508030307980848100702000810301140c10210150780d0020304170308203d10030003600d2700d02c10b18940004003006d444184030f41502082d50785580013046001084000d0325 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 49173223 1250 49171973 49171979
    0x6041401200d05060916050c010e010c020c150a090608060102010e070e1b030915040f06050c0901030606030c020607050a03091b0305010c05120402010e01090806090d090501030e031903060f 83
    0x21140e40c104030030b025080781c50000054100d040c0440418443c0c944c10421207643d103401b2030b0958a9400c0302c0311290b0159039550f036101c1500703800d03c950340c003c60ba140c000345600e104440800090590800740800e81e128140031030908030740c01c009141c4c1640e12600b84070a00359140c0c00100e0052801d121040c403a48605440091426500c540041c040d1b11a081c400780c403070503042d02c2039110f88400d4a9654941e0b108051001c21100e000440c0b07600284076060142240526440d80c0080e55400c0c0e405c0440c22a00160030a01980c040c4a614010070150500740103803240700750081d40f0303034800070140c00511500040071502c2c03e00c60b6212031200c0da8803180c014848800c07910b46443c2801540822a01586444920740085e401030042e50943c1825094401307040d070340c5c0c1c1e0046801c003094034003042c140500701c0d402146003802440352620451280e40100030b005551000200680f090b40e000034140741c50110703003203c0b0300d001100f20b0742c2c0b401c00c82010003580504440304500411055000c0000034242041c04 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 49174473 1250 49173223 49173281
    0x90c160605010807060c0308040b0a09020307140f0d0b06150c030a080103150204151409120a0201022b0315051c0311010614041e0c03090c0f0806041401 67
    0x10342d040c1c0391030390200c504480e140c030720030f8a1384008500064041901c81000500050803004020ba1041011501164003c096800319261801e01e810808003d07019114501035800d28002c0a483d04208542e49071710306005460781c805015014202900444000c41c41080c150311850442c1d44286041c0100c990310100d100e802080b2a10a0000710390640301020151840e02840c020b8a068540201c900821502c00701c80035143c0e10b200000c0305030000800c5c0b010320080e94a43c210f49401032450f1024080d50222440024100070041c0b00608151403254030600019080d6402141e076100c4038240007828004c020613a0401200340c1e84080e40c0f00320500c0c03a0404100540103000403141c4240c46410002e007240491500381d5080740207002028041d09580d0510780782c5038120500e440710250741c0059140b1948080010780d040c580d020380c04a41c0315039200b010840c2c0016070078005e141d0303003402011680c00d100006840d02c00161018244124000c10910101d000303501543e0341d0400c0300c0010800c4003038041d203 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 49175723 1250 49174473 49174481
    0x203030301090618050403091211030303010b0406081f0519090e0c030706020609060c0901170a020415080606030a0902030f070906060e040207032a06140406050c07030e090c1606 78
    0x40d0001c81c48000c02e14544c00c55035801214040c680c9625060345103170610000c10300c1000720070403d0358100f0036160508002d8505200035801ba024050f40740f584c0e81e041c4440134281c0b1a0191003000590950030f1601a5083d0034841e038000d8480031910241030740c10300030300913500c000580c1000203840d240444ca00940c3c2000509005071074001d030240c65513103956500680e00c0d49805c94100645800100008024041c0700004203c1000d050400d000d11070003e4400300c18004003107540a5245034006801d00c00030613852046406840c80f072401c00464501035020450a00010b000c0940c1180c40c0d2100c40d08554090211050303501e0f41c90101c1b403003655034880a101905080c403c0c08041032801d8030b2038016040500844208a415448062856501269403500306e007207043c0c2010420310301c4400000040c2ca03401200c00071081c100c1e00c4070321400c1a0030700104440014006903400082040032100190700b20f20290340f40c62007110303017881e41d80c0ca0481c0a81c15114035085000ea2aa038003110008111041c4c0c4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 49176973 1250 49175723 49175729
    0xb010f030317010e0402010e0607050f010f061202030705090c0c06190f0507050306010c030905030a0609021003060f09020a0c0f051617030409050c0c0a03020d08060105040302130905010902030303010906 89
    0xa110b0005400b00410100c5010084c000c11009400c80c4001401550149401c485075860181036a4500051030310b642c0d0030a19440c40810390b903510380c492010400e00b507010f0003016001150281c0103100305980004d91f21000ea1095a01905170040014010108002030f5514503040401f42c2d01d0340c2c0761000d0440c1d01041c40c581003004a9103010803c0c02d0400d214414140300f0200b68a03810b142d0f0300c8020042d101c070800e0080c100c040240c0c411003c40c0301c1d1028000d00b03102500c904408200c081e118810080c104c004031041404040c54160308005180560880c0030880b0812003006a035400c100c8011a03000380001f02c060810302c001c840d0b000030050001524540c2c201120400804c0750740307402080154084035071004100c0e0b80b05200174000c070301d507540c8410b4000340d034204041d1030322042c03142080c24042400c5040e0050b030490700e0041001c81e0050360b801e5000d002444d02900d020f088d680040c00c10b000c40488068100e540c2ea5a070020814258450350003190000d040303940341d40e51042d00c040a40350b01c2c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 49178223 1250 49176973 49176977
    0xc1504090e07060c02090411100c0215090306040f0f0209011d060414070f0c12050403050d030504050307031110090b090d11250b040306050105090105120a03030f06030b010f0303 78
    0x10301c04510700c080400c080c025036902d03039100d09860a05408002c00c2c48805801a01d40d80795025007010a65a81c20040d000c40d03140c0d460300c0d0130408003801040f09440000d21114114001000403288035940459215841584220405800300443c18070000c01c59418500941080e02c0c00000300f90080e51850151445180f00c40d0490300d80d8801090205135290491550310000e9400c011480e03040c0190030b64034610a0302c0c03a008558a58a4079074240d000c15134940540403800c001401d00c1484401c1c40040300306802428140501d081c00e998041d940d02c030300000903080017034105e402c0403d0401803080b041c0d01c40070340790b040c0401c0c00c00707040c486183c001c02d42e8400e03000d2250000c05030f0713150302035188956900710310400740044800400d40044001112913800308650039011010841c41c1603100980061405990009650b60508042c07024044068005510561f403140340e5104042d80010708190315549841c000c107414100700c4002000d09250742000b02844c40c0d140010480000d071001c0301088902139 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 49179473 1250 49178223 49178231
    0xd020303040c05030c030a110402091e040c08070c02040213080d1808070303120b0307030203031308010b150d1e0c050d0b040b131a09070c050c010503070e0405090c150409 75
    0x20f10209541ca00d1740720035442e015085045504040b40e24000d444192080c0a0070252504000000292100c000140410002410451140501d0130988507170f14400b401800c0c28422400e02e00e0000c0c0040c01c0180009200e15000110320341c040310204c1c007142c010064002124245042c01101034040d003884103440b1408100414000707448100051564100d98040c0c46d06200e007440d039510350020b49240c1c6d2132540c05204103000000140c50810080124664482d00740180d0707070038408903600351012445c01c50b03c96480f96400c106000400c408a50f00780c48009000228101c50300c00202040201d24109050b0524010b05d4034407254111004000030218400100498400d02c0308020440b03001441441d0084401c00e180000a000b980c0408000040b0040b4810302c40108000220640d03811540c0e040001c2c407140700d61041020420403400340361000d0030b1090940c9000c41c0700516040c120b0703800c84c1c45180c841c0c010a0312050140000445000050032041c80c804402c074844880e0385c451721030240d14a140c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 49180723 1250 49179473 49179479
    0x50a1704050109031401020f0304030503040c0e1b0a0903230606040216021512040c0603050f0f1f0504060308030f0903090904060207021201090b090111070c060c03020304080d020303040c 82
    0x412a4160782058440c80c1415046444244d54140f8841294000c0d40d070800011685040040243d44928801d41d40c0907541d103814500200c0c0001c06501c803944803240c82c420f00c8003c000034600c08440b44040e00c034641c3c41c0d51901a086880d940c00d6403000d410652220b170b036102010200c0004d0036403852000105c0704142c40d00c4060008901c201d000303c009040c20b86246000501d0181c14031745d4034204055a46007007202003203907020260001e41c1c08403400d856611041042903010701034160b1205100d0501e040d2403920405000d001d1100400312420300c0840c05030b000d0300225945114001d842c000d0070801c0070a850740303800034041e4030584524418049000000321042d10010889154610203005015240ca075a03544d4000b07500600400ca074030181c1c042040c00d18000900c202c204450003a880446c250902071205400c4402000d0b140302c84890800a280100d0303c4074002004a4485160040d0840480c0c2400c034158005c4e5001203e1900810583c201055400405503000714083c00d05209100d0b9 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 49181973 1250 49180723 49180763
    0xb070314060f090c0f210708040c05040509210a08010f031703060d08070f020a0506040f05060703050c030d090203120a120e030d0603030201050f060303030708010905150409050a 78
    0x10003101c0550b480b001c500026070031400c03c1800c06410000000c4002c1c03d109a003d54001260010250000f03a42c0805840c00c1c1e010014080594125850b030424240300c0c2415282c100038031085006070350045407120f005c25845041000002010321f52100b00881141680361215580da20009100700003030003490020441c45110506181100d50040c02d00001d116030b000d0140d146e4100402e8031b503000107450341c2d66020400190085c0200c038400c01d0040ca0784540c07071041103000015030304181c1c010201840203200c170520901c000c20644404442440d1603060358a4121024491003440030118000855895800149034203c001001e1085003034808011146d0600c88090249451000001c1c00007100e103449000d01e50f0054640e0801d21040e01e107230004d0303400840c042d07400c91303401100140e42d2401041034220400c02106c1c0c1102e0120042d500d1030804400042c41240d040c003c81207026503640c0800c041c0c1e103400780120403a4001402c1482800058103141d5152500203070290b41d2035501079503010b2580f03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 49183223 1250 49181973 49182011
    0xa08030903030a0318020907050c150c070803090106030c15090b090a060c050a060c020f0c030102040e22021009080607020601210501090605012913090b060909040b0703 74
    0x414040c00450034842c004a007100505266242d142613402d05c100800f000d80c40e0904c0d400d215102c603031603455071411640e060307a00d406910402c103841c000ca048180080388900108880c501c4d038120070f0190320780d00c90080c128018407107070744018460800a0702c00940c1c0e41d45e0606010310b82c42c1680b50440410360316280c2c400c8500c80c10410303643c040017081c0c0c24031059004003c80e0380e041380164211141c0000641e03034541240c08504148000d03a00c5204074006051003003040700c0d15410198000d504051500b0802202100c0c00342c680e00d07413445029400c1e4120794200c03170780301102074009220a008011424000c1c0454499000720b0909000760400584241d0002460707504849401c209400551300c0880401e01e41c00d02614129290f54032680f407030000c42d90a004075406031018588100d01b044030300d100640c0c041c03a0100300c82a5100c0074041500d40b00d0315000c101d811581c40e007801080554401b40015128850b070301c0e2103a807095071201400107000d40a2620341c0f08000b2510200705855509103036041c64 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 49184473 1250 49183223 49183237
    0x303060609060304050a0f050f0c0604050604060e011e09030209060f0d0602090105160606081c0f0806060f07110111010603080708090d050d0c0303060e091b0a090216020a0803 77
    0x800100003030700840c02d00c0c80c0255030090090041d10f450145550f170f80040c401c413400f400d40700790780309854004040b0014000e00ea4106d404a40481c945450702010a40380d00903842003205008045a2910032a40642c2010781c2103a81851014480c2c1c441c000c020b0901150782c00260302628000c40065450300740821241c4040100401c80140b60a1543d40d00300a03600240c072903410000103010002000808902c0704141d14450340000c80c24900304a4518644081450311004000300c0c50301580500e40c1003204031038041820718042e40c07140c2d1041c010a8545c490b0071500100d1140009502052140303500945072001002d9903841c040d50411a01a07003a200a070101511040c0104044000211208001d18202e0400b03040040c0140380754036043e007031004000f8040b011464149804040550504c1803d000c5e0039054a2205c041c10007002ca1981c84040e00b81820408442004104842daa11780f221801060b200006650b20051b852000c03c081403a08800c0340150207454001c204440044203807400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 49185723 1250 49184473 49184479
    0x50309030d0c0504052e0c0b16140406030b0102010509160605071110080f101a030702011b03061805070804080304060209043b060a0c02030c0d020c01020f030306 71
    0x380448064038100401104602c181800340400c0b001980d034441b1025a0a003001e40640c0c400d00e17404a14001c80109000b4510101b003100500191000954426005804c41035682044041d80e04640b0f040d00c240070a402140702290001c50300260300f5034103400c0201044804e134001d2000362503524107156140b04240042e1000e005072642804168030410152445034041c4000c069500b0b1020701182c1c2e800031090303003200055406030421a001c2e0115407080c0d000383d15601c903812014900018840c9800c2e0251b0210750b20040003011072290380c401d4000204074038600b40e8642d50400d000502900924461156211126082e000010310541e5803243c140303e4001d58540d40c0280e82e407603460341341c56400140110707001582401004090307229840340c00e40f02d55041c044420b5402c045501440d40d101d002110354441c421152907140350100c01b140d2030360032001c0904042240c0c41c40a03400c1c3d086014400300507015118000f41e541c003851340000d64045141c030a030240c2e81100c1808a0694413407000711140742d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 49186973 1250 49185723 49185727
    0x4120906080a1109060f09010f0903051f0f1b020c0108150402090d05030708070b01052d06040801110a08010608010f060c02060c060f1005010509130203040c03020d05010c0305010605030903 83
    0x400b04440350050409030302c042d4415854200c40300002201034000200c2e0200c24103000c101c60702e655800404640c41d511080c10640c290300d00e11364415503104108280d07917000002220f44100c07800141d0b040b56840c0252030b00107002c00c40c1200008101800400064001403042181100d001d50041c900d8600030315901c06084403424014080c00003961010400507004001c010f4900d000c10014800b402406100d000902da8504050811003052401038100c503120b24101c6a6080c0c80011960310000000700840c1103120100200000442900456000003402d508208a021810302661700030a1040303610385401001c2e907201e00302140c076134500b40526a41e8582e8448140308890254030b2450a961000700a01e1502c000392200700d0130a601542d5508407049254107020002585070100b201620081c40c04e01d0070501e009000070140301109040071011540003011400340841f07842c002c0040c3d900600b072000b0949403803815600030180040b0034800070386131800100303140d446001124090426003000394 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 49188223 1250 49186973 49186981
    0x1b1101080c2107021c09150509030307150204090905010e1009020306071101020f12041a0c07060207020303040504020a05030a0501140105090111010e01050a020405180705160c03020303120412090608 87
    0x1c2400b000c00f419040030b600c600070f10200c441c0920b1084030a0b0b0501d81d84c2d808000380c80c00b40600c0b0b05100b031817003000030f1003000d1040302919203000080e9100c4941103000c2103400403100b42c2100083c42540c000c4030107a4141041802131020541240d00b03001410400c4903030183c1c481c9003003070417113407501c03002940360b001180071410851113090650700320035001c0300040c90012a400c40f0062588042c0740002a00c14141c208805c0c8150384298000c0d594120058039514602102c1c02d0403548122240108542d5000c41c2c002d045d5181081500c0c094a4040c00440d41d84a040c040074110303410895003246454100301c0046821011034404104201d4103848450a18814400540b24107507400000e01c1150340e00d09911094032024082e0340d0041c07410602c0165224201410701655043c01c084425018008509004070700d64085e040360040c441e12220101030090600c0c00c0380445105520180d494400450b005074000400c11015000314803506460b030800440b0007040d15044035501c1000c012410840020b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 49189473 1250 49188223 49188277
    0x908030403050c0115060c0b09070f060c0819020604020a080d020309060904020c0a0b0a0e03040807050409030504080105010303090f05010c0215090d020a03060f0b150702060a1b1101080c 82
    0x1a0240140d40c3c0c0c0041110040150306040300d082540c00040020358540342c000511203d8086190030054910160051600300155030300c5400203482100104614400002d0511440d80180c5908010050401e8461411032400a541d2841920140e00c941ca4890000030420000156401e400c03041350084e5091100d45000c100b0365400c8116200d030401d808206070940f000b01032045c4600107218900d000282c2c1445410325048079540e60784100c03e503008000621600c000000e0080c00c0b11012280480c64020902c1c0840369400346510050791503090000102c00c26402602120580c2c601425a00d42c490b030310300044030340300740c1c00001a40200004184080d1824940000d08010750302810382400d101c0b00d54046280859243d0094034a40e07510901c81c502c104180c00b0f01c0c0f00b800c00498244040d0084010740460521441100910903480020000d0915000350101c6040740035800207403252035418201541040d00004601d030001e40704500007070018030002c0c140c564090700c0810300001c100040c11a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 49190723 1250 49189473 49189477
    0xd0e07061e1d0301050702010903030c020703020a0b07031110060302010f03050403050904051b04080c030606030105012115061401080601180b340507060504030f0b060103060305010e01140109090803040305 90
    0x9400c00c45505030020b1180340d202400f403d809003042c0c1c2d00000d12010103080003812034076444000c034110f400003101040503a0b20341c54060241c4000c1510309036141800c1c82c040d0b503244c606031801c0c80540601c2c0004038803180e031a0301c170000b100d0007078031080c2615824100440c1220002c94000b80485c40502c000c42550409034040c80e881610a81910f500030110070602c81c59811a5201d40d6069025000344900c6c0d06041c010141c02080560091120f541030001c0c3d942c4003c644d200c45600b800c0402022000d0250341d20481c5684080c0150400c03150f0b44481c0005000141d0b0741d1454041500c1ca00440c115510942c1103142d591400101403001e642050410200341d032001203441401c40d40030301204550110f042403511100e90400a40c0001303045071030b001307061004a40c404410b011051004102103200f541070344002039440380d8852041e540c3c100c010780c020050b503003025010350711340010881c0c1060b0550040080200348549610240e03640c8012409441003600000d08858082c40407074002405400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 49191973 1250 49190723 49190747
    0x1202070201020a0507090b040f0204060f050a0e0405040b09010e07060f051804020f031f030506061315080303090705091003060b0d0b0f01090516080403080601140d0e07061e 76
    0x410745115103c940c840b42d182c188182c0081c222195609400c800b1403406102d483d09503001e850301135060502e0500c02038080869080e04c40144400020a0681140b040520382881034009004000700d0074107040008110008032281e0b50760b50301e004080d500b0440001040000c95141f40c0e614400950401411101e5070082d0507424034503134600b1065250341d40ca50001d01030302c24956603503d8481c0b502442c1d850b4840c0c000c0c101070796422181d22082c008103501080d080e6100905a6a650a4103034a0b6000b10080544a0045901044800020980362300c0800154020b10811040315201e58840b006c106103c2001d0301d84c821244000d080400004e0025000141001d0004010014440c020340320441148030854100088070900c500600c4900f101c0e204043d000210303a603640700d40000040c03001d0000b42c006003025040c49800c2e8001100d9078414080315003441c3c04281c03d2030301c802502c00343d20090480c007103078401d00303004401002c14614450220b0300e0300401810380c100028100020283d4505031681c1c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 49193223 1250 49191973 49191977
    0x30415030911153105060408100b12010e0d020606120601030f060b0a030c0e010b090d060b0310090602030603011103060105070b06030c0d0311121602040b0301090c080d0e0405071202070201 83
    0x11140040101c0592030300a952591340f41c4a01c0600000348201c20720242c0ca030415482a5000d100038400c844001808542d040980c80c000a490340c0c011000600c1b80221141c000c1f100d600b42040c401034840f001c1003081d1441d919408458494a50a04100b03603031061103028205503004a00400100340d0340250744244a024580000d88840c3c5003010a4201c005a081601c0203026450704110004601c5696401071403010300540c01d011640e80010103150303003c03002030800d0b91075501d507054994007444401684440a00200a01c2d80103203810380c00b94108032074141c801e501e40b84600d0746c420618021a44200030589d01d46203407180d19a141e41501001814550b01840b400e040a40c0e1901d80704000401640a03444511040300c0484519150144000e0355043d4090180700a4040100307100003a920140e04a40c0403500d02000c00c0072900400c1c6150010300702d10111000080d00d1f82d40840c030444011003ea8a0b03407513840c0d0031401d00058400230740d1202e000030009402c2e1007048140741d01400c4441d00c14 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 49194473 1250 49193223 49193227
    0x6060e0405040c0306150812030c030106050c070906060e09090703050a020904110a180b040e0c0d110d0b01060f02060402030604061d12030105010e040b09060402090d08030903041503091115 83
    0x3900d6400841d13035070f082c0e46c400c210070619041c4506c40b0200020066a8220000300d4610f00e041102003106e070106109a80c184440803c00b40d000d004140254006418041410842207546910007081015844811400741107100302080110b10080f6a8105980d00700006181ca44090303400e001d090b01008000355041d2041d81094039603070707403421580f400a100ca031100100c000c42c0703900f8440480e02240201485903190580b807113941800882d001d010160116084940003280d03051a482029051a9103940502c80018940421484c16110307410b80f40740e0b9075983c40c0780c541d41c1801d85e990602aa8081d5155000f003000400040c000e400c0b003000e02182c003c1e1854003401020b04180341c520f150301d501d21440340c0440184146d50340003091005910702140d06010064045000c40c0c4824009811a8040c6400281d0108652180d10201a01a81c4481c0643d501e00d400d0040d5900c0c0e40090281a00d001903c01d210041a8400d002e40084135811452410001a5a0081209403c0a0001c07002c1d10b03007007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 49195723 1250 49194473 49194479
    0x2030f0102160204050a1506081f03120305060306010e0105150405030105070207080d0e01050d02090d08070302030c01050c0705060f0718030b040c1d0c030903130b090406050406060e0405040c 84
    0x280040e062408490003284a02d0b2400e10400060b039a005000b540b01c585409000c88901d9201c65130b1004440190514a0302c58440f4540706001d40ca1141c0c0c0d03a03605600b4450000100034400200040421140d40c081001351103070130405440e59028811041c0316403a11005102c1860003040400ea0b09030500c1141d49000d9888000c0303400e480080302d542015820444040013280018010703510540207921301100c1c0e0203200c1c00080e040e40500c41d407110381540d0110748804076444104e4800d84013030b00944250748070f04a1f4600256a948041d4940c007542d400c0001080341c5a03503200c25120300319402409050305030f07250070a100b10018000c0644041000210004030801412200c0078051802010b20402a141030709181482c90303d60b60100d04910304042004200c0c1d9812f0391400e1700410700844040c1e03a5100c040d036452640c050b40c528001c1d0029a0340001074955588001465264400c0d0f60601019503a00f08200c00c03281c5900c115008103607100c001032207038a465403240350301030f1061204440c4561 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 49196973 1250 49195723 49195753
    0x90409060f05040b09010b0310050405121605010b0a03170903011e06030203070e0708041b05130507080a0b09070509010903050106031415040f0f1410020315090f010e040203 76
    0x8251070340c49031116a41c6041c0400d00c000c030f690080d84a49100e00034090348031650007296a494802034682d03050759030394020070200070062010965000035800b102c0c1c1c07174000040082c1030040c1e8220003181c0e1036107411132426031400c004003244201c0380c101040402c030311030500840b1a01d40c000561240c0c955038440954403600c40e40c80e14040c00d0b400d80d070030001d0b0f414210300c107151901805400000c0c2440c503c40802c0456036101c04001c0d801390340840c0942e50700e40385a405c0c2181c0c0d895600300e00c0c0d00a501014842d01140240e00842c41980c46944074582034a40d81c841c00b045400805107207030402d10040010306014081c0c401000030460614007104281ea6a40700c00b42141d007070341c00889500d642ca020440460781c0c200050011464680d40014070ba08007550b0320385404000840040c1803008420900c1d0502204840d5010b50449902c10345440881d989601c3d00258801c80b518004100d440081c0340942c200000071504c2010007824207000c0380d080c0190140c0340d240040c81245e00d441b41d13025001c1a03107 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 49198223 1250 49196973 49196981
    0x11100905070f05010804020d260315100e100503090c1203070209010501110303160c080a020c010917061f1e03020f060a0203121911030406050108010e0d0509040906 72
    0x150240d406072481c6400c060300c180300c5001e103500250410010006100250741d8440000348025070140d8070000841500c0c1c0f8500c004505440d00840c004000f10801a401040849446109400b26602052000d43e032105076884c4101280305904600f0020f0507081940c080c000468020803002e0441c0d00041908000841aa050f1240300b84107820100b8041c04604110201c5409850242081c440c440e80360010150b41e400010620948104100420300d2800d0241207184481c60300301c0b40701640c0e01c0490380e0184d55928146c000e00d002407e0f8420010340310703609803080b001341004040a042030380c03034070303d0004c1d40b00b139a1000d0a40d01c4aa6204009030345040741984203050702d00715001d24160f42ca58010089049118074110b8003032002080284034469000c4119507108103030107034400140e110201c480c10800485824404014948001100d41e88c00503006584154418001846641c0c0c0701c00c100d40c265120400141130690000c2034014483c1c1c0030781c1c0070705201c2c5d02c080c00c001001c4c050340e22200107035 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 49199473 1250 49198223 49198241
    0x8040302070b0705101107020d03050d140a05040c080303061311090a030507081002070f0f030c050106170f010204030b0f190c030209040e07030201050307030b060d0203070305100e070e011110 84
    0x180e44044240305688038135010307201b4981080c0701c2c00d41c20404d40e40c01041d0300070a803c2e401400c100d0009180b03c401000c9500504107100411005440392812002d13010080c07509580940700d0710310031304000034103030b01c00011684601e501814481c4601c00300c0d85160094805210114041d44040c000d80445c1d4850f140a0002580500c004121040c40c00c000103084c100714654542c400d074010044070011481f9000805d000a90050400f581e203a2503003811038404106140041140d400c19000041031400110f01312200461001542c5c52a040c0d40300d03103800c03486103100040506d07000000244800b8110f030b2069902c24520008014040960344186080781c0c640b4000001095011500e11260b05251003100030030a0004000c02540d030554001a09500000340350501f05911480002810346400050b1041c40d080c209066449050205c4042c0203020200c404a40b4203268000018041c107030248498043c160719246c1c0d0b2040c2c0112401166000d19500c0d001a051240c401222900d2900d03115072509 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 49200723 1250 49199473 49199483
    0x50a051203010614040f180f0e01020406090506090d030c0f0609200108040507090b010c140309011e120507031b09061d0102100b030705280501050406050a08040302070b07 75
    0x10302e606201001d440041600e5000c061980180710070b000305c0300c82d109840706440f00f010003a006400412001c0c0003038012840e03068071050400d40300304851401500680142c0d4000c0c0c680d40d0304540c4403002e00c2254000e061400c0e0344041c0640441c400b090280700f1102c0d216010f0307900d035200c83e5100e49502013a42c444003011100c04540b07624a0200b1031040ca13101c00005001d00c1c10002604080d02c4082d80c2c2e005900440318040e9540ca0090126805089413059281e44083d003c281c0e400d550941c181c89410000309240858460100310f028540c41103265503d58003075456500f01061f10200c1700c0700902e40103040f803003810356421050300444a03404a03001c8601459581040180c101800285a02626120018a0342d514004d848142c0c0e00030030244503940d001d41e00003c06000c8100002d2400800f0390003a504810312082036008840002185501c02008500c2070501d81d65401c01111544194845da200255040c000d0340c61445c40781482681060091044501c40c50b101c240160056000e1071381211 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 49201973 1250 49200723 49200727
    0xb040503031009050f0403111c02060f010501031811040209120303061207080c060c01090605180d0206010b04180609020301080c0f030706020d080a020f0310030201020c0f0f0409050a0512 82
    0x5500b141038041c0003030b10440394107000c5404d06030f848595200010700010107116011813400d9000c42c081013020142000500807090800b0802070180d06c3c0d2a043d50300c501c0a0040d8000481d95500078000c0380b91002c070020310804a203040380c87d00c220005013980e28503440f907002c00c00302520f5074850007407d40c0c2c051a10041c540c1d900340001044084000000324082d680c000344010032190348007088004071081d003900c6142d5501807030a0300c00e00400d041d00e00200764620f4403045c4045030f0051800e003240c00c2c00d560112500c0954141040e0703070700d1000f4411a084010100824408a50781751101c9402032104807021800a44134107150069030026001001564000c080c4010a407500200b0000c0404050b00034004240c2411030007501c41074401c03400030600180101040c841011a0304131030b84c004034441030b680c072820040114090f00c8600e100036030041c480c0000768001442c2031031210040400040c802601441c0040c2484003a24915000b40c519010303082485001c50307003d01c004d01460307942106a80e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 49203223 1250 49201973 49201981
    0x31b09060f120a0905120f090306070c0203060c03091905010212090102090a0504060308180105130803090108010605271201060b09030609071505030a060312170702010903020c0405060d0b04050303 86
    0x1440d00e0b8070042c80c078114207080003084000305a0201d204034004090203c0300d951034507128000817291042d0550305800d031040400704002e0075804180402550703c00c0302510304d05d44038104500114003041e04c2c00c46441d04007607807803281c9039141009000101e21a20001d418150f10401c0c050300c00800303c4800c0001e94000070458454070b000d455000140c01d0032a4200042811a1180d03043d60146105400401d96803140d280d0582e07008a0658520640d03040e00340411507120810070361a60080c500e4140070070151000485e40901540c240c51100d400c00b020005020006c4032514011040a2074854006030208500c080d182420300404004e4148507100d01d607a01c44100c00c0c9450003000400752005034001d60b40c180807500c840306040c2007070031340d526103030b0303220385525070300380001d190992000340302801f04003a401b50160002c7c2040c10302c50081c00100120354800a05034242c0e1842c030801401a0010481349000c0d140c16845103400500241c80c200d00701013590746914401405480903109640040700700 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 49204473 1250 49203223 49203247
    0x603010b060f03040609031b05030901080c0306010f0c0303060f120c0909020109030f060209060703080601020606011107030305030405070b0a051801050f030103060209030f0d030b010201060b0906031b09060f 91
    0x1642201041d22050710782071445040316540c0c04060310042250381c5940501c0107140c0700e810b0b07410f03414a40701703034000d24130006141c5117590341d11810909021a01c14000112001e41c038905491080b081a10340c0e811005400d44c3c101c4a1405e104421418180d031030a01003100184401420b01a1081d01c0041c0c8a40700c144c104a4401c6009620402c00141440e01420050341d000401c0000c0760790001d4890201c04c2640341c108007074000d07481c81503000180480e0312020705900c0345180380904020780030340b0032607140d81004503205440390940a145a100c0a01000040d209200640d0301c14050020f4910b0552150561a225800508041b00040010820340c042c5840303000b090001c0310090802500d46060600015054001440b01078042c83d80401d42c0184c544003440310308048040b02040d29407400b04007201a004014032041240198070704a00894030800d0081110603102d001044203066903100b000c2d000c010100d14445690840b0b040c01b44181d039807036520160140c2200c00c010191100004220 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 49205723 1250 49204473 49204481
    0x3030806030f0705120106030501050708010e09061b0a050405100203070209070f080103140307170c0d051e2101060f030e010b0f040b010507021c0507080d05030a0513020603040b060301 81
    0x1010712030303040680740501d00c1400051410440c4c806440c0100c1e0204010f0910b4018010b90344041c00b154209810020981d074481000d070b040e41c0c20b0403c00c0c036250302e0300c401e1700355202c2007212034022205258400c206490006c001802c14401d0a1800c14503264443c008a410300c0300c203592501c0564000b0481001b10f1801c1c2d107203158022150b180c03c2d17503031044603840204000010312010304170010044d42c8084400050007119035040d0400600046a200400c01c0e031517aa0104442c210a4010380c0d01029250344244100c903040c212b001c2071804030240807030009d9480da01002c2c5013070168080290006840c00c3d07111b900b900800740c070745414422035100300380901503e0520300f81d21940d915181c038880c40e540c5d5030491002144000d460000d026100100180c815200f2680007075840b803180846098030080196802c7e0642d84108156900980e4441d0321595440c010804000841d805100043c0c000d42c29503c050380c89031507598994012001c1c0d8003c1407403540242d07000c0c0c036400094000c102d2542400d0203 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 49206973 1250 49205723 49205731
    0x1804052202010c0c031a0709090b031e01020408070603090c0f060f080406020903011109030c0a030c090e03091507020306010e01260f07060807121b05161506030308 72
    0x40840400380510604011140c0300c1400a040c400207030459428403035507514100140d17600200200e1504041d5241000341c0c4000c035514400030362030710b5010450340c001e030165141ca41006070040c0521510403025002402c10101022600d41d1709100018030113804001c0301d4000c044946001410403074071300b06039147c460b25810030200140b0300c0d00e040100c5a4800c0490010000784d14100100391160724011003e4031401040b51350541c02c0c018591001c2c5400e000501030a0411411607040b640701d401801221f42c600c0c840170b8036207080c1100070062015640c200c480114040b9058a02e0030030f080f40050540d1754000e0a13510b83c040081600011814100036090241407000c940440340d62604e40c030740c41605841d041c18000d12000d0049503204480c2000340280744284081a184815200d00c0c0040a80300d007142d4040004480c424042c40c203032000e12903900040305001340b040901c400e54000381c800303034001c1c40107968034100300115802203000900d10342030b5240480340101d0860300c0e50900030318100002e4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 49208223 1250 49206973 49206991
    0x80301060912110402030405011b0f030e010b0904080a14070b0a1505030c060d060506040b03041205040302060403140307200a0806060d030f1b030e0427150e03180405 73
    0x2c0100c01c04603896086076030062030201d6000da941e5a0328034140f805807549071500041c094014003c408455004164950540041c2e030b000c2105802c43d8600d1803e0711303604007145400c060024003040105070f1000007400c1c0002c181c2003405030300c100004e00020301c0d40070314410b5070450480400e00001c0a42e502032410b4500b4100e00080c051070501e8000380d120401000d0044c4114000149403241843c0b50300701c1c3c00200b10040003640c803255503818000030b0b40d004031003c80c4d00f0985031400030310040c06042500c05032030300503010504150031607850b40d4610300c0c20b01c00f112251105201e0000007907003417035084c610303104d0510700d0306804c07043e603010b03c045405141c01502607a0809820041c194551001818010750186017545051544030402e4584009039410003500c28108508a4103050300700c2040580084150360400001d9940c1640c0482c4240141c45031004500400111002c10000440303003588036240c080006050500610103480c550159404503894106d0a141e800645818428594410501 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 49209473 1250 49208223 49208249
    0x5010f0c0203060f060415080a0501050108070305030306061c0e0a020306011a070204020a0e0909070e060108040201081b040f0806090106060507050a08030712020a020606030f030c151506070803010609 88
    0x25400a40c41d00001003a40e50030b0804c410005409a446800100e41082501004170300c0c540c4504c2440d48800e8903040942ea998208800046c04440000312801105e40140203141940c90b60306c10800107600c80760000701040c42c0750341c0720160068240b00f034050160000d4001c10488001388140350032720005920403402d00d240c6079501004c030006901141d40980d811600165200030b5860300344e8030f0b00c410071800341d084102c07601003198440d40000d0440640c0c0d002c03485811140d50366001141c0741d0f00100c4000b40041c3c00342c1d001c0380d005030541c0e600b5040f501c0700c060320318201070701da007074651086409a00540f001e511520034080500380078071411002d482d10b8035000e0300e0107905480301640c3c0c0c15900c06c0103101000c004002071010740b040030824585451640290356400000000a40e1908240d40c80c030711074024044094030f00c0000200300d036000f5120102604280f054086455070a04000385403103840c80c0d007400c2c0c2c8141d03079480000410016100e0140f040e141c0d41802002003907070807242c005231299524 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 49210723 1250 49209473 49209497
    0x30509010b0102031e1204031d09040809010e0a0506030717010b0313020603041a010b0405121c0c05030c03030403020d11030f03010b0a03020c070303020f0d020102040e010b07021801090605010f 85
    0x1000c03040f21380c03905c280403c0c02800f02c40e940f0011410310542d0030060010a00c84144810107621800c42290700041c0101c02c112041418108100b140c6c007074400a004410802500d0703ca54025171000340b550f03200130306081c03940d86c0e601c0200d40c8951080f154a00042c0500300814105056000124090040108090f007980b40201d0303050503031405044041d2050001000040c1006180c0d8510702068003104200302165030b4540c0d80b0400394000b801558812444030700062401704c000a2042d030f001d1800d8551940640b240e0388103494417210028242d84c035000c100400100403908000540c0a40c1c807940c0200b803121143c0c10010b004501e41c81000182c0c4d0820002e0114003414901a43d064940f0706030580c0d540c0080c0b500541c024440c040d491070070781c05041400000d140d0041a004001202c80d002d41d4500505818124200c1c4107501849614021420050000c000d80c1800740884910107060325825040603076007064648400d0303201ca2a507503201c6905114550384540165541c000b02e0400207010f0303030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 49211973 1250 49210723 49210727
    0x415050306040b190906020d0b0402030403170a090602030f010602010b03060f0705090a0801090605040c091e020a020c03031306020d03110a0c0602040b070f061406100806030a0b010b0703030509010b01 88
    0x8000b820103811002100f010410894030101151000c090b0004108056046890848040c5d04049880111685071015960403401d050003103c2c0b0565240c0d880440d43c0d4092a107151340740c0300203810000311943d901d050310b0000301d9600c000c41c02800b043d412040e50758034188000f800d48030103002c024020b03080383c4180038000c0030200d0b4042d001101070038003a40311114400440d00d82040e076442003000350700b48400c04041c000d450b400703540200e002d100c1c520044c40e1141d64000c00d50b041e01141541d10701689080f00350b00156540a007599113541c2c41594503c003000300000389943c000304a07502811070301d090100200394042200c4100340c10503045c10b11462100f0798104507d4011301c11750354180411a4a84000c00480c0d9040700c0c09080c1d0f81840944507400d5040c800f00715401d1050440e0010b242c446900b0301003003150b44540c8203400042004000290707030802240e2520020304101c0e01031181d480500001105000d250307000c0e084841d0020b40b40c00250074010f0644102a1407052a64500301540d50315907 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 49213223 1250 49211973 49211983
    0x16150609020f300708040506060105040501020a020f060f04170606010e0109030227090312090f06010b07030e0301062409050a0506070201020a06020d061e0b04030209091509030904150503 82
    0x500485180401c0c215126094114204448180c2414105603c100224542c12011003801140141c0840d81a0307501c000c015107003889940501d81c007507888080e0170001490007020618000001400050a00700e41000c00207954001d5000701c4a40301e02c1c004400410502007020301d030300c44002d180044480c81c20500207081102c0602000c5d004032240c0319824104500c0c6208001c0300700200c46900c00502d00400e0480e1a40c12a1001e5910860082c0100f80e4105000480f00d0b102083d020107404140d284c0100c801c003a5000540c110144814020fa0f40c0c000d98081c4907460092581c10b06000c11070f0380c005181210070041d05100e0040c004901c400f400103441d40040101076803010b6600ea0f80d074035902e00050703142900181c001006140001840708810449400c808101c07404c6084a403030b0360300c0761b1909000303c6080d4011445449010311040001d07140c100f1805030015042070507a6088400384442d2401c4580803a81c50b0300990001030703202c0c25401c0910410603421480501c2d01d07261402d01000a031a2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 49214473 1250 49213223 49213237
    0x603020612070c12020c0a170709021605030a020109060b04150e0a0902040f0b09070801060509060315100305070e0a030b0a050c2802011505101416150609020f 70
    0x700800d0000101401e00401d001c0480c55007000246040d0350260354000d40c0c4020a00c0100d001c0c00300a0b4000861a14002c072001d505400c1304003070401d003030410f0307840802074006151414581081e0407411001c03410500c02884030b400d16500104148181d418000b041d54601424a8012851f107440701000c050401508005c0c3d6000354020305058513005906405044106800780d803103468801c000c2151203c41c2d001c41d9100400703071008540c54bd14080103a82d86402440b80d900407c030304024040722441c1000003181d1203200c10a1001842ea00400402c140c80b0702c22000601090765030341481100d6400c124212101c15049032041c000c603040d540c0b01c428400303000e483c090280340c0342c4010901d8010010265003500ca802d1204080c44101d048908002c3e1a4040350300000d546000500c108181d0922081310540b400681100425658210200c4008500700c40100e5120010301864206400b0b420250f1003290081c04c0d802c0300c030394419100310120349050b0b004107500c51040100d15a4401e500341a6960 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 49215723 1250 49214473 49214497
    0x30411010f0905060412020916022503060515030708010219050d02041e090b100e06070609050303090307061406030d1d090118050a0e100c170408091306030206 70
    0x80090448242c0b68000e143c1c0016500c50f002140218400d05170ba00e5220109000300da603c0c0c03142e101e0003a400082e2010009520050b0006000111080b203100b654007141d22401c807940c0200744d501e44030314086401c00c0d00c085070018410790541e99035107030400070200903003007581c002c5103052204141504c281a103100d07424180100400e0161662400d81d05690007003c0140300c0d20000c80c6810659001d2081c40c0c09120216850150084c0342e60070b01d600e05568a001c40e4590359000038000d0100441504045000c03078045031124038800c00107000b0f0010714000c03c440c0d402151203d40d540f80500079940c008500d451402810020011659030008070100c041c14642801079404104180400030a40c0941c5851740000b1500c0001440c1d007440e40f101a2015081f003801c00c803a403113071064181a14540310a15080758455a014035082040d64006081c0c04040e05140e507010070b01c401100c071900000c032820703a890b420100303507001c0906003071194030b0524490b0681040140e0540d030014505d4085d000c44840 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 49216973 1250 49215723 49215737
    0x15050619030204051002060708100e0703020c0f2d03070b07030e120309030304020a08010209010c060c021905030405030d08070504060e04060b070c030c050607031b060912090801050c03041101 84
    0x20080e40240d04a90140001a150000f00e2240000c040d5564009850703200001c0c4022001506190451040341c00760351a40308140d52b42d80701c0c110101c0c040c1d00318003a0041e036030013082d0300380100e0602045004505000164003520380031008074000b20b900c1041030702c8010390700100200000505002c0049900c11480e040c0000c241041e540043e117801c0c90081d18803a240c4000040c8009608004051031103103208590040c00c031900d6a412509034004e031904980420184a40c1e2400100c16800003501d4400900c1210340c0c80185004c0b10f01c0702225242d007540c0c0c50f00001418802410140490303030300402903041ca0405803d21010090a80c821032040c0300411a400280715031981d1680c006000070012001026119640c81c00d011103006002e1204844051141000140382d003000000d0300d20780c5400d5120803050400c000c80514032039881031030803503041740e440e140381000a080640b9161ba00c4d02590b50090011300b0400c40e00e0031190040c04155284005008000c0099100c42903422100400e1030160 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 49218223 1250 49216973 49217017
    0x1501020a0c120f02271b030a1a03100204140315010e0c0f04060e01020c15040501030b0a0911030405010b01030506151804020309030a0201150f03080307050712050409150506 76
    0x90080812550002c1d440014001c14117032403100c050181c0344140c036035901c080454803001600300080380b0070042044400d00030702c000740101005610070000152081c0761f00c180c0303100c40c0000a0400800e6840000d10640c04601030200d04e10345652070042c0c0009400400d04601085002c032120030051040c010089111800280d000002e502a108440521040079499130b40300d650140c00c0d040540300450051043da00340c07440f0707450110090203246008220703d601e02403c280044001e803c3d03850f045a007200400000260042040c0b00e496210211541c940303840381010710b001420740b090000910304050919080c45490303942c40f08000003050711241c02d159204c0d501001c43c44802820081c4507442031010040000c8208040028100110654000c20040c1d40e1101495804506805001c0c00304081c0842840001c000c50001c5801402c41e0030090704001c09540d030070115440007010780d800518007040800800c0300714055101d40401c100d1740d05498a0900000c15003c0c011600c0c80190402070800301 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 49219473 1250 49218223 49218233
    0x1c0203011d04030c02031b01230306010c02030f030a030504150b0307090203070c0f080c0106090e0c060c032b0b06091f1b0609140d120209061209061501020a0c12 71
    0x9504199020b8256200180641c801018480140208602052807141104949c10501c0468014034080c0f501c21815501c55400459a20601c1070040360944242c1c6c1c3e040c0c000b20b80400c098008610581d401142da4513161410224110505010102840c20110124480d41d00450008c7c1500c44d04040103032281c3c2c60b0342d42102d00a6010202a1000c0920350140c0306001c032032030080c6198403441000f446a25030b1ba1902900b20340a1050521240c0c200c488450500d00d041c600400244184404490416085a5240c8014425407000c0c0981000c144c0d40703040065420b00441031a64000c565450030420795601164596801c500c9a00c042d40c00c0d002c941c10a140240b2010307840c10721000c4100401e4410349000001400f50040c00e40e03680108800c100c002d007000042a0740c000b101540e03118074100c00404401c010703400652015900031400d11070004e202c0d4501500f14840c4183d00b000b0961403c184034842c004500c4c040015045410407100c500c0416417800302c807011030b22490381b00c42200780c0034200 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 49220723 1250 49219473 49219487
    0x12060207140a060506061201120501020403050304060e041b0804020910090c02010207061a0307120c0e19050604110405060c0a080c0d02060106021c050a031b051c0203011d0403 77
    0x51807500e2446031014902030026501c9030303491161004111940364001004054050b00704001090300030300c1c3c0144000c0410000080b034007481940091300305a10f907659503003103800a0300324600052030742144500318540350244083c0e140c10302a5119880300c0014000b0010200200081e0180200b040070440300b8808204401c020014410200480c41803c18000c0c041e51040c101682d805003042510b039000701e41d21388002000600200201324246c074201c40300c00000c0152800f69140c54050400180101454050512a04441303400c9521802481c400d403007100c1e80500954000c52031300c0400000c02d14104121029100300301c0b0869180c410040701d00b4a440000000104101310100c0c03550810580001e0303104260882d40c080e01c4050380c03680030072a42c800003000501ca80601c50105076000d58010001400590a245404200e08501e03200c043d000c0404d072038804001940000e174580a0b041c0c01c45406501c100c04500540c6554075001004a1031080b0700c407450191580c00002c14101401819 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 49221973 1250 49220723 49220737
    0x2120105040903200d08011505040312020109051203060405071d04090f05010c0e090108010507050315030a12020610120f12051606060906081903030c1205040b070f02070e01120602 79
    0x3140014504402d1501e0fa21170380003070000705c08580000004682048081381c0543d20301c0c525501c980c2090301e9500c0341962310f03285078141e505655842c2c1055001c540184051050940c01c080103a54a04044040c0821214000c0090301005804060f0782d0300752a9646141913100d40880340410391000b036080c10b4000910205000342103600e041414912160804814110700d641140c40d04500d0f03907224442803d0b110201c81c0040000c2041000a038040a80742c005040080040d003103801100840d036a02408072000700180015034070000400464900031030701180640071110a00800000960700c40355050000000144016074080840010784d2040042d5400000c9603520001130345014185080185403e01408490303500b001d0011401010000355880aa554030400380c0c0710b030300e0586084004140020f5140100503c0e04c14000100c038450140c0d5014501456500103e414441c0c000b4162681540701d01c1d041d03401070034040098000843d500f0f411a21103003c1607151004900d4490024071543c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 49223223 1250 49221973 49222007
    0x70b0301080f071e060311090301020a08060406060e0603040209040302010e07090902010201060609030b0a050406020408010f05060a0f0308030f09100207050309400e030316090902120105040903 85
    0x80000611600001420003040e030400e815209142c2e00d54520009112900c9400e0031800101081080b03054400c0d40888003003404910403508010800300060700b0381c2e000c40e0445000402036400d2180c24500341c07051a0043c079050909900e0f084d45140482e4041c00b0080010f4461030444001405041c001c0d009a074071001080180d400e002d031241c506d0001014030401c2a40107619018011802d24005e2038520262a000303100c1c013200e9038804020001914000300100c0d40b05409020000c1c036604240540003603100e14010200d014a0b00c0340078041818200e50000e148407211400410104040108580e0005c10130240d144c1c1070340d43c0034540d600c1c00c0071117041c07540542d00c0080c1c400c2c01d00c480030014003500c807021500b4880d030040c541c2d00d00c000c001d90000007602c03010300c0000e120204440b80000b400c02d1039100c0804030b021600d07000e003142940c0044130050700d81100403600d528155404103280c009000e061800314101103100b002a500d008050103414000c07540c07520350300140750080c407080e04000149 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 49224473 1250 49223223 49223227
    0xc011401030b1f0e01030f030e030303070306030605060a0b030c0c011b110c0108070e0613170d0809011505120309040623030c090403030b0d080c0307031209030206070e0102070b 78
    0x40c1c0b070101c02005048552980340380741510b414689204020810f01281d00d420340c0a5500c4c1d003151102d400c2c0c0c1c405510201e0030700c000c120b025469030301e00348080e620070300709914006042440c5042c4282601c400908040c810cd00c899410300140ba0110250703038200c09900104c0d600e0f1502c400320381d40103206850311380288104203600004081d500c10860312800b07600800b6103c4d01d10544005440074071040c0c07038880c007050418101d680141010005400304064108003550718a0344c5000c03240340b0441404001c40d403a00007800150a542e040040d8503004a0040000c000e00144a1145881c0041c180034081c0f003a0003000a0b0a40300b0b03000c00c29660302e140010810001107a031502855540c0c42e01c00c81c030000405c00c0c500820b0719460003251070b40c100d030405018070b00c0070382e542e0f6021030090503541ca156078006001c403440c002180780c200140461606200c01183d8170070742404c008d0001c1c60189070f4100e5160614545c10006a404500c80703030400c1c084d0900c503515240d44c03030060b400c104803500848044000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 49225723 1250 49224473 49224479
    0x304050f0303041b080c0f1203040e090d02060105151c061508090106051207030b060604080a03030608010f110d0506060c151608091509010603060f05070e030304050a03080c011401 79
    0x65106585046014a0f8004d100550340320215501c842104243c240c0c80000c41100e85918205620403000715810750050301c1c0341903210464440071103c1610307e42c20035171110004a07100c49d010880b144c0900021100103200c000c501c0414042441401700c04025454400c3e0080300c801c05907080b9801521a0050550384c511036440d008003030250440e100d500a40c01c1030310005542c00c000500892400c80000036080042c1140c46103034586e0340142805800c032008200006201c00d041c81009a0940b1079500469224074000240342914003c000400d50145400c040c0005030098408071040c00c101c205c804201981d4200004e08070740210801c2d81c6c15401034150400d02880e0f4010510311804c6203554141c20118590b0702110510b074200c40003146c40d482002a12040e0504000d403a030f0002ca03403000454103644aa880c00142c4038900c0d034420541d03858105000e001a0004800880d082040c0c00440c2041e00d0b0000196404c415031102400300340000403000c529a900790480b2030310045100c2d1072082565 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 49226973 1250 49225723 49225733
    0x20316030f03090c0e0f0a050714130803040b071704150c11120d08010b070201201212070f020109080d09060207020901030309031a0601171905010e010501031805060c0304050f030304 80
    0x1170201d8100901c81508000180d10300c005218240c0180302607520310320307a407130102d414810070342c00402e92130b0071050b49480004244138204010f00180c030011012903240c040320302e0225600c2c0410071681e040c0180c140300a02941b00310604a0100e140c6910345042c08000604107555032454401100fa0404182194040800d0300003c91000140f030036560451142c4c0c2c0c0c0c05603400d2500640d40020b002a001500b184a445d41440041c080c451065040e103203001058500312005500010184421102640c104030406400209080000c5514002801403046503503800a440c8680000c1c0078401e5560100f15092004560503254030740d5001d401c0c135072196101d0070b0180c030002c4948001c0303070002e509501007103280a000c4103040c0110300c10384981e00300b40c0c0e20000008803460024104003100003450207041140101d401802d009000300408141c095043c0000101030302c0d480708801c0b80c4a201c1e0150000041d1001135a19807120081c00304540740d460f02d241140c2801e9045516850600c00030091109002c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 49228223 1250 49226973 49226999
    0xf09030504050f010305010b0f07080f0c0c040b01020a051c0c050111340209040201050c1005010e0105031204090203060303090a0b031f05010c0204090510090305120106020316030f03090c 82
    0x4100b2502c03c052074900ea00110151642402840c8103c44c080c80711503003e1020002a21010380304404c80c40c01c240c440d0340110040c3d0400a0149480d5021071041a4a400d0030b05c140d4001090a1014140a01c450740301c1690310305056a481d04c154824a00300c043c580c0c41440441641d0303a102c402400100d00c80c2d08210400c0d04800483c40034055062000402160004502c0701d83e00d41002c1009410301c1207408000006400401c00c0c0d0500c00108800c4100d454203002e6080c0e00d60b44010000b030300e0f50502d01c43e04d5140b030050b08071501a5000b110402c071955000803e540458034505005640e950f0340b10f002c6800c40c01100311090304880002800705c0d280d689070014612909910b18510510800c1c01c50b044016581441942e0205a00101807000341c1055013003a0b10040c0500115142c10700c0c40c49070102291201c40c070580c000703800410081000070100800c2401003d2501c029402c240c051082400941c07030410009051091404c5200611030080e0086003805070020841da00d10f6649104107001a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 49229473 1250 49228223 49228229
    0x110f0d0207090506090910090201020c0402071209090c0c021e040203010e150a050d15110c0d0201051008190c09050a062d12050a08030114030708010b01020303040f060f09030504 78
    0x143c10200051004c0c20403942c010721031820003009042080803000c80701c000304a220790070390460103000c2964445841d540018411f25209074412000307200500350051003480103401031340100e4202500081c41c150f0010200c8001758040303486002070100c0710a81500c2c40c2d6803900507500540040000034504001e101c10511031051a80e0b0440100d03000c004009526040340a081e41c020103005c01c000c08140e029051500d81096260000303201e40e691400703d4641e40140046500d9544075034800071943d40e083c010207070003404003034071013030000d0601460a071241c46501c0088118115207003c00e09000318006010000e004032082085031382030040548000d400103006900424000b039040000210a0070343e070040000044000b0032003641070005441e48041c840406507072510034900c1d200d02041626005500038605450614903d0515609060519400f40e008103000c5c0d1400b440214035903004421070303500590061a03040396401c5440c0500080032050303100c880b080c0ca003503022010150004020402c0d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 49230723 1250 49229473 49229489
    0x60f12040b0730020f0c010603050105070e04090209040b090a0b0103030305060907050309060a050c0403020402031603060e0903032d0403020a030809030906041e031a01180615110f0d0207 82
    0x251409400340740d4407480c2458683e82010820700d40ba03103812401d030b8040e01c0c4c1c1241c1c2c0b0003030620708620b800d801820f5484640050340c05075942c209000c11160082442140110265801e0100500c1074000810310040104090400383d010000504014003c0c800c16001e1355112402664030350b1079040c020020701c811101c0a00806074400030500c520f00a0003940d210b001440010012990303202e55601c0905000340a40f14007210901c00800143d4039030010310700c81c0c0f040005103071212a040400a05403122913003d4800c0440d5041400b00c508030204c2102e5100900b066542405100540d00f80312082e00d07040300a2100d640d44003800704050f404121a50158001d0391080000c1d121078a8854980c401e9401d025881402000108020301d03010000644600c0d0450400822541e01c2d240c80c405000d1020010446c00f140300010300250810256004102c100918100320300c07400c120502c07441c01000890070052201d514111481c84200300086070015941c1e070700b0f980e01d1701c04451003e944c8150034011095 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 49231973 1250 49230723 49230737
    0x1217130906060302030c1614100209090112020a0b070c0f141216031113020301060503180303040305040603150807151101050f04081b060c04080f010501060806060f12040b07 76
    0x2d11907200780280c1c0d0081461050803850908805920300c01c90340f100d101280c600050168501c0d80b26800d0081b042c030003a2607040075a84100101c100511064140c10200e034502c03d20500c000503032078900603581078030000742c00540c0d240c0c1d0307904107050002c0140d440000020b038014800704e204208480404444501901c640c00400e00440c2030f0350302d4580c09041504165244ca40410106403480980c242c0311300050040507030503518543d40340c02d0341d009030052000309000006210f44806212505403660344c1683c041c0d415401d0941d001001c0d4400c074803650b01055100c01144010f0b0118591090052841034116800680d0350b06582c19a44012915040882c0d004240d400104c20180a29445000c00c4100280a55503030340d91240d0681240c8a80840c1c090040d003203402000003042101d0142d01300c920f21a07212071800d0140c40c90b2200812003094580d050500400403150002c00c2c064019000711009a00c0300c1103451040104d0094118504140b81281c1c1400300f0300103034102aa02804841e69440 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 49233223 1250 49231973 49231979
    0x20405010210090b1b0d1a030609060106020c01030f140f0105040b030106030206030a09051507120c0e010e010e030a051f0606090e040210090308071b0f08071217130906 74
    0x2c125400b019001c3d001510003030014003c064601d408502a05c11180001d0034002401d0380e2004903171032541084903061801c400d000942c5070030004254001c1400f0010700d003540c14860002c3d10383e80e00600140c181a111500c0c400c81840c29005011032040542d204501c52500d403102103030341d81c0c0a10615010768600042d050351b07403d042c020f00e01070380d401a00082c0303151224180100100180d8505462501403650350314044500316114601800182d69008541c00b20b50100d541110300c1c0c1d440b55410302c81310a000100698100c2c42d56000d1007001d08108440201c01070100c0d09182544400410f2406408105820071860b40003140340c40040070300c200403403921043c0955540980d4018440b4012140740000c0040c64050440210750215203000704556a4a41e01c941c01504401c50895400300184412100c41114214510040901e55041024589011242c585605141c00b03592825041e6054803c00e02034134501d9000c521040c0b4008640c0c0f0381b1a6840740d1003600441c0180c0703240c281440800 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 49234473 1250 49233223 49233253
    0x30a110910030f0b1b040b0c0c010f0c0b0a110406030e0d09050102071701090204050406230c040509041403040b190822020a030501020c0c010e0a06080c0322060204050102 75
    0x7035030aa07640003078102440d040a848914111800400c01c207610400d507142c075089544918050002840d00c0b030103660301e90304082011410b185030440c10b80d04101050740c034000b065500c803070b290120740d4006140100319140c02e280007000d081d410548080e860000900040d2041d8158405410101d21390700707641e5000360407031044030340140078821240164400c03d0144281d0b541c00030104952090400005202c103000e5020405594084038251452956201130600400c1880c10702a0a00b070005900c107068030f0005200b410300e0255000700c03801151120005404c0005d022000c0001d9213580301126200d550340c120308100c40c1d204106140c034441c50140d032030388410b0240202901807604400500556145025402040f0082c40e9059921800300380000020032070030b10084c403a0b15001d4020780403410f500b038005007180b100034000500610f100c42d01000038a40c00340700d240e0000e070350301002d669070f803540f42d840034103070104a034026401007580c1020343c00c200031940140b00f110f0b802e800351142440f0100c00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 49235723 1250 49234473 49234501
    0x60f080105060a230403050604031d040b031209120601030803091203060102030405010f03020904090c08010b09060306040201050a0c0503030703090308010816050f01020a06060905090f0a030f1d030a1109 89
    0x10240400d01c0c080a000c40066a28000941303407841c1c1154508081d600e0300d50781c1c81c000c0151025030101b00804110844003039820b448291014080c1c40900c4518403580100c5d955040409044003000c0e4003284120b02560349402243c4007000040c211005540c6a0a041c2040c1e4804c0d58134029074410707840d260340e82031300ca00280c0b0b1007218160090340c01d092900c1c005481030380071540074604066080007040180c1e500d40c03048140d80e40c011580d1405080c00c02c070b440b6007100c03101750370207104030074010400640d59400170f0050360003076080c6441c0c0e07207a1005100564040000c81e0006050740000310410480b40c0d03150303008552450003540d13103851590b6242082c688850441c50200c24400d1281000d00c02404e00c0303500c2c0d0000d03650602c101c0e4840f42c40d0762141d20484520703820240070a911803082c015500c07010000e00942407000009825800c060b07580c06000184105e4681d0280318200014400c580c808501c13500801001600366440c0303038003c2c43c0028681d410709102d2445050024040b5040e0b5154bc19 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 49236973 1250 49235723 49235737
    0x603010e06070e0603060103020d022b15090207080c030301030503030a05100308071709060c010207020f0108010e010320040f1b140a140d090b010905010504050c0306040f0e0304060f08010506 84
    0x403088103004a03c1d040c8040f540c8000e0925051540810031f8081002040c4010b20103103000c00c0e444040205210a0724440700009144c6a441c2804c105660701300400c2000c1400c2190040c510040e1f5810051800d06441c0c0140001c1c500c840c040800008207001c0040300451191610041c100881c6e0368000029584480501000d4410301e4140030301d42c0040c0d500740795a1861340d450403180e41000010000141117074000c440804140c2d4021641408500303206d44560755941e07003401e20b00380f5581403200d0344510784014800600481116090794550150107103007080c03030010240040c81406461011000070f0080f2411540c0449803442e4010b058610031010000702c0202000346900d080c05840044801d03880c0c8080e00e00d00c03181c0170092004200100d00c00c1c0030079944165007a500661401400304101c0700140d0046004600784020802651800390499500c41c0e01101d000840002c40d0031103134020600c1c080000400e00c00083d003c04e0309030704410000b24060350303a642d030242caa8948007404040e001d401 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 49238223 1250 49236973 49236977
    0x70f110a0b0708180405072304080d1b020d0308041e02011e0306080609060709091e020a02010906050a0501050307120f060c020a06050406050f18120a180803030603010e0607 76
    0x4001000000d02c076070000c0c1018481a807032400d0703400b82c4500180861b941613aa000105d1800c3c05086241010060740032004140416030605003842c000310183c8444500280d0700802c4078003014500d0706c4a1120009169075000303000c00d468007d1518000d044490309440036120741c10480d030301381440c9940c00c850501d02ca41c1a07488011800300000301c81000380c281013815083c19111000841c4001b0300300001480b0b000e0b4400100441d040c9044041d005040507045422240e05240190000780300f0f00d030540d1020020f668005a544020700d8040780104003001e0000e0a5a040400340401f0001a03040117050b241e0807000e0b1008a80d0307030304014640140c504001420030520348110404125940e11281c4100418015541c403401c5aa9889080f82c0c030450341160055600c078140400010380041d101c1c0c0c00120000b120840c543c5a035a6155642e03050074000c0c440b00000030380e0308400d9110704246418010044007581c000c948800c20aa1a504221107180c043c3d80f130004115446040006d08034000c000503 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 49239473 1250 49238223 49238227
    0x10e07061b08030901141608010329100306050903070b061c0206070f03021603020105120a110c03030a050c04180b220504110301060b0d0f06050402070f110a0b 70
    0x310409494500d0056800710011607411200000300d03140500441c80780d8650b13400061282c02800400c44031100180240c41c0e02481891443c04542d00700708441e040d02d0b00101c030307040340703c0748505800b1444291059960b0341c943c2010900481e650140340100540340314440c107004a603114000d160f9240a01c0001600b0b80c41d101d40400e030319051506602002c0c02c5c0c0103110601243c071380d8020649642c41260129880c81380c1880600030f05906001a005c41c0070980090078015146800080c040c3c00361030002e40c185941c1001156080c0b500381e110014200c01d81007002d0702d81c0b25504100c1d0700e035041143c2d002c0156040c480024100f503600002c81c1c013550b4006103180c600d189071001078401885c514262681000096503048000f00b5040352180c0c2445031440049040d1401b4540704800d03a800b1042c5a0003a8142107040c001440b45005581c10600001380000c0c000c0c1ca02c09034500070b000a40c0c040d07600903200007a810144244401c600c02010701500901e403814044009010b1354400c03a2003078806103101 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 49240723 1250 49239473 49239479
    0x609010213050f03210d05340e0a090609110a1707020106031a06010f08150103090512180109080a030203030c0d0b12060a0c030203040f032001020f1308010e07 70
    0x40f0090002c0c2c440350190071200d188021040070340b09205514840426170700d01141c079a450a820b0b01034603501c154460000000c8080d000840c5054101d4032050000399100c0358000080c85200e0500c10300344a0006140c65030640c0e0710f00301800101640d003e454852414400c5c0c07591030300740d504100c80c50602a41d990800c2d6000072070000c1c1d13141201820080855496a80000106800303024150710010080320380f00d941d040007000540702941c00e405900922030300000300701000083d017010214007603082c2404a090280d900e800d50801c1110a80100031303020201e03100024842091501e624504280c03201000541c54810640d59414980300c01401680b04100103003011280300081c0810070003865012a4140c06100011690040303d05010010742c0b100c1c00304041031810780a60030006d0000d0031f04519506003074950710f42882310910080d00740140c0800b0031240c14071002e0f051044851540085484201c1c290b50b00c07003103a010f5002041c140b10b4402d40441d01c4c06c011b1250b203400092242c01004182c0c6 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 49241973 1250 49240723 49240729
    0x2030109060e21090d1509050c010e030607090b030c09030a0f030e011403070509060d020d0c0219020d02150712030603020306060109080d390b0a0c02031e07061d060901021305 77
    0x1d0380400310380031b000000d4901d800f01e803a40101000684200054115140e0f03613400140102d01d0640d02501c00c0d0b00c400240004c0582000c040e0080c1c402010036a542d03607854211000c141e120b031614007900b510030340038410240247d102c10108000c1c4203a83e030b4070b001c01d444c034011140c176002e84600c1e80302442c0c10004605140c1c0181c000340b24804014011a0502842c1210302d41260013002460580c1078031119a4555194148821043e017503142d01e8042030240030341c0108440b40b4007400000c2c080e1203102d04a0303042c1d064800c01d546120391310914480111044500003000341c025840124003910622021503099801000c100054a034604002c1ca01c0700c2442c2c0e001c0303441412000d00d56511020340c114901d81c1e400c2d0700c4c04142e40c245003043d56450010003854094980070000705203800140c83e0203040044550f011007101d80e00f1080030360041c012905141030615a00c203e65005015504c3c100c0c000c1407070701e6021031340c00440c002007003034075240d98540080310300741d10031100510681101c00100b801185 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 49243223 1250 49241973 49241989
    0xc12060a0903031404030c2a12080702043e120403171e16020d05070c080d0e01030507030504030e15130807050a0609030b01060e030a02030109060e2109 67
    0xa0301920f400b042415805941103910035003560150005500d00712100140428114036612541d41c20240002c0e400003003203443c9081415024900940c14685801c0051004800584a03402e070010000c02c0400b00c140b000c50300b00385102c4010020079000820305040911203000460b2000b110840c02d624280e100075500d4040da10040c811070a1203007580003005800d00d0200c41c2c2e0701c5140c2c0480c05444003200c40000c00448030000b03190840117042c0102e88140d56501180c1300d0145856403c14075290a0145807228030745113030f90401d120702e1080d5501034010381d51040e4640c01c00c80003078034100016104c0c204100c003503d100321000740c0859840450034409040c030040708000e40404141c1e142c01d00221034509030221003940e010002e15030203000144081c0c5008013581c0c3c0181414101012030394507582d200403d03004144510014401c810340101c000da1814800ca4942d079038010700801241da082d01e030000c0105445d04c402403c030b01c5440351664600c51681d0240c2d20a560740e010390390525618104200d41e80b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 49244473 1250 49243223 49243241
    0x402011205041218052b06020a030902010f0e0306010e070507060513050f0307030806100c0807051501080703032307021804030f0509010c140f070f03050c12060a 71
    0x145020418058152441002e00452103800b090b0b040510211004142090301c03405414004140c2038100503981d14035600988038980728441c92401003269403c140740a20948000d481e0f2800004e0000440ba415480054410f200340c8030324001c14207a9004032508203180e01c0194159000360014800d2020082480c1e07404900c902c1e00350328090a40d039a841c103031102511001e88045910b0400c000300003003442110410158980103500740012610700418030540901518022000348842a40c02403140d40011011504550702aa40d16070358541185d540781486442025010385c4800801e003c1d0001c1003040460f45c155a42103c0184401c45061402c4540e0301203510701e0004118074070040e241e42d45035948d145000716a0101d01e00d010304002c1e001c07248042c2902c042050030011030100e1307130700521440086600061010742010f05a10498500703081d49818101034401c1d010001085070202d10b1090030780340b00b00d05840310a0510b02c14420021405030307002c105c9400210010744814408c0d406203c403 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 49245723 1250 49244473 49244477
    0x150b13021e16020d060b0a080703110d0b0f07050702040c0203090907030c050901030b0a030605010b0d05070c03081f0314010f0b0409020a0b0309071203030b0f0f060904020711030607050c1203061503040201 90
    0x6c0307508143c0000f5401543c0380e02030443e40d08020401c0050001403420080c01c03081c2600d84080900d1107558004135204001c1c0080400c2502001180400d032180054440c0341e40d004d0300802c03a092120340e01950b40d400607040da911076002c04001905062103400784490600b0281c450078107050000c1c0040d0094075445104a07009603943c02c0000201c0c406010710342c000d180110700c00e0f5440000c2400d48083d941c4c02020001401070680c0b003c000207900101c410307402801c0703000750041d1b80a414241c29200c0c000c0c3e0720140c1035000760142080d0340c89040d0720448105002c00d104205030314808080c007060700c0801401070341c4800c03900001c2040014980003503a04c1038000c0252202c040d01d0f403030300781d440582d541030503000a980c070701c01ea10050529910f1820350b0901161010100001d82000a1035482800e101a019a40115400c0200301000441080c3c403e00141514000e290203000140150404d00180601d80300302c1c5c1400003040c030540100d0b4010340000d400e000304000d00751b40c940c0d1907034009041241 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 49246973 1250 49245723 49245731
    0x304180207120302030403020d0804080301030f030c0204090c062003030106030c02070e090a0b0c0313080a0201020903070305060402010807050307020604030e0d06020310260a150b13021e16020d06 86
    0x100048406128002c100142d490058403810319040c0240307001c05420807242446442e505000c00718010800341c03030440c2c4d8000c0c2d0801d04680e81340b4003281c040140c0c2000a401c642401c40000808c404460003a0603a802999100700d03134030800d610011450348156468807550001c2005205c2544a0b800a084034925401180c04045da82c00f2051010003084078804580d4104203005070401984203040d94001d42d100210f80e0440c10a4880f800306010203480040054100041c000c407264003c0d010780b00300c400001d05417071805039030b41005a140d040c01c450880c001036010380010100c9000d0b0042d20f028a2041e801090150b9803980d040d11000b0354130820300e40c0201241402030000e00c1900096104441c034408007905680340908035400400c81000b0300c041c1c8500001c1a001d0044002850034840c0c1c1c000544c1e104841d40170702d4500040910003d0f56030420040865005800401e800030b141c0c00d0861000b807000800c4c45c0c0c580f00100c0c0904040e40c20001c0c00c0803100c00152500540e450f441c2402108001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 49248223 1250 49246973 49246987
    0x10f2a110303030405010e100207050c0f1c080405040510060207030f0c03080f0d0b010e011202030415050708090c01090b03070f120501150801080705010c0206070302010b0d060605100c020303041802 87
    0x81d02e1038004603012516691030741c10048080c0000c0c010622038001c0c4c1074055050070b0f041d5499035102c1c500001c005004814200f1400e0007a5500040d44014008000b103440b440012418594070b554050302802c0c0c0142e0030302c40031a030b000034188000011600141c1c0540011401d65923007080d5408100400d032140a0203c4010020441c0900280310704856404000d0340e40107501040426680458180c81c1800a003458581059800c202d01d1010440041310050396607035940f07020940c08a00071300d09191140742404000700650010811070142d0310780802c07a642542070b4801140c008919009203880c54902f480070130f1541d0302410300d90811821505204000604d0f0054003000c55009903c20b04000405c0d2207021b10305ca801625840c05041d5041c09000714504010003e4a0402041c0c40240980303800264181030510079403090204000003404c1034603071034160030550701400140c0641c5200751001c208840b90a4042c1030070400c2c10368050061401d09107440d0300280700b4805a080d010005400f04484 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 49249473 1250 49248223 49248229
    0x5121002030a0504120906080612010f0501030807030801150903110f0d03090512010204080703080c1606080a0c02010507120510050a080106030303050c1e0306060f07060b010f2a11 79
    0x694400d1000e802c000906240c503040401010035030140b1003003802a03a88090040300e51010030981e001000307540604200350046400340c01000714190721a07045142c84008800c00c034075140101402402582d54010b1a42c0b950b007030400c3d2404412071200407913134900c42000041c0005500d00c18012005003a01c00e0035445001044544404243c120002000000148468600345410b0030002e54004000c42c20309040c121001d036200a94080600602c10110b407000102d48104262481044c04080015400d0380c1c1d0b04c00a88a2181610040c5c03c1504180011104900c144a458403510031f03035482e0a044003010386d600008000241c82007103031403115400030605450307010080000740900400090184e1550900030220344014282d0b502902d410480c060001d6801782c6400320b0181b030305280540e25151980010358074803450b141200318090100c0d0075401d1100c5540b00b0080c3c880c00307807100d00d544018110100c6100202c80740c0010a503064191034480c0c0d0000c803380490302882495040300395103d003c00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 49250723 1250 49249473 49249477
    0x403060e060412020703030813050304081c090e040b040b0c040504020a0c02090109050402030706050319060801150504050c070b0c0c0f1b10050304060203100302061b06010f0305030405121002 84
    0x428490780600240001c002d0815440a001e4642e4800707031424030700b1513900900b081d1020300f03440302e0201d0004c6244244402481240c0041074010116001400405144451216250080c501084018600013065001400178502c40ea900c41114256075549507100c0c050260040c00c60139082d0024040402e00303440b184010711220301c10b0f442d150321900e400c0c8100140c190051b040342085500705403e0200589000540c60b0944040d03060980e241d980b401000050a00f0000e2442d1005042130000208954198024440000d0305814007101a4841c030030322066443c10340740e0b540594810019240414a208062a00702070100070702403410012424003032505200e021021903030b400c0580302603000ea90716010381c400d071403055030403c20b42c1d10600009409400010000b50441f50000001a6043c8900c001c40020f5903000741000c1d21505c4000d01c2c0d055100c205c601002061090200102d00800514a2a0100c90303101c0c1c02503192504101c10b200340003d4005015074644070710001020200d40c2400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 49251973 1250 49250723 49250741
    0x160e0f1915030b011a042601110301050306100e0105010c030e270703110a05071a0103060c09050603040c030f020604090905010b041d061b310b040b0a0e06040306 71
    0x110200702400e50400b002070036810784c0802c8185d0744030a510340d2810003020685044408002903000c800d141b059040c1039000d0009104a01b551070b104104c80551440c0d00518181c0e00242e0403a186507840016109503090540907940795000e801d07004100b99886200490b80380c51003850550b002c14946004100c40e100440b100030580983e00080504d000680c0900e25444200c5150a1001c0803a1500b8099917205110542e030420000180103401c3c850f40200399032486c19811a10549507a480c01c0c80740c001e0240007242e900240312074070001114509101600d00898100ea4116889895640c62031405c000b16a000c03078008a0034400080c0000c018402e0100d024081c00020075115609000c000464200c203240801020400c565108000c400040b01640200108803a08150034a0700e080d00c860300981d5110b010b49130180701c180f841e0740e0021484030800c1d02c88041907100540c460040b0401409240200c084203102800700300d91451180e10310281409025160b14500b0b80c482d107a201c04c2d210541 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 49253223 1250 49251973 49252001
    0xa020909031c0603061103010303050406081008060411090601020706090504020307021608010b190b190905130e0d02030f0706022208011a0402090a09020d230405160e0f19 75
    0x40b0130000e02c1090301170b612801040e18540d03480c56040d03660240c0240654050321003048814400a8100c0301c40540b188050510344046035403901d0700d40340c2000e40f0020105014011010f41c404102c19500000c0e400e020b4406540f6051400d60420301404000d4000811980440c031514503000b0020144550400c003602c42440003040017024101804810b250219424400400f064410041f0f1100070302500c01c401c900c6600c0d2016988800801c03a070852650300003035801206001c3c10350400c0b034554030080f4000c2c002c4003130702c060107140c0b40b060741c03070340a00c0c185550700f580108000c900007040c0d40d0042c20805240301100c2d248003905032070a164400c440d0001c0c4450fa55030352040510a0224103c01c021034000c840c103526020160012030400b6000b03100d1050315680100d42c50300c0140468001040c02e0160311000001d041d0f400c9540b9510b120255810b480f80d00a00c00701c0e00424000c51100c0e016500301a1240e06a87c84d4a40840708101e001440303400034050180050344450924041c06945069007 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 49254473 1250 49253223 49253231
    0x20d0b07140301050603060d020a030b2a0f070f17030709060206060906030c010309020105120903070b0c1810020a02090405010f060501030e0604030f09081006170604050a020909031c 80
    0x1034030000d4282a807507600310700440001d000410140d0381300000c403a800203003912910303903103038082c40411038015440d04001e1031115110100030440844009a00c002c541c0044041c15030500d283c024010341c801c0c1c1c0700d40c90020038200050404600c102e60b9051107544681c070f0384c3c040000c0381c2e040110650400d40718100003d401880412281750304001050300411b003201c5c101c41ca410000c001030f0780d4158070b00c0c1c424141501c5041d00c00642e03018034180c4000600d50b1800003014071f1b00c514401d86984c05030b0001c50b040c4401001080b6245c04071000d4a81100701801280000b212440801080c2070408a42e502144140c0c945800140c5460210354001d42c403400000c42d08440006144050700c04a8000310304140c5000a02440f580001680b950059098145004240f945c410121410641a00860507620542c0d640d10805003181d8060b05c1140c1e000c0c41c0c98810400082001074840600781c03000f814682c00300c50301c40050329100761500e80140040782164501401c1c3e44604100600308441a00500d540f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 49255723 1250 49254473 49254481
    0x507030f0b16031406190803030a060602150c0301030b100b0c0a0506010b16060e19030f120203060303090906040e0f16080703031d01030b060712030f1b050f07020d0b 73
    0x21254803202c150038500b03040c00a0108107015818900c40185498071412083c0034059004010700b00c0310024060311402ea9580c2e1800c050840050015440f5103401482152703110140007442884480c09a2400c0286604d142d1039030721031407061200a0b01100c801008624005405210071006007c05070200300941400b8115050a6050032016400080d88403c200500c000e412059440d54000c2c5a201c800001c003d030281109600d0108a000c0c15500602c5e680f8000d000d1607080102051410140d42d10518003003a170500020580c002a24501d42561040c07102a4103403900b40c484552120015200149151100791064549408041010400d421034507811202c12224154000a00038110007400071030b2039980c0007030220181c074221a0001c0a0780080c46001c0e0f100c0c0e0085420010020416900d030442810b11000503040d00611030046440c0551007c1c2152440c0180380807104035000d002403420f94980d041d0342c2030303116140e80602e2201c100420740040e030b2600c141c22141402410344201c2494 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 49256973 1250 49255723 49255741
    0x9060406110c0906012708030324030703020109060e15160c0b03070e0108070e0603010902270f040903110a0308041506080703031115012405040518040507030f0b 71
    0x1400c5890380f405590140300b009040e1343c020710102c1c0c0c0340c012400c242a82110800300000c14101c2c1d600a001c03903000010071720412040c44101d6040c296a41044002c14513910b2003095540d100c0e600c802404a84010800c000c0e090040400004215014040403c000d148503601c84841e4000001c1c134400e0055458060240980003c003c005407101070704180ca1410588000340200c0c0d501080309042120309000186058844d14012403040d10103003525489584914401d030181d0440c0c1002d24074805001d080207400c0312121910781ca07484015042c078542007901c07028400584042d070015010f211413005010660a01084181045070080d80c9000d164102032812020310032103e0070140f811814540c051206a0f004212842129498104a40247c104004081c2882c0000d24810040a961000007420380e644a403080c0160541d59041150076403074400c03e039005d00880c0a00c94020403000c0c81840754801c0c90b00419013182c0608125001076039a5644c41410050380c0d1307000c5510304400340520020403 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 49258223 1250 49256973 49256983
    0x5040c03140106050c0d08040213090c12030507110d0b040314090604150305010e0108060703020706270b0604140112030504150309060b09060f04050403120606020a0212070608070c06020906040611 86
    0x449607d443e01185c109074000070010350780d5040342c6242507520500001004800c4d0803075802080d00301d03400c04200082e13090160490700b044000b580c48104080c00707440c591030074042600340755a1002410305540c89a85007103c000044040144600408000c0c065036a9a4407001d0401404901d0780c0f48106005400c001b015114180e00807800240104010b2007019804101d1950250103481d0041c0c4030641d078100000038080400304600110103003610f41420142c0f410702c01450a000310012849501c448003804103c40c1991208001304030030740010320100d880c10502c01c914900900c0c2060403e031b00c4401c000804800f81d04030b81e01080c1e82d501400c0c1003104034043e1a060b4441150050014078100303010074942c6800c800a28440c0707a4403070010301098061403a00740040c5050710204141d50b165400650b41b1000700c90264400c08a4400740a41040000b50600580f011561414601d407a00401501c015201d01030132112141c00b8014007030540c40700c201410050005603241200241c20b180030340c0c241 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 49259473 1250 49258223 49258243
    0x5091f0501180e030d0e07050d0510050c09300601170d02120a08041505130204050c0406020705011808060a0f0f0614060705010b0d081209010b0a05040c03140106050c 73
    0xd400c00c400030740c0f0f80d0004010703192201c16901e00410251803520b08a420150107401807644258840800014060000348240040ca140c4a08110503105c003054441b0038019507410717560104488400040360f41c1c681a0010200180344180c2002c01421200360303003888000d80001d000b003603a58060480c0070401700045841c21415001410440c200c0f503a007244c09202e003000820600c40510042810001088024a82c41c0304a8004000c0c40c20251070340c0c80c04403401d4000344d1055040030301090054409508440848245030004e01c009c40c40e02c401524042101038403040e1500310070038001140507042c05124424000c08000095425000e940c4104840c901869208024035115050282180c840443d09280384100d4055460b00c0b06c81c81c2c414050200040c2c0d854000b80140581c004021840014040d0a441920702d104585c0d1401d130304500301d45075002c54035805912107c04100f18200760384000054a95407802080c51080084800c2d016442a402080043c03400030700c15520f0b4005000e01c5001c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 49260723 1250 49259473 49259519
    0x40510030929070f020a1106070c030b16050c0606040507020f0102030709030c0602030a090605250b0609060607050a060b0103020d0c09030201090b09090a020c03042705010509010303080a05091f0501 87
    0x44134101e280003591410f042100920780e4640790070169159995000b56207034158004201c580040e20707803030444c0e22501e09840c00e81e22084005102d0300b105000350252110103011000900d0b60340d072050200409800041c2016007075004443c42481c01e9142800258414111902c03405040c40c9585002c001b03141c00da41c002d004540050110112a036800350341c50041f01e980d0300d8440d4883e40240d842c14110100c449200e9030b40400100000100980105414441c80007107036640001e0b42c80409100c024842e2560041030740d001900032000140407980103c01c140c1040c580182003244000c0d9100444106805070404101c05100410442da88202004082c0c28031030312050401132818082051044041e100144094000c03518000d00346c0700f00190340041100712aa104400882d00c5540003035403411404001450030807001040505000060700c2c1241c2d4140d4a008407603076080900c0008000281c00000781e4041d0005143d86a284039003082c998080c40c000000380c03940b500404080a036201f0202e400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 49261973 1250 49260723 49260737
    0x16090605070f02100e041a0a08070b0a030513021c060f2904090501020316030606020c09070302090a0504020f0d0e012a0201110313050d02010b0604051003092907 71
    0xe03080b4040c031070010381d0548020241400380102030310113500000c01103410a1400c01c04c440c0840501c1c4030000c0740340c0c042e180c03549040c1d1034400390350b19050035000e0b000807030f8010498401d44920075481141d00132421119142500c5280e4005a020342d5503140b0007003110440c3c00c0c0b02080c440140714090311101c1481d800c0251a117070403a0900010102040320710a015204401031301503e0701d801c140d0345643c0c00b41c004c560340c3c03420340034010550108044060029145c02c0021401600000340e49001002c01480c589107030307440f000120082c0d401000610b0300031983d030000040f80e48450000d040030101181d07280c3d450b0066558107008651091588080036030502c082130b003400c2604100301600c01200904c0003515000c07040203074003510f040343d5a211820000400c110000c5034100242c0a101e1041c000d0300c070b6a001e400401c0303080c1c644d1001000d90040f02040200003e1900060b0300c44420090308002c103050362540c5441e080105212880e00030b044064007544448021025125480051420441 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 49263223 1250 49261973 49261987
    0x106020114040506010605180d030801061101050c0d02071e0302010203011701060b0403020f01020a0b100f080f0d050a0c020406090203040b07080412030f0603080c0f0f01060302030a0213060e16090605 88
    0x280ea1134a040c030411052040010b202a5034031441c0c1d07010032000c50007400018445190346030041c82c02009106410010310000f07415072030448180910740c000c0d01c1803411a0b007440c1002d420b00000b9032009104642c1c44c0d080c51000d901801c580f696140110740a82c000684a44c94182100302502d030300c220106450345004800d110324641002a2815030350159015114610b0260060346000c200410180800c003006041201e03032096400d2102c19500e4850710710003403ea4400c40c1d1070781e400011a440106811a00c034840750284103101500381a005440c04034850101600482d04544003500044c0c01d05800208010500982000e03580e0803026038a030910301c501c3d140c0c890124144c0b0b691003031000c064a54102000b21006600f005020b0354100e0034860307a80b02800080d6039907140604c11000036001c0c02e80c8820001030b0601c00d000c1120303000340150000d131003c3d500300329140c800b01481500080c0e075410040380b0120081c000c3d1b4031a41071980100d004c12a040b0019000750450391140d801c21008004003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 49264473 1250 49263223 49263233
    0x20f0303040605060411070606030203010b2b0203071e03060c050a080103060e1006060c0507090605010c0609080f0c030406020c06090a09020903010f05070e040501050a050d120c0507030605010602011404 89
    0x403503000e038202e080001c903a1140ca00040240074008100c4605610104c1d0001c00d0040e035501000880f84214000c00c41d0801e00024480500454045111001060300700307103515410414204100d2440202501e01d115280d0b03655090f1905030080c1003181113003908003402080568801c00d8419141c0713003040307414445032038001040e88070140030041c00c072a1030300346d0410341060400c032102c0896014a0103001594031001e00501c1402406400da52500c41d014001030703104402c4c800d66003a218103a540e0344281d80240c6560000d40b802c16000c9510550400c0000110303003103080540034401e1f05102455a030380c41d0140092800e00c080001c1481170808028082907961042e41100442d901d0000140c3c4483c0d0502c0043d005200b41070201d0f0042e42000200002c00341e0107104c6a0700340c01d0494081000d43d0f250700c10f200c07626059005003074000b0420407255000c40c040c0030b2410341e0440c0924001c945010356503585c60500038150700c201c030031545a4005004998080c0036030380100c40d8408030105145040c0c0c0752 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 49265723 1250 49264473 49264477
    0x203330c0a120608030f0a0813050613110306010f03030f030509030306010c08071205090a06081501200708060414031305011110050906010602060f0408030123031c0f020f03 76
    0x10400c2c44420604000c07511541d400c200c00404078002980d855240d05a00b07000389a02c15440200056140310025420101e0101034090309a044002062503581d60b82990461016426003a115940304201c11031031540d0401100b0b0180840400100b15940f81d442c000c2d00c2360340c0c444208018141844104000e2001c0003060701d03800b134402d20b844800184c040c02c01c002c2910461038060180442c00040f60400c54022004204104068402d8002c1d103541c0d150444480506a07034030704044030b0880302501e0700c1d0310aa0214010300e07400440c9881c0c00c80c64480581c07600c4030039485590650440400c020900181c5e05100340d0920158018518080e607030075412045030b9090181a05024400784241080380d0b0410180c2c0e800e5400107010030950411201850740c603142481244014820840002c0803d0082541c19000c2d59206a480b07080d6402d015415802480032986500e1614805480c907845660030008400d070710012007a824130034803852800a180e0800c2d604c10b901554448001e9148005c80001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 49266973 1250 49265723 49265737
    0x807021c0b0f0a1d1c0302040305030403060b06091206040b071e081f08100c0c030c060209041407030203040209090f0a03030e10020a020f0606010c08040e0a090203330c 74
    0x941e0080d07940c0d03e80184004159584a1076450b503c2000d0302070300c588000440e010800038001d071075050f071301d0329080c110160b06c41c50100422a030424042000015006d422400316690020890350900c0980c0002c1020000c2000524040c2d60001c3e043c4800c1c010740040e50340c0c00550300e11b000c4070501c09072005001101080c00c0c811041112550009050303e269400b40c10501d14a10901100c1d15070392103c096a030b1410440183e40a850b00c006143c0d050b00a2a050f04103d5050b25544049080740c0c855000a4020081480d02300c1e4603089900c03054103400084510440048e20010f13207078149401030052000e0000c06498059110b040180890b18001a920311020b915103000314020314890b0110b4101118603005040a40c00407a0844082d500403a00f400032812400490b00c05650305401190f00c0b0780c0780d400183c030f049c81c100802e00590300131800040e4080254a0046280c0180ea404a0f02d40004884075200d02540601810f08200d000d0a00c0f0060101c0c4d00c85486140c04e100d0a045200d2040700 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 49268223 1250 49266973 49266991
    0x2b02040e070c0c05040507050a0909061401120e0105240306010803190903020a17150417030406091a0709080102090a090504150c0e120d0c1118040807021c0b 69
    0x7240a0411107050511005004c1c068820310107800d280c40f01400a402240040340401e0541101041d43c5045104060456102c1c60038030010340500d01c015203108074030710281d824031034490394040d200d5a801d01421b4001e00900ea0302c01410200040c0b1001d444020342180b910a402080c0100400e90001041e5030304100840714450030642c0041c0d0988400c000c1da44002d4000f50510740001c3d007480c0381c84e41d400202c011042a00c0b0300e000050102c40e500307203040300c0040c403070700c100d807030308207d01907144080c682c0284211030000380d4401c5070b1968003080d140f001c00c201030141c0319801c101c03072039510101e010001d0154500035030030103004d54006040c8001901540c07011a0f0382d000050148940203840c0040310b10407030401c009044403014003e0403403242450080c09240e0551000300c00440005802d4485496940c45844d0740905643e01c0d040303070301419005070707000f004885004180186940414000e511078000c25507903460078814020307200c400c05081c6440c0881e240c0f6110200d036414003480e40c007000318 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 49269473 1250 49268223 49268237
    0x1a0103020f040503010e01050a05010819030c0309050402030405010b0a0b0a0c02060f0f0f070c0510021005090715020703060518030a050706020d0516081b0405060f0f2b02040e07 78
    0x480451409010320f50100764550308090414100340f806500030781c0504002c3c1000d20183e81c80c0c00995a071b41240c0d0303400d4002c001c0101140e0021a218200300f6282034807a11b04949401d0380e500015050780c0003500c080d90183d5482c0251039242c640320020310b000304030803800242058070740100a03250007440c2c0000303401850000b031060350489484044441420510103d2900c420f824807600080d60403064044921100f60080401c4038601601800e11440d0154001c00b06e040c075001c2c612009c0d14001d070010440f480743d2100410040403070a0000141111342d40141a800d28605190f0283c8a015040b1002007852208241d009400482201c511151a0420f203540d9103551414100903c02c9110348807031503281106020550301c8040c0310349500d00c0f043d0746085403516140d10016950111000d100c102e030b041000300300013600788030014141c00403d01d00194281036000040c10010f6106c008482c0d4400d200d00c070110491105214401600e0f031021a0842c185810034102d0803007540041c0040b400c0c005c03d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 49270723 1250 49269473 49269487
    0x103020d09020a0f08060108010204051e031e01020705070b0307090e04030c1b0305060703141305030708040b0c070803090d0303240f060e0108064f0b01031a010302 72
    0xa0394001242040d40503100001c6907583c2c51505903009854054080c03035010300b000000d850740c014020340341621801842c0c0701c00465248080700c204111210f0058041c007401d01c00d090080c9802440c402074001c0e010015a950303200340740c06820507245402071502e072882030080c4207074190700038104070079981155201c00c032944860030b056070880d5102c000201b041203c0c507000c0c00b1641a5190070400c980c031440854096440d1b501041d0280c400d0360000c06001861000013030030031407825071599000390041c81038038601425620341b04a294810b40200d41007500006000c04010820000c081c01400c1c584003450402103003200051000f61388240160400d500d610549906041080740014141111410403100301e98030507840b11404824450800803030b540706001603003235004186043c46600018403641013484440001215035451300c07500500c129244041c408074028090038a641c00c0504011400c1c0081c032864a0810b45009012060404d428003146180000261126010841d424280561610740f = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 49271973 1250 49270723 49270747
    0x60c080d11040603060b070f150e030706060503060105030303090a0b07030e190209010506040b0301030b04051207030206090c0d2102010b0402040326030c0a080c0d05040b0f010806090705010302 85
    0x40c0c0104004640c0c41c1c0340390a80c4103112032009208564080d1800c0c040b0650750070300300d02903000303200002e40000c4500602900003842c140082145240e00ea400280310a110307101c49203560040c1504940096a60000744064a0100610350040c10100c00440c598503003580d1507912081003040003007001c10414045001c05000b508600100307030782802220200110f908080000a8007804164002c1000c00000300b0903003080c1d01140d080e00c108130002440c40c3d20710743d181901d00300001e0041d5264050002c001000c069020001c1c00094042c4d030050480d0304007001d0160a280b69440068812140710b40c0d082c2c001401d504204900c003894480b00d0003003028100c400d0b8050070b00c0c44009540140300050200400080c200b00111103000d641c1100c0b00c0388140c0c500d5581510090703c40c00c410350024889a00044e1140485582c480b0340740340024140112400000140c4000352412252010000100042c10001d8000e02e4010a4448000c0c002070402c0340700e00c0d4840249c1d000b428105034000580c020445 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 49273223 1250 49271973 49271977
    0x5040303092a0504050717060d0c030510060b03040201090e09100c030f0506060a020319050c07060305070215040b01060507060204031403190e0f090a0e0609030a03060e010f060c08 79
    0x640c0141d03040d84210090050140700b40c28a06000040c00b5580c50086a2401d240c0305080c403420a584400c1c2e10101031605a0b0305804000301030700e51012103062440f00044990354008004c510803001000b480d003820050030b082d950f1030b401c1140000000d008020144c0e9020040e50200e07200326400c1d04080c0c80d100c0036103017407107440050b0b105510b06028102c1c0d20140c0c544d0114141150b580c60420240c0c951300c0c100110fa00c44d407030704900142e1083c08000119550500c4050b00310216040c03003440c0c031054940c1a03007496602d5000c034001c25a1001004030564042c010003c2440c6100030111543c98035644075840e005040c06414204038010448408020b090360454014541002003c14500180702c2e2041d5254441020000641d50311050301f01c00c580201c040c23088681c1c004156145c40e081c10810301641e4180240301c0b030340c01078540f0240582410244102400744501c0350107180e8a004452b4040c0030f03150640d2200e011408407000401000d00c4d03114566066540c1c0c0e281c14522a0321904024540e8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 49274473 1250 49273223 49273241
    0x61603020f06040503190e090a020f16051f021204060e010207020a0f0303020c010c05371a0c0f030a050a060e16020d030b060304110301060f060504051e060a0305040303 74
    0x50b1144000344824000000090a0300406001002c005150042c1084452042e5142c1c1d1581082d001d10104038480d0301a009848410404d1441c50f09069017202e52800b9100321200a980702d8010004180c1000d040d542d00c1920407210317400c107500d401000c00505025080c0144058180380e50307500b540b44040402e404032581590000c16072494140c40b0120066484075500c001c50152141002c030f40941e5004603411040740d0f4000b03000e054000d4140c05c00002e600c0f1010301407100b403400d000d0b0b18480c0c24402581162294000c66040d400c84403564009c00710000007502e400700085e404d001c50900d100492080fa0f0b4800303040c0d403001ca01030f00c43c0202c5801070021030300400c0312442500f0401010742c040308494000340000d64202d405c901880142501210b003130744226a0800800c05c0014080740440d01c044500303002c0900000342c8035643c2d803c43d01d2003030700a4205c2d9002070b100203020001c600d003554035115120159800014600d00b10000207000d4814480b001052680b42c60020b81818040e80c00705904c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 49275723 1250 49274473 49274503
    0x50a050d0b01051b06370b01050910050a0806120a061503060509060f060f09010501260c07020109080f07031b050603010e040201020f010903050412081312020102060705070206160302 80
    0x456030403030440745d210039007100c04d00301070001c840c890180405042000c044c075181006000680043d141c00620103406c540025a0500c1070411104101e030f00d501500e8441c4c44490341c1c0309501e880c5418070042c5000341c0904414895050074900201294000c02e0740f505103a0700c19000200c05400303116400042c2503075400079044518103400c10020080100e0414865200788401010560754202003103611480000c126404c01c0d100030040c80554000c0c600310001e00028148102e41050304a4826600c100481f020443c4a00c042821011035030000d02e444040e1078104040c3c0454154841c68582c0c0300c0f81448040d00446e00c03004008a0a034503214004007501020300155a40c2d1307142c401c0d0406006041e18124018424488580b0210340e040c0315581003135034140e94184c82c5c41d15050420800381c98200702038030401410001a840c10320b402a004004000b402e00c3e0f841d45074402c1c00017900304180104900203200381008030f0750059a0700c20844480e446103500c000754003250f42c2000c924048030f079607030074030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 49276973 1250 49275723 49275757
    0x816020f33040f0201030b03010e161d0f0a050402010c0507030506070801080a02010f08062b021008010612150803030f040203070605040b09060a14070812010501050a050d0b0105 78
    0x40041120000079032a1020007a103004030a101056048503a60100c41c00780002d401c000d10b003001984682c0014112a50060011500e0814858075600f0701249600f03100e40209440c0d4200a400118140a0300903a0941442900c44c42e040c044042c0c00400141880703101552800050111ba0050a07030b045003e0304001110041a100e20388a6600c2c0c0e8140c03160f1001c5070800c00009981c00f40010a40040303603040c2e503203020144c3c50388020f56038a00060249540450b980c0412150b0341c41030101e107014101d03601d0018030300680c00e00511440450f08440d00013000044c03801848029000701c0d24240c210250b4000140e03281650466210b8000b450700102100c0c0030000500c40307441e19100b500340c00366000310b081c4c4044643d51501a41c491040b8803847c122144144840b41c01c515100000d410314041d9402c0641d0450b140f070120010652012300110740421010a04809c12101c0503001409490282011842d00c5020040a40b1034003c40344200002910360700c407404664440d4055408034040d94200701 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 49278223 1250 49276973 49276993
    0x20a0504090f0c060914120a0201080a0605040c03021b030a08160302130603020304060b0901060e060708070503071401050105150d1d100606080603070506030c070c05150405040e07060816020f 84
    0x1400d150300c0c1d2040011800703141b6070324509450800000f00100c20044001c1060b40c04075030041d030711808000e01945203183e546d503000600d0b8072940108403a100f0031341d8005030b40b0000313600040d01c400b030310015911080c0e10038081041096040b030103144d048202c401050f420a48811001c4029200754544c243c020b11015170002145070b0150081c41c0030b544203110900c5280300200502080120034820b94000407a60000c01c035050901c3d0004040076070203200350301d142c0145e580728145140d01c004812144007807107030041c50b0141e1080c468140500300c1114600b800521000e22a040d6009044086031580e03500c20804010036102200c0c8440440080151540032a0100f0624000c00051041902140d8100005401c0e8940410888203071400100202c2c00e5488402d408011900066000c5400c009542400308055480318007000841ea8107072059640c9505010071b1000f515203485240382d583d40401401c0c00f4958100d03120903030000c0200590050102e050104a02d040480c05119580f405980c40300c1c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 49279473 1250 49278223 49278227
    0x150815030d09030209070c080f070804050a0305070e1b040605090102030c0f0610170a03032d020702040c0806090c03091603050102180111030412060b180603060106020109020a0504090f0c06 83
    0x200103c0380211800c00751592007605c2507504d6610188021b0038004204862002c510140b0041c11800d40035406141c205600c0d0700106146c4011600182d802e64000d002c00c001d1003414816040d48035000e10103059400c0018014110385000d14020042440004901030b11185d1080007510505480c0400f140c0d000c20036185125103842041d603880d03111000000000c03680c0c0c061090581d4803c1040e1004204140803914100c2c010003402449140d0b00300a01e91040031145d8030041080500c507240d40050b035815083c8104030440310340203040c0c0c00341700c2c0040030441d1607a602051a40d0040080044c540c1c1d0b580d0b08040c00d4103226180b00e000788200c00e020b0012051150540c007034000c940031020321245444407600103607804562240c820700a94020402481280301c601903403041d5a00c510000b103010000400051154480e005510010200e8601000b4261030204441c0740105841e0001304400c85558000c2014110715000d00c600079500c8908040400c90880e40d550030554101455160f40340c0c5a80d40 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 49280579 1106 49279473 49279487
    0xc0201081f0e0714130f06090e0411060c03070609051615031505060703110706030b0d1b09110705060c16060c110304080c010315150815030d 62
    0xc014920400580981744101c069808030010324200300003298441940d0b4007900400410400c1046800c4400d406036801c41d0308841124503042110001c10311600c01d4a800300c8007803000260650601c40030303902c0a44550310590a903042c400d980c1d40d4800440c1c002d03000c0d442c1c1d008204954148014082e50040c0020140c40c0d401071805542c0300001100354002c0001134020800600160709070050900041c0040c00b0b2a00b42003041c07015460214000188030080201a40039442d00303c1e415081e58030160004244150b024007804686181d0812242c101d140b088a1500c142e0000c6841c0608001c252400e01c00305400c0d180780840380e5111040a4030040c03c01106000d0380e40401c100b000402d10090000c3c0c404e0400501d41c03110240001030459220841c000c08641c2061424000714820704051051004549004d140c075455206443c0701e02ca49031401e95078140301d4200c07003400035900214 = true := by decide +kernel

theorem cover : BRFrame.Cov 49100723 49280579 := by
  have h0 := BRFrame.cov_init 49100723
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49100723 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 49100723 ≤ n) (h2 : n < 49280579) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
