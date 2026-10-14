-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0251
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:44:26.414682+00:00
-- url     : https://prove2.me/submissions/f681ce6a-bce4-4ba7-bc31-fdfafd7bfa03

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 44964033 ≤ n < 45143889 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 44965283 1250 44964033 44964041
    0x5150a080f07020f0d0203030a050606070314070501060906092003100e090a061509050603030f0405130902090a0603140f0d0f0306030803070306080f0a02090a0f0f02030a090b150904020d06 83
    0x1c02d025174001c041c55003c145500001451145542c0d100c240540c1e182e0300148100c5100d03600e40900051220340d02d4026000c0190b0040840c03500c65030001a9960380c07115044c0440701139400c103c1203c0d40f1031a840c100d6510440e00c0c00c0310070502038000342c69810018440b12a1202034407955282c5042c41c030008500c1d004c00d01c000c03a102c2d90050001e001b5801488010305401d022401071013052407500c004900c00382400000c1e6060301c80e034001500e1a10341400c0c10081303c0c042c1c0c00f0038040c4d01503e40c001000180c076104140d0307002d02d01446000c58118111b180240c1e0252101911101d95801241840d1300d4190020744a88030413880d05004501d210f50a8046001d00304a800142501d10008180111180d040d40703e0012240d00320161106100c00004072915400c0403000030358006650b01c081034080c0b200f540605035600804600003207152243d082070090b80c20072144500303880d50758030284041c0480307541c210b44c1c0818507080303403040302d0000000503044160203480640600020111041045030a1780 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 44966533 1250 44965283 44965303
    0x9030204110408070e04050a0b09011806020406090b030609010b03070c050106060905120f1209061209071403190308070c0b040b06010f020304050d080a02240105150a080f0702 77
    0x510052660215458895105100f030a00e2440345a00c00529074005406a9010395485800390100560b5a10740259100014016000555803181501c201e00c0c0002c10040c9868801d00c40940c0783c600d420300150440c50654804021440e04100b00401c5981e82000385056035a5003030740c2034481d06d41d28000c4aa088191341e0040156291040c041002c80c2c11411030401c480088548509a40e0b101543c503498616032824200c0c1940040c41003100d0003440006004940d5019201c2030810300e80d078100341c8032402c054a00c044250000300c1d041c131200848005000300d083d015801442122400e2040380f120381e000c00f901a08000c044030110b0034841c4905401c07a889a0800700003c094280740c18580103801080e503107140420300300804a00100d0012060702c3c01c90f000146820504030a5888003e503c0d48a4280182180501102c01500782c0c01e00450300500742021010014a604280c1400b02c003401d05001340d0240748003840301c10f0f80142c0c01041c2c590701841ca406c80e0020360b190543c059191102e600 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 44967783 1250 44966533 44966539
    0x80f0717070b06010e0112050603030d060303080a0c1103040303050703090b03010b03071805013606180503030405090109020d110c0d02010b040506010e01050705152403011a040c090302 81
    0xc03441240c0c0e142034401804100780600724100c42d54481c0d00c01554011030324040b81d8045880f0691110009507103030311841d800140601901d28014180e001c8004846803904120082800c4c0780603c0319a030103610540b00b6031080c45c1001d1110006100c001d9640c0d000c0c070310009041010015004080601c0341d030040001704030020b5801d449507103480107036041d50401c503a0000000c3c01d050b5140410420801803000720307141a10b8094140580d020300d141042040485503c0f40484201c0100040001e524220010032640ea601d900008403c1d66260030b001c01c540c06544241d1042c04140001c6ea60390905a0440d0b041200059590580303013041400380c00303040700301d4042c0407020544002954005c1035801c138507461640200014004601040202c03001951480c0c00192100507020f0701e94084d600130b2070030701d0080c0e007282e009603109040000b440d5012907005400081c884500000c03c1403404420352060b908500038003420059005040351034403488101481107440789840c0020341d0044030b886015640103 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 44969033 1250 44967783 44967803
    0xf080d020f0a03140f0f0109180503040f030309080303010308040909050a150f0b030a15020f1608070b090f2e0f0204050a080f0c27040c0303020706090b07080f07 71
    0x84072002d030003841e541c214804c0c1c1507809000100103003a82e41c01070740703e41090b041450ba07076401c2c400098018004031510101c0c20b0015401400887c00800240005201174140100c0d603c0c114907005100c2d40c40e0790300050b540d9000340010310020b034129044d02c003a00d01c540e4000a03148201d08050b80303010100003015101c04040004a41c062480c0d0300000c03041008410144035002c5001c06040c0d40d2072071154050070900e000500307c004249036030010180d03040304000903400e0201c0011442000380000504440340440010303414200509240310036400344070200607100c50f601407041591600d8507603011030a500c4408000c1c01c41a03080d8080e60845042c00b0f81e0410403c94150107140003540b15005581c412301e000500001c802000040300301c2c842c0440390150100280700424017211000a515042003803070f2a075955041c0b05d50780d840140c412401020060295440c505000e030614000341c00810411190503410b200080a030400c40c0c0d10745134040d0030349a5802c03c030f5243c03182c18003920200615030118 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 44970283 1250 44969033 44969047
    0x5070b10060305070207030c03080708120708040501050c0a020a23010c0201020408190c03081c020307030b0a06030b03150411030a0c080c06072307080d0c03080906040f080d020f 78
    0xd600c8450050300c40907203041042c0d07114904240e070303202ca40e88030003424440b070980705000143c00400501ba0f140d225014040c2000c448000d031003200f04080b1841400111080200700c01e02c0400d021341504003c108100c10f03e0030f03c0c6580025181c0d01c401e10007616004e5002840540c88403000c61100404e0000402000703109100e00c0028080e40c054401ca81143c0b00314500b01c10b42103541c1d9a090072782980900f40c840d04038075564030031000d60800b0300c200381c42c8850382038511082c642ca400110320400d401d03a00011443c00450130001d504000f03070400c40406241005101854900181c0101c81081800a9050b1551680341008900c46981c0d01ca80c0c0502a2141e880100000b86020708140e41001c002c0c1c031405454441413102c0c60080207006400c01c000103610b0707442c591030302c00000304000040090752109034a0b0101a8600403003442c0040c000b4208081d01018940d001c84241d400c11240c101421141c18a81ca4100781e030010100007801c5203400040c60481701e41903a04554045040c1010691a044 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 44971533 1250 44970283 44970301
    0xa0503040807060210060f060f050405031203010e0f010e01060507050f0d091503050907050105070f0b15030d0c05120a090f030803010311030a0c090c030209060f09180f0406050705070b 81
    0x2140e840303414094803a42000d4017180c2118015401a10721665006050034030b0b118003111a0f000c401030340004c0c00740800001c40d55440512241c0300301d01c20241005e03500e504d06222002d4a0f00300600b0000482410780c014080a104180064112012450180d031904088d0603d00d0511102c506902d110303100d0b40c2e2040356030380c1e0040100411a1041c020001d0641100901902a10401c03a0380c100a03420404003442158080d4000d07008150040c5000d400160075a914188071070f00c10350340f040359218081e15100b40c0e8907081008050300d00f818a0014003c0c0043c0c0c0d00c0c00e80c2d401d09025200301041010455000040c4180c00e020018220500b111702450b90301d06209106900c20b00094071301e000c01904400223410300055900c0141e51042419600c0361070040a0f100500829804904054080101c0c0c0704958440001e01162601e100741a80c1d1461040100142410300035074411071550280304100001c90650401948140c00510102e055913070075000b21190302c201040207007541c0c4507a0034040154 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 44972783 1250 44971533 44971543
    0x3030304140607110c090403120c020c0a15020c12010219050a090f030f060e0120040504060f0605031308040306051302180c041e0f080a0c0501140d0e0a05030408 71
    0x9054010340b00c036a168024120b0341d42801280781c103619440380805003e141020078903158450f0181c0380c040d0700e014482c441c50040e80c80f115034040050f030100aa031402843c0422801c8010802c041c00c0204a00c201280a5140c04947e00040d12503440c030101c48205d08820740480d604040300035180c0805080008000e0b24a810249500700061020540807640c1c0c1e11248000080d2034010080c4038200e0060741c1c41c0006803002c200a400d0035500d80603000350140c0504910307030140c0904500b545d152030801c01403104440d49944040c44080c1403074400c00040d0f8221048a030040115201280080d02504107440d461055034001091b01c1d00e404100418079010301022190f80d8801c8a440001580390404081ea81c0d0080c0d622000040003004100101c06051402c510a955203007041c01c0031640d200745070300400c00260700030021500305043c510201315200301c03580702904090074989001c2d07140c0c100e4044140100c03044030707103000d40c0c6100c03038161500300b00304010085030b104044a6545407070f417045a8683c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 44974033 1250 44972783 44972813
    0x40909030f0e0f06030a0207110301061d0a050c0a0f03020f040603020304120c050316030c020910151d121e010c020c04050618070918051501020c030606011d03030304 73
    0x1030240c0200c000b1460502c03080783c44030b007004040ca030950300c0b04d85541000707520a0104541e0110300e9034203c0d680ea1002c1c002c50b0003c00026950b2407240b9000c0306810f2640200404010481c1c0c43d0204100b0540540d500380c1d00d9981c0545851210059035200607070003445025003900030204080740c002a82c580c1500118070030740c4281ea00c41d480308680301c0142d4039034080500c0149103030000c1c050f00c0300b0100441c0d0004c110f50b0007450b215803991100d4010444403402918000041e06051109209660541030b262044410918240c0900e0720b07036a13880c00058a002c084c003442441d1914050078815020010854180d03a0700050314860300c0341e07402c8213000b40100c03401d00700507018a0b05048914500352040b180f040b6400351100041d880302661821022800810001c1032010002000c5051740501d16a035004880c1c4080c002014103205050580f014205a182411580840011645c980b004a0005d400440070f08040900701400d00b4590040100d034051150144400310810082c0b0481c4d420010034 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 44975283 1250 44974033 44974037
    0x60203010909111c140312090307020109050117060607030909020d090606050609060f0703020a0b04050c010305010b04051f090503010920040902150f070606090b010f0f02100e03040909030f 83
    0x70201c2c12000c0c002040000d00c4e02c0121501180c141da404150301c0c0110350000a80710f4180e916259017160818400711041d10310760156030010070b04404658008030424081e143c02d081544280c100444041e00740f80c030061030f5a0007045e0100300042007600408001000d403801d002d066486c0d0b12080800801840001070544a19007000f10014450400000312903894801411152402d0030018900da040d502c010360071011445596490004030f0b05244505000c1e500c100042e0100c0c00d03c1304001030a403071040c0c2040c85045420042000903036248641c3e2500010f48808200859001b24001d54424140b40c0c8456019400e10903031400300041701642d452140c03541d00d0158150441a82803004585081c00003c9d04420744800842c2d640c00140042d00c940718481c58040d140280c5a5104010389071184c1c4510a03980d1030305c24a10240d03070401c114240c0043c192804110118540f04029075822012000500440e0b94188600d08180c09104130f4010b08185031080c414015149801880303144d9010201d40 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 44976533 1250 44975283 44975303
    0x130201090905090a0206160803130b0702030315040515090702070e010f38040e040201020c04290a0503030c1507031a060306010c050a03020105090c030a230a060203010909 75
    0x951807020b486090700950806000300315508066081c0819036100986002100c1546446000000c81c52070081d0b10980d801c1161460719905840c08840c0108050403180642d0070901c00c02401038910201c03c3c06138201100c0201d001e403641007401c02881c01c0d2200c01500003810804000a0b207800040042c00c8881c407100000f250303030b07032030b44e2801c0f08403c1400303280507500c006500c0102c641c60035011214821060307500c0400d0500000c900250030350140c2e11045100d00711900b044155a014001c006c08520b055406115042403883d01d511041e4001d180380540c149031010045241e1110344005000e4040903003220742d034010303a401d9140d403450900904c0c40005034180c00242070360311a0181d0510b1703051030065a449150510200480f6130001000541044552459440414000c20000c00e4090007900002010f041c50500c441c01c103074140b1a100d01036070144507808002840070103401c92500358101500c44040a141800e41041c40790303200034042c180040008110f0031844c0d44065009840fa20b0049 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 44977783 1250 44976533 44976539
    0xd020c031908030a050c0f070c0e0903030708040b1008030c0a0c06050c121b010f050a0c09031a0a09020603070908060609010e07030b03030903030403030e0a0b16060e010b0913020109 80
    0x84159440c0010040140b4000e01c08911401e2054101d42d4000d07800701000d0781030020120030a41190400031042e184c04902040800c040b01d0840603058003c038000c00035501d5072402410240954401400082245200c0c4000401004801c60208040c100036819603544001101e5250340e90302c03030200191050511369100040c82401001100c0f006003001c0301401300302400e50f980051940140f03603154103110f4880b40c0841100000e128a1600c941c045100054609000e06034400321078002c0544014050854010700c04038010400ca0030941d80d02c80100e5019139070b1005804040c2c001e40c42e00035040100070050080c140d0704106004186c034500070481d4069a01ca00c200031103500d01384140607156000c00013040800d8441c3e04580403101025045034641001c60000c01e2865005138029000903580409941c0c091a000903585d00820b05a40e81c64182034080c4070b0701d4103002590070300800c4d1030b69640100c43c02c04001e4100c882e40c030303000400901c0c503807400e05007120031030f010090704900190701002c001c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 44979033 1250 44977783 44977813
    0x8010f050f070c0f12020109050705010306051e130207080c0c040908030406090201091503020d24050112060510030615080702061314030408030903070e01060219020f030d020c03 78
    0x14501c101c1004191503415140d0300c40075581d280148a0544c1c0200441c10160b02040820482d205010b080360b000181ca0045c038200b807410460107030032450405080680030041950741c200030b0007004110031204000c500401000030800111207880d440818004035400003170100442c06445c001d84594241c2d44550350320b60801044520501b00141414070910115000c110142d114107812071060420086080e229280c03a0400340c0040c0c030b142e001a80008548100d014580140001c4a61081c6540d00011120202d00c2c1404214060f040c1089a054110000300c0d01d2500100c00814010f018070041d80340052000b0050880d80c01070f15415005900074505071403180850510035a07281d4051308103510b6092400c003400e0074070242510031916241c00c0c0b0810302803d000a0000f840720000455503428508141424101d40380d100d074445070a2030004200550b0082138681c4140c4c0002540007641d0b540340f0010311210072040e410341e09485440a070480644e00000d1221039494118211041c2030410034107 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 44980283 1250 44979033 44979041
    0xf100b18090736030f0203031b06010f1703030c2d071703040c030b0702030f030108060f0f16080a020c0a03020d18120206030a0207050d020d0f08090606010f05160303020408010f 78
    0x1422101c3c80c180003000030035034600800b400d60303100805903460240e010000c601c2c03074030541c00f151a407500064010894610500810700003003031554802011510700c41400d0341c481c040100040049800000d00700e8990300c180c21104c01095007182212401c010311108204190002d681c1203030291701b00c000c110a0040c0030b00c2500d100d558005603501030b8908540c0c6151007040040c01000540c071040c400180c3c020a00e0340510301078a807040c010211803412001c1c0c3d003d01c00007d0000044001010706000c1030145500c44804240f1440c10074820740c1d11618080002841000e0241200d8015500313080c4c00c065021031600588065a503c0d20002c010100c420801d00c443d51068603103140c8101c07900070050802070051035018241e200c00504014542e02c8007401c12800844c014010307000702c0700c444181900041c0042400072185445e803c3c0f40b0f811814241d660402401203818400340c1c869002d10130303104208660507900c45a101c03904c03030311052401a020b9041780c021503000c0c0d401c181e255520a459889 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 44981533 1250 44980283 44980367
    0x30605030a02040b0105090a14032b08040f060e030a02010506061c09060603020604030507180b0a050f0409080a050a02010e0c030303010315090203060f0703050f100b180907 76
    0x780110030440e5003040020540038942605021003840b0000280e5915130860b001070001e80010156080c00c81c2c10941416042154844e03002903a0000f0503090b4600d000b8004102030b1400d240265407141c0c1068009281c54100040156041c1000031800032004005402c40c941190002e010607141c45040121a021b400703551190a2000c1c00d03062a900010707044060118000c10b00006c110b80c03690080361a81d402a00117589917448503101700501d04c440c030080c1e0011624900c0c00c101d4003204000003800141c441c85428803038010074600c40c0b180d980d1540000d1100d81c2c428000782d50755490b03000c05806034001c41c0c20040035518140324a0f00e0818045401c10312550010042d41c030310fa0071503590211200244600303140095680c60200010388003001041c0c054400e400b0725481a10385410002c0070f41d580200a158400e0380b032014410310002d0807841009503003540c1c40a507103801c0e000880404001500580d5648142c5070070a01000e41c0c1c0200300c01d00a82c0840324502400d000d4840200d111040c010 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 44982783 1250 44981533 44981539
    0x30a0309080139091505040e0a02070b040f08090d03030b0a08010911091008100212130f0305090d020306010b030105150c060a020d0b040f0501050301050a0e03160204110307080702010c030605 84
    0x800741101c1c2c010300c801d06207a061204d05007a9034407515000410f00760458a0209408a10002010f009182c0c585a001364840e09081c011741c58071103943c0d1821100c10003d0300081080762480c990104000070f1238103907841600090f00c2111910f259080c0280504040650700b4001d0850010220380071340e041c0501750b8401d0f040b14244100b03401c98014001c1c50b200042400404400382c00000caa20782040c081d55003008420540982c54954000d0030200345203000c3e0514008041362419100055000c0400b0000c290709402c10039296600807001c034485c0305003004000e44c1805850008111580f102010314161042030b80c0c007190b41c080607200e40c401803040c80b2a45085074401c50005079401055002015501c10502c804134440351140302080540f0b5102e40c1e041041e580704c800500c120f050901c1260f0307008401c0d64045c014040d1076800903031a413090b140c1002180b07071a03801d444103540b19600100e80c0c0441c1d107041c880c9c3d80e181001000f00800d13020b8440c60019401c0070300b05800e8500c80e0044001343c400013 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 44984033 1250 44982783 44982851
    0x30a150503192a0801020a020c0a1d0721050f07022a06130e040201230a080a0b03031c06060c0210080a0b12010b1f090e090c030a03090801 61
    0x261151081c110104520f181d2000c81c00246054500781603509000500303480e00003507152000705a0280c20440852000c40c01408030160400511080e4580024000310071806819107488480f01202c8010000034052121022008500700035005580402c0c4201940e00440050382c1f180031040b038652919010030240c11040c0100b100361004070456480040d03400410071840c245480303205114103803050307111800c0c81c1030340c40401081d540c001c4607081c119030011a4052801c903500054400c42e0040c00501800c003c2d0050004503460495401003090500003811030f41c8400a034181c141c1040c04181c1d4103415582804000a4141c1c003801c0c0c4600320a80c000c0110000507250700089800c07c000410341a06c1ca034480d8510320a50b1075403401c01c5200314040001040d42111681401019a51501e2030701c44110b40a101180d260b51002d81c000582e800500d01c0d0940d6100ca20a051402d040b14444941c1402414892000c05412403601011030b82d40b10001d000700074008507042461900b440b1269210591 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 44985283 1250 44984033 44984083
    0xe2a030c061b0106090903020d0314010b1b060a200901080705070809040e030a02070b0301151b06150e07050a08061201060b04080318030a0f03030902040204030602030a150503 77
    0x100c0c000d00100005041c0c8902c01c036070100d4142d82514801d07405940003a44ea60405014940d0512000396001664102070181c070800343e45005804e403051103803541460002ca0380c0a14051081c42c1d9103444600101200d0f914100340249000500c0305201c043d00c2107000355550b40d009252103081d40c04c00d81c01611018103507544c00100351110b501150080f111194104607401599449100e89a02a40307603400564031036503640e4000e0710702141500011407540080c80100402000c0040200c030011152070088103850b1542c81c185024201400d00400080c00d011001441d502c0542c070480845903091101c0e0a02e4448e498251000c0c443d00720060001040d08001400c141490100c3c1c01050300300384000030b442e40c1ea403c10b004040d089030b002003a20380c00028801c10241c100c0044003809a038210050100c40c103055641c1c0240c0022002c0007400c0c16250011402035503102d505490007075801000a42d5a4501504030781c0003402d2898240540c06014100410b2500740050501d202e00d040c1c9802015880f1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 44986533 1250 44985283 44985289
    0x1050d20011101020d050105010e0301140c0c03040f0b07030e01030b0105030f040507050604062c03032d031302010801060311070b04020a030212030d1b05030103060506040603060e2a030c 82
    0x452030454103001c00c40c80800c80c00c15003407000b40600c4c0c640715400155941440001410851440800740c0b09a051820002d41040d11203410398010201034881551084210300140c00c1d8015a400b120014541c034030300080c100d100348000c0c00001c1c0b0075541d8603410341240b00154221840c034025140001c1c424000030328002d084240305a0414000c60807212001c0d03482000485030383c0960000000155034034541084072280c41d4030f40c004400c0da1403081d0800d6500c1000700382d0364040c08210321a02050303212078407000b0f016001c500c0600c4880746400741d6640361509200e10340c49258002280001c02c0d24000107642807007407080009441e8a9501c0b00d02e404907680300c074094180702400a03039010743d14034000401a52240c4801c98500e0369a4080e40d142e0b1042c140c2401207801d90345032807441d80031900880100980c0f0500b26030660b90310a00026540e01c9149c04030f8000e04840c0c00041c1510729180c0304080c02d41000594450305100078950b00c50b0b070703003403c9000805004020358503034140d803000703030000341c145 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 44987783 1250 44986533 44986583
    0x2040320010201060512070315020c2104030204062c010f060c0201020312011e060c0b0406020c0c031203010f0503010204080706051e070602070b060d022b0501020408060601030501050d 81
    0x40d00510012800071384820005103980714540050000381e00c80c800030001c110415004d05444012400114101001c2580c80d42e180e045680c0b90b02001c2d0080600d0803030702200b807400d0340e02464028104003c410303190580e84aa480c94044040118040305110103240e00400c28824140c41c1c02c00d0507000002c0ca0a1002c0d10040203040d0308a056000511028502502512083d4000c00b507151000c2d810f440d04140e8a417100100350044010000e901803860302254498002a400603844280140d5032018050400d013804c0001d4035032541402422401d50750300c00c00380051410b8500c8018812299660b500400d8200d204074441c40c09142c00c405810088240200044c042156417600500340703809814040d250b075607108103011982985d01060310024040d200034500d03803240c010f4401c080f00b8200c980018281c0110300c007441010296041400c03c0108444154007a0740346d01c0f4000399141c5441c0c000485c0c4510003100e80d14002843e000000805241c001c0402200c135802c411070018114111044030350203 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 44989033 1250 44987783 44987843
    0x43020102120a1d0604030903020f0a0512010c030506030f1009060b030604050304140103060302060d0e072303010c230906040302060c1506220207110405010e0f060301020403 76
    0x5554240507528000c2040800c541c840c42d618140015280081e29203a0405080d00494688641c0074034100400607070442c43d100156501120840300d82900c00d000aa81603110360419a00001041803020743c045054010314000002a2828002a9101024036a03215024048000a039002420800c8400760301d5008968080c00341070042240214a80403030f24003901960300301e50507400021b041011800880706000301c03d800740707030511403185035030001815402031903c100260781d584e0710001c0c0007207002c1203078800800d006070503004400790301c03941604c0b4032801d040b29600035420100e214031f050f03100c0c80b054641c283c10001e555845682d10b901152850b04101c1465411100401012004d6541c4e0400b0341000d00100c401440001d115a841022844001d08090700a007030700c01305886204140c800300c8920424041005884d84031500305082c0082c034403070409400c645068000300e04800403150301d03813080c10258152010b540712102894204c0c400e52001a01c411010800302c50701c105220303401101 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 44990283 1250 44989033 44989037
    0x405040812070503040605010b090a060e010909110417010204060f0c11090c040602010e0c01090504091a0103050102090102060903090a030b090a1a071101090506010e1008060403020643 81
    0x18460490041840d100e07069950001080e0044204001c01801c2d01686024006504019040c290410040340d07086609004400900100540520190f4461940035004040310b02090101c01e0341c101c600c0009038000d004551000814110284030400c050086a080303903010350740c00201a4044104850024071010112005030b020009442a650345040d4a80948510013800d5030303c40c03814001074211001c02014203103d0308004a1200d40e6a0000e290302c3c2181e80a5a0110300e040040ca01110f8094044075445440c268000010003481815405841c02c0725080e0212409610313510102940c0340940381d0703a1a481204001c05200040030740d50410b0f005414001110040350700ea59880c24040407001d841450f082c0345404200000340c2c04180200c00c0e241349002000080c0080c3c4a07070f91920303014041d040d4805004000b04100c0d1600e825000010403030302c03094414a040c41d1074025103a0700c058032038410b16070025000c002030743c051102d008291042c442a00c4002d211400044003200301c44900d100c2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 44991533 1250 44990283 44990287
    0x20181e060c0709020d2307020c010f031d0703030306120809040b040209040903030b03010c090602060c09031c0809100509030307030e030c011812020105090709020f0d0603080306120303090a0204050408 88
    0x584401d1500150071510b041150100c1d02d070140001c0341d040c040081079101d12103841b25050015140e004a0700814a09c82031904010f01e20b04524207401410350300040565410182c0704070720700b01c0004503010013500e01c00e50b8184506e80e0f40d040343e06c519400d508400f81504208220580c07603890142c1c0b010079030f001d001d0000b600b00403000c4009021204090019804a6186c0c462800e142c5404e109220f8103080030300700034080340e0800000a6a40c00c00601c0e14400c050000f0f0300d828650b408201e01c0e900d0128103040146007070004000204000300907110641244543e01e0283ea05540c070f402200d100c1e00d82c110040d4103540d285c4c88120040e03c09c8000a41d6503000420031101864028024524600020541102d82386101c1c84c001d10940000e45018045900d08014000301e81d9000c81c00300202e5441c4100580c50740c2d92415800314904c900d00c510f42010b480c0020000410a07035801440c0b00341c404840102103103001d9410b0a441748021158045240c0250b071403100189050f902c9180c00070b005602c128 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 44992783 1250 44991533 44991539
    0xb130207021c031206060f050703030b0f0303040303090911030618040f0b010b07050601090203060603011e080601140102010e1209010f09090c022503050d0503070320181e060c07 78
    0xa20b80560140d0907000250301038001c00c0c503481a40030f080300608440c40d1036442c80b42a400c0041242c050288001d00300364a07800c84100390b550300409410084401010f40c1e685603501c2c0380c05400c0b0305040c4141104542029501d0006860390301c19244a0070024020702d84441401e03002c1c403040b17200103000b140d040707a00e581c0c43c8000c039441118440c081c01d0150078540d6602c0e0281011450901d05901c90341c015801001042415284c10040d00c0c11200c40040002118011030040a00a2000d0300321000600c140000042c0349040c0710641c9003290390070b800800800001046854448034014007034504145c04019562041d442440940480310552a0000e0082e8540003001c054400e80d066450040e400070031140c800352000040d485074220944c80000f01e0602d59070741c464448d600c00c140d1405004011000486150082c0c01c032104d0724032901380080700c4210710010801c05030800800c0c0c2c5590015040c041089090015503e8038440c00030150b1840a1000400c02a05901c501303199203e9008060b400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 44994033 1250 44992783 44992819
    0x60c03050c0d0504060201060b090a090b03030d0c0305010504060506030403090312030216140d08040c03020d030e041404110a0e01050d1b0909110f0603150a080d050c100b13020702 79
    0x311010440340d450f43d42c0c451a12000a0a40303030b050300041c02483c000c000018066840d218260704480c0c07014001b080040f00f5100090943c0940103800a0090424084440d0241c1c9070b4082d80c140c41c800c40d0100201078845003885200e00007111b0007008140e060300c050002c2484100d0800886c0714901d009803070b0a03c88200404240c991240840c0c401000c00350207140f80106100300050305000d0300d404905460540c40340e9a90440510010703003d07005100c404014144100c485d162100300c054014010780c0c0303054600701900d0204640683d10408070f012103001070714000e0420422100c079a07000140690801d400c101e06002120f008031411507035140c911039612007803000707407005101d201c03030001c2ea2543d03d04080c595241041c144a01c244107143e00303200d05903509400e0b20380020b680e00d410001d826142000c510b080c0140d8001c00c0316071040f03003944030895500c00d00903e85c00b807a280c02c1e2020960344060000603125580130256000001840d0503648a107507034040c2c410320380010015100755008100c9 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 44995283 1250 44994033 44994043
    0xb0a15030605040b130201020318010903170c1005090309120c150d06050109120f1703010f0504150f030f052505100f0f030207020604030203060a090201020f0604020307060c03050c 79
    0x701c0d41c194681c0c0410003441441003003145e000080c80703045c401c20307011540002e40303902c0b5504168440080c54016016240d11640d160806154800704080b40003400d0380b1301d2611900841c00c409024800c10420024140807070246038007984020b0021814003a001c410030441290789900c401003440f07008512885544d41c50071842c030840c5034000b4596130f01440024001907520ba50040360501000c036008111300103102903000071168000d50840054003051802031100307000040c100d400c100000c030000ca441c84603403580c841100c8049030100160f9141c1620940303200218402c031a01c14442401c1040402c06000a00c060300740b0840940b1b041074401107a1126038402542c880c9090450303104140850305006075190800419030620020140c0d03420b00c010030b01c410010680301015000b2511004644886c03040e40c001c2c41c0c1c01400e079462441c181c0382d8a0000c03c1d00c444180d0040c8688007144040c5070012441c0c1d0b02580d000350142c0300032070501c08c2c281d50f503040c1444103d0410008002c13900502c002840 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 44996533 1250 44995283 44995289
    0xf21020d140601180302031005130f050705030717100c0c080a0f120531020a0b071a0c03010b0a11010c020c13021c0e0102090303180310050c03040b0a15 67
    0x700302010305288000600c410011030403030b5400800795405001607030300003e801d089100d1100c0081040d95400c04828401030150600510030040340200074101300c0f020408800303865080d01221031041c0d850400d0215800100400741a5420899050704103800340e4000d9045a03285042c00d52481c4910340d80c0040700d921207070788800022090a10b848842c0c0d4810f0f0080d100e030621b018140060300b41510110f02001d54074288190700c1a501c10f80c44a004440495440120b40080030940480c1d80c86440754a1a071004000705e8a01440724101860144680c0c001d602074004201c04030304681c20010402080c1c2d2201411105000010009440c3e041c000d000318088002ea0b940a042c1d070501a400307000b01c01d1000348100e40814010f0000c0d110b070041c0c1c051041101c96101c01c01248088400d141d184c02841501c1c03c0e25014040000c0b24000100080b0b5a064600e006034111001c88100300c042d14115803068666180142c41007000c079021072101c4000540003400c5000000744200504a80c2eaa40c41d5a68 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 44997783 1250 44996533 44996561
    0xd020f06030a060303030f052e050d0c1e080d0f030b0d08090102010b03011a011803060c050a0f0302071203021b1e10060803040315060e01030c150f21020d 68
    0x1001e00c201640341c01580b0501560360414091801c110981d40e004441144185403003107440015240404027030a100c100600025040700203007260b0781000c22180449000c1d4414035003100c034285145a498016a40840c3c01034000360080c05403801b02145d0011740d03030205600301901d42c4070740300003a981c1c840450f03105440317a80074568841e0b50100190a40341010411480390b4948032440940d142d00309000c0a240101f4a00643e030134420800540800c07415410180c14075142000452085030068001d248104207500e6445c01409418000c405a1240720390040c014401031101059844c0203030054400c0005004592640341455000e0714035000d102c4600150300c104180c0c41c1d4003900303c10700c00d80c51001d0282005003c05410310100c0f030360b6440b80c2c2c480100314600f110070b207010901803a40b00c10042c0c1341418400d0f12a507580e08285401c42c030b4a0007811664000356010b41080c900030310002da00c20301d04e900d82d4407138a0740069134400c50288002024030016020010842c550f0100d21404003a040c2e40 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 44999033 1250 44997783 44997791
    0x1803030f030411180a0b12010203090601030b0a020c07092f030a0e06010e16020703140304050a080f07091d060c04080111030106020316030905060706050106030506150403020d020f06030a 82
    0x1070030100103400343c108076180200e03452000034020010412805a01200454001ca600b82d019404541c01c80f6501d80e0fa0011540f01205008ca102808140141207034003500c0c40110680703807101614200c1c030880709100c0341ca134801c032410084034031030790089203151030903417645040c8640698400b0324030f009100d01c800441600104203d04c07442c41c0d1044417110060348009103a0b56041c4906030144600190000801442603041030000d14401c03c040405035074440c1c43d10307040f00a14040b050340c0ba0001d000300c40c841c0110310740120f100800002d100310b41d04140c4004159503072601c20050000d015041c10f034091140022850302c0c00500400105000c3c0400c242284d41c1d4902c2d10004a08450032042341c1232072058100010090701d6400820380d0100103004000b00e5495102d440c054075070328020790155410140100342441804901c9c8c3c4840e04a58441c1c4090009507903007400c02001100e61811562000d100703020034000340c1041a0002c4801d84003514900ea4031110f0310002d015500111814144a070325 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 45000283 1250 44999033 44999041
    0x1b1506060201051005090114040204080d050a080f040201170901290a0b0f040605090607020901081e0610170709090f03030e07050604120c050907030609060e0601050f1803030f03 78
    0x42441015442800c01001350051820840010032030b46041c03150b4403d005010b440510680e0b070700d40c1120001e00070402101c081600e148001350864216010300000f040c0c0450010b050030800e401000d209541c165911180300b0440c0195640a81000c0c00c007010035136032030041c1c4001103220846050680da030700041246030702002003040f4600c400b503084403009a1050180168450300700040d6001c0e6821410070b9903d549010380032a2050080c035070081e511034140000066030070004225800b02940005003402c1c04421400e5281e940e180944007412a1000c20b5001c000395101101c2c2050000c0150055801003940ca07202c101c01d540413810240c0c1d2080141c071a080070541c2521a4420502d6050f01501c04649044002141380c05540320b01d241040380c207070248082184204c060b9000d000010300741015420300260082c0203003060f02a1200081c90301c01c2c00b04850707003020200360cc2160141e481d81c0c0303000d400d83c00034100c0390045c3da035146010b40039618042841ea02403016200410301c404219840e0301e0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 45001533 1250 45000283 45000287
    0x4140f0f060a091208130501090807020910060203040504090201030e070303050c0708070f05040906020702090106030501080c041109011b0c18061e05040e030715020301140303031003031b150606 85
    0x10024042c41c505078a0a20208001515005102d900c8051400c1215807030b03481401040641d81d9000c00240340303520b4200d02204100e425409004040d0003130b1003090f42980e038038201e0141c4002e5030107248050ba009001c02c12192400e6002141018418580882c0380291340c8c0500e840d04506070402c9021030004a20006645010803e260003054440d00070008285403601c00754203e42c0780c4c042c0d02d010f00d84881c400400c0c009550112803e84c5d81c0684481d1031503a4a91006005010a000309032050282c1802d43c0c841c0e1505006455142810750211403900340741c080151842c035106030032a01c6990300c2c07500030700101303101020307107401411240d40601c141400808032400310380a54000c08022a00c0345950311102d000810000140c1d003058800060701c034044e01490b4030314040e070340000f0015001c09210010343e4034141c001c5c5048071503001a480b0031090807820541c4a0100301d0f2182510313103c1c0744003000400d2203400c01800107050301e40c9624521a2030b4444030702035280076880b20305181c2ca0703010400c085a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 45002783 1250 45001533 45001543
    0x91f050d121803030f141b0601030201020106080304050105030c09030c0607060203100e0103030813050102090a0b04031101080c070b04030c02060c0a030207080f0a080c0106050303070302070303020123040b04140f0f 94
    0x603021500c0b100c0c40c20f0840c1c0c0c01400e1030140c003182c5d034200101240c460350790464110031642c20b00781c0074908019088401c0c02040c1d07540400d0004900650234030b034001681040c0001545d0941c0c105854090940d96111000101900320740540780e03262080414580554880c800100b104c00e009880141e501e161049502c91100800c0e808141144804001080803a0303100c0c0341141c22241c0d040c010650f40c2280c7c06c00e0303406400b9011005501811056000070150521f0f4000e1048030320512100c5c503ca6061401500c00100803252402c4042c0c0400400d4009040c000030141e01500c28104020b0071220360700821a550010052a41c075903101c0300d0810203054042140d0001084c2880061031010307155000e540e10b171000820000d10201010640d00c450034829040100541400b50403a500c40c0c1c81402c00a584150b50710064016500e0200d0307200c05601c010607800074601c17102d8100c11441d03c40b5600d2802c6c00d0802042502c40b40e8010040c01d03140c02c1e0607c2003000200c095030043c03116040000da00b605003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 45004033 1250 45002783 45002807
    0xc0503070e0d0807030c020414070e01080109020406020601170a0507031a0f060609131b02071a03090307020d020415030c0906080312040222020408060a0606030b091f050d12 76
    0x40c04400b002100103000d0303200315084284d040c07078464036040d403910204010b400d609500c88140d0140c41c081100d030329400540f8000004007640c41102d903990320b1140d003080344120300404005030041401403200c0c02ca041c444ea14801c1104085440d00c3d00c003500c50303d0030a07015400850740c4501041800000074219031000e900a24a00800c040c40d00303116000461500c1500d8540d801100c0041144407031100390780c800c00d292f0904216141a441c101c10000b5200e4145000e100d00d540c40c110b122041d40c54051040d248540001c070000c5240070003940030420100d891103000c0340e000d0b48480c640300c42d003500d808545000b1880b030901001c1d038900301010076040d28180d8100f080c03143d1080c0400701d00b00c0100d40c0c1c0c854010b80c050303c08071100d02c140c0e481205101e014024602c580c42c000240002e02e0140000d02912a07001204204015521003100314103542038243c01580c041b001d0008a80005041000082c0405558847d003041c2540d0780b004c1803a00030090410b0742c2c0c0013440703040c1407915038000c0b294000c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 45005283 1250 45004033 45004039
    0x90207020f04020c1e0102070c030f0b01081504030513050d030e090106020318120c030303070f02150402031f021603120506040513060504170c06150406140d080d0c0503070e 76
    0x400340c002c044c4940d03601070301d0b04580d002003070105032a02d884029811104503d400100390003810341c99081c0844804c00b510400c0364030922b00c4000047c0d4940109020042d10081c1e09148a180c4803a202102d6540058078207103842d86143d01d00280542e144100546541c1c03203030300c0e019118503400007009442003050784120251740081083d001100e4404020348044c52044a030b210b03c1351280c4801500c1c0c14020010aa018440002441340003500f00724003049030321150342102c15480e1384031700010328a0001c0e640250554401780c903400317090000c808030301d003480b0340550018140083c011410b1040c0b00c500d02c00798081034001c110018822080d0081e25800b4800303135024000e5043c801d010001041c80c41c103016000c0c40d500c201140800210169042120380b2041c050703901c402c003c0004548814054401d1204024800c011061901f098000d81c000c40d01d061103455131503820682488003c0b001c0728422074124004101c804018240380c480c1751704000d000d0f50781c1d035101d00d0310600c050402c20700030031003c2c4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 45006533 1250 45005283 45005287
    0x1209090e03070f0804080d11070909120503040302120307120f09030f050c030d0f05060f03060609071103040506040e0115020f0304180915020901031401030f0305160507090207020f0402 81
    0x208103600004079030005900541c103c003100c4a0303040640132802281c001007594080d2481d034918050380140001040f418a0040e54112980c407131807101222000e41c0001c1c45210800d92010038a03010f500610783c800d0090040e2251150303445c0c2c140d8481d50044441002040c00c0300720304501068036104481e80f00324501d0040040b481c42e5140944400b102c0715056081090004010414074424000c0e154101c4002c242404074522060320f03900a0401115040c0c0907040381007040481d80b90001d501805110301600c01d46c41a02c42c2c450482d140c07080441000742d41e10080000050646414009200400e203481c1e82203202d50400450143e448640d0326000308540c048a200020100003004a5007240d541c00551802e0b001981d4409005d0f11480001518524610303a0f401540c619035001420700349400d03601007044486041501008034820301000d03100d8004d6204010000380940010100700b810b00481040320300c0e031541c0c1c0c98034040c240e4200000e069000310f1010218146000c5400c030041c02140c00358 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 45007783 1250 45006533 45006551
    0x1e0b0123030421090e0f0411090a060b1303030206060a030309140a080a1407060c0c0506090301110d06030c0608090c090a0b100e0a0b04030302030a2604120909 70
    0x254041100a00003111000c0020101c0c040143d054188a1030307604407000704100104009024000e201039102c0e144202844000180392142540782c1640b046034000000a40c9010003401e001211100415007022507907a501c0200310380822401802e441c490103524008901d0031842c1c0242808070241845006035005c2070305100080d0400303c00000c1d118140381000068884100042101402c2d50101034103005080340c010600801d807610800c655880400c9039007456449508440b22440780c14080c180090030001482149400ca000341300d14000240007045440301002554042e03446110b14400440e61044100f040021209002d0010304541c00c01c00708601d8140340c01a201c18104217602e02c9528100c00269140745c5681c040d008410300580040c00c142d41c0d408001d0601c604e20040c40d489100c140380b0018070401440e00f00c1c3d0a503075040d03014500344050800284c0d0745c90400529403d51408441c52407000000c907182007441140115208107040c034100d0320217800039040390800706409041411031 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 45009033 1250 45007783 45007817
    0xc0118020f01081e0601090b2107020c0303180402070c0f17011b08130602030106090609050a0602031204062a110a120f030207050106080123010608070c080d1e0b01 72
    0x40030120082c4615041380d43e83d18012164606150440030300c01d080414102e281c074500c25640070016908405001c00da45883c40d0036070366141c80442c000d5141d481004401c41c055091002c40c80c5480380600054101034140e43c860040501c1608076003030031403910340200070807515030003456464a9030000804c6041c03400c030104c045e2107501521358414031000344082855080d8160510034100c2e0800c0003191a561900001013130035185104400009006036030101e05440c01f40300704811200300f50011440c00c4a144e11200d0301500c010f00a42d0741640d140130350415009200b1320304400ea40c26003910003000c2d0b850100030b8040419411075001e030340e100c0510309001801c094807200c03009074a41804410101050800c50291088600082465003080000104110150043d1043c00011481c04071030000c003401100141d142442401d0004051401069005000e90052100c3d5030103011468a00f00d00c014050b01038889040b940c64040085141c10740c1040344904c1103030084030742440e000365482c10160f42 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 45010283 1250 45009033 45009061
    0x20c100503041a1302040c050d0606020606090109051f03081c0203041203020c030c0f06010f05011e030207030c0f05160b0901050415020c19090606030b01021b04020c0118020f0108 79
    0x254180b2030700c4804124900513501c4042e21582d40200188104080540010915004620011700d41c0341080c0003c112240049481ea214500152030049185e21781140d0501030071014040b000d0103050600140c00d0440e40005c10130185000c1e41e0ba00390303500c1703413010b1103400004081c1c0c564128030b1040c8203110014065419200034103c0c40d180150725001320200d518118807034026070140d01d00c620001501700000100e4010b0403102d00e03000d08440d06643c3d2006450f00f00100f004280b0400030900302180541c000e81c054502c0724000c0c6040744650240e40c1e56005040002d1000b075a1a074412080540012280c142c5103014200302054035040c1244500040c006029a01070340d4150b94180b100c0034190391007003000f8401c0d1400203144a0b0510000e03c0300c1c0c09403003554003850745500d08100340800d00340d0081c0682c540400701070f40141855007a549060b40045501c80c4001d500580820099a10083c00d000c0c2e880d0500c0d029112030010107841c4100300180e01d5520500d2706110006003000419040009 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 45011533 1250 45010283 45010313
    0x605240d030f0e0a0e0906060405090a030309050703020a0803030f0c1c09061803080405011b1e020f03030a02040f0f0b03010302190b0a0507060c0305010b0306060c0705030a03020c10050304 83
    0x1800e03940822008400c0e20705600703080f0100e812101c0100e0024040107400c0300307035024041050668150b40c0300d5806000543d00100d4039440030f64020003120300040d200e50701096483e0302845c2910315a94881d40002c0750403115520003000d0f82c0c40417040c002c2001c2044d030401d410801e01640240f402001603a110b200900c2000e60b50483d41d51840c1810070300c0001c1d00715504030005600c0480f166040b03482c015200803c1030350140c85940c41d0a25070320740f00010305e0700044884507541b40d1008070003556240da071081d011000c410317045009590440c0154182040a98003500107101c0241e12917003071100403507107001c5a5200200d8034038502d00800a522040c411070b815a81c064407441c1010305429000c03449071030183d004401034040003e910881c1039102015100062240e0410b01820141103000c030700740c0c2c4080c001c02c04000f0b0100045240c500e0b0010050594400700b005481d00c10f81e442e40040d04080e104801500580c000620f070580600e480075401040d00c1c01400d016043d402c051719002d44200007070b5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 45012783 1250 45011533 45011537
    0xa032003010b040c020f060109020702060301091d1006061103190809070f09060905130203070e0604061e03020109170c0d08091c050105010609061407021c0605240d03 73
    0x5240410a920207402801d52488003900038001045030b004025a42c9415403482001c3e402400004681c030a514021104540d40041416042d6420005414014211050402070300035125280c8003c000050040d440703903224110f0000380c01c2e4908903016120303107030740c9031440f0803904108060071170207440008503080341c03080c1e191941075a5210f520b038510301402c5400264040c00d10400000e080c013001d0b0844d00c143c03101d403001803100e61120440c2c0900a454031400030f40c19080700205001050300b00345c16540c4440018000b1407825034a40741c1300741a00c840380c08a00800f412900502c25540c100308004018840b101406928120000f0850348580c00110340c98455404c0032445010b1100315000d8138020180188120075860200828004000b5500c0b0100c69030b5007064000a1007e000d0b801000442d13580741c90740f118000480042c05c1e0a6400108120790040b40501c181d01c2612401d40000840ca00c109000070319824901050780c074140ca580840c00c08030302400d500072580e80380c0701c0c1103c018603818 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 45014033 1250 45012783 45012833
    0xc0905060109080601090203010f090c080402010c030306051e04050603031329041203030c05090f06030a060305120d05010f03230c03010e030702040b032107060f18110a03 75
    0x101c40020241d44800382902c1504c0011030707944a00c0e402181200c84450102c040140c0e90305a04c41a507034442044004180d2001c0040c0140d40144400810136100785000a000741c0c40c0e02c009a000004c0145d1804001400d181d480135a003864481c05811001c01c40c0290304010002031002a40710403801484900104004141d02c041d0100c0b4010740320b560081151070b220303915005d20282c2e2070340710a019000203003800c0ca031201660080040b00c0081a010b0540414080c00b5001d2015a5002400c92141690b0381c0400001040040c00b4403000e03e10b41030a0365030f960b2550941c41c01501d4060308070429080a5100410014684140c0c856400741c40e124090240100c40a00600300700c1142070007a099403c002c0d59092082d00480101001c5208440402100841ca020715a0b250340151800500b43c100540d00700f445000308001d01000da1050002241d62020310f445801a1440d02c0c54400d10a8284004041004200d00350703001c0a500c15110502d449140d41c0f900d9108031101801d030b0b444441c1d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 45015283 1250 45014033 45014041
    0xc050607050c06030123180705070201090b040806010f0b0307050901031d01090305040501030c05030603060c07020319080d06061b020405070309050a0b07020c031c050904061d06030106060c0c0905 86
    0x2042c0401d10302820020803040d100d60b510383c181d00c001e40c415030740350340000340561264280380b419804051030b180003401a10708550f02d840c02612903601880d42a0305100e40c078400090a050148003c00290034000b024001c15450001103005024003900000080e04061040118056020080e18541c0707030b00740380201c1c0c2c4a4403001445d034011204810040366500b0b1140030814550814010012280282c2c1c0c100107418403400e08454038003003900c0c000d52640082000c00c0782c000f00c08024118280c001029a441c2c0c0143c00810040032502040c100c4103040c020961005002c4d440c0b14030740081c2158100301600e40c001d5000181300320000e143c028444c50f40e501c04641a80d1207a848501519400000c80d509490b807810f001c60000350807510000148559141092542004513012b44071610441c4074420903101401d06440540008220303035000759442c40006456020368460a0b20003c240b1415542030510100345825900190829010701840c078640e100000c4e40d0032088821210500000502521 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 45016533 1250 45015283 45015293
    0x1b15090501020307080f0702010207030c0210110d080105030709090f02130b030706020307060506010318031101020f0d0b030c03120405091302030109030504090b01080601120213090f090516030c050607 88
    0x65402502542c4040208a05182c000e21400e0040f0001c0010603030325900e00394124241d2003a000001c0000344400410300c018244440c0704050403440342862841840300c02d14007840d0594045400e000200e20600412082c2428882d160207001c1d001c0d014803120f00346880d0201e01103a071503030090040d0300c90007134110384420039407000f26507103001400e07248600d5444c0c1c0f00a40e0307031300509802e07102c0d14a00343c045125580203204e4003160140030070100300d10f0b0040b42c9054410f40d107030fa460500755540030070405550b110340c0300003042700f00b840306030014540391007030181072405100100490182c0e00c0795200000428821094400b101c4003110610011341e24000680300a10640600030742541c05e1032500c40c2016000405803050300c00b400f504214500000004545010301640c405000c15400c0380040360083c0c10307070014401c00120183c46884269552000021070f61350b080515030541d0f45151000401000f404440c140c0c00c1282d205514050642e183c0d004e0200c000d12a09108040000d000e0081007 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 45017783 1250 45016533 45016541
    0x3030e0105070218070306051503090703021306120305031618120201020106050901030803090d02010903170a0902033004030804050d0f080f0702010f020d12050c0d02031e071b15 78
    0x55500f42140a50741418a80031b00035020a0181901ca00c2410020607000c1345614142e0f481182c0700302c02403c0040c6940c091200c0071a100c40c0034a281a2a02030109501c241c21008103a2548a035690756074910300034002000c18900305c40d010080202d01c641051100c5640c4086206692010742541e065030480d10044c1c0c01446298030440c2c009001400000900542d83c003d1482aa10303081a601818805502242211805400240480d40f40d594840903101101e80050344260001c600043c0050b00b90002450541009407244030a060b0580ca2044603100c1c2c3c01d06928666103146290a1a044d03a880d04014000d074001c2078060b5001d42d66200a00c040d001c0d0b101d9000b074008400c5680c0350514511080e0b00e61200000380c1c0407502c20f105502d0141d1001840728410501d5a4625403003080c1821040080d24000d0100d5291140900015484d03000038030041d0b000f0070500140300c5541b002540c15104441c002090350082c4445000f21008040d5203107d000300d170581c000d10782c0d5007003152108010020 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 45019033 1250 45017783 45017809
    0x103140309030d0e06120a1a0a06141b01050411130603020a03080706150807091103071e09170303060f09060a030303150b0d09030e04020405030a0b0c070803160e090103030e01050702 80
    0xa40201b4041c8054100c0780c2d0700074071504160f6003404101030030003400c2c061400039070300ca000000340001804200031510307040604840b140000000718058642080103095035429201a5100690036034515403034500070750850210900c0d4141884018650303000030740030105c1480003400c1a00002000340030021030358452604040001410041140c580c141266074000310f0207000a542c0c580148821a80400c00c04d0b01d202d18425543d1000041c05c40c4210301200b8900f004010038802c040102041c50680300c0384940f442c000d100000e60f00d03031500000700306400071440c1c5080d0141541e0000c1c401d95890b58420320041d07a405041c041303040703c00030401e03090b050344d554440301114001080005050443e0f4021813034481c000c4e07076041941d010400801c0708074840e07849003a515134084030726880024049600f00758000b48204040f4205a116264580c095004864a80e0b0703c0d0b00e603422510b6919003003501040070040c182c4040c900c0350b0540da800750020404030b60441c1840340101d122011580d038000c2c21429 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 45020283 1250 45019033 45019057
    0x10605010e040207060222031202070f050d020a090606030f1811240f030106030b1504060c02010306030609050307050732030313080f010c0311091009090507080103140309030d0e06 79
    0x5007c1ba40000c145100b09180403ca418881c0e014100151620002d0044140d6800e1050f21540b5441e20040044c080340740f050403600130740d5422000445124a10801c0010209034a0104100c4420100401240c116802c007408260002c010200803c150b0b199000000400381c8030520310078020b8040d0744d0040482e201c0315256034800985044020030a01c007550403903009440511406540400300324160900c43d00814070414188030800010741715940c3d0024141c01030500083c04c2d601d0f519000d05541000e542544c0c103500004289003004002c22040c80201540c03c44800c808550166210510601d075078000141e40003d1088840d6640600490704401c0801e91540040c0356940c0314951656020790205040394640070048075500d0280c001d0480000d01000f0492501051804209078139002c0c6401d2810410110008115840036209140c018800d54a96402ba0341c911700d46040d04503907000c50400750740c00500c040c2049450000301c1c486003c90f030b8100003d498007180007007042801140b090f105 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 45021533 1250 45020283 45020317
    0x50d0e0a09050403020d0f021c03050c0c0304031406070f08010506030601031b0305100b0703051c091e02030c0109031509060209130902030d050415080411090408120108010605010e0402070602 84
    0x208164000800007100106ea03103a006c1848220314059849080840c1114910440380c0c1c201e00c0060310985c001507100485440985c01c00d822981c2451031a00550001c4070048035565007500141d608101d001c0d07010300301d4982034119041d0080d00608440b010f200c2d940c000d44022001c540030741e02a4100c0010030101c1d8150480c0e41441c608002d014100c180c030349102d41e40702d084020540c02c141c2001c43d0146501a02c8841c580700100c00d5040c0807070f4009443c2501a070b40c0d00c1c0e0341d10004030655180c1038600d0480500c10100b5060707004041c24002a2852503060041101013000061514019446283d41d0104001000e034250b0519901922903001d40581c489110400090f02e8589641f000d540a80207034105c400b03139a04200242c03900c2c403d90081a2a8502d001e051600d214880c52419900a10548a80e100a40d0300c0780483c140170400c0d81c0c2190b01110200703250412803400203215006210240007809281c0c9001c001800081915080c01c1c01507030006500f100f0b000c0039030116603220003000070305030b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 45022783 1250 45021533 45021541
    0xa120c1203030f11040b0a0503100b0f0c0f0321060103240e01050405060d0b09030f04060302120a1401061d0d0605061203040806130516060905040e0a050d0e0a0905 72
    0x2c00410020340750004881c0b510b040605044425400d8601366400c40881030700c0c02010b203200755240c1e0001024002c0340805120041001701486026050794404921002c1d240c9203d1b4951500700801c051241c80705510600140485984406041c0900804407440c05003070307100c610048003d0036102c036580f1a243c940500b000d50030303102e084201045900b03165000d007050b600ca00401c01940c405844855100241c06085400300789019030460300f00241e0f904403032406403062314034403203500507902c8a40465404100c2c011401320b1807113001c2d404102c6203810010b107008407141c6000001c040c0101c00421009250f025010050328182c0341d08208028500082000d603441e141010709400c43d0010b00070036007041c000c0c444c518000705507416201994064800d540e100300300e034840050008802e607054440c90403101911500020480c01604d41030ba954140c2134100411b00044d60074a0301264403076408980d00401080002c60145000e004c07a10b4080401413034800041d0101a064011042c01480c0c0030601c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 45024033 1250 45022783 45022787
    0x5070908070807030b060909150a0b0414040b0103140102070501020409050108010617031e0904020a0c0201020c060c030306041802120d08060906030d0807180e010305070803090a120c1203 82
    0x502140c403004115415207407604640354581840d07110042c01e0750806408100c0c00c3c50b02107021036212600f10b04171281010403086070415814260355007418541c4c1d4000d11002402e06d80034407024560107004400c0309042c00c0d40e03249819401484080c0c0b41c90700c088820200e51000f0b40441d4040f580040007551902d8440801c040240030030301c510510b80d07284c020001860311512100c10001c0030380f0805142043d100e6030318800c0d0040c411400504003041041010490341d11031000d488850081e07590222916100d100183c44c0580c01c0116a01c1807030180103890f0090000000c8039400a405e03540842c15500094011445034043ca100a51002500d41c0c12072280000041620341c0c0752040c2d4804180344c80e103200313000b55003500f502d8680d0182c00592234410928080d02c54540c0085041ca404001c0a55070321200100302c11507004201221440380c01001801010003c550180038810302035407600340c41c000040d03566402480303003641e101d030285a22000e01c550081944010507200c2c80c0d40c10b0040a038600 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 45025283 1250 45024033 45024047
    0x3050702010c23011b02010b060f0d0f0603060b01090905060607020f031509030c0606060f04060503130204020309030c01151508040f06330302060f1e0c010203090d020a05030d020703030f0507 84
    0x1201741026040315846425105000b58920410302404031868504048202801075010349a80c410154480b807041e2400b40e15480344200550103503c0000303040d101b074000105108640d9000302407850a040c1413001980d192811120280da0445210107080c10000c0440c0c1425900034900114078142c0040046102d004401081d0080c1e400b01070b2161923031000c04002c481d000d84042c2e5100008244014010a4022001950041030f43c000f628035407586580041c00b40da10407140d040c000c1c1c00102c1d04407000316090048000008110454600c03090070003c0f4486070700c400c1e2141d101000b0081d00031406100e0412803a4140715040f0f442031007105c0500b6551304c00b1020720f407617000340e4004504030888802075aa40e000180d80d8000d007600c0c5840b900880c0d010326a041004c40032598241d4a00760092415030b80010300d44680628005030312807074a42c0019060002c405500010b40d0040500170001039004012202600303090000140c032071240e070408030002d0008102d442d401d06d02e800d0920508030380081c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 45026533 1250 45025283 45025301
    0x6260114270303190b03011509061509030f241a090f04150519021917070c020103090c05030d0801030506160503041e05101407050703050702010c2301 66
    0x221240341c80c0a48005540e80c802101c2a140b4082502d81603138000e0306641019004810080021036815181a8002d5107640300c1d0348450f07a0310381e655600b0030041c3c2c089400320025140d00d04000040c64a0340e200c00c1100f400c03000e001044803020525000c0701d040800b082c034001000c4c510040190810120544c400c82254058441c0700b800c18400050704c013843c0300d040c035220f80e80c4961602c40682d210b1245502501c07000d00340301c0900e903205440341624400b078400303002c134009850141094010302c3c6602804100c03d101007009030108190801c04019000042186110381c2803a0000d02c2616034140000401440d4000903414001e4602c459500c0b0790101c980c1d4180e900800c00e640154860f4003141c1d043c80041440100440d01c1400003038003240020303400100d0851841c0300e040b4600901d0341d90354244420b8403c01140556260360303420500080808050703000085050091410340c880e01c1c05481800f540700000e042012812010317080085001c6149415030190001e490b040210641c002d0190003a16 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 45027783 1250 45026533 45026581
    0xd08041703071e030203160c051503010509010506040602120307030b0402032d0105030a02010e0a03080406020a0302011104060e040b030c0301020d0b030c0a050609120f03071505070306260114 84
    0x10b501e43c038040b080c40d0845050a0340c140c0055181a50784c00c00c007610b05680800a4410856411001070140c80c0c41140c41d22684950310a02e80c2d9604100070403c1d1404c040c2c000b00e01900c4180400d200894002500d0740340c0bd50100d01d0a40c90b0380e02c10714200c024008060000d42c0260011041c000ca44561020b201c0ca50035409441c11000c1042c0030341c00308480d10034466a0f44c90fa1207200b918015501902c01d0041c1414090304c1800c000d1388984405a10360b0103a800070300160312901810050607420301c14068417050b43c00115181500c0d007a80140b00500c0d20380c0741403280e981c56190000a075020040400d0002000d0020f64690103210348090007030180341d105070b01038042d07000400d50525104011600f0b5070b0340100301c0d604040d83d4006000c103100510854540b2407042c0001403070114810030243c600c2c10320810000c104246400b49500540380041c00d03140c10b040c00d0071814400c07110034810301002c0e182c29416030b001d40300d150ba640e18090403c019015003041850000d0201c0481080c031450f018076280 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 45029033 1250 45027783 45027803
    0x203030c030c04080d0e3a0227070807050a09052116050f03010603080d0509100509031309050601020c100e0a030c05180103050307110d021f0206060307140d0804170307 74
    0x756005660741f500a5000001e000e00302007510782e0b0560452808000e050000d001340042042c8003481e2591000d00c806c850078600d401d20108401c1560088286500200790718003142044200b0f04041c00c5018503014582c40351000414030180e094908122000720300394001140c90071007201400d100c40720000c0c0030301d901410310120200c02900b814045c80040701e0f8400c00036460302510360454001820050460310140c00f40c00e0020006080c24021640180080009980d80300118078404012201c2988898046410700c005c018460380c010610040011083d10802e8501c2e50320364003203e8a50040700380d654022410a0040300388030303a400f1080107035081604c68101c07140846d405442317820310900c402000740d0b0040100c1000200450441e0083e0300e0050036241e0220000d81c00146400705080c2c0d04100494480d400e0140d05a0400440c0d81222040d0007070302c40340d8244030410480c0c3d03404240b82030180d8501428503080044900c126001081d418111100003030000214507165072050809030346010107 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 45030283 1250 45029033 45029059
    0x210706020f061b04050a090b030d0809061302150a050301030203070503030f0d0f1b03020901020105061002101e0207080a090f0e010905040c090f020c0601150203030c030c04080d0e 79
    0x55601c440c070180030010002c82c2c0e24198545440f110000541252540501002030291594155030f4041d088000f40450107000390303014581707050058003400c8100718881051241411000c100650096040322000c841c070000340c00071400c0c2c1d40146202c1b2005032303400a8001041c80e40603029505a9100701c081e01c1207d6070fa8030805a585c012110855407121f020486a408a030f0300b64003c840d0907a1000c400f2030b2400941e510b00030300305c185034110340100381c002944503a50f60342886103603442417007154000b007504d6440b40c0095550146211164903550b440c000101c0000301003070400f01c440418402590784030003610305414241c101450310301c0400c604400c0801c05855510201094135010103910000b43e00e0103249802801c0050025100c90513410f03000308013101d05000b00004a10000400369403140940da030140351142c16070080700c1d07010501d03400350303040c40d03022040700d8001c41c4c503141198a13900d070900301e440306109583c0500001d00c20701412034005d031b402c00c4502850040454440407400c007 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 45031533 1250 45030283 45030287
    0x1805030105010b0f0a0909050a0603060e06072a0506040f0b011409040f02010c02131d0106081b120303131703040210120204030813090606050c10050411210706 70
    0x380140d40074900b05001c084c0c03404081c40007409513504240b038100503269a1306184030407604152410034540351031b003000b88203024031800f0381c14050300490000c041d2854220801040105100341101c070841c92a8111030203024a900010403058100c410b4070b10508103841c4c00000c2d1003402408413125040400002018000d13440000d484060280c9881060350340e542d20450080404403040b418817400c58810005030701d81d00b02c203a00848a54400060101101540c0b44280d520541c1115580c0e040c80c0c0309000e086004107502c007082c1002c003007c000e42541c50001a04003484c2042038141d503c404020015003152000720200440e0080515050641c40500e0300e02d107500c41141d0103900086800480a0302d030f442060109400e003030740c135070050406480740d55010440e4001e0000c6202c0c10441030080c08481d055129000040802e400e00e0b0307240c40b447c1810b0701e880362000e10040e80c9240d40c40c000102400b942e0b03151103a4a2000414007641e2841d8041844d0000b42c18040b690350306d10030000d010401b18 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 45032783 1250 45031533 45031541
    0x4080d05030405070501080c04150903020f030111070f05010b09040803070f03090201020d0f050c1b090105010e0a030b04020f0612090d090501170907090204080f0607080f01060e040e070618050301 86
    0x2030b00703c0007a01130365041400550340694060014408131601300030010740c0c100702202e5004400b0341d07035450703100345859070040200341c0560a80c024426450944120403a95058084410a41c1c0c41451648001c1031030400300e00610003100580e030404a461f08000400102c04000c511032111501c0740035044188030002c8044a00700000240940d0000400c09000c0740103108015a0030500e1901d249000243c07003516003002c3c0b51800c950321410340c1500a4405150030311050f800350000386002565002640001400d0340c031203100140c03441c40d804001c64150b40341c841500d40c07060300240099a0300c001c07610310b07840e40d0b0034102c1c0e0000369405040c48004240740706520350310072648140d4540c50106204049010120030151400302544030300d06001540352194009040144401c1c00070308000e500c0b0101c128100880140344604120100c1c1c00c100f58101c0110b40030b81075804a1401c00801e190440c0810010083c0c0b200ca60900e01c60a54000780307203a8440600210b8600781410303403505556400070705007a2 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 45034033 1250 45032783 45032791
    0x905010801060b030c03102301090905070206071211040e0103060b03010c020622020a06050406080a090c0e1e09010507030e0307050d0e0d0b07031413150f0209060f04080d0503 77
    0x2524042000c0354217401605d0145400031902e81040355a03650f21640c2000448514201c800041d9070060034420560300017940d50300421a0705c1c0103000710b18040500a45030b0000500c2207091049010030b01c400b0340c071103610003c01d0203141043c1079a940d4031000d04200340360007484111a4141030a04446490074180590f2030303404060340041500b521150602d000e1b076007080c181c0320303d44c01640080c140942d44040c03603039005010b60f0711140d9a441c24100003c0003004003c010f000150b0500314480006868049007a088820385081070f8465150035160795018040c50500002e000585d00a00c000135806602403402185c00352000c000e0411601091078913402019006001078102d2046101d155000d13024510558900400b5400d03514519994410b84290a54040c40060fa648460780282e00c4103d01d0310b81c1010340c0c005028000300883e505ca04000c4070720900000c8640d03c5200b0204030b10225010f60361140310040409480307840011110000381c2091107104c585215180c1d2200c4400c0c003d408807805 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 45035283 1250 45034033 45034049
    0x90a081c0f090f020919020304080c06010501110c060318030705010f240b030a060e040803010e060a0503031e04080102041e06091206091b15121a0f060702061201090501080106 77
    0xf404a150b004c00071010f04c01041926520501d07100c004400c590f620080d07210f03078451224981c884c04144110b03481c1c454140c002a052040410004050102c00641c00c030b2402006c0f6101d0b07603a65200759240150068018015410744008070f400410400107401400302101e103a0410049d01508a102c3c8048003180b16401c42d05920950040c01008003440c011b56216103040070201d01031b9610040c40c0c15a0780200c40a441e01000032005000200181ca6816040081240c00c00202400e00c00082d81703034840c4c1490755020390440d0b0341188010040c441070b00d0050114034000c545950b683c0d000c466141c16690280e02c42c0c105520000b050490084240f4000e841384030b41901105800c0e03a403000001c00303106206440130320300304407064402c15600c5504400740105460701e1604141585002e840c0d10a0742c85018242418480d000b000c080b02e03582005c41020080700c12038a2969180302203000d40c810020040c1d0400c2000903405001b03a414200c560403079440c0d04040003d6a640c1e0308040c200c410300d01803409 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 45036533 1250 45035283 45035303
    0xf09080a031104050a1415130312020a03080604020c071e140402070f0311100516030c0c110418060603030e13110a0e01170f06040b010e030c0108090a081c0f09 70
    0x200191b032418140b0700304017000e00781d039881d010b034100b04903980d0b001101842c600c004510420f000704480580b0081c40b0343c000d400105030603c203a54000e0144079005001e2400740c2c2c1d002c201501d0b10f002c100301c0807008040103903110044929541c81c0321128074071030143e40000454128a040d01d4107040c4216040290400031200d0300c03180e00e6a04640910200040d58001e204811a021580c421032003101d00a40110220450400d4440c0d8090241d400c05e81c00341c42404519880e44002c41c0340d005150701510000c641c00a10304e801c100c500400c20b2504903004e00311a203020408010180c0081c801c40340410308a0b550762468040d06403a60a81e50720500e110042202400081d038480d000d1440120002c2c01410a200321f889400090036500d0f208581504071500c0803014084981014458a000c5807828a0003421044c050310111b5500c0e8646d13901c1c2c40c10822004005041980700780140081c0541c020405551440729002040706a10420b030f100044900d402e0070212810410312a0030411079001c10a00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 45037783 1250 45036533 45036539
    0xa0e0105010c0812070207090e01090f08030a020706020c0a051204060504030303180f0606050405130506010510020312040308040506060109062102040f0b070b090a0309090509010f09080a031104050a 87
    0x4031411110700b0304450805090005145444095501e18030900c40d1758010240c035454400c00c68162489a600301a00381d160186940110b2a041d40078004650044844d07a66070b1980c2c94410020702c144040030b0000c0307101041d500c01d880e00200d403000e4818003e5084400700020b001c50452544520301c244004114200801c10000b4001d030000c508a44c500144404051190f454004588908440403980f0b00e64400091200e441c0510810350403004408247c00824495036075650790b1041800b40e28400c80854034a100310510810807603643c1c40710002c100f20281002c2c03802400d03440c02660100c0c0e042c0103143c0000e40ca5441410300008440710307030fa601149482c036003641c000038445411484114580030030010605064604200009000811860303a5031340c8941080c01004402030300d621206d0304180c50300f0000c07903407100d140c8081ea0511440000c03182c80301242da03401046005104c410031400c10300c0c003206009604014101044590b241882440e010b42422009440f450142d150b108135030b45414 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 45039033 1250 45037783 45037787
    0x60507030309060b06030103030519020d02030a08040f140f070909020a0909020a0305010509030a140901050405061c1d0c0906031b1201060f0314010209060a050c0c0a0b13050a0e010501 81
    0x10b049001e0140400258030f6a8003008240c4d2075000b60410380c041040028110350214501c0f128401011a07440500720020b40c16800035121b10528003550108a440000308090025a8000000640e4080c0e0001444600c0c01c01c419140c4030235080143c15800380da080082c03d15100c6c081c03c00340a90003015540403034148000c0d00024030f1040400d07038101c01484008400110240314590080c08e480c4021a03c1d40818500205003000e40701d06003a01140c01d000080d00341e60004241c9083c0c601c00c07215603480311082040da5204140e24562403455604280d031079081b21443d141d018480381449019a4503c642d004180044460103491064141e48070091410298004c0a040300d0201401400640c100304101002400e5401a0300107020240e0500d00070410014941e40c1c2040034000701c0001c3d400c00503d580061032600034600b8910500c00c0028801034444010b00c06420807540c001c0200c0d8569440d90092039240d0884040500c2108200d040030542c1e2810750444000c448030307000c1c500071381da081c5001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 45040283 1250 45039033 45039041
    0x6030308010b0306010c290405030c0f070e01060828050703050a1a01030c05120103050c030c09091f060e040c091104080307060b0a0e0421090605070210110a080706050c03010605070303 81
    0x485881091442032151f03600c40c0d2110180102d01640c005c5d926020715588490a2541e8403001c946a41d00051007008203403d41d504e000d044070f105003003049142d600c07845041034076409500f041401550000d0307680c86c4080703240d01c002d0281d00507a4013000b40d80d590001100880d08010030f00b0b0741b56803860340c05510f030358403a411840344031a0a1800ba8107080b01141c64610b070440070b030403c850302e8024458041c2142010002e10b031200c2c904586040441c20500e184680b5048a441151541c2e024900c14000d81c2d041900104014280041703619228a4103080c40990f60805005140030f881c2020102c030f00400c01003050750140d99084003d9881c10007543d0398100104203d007070a68000403c0c00d4002a03040c0d109000740d204034058030306420700120010103004c2003d44001c101061250604d000c1c080b007503010099131252681039503d03508401c1c000209135540b881411140b5583c0c89a40f250000f000078a0029280c1c080c800c4005000c1c0e901da416024003039001c24081d10001510500180c1d020a2103504 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 45041533 1250 45040283 45040313
    0x3270309040b0406090e0708010c020a02090a050403090506030a020306040c02160902070614070c0303050604020406090e0714040602071d0601050a05070c050301020a1e02010e07050d03030b0603010906030308010b0306010c 97
    0x3c400038801790303612460810b03500d0f54641e06040e40c001c8003003040f40000a01540b055050f140c806001d900000354001051031501a03e60b1403481d86e10000076003054001e05000700070780744c01040d031030b202c1c9400001440698030460701030740100d00700412114030728000909002c246481c881d1588209081c0b46035400290880384065601e95118004504109582d11030030380202025614030318050940c0c24050152107001d8202800350388100020010503501c618540240c8040d5610f0301500c0d00e420a080b5084284079481d8141d21400080c00544035400182c8e1004a8070181000201b110489404100c10601100c0460214004000181a0500c21801001210700c1081d550341e0003a00c0300c0c0400c0c00c90f0401d480d80c101040401d903950881c18218800782d01507203003901c024440c07200100030450701c1e00720920986000e420342c0303c001000c15000390040e00304c0c0c48000d80351a480e0761b91120024054025440140c01040041002040d507290350011240300c0c14041c0c41b01643c1840c1075a4452080075100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 45042783 1250 45041533 45041539
    0x110610150311280806030a060203060103020c060f010807060206040503040e060a03050102071b0504020702010c241401050a1a031f08030307080108070909020f06090f060d0203270309040b 82
    0x1c03002d00d031407012000180001c21a0400d43c40e04640104400c00314402c804410a41400914020410b4070b036030002d9065003035584501e0150b22901c41e5001680030f13000b46030a0310303647d0164404000010010b40d426504941c8410110f600d016902c0c94240d0701d91000340c9000d040b81e00101700c140038840301100000d4100c100500f03d05411903403900e0350340c221f81100720300b1203001c2940d564040310660440c01c944058041100c0851422001d680042d00341945001d00600f0400214184601d00a80c0c000c2d580b200010f4041c144150301c000c00c02c900c00d0b0102405800d10500d0818008550b4112121710740b0440036030010501d207903845002805c8135034004154405402d81d560003021400c51424805140211815280d9007000d50412542c3c50522103a40c0104d450f440c58041040096a5040702040190409894190ba41c42403400421000c010329800c04c0c2c0c10000c00106160607148541c0194840c0e140e02003080181d0000318040050120900d8070b68400350310a00400385c6c40d1400d688004141d480007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 45044033 1250 45042783 45042791
    0x11070206041e0510030b010807110a03230c0c19030309030807020619020303040c0902031b090303091f02060a060605040b0c0c0a0603060801050105060a140d090f0609031106101503 79
    0x3079070020344c00c58680d49180d400a51904046200b9580000ca07203a000304950400341d22005030300028581d200d01c50f1101404100c0c800002d21030b40410400c2c11444000300c1c040c6a48d0700d4442c5860b1035668000d2440503401035500802980d41e080b461103543c0280c07641951a040350701d2443d01c43c0311032074000c43d038181e911003010816418428010741a02c65109119009580c82e0314190408840c04240b952040c1325442c010010090451000c03880c4001c001d0a03880000d40711503030a00072a20f18020841d6070354004500c0345890b454a00c081826002000076507003110026a6140f0f0f810042e50007921641010440c14071007840030700c01d48000750414106101c100c44050f411703000000c03a00039440d07000e00e01182d5a2481442030300740a001391805008285c90b84c1d482d000380c01d00020156103d44418000719071010600c1e01241c241a00854495500841440c0984002c1c1c14004002c00c50074800300c01041046441140c100d1000c2922403080650510844101d0716280c1e0505001d4003607803081c810180d403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 45045283 1250 45044033 45044039
    0x80102041215021204081c020409050708090f030a03020f070510050f010801020403020a03060519090c082a0105090604030c030602130608070c061a03100c0908030c070303050f04050d0b060411070206041e 89
    0x1f50b4406003008100d1401c0108080c14540d0000d4510080609420002d4001e4003040701e607401c1c00000c0b250710356840e180051303070b0303000301101c04595024584000b4000d001d40508243e00c643c0c10b400540c0180d09402400580ea43c0e500501803c0388510300c030003074201c0c0d04800208007040a40d803000b5070000c4581e82c85440c280c110401c60301220018003048a0154542400340f05c0950b00b000300302600914124104d00030068402c007040e22a4560724120304100c00001c9401c040c1d2a410260380c0110342c800d180000d0700e6201c1c90101c029410400070042c400d8131140d00041d00d07520404c01d00e80640180d031194290b02c0c050362a044050031130b64204d04010150060011404c0d00c0810080300002002c890009030340c02d902000404500d0301d032b444002d05034000c2c811104000000301d4194200d130786c5414013a59900321810f4040d280e01441d03010700c0d4420444085802440700d8003850740d104000450b03040120a51004ca1522203000f0103101a400c0031040c071060000c0c030b0900c01d0380c4d0302c1000e02450720307044559 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 45046533 1250 45045283 45045337
    0xc030f140c0604240605030a080304020303041a03160e090f060301110a11010501290705100504110108160c0f020604080109210e06030705030a0608010204121502120408 74
    0x403d580440d00c030981001210034a1259861480d2001c0303d030001801000d14103c0046d941e1a02c580c000b501018000011500b190b46c02c104413001400d140644003c40c0c10b5111800c1110b801c2116004c824494145400b1a03e40c81600c030320300106c000400c640d41c01c2d1140b07841e00849a41c01400c1e01c3d0190751b41d01c1c01c85c83c00f0b001c3c0b0340070304485843c5949640702d4120545038242501c6041e0b014240b42c5211400f0380c40010040442601c11580100030161901a14180f55103002000d451240709540307000b081c0414000c0d040c07040c50aa4030f0070380301d00800b41c41c0e82c4d01c400042c1c00c80740307481c0000035808030104001411040380d81c1500c900080145042c2619011003d003182c44002007180c43c1801001d00c0d550107090301800006281081c14043c1c005003c8001003000c03440010b0032841080030000003c1d070340b40343c1c95000340003800302c8138001c40d00e4035260741b0008400c2d442500183d0301c0a84042985c0018201c034003ca4414204141c0b0f503031000c0d1102c1e0303247c0d851504a0804c0d0640340d03441c01c0b400742e8110 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 45047783 1250 45046533 45046543
    0x60308030c0703030b040603030c08070c050901121a0106021b191412070b07080705011b0305090c09090c060304050a0f0b0106030b06190e0a030f060501080d0c030f140c 74
    0x8500701c2a020350307891592074090b00301d078010002c0601560a05004001007508400012681600b21030003517030307400152403d03600044441e00000d903c040003400205240f40414412441e841c0701d0600000c050b0003020102d011410700b40f044030010303070200950980c2601e210012541040b400342820300c1203d0301500034030590f0003582061420300b040400100340c03440e000f41076030001c01055001d03100c8582041003030300003071140305005461103a0009080d01045025880091440d034150b0103e0b098603107200004000c1c100079103042d08288190b00c0c2810340b0340741900c110340c02407001c10028420130140000f840401c1d04020700c29240ca02480d0135a40c042080e9008201b041c600c41d0314007003219070601002400711346a42a140740241414002c003070810340d080001c140c500ea03050402401d841172640000e6403c01540e007004040b8400c1c14415004c000745508418140c1d00404117403140e140018000f22100004d80c0c00c060009600c50500d04c100a009645e250801002c0402d15440d10305180d528500d04 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 45049033 1250 45047783 45047791
    0x70501050a050705061911040303080a05041401051f0602010605030a1506170703050d0903030507060b120f010b09010501080c0a080916060e03010f02040807091107020307080d0f0314150406030803 86
    0x24492600e00704002140a202c2d03103140e207c920072001e00301821510010b044203002460402417a5860000c07805200c0d00c0200003241c11f01001c000d0040345041980706403000c6d0482d001c1400311000d8800460340b18018042c038000d8880c0940200401105916101a007160380011040c020b50340d090302040d009402426401003440500092400c80e00e10300d0032510b080e106071404001c010380c1c0c28051001a60200450348015040b80000c503048a0410000c1c0e4100e000e441012110312658110581e00e0606410101c03000c2d108590001641c0e07030b60001507804071000c03101e5540c80b407410131540040034054803181d5000400d5004860b01d4005051a80c4000d0300c3c1d80d0800c5021544106043e58646424010000c990500c44d04c1542410b10340002da80c4d542103940101c03a0804c1d00d40d07196507500880642664035a40c0c008084540031a5030751501030711050b0181580c03000402ca410f0640146010b030088421096110180b01c1959aa5002511860441060b019800760f02c81c0e40c00008900d1407405140a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 45050283 1250 45049033 45049051
    0x100213030606060207080601090b01120b030f030d23130b07020c060304060618060f0902090310060b04060801140109050f0d0c15180803030402040203060604180c12020903070501050a05070506 84
    0x2071b040c0710500d407030000141d110b1100b550412070010301c80c1c2d074030091518502c10050400305450300848002410016086e031070421500c8003286ca051041c0c41600030040e05040c8440d050480c0303411000c1c110701c0c0e610403034840c13444000043c2070100090b503418071107511480a1055446410700440061440d500c10b0307c040c0c62680d1580c2c0d06001426845084d0b441c0982003000400855140208070350010400d03210300788034286d021404040507107007441020103000301040100485170300c5003001c3c00c554205e1f0007000005065440007190031440030002e50700904058591441c103d2a1408200340c1090301ca0455030403183d402c0340c09000400006401000d080c68007010120280f5803500240340300702c100c0c91000a41b650080030050688044200c07034006405903030269507a6260404540c0310300c43c42d40944000581c0030045458420148d01c074900740c00069940240f18050031000b20140c0c000c5407401e60341074001e540d0420496000e680140000a090f003130003030070007407182c4849003812070031940409 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 45051533 1250 45050283 45050293
    0x30a050f0105030a1a151c0b13150902060f13060e0a0501120c030908040603020304050c151206040b0301230a0905060a020708040e0126010209031002130306060602 72
    0x32502111611503024010940081034510319035154141c00600001d1016100c110f0b84020600d111407034103821700c848174082c020200745031001e03150800d9000c0d10b0fa81a15190401404180c60a41800000c0240d0b900142c00103440380d084100b48004101d411800c9900c58400c00290301001d0b1010003510b041c3d40c8c0d410300002c00a240c014040e00c80349060080b28810500d100c42405160f0704180d1581175810b1800c00041c8800030701c241a03004044020340546108404100058629410b40065218501c51802d6615440141052000030035003820050401c031010f1000c510340b62009500c0943c402d000600110344154504046400c441549281220201c0c80305070100308489103c4001c0e80042080030704120840300e40c0c4489850b040040c1c1764401441d000202001403002804c01d80f8082d00d4400c0707401000b965a010319124490074010910408906c0ca060500822818070903200c51820103000b8011007c00019001d009511415815000003804540400464101d1060401801d2260010700d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 45052783 1250 45051533 45051541
    0xd060603060219091d090f06040c03060b010206130213110409090c050603070503070c08190503070e0d050613030c060f020703120501031106030403120507020d090f08030a0c0f08030a05 81
    0x1001818020f0004414050104420856000b601156000b1600040085600f503111300c040d190402240d4600e005440c41104184401e01c0302c000d51000482c2d10034901000040304071380040e0780b0307444203c3d401f81c1c10480840004015041c01f02c0e4802417407188403c0020b40c151a00590200c1c0c2e00a0b410140c10503540d11a103400304100070030140090031040300c0d80b81c150f1607c1e1400502601c802400c010403c840c0f405004200001a0203441e200711400112221251100e00001e20542040300c0e04800190307400102215800c28200c000300c004c0c0c01201605da260750360401007110066140f0220b0401810031480e8010030002e00c50940d20500b846000750f51031845040c01461440200e040540749883c100040000803100c0f031100c01160b0059035000c0e240d0341d82d410244c0e88003040e440e03462900c6051504002d4159400705449080c0c10064650418094483c1c2c84004214105d01a082083d03104101c0102d02d24014a00a074155102e503400005014107591060300c82c2d00b090b0b42545032203464400b40 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 45054033 1250 45052783 45052807
    0x106060f0201140112080708040308070501050f0c070c0b0a050f0f0307020c090c0412140312060a060f0e0405130c0e06041a03060f150301060303020309030f01150b090d0606030602 79
    0x71181c400302e0829002010350400c0900781e10001545c2004080d03a01c0010b09400304070f0218150f0780290707004803506031155040d06115000e050f08890982c3c903100e20f000041c040410360030a0f5102d0030b4000c9800079415003040ca16810a034800e402c03002c117115061288284030094000100fa0409440310580c0d00c07810718030400b074a492a140f036454490744000d82000714000b0b018081e1001c9603480044070017081c3c0c0c03038140310f0b8019414500c0039100307000025501691812140003540588420344029054980d1210110350300300c17009030714000080040010124525181c1c1250703401004400c0703d40301c4100c0719603e1498a0905500410150250604200441c40c05100b422410f07a07080c2c40c418601c03820a00081d8032008014044080c0c122a00045410788209021f608031048000c1d0081200c103842b800d01954a81100708600d2183c8141e03c5800030700349060082281c010103801861803c0c6042261074040c135040b50f502980c000b548071041c0300100e4294000c070b00c02540940001a82c034001c106c0c030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 45055283 1250 45054033 45054041
    0xd0c060c050c030a0309020a03140a1106030618061f11070609050604030b04030e040507020c030c06040e040206030a090501060e0402040e010b0901050f060904020408031b010e0706030c050c0106060f0201 89
    0x3922050041c18024903451507004800c84401251601e00010210207910006103070b00e840350400340408c144080c1c00e442c00c1c07000068039401e0b5409015581218200ca03002c110a0344022181560031600000260720b14154201003030741c02501c010301111106001c0307515443e01204040c1900000b461401c0c882c10420001c1c400200902880c2c900041c0319414403020924520031848000c154940c034100103014980302d070780d00003a0705034004c000703102a0914050080d42e440b110288144640a943c42c601c4051401781b00700e8003150001d078498102c0c0c0c1d441c1d070200103281d04000c3c1620b10381078445c1d041d000020001c4c494003015100c070000420285c101801484112400300030103192507071404680c401c1c1c0f66101c0d811076045400c1106c03505080355160300400c4180c051001e200f030304503001050108000380c011001e03004d0100c640300841842c2c11200c103800d0030f0340d0103460181295082078009100e4a84a42c00c900010655414000d1506c0c004403c000e0848605520500c001740194017600180c6c2e5080c05 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 45056533 1250 45055283 45055301
    0x902090f07051c0f060312030b040212010e090a0506040507030c050603090615120609030403060509060c07030507030302070b070207060206070513050d030c020303030a0207020301050a1a040b120d0c06 88
    0x1220328081e1828000c058154400c3c00e100c01c0500d4100c641c40c0000420a0f000030050100f06031052244070b03940d03d88a10404100188140030a04003292001581024801d8818010644d04200c40c50391030a803000b8140400030b00301c80158011418002d01040040099500a6125000078003a030391450403e0841c0e0b00c0a9004948504030400500c90301030000141c05410149000b6800800340e12072001801c822040341305100a40144410801c00c403c0100c0030300304890003034209021b65900c1d200c401d41c031070764100d481c208921418031818010a02c114040d1480610a040040c981419900c40c400c0c0041d080b070724100180d1091906001c120fa050090f2034001145013005400c040f1416050409000d80d0300440f40640204840e00f000d15100d54681401190050196070f03583c1802d07409200a036000c00d07020b0380203600b4203010510f9071480740b00c0e03101c20802c0e0b2081310f0303d402c0520702040003a00c0c2c843c641a500852101707500500801c08d1141c151001c0e02030311020046d19141c40d014040d580c00c10 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 45057783 1250 45056533 45056551
    0x501031b050702010f02070801110c0f030901021002030604060906091b0318031103070b0c0703020c0f010806011206030c0902071a0c0304021002070801050c0405031009030917010f020d090209 84
    0x2600001a00d90081d040c0d500e00765090074903601c000c083c10300403464043d05503c00010303907003024681403146621070020040749841d4001e44501050284106a03070b88265140d0500603846140780400e0b4603d554003030360304000c0050010a4440d600c07120720301621400d802100b02d15540b5080444000d60044c00c1d02210029414140200b0501d146040812410308102806100440305a4400b42005008681032250b008405031590300300401e010115802110084015100f9500e40861503d231400783c1544683c07050f910302c0c000f50b8417074004682c00041c20182040c078a4480f400440080d4980f01c065025096150f00182c451745207050014006420612907100018110248020500280304880d8415010340b05400c01980d900012842d0048581c0090965407800302445164403c2038020001c440007107040703510205010070058111035440300e0003408a09840c80406c011303503100d22680091220640006618000100b490051b0390100c405004116960325903c0e0442c9800c0000580004200d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 45059033 1250 45057783 45057821
    0x20606010c05030a050a02010b060301090b10110304060302070302010b0315060103060e0606030103080c0a05010501030308040c090b01021b0301020418050f01080d08040303020d0b0d06050415020a1704080417030301050103 97
    0x5074540725142d04c1206040001c1000008042c64000d000750003680c039045003d44100d0741c960f51651000002d000c8810303094400d4a00c1821034800b180f1880d200d41c001d0b021a40614a82480c1070400e030020b61010004070195500d4865240709654280105c141c0d02e8a450a805241c0c80d000e000103007100e0b031640041040040c0c200078004580c5401d41500d040d20b0b40007030034030b0b910704140b030180349001300d82e00b0010255030a140021003050342c4240b4141c00b40344200c101041160711034002d40207440c982a10140142c1c0f040d5290b00081a58a422204400016000519280c0c0302e108001617010703920a41240e00b40c6400900084502c520544c600418605000c0c01d0041843d00000300400da011f030000d404c00da004213801410480c81c0e807013400c230003c0013010b91001c450741d4501000540801c9a0540f441c1848181c1101602400e008940326040c65503a00944082803528131005410054001d41c0d039590248408204141c0c40402050425007000c02141c0781e616102c00102595402806000f030300c615 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 45060283 1250 45059033 45059057
    0x108090115151814090f04350d0b0a0f0302130e0102041d07021005011a0f090901180b010c02010c1e0501020307030f0509030a080f090c03030a03060602060601 70
    0x710744603050036200c0c001e50007024480c9405003100c000000c00e81e00d110304084100d00161600809080b02920081a502103030700e03030b40e03c1c01c141c000d85e4000c40f00908640350030711a0f0720003804072034001c1010041d42e0140d4a4480c0d10103840c9034040e0410042c080700300d60307a41610100c910b08a580c0e04000c080c4840102101c2e411940070a11039526a4160b442e0107454042d070a050041c207406580103412070300c1544010446003100a0b10310281a1400707001341c000c505042403200003500425041e20800200050f4800c0d05003400c561030391288403441c1029500b0703c40d2508e50f41d0380c116000e0081580310078031030b041e0b26a4160601290480d148041c1407080c1c100b141c00060760090042a802038100301c00c02003041c0300f0110700d904800c00e080000c0840d41b0000c10000701e40c0d01a80b25504a600e06d1200300031607545c2d101983c0c0c0e82e02c901c1c042c9c800401e201100188a01740b041c028207074001603800949450354191804245140c002c503444c3c070080307a110203052104560410001d0b50202091038061070b1980 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 45061533 1250 45060283 45060311
    0x30717010b0304030509100e0d060203040201080f160c140a05030304150209100509030c0901030b100b0906030c0309070305060c030103030e010f0c0219170f15070806010e0f06070c0501080901 84
    0x417400c0310542c0103a00d45151101d0b01f40c0107480300303030a89030041d2041c400b20125161800080d80211400c9000c940700102040b40720150900c000e04c100c013030118400c0ca1450340c80c03050710a0410030070b084410903d40b018009102c04184080e0550a105800440c0c0317030301302460a82e034003a2150070784a09a52060145041d0343da1a43c42030483c01c40c103030400725510b11800c0c003c40e040075032815109070004503d40002041120714417115116000c40908524010745480310003030b0318400d240c60140d1190040c0007155149607040d00441e0001022012a006255240d40715820f200c4201ca404111400200c010400e050f0040d02151840100f440c00d0111059807200141008115001c0a0301030002c0728121000c24101d800c1c600e026001d4145250312813180019060341d2003040b080408440e00034406020000101102d01c94000c5980b40c4031082c007a07581d44011510703072401d11310490b88410b8140c2c0e000f40d9a00c444005000e04d078050f890560903107050400160580c0d030054258401c1d031b03140044050341c0c01 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 45062783 1250 45061533 45061537
    0x705010c0f0206012705070906021b030304030b060303070f050d0801050a0b070b040309050303070c081212010e060102030708030a020c0c19030303020f0d0c0804050c0a030b040201050a030f02030717010b03040305 93
    0xc0c08551410b2811030755450100c2d178500d5440c690412007480c01c0c00f80004982c101400340b00300c0e8215030854039001e5013108031001c68039104000582503407051000b0303c0000c04814180b94001d101070212803c1c00f425480d85400c0c690700382c0050f601c5400111004c54403030303842070826024003002e58045003450b140040c4200c144c4218800900791881520101e8100b61017080c2e400e0090000804481d284c01550a0402000302244a103000038498240e4841e132801e580e9068826000125001c51050f0b880e00500c5400305200400403030442c00100079020004190314061350144024010041e15040ba100c41c8918104090120510903003180b803001c4581d020741c4602c0016030b980b500c3c016840e0621101055680c4c010300000e041030178248006c202c142940150b0301486180140102e5112040f09014041c40c00c00c1400042c103070503040c00000e00075500030802069148524a0009050b80302c13120385d83c003241c0059070b076600003580b086c0c01c040804850b843e4103409016040500c1380b450400c0c3e9030240c803034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 45064033 1250 45062783 45062789
    0x50402090c09030703050106080c01030515060a0c0f080a080406050603010603050c10090e090604050d0804032a02040e0d0f03020324030f1615020307030c15020f040b0705010c0f020601 81
    0x81e020001e1440900d440520080e001958040004d00880f034407180d1154943d6101020640000d00c0c000019510b4140801000301c003040c007600c55443d0080002e404c4403c110004402d0f1403046410136034000040c100402001032007000d64803000c81e800c040c40d029043d01c0f009000f061007603060010500100d000402c040808080403141c400e0f542400030ba06407030b003003a140d2110f4023208112042000d09140400c15620031441070080d1070174a03600c03a40c26104030400742c4019000618564000340c507020200f03c88914101c9005002c8502c40403030b4009401d40e91302c9138426245402c0703030784014030554100000541090709410290b0440c50100245141e444000201d03030580d031b07282ea10400f8507403014001c41004102c4a001d40e01454070400c0382c035007680480e2040c100d045403e0070301301003075130320100c00c2e610000d134183d86404444602d616002c81c0c1500403000340a085030f080201d003041181e004002c10042502480c0c0700c0d10f0703d06c0c90600c142115840702030b40044c8680803000040c110782c00f0810380c4c15 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 45065283 1250 45064033 45064051
    0x303030c0512061c050105040602070302010e120f18040e0c040f060b030619030219061404030305220f0305160501050f1b031303030305040b0601021b01030e0c10090f0905040209 78
    0xd0071201d09244c03074880b01c0707000a40154078020500050080980082003a1400307a0002c0c4004200640c1d07480c4d881184071940b441000042c0100c9201f01800b100508164602c20082401442280d00040c100c8024507550641507200c1400409242407500074008003510050007004a45c0c6002c07000320361031100400700c1d88241c0e500c02e0602c10042c89400c294010315005000d40d0751904030900c0005030583e450160801181b004100030318500d0380841101c0640764140d40341424421400c0e813130200c07110010711960603c20814004078036440f00c1c0c4800d1004500813002098428100302c1c0050301c0352015001b40c1d040000400402c440f410131082200c050b0311001c003d903081141443d1099056006102800c50b69100c80e080020034503901d5007245003c6c40c0249600106e0ba241c00005a0380d44062009038496080c0d000c00030a0158041c2d804000e0000035401500c2510308080000f80000f1840607030b21000c00c03000081440141c180c1c00940b400b0b804480d004105c203060640001c2c1c1c4480004100d0340b4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 45066533 1250 45065283 45065299
    0x20703020d0501150b040311061c09030e03240105040501050f060304080d0513020906030c010f14040e040308010602100b0603010510120603030801150206060f1005040810060303030c051206 83
    0x3005004d52015000659000c845020300d620340e06003842c1980948402e641c400c1f07440410882504e1301c4011201002d40c6007090034030a07404c05000801610b9480001d905002c60308940c2d40c0c594405000da405150003030b400c0301b6200404818011501c02068201c40d01a80c64032005012684035120340c2c004200d011515913840f1340d103038608402c0d90305c540c03d5192802401e01e0113010192812821340d0030f99078807c507403440304ca949650501d030781c2e001306030206800502c00030107014140d070007500206050760540b025a4903054460090001c403205c195000c500140b40c09004204540c3d0501c400391000000c000c00f40a40c0b5001d03000190342e408180107461160390100da00c03040143c02800c198890075202c00c1c00340032440e540e040241c03000c007003482030000c4081c0300203907454814400324a0754407407007000b4007818240e0800e400344480c01803092880010b03c40c0c10000418032036020065a0021801020082a95825890018165075004c2c00e02001d1107001d01820342081072003158198000d030b041c5e407611b03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 45067783 1250 45066533 45066559
    0x10302030421030209040609090c0308090105090409080904060b0412080d09050f0a0b1e010b0304060902030319020724080a0f0e030301031b06080703020705010906140618010602070302 81
    0x40c2e514040c21108110300c1800181c5140720a4064001d080d054404407010001c169450140e035083e2009128000d00b22084444c0c18400980014040c1c05c00390810303d0301c20b040151003400f040c212014800c0a4809030400300d21414145054060b841c054580500668202072504001d0b403581154140010100880420304064030076280d44041072985e0014111058180002e007429204c00040c3d100381e41d0b803541c07a40001d680c821060003001044060030347c00a0315030301c0c103241c01d82150000b5004a40c441d40b50090130b400360703500b04040e116000040303800b4000c0c2141020060320300061039000143d12941300080d0030898500d20341a01d044641400e00441340c3d603c40418000a00d071004800c10b00500e03003100903407800c0000020f103069a00c9036042002c4110026402041c01169100b9800010041c40014048074440e0300a404520320800002c0b80ea007002c0c0d51402e00b1758130f40304c0c010100c1a501408004c0c803450f14104210180ea02d25040c0c15003541031403402516030300140006800380442c480c0e60 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 45069033 1250 45067783 45067793
    0x1e020102151906140a03080f0f0f13050d0b010608040c09020d06050102010e07030803160c05070e04020f0a0302010801050607170a052a0c21060c1b010603050a020103020304 76
    0x1000d8000350822066807500e48844800400241d0508200d6500c0c0350100100320488040300615500100411801d141842c683e1002e82603800301903014140c06041c042d400080124801600b6a6294102c00a486541343c0c084189c07500d0f0310742c1c0440d1044d102d9078107003400310300c910864a06640452500c0c2006550358248520480c10707036408051030340c1c0300044645a40220754407880c10f0f03176400d034024030402081400c503c0e5175075894000603000b9201000484d4505442d0030f000043c1d8030035030403d144150b40f02c0d1101c0b800e1a55a5000c10000d4543c101044110b14200c80300800b8240115a141c0d251800c50b00001c02e48801405003500030807001400e5828400e1500e41d203a079010751a103455030b0315540080c00030181c1c0c0100c1d0001c41c000c00300845100486ccc4211030350310400081600203140c08918201049010900e808854500100002c03107041600010310019100b41014228595500038980d21820700e40149201440c581c3d14091702840001d03800b0403a040000d809180c0903842c3c1d2514145 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 45070283 1250 45069033 45069043
    0x804060216170a0e030f100b01021204060807080612060f090c13091e0503031f050301050a1e230402060405120607080a111b03090319050c0a031e020102 67
    0x2000d005500341c1c0b035108103100e035072000810322140d00c0da03601110b1068440605a44031104140040d464101002203006460564860326070404148115040b511032001e9001d2558043d4200c0e0000072a0502003002c4103400c025a0794004005840c00201d041c0c01c941da450b140c07038003e0400101c000c40e040c003148400304200711120388110010a50f4459181c0b03c8242c000500710748400315000903172540158040156100c01500300c64108006e9403a554a0108141c108540500c40602000056034085550740b000d00c2109e10400d01aa80081c81c01c650742c0224100102005c0001e040d18141101110f05202690405540072a40070412085488901c0050424051508415000204440309a82c10f42001880a01501c1c164403014099119100c00d8000e84050000404622904000441412043c0c1f01c01001d00d01c55001681d04160460340003d04102c010429624000da01c030202d0401c1c05402c0c00b0801e00d01d01c04462400c81503146039201e811034001c51001d4041d44071540720660541e402407103 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 45071533 1250 45070283 45070327
    0xf021b010201111206100206090709051306060e15040b010c0b0406020904020a120c0e090408030601140a021b040606020a0b04060e12180904110d0c08060403020c0112020a08040602 79
    0x503e529401c014820b141e0503001101e80f14810010880700c000e01c14004903000740a4980c00c1c020340742c0c44e42403400040183c8030103080941440215400300000c500648542d9015049000c0f040003242007100d00d8803010188401e140c0d20440c6801d0354074440303a80203820b09001c03651022680d401039549081c060024000c120301641c00500000c0c07840403450f8050030840d81111002d00400c030614076600d0480c4d2a0980b01c00c51900001003c0200300072551140c00365030711000500d004d5410440000340c40440707070040c000f16805681b10740700c3e0710b540b03604030500b80083c11419501000004d00c1c2c188000d60710041d030503002d80103480b0440072505104243e08170045076007980e0110344881120350f05200c80360303208211010070600c112106080b81d1411582c6180555005070900c1308241d9098100000c5c2c5584c8034045403500ba41080000d9a04000d01030709108034001d4000c3c1c0480e00010b0009406110350051509240c0d10400990b44810380025143e07801a400c44d000503198040404c0007001003403441b07 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 45072783 1250 45071533 45071561
    0x180507030605040b0703050105030d0e0301021b0f0c0102031207140c030703080402130b01080c030a0209030a0b04051e030403030f0903020414010302030115030b04060b0a05150309010c0f021b010201 87
    0x4540401031107160b40120b07000d40e00c100505002c590b0303041001c45c1291020b0040c60343c1038012a48000c24a84200f480303100d850340003000181b0308228203099800340b810403003122840390091200c400d426501030050744a182001c0c0041c500d000940c060b4042441e4008102c04140000c00c405400404112010b45580e9104403088a640700310600300178168501c1102c080703200381040140e00798441c020b4010045007940c1a10b032808503803640441d42c03880b0f070401403070300440c280d0030701c0a2615030340d04200007915940280024903035801d2a00b082c0f07007031200e55111140e9440081d034000504900c004100c808803905480c01c3e03150842c0c041d030211465105544003030341c0039081c4107950361050500d041c0c2034120b9200328002c20000c001014100c2956003188005030001103107a00140110300c0f690401d00b80c205005003401d0002e03844100182000042010b00010000c0200c200807004070244614502d07203829041c090781d410303d800784c002d6a92040402c4506004404400b07060345034000d4010403034401c091 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 45074033 1250 45072783 45072793
    0x60f0c1306080901110403081206010e030304030f0b060301020412120201060e070807171302131d060a050f010b0706090c09050109020a0207050402090108010b03040302070305100e010e1204091805 86
    0x2640c00401d4602e06032102d2009520b00703c51020001340b8841100e040b42d50240c1054200a0781060078a00f9807001000703103050000d00c1c1c1d4a094540e40910050011714403450240503004074a050240b205100140407501aa104001c1408200001200501041c0c1d11075101c0c50f0412000000b01d0141c1506c0c0e000c074024002171414021400d0300301210f41d200346034030354071120001c25040404030071030000d440301c046c4011148841d00240c2802c403043c0d6a03815803204042484409810311900340c200320700f40c04030641c0103039081c0400c0458174000e41f80c102850036140c02e032a5061105000440c400e8001c0205130640e500f90200401100c800044020660688200b1566a5884049001e540700103107045c01801261000b155900e85842a41da890b001a5507884a9070700741f40a075100d9a101400179007d42c03082c00000800640108030784421480c1d1818040b0308441c903203014a007502c03e40707400c400481d000400500d1241914006030344c00c0700c205900214065240a03040b80400301c8643d40600310f8024 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 45075283 1250 45074033 45074039
    0x110901052214040c030302061b0a11031303060203071107030b0112060f0e160902040807030201030903090306020a05130905070f08100e0f0702060702030a09151b14010e030a02060f0c13 81
    0x4c44800d603084034081d40941d441c90765542590b103d40c0d61054064200c03400140806062a445181c0c0001a800d0080481e4640840000c96514100c05544101c640940000810800c0750b03004c100304c4418072102c001800e2041c2959540506054140510b450002c12102c40c0420701445400120b40491134040801103101c0d00000c40e603c80445178110342c10329064003c00502000544201d078203c9a03804082d00100d0b040da4011030260010a1041d0f0070407000340c02c0840070071024801050860f84544640390348905100d50080102c4050340301c01848c41c80c06040000c072a030444e0301107800c1c8000d490a100c081d07607042c15100c64803d55810a80c078116190041180038510b40d540d0038000c40690302264110717500d0340402c80c1c0d46e1140c4071001001418141d4104602001c0e00860308540000b410503010303511303c2100ca80f00b40139440d10b0130b4070741510b80700c02813840388000c2c8503500e0071501d06405145044040e100c040e41c0c40002404145400120400080d010072071041910001e1008201440c040383c1d03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 45076533 1250 45075283 45075293
    0xf090d080310050114090904140111040905010501090504180201230a0c0204060e040f0311012a030501050a06170c040b0c06070305060603041703101e0311090105221404 74
    0xe0b14022a4041a003a0031140400c1c1d0b00801600c60408008008030403076580c6580b01c1d508641d41d14103403d001d42d2182d00a2605001c103c1c041c00c06008000400142507240030001403070881180c0c001c60040d03181900152280c081203800303000680c0c0a090181c80c400d400701020032021b840188146465001095080030706a020b440c50700c88a00854060040720340b01c16000c0f06500c07080d94000c00c400c00307000143c07000900808420817144a4580006200c034418540003181038030003401c0d0302c50b03102c415050140090305032141ca070150000392124140a41440c4002d0f090301144420b59000e4582c0c080010710b414842011100074180c12280151120f2105661590b540b1b0300346d0315000071a0a0400240b80c80c101601541c2c42603420401e00c03a040b5015544140e06903001900304d814100d891200403401d0350b201929101502412001d4040903803450905000040b2150350b542d10400030f0303500400140e42e46c07030780c0a0342d020031409162004008410344035006100003c1d8100d05008901c0800c0b080c08 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 45077783 1250 45076533 45076561
    0x9140102030c04050a09110316050408060103080405010210110a03021305030a081b060601020c0616050f030a020709060b0a0f05040e0a02090108010501020312010e060307030204060306060f0b0c030f090d0803 91
    0x44e0040c0c80e01005580c441a8190030b6460840203280300501c24400203299400100c801d0301c0000300f50500900e069114103545003822026002079501ca00002804c00c030355681044800c204440742d002c108400020300f000c0e0043c0740f1840da4013504058002c9001044286111509001404010111043c42c00d480ca8152007540003c2440c880c2d0001403c0117561b0345d01c0205401d881400141c0c0503084c421003407401c2209a030420300d00c02c19044011a4003000041041004100c0c40000c40000c54030f807509454000d14000d00d5400802e04541050010080502c10400751001c201072801c0c5111808840c20f01101c042c0241c3d0b00019800b800d0b401400344106107a801464400000c0c0d0351511160780312801a070b52441124050404103d54500401458002e4030b405a08807034014251492140d80c4d400280130355003d030700282e07078095441d50100040e1001c8010b580007003251004d440e0910500f00340c0c0035103d005400c80b280200314000340b21113043e5140c00c0a0950710f47e01030f10041d141e05110300034444131 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 45079033 1250 45077783 45077789
    0x408130e0f07140c06060112060302040e010f0b030f031c11071a0a0603080904090302070b071103010c080103030c080a020a0c14010210150b0702040b030613030e09010605030a09140102030c04 84
    0x10483e1400310025582d085011200e0740c050503002041581c480d5001101c4c580700c0940c0f40b00c90325968510110043c3e94a01640b24030702c1c040300c0013040c4413030070b004900e003154003110755a44268401821800746040120680320701940c61006e00302c4e01395800f00610060f114440c40c120040200159020421500f0010703a0b12200d52400100d0b529a03583c410b40301112a0742c0400341141c40d050202c800c851902d1f40254124902c207106951020780d80d012040880d07040500201c4401c00550803d0301942024450041249082c0c03400c0380295165440240c244406054060300390b0f80300044c00e20089008201c150759540e4401048030700d484c0d5031039903003507042e8880c0c0c1c9803070060040b01e442c41c01038032050007007501040d00e015603050750034a0700e40c119107658020078040303030003988072041300b140c81d601840342520401011011680e100d0461030020440013081b400b5a00ca00b541d81c0040c001c0c20340c4074069a9001c3d0160400098007901410117003a000380e8400c1000c0706600020810034100e032808054000c07 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 45080283 1250 45079033 45079037
    0x20a060c060c0f05030115020f06070c0203010b030c06091002010905030d1407020606150c011d030c06010e0405210909010b0408010e120703030b0a080312010e0610080408130e0f07 79
    0xa50b40e0b40d0411648280c016801800081080c00140b0195801e2095424801c4407070044410000d8120009424800c1c101c1d60712000c5500965074005601b0b0a000300d204c145021800303080b070420f01300300191141c019450100c0c010b003c404542840341d4000d50102820541010403039031502c03444805003015007503e1241e42e90314641031002c200c05900010300c890103507200802c0b9241c88081200348103100d40006040e090035641384c3c64a00144601c8400c10700f4890314074000780d079032103084100951902e44103a100c0724060800d04c04000116002007864000c0b01800207031240b030b5101c84420071100e4056844180d5200b014000005580581000104100d41c0400700134801d104808e00400c0e10fa000c4481c02c2c0c2d4079214108500b07000644a03502501c8100380c020a4400c20755141e0b288103180d50407480c41d03911910a183d0040c02250403201100c1c0e484841255890030741410418002c00d2104083c000501e002da0110702d0780f01d82507070448440054023040d04003c0592820208842540302c0035200040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 45081533 1250 45080283 45080291
    0x3070f021002060601020601090f1401032307030c0e04060905010e1c05040506031b040f030b0403090e040f02102a0b010806071d030c04051603060e060d06050a0207020a060c06 77
    0x5000b40041406481200142c0250090340e03c3c2c285d1040240100e00d0111420700d07a62030000703940e60400c1300b85a01840c00344013800c0c01c0d505541d00d14900300041300c2c00002c55a0005400f08005130000d201c100540f800325216811584640c030b010300140c0100f0704024000e50800780d606410800000f0715869840c213901c43c0e440383d103100d50000d540034403442c0200c0d50004d030b0410001d09104009114010180280001b00d8a066030b250180c0e05414466001280c4080c2428188801d1603400418030010300840d0710840c141d030609642c1c502001c0311100c00240a1101821214000c6010740a50503251080c10103c07003181c08502001507601c0301d824001c4950140c0e002c00070601050004000d0f2054115442c2c80c013042d011080250403074170030a60000c1c0e042c815010460390603110381c01900c1c0070b4560080f1659124a0800707010301529540c0e044106049007600800585a541e900c4080c0c9250b088840004d0903228250501c0191040140203908010006000600154800070026805014160400c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 45082783 1250 45081533 45081559
    0x6020d060317030a1103010812090f1002030307020105060105031302040f060936030806120a0602040605030114010f02070b0a0e0d0b0f0a0603031403071106010902090307080c0603041103070803070f02 88
    0x4c4c1146c00280980d00c41507000346129481030510740c0091100ca000107140369580900c0b200060020320b0805901001600302005000c8025024001c940c0c20100900b00a401d610709803041414104505102a01c03c94070383c1c0103a08200d80607402400a441c40f62803d0002c1c43c04940d94040c40006018041e082001001884005e2500b640c480003000341d16564206582d15002d003045116080c1f40800d200e01d000d448000d000080c4103200900003402c2c4c60301c0c0c15403203624043d000f0015002c0c0c0c80d14241444a9031107460384981d4003180d490107569002c0e26007070301c415000b0400c64800c00700d82c603070781e801280142d00101841108038449102ea00b42c043e400c04035a40f0500181d05491940c07000401044201c26180384103141c40303002c0c56200066140c4051005000301b8002c0c1340000a03801100d219900040e02d080d03604090040d031014103440c1d4010100100340002041c0302e440010000303010b05860a020700c485580034405100102414000ca9031180213504181002483c00710040303104003c03004c024 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 45084033 1250 45082783 45082811
    0x5070f05090f010302091e0a060306060501020d080406020a0201292d010507020111061e060103200c0304170123010501021e010b0a08061f05060706020d060317030a 72
    0x105115011450020ba10b0384d1a503030030b00140034070281102c46001142d07104c1400e04520349010038401c03410b03c40c000c00c41b289141010022100780b03810150440d0882c80030070300c10b99048032040307030001e5108c03100603070368505250128010101107403d50a060300038203941e070303210302e4411041d4242c55040b5100070111031600e08040001c84116851019550030310491000ca60081014121050043c100302d400040d544048600f05902150a09a001c03841c0003c000021213012405030310101c01e080c200900141286000b5040113604031074410120000380041d4915811702c01d94004002ca000c4401803a401504814082c001c2c074408014110b01c207044041044c49081c800c3c034120741d41030b0090200300034124600780c84066040540076040d034850400c070840b0b450b040e1128005004100c06001c007802c0a1501c40002400145002800e41040b0004c1c00242d0b122001c1f40c40641d80598010781d80c4451001a402600466101600603400700201c00e044d260514019441150055400c2000260b56515 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 45085283 1250 45084033 45084049
    0xa09090507020f0d050d0b04090f05011a1305060a050306070809010c0c0308010b03040c030c080705150304051e0a0803151008010308041211040c180609050105030a050a1805070f05 79
    0x14003c025405480001c02c42d90080c00141000c215006011560001e0b18011506803030010340201c4418001c0d100381c0061210a101d580d420301e000300c1486145000c0d102c0080c03115055004003149990350381c00860f00e603a440c005031500801000e0183c904a2814103005070292100301c800c5050b079420080d440c980148203089071160140e0548601402e44d003032032107800d8181c10090040f136070250b911401201140000d44e00074000d1550200a040803802c020901900b800b45182010004509109000000c0c202003100c030030284540a01170490303166803000c1450812613100140401c04000180842440000c141d141030039401d4a4550606036442404c841c014402d01c0302030a070b080140014050302a140001c005d0182c0116244007450301c030f20b00010111000144050085403010034440c81e60850010200d0003441d07030303041a110141c0340000107011488000c000c00390041d1380f64009542440c0c580c1c080c000c0407400a000410840e00c615195644d80814012100141c40d40d500010742403a01502d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 45086533 1250 45085283 45085303
    0x507090e1006050d02070f05030921060103060207081c06061e140f220501080606040605070602030c0403050a03020703051b0a03060f110d090606090e1903030608030a0909050702 78
    0x45078605628264046400d5081001c01c010b409800f004a440802d54080d00c00e01c403c2c3c00740e000f450303640c0c039010104445607180a6030720042c09a81c21074a0707140100800ea8604407a00000c0240e666291441c3c1403e140c8280040c08451f900c07000117401740440554420341c1628840c2d142c0c504810f444144584010002500c0000050940c50b0451440c0301e405007e404c1000e100c9804c01d040c802c081d00440b4041400784a5945c06544100d020401c030740c1d0002c0e10b036810610a40740f141c5040e003080c03001030403481003100c09003010780c002002c1103846203488100d40003160401c081d50080340d43d81c0f41c000d403075028502c4155001d11070700710800140000340100440c10b8000608841840c0d24558904001c1c00f0114012220140c4d5004c280d60306d02e15a800400100d0760701640010100064a40320007183c030b00b0b810014240e8503141141c2c2102e0700010f03058006030f09461a01d0181d240d2494120040e01041d0401400c500001c19002d400342e0304110b04409907007a0302c0041c80a60703200c00341280d0318203a00c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 45087783 1250 45086533 45086551
    0x103051506091303052b3204080904020c03090f0103020405210f06250315050f0406050402160b01080604030e0d2d03110601050f060a030b03100507090e 67
    0xe001c80c00040c0300c503100c0420544281000c3d800d1200c6c0741240e0000100f01035041d20340383c0d41d10a00e1010040c07244200d500303000e000e05040703503007094006504d140d68032890607030386400249002180030302004105417108031400400c290740d51801154519107a4010388001409020004e0180c5003540c007c1c02680c06440d00a032210b0559201d8030103044244010000502450049194a00c80c1d96010f0280d20300caa00b02c1d880329030060444242d0441c01e10302d0704411034201840d2100301c1d854003820320000001c0f1030302101c19014030303a11600020010700c8140d21840e4081c5c40051815140144c007010104030900400032000305031703a18403150b915048100d40003400100d00f245100124640351681d910303910f0042010264400c15a58119100324140c51481e00e0500d401d0600d00406902003004010030385080e01070f24042d41f5040100d031a03840e140d01c21511401011503400c000b284030340e108210b21000102100c281c0c0d8034942001c00141000d03504900040d01000000c03410126a11419014949003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 45089033 1250 45087783 45087799
    0x4050a0b15091914180114131503061e1a0607140d051c0c0806040f09080304080403020405071b121b05010609060909020d020f0604030b0a050103051506 67
    0x1c109800d0b07444900803e501c0151404828500443c55000070042c1107440c0c1046960402e0303004001d0300a0a0400c49a80c4442e0307840144040c8104090200d10510155003424141c904002c11030040c1803817032580005d84242d000c0000034000c444d0021750082c1d034200100103095401842d00d0040d203600d80e2884055407000102010780d410540d0040034260b0180c650041d4070302540b40e0789802c01340f00c02003070000258007061100b0100704e00300d2443c00300c0700c01120030800d410320503a020301904401051540324aa07103905c0e1201552040d0484543c0c141d001e21038650320301d044d00c4d181209030020b0109038040d91400001905503801507048881045443d58040e103120115a1030040d4050022030401c108401d03580c0084551f2404160b4400092103007002050840c2802b030b031401140d10030340c09826542d0030508030f500541c403641800000c0ba42c041d02c03a0900e8007030785008202d0f1403060343e0008029061a608200f030720240c690081e070590740308805584000800d908803000c48041522119400703049 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 45090283 1250 45089033 45089059
    0x100c030c020f06070203030a091809020d020d05071a0301031406090615130608100b040c0c08070503040b0301121202120906091809070e090601080304031202030c0a08070204050a0b 79
    0x2c603085004038600c0c000c01d45460100c00c0c1d800b09041d500007102e00004a1200700d002e20030314910101408186118100030002c000940d0000740740c00103480c00180c01602c12181000034000140411000b404269001c042c40a00c01c90820074258000d02c01590604ac5d00c042604443d2800b050060054500c20300505072510b81808441d410784a000a40fa40502c070410800c1f070060007400340754000e000d428064207904113030b80340d82c0c0c2c20b45000d989014803803490303c910412459001210740301c1c019007003107400da100c50035482d00702d28500c565040000040d00200c00005da18076150700803d0300038496031400c0d28610310150180c0e90340701c0410100f2808403041c042442e05003420b9010b4031b441d250042000003103000810540202d0034040d2070000054000040c180010b01051462070741040d41c00380202482c3d03240a42a40c1c9074015408000c017a05e1a004022001038400c0040d56107030710740f040c103a6099850915081740c0075407114004a029070b081c900021608601842401811103001d448091a660 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 45091533 1250 45090283 45090289
    0x141623070b0d1e140f0601020d030b0102010605030a0506090d0e03060a0b010c0204090311070f0806070e0315011203120e120a030603060504080903010506150d09020a0b0c0606100c030c02 82
    0xc64141210710300c0e81c40076000c141c44034444140f00c0c20300924100103152000340b0007116018000421281201e4404024400142d80c0001d0308604d121986c0380c000f0b01a009040101d01410850f4442031f40b500c55440c120081c4030000c80c40c075016852800403103000840100c03041e40c20350750700b410141d41a00810300080502c04941c002c00e0340000305141a0804074515070020301100e11001081e000210b45201c120304103a410082540a04600c1403003007011440c18500c0303036030307018002d112100b0044105201041038604104480400c422550205010741c0c44440c56803031030b804904154001000211012120384180c800c1c5c9815404090140c550414011001580c42d800b0440c0282015510070b40000415958410240542e20852015949100401c201425940003400f0070b4402c680c01400400300300d0b00074045403085101707554089103001c1a0300001e8007015040c0e211010314580040d100b10458404140c1c2c501c609400c0b1081805424810b1044840e54240380e80100810384264029001d86 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 45092783 1250 45091533 45091537
    0x30f08070312020a080108070609050a1703040503060118060608070c020d03020c10030213090c1b0f0f0501020901030e070f0b03090703020a06020f071a0a030b01141623070b 76
    0x6009090240070640d0b0b00a128040760300425054002580c034a0051001440c10b000c80801050549400060b8500300400200c0310b095510030320340c0246212a01c0040ba103014010f840041c0070080649009603500e68110361810401030002110900d49100410914041d50b41c00b0b000c0e6500c0e680300d0500140d50f5080c042000c0c0002d000341c003507100d4400200e0b00b580c0e81061500d18003103c1c2d5800758880c52400b1402e00107270504e8000c00d51303650030b205520219541c809010544090401030500443c00f003818824080b08480d00302801e458012340354501400815001440b110390b0070380c0c1c20000840034141c400d445171014007800312094800e00b010006104000c01a40d0090602000e032800541d50342d001660065140c0c0c00a005030700035a15000c0c3c40c9100f400f5420080a5400a0380c610300c0c0303490b2807003085200760b0f0440070505540d0080350a03d41d02c5070b8082e1880d131090000d550355403441407012150020f0940c40469024088440048075207803114403007440010640000d1040c1c44c248025041d5075 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 45094033 1250 45092783 45092797
    0x60903060510090c0c0c08070501020a030507150507030204030209100302010e010f031104060314090d121109040603080d1a03060a0905030d020409061a12012634030f08 74
    0x1103102d00002060f801d00a00c1101800d00c1e5940329445d41d40503600e44482d982000b035102c0800d40d0043c880c10403007640c01140711490a6030511300f00f070340e0780890300d000300607507451a0103d0507440c40d1504004803190568003c000b5a40212080d040d280d440c29410199800780d8040280051198040c106165011307800c41082007226003404980e04000c1c04011712160007550090001984503200c0d003854500d01c0e91800d81007110140541407035000b149001d0508141c1381d0301c03179083d1903440082190300445035080d0340705002c0040c4240480c41d500d00f00419541c22001d140d0307401c00c0c900f4400d10f5051442a01824000310b002e0080d152591741d0b004030304002c043c8401c0075190350008001540701c110f0644001d1018000c00b5900141c00c0c0c0c2010441e822840760150050098241003050b10100040d484500381107814080820fa40080e0808141105240c81245038420744214035424070401000070f510101158001d070076a030f6607000c03400c4488042603d4403010b40611021200400030901074002030110f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 45095283 1250 45094033 45094051
    0x1c080415290a030b090d18060c080d0605040c030e0d020a0309090b0102010912230306031e07080109050c09101a03071e170703050c04050f1215010905010b040609030605 74
    0x8682d56a8841394281c1030100c0b00c1c03102c00d421000a24100c0c5401441000c280c02410b507090340000e060031000780c078040e258880a4180300001c140e48407168400c0d0400d40203441c010300280504a01d500014000d800c4940c2ca142e614001c1c40f00c141e410074400590003180b89d0b0195076110003145401550780c01000114001411035480d6603004011650300c005840701d281150341c2d106039007400c0307034a03d006001000c410003140701010014480e517903400103408041d0041e40407140841d000c5107100c0710710709001e56001d54030307550811002c407041c840c0100d0102107100003640e544055544418400c1d462021038000c408481c0241c3c0315490304841c1d000003565210302c090502c407190300010608032600f01e48a0707102d40c0000307200100c24503019580000040c1c106919050074070281c20039100d41c141c0e90182d4011a40140c0d4040d420030082e950b124140801d20f03080a040e42d180704101010401d10a409000e07101040e4241000043c0407104d80b0200e504982150366040d0256003941c5d85c1001409019100c00c0d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 45096533 1250 45095283 45095299
    0xd02090a03060507050c070f050d060509010902030706050d06141507050c1503090d020a020603060f0d0b0c0901090f050904061a0405070801090c05070c050907021c08041529 76
    0x42d805128280c0100c2098880702d4444103401c0e560b41c90304046404c441280003c40400b0001506e490307c4c080320841d80400c000c5081d40d503001c107950041803c241c000c1c0d454400c585001420540000041c8131449c3d1006007440b555031075603140c0001e0000103641c1904000565500047d80d2501c10190100c98424029103c2810160b00024800010000200c410480000078018403200c00c01ca500052000d50001c3c0090b40d205800103101c038040240302c2c500942c0700c1c40c9000159a56160f01d80703815940000c48015508101a4480702030300a40855400b1030040d50f80455081e078144528000c072400142840030f29613503550340c80c01604480701004107003001c0c8409a20255038502039648907400e03564030b941c407941c504030060341602ca48113407520511104009800101e1030451044055400c15100d24a5603190410222714140e11403240804244003044180c141c5648184080d02440c0260b5001072681100801c100032a4103421124203c40759000c0d11040c0000c451482000030301008240103 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 45097783 1250 45096533 45096539
    0x8090a0f03120906060509091f0b0301020d0e0309010305132f0612040312020423010c0c030c0311040621020102030d0609020306090901050c0a030509030904060608040309060f02030d02090a 83
    0x70080d10500071003201c1c641d407100000d1000342054101c0603844030a010060144c0800c09c1e00e2100d50944006000c120284c45c0c844036451908d00f50116102c00e48083d008002c1082c5410080d902c9401c90200313940040c0c00d01002c100e49804001c00f8075803da80151a002104200d0343c00c064030103040c140091803028540720088032950301c0c10040d0084440d80c9000a40ca403616103001401d0303003e0f088480c80c500f44107110034803540340c403115241c2043c1840d0341c13418806143c034401600d0920b0a082c3c000d00401890f80f02004003d0243c100c403040700d1003001d1848000f88110308000598986000c2ca201c2181140740c0c04690107001d2614115590060041c1c0e45000100308851007528025005566456000028002c0c24140004841d0b80001841c00801403800c012a8000c1d2500c124035100081580318004617038040414800c540c1c03034800003441000b01030b82d10030300600310392403c60301900031407075044d00028920b000d058600e134604516405189400c1c2c003280554020741080c46007d80056030700c0703804 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 45099033 1250 45097783 45097817
    0xd0e010b0604120b010611030708090301061e06090b03060d030c111504080c270a1b0c0b0907080c060c01090503040801020c120c070303080402030102070209040b090d08090a0f03 78
    0x1c00290405000070003c404103404c00465100d01a48081d00700516500c5170300005201100f52400d01d0f5000151580c0d800b0504002030141c10b050b08405242c440030003810032800d02d1120b4a804441e00c0343c654900d00741d501c46000704140021110f20303402440c0d80ca44800020310440807242c20130300c6032141c4128801c0d9070780400e0501c440903c0d10045258000b82c14405500c08200040d90600c3c121010100b407000c1202c8042c05101e5510741c9400318031b1800110303451940c96040310900700b506074103c1c111000c4492001304804004041036800704440302c0460031001f4080b4000b400e0b90240300081c040b118080082c49000e40c0241c1c51001195070b5a0000300000c1c40074802080109040000540c803244a07528060400144030103407080380400b0844070203030800106000c000c990705820324044540e01e5002207401f9100305800294085110b00811042000d00c0740914040c0c04540101c40d0580c201c0c0c03900303580b00da10a442100407540103c1c02c0c0781c0000c8001d034403480ca0368801d15041d120708521440c8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 45100283 1250 45099033 45099037
    0x316030203041a0705071a040312020a020a06110a110d0501050a050609061e13061212080901180b06040617030c01050a06060e040b04060503150105031002030702030d0e010b06 77
    0x124016000060304100b03200458a41e40b003507208625800d89000b215959044e560050b070b11411880c030010301009003c1101c81001e0750003c41c1c00483c21801c602c00010b000751211000d0208030710803203076020041546480707400c0e5941400a810028003000829403284003010500d080c2c2c01e6448113290f0240c1000403000c0c0141d0340101100340002c18103007030600400c842c1c1d01c1e0091403d405241d00d02e80760f24100c1880c1542141c0a6015103410b8142450b4a9001020300103a070003481b40180241c41401c00c001c0342490800c0d103030300f0a507651005526500701d51401d8400c0100200707004412411740f00040780400c1c0751141c012800400005546e59035082c0d03c561092051640001b41d003000c110242c0040c0c0c28060553300600f100703070400245042880140c58690311001c02d901031613880380d82421546813940f00d80f000c3c1000504481e80340414005a0b40ea00c0424051a80280103a42e4059039402e01c6000340e0380030b540c07503030007450801484107030368002080395006e1980e0303545d22941c0d40b050940320000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 45101533 1250 45100283 45100327
    0xf09230c0a0c05031b060a05010602010c0c0f0c030f081b0c010504090f06050910060f020c01080114012102070c0b120103200a150f090e0601110f010c050c12040501050d05040503 78
    0x7502d654034203441f5100c2220300590040080d6410100c1c800007103075114012044082d401a01802000c10a05041c010f031b008a4000501c0d07400c00030300d203c1c00c1c0070384140034124450721149030f40c0b4042c10b00460340d03448040045d0868040b880c00e1009000f01c5000b500304140340b41040c00000390090303075407000030001d0388162010800d9940c0840c0602c451584450448248012800241503c0703000c03000017004201c0c14450786480404082c600c405c0c2d40c0c802e10040e4580342241d00b10000f0180300244c200001d6122100440302201111070001d0340701201000e403124040740e260058010785c6540c4849410f02036460340e48414401c83c42411805981e2132a0000c090402c0d600060b034020b00c1a60f01a0050b41010f08030000e005400000700a8180004807007a44101c00386040c0d030800b0500c00b8002e01e0304104001c442c0700c41d420100700014165002000d481d818194108a507041e02a0146100c900c0c4a603020309400140200100ca081a1003600b044d03070400d05c158204c910380603100d0000c681d4000700c08 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 45102783 1250 45101533 45101587
    0x109021605100606021b030607030c120c0f0e01030915180602181503040b01090b06040503300406020601030f0305160b04050c011106040605100f09230c0a0c0503 71
    0x3e44188038565040000c03c100c24050400c4507030351340500c0b001940c0ca80008040608054480d03c41184140c40b44060748907800032a0420302c40716003034000141400c0781e0a4283d0000400c1c5080d001000c0d0701c24051003014503000741c0c0c801c60821400030303c5c00190a64030902c11594030b001c4503841c000384843c030050013854000500404003401c5d45080208400080020000310b400c18800e200214600b015241c0c110b0301c15003000144400c160011071403a0140e035101c00d6041c0180a4040d240c40c085104200301a48a005002c910070f2180c422001e942c040c90003440c006070b20070b4005000140050461902c0756000b410150b0800728951013010503940b403804219085207002c0c040c00100402080100399078a42400c001189003031181c141542c4210040c406071046881c7c07400710b22014054500346024000c0701104100e81515400388101030b01c5481c1c00500300c03e5640c05102620300b05c90141ca40070785480d00b03c0518100840c0d6080392107811201094815010820040d04120b03128030b04034550301104 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 45104033 1250 45102783 45102791
    0xc0d02010c12020903061513020a020601030615030f03050901090902030a0209010f02070605070b04021201020a02031306030c0f030203340201110304020d0213090209040308042009010902160510 85
    0x1856004004028682c01442c2441c0140096242030703401282540e406400b81d00000301c612888000602d040e0f000708450700d002403000910500c040d5000c03d10034140d82c0508014007401c421035460120002440c840a4142c0b80c614144c03000083c800d41c010400118140340028000361195403070b000702e034801e0318111070f06940014011441d5070491281001c8000a00207410b4551510700050402d210307645000b403c18000b580060119900c1845681c004104500215281c04210001075900d9011001a120350041c0d18000903559100303001d415621540c5658101c0445440e0f0310682c040d40016082c4021001448031164203500710004007142c2e0a0600c58254079030a403d6000380c01c5607283e0740040d2505004208010158603020b0b80e00c10303c607505507144070620048040d00e20082c98100c00c025130141c0710006210502d035100000c18000c0e0f001d84080011810100e034031703888043c2c0380301100350022020801000b031036150340d01400c0c0440e18a40c0b400c24500140d0b82e802d082c03c1415072402002951 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 45105283 1250 45104033 45104051
    0xc0c030d1d0105010e010b0c010207140d12020a02070506091807180b031501140d02040e10080604050c01030b040b090109150803070f02040506010c140a1e08041203050c0d0201 77
    0x20700007141120a1210000c015035418500c41425502c014080e031400e070600080c01c40d40c01e003402d50444400641001d03803a859080c400c00c0307079505c07a146005620f000401411241542404500c00c850b04d960a43c0c0061118901d0300301842040c1d0070201d0615800049008000c14090b101c141c124442d03116590b661700000204428500140030b0303508207680401090040002d02d0b8403050310800313820000d09019101ca82802010401846810300a0300300900104000030040c041c0c1e0b070300c140158114195050704d9900c495849541d41d00864016056600c514201c040a5004e64800490004040d00110703418211402040158800ba4408811141d4502d113072a0301383c100e05481d5010389401c030080c52400060740c0b41d0058400c0b003444064456680d40000c200b0a82c01001030040469020380812401320104207001c0d11042c43c0081910f01d4064844070307210544c48496000310031139000081ea03052901380151074020300c1e4440070071000c4c0301d0708100741e02450707004000840a40850b68004580402 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 45106533 1250 45105283 45105311
    0x303041406160207050630011401031e0e030d02070311010e060103051c1b2001020705010c1112150121030818070b0d020403020102060c0c03030c030c0c030d 69
    0x80020701040c2d2111580d0303070480d0903560119004040b5141207034003d0311070003450401d0000341e0b40062000d20b840704a40b071024203107010764034260403260034465041050803d50300541c180d890544061800c1e1b050ba404015041c5420350190615144440860741480c41052000080303034443c54082e0041400c0c8140641505001d02941e1200030710203015252035451650f80503940d10745084a004851140041c0000040c0701d410440d071a480c4010406250001c83d0034882403038160114204450203006808001c59400064588201c801c180d4525402052a0b2101c03844819590215130788891881c40214881c90100031500c61000400301c031032082e5145c41c3c0d40d2046851501260700758018088004004640c100d611594000d8050402c0d124142825070307050b08003902e0b078002d011501c6012655a4454081740e001d0015640b007a0210f48107629105d480d011540a118050200d50340100300068440c03036104040c6401005c1900100d0428507107054050854022824501d40c40303554800c0241d4180c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 45107783 1250 45106533 45106543
    0x3090a0602270d03020307020603040f060903050901020f01140c07170a030b091602030901030b18070906120b0f1207090906020706110a09210b0a050106111501030308060103060803030414 82
    0x10b0308640801c94160f07240d43c042d4403405101c074041d204010200000d410321200000c8480300c1a806001003040007030710302d40030384140c014001c100c2c014840c006407035075100c1d0148900c00f03480c0c1603482210910b9440c02940702cbd00b6403100da021116402c0224107100001d021001811070b07500945c501080c0031f030303140c02030249000c4000c0840d10042c3d45000900c003410340100071070380c0282c002e2030042030ba04255004180700b041c02c5201c1040e070313650308020400701d80d900081c000141d4030503540c0d40080440401109040e0b0b500e4500896114001c4101130754030b80b0b030040d43e100c1030310780781c005440303c0170740d03511401003200c0c032004081e18100c1d000035880d800c210442c0b1460411008071b40c0003504080c15002c0081910f1214001c0a00b000500307035001c1e281410641180090a60103004d0320054a0b000c0d009402400d07081c0b0612000c541c030085000e280e1407020446801e11005003000c8503013a1701e1034404450011000d002d990515546000c0841e107030300d0a00007544140c0c0500c100301c0d009a0080213041c545 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 45109033 1250 45107783 45107857
    0x203090c010c1a0a0605090a0c020106060311030a0c03060806130c060311030402040906020910090305060702120a0e060d0603200108090c06031b03010303020a0506010806010b0f03090a0602 83
    0x212a00c030040002c484100c1c140c00081c03154032007003e590b07441c00c09400800d5140c006c15403042940b802c00c20a8281900301c452200010f600a02c00c031980c584003030b016200342c0b2032049007014007070000400060240d805000700d003030700e8a0301241566507100c1c46418044242d42c0c0601503245105208140482501c00800511680ca4100156905c90092281c0c502028000234423031500c41c0b00c9101030003e0368040e0740c150340008001e940342500080d40900390b5000d80c841107903e8040e40c4005042140045941c5094024820115285c580c051104070ba094910b13040b40c0d6408042400890780c140c0d400d21510700650b100c0c40c00c2100581008622022a5140c80034035410000d5020030000b5001000c40c010010ba41c00b920810346036112501341030b10483e00e4a46050000c10040000024154006621800305010714103540c400d0b40c8030304072203459440c2401000400c640800180c0b1074031a0403001140d00680d51020b0342ea01c00d54a03a41c0070166400311541d40080302a2001c01e81120800e01e60050344 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 45110283 1250 45109033 45109037
    0x2100c050a1b060902031209030c04050105090402060307090e070c030e0405060a0603090c030b04050c120c3a050c040b0609030705101701090c0318022202040b030a0203090c01 77
    0x181031000100810030282016002c0c00603070380b60904000c20280d60040303194582e0090644142e1800000c41034980e0304a0356440d4820700c13500d40050158189445001d06a60015001d40e007180d03901c4d000d01043c0d90026004008202240e0781c000780e406400b101040c01480d03d6910501c0c41c18907402c0c02420049892081c621482c0341c481481255602d48040200700c6d01d140c180440c200c0d00c24105000350503050391004d03180e1f0b11504204010000d000c5948141038200b240c115004001c4418281d58507002c140700b854000b80540020881c1d9420300e8900941c480c811390340003030a1701a540c09001d8040700704c1c20850305e0360320040c3c50002c04e281c24003032401c40c0601900d08500304078546000981c1c944051040c03d0041d011000c204e4411889208100c1c290303030480018100a50751525410020286450b0510001c2d1a21036450914a4400e40c040005900180740180c0c4000700045542d509000440b841d008540c00c2000040e000700c028050741c03003503d102400603182c1c07808000244c18003d1192041d81 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 45111533 1250 45110283 45110287
    0x103050603030d0608010915140f09010f06080a020405010f030314031909030305010e0c130306052a0301030b250806011215030c05010908030301090507090306020f0315090601050d0f0f050702100c05 87
    0xc9d84c00d50340700c00e1903001d54104000d00c010303141d4070b51041c010640c4450406c070260400001048503180080c4c0c0d00b114038400e8404004981e6100300e00a510344190000800203441c0d0030350240e60032070300c001458102500e14034844c01c116252090008841c00280210042074866004001480da4485c81c00d81c04110705160701e103070400040120841e803400340401002d4581e42d40100301428540d500b40209020100000100b52480140a0b480390f00b09100480300c10244d800041d00031001c030840c00c1040c809200800301d1100c9480b600b42c0780b003500100142d04002c84d00502c1d80740b020b0725009111110300320b13420b41c4100c0b42c03e50511a4203694160020350600c5170a0004105240c0000212411070303c01c2c40c0300190945407108110b0762100350782d10260103540003040070160f550f4424029030041d5448806490000d141d607081c01907100007140c0380390214000b406084400350030341d0000b0107001c50220000500d00c50910480c011584280c4681006a001007044a1a80824880c0c5207050034a418014 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 45112783 1250 45111533 45111551
    0x40b01060e21010608030310031716060902030109150204061103120103031103120403031a01020c060306100e1e100801140d02040e070801020903070f030f020103050603030d0608010915 81
    0x201c0b8503490700c01d207980000501c1c9009105020a602c00c0e0080c110102c103a90340c03400d004400842040940c041a10240c0540340482030107001d4078102e55070350345051800c103500a080c0c0c40f40c07401406031314001d0b41c06540728414140061b811401c031603035503014010300584403410098014800c0380054203019aa601c02c01030b00d100c4141031560a411282c1c50302d00301300310034014010203045008410b81c0c6200344e502c10060004050305508103d100440c060300401049802c08012655001e41081298100741c00300003186c09410b0108143d4203040d1766060204003001c5241c0400c803100c041c4a0032180c6c14082c042011010724140181580f110302500d4880b04550405e034240480c0203000e20f14500c5083e04082803c1192503d40003410300310820010358580e1507541e0001408dc3d48117541c4144607008008020070644503180d0142d00b40c98100c03d84001440d1140e0041d0700902001c0c0c85141c1c14801807103042c26569260007031001400c400000030a8400143c82d24581121818800c1c00e010f6040c10500 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 45114033 1250 45112783 45112789
    0x130e0109060f0b0a120b09070b13090c02210a110a1505060a0803090d1403030a050414030a021002070f0f030e01030510061e052101050a08120415020102130e040b01060e 74
    0x1010107140c001c0040591ba8803100032503071403c43e107507014250030f000c04100320354588550440c41c41101c21440c0240000a043c0c84200d03155040289948504400a140000203017108405810140303951b00702010f10288103818640b03054201a400c0710320541045111043c0b2289004c6c4540000058815000d418103000010740c490040001d00c034040e903104a004001d0019441d80d2480d00c10750001543d0b40c9051801414000d0700003100d0a6031014182c00c00c0b09040301002003100c145006030741c0648024031209140f10040d5018000c240d410304580490403001c00c034242c0102409034880e03101c03141c0c5507402d0030000d13081d903900408a402d4103080301e108000075034000032030790040c80c992403001000410080055070580038002408a603403a40b1031903030801c20306902d42e030750584504654140c1841d948000c0160750712400c485c01c2c0c40403402030004100b21105a0204c0c40031758842e000242c05c00034144020494502c1c02e034802040030034100140000d200c2c2032605603000d00440e14208be818640d107004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 45115283 1250 45114033 45114059
    0xb0a0924050a061d060d0906050f1302010c0c090e030a0807020a0b040201030902130612030e040e0703020108091c0806040b01090b0406050c0304080105071701080604050c130e0109060f0b0a 83
    0x40c010620000c49155800b0760b0700856134201003030004003802d0f11030103c00c5050000b0100f00c3c1c003ca507220303d001e0110b042843d10f25000e034801d620111414160f45100c2c0d004440b091003040741125000c05601c00852048114041c4850301c14002005544410318402d00a2007140c0242c49002035400ca0365103240031030103401e141ca500c1502070178085140c03240307032012401c0802c4ca00407501400d8a407001c04200c1c558a0050544002c2c000d0307850380f64100d42901008200c40c0701c828904542c0e844480208015400307040704c564041199003e541d1001a15015141d6180442048800050800341040030500c2c0c10f21641400d0413083c64103d0030302d4200b0305043c62610440c09141e0502002046070072003070201300b08541c003611001c1e000707220504050748060030800794078414400e456410b100210f80c0c5840020151b2285802400604100703010406020410079103501e003c0b03032242c9650152850350800d020300582548514030018403581400c00c04c604031801c0e01c400504c41d0b9040c0500308140c0e2041a1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 45116533 1250 45115283 45115289
    0x4030503071b0203121306110601050103180609030804120201050f0a02030c04050604090207020109080609030a0507030c02030f1501080d05030606090321131719060b0a0924050a 78
    0x10210305240d035503500042e03401042d020096152103074912076203124520802403e08101e0b081e103002e00c07554460f10192211503080240404075070056004100562280d0040c11301d1302c403034104608140c184d90b100c440c107031034035050280c01240d000340c00e0004000140943d4111a12513100800c441c1c1042d9036149400c80d030160000315101d4012008c40d0b00180b4001c1141e0052030000c1c2100d584035500d402c00c101079081140e0980c042a50380e480000c0074440481c00b680b164035514080c51419510304426201074200007000d80070040243e02c5040107807030410550380d10305400001003d0b10190207501c0030712140140c104501c3c6410200720301000b503030460292500103104a40d140e1f04c801140d00444e103008105649044000c041011408603542c007600100801d81c039802e07150780e10365140d05c0010381c2c90800f001807050035400706100054000d18500c4600020744909070215030002ca56001600c400055000b058030300d40c0d00e030380d090585180d02507100c1300e07180c814590b0040140b4100010f10119600c0c4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 45117783 1250 45116533 45116537
    0xc0c090a060e010b04082b0c030e0a1d0c09100309060204050402071505090c030a030507060905150405120301030803040602070c0302090108010b0109080c030c01050307020102091509040c0207031e030201060308030f04030807080403050307 104
    0x41c44480426001d1134a212400001800110bd1141d940340c4001e5401c0040c05101d0006940001181a6039003850458005041c098118200d542c01f0803001c030000d008400d01a1034060342030001099560359400241195030268100c40c181c1488800800210380000d4010740103540070b800010040e80700402c0c1d1071f5029406062094075002d490800801034000c5a030010054000ca0888000440b91401030a00590160084440604001c40329002501c000e000c00b07400c2d80d0f024000030b40002d01640051004910607004401015030326070100d02d07595020b070401c1074240d44a81201165507805440f402c01410080c0c01000c010f81d802e40030075241d055607041e460402c00008001441c0d54000d40490b22402009416004002494114003100c2e400130443c0364462410500345080036480001c05d141504e420040682d042d800340c440c284400800b5210460555480740c03400004140c1580c0a54401c0c440d004650303200d890075190090400030010810014403400c0418480804ea220080d2039000f0740c14 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 45119033 1250 45117783 45117797
    0x9010b010309150c050906130602120a08060904060207020a060e01030f0501050d14190f0b010608240117040b0412090303081f17010c030b0301020c0c090a060e010b04082b 75
    0x1801013154241b01d818110b907009030000501d8843d041d000c00140e01290825400e4a80d41c001c04414910244146118180022004030206140d4504041d00c5170f040380c4a85c1006240401c15400300791381c0101544003101260100310510806e50705402018030703425204004000701e41c14500040d100716200f07040034011140540c0c2844030700c0c0381080310b8100403c4d0314900801e42581d40c030307223150030600041c422505c1c3c4007020000a00180696500b901540d0340c441385204241a130b0780e103100500d0350082e055040003840c500072040310118210322402940659440d45961415090003106850510002801c1144031001000031075400443c0c6074200202440b060301c0c1401c0d000307001c0c2455005800c4009481509500556088015400840c1e4080b554405000308500b1204141c202d010300c3c00c011a040c3c0050001c10b642d4a80b44a60320b80c03020380403000050041c0c58000f10b8210300400d80013a49189170004003480009d40c1040909400348400100f01a40a040130001310941c4c0314003030f054140445 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 45120283 1250 45119033 45119051
    0x40606050715090c0f0312050301120f06110f0315060702061815030c0304030210051306020d110f07030801080105100b03060d021018120c06050309010603080d0509010b01030915 78
    0x210350841c002181d040741a804039a500c4a80f0b003d010391580c403041f02c10000d10032100e09551300070400d4a04882c6144101450200561602d5000c0075801130f040b62056910b03840704150b99170704409001010104005582c6138500380e000815a203903250a0180700c1d04043c80700d030005954801c12038420f240517545c0ca17031041c281c0401040c0440c120307241c00e80764184080708000e003d600d9070000e140300324001d50031180c10881d4005e20000321380c0103840e8040ca8008a07a500340200d034064004240140d841d0800046042c500400e1240c0c58001c810110200e8000180f010f09065200030300c1c0c4d014151404c020003d40c1001c11200d200e10340984203204cc82e01001c030000d0030546d601202c2c40d071015000b0b0040805e50401c4c9030000c00322803071341c450010380c10036405010501c900d003480c4c03420107150b004c0c04d05101c01d0f06142090303d00d0382005010354400e40d01c800001c00001d99180160044401c00d00000c0761a040c0700d0003803402c1d82d62285c038041c10540741c8000c00001c1601c600e0700949050788000001483c4d41 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 45121533 1250 45120283 45120323
    0xa020106080102030a1406090f01120812100503060a050603030405010f0507020a14100201060503060f1810090309140a0902030c0906180a05011e081003050a11030105060406060507 79
    0x4001c0e800100a5440403007004800001c03a0002c18111220340b502c0c0d00280c2da130501b005145d540c10b40390040540c100000510103000440341c906902030207082054281000c0b01c031a101c420314110f0398940c6110449a0801c03040c00c08018094204402200c180858500354010a0340e9000343d1141e00e0400150a0780c1c10301680c002e400b29a006500070f030651445c1d54482080d0406000b14990030b901451a085410300d038180306101d64006d54400901030445503da0340305980d401d65010349070031050101c40065400124040144952019050002090002c06800d014110456580c08078440485030b84c0344070b0783d5594055030981030b1081600016100e446040c0c60003510f01420144c1350704040000f600b1020244150340008a00360125564405140c0301c9004580c440d5041100950b001581100200d0076409564030b5640312003c40c881d004003907540e45a1518100350386005039508070212112980c1c0d400d0030700a0940c031102c10b44050060a00d4114000c006200b419800b402040c101c40c2c2854000b1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 45122783 1250 45121533 45121541
    0x40b130314190e04020a0c020609030c030d02010c020d0e010e09090f0d0e04050c070305120a090f0605060102070b04080703030e1216080d080c0a0516020907020706320a0201 76
    0x7441d030010301c5440c2c1020b40c264070005810800040c001c2400702d40034201d10b00d418002c5410803006951075132000006070f400d014858000f003805070392500815100c00f010b03803010482c070840202c0d00e40c0041020407c0e444043e00706101140040c0810503160100324040e40c004501005462065404130745036a62951040d003446001c1c640b9940c58016030010381140e640c008401c228403207003200c003004541c44103541d14000b44905200100402c40034001c0b5140ea5880703c860b03503800f80c1c1c0c0c1000854400c21700d036540a43c5032003010044500964900502900e56170400166010301516080a4030306424101000c0e40c0b517050f031000800300907450800d406035480e40054014410180422903804007000110f200d1160b42c41d0203007440c0751044034031401e0710b07a00c0703424494040c8154160b210300c2e10b14540003c461070303841200000d403c000a19a007000503210400d000340300381c08960241c9826405c1c035500914034001e81425000720701a0f0398040700000014030441c840c8589407211566901c081000580c058 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 45124033 1250 45122783 45122807
    0x601120e060705070b2202060a02160932060f031606020d080a090305120403020a150b0f01030207151e050a0c0f18030602030c040b0301090905010c0206040b1303 71
    0x740290014400155000320150811500c00c020b4070b20b0a076599103010028081e0200390b41d000240c102000005820300030010900502148180d405448001c003081c1440380f074650190031140d54903031500e0f0800c9400401046290510b520701403c940407500c10081030200030740300d140b00d010001c1600c0b10940c1c007004901c50002c0c8222940600310340e84c3e0000ba40790703041125a02d01040c038607000101d8070101ea105001405c2d5164039202e04048840741381501a000003030007141544504142c0c480812090403001c18841c806190205d900f003654800d001c24055000e1000b41418014400880060100640c0801000c9a4440010090124a460309000241c00e9111444074500f80a00880380c0540e0060188100c1c0c07503c40c0841000754142c110350104801c40c0aa50983c3e4800c82440040d8098004580296580c5200c6050030f840c1c0890000d00d900c02ea00c10183c045e902c000c1402001802c0c0100340348090302e400034189900d01a1142d081041000381071000c0100064401400c00d0b004402640b01 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 45125283 1250 45124033 45124061
    0x60114160b01080105090105090a0b0a0c03020f0304050a030e181501031404030203070215120f070e040212090615060307051608030717010503030a02030d0504021c0305040609080601030b060112 85
    0x6650f919100c1c6402002d042d601c2080303d508060015200340d40004840c01940d5110004c0380242d0760340a00a001009000009400c02d82c00300882d819070109100618019402900500312041a51074064541c25041e03503103034082d0b030050188210400c03148500640c400380103444101c6401c100c4004030000d080300d104c2c1c0c118905024083c041415400805004210f20a88212986003a1400040300c0ea001e61080008100c8100c1c000403800c1c0c0010f10466041134060070801a855110000101a60080001060700c82c1440e4208824940d0400c0010f80001400c0e145490402810b00400da0740e1200800e03000c2803100c0020881c000c0700e040c3d2011403225800100003030700d905040d10000c002c01402e0b014002201070181c004034507031074040704a480c54403164005510b002200c000450151800070b005a07804607610304034440d032a901401007281944240d44065644c0c1c203080018011080741c0c4c1005565a01142c01030000400c0a80400e0300840c0909250880c0041400d046024101e20020f80031 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 45126533 1250 45125283 45125303
    0x60b0f060319050705030c090f1f170c090105070b091603060204060f0f0207090b011101050c040f080a030c06050612070e06040b04090f0219150c060c0806011416 71
    0x1c098102c2c440d07080c450032042901800b8580f12690222403901041d2014500fa0350108856a00d51a00e03890304210048007410400c0019900d11204444001d0303900894040b5411600900000318544919544060410b00e4182044401c0300003c08074002c120009164000c68030104100e04010084110304110f4400c0345024180c4030300c0d08201941080c450800440d070403d16034010b5034042c80049641980e154010140d580ca000400005070040854903030520181c10241d034041c0c1e0081c004d1034841c909110705107654070300d00003640400f801194060a42c94202d26090360000c0c0d8400041815a9040311000c510794803048009a034007155401c01c20707200d2040740b03c001100c2c440e0f40803040c8103841c111000c11840c00c2410902054032914030005105d262201c0d601c80040ca054150303003400e03081180410000a1f00c54600003101d000007500080450a442e26403002c0000e14022004401694940b1044070706020001800c403da040c842c4000c0d011001c29500707242c8414016152445401c652544 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 45127783 1250 45126533 45126541
    0xa021309050a0207020f0103050421030207140604020f1002060f151c060507030207170a0c022d0a0305030327010f091b05030a08031005040504050c0307080105070507060b0f0603 78
    0x4c0d030041074205c0c0258030108101400e50b0203841740030b118980011100b102040107403841510f0b0307182d081c1c41c030b01030503820f00c00003022034091a03e806c1d043d0200d000801c0c0c64103181c010044d0001094460601c10b000140380c0062141e0701148598001664641d40f083c1e5072502c4511524001d140458542c0122180b0600d5802502c0d48850301c5a0a000d10400c00558a900c40e044040c1d201384100030303051010b12042c400626210780000c00e2038542600e001b184d4410a580040ea104004c1e800011034408202c00c0000f440300014004039a07034404a40a01d1103904d1565880d489020040103480c2c04030700300e001361500070b41c04404171800038901d0008005941e504d005001c02080702240503903c0c0d07052402260005c01d42040c2c2801a1607005000701804003c960312040e1692004141041da48a070a800003600d40f240d0043c14082d42c41000640204070a9009251030000d0b95404904240c0c10442448401c58201080f10300f020381144010a0007620200030583d682580c0e408141c000307078000100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 45129033 1250 45127783 45127801
    0x3070314060f0901060b0405011107030c080303090606030307030c0b090a08040902042309060603040c0905040305040302030c010306060806010e01050c0f0105011e0501050a200f010203060406050301060b030a02130905 95
    0x510a030308444184030140c450444072405c9407010300424007400001c0205004c50360060a000013403210708002c036076165031280d6407441801015401a20300354408010300038041d0b400d2000907070210080c1c000750702740009914002c1100850b0000074202c28011004510a0041444000c01c0b664005441320f9440756200e140c40020b603c1752080250381c0b08e091302001a0b18102e400f03a10b4481c0c400414000c80c0d6240d1108008042d84054011541035015820015a00c00d040c082d0f07911030350003a01c5503a16603107140141341c10701c40c8440700181094239022080c408250007064070368100c1420b20b03000d000729130a80010781e0a8402c949240f13005200e2090400e502e0a015040907058954402800d40d0b488498088550004164010140440c5003403081d0700300715200c0d03401440d01c5440003c040701c034024056480390070000e102c200000e40b80d4000040080506090081900502c1c040c0d00810082d4503140100542e400082c0c960b00809400040301144a20020280c030003070101e0940c1044242042188 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 45130283 1250 45129033 45129043
    0x1305100c09060201060e0105060d0b0303210709060c020a0b090103110d09021906050a030c09090207110406080309090a0e1e06010e160509130f0f05010503070806090a060203040203070314 82
    0x450b4010f609042c8007240c044c6070156468100d402c090243d905105286001c403016004040002d90144410b004240016000c005c0105010302e070711440341d0603410000e200420200b1650448010f200302e0300000e20058031195011411140b981e8072040d03c413041d400040b0041e01c0584050800268007142080d4000015400486a01e1085502440e090f500d1460907a141d10320388a0140812000e0251180c0c080c06900305184440c0d4510340200250345841e04842241c02001c2d00356a490381b21280081c1350304051103030001a003140c200450414402400151900d14000c24031081c85803120b50160749205c04101c100c10800c0b01e03a81a151421b040306015545503424402c02211040704000704030300c5403283ea80c50104900d0390303030794074136080e00c00003400705807203006a81040d990359440b01c40110742c2040c07082151380341941c28003207419458501010300d0690b04d030b01720f2109508100705204541000042600e01140d124001585030b2750340b03000003401c2603541c1e0b002404011090100d456042c0c00171134 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 45131533 1250 45130283 45130289
    0x403050606040c0c03021506010c020901090e07091b050f04080601060f020c06190507030207090608070303090506090306011205070801020307081915091a0316030201081302091305100c09 82
    0x103010068048481001c13900c00354078140240150300501c00788145e502c1109583d42d40100c060405004501d07c030b81c0424290007007603000d800240d03039691000003035080902c136440040004030020300c00030b40d914803411004d41c84c2c10321550a000000a9070314044a650055078010000c41040e60721560303480ca800b5000c6080840750070014041c9a95aa080f807411100352050220400f20020b640031411906946551080c14143c040d880f41d00d40002d00e9011a019040181400340043d104a91452402420403203860b0400c0d0321440c0248000c00c090348002520504507140290400c03005032407818240c2c101074080d003000c1c103694000400c22482641000305103001d81d012480940b0041000748001c0100c41c4201d000d040003001c003100401040107580c004484800004003581940002c2c10b00003458200c540402900d102d200800410943d03800c42c1000c0e502030030115200607840030540c0001d80100005100480084000300b141c41405001c0108018003882e01c101013244041881c03003d05005000d01c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 45132783 1250 45131533 45131539
    0x160302131e0e06070f0c0b0402060c0a12090501020f0a080d0203130b0703060f080d090302010e1305010f151b15180606050306070c02031b01020a1703010e070e010c02120c04020403050606 82
    0x5c01a032003000d129a11500d4041d13001420020203442d25401c00c0f19550003a54125614414140303030300c02240c1414024500750100b0385519640500d00310001e414200c4810b04100950884500000858011070840741c440096074001a901e60325000b07204000c0b0402d5030090105102d2008102c91070b90035610140941da0b400ca03001106a5403041e28075501c4110040041c0051182c00e01040103500400703900e240050001c3c4186030348440e005020080724002d9000c882c401c1001c0700c1c2004002088400c909000d05a417030458800000c802c030704d01e0007041301e0310000d100304280f200710107902c83d06900c8800c2008800210180c13949160415001034655030292038881d00420300482e6504e402529801c01580d80680609071030f031388070170b08d4003107082c40c0364169415030046068100004440104800507520403a00403034a0b5414240146a01c680081c0040d0a020604c8650f66807681c0007580c1c242d00c60303812101c1407803003190304142c182014410b0a249411500214010080020101d000b620500d03040d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 45134033 1250 45132783 45132797
    0xc0608010f05030d08070302090301020f0405040b0105031330120b030d0219020303040905070c120212070b19020f0702091e061e0d0b0405160302131e0e0607 69
    0x1d101c44620700501d44a640d41c907030300148090715400e01942c0403503482109030400500b400c0c000c401190a992011001100101002409010602d8203225442c03440f4002c2c40c00074103516003020414010005030340040c08103080400100d010f1100404101c2070819000b4195810f08050840a000c0c85200f83d4440112810300c1c00072145c0d030500141800081c800c86d401842d1843c400e900201c0d030505d6001080e038050104000110f00c00b20240603c80c0108010354844035503007824240000030f40c6081c02c00300110740140d04002213140d6100300780c40081d500207040b070746580c644040340c5c00b0b50740b01c141805122600104202ea01410f5400140039042d0094032029099030318a07038103d103003010181d506241801180e001c21302900b40140d1076004a0907401e200040c015a060004e07440c0007a504040304e1071840300382007008000040c011480140e0358201511011811580051414940f01139503403000765850006540301264158043c800c68281e800c20426807050036041c64031120300710b0b4000082901 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 45135283 1250 45134033 45134039
    0x703060605030f0a0503040b18041418030c03030a0203070c050d0f0216151b05032d0a0210150e190507080403050904090f0b0f01081b01090e0c040308070c060801 71
    0x40032842404071503004000d1880c050408c1105005504540c0a0b09030301c0e0010301c903c044648940c41124841012283c0b1aa280d02e000400801041d246003030651081e001444001440c140000540b03030058180d000160b207941c0c440a045504e15810507001c0d2941c07003024020000e071034014402d1a8844459806c0e5007800e0405907001407c1c00c2e003485204d072984040480746803400d10031a806260f0514104900440c0b01103501c0d100c5ca150403002c202c0b03038100740c05150300a014070f142c0d01d04100f070108080c00d5030400e001c000b006034650031140100300107180c5800915640440e284a801c000d08005030f0504c441341070203001d00e0752898882c400d01c8240c1e0716290101700614001c08480f885135030305580342d030300e81050320090001800114200300d800b044051020000100b001184901c5031240360380a40d00703907150030f40b9645042034504610340085808103642c401d5903071048282c000d07264060945166516840d400c804d440c030850740094070413080461110204013508001004840c869030320600b243e42c03 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 45136533 1250 45135283 45135313
    0x7060f14160e0607020409080a0201060906051002030a0c02060c010e03071217042006040312080a060b090609061e03040c050f06070605070e040f090209100b0307110f070306060503 79
    0x1000504401c041210300024540c640b4100c1c00900102c0d02c003030808101c40c0040e68035003a00e030b00034251000150751100c0042c003154109100703940007404220b804142d88585800080e480b4858a417044d01001030400d0b80c00255103502084610f88400039000b0031100c4a0b15103029200c0e0400d440032101c0340344640250f501940b249a00310411008100d03880b0641d250f40d942c11048007156034045800c40b01050b900380f0b07103540e024050300c001e41c0902d07826111410440030061078003a000389038410140c5080c0c2e0074800c1621010503202003136010380b00603075070f9560341d00094141c0c02400e04a030100c5c0c1c0c240418034100c081c8000503500640c80f4120f91012030b601da82c02c00c02213130355644116800800030f010440105516403c8990090040e0070101c14010b000000316007520344860010320340d540c4600b60740046041020300d0503440500c071500c68031001d09007a410103252001400741410850990800ba2003241c1c10302403401c0d280042d41c1200c6600d80d076850400040e142c3c070311a01d48680900e00c00c0b288524 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 45137783 1250 45136533 45136561
    0xa09080604120804140613050f120301050d02040b0603040f12080705030a090f0506270604020a0302010305040314071203110a091511010e060f0702031801030203060607060f14 77
    0x150b07106803540c5480319885000c4034048070062080c0c0f40700300203818241120350207000460088040c43c3c00742d404001d050038001c0ca4074458801505481d8002c0e01c00902a030511816241590343c200e032020100300141c00001c010f000d0204c100b60344840000280800c20041c0d121400c03c507403040f81e00c0306489075a0360b016500e28000f100ca589c00b02e44100000342010b40298040b4100b01e1280024082d169190b448851900340111030001540c0c1104107140890703204103040d211260114801403803035140c207501160121009100007418161128007003000c140c019403403100c1c0c0964580030180c60303010b2410400d04c00e40340c02004801080ca03040443c8600d458100c1110041c0740203031200769841d450000702d900c07514600100d03501000108014001618428020304201484140c001c04507070410015000c0a0780c000380042c025980104120b880c02c005c0f402c4003144a010900340140c40e0f50b51403000c0b541c24455400010101ca15102191400301515070000030746245806204000350f6654441d03e09030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 45139033 1250 45137783 45137791
    0x403030507110a0803070303050708011a120411030307030c03031a0f0906041b02100b010807090b0309070b0a17071b0f06110c060106111612050106050a06050a090806 73
    0xda04000c00400300c1e2804142d007181403005466281d01c0d0f9943e141150464006140c1280060b4444051181c0c040d4012461400b40c64107401c401003406030402c001c94039110f00300c14070070b880c081d800c002000d00035200c1c01109001c0015003a41da80303061919000700003035012039040f00806e01c1d1100750500b865151840c08a50000034054120b60741820301003000452000f41300642c419101c411060440e200b5801070000543c907500200a9500c808003004240d402d4108900d040110000800c03004a0303024649908943c40744007155502d454029000381801c103140c00080000d04009500f4200c1035111181c103004068103c8411415242c11100326010070580c80e134516404c0030500904041020b121070310300060300c07a41c80001d03082d90101e0103c100d5007205101c6403c1340c02c0b000c010810720f81c0106600c0b901e810b216000d01001c4040d1000c2e0790802219010300c0c0702031544000c4078010401c0960221020f0030008010620840d03942400810b40d62080c002140000c955080005859600080326405 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 45140283 1250 45139033 45139037
    0x100512090606130f090203010f06050f030a020603040f030309120503041115181315030b0708091504020609090408040f050a08030702101202030f0402120a030e10120203190c05040303 80
    0x1a601c03a462180002d4201420100004c80d40c0c3c1c4040c10040e82c0922404120420011012460324904400c2005101d03581c0b8150f4000c0c0c11141000f8016520141165445680a81c0804003000c0c1d50500b24001e1240410043c028031420904160841d04039014610a91041ca025055444100c0610006a00c160040c400000c02800541a6500094003680da10103024003190300c1c00c0c5030700c01c40700195401c980f0b40e9040c0f4880b203c824014443e80009440c0d2081300742c14105194100004a01d650f011002400c40495640e90702080855664030203c4602e80c0000b00400c03424202410444030300e078818030034403c40a01c0980d0002c1c1e14104031241d1401c48013210040c5081c0003050f000e1003907145481119900300940014410b001c10b01d00c0c0b02941c000c201031003120644d4035192052000c55501d140c0d115180d03600a00841c80001da108116201c0408203554442d40d0f20864003040d9460303124110700301c00d07441c008001c1003241c460501440100020700d181c18031100c07800071f005440341c5c4924000900 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 45141533 1250 45140283 45140299
    0x20f10080720011104090606020d050304110d02030102070308060301060807080601090506191701061706130221010b0a0b1216090e040602071b06090e0c0405100512090606 75
    0x10500d00401110046000c0d00d80b5040d054403400700d4803400c60f250480501c807410707030114092200c518503204200c041d00c13013070000b4030302c100c1c0c0800003a102d8000104001c019414004811078280c40e05403180310310a9000c2e00a540359503191802514000088074041d0080d0b18124002490f9680007458400300c895407030207024140d091550f00d0f13005d800d0080c0095007001030540c04d1032510072a241820300602d00c1d522004044908007000a007940c4895008450f841d418501c15840f070040400c0c210340200054000740c5c800707d0184082541c161464011036003010f600b040203901845d06421043c021942110141c401c5601c030700728484180985541003200e1a0303118000303005122200110080107403941800741d1415698441d100c0f030154115021201c484e00400e0b00c1040000a2030340b14280d41501283c662110b0414800501c101154820945c400003c840440c280d15800c60896000e04005820091181880d103000f4150b540304140074000254044000344e41c0e0000450018042d900040c00b1035 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 45142783 1250 45141533 45141541
    0x70b0d020d1103040f0606050103060506091e1f0219050312092109030c03010c05030c070201050c0304080c030d05030105010f0c030513060f090e19020309070906080109020f1008 78
    0x54029001140301c44161076444201c00c1c2c1030000030010714070582c440c1d08100c0d00c14559192190584155030321060505042031014440d03641c94102f5118111810b0390b285881c06a6003e4031000043e921403502e40182d030440f5070030108141242e03241d8040303209400b103445185040c544060a84070001000c1c00580050010f10b2012100303030915504146032a080315080710040c0080d140135142000c0c4074452100000fa0810079080900c032070304003008118020000502c142c0d101030b000703100007844040d66440015041013168002d40a0780c0300200782c802100d0b180da1b281c038503407942e491030520720034421b00c80c400c1d0160b4041d1240701103a059800694651404951140c000c0d100040700003411030500c0002d00c804d448069088032010000c0255070341d810501d281180b400303010f48030560030000a80c54000100000a0201e1504080d1038626140051b540e580d4400198141061900800640f07400c4c1030001a4643c4150885008617008440c0e404c5031551503c10001c50611034080000811040c400003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 45143889 1106 45142783 45142807
    0x70303030b03030304120806060c010e01050f06090c0a080705160303140903121305070806090c0f0405070e090c130303120c1403041712070309050609070b 68
    0xf0f1071460a1980b2030041040005d1078607030074801d0383c40201780140c0b0303080110f824000c8a40000c0021809089400d40a08000c0d5100d02254500502190340d91a11101707aa000d1520741003810f02d02844540141c032114030040c0364005100051000c0120070891a24422541d07100340d400080481c1424074880081d0000342c10261603a00902c031021840f0001c003401500700d00c6000344601d00842a00d08145401c1041e004034915010303000501070105000a101d03035110b1000c54060000c0d0440e1020321040711801c4070180c000070b182c042c03401001d00b0304d102150742011180004070714041002c0f46190038a8141d40c011400200c0c05035030303604c11110300d210b504942c0035203181a07508800da50760b44158070f0201400162040c0455404a040c1c95030203012502c80c8060203206090925040038060020700c1c1c1400151303030341e0140c130000800e0144046182c0d07040d2a1130640a0381450318420b15 = true := by decide +kernel

theorem cover : BRFrame.Cov 44964033 45143889 := by
  have h0 := BRFrame.cov_init 44964033
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44964033 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 44964033 ≤ n) (h2 : n < 45143889) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
