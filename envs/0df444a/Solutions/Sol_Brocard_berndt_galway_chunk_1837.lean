-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1837
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:51:29.997028+00:00
-- url     : https://prove2.me/submissions/ac1f9581-f4be-4f81-ab25-9e3c4d30805d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 330215827 ≤ n < 330395683 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 330217077 1250 330215827 330215833
    0xf1d190507030c0e0a05060a0e071409030a050619020a0e13020d0f06080d05070b0105040b060c010c0512010608090601050114090409120315121509140604020109170601031112 77
    0x2d9a0b141e000c1130301c43c003180c1120026103031500207001450700107000c0090300e035918041e007010781d201e01b03040d0f030354106401c1c00800142c000d211594150b07904106075504980310340050716040c148941410500007020098040460040c084518079550040321080401c204a80c0301c0801e100130b500e144024450000340e2107242d03081210003100b121094015008a540741e504403030b039045c3d07106011103036070081031402048010b20800400c031918054101c2c0b20560760082200c2e21b010b4100390000c0c2120b42c00c00c50b45010403c08680602850080a20580103040c0c85c18100428070b0b10025403905c4000501616060000d0789075003010000900d400d03241c1000000c0d008101918aa0411085150000444c200028148510195001145208802160385070102090440c0701079542100c2001d1410141543c181d4440b860000700d402440c424801e90103035005802d050410b0b000040000b00756403c0007026111104403a0304c071000019005045941203a4040150561200058001ca04030700d458810f502c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 330218327 1250 330217077 330217079
    0x3171602040e0105060901080109030e0906030114010905041e05030a08090c1207090f0605060a030b01050f0723032104061d10060501020105130b04170301090f1d190507030c 76
    0x102c056101500440003224040401d0780d0b02c10310b450a8440004008001819100411b0300f10706040e01d03483e030004d00081c0049150110728400408092099001e070444c5c5444030240010b000080b410001d030880428144091100c0c1742c5c0320b407540ca224070240d250800c00c00600060199405110740c60300c400008065480e40c9501c60a0b455842901e4010045542d01c2e001c2802c0e03840d40c01303110b0ba104032100a0310003401c1c558425010b5000f011040d1a641c14808200048000c6222400092246521580c00400031a150007a910b40d8a09000031411440d44200044076214840724480010507040380c1880100f0b550303c0c41c0c110090805411808812002600342040c9100c000c901c10f141003100c500c0400c50159030b440128240c034400d8685859804003071103800003245d0500b0100e607001d03000c2d12a01c88a0070400e000c0701104e600992090032041d540c1d6810020088031405100190803a102d00c580380e2007894100d11352104150344801019500c00d41d096410003006111500c001d60304280f140d0061 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 330219577 1250 330218327 330218351
    0x406030c0602070e090a110108100f0f08010b04050103080409090c08030304050606270a0f0b0d030909140640090204050903030f0c2a030706050c040317160204 70
    0x783c0b654081d80070010844400102d07900000103001c4036041e0400d01280b4003241410041d1401807024201e08a4400c20320004510704d20720749000b2005100b4003000e1a48035241030601421100540401e511803410080104040780c2154103950945009030000103510328645400e4917080050f41c0302e81c0040c000801008140000400c50504c0f0740016505180d41c01803240800c215000303c102e0030340100246901282c0007100701e90007041155203095001600c1c0140c400020000f220500c803c030001400b103e41400b500c1c8850107010112032000e0891802400d0501c0003981a6007000210b0380310401903030300d02440ca004220021080020042c1103090042c18449070000345c4200c2005074080c0c0e00f030102045017a4000000c5901c41c00c8079411042c011b41300c6505500c4503a1000d0001c000e28030400903400c01c0d81040700c100c0315004c80820015135641c1d0344ca24150054038001403118800c101c0a101c00c00104940134a91280d240d200000c06543e0322040359940d5000c005031901075085443c0c86080d02c00d07 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 330220827 1250 330219577 330219583
    0x81018060f0e1503030703020d051606140402030f0c1e01020123040b0115020307020112060807060908070f06020307110109180905101e1e020a0f030b061303110406030c0602 76
    0x30310f280144403a91203c541c09041c1d0303038440c2c090024010785c00340311030301131140c828800b4240c20090030180c04405507058941000780c2d81000c00302141046544d00b130100f140340800072481043c640401038101e28000c40001000c1250482c020404084108000e5202c1e07032007907001e91919500703402d000416051a80d100050400200c4049488803500c2001068001103107081043e51130640d07005518002c2c0c10743c011a030040301b903c090a441921600c02042603a0705108076805080d45544404509140406d62803a2144545c4240070714410110203100490b400f0040301d4100d50069113000101e8843c4e00100c0700d00c3c2d0715900c002c4100401000d140d4081c4500c3e00401c0340140100c0407254104424800e0004071900814191148007210b5141d040008a036040030700c480f2a02100000c0003003074040c80000707a03401580d480001410144089014942500c0b0380c0e800c10038143ca0450509010b0544a031810000e8080502400c143e000950300c0ca42d01d40d001440503560094502041f65602c40300130356 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 330222077 1250 330220827 330220831
    0x7230f1902061b03040c06031503170a0905120d11031201150e030c01050d0e1e010506032103041104090c0e10140907050a0210061410081018060f0e 65
    0x8401060f8001d07100c0280c3d01c82903034042c0c0d4200c5010002240b070b1100c2a0010058590380c545c220706c0451000000c1030032031a0210301d0a509903440e55440460000041190321749400c414441c0b00f400c404440c000100040c0c06040b42e8250521501c14140170b0003141c914059800300a1b020020240003003a0f600c00c0704000080b11030b450300c9a9448203100e508150f211070000c11445c2c0080c500f40584103941d90b1540180e22110030101c00c2d1201002c1e110415800c2c4d90344092003000a030b4503002030105600b4104042600c5000224501d4141c2071101d58080862102030800390012514095008681c0c0c1c3e00d50144401c1540090501031013a0349070194000750200300c1d00244c8615032024000b40d0001004800701c5d070303401d0060200385159a40342c1b09480c26080081d64004601c1307201c44562030002a07200b020090701c00c0100452840008108101c0400c070001d080340b00b00704c1d42005000c0c130450b40c540360f0340a0320448102c50030709280540c10701e0f0042842d13600c410824480c148000900f407074035030803441c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 330223327 1250 330222077 330222091
    0x302100603150e010506011e05090307030605010e0108210a030e0d08100803070201121109090112020a060e030c010e1504030b1915060509041b080a0507230f190206 72
    0x71143c90200c1d1805070072190b04072141d0340480c200394030124541c61036501f01c600044050618a0900c0d0301c0001180c5070480c03e410854000f50303200014020b4141c0c4a40543c01030015100420395160149103900354002580c048a500302c4002c20100a0345009411000c1c19555450440f0001d40c0317100401416085d050b1792008071214480c00100d0072117800f00840ea1411740617152000c4035028017142c80000d00d0300800c100c0c04000240040000c40e40ca00c00000e0081000715081e2101d04a5030041006001c7d040c1d012a003446041c018821031038401240780e54a0101c24244045544503820106510220747c003528050000005004810404901580c5e0300a2407002075440c000030105441d007044405056402e1031200c0e0b40a000c100d070611031802802520f10140001c075a00703004140c400f42081e010000d03200403039000f400708500005103200303090748158103140c5407201072045007034401c03030f924035051401340389500240401007070441804a644101c01d6052440380b1200ca032200a4803034805072000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 330224577 1250 330223327 330223331
    0x1518050a06050a051302190b04060f021203010e0c03070201060b0a050a140405030a1211030d0605010e04110405010f11030a0c03021509060a0905100f0f0b19030f030210060315 77
    0x4680d0303c086604c0790303d2003030191703002c0b1003080c0d0b14035000c100107103005800d550303140918108045520940720029200412560700d80c1584500303015000b9081c1003842003c8412118203000400640c9030301e000180e0444160016250703030b5101c6131812405041c0c0e6030854402c9079000188880360301c1d170100051501c5042e650392015070320038080c2003074902e104910401c3d505a03c1150150003290720300383c0450144c0401d0274010050100440b00d40d00711707009017100c41c0d0034940e80c0c4810032541d6088116403218860031102013120101512048079035010724000c840c10441900c038801200c0b070003100c5550004034440210382d1999510b02c0024000299450100d0040c042c004034650707014803030110175000388100d5000d40020f03980e03028030f03000601c0321503826501440380004610100c0c9451141c0c0b125003114410116100184490704820348801c000064003c070004100c0c0804406c00b941c0309001c3c0ca60042070303c14a00010b090407464603900c49050030103c1e162110010401048100107400c8500e6800e003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 330225827 1250 330224577 330224581
    0x301140409050111131a0909061f050403060c02010902012307140109171315200c0f0109030203150a060b0d05091e0a0b09010e070612060b07030c1518050a0605 70
    0x6c050103010b0360350b0480200303841030010302c0c090325107030301c206900150240244000103a03a07103600c4184102d00d0907070710100310001007d10901129004460030300d0b2842c0028040c0e0a00b40e40001d005400c1000350300c0c0e505040d6405c243c80c0101e1101201c841d243c0004000080f0340c441c4003468002c1204074000c0710700c1000410f84458181c0c541050340c49401c1d4602c400e841c4946000c0b403d00c92901c0c100e50740c0080000c800215010700041c4401840c440f00e0303c500500080d4400350900046203035a03040700d41401108001000140c2c1c00164a10300c1c0c18141d1804c4540f900c58480071009030203650040d407030b140d0000c42e10468030303081940128030488002c4101e4880e20450a0002200c000c920204a0160880150200440c0c440d05030190003400e40c0703000140e604c60074103040b03003008416080000020340a00403561408035501403500036001a4088910340344c00d0741c0d400303440700b078103010001c01a4620398001c900d034100580c040d11241c151420072071462012840c01030344070400000c00715661441c1c840 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 330227077 1250 330225827 330225839
    0x209130b09040f0c170a061d030706020d0209180a050112020d030f020a15060305060606041512060e0103080d2306010c110a0f1802030c030114040905011113 69
    0x580c2018000c0030345810002d48594a49010807800c0c0c41d0144c0b0f420004140020b18420b8400c507414410040a0103800130030814900001520700c5200346218070f802ca02480c1524000210880f4201035110038016a204080c1007984d010380990050180d00680c003090210454251401442c8a41c25840c0304102c240c0c1c0701c0e104080756041200f00a0340160220b80c8503400039000702c0d02c031217548241e401145c10101480e5a10300ca9400c50b884941c400316100c4804108000040229542114040350154202810710f0b644404812850842030100910310b80c06c6c0b072158055a0286026002151941e0450340e1039003410182580070300c0c0c000c0000c40c40c1c0030716404450450000b05400d0104607120f007104e6124400112104001ea820540c0c989808854030b081c0b03603030341107400e000070401034a40c032001750f01c1e06410300c1003482480b49012009004200f001240d04c280011603040d0f801505c0b094584d4070f6054003040040ca1515402400c9629140e0f0f08203c6010302405004540b001112880c105a2250 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 330228327 1250 330227077 330227081
    0xd0c0b0a1e0e0d1104090809010e04020313020f1309032f06010b0310170601030201030b0303120f040c090e1b030109050a1104090b0a05070f080103021003110903010f020913 76
    0x1c010480000e4607584900c403940303801000b19100c640903043d81041d50b240c0000050460b0341206e070803140c080c00001c0c29001c1d5600291404103106045070114114a440141c6409a20303001c98000d05c19450074a95a1b040d13994004204402c2d040e561081100c80c140e1314020707000091071103010381c04805007918031200410082c1454048004135014100760391820301513002c00d400103001d0f050f1714548001d000c40d5101100305107501c54603050008024551445c00050100c40e5004903e0703009400801c41c1502d0300003950b111641010300c0c4c548411899580d4200360500000300d4118981d4981071245084845d8800640e01d011548558000340889801e103041600700e51759080001d00f0f46e00603001d4076001c00c0121400e450088000f61003c02c1c0e00340540d49180240400700c0324810625a030b48140a0300c1d55001c5030780c8142c50743d103007403010003941036400003000d00da6000b0320034041640b505403800c0803881c200150f5103050006030080c41003509500e4540080e4110140142c094206441c60881e114414 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 330229577 1250 330228327 330228377
    0x306060506090d062d060504050c0f1b10050f04020f091b070203030412080703030609180b10090617060a05160f0e0a030f05010506150a030b0d0c0b0a 66
    0x1400f885507010300e656080051320b00304e031040000c1540d045800303226454408001c40b16100160001038458201001c00080b9640a0400303420341c1c0d0203101444410f4103d800312001041c0000203654180407070441c0c40c1c54014401d100c80405410241800b0b0b10000224940d40594422100300301c880c40b5040c11b00150318011a07000c03140300700310820844d0840102d0000c001580c0040c1c203403481e0984032440300c00420b40c00f2a00301e484140000d252428140e1512641d8042c1089640500610201d24000700455081034000741001c8011408140d482d0b41e071003a071800500c1401424001c81c0d580b0020346005002e400c00d69459401400c000540c01c40742e502c1140c0c4074811003c1100c070b0b412032620084a00244400c110401d00640b940f81310303501d41d60502c010004520402d0800007601d01d6241007425280c0140006000d2004055040245448001540c2c40b104203464000340c010030020000d00108014070300a0a04205884040751100040c002000e00c20000e4031250000714450420a84031009 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 330230827 1250 330229577 330229579
    0xc0201050301061412090f0d090315050c090316140105040509010b40060309020f061309020706020901020c12030403020108100b031e01080706120b0117040c030606050609 75
    0x1040006004250142c00f00e26031348001c001c021420141030700810007035110241e5842803586e00111441c40092000c00c5010725040c0c0c2881c1000b401469641e46891039003040e448422007588403c0022100e0a50318240d894000b002000c03640052032030814151803d2550284031480c414043d8480c07081c0d4028800c4404540d40070317007428202d0f0b103806810701581e000038024580084251a15208000d0290280c06204c01403110300755031884140303490750703078580c490b407102c014142084800f40240e602c105011510180566000307503101150a100c52004d0215000080d40a101044000a000d81c40e03018200301442038003100c0b504030301c8808005002815140044450348100000d200651260302d0094011814036030280b10107842d034040c075405420860b500c03160010250400c1d40e840702008109401061150090700400782014001804c030b0007800850100c05445014090b25a4450b4804400b46d46070401d800c1100d007040e20305503901d8046d910007030b1110f500b0044045058031300b05003100d18000c4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 330232077 1250 330230827 330230837
    0x60b09030c090604091203140a0c0e09041e03020c040e150103080a0c061b1d03070b2d1b01020a08070f0c08160c081b120c040204090c0f0c0201 63
    0x7080000c001c55480c00401c070540003604c5103852000a000c201480703140d010191000300d200c03000400051006a00241101e0360141088034810300710390051071409281c10181c420720a603541e107041103120090fa40c1c0d42800d40000c0c1d003207000140b540c0890480c100001c03c032002e00544401e048501e035079002110003003000002c0d9100420002d2181402888a0002410700ca03c20124035250381c0115000c15128030340040a1007000152941e004007000c401c084441c244a0120070b800c2c0110b90342d1980d40c040c1f034405110008411070f2080b003012000c400042c2002d05110981014080143d8503000101074194611420400341c1c00c0d8101070080e0f400004941d9100c424a598040080796205000003d65003800340c48072203034000c16000d100130003084841da1103c44580d071917482e11946d0b45015900080c110340000741880c08586c5000c44041c080d040445d005034151205428190030301c00916469984a440000c0024450f4010340024405007641d03102d86420080758001600d086400d8031001740058 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 330233327 1250 330232077 330232093
    0x20408191707110303120603060a1406010f02120a0915030603080906090f0a0303020f0d032c070b04090c0f051608031305012901021203070e0112020a1101060b0903 72
    0x8a00368040e2500d940140d0900710f050104402090440e40b1940340141c288410340108070b00c034203042098603049600600700704801c44201104002912014001c107040048455010203564801c04c01c11800e010080f0132660384800d00d89000d044080a031060100b014035452a1090a5020f4801e50040f01c2c1c000982c0e0307162900000400600707a100c40c400c40d600c0710b4072240c5904145c445003403020240d4440e030010442245806101071038843c031140044100350a00059046100408082d051060100c2c0c42c0003000c422440380f07050a083ca01d4103c2001648007250011300814590083d14994059031180c0240bd01e502600b11158418081101c4581c20340b000100f0006046100440d4481038130301c1e19001c4800b250381c0c0d6a017980c006010305040310f055003202001c00c00c64070648648995090004000c20550448101c04500004020100b8082401070820070359000d0f1280c001040c1903500c0441d0390396541d00002d03002200c0500c2c03c00c013135860440041a21014901110711040c0010000d18180c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 330234577 1250 330233327 330233363
    0x20d030c03020706020c07090b0f0a14030a0b090d0801090501050f0d05070b0a17010602010204052d062206080702031606090b0f0403080a181407050a0902040819 71
    0x10300006006541010307820030441c000300e4050302c040d050900c14040907150b07251a0102e000d083d030310b020301482d05c952415012290955a000361403000c0b41ca45401c45801c3c0d600d4200060308000d92581d0143c4062a41020084400c40c0801e62020b502c0882d101c1041036600c42c048041292404d0095907000140c641c0540680d00d094001003034881c0c42001211040c54840c024007499030085207076400030400d0b0038140074103030300f03071642040c00b40907544001c505061410000170320503144c40c0c42c0240b0600598403400070400d400800100107243c00b401617a80d034456403402000344880d800c01002c50494440300032540340d1156800c240100103550085060403803c1d01d01c5007140c400150200e41d1030b50f41c1c2c0d00d18000285c00d1b0500e1031045440014802c0c0614150070701a0500b20020081d08515141140600b00300a441c0350400410745c0190340c01c2044585828010302e00900c81d003103690b000785200300004440c080c0e42c000308107544046003560001043e01840b40044203403003100801414410381e8101c40d0b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 330235827 1250 330234577 330234581
    0x20d0807090506072d020a05040507020a150605100809010c020d020706050c0106050306151801030f06090f050a0602030109060506120703150909030e18090c090c07023607020d03 78
    0x101c42d005d1402401c00340904945030072140090b06900e00b40803800d40c050f00039071401d012101c00500003a10144200d00e0000303c029281e00500c82d00811000950415030111159540312802406010b0013040802251000241040b074045556041d00d6003020303440c1c0410713813000c01da42003400c0c2c4940041030581c1c1004400d80f240d40100c04803003510340d0380e0340300014039507410000907001c0d109440b1100310010802060200c2031403000078501128451200420001d805101d442c034000f6004000002c84503d5441c1000d1040c11014000e0324920075200340406002003a80151f04a40f8445010000c1c1c2c0da07034030148444c0c1d000b007443ca50004031625000030304081c040d400805524961451407482c81c1d84a01080d801c84603007070000e40008100da541101507080540c2142c500c80745004105d40f0501d4a40d010780d42e07440900c0680e5009818a1300030940d000c01c400b041e207110550003040a80c2c030200c0c442804e500200703290412064101118007030751036148007118050240c0030980c09003079004020074041d00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 330237077 1250 330235827 330235837
    0x40b030c091504150e0907080d0c08070b070e0f041e0c0207080708070303080a0905030a030903120609020d0c0f050a08040c090903110c0411040e06131b020d0807090506 74
    0xb801c10240068041c40c0d03880c1c0c8192000c0d041c520010550340c60515001c0440b14400600d6111075500555092000d0a00011031400101c802e00c1c0c01c503414241854014114060281c00421410602c018840b149800c6440c2800c107850541e040c0101410810402c826201051140a800c8810601b1785442112541200c0c840340e01d2801200c805682c5d6541991512100d5030020a040d00320850901c1015031044004d43c101002c8401480341c00407030303144c0c0350f16449400e20840034180d80f20010300c1018028161000d4201c80c41c0410030403203030784110741c1d0060340c458918086610f02d0403004070000340c01110000019600c0307075503290829014078801d45020340c0242058584c0041d03410005440c10a034002c2c207406501c02c0d91524a59454890054642410090789512950070016541c132401e4244083e20121a51001e040d40356484d0034021a40c1c0c4100d60038204026030409085c4848000c0c11000b00c01401e040d5030855034800d24a00c4101c510f240c5c02e903000340000d449501704210b0f515098010b40 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 330238327 1250 330237077 330237091
    0x30c060a0f08092e0606020703030f1d1c05070801060b0306090c0904050703090219080d03110702040204030c030c0e060310020a200d0e04090b06010c080c0129040b030c09 75
    0x380340d8030031138100d11600074007000100d40f409189031154040300c100340580c00050106000070909142140c0e4003a000a060b001d00c40c042003a0b0382d00b0799140c4061140f4819540305c02900c129040103a0081c1921040c1c03d846042d42c0c20b126810000400b84414402e01c0c0484102401d51415500c41d031303003009120203004d00b4503034480f03005100d0400e80e0380c0c8601c1128024074068070300054001d07862050280e81f22980c0c49140f148110301d1010080841c0c00f05880000c0c1c551b030f00e40003c5519100310410994040d0310400f07500544040760100030080310424610984c1d00562003412242c0e0746898040d5900b204680303136034064200e40103c140d244a550050030840c2d080c2d04000c62420b41d40c003070103240540381d00b821000d264007450040149a030000099610389400745d81c02c0c42409000d48424a2a400142415040100e043d074a40240304c07a040c142c44020110310000e20543c0e9103650030480c14130a00004200b4124000d484030340a00e0148030b0404240400382c080c080f146c0d02035040000c840c200800f09 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 330239577 1250 330238327 330238333
    0xc011505060301032406060e09060409030c0803090a0f15050c0309070303030b0a0b0c010c1b0201050403020d170c0303060f0f0d060c030f0c0c1709010215100e1302030c060a0f0809 79
    0x908401e600e40d0040c44050807ea03503a0b444094a080d0410000080c050201f50045262030b8000d004254481a14040e042d00f1076002d50740ca44640c0c0c52207252004404001d8a1000c0e917034002c41c10401201141c5500c0c1400040500054440010060702c1d4070041da00b420b05a40302480c2000040d010b0b03004004294401805800a02e54441c028000d0343d00192071000540d555550007007000c0d4010900000c550b41180003001d0080696001070140e204500010f446024562012005c0061301c80e9419145011203e00c603480c0e0700c050100d5543c0b500243c0d8468481e18285d14040c2e660b040210041040003001040c164882d030944d1a010014980d0298202c10503489000c0c03030884000780e0280540c4c9484d1944c0e80a603002c224100444210001d5040c440062000c2283c21180c0e070340041c000001184c0b00c400244e550301c98802d1110440c400354803241400401004111402e00e50010620702c850080d019206a01d1628040050350710550f2242d4002c02d25008214000501c104513960f03200c2501011 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 330240827 1250 330239577 330239633
    0xc0501062c01080d0c1407150206010806060f0108010b0903010b12030a0e0d020a0314011b030617060c0307030b01090504050a0c1707020c091e0403050c01150506030103 74
    0x140d4070481080380308045202010200c581440c55880c5005005060003400b50079464124400107212094403080034056005071007189a00b00030500c084030003811400c00285c47d807483c0141c040d403690000d22907103210340515000242c880c00d0103441c103c140c0d041696042d550307030309100300007030a5000a41c40c11b40541d81e8021071080742e212560103000746d21510000f141c80d140210002801c0c100107210060080400001e17080040e110096044280c0b80d0000920b031400914522070740c0100f840c1a04284203d031410f181c10036094040c1d00c10000e0741c1d8071040c029020021a15070650310034003a24a0120306c1010800101b5440c42548a001c90613014500021950b41c0c0d100007605540d130035540e45d5200c2d540c41040d24a4150402c0c0e5020200a24084a218500d03007240065100c4101800c854000d03060803001030b8020f40031804200703c810008030710b00010300385400c004040c2c1e0810030640c0115844c000d808503000c0320301003000c01160f4008158501c0c5030b003150380c2c00040310458101c50301c43c0036000c41 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 330242077 1250 330240827 330240839
    0x3060f010c033606090b0f1c020f040302010e0f2d060415110a030c0b071e0c031101140105060c030f0c0109060b0103051909020a0b0d090515160c050106 67
    0x140e02c0507903c1c00719280d080c0c11400c9501d03100080e02e500034801e02c003031002e04101c1440e0280030384012802110145440b0341c0c0c00d0101800907400129403246680c400150000050890710141055a000b80c1c3c4481030103140304140b100d000c0c20512000da000000101c01003510f0007800d4425403070030500d40760f003941d9801d060100f00aa0002e4000c0d16180c0c2c03403080f4003c030081c3e000c0c820100c01c010a10041c0001016514080c0540c040020040c10002a00000911480c09510202040c1d440d66008070b0390918000e80040c8071050f008030403800030b421060345c810007140c1401054140c4400045010059180000b0413010b81d0020b440144280000d10803560405040000b03410000200400071648404070f103811004c50b0010304040d4140342c5000305004001034011200024006410070015603817003940002181000305620408890b903001603080c1001a007600034490760351040040711014504502c59501c14441150781c500c1142040030420790461240018610150050340000b481d20740b030340 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 330243327 1250 330242077 330242117
    0xc09030b0f090304120c031209050108010e25030504020901050438040504030c05250504092303040603180b060d1a0c070b1005030c101b0308090f010203060f010c03 72
    0x4207455418240700704005021461043e9001d104889c9440810b0f03905050001c4c2c00b4601c18010036a0845010001420307201610780340814015907296220014541140b00402800c01140c00300c0c0120f900100014080c1040c0c010b901c1003d8401a204685107030343c001d0107100c14003c090029040e1103030501c5030310319221442518080c50190340e804004041c00e080ca03504c0d0020170b10203466141007401030251419a449401d078103440c4219004500107840741824203889007041075005010107901141e10040100000030011601980c80c14072410103052680307142c20041c0d00010b0301814110000501340d10b0700c081c20000c55440b69000c080110b001070242c00e8500c5040710500900440090110240114410040e80c0b0035164101030000e9030400e000f0a45030600002450301480c80921002c80340c600a00c4034000d2914400f4142c0d400e03401c5420010541c12040c3c50000243c01840481c80110320180202c901c03940c4094403103e8040d0962004407062040340b40244d00300200e150412640020038 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 330244577 1250 330243327 330243359
    0x306030b010f0302030607051c0504031116090b0105040f090914030c010f0b060a09050603060d1e0204150b040506030c0f0c0f010e01060e0c0304030e03070f090c09030b0f090304 78
    0xc140c50102e03505610505183c26000b81c00401801000d10028800c0c1c00056030124601c1c554900100701511245000d80b000c5941003400d88417805883e4000a8015140712601e00700ca00c446018081c040600005441612450003000220540a4802d2282c640075421000c1030714450442e0180d030403c0341c4500f9040d502300410006e80c5944644601c1d4601c00c45008650500c14102c40c100d280000b0400054a903201d01d01c101c40c0122000310000346c00e9034540a882c1b480301e820001d07403002c100340038020016048042038104d2040e40382180c1d54041c2028022440e06480106151515250800040100310f4000414030340c2030a404003c044402d07580032000c1c160074100300000304150011982010f09481a20710100031980c901a81000402c040d130080340e81285150b00259500d44440c00c04030303040c00641207040e41620407141d002881941c07040d81c20301256440c0c1420010300f00711000854458100c2e10000e0441c0031100045004000c074040392a422400754411030f464a0fa0b500328015040d042 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 330245827 1250 330244577 330244589
    0x50a050105180f030706050d110f0d050c0c0f0a0210020307080a050c01060b04030b04020405010b0c070504021c05100e0714190e10050403050717030f0304060902090a0204031103060712020a0306030b01 88
    0xb0200d07200c9402c104501589950327240340d02d200f5003002d001c0100d0340c04c18041e009041c4036a079103030400715201c280c00344100d13030440302100107450641c51910a1140d035050001c00c101d02502c0c0c080340b0780034218804000c1e501c0c100c0e40100710602d04021040105c030303d500968001d00c031655a8290001d5034005040060000314402c1036103954901d06801088100c4030143c0c08075491081c20003a0408072880030840350269001158011703113901410500c40d81e07903032315010702d050362614240900490040c491042001c503803108088102c0741d41c44040071106440c0c03482c1c441c0e00044081c4000300c0d29401624a0107240c511510704103c601130803900190341c2c00c0c0f4540d005004628000f605005000301889024060500c124003c007030900d1001c0c0346540d902c1014032040161101001183c01c0210070703003190b60b0300c613001004450207081c0000c0502c000d5010b0311044808a800c85040311542c240401c10503c40d0a02c3d80703030036811581030b003ca0400781d4020480e541c02c041c4d9601c40400000c00004079a8003801e0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 330247077 1250 330245827 330245837
    0x8070b0c09091005030f12030c1804050106020309030f0d090612090614060a0603050103020a03020105092103030f010504090302070e150d060e010c0c0819090e150307050a050105180f030706 83
    0x2203440f0a0504000e181c0b00340716815040040c004013000321f100100c3c0e8000003465082030361907040c00000703100b030080406001c1c4d10508000001401e103030700201800c4040b4084064804402c01503841c55034600d40a80448007080c4026400c011480c0a042e0741c05591441c8400850a900c5a9032240122440c419104005401d4081800340c1130030405611406000503003820400c03541941c000595003101d500c8001d041240000e8074a90b66150182c2981001c0b400c044c81380900080c40e10708640303a410031500c599240198200005403454107001d071075542500350700a010628100821b0280390480184201c0141425403008000c5813581d030804032009000d000c0c009489084184842c0c2540c402c516400c0800002d481d061010400d8001241d0b6040d603100d241a0701c0800f401e10aa4100309103502c000145a000000c1200440b10a110074000301d8007103003602d01003a25001005070f003021170300400f40080c80900003440c00808103c1ca141e0800b000602050762100020300103440e142a41c1c01c0540052 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 330248327 1250 330247077 330247079
    0x30b040207050d1e05120f06011103031003060b040c0c0f03110d051309050c0f09190303080a0b030303150402031b0a02030a03050f061003020304020f13020912060408070b0c090910 79
    0x300e2a070454214500d01d1410f980761150131a200b0400c45030150201c1f440039000c001060b0301c0c2e17005c0c07496940100c142200342c0e03031249070003c00340c03040c02e450b0710042d100c0600788001100c0c0c5151034450180e44148507107899545074030544074071481060b0b14001300e05011500b015940156410080c607400f000c99591a00e5407041d010095000d075811550210710784c10301340410300100004032801d40d006011442d00c02e5489140340310005500b58281e10341c040d561104400b000c82815840403000344110b02d400414044440c1c400c09050381c0b031100f220b2b0b07200400e190a40b9854545400d0700110341280d1034161441a80c03030040910302d503a030f01902118000d6400001c00710901c54142c01020382c0300c9032007440c03000c0501d840000704000500a002c40c03030405500000003005c41d61030b11400e0294801c05000c1610210904014100030b5002030301c1e07144a450140d20000940c40c000804602c00c903031004805090502c1581c84140c45c05020f00b014840310402e0010703041035141c5050141c803448000800444a03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 330249577 1250 330248327 330248357
    0x1a04053c2b0501021c23010b070c03080a0806041a100c0501060503030a021f050f130303020d060902090114030129072f0603090a0311070302030a0b040302010506060712030b040207050d 81
    0x403101c4500010000ba50300100328944e4803940341047c1183ca0303041d003450341c03048503141c46400d0a4481d08002e091020210b0a04541c99208100520480f426a020018030a80040c22041005c841010681c0f05810f4030f48030300e100d449686c510301c0c06482000080741785a1540c000038156000308003008016400a44500130448150340850001d44c410942000326040089168101ea1801020040011400c0040303804051180e411900300c184941d00c10072000c0c0d140c9164401079408203207814006004d510194000828010440c0e040300d41e50258002c1c044400504150000c504968900000e4000c3c00320001041d0350498590540082454048003021862007151804d110900001c0c020f40007030040240014000540005241c0c05007081034031711420103000c40c504440f45c0c01c02505401800c011a0402c10f04100b9075005e0703886500207200c10b0365604d0a1020300d00802c0c002601c5414128040400c1e01e02034ac0c0950441400a400503150829988407a0324140d8a11220400910040c01d05600 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 330250827 1250 330249577 330249581
    0x20706050609090703120e04180204110a080a200f03040204050a020708090112151d060d0c030311070504050f060f010e06041a04053c2b0501021c 64
    0x4071850450700c580c8541000c0070015070740c0c3e07454000200b54809100840081c83d01602801c0b802c840010001d00c107028400103064209152000f00b06d001e54101446d071005280b0450a45254820540d00c140d0f259980803042006407529a980101d011003000d0143c3c82e80c2203400040603081094020190340341410f10500003146c4c001003654148a10510001e0001401901103801204091926802c02c0305040318041c000c042d0100d00e40c04502c88401b00040140e4081074207408d4164010302c946250303407000300384131600f06c1940000749414800c0c2c0c01440002d0044072400d1280c2c107150211082c26403118045400c455040d645c06410311203200030032280b883e03c1940603221200a01c0c7c0320104591410204a00e80100d00804440707149108840801103449070a80d00144002010b400d54903207080d0b054070071b5041d0380030514070300300c0204050301441444229103025000082d0045207102244c8000e0188200d008440100b18904030710280007140090000d1b00740211030600c0243c50818450705101 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 330252077 1250 330250827 330250831
    0xf04090605091f0b100e130528140403080408040e040311060a09080d09060908071208090d0207060f020c031c0905010804020d110d0c080706091d0a0b03010b031002070605 75
    0x80201c4c203001071480991540d005803061080907050924003030141da000107120340d801c2e1034500c200b10310380303020019030150309180a184e048444030142d0480300e80c550074505542c0e50442c15000c0854000100340001d110b450110351050080418500305a03d401140b500d054050300c0070742c0014228107065401c0701d41408000d0308400c480d1000c2201d40c44940c1d8480e03084c080c1000408005594004440c1480442d030410424954007a9034156590807034500000d061540300003081c0003d031880002a8a401e0001d145240c0c0d40c100d4004000c02494540308442619018032004214020300c3c00040150302e04209001800300130034a07020358800f12002c01440400389a00c03840c1007003144424080580c8840b4501d540641d007000c42602e0386807414001c194002d0040f42c1c010501c18021400282d040703c0483d030042917130242d41e140045207a4598400710f0900e40806000b111800d680f0201c0d4805c542d030b0b44800a20040500080345030510003001a0808258102c0c00c001d4070380001c0c1d800200306132445015 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 330253327 1250 330252077 330252133
    0x606090a020309070303110c0411180a0315052d0a2405060c0304050a0b03010305010b010302071109090c0334060c060f0906051e06031b0f0409060509 66
    0x6065143c281c000307a64442c014440030f01805144c0e0744a09041c10180f05801101d180540103105103002c250f0440e10139031101198401014000d0002030300c4d03240070805441200d42107401c0402a4034003074440001804040d1a0100b105c0c40865003140c2d410ba1004a80224486251124000c1c940005000e007500c400001000038921030703034050420304c802d42c01310710281c0d4419502030307031142c040c00d12075481d6120b03c2c1c0140c2c1c0d000d040d000d00010a0001d050040d410303280700d0402803014142c41c0c0c0040d03041c4e01070684000c20305c149000d044290390807c005104d501031443c1c070460750300744144400709003030407000031400450f21021480c50b6150340c8500d140205100c480c07148294842c0c42d002c4018040a100c2070000c140ca03460b1000e182d4460b40c00e800241000d500558100302500f4919076108180198031310f02010180d0490005195150124403410350b0b5000c11900800404a401000209014401c0303280d0300039030300e00020010030304500c92180b1039174070500100ba481000e02d0903254440c03e880e500b5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 330254577 1250 330253327 330253331
    0x30e06090a181505130207080c0a05030a091e0e070905100c02031203011208130f06050306012706271409090d09150203071406100e090a0305131203020606090a 70
    0xc04c510340754000780d00f43e6416054001a129003540c649045c0d9482405100e48043c4140d00f4001d09100002c0010200ba0303030542c480000980da1007a025000c90a03181c0c035070740c20901c0640d0410402910000710b0b0751001191a114400359111800114031140c4052460002031002c540c02d402c505040240782c07a14800124554203661410141040e0340c00a002e00a201030710200d46022251a185000006030150000c00d060076a11040000c1564000320b903403a0000c0c04e070904075003500031900741101e40300180344120714402d4203000041c2c400300800b020900301c026075458007005911205000380003a1080e0303240708024050000401240d02c0d406821071900b82c104c02a0880c01581000603582190300031080071102c0350070302e070b0264118001c610003c0d11200c0158074000300341c03038045504c034420b8803003816100741c483d2907d00c120384003c402c451440c0e4030382c4107802c520003090103440034015071a501c6040500203903ea079088003a40103142c0c000c501517801601444001e00d0a69102ca51112085a013 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 330255827 1250 330254577 330254579
    0x1905010b032a0703021005181e03040b0f09030c030303070c0b040827090106020309010503041b0f0306091a06102003280c0f030e06090a1815 62
    0x990500c030242c15070108541c0300c0101a9040c1540300b03030480c4212807a900c2c60b16081c0030306019455070034080e0280c100d11b1070000010b402c0c846000858280c0482d85006241b00c411544410341504460035401083c0e12042c0000144c29010b0b0000f4414510202c040310385850b500d509251401c0350890401d88250010700400c85550342c40a5030540c2a60415401003468685040010162040e08198040c40c1828504000c400c0b1324001201c6102030240e03005e100c02d1381c0c0e907407089882e8050340400c2030004404102103400300b0582150040e41c00c41003080050700c242d480150880314030300756000f2110207840d40408410300000389407100d841c4240c50030600c80c510780030740015607014a90100009101c030030390305c01e180907400c0309241107815068003c59980760401d030501e07024000310b5401c0701020200c1d0000049031034420000444d00c550710440d4000c44800b16602940c1d903c441c0d40c01c654200d4401e12010200395501240d0a00410310034490b80075007110141d0310401d84540650b11a200b00700428 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 330257077 1250 330255827 330255839
    0x1080402010c0b04061806020a021213060509150c1b0109240c0c2912010b070614010f030b10061407060b0301050421020106080c040903031e0203190501 67
    0x1401c2e1001540903841c08030f5036a603454507000a1000729548040d0898160b4041d0400c6880e07401080320080d640c08a03200c100811003002c0e0248202c6808044030702c0c40c075200700074440c0501c1c05003010303c030021305818640a50701221080d58014040c2d4090941c00141d4059a50040124040d0021828642080c4503410800b07030044444483c0b5100e92040704441c0c10301010740c8208000038005501132009581159074030f510700d85110b515402400111840060603c5404482c000c480c12030040d82c6c3c000020f80c0c60241c1031700700f50300701c00c0065038a81e0301c1c2c10b03c1c2c1c00d0220304549410b000c1c0c00d9243c6246516030842c1004004480010f05500c020003200c00d00340708550b008a011402c014850500640d112001d18200e4042c000e10b044440e01340d828a02407000300524809034103400100782103809031800c0306d00000c070300741c8503d8804c000c0150410b64840c011802c1540088554500a0030081800d6500400241c0403807242d0740c0340c4910640c040240702e48130411028110180125420034000c40d41880 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 330258327 1250 330257077 330257087
    0x1707030201090b090f0411091206130f051f051006020118023001020403030215131104140a09061802060904050901060e04030302030601090e010b1210150e030c0108040201 75
    0x4041e0030700e100d2000c43c4e01240d40d9240003200549403c040c04c1404402c00354603501b41d0b43d401500703882d841145174221085504000007802c1c3d20501a00701240300c08405922880c000403104402502c0e079004442d0000d595540340120a149000c0b03040002504e0303d4000780a5500c0c10507508010116410280c21001c003c40040301d1000707603901226501d10440881074501918000c5407500300a40310049501d034200c05040d805071040301d0281d029100352040054502c0361244040710b0fc0e1804080d007d1000001ca5140744078400841d0000c0c20004500b070307246030700c080003500486414046030f4440f0011001c1190703c1c0aa2820310044041d03101c01c08a0035400100f4502035045858003596a80c00000c0070030009400c02e800030800f4030b5050096041908000b40a1b51003140c4860208014403000107041a07070302030850403102c200c4481030030300b550340060703080d05807029180070222100300780b0100e401100700c0c20b036002902194940001c0001000140760a19000c2c115941c10710540c0c004000251b6002 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 330259577 1250 330258327 330258329
    0x1406040b070f0903050a301205100e0a050402061620121b0a03080415081b040b0a2a0501110a080105011b08070305040e18120903150406020301170703020109 69
    0x118500010461081c5128000000880301003100340d5107c0c1c00022138100980f41c1e02c1c400440c0e4144030340c0c1d54000c80b00a545c0c10324450701d1a08000074001800d1240c8540c4020b400a1008003458540040101c919100b61403074038081e5040c1e50502c1d4001c0c012001c1d0410181c4403502503405540c84406003140940721010643d21140c5010302c620b0143c01c6176510340594000e5640403843da502c3d10b0b200c0194129120302110b19001068010002c07680b41026144601d808002d102c1e0034500d032500f884010190b0750030038035084040c07101e11840720040c03059280450900400d00d101040058400e400e0541c01d4030070307410302406403140402c0244003140d40103900c24152007080c24080b24a1841001c80542c0301c0c1d00c800d0143c90802c01283c14810135901c140100103c034046a0220055251145034100c04001141c00744140e40c050b10505007080b00e10b4000d40701006005043e514401e4101400b250301c1d00b82202c041301e4140e03000006024071807060203402e07130915468000704a16400e60740040c09800702 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 330260827 1250 330259577 330259583
    0xf040f0e060415060c030c0503030103030e0316033305070206060414060306040201050304020112050705211311040f05010b0901170c0313170705070e0721091406040b070f0903050a 79
    0x170040a506140c000d64400e84c0c0f51743e0200803070390b4941c0c0d02d040003444200000451486030140b101401550203d1030100000d0740d4100d0200442c1d103403030a840302081064845d5074000303900b170b0200c0c900d481d0745907208440c419045500985020314116080104642d20003407251004030400050002c1901c001031034a0f802513083c00d00c1c0b0b41e00e032210700060312001d8032060802c0708142020208801799a0000213000d4000c07110942501c0d0070408007190350018002c4920b0b140604000d8082008a12020340b044a00b42d8064000034001856028413415614241c00038550b8003800140494196441420742d4a45c44400340e5103034043c2407203004480f140c800139203518461140102c00e5000d01c404150120012210000c000d0350704d81c0340c0d1606a4940d01144684403250351444001a60710380200c141801c40d074403809203070b80c0007000303904610000c104560003a1160004000e00e2a84880c08105560055000f8000c0002524081c04000d01e9100c0c1c0103041d800b0000488402c00000790001440700c951a4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 330262077 1250 330260827 330260837
    0x11d060306061312020a0b0a02060f0624040e0c0304030f0e012d030e0304080304031e0515090c030a0f15110307030e0105010906050d0212030f040f0e06041506 70
    0x30341c000014040d0044114603403001164070000a0300481d01c1c06503105541c42039560209a541d9180e00102c503004410300c07100035801a2002580d10b80c5200c1c801a40040d005120075902c10307400d030707800e1900d0248600b01040080001014088010714109103035010b1004039050f869890107076002400000d007900104103000c00c80d90051b58030303070103220010003d0241c4401518403000110008010001140464020901c0c185d20038003200d4003c411a0700b030303070601d0b002945001c4c61640d0303105c0c0301604a44107402100c20a000100092802e01c00203894810040304c019440c100810325900b00711454601303502c42e902040780e6800054401c400c40c0b186a41201002c2202694080d0810103809038551008400d1000001c100c034042d0944d01c2001c049a0860003045a0782e2980d1500381210254081c40b54009426040000103150011010103451280f0342900d0a02e4500020340c00d40b900315400002c0d02c960358410074006500180c805a5000c142110107000210002c000d8418003940c1380620402c100c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 330263327 1250 330262077 330262081
    0xb090f041b050a030e0a0c15030509060c1c0e032203020a090b040b150d14040b06040222060905010f020c0109090e0f032205100504090c0c02220506011d0603 69
    0x3078060362029000340b0a1409981310506e8a10340b407040c001e11070007800562001c02e032442c110710303200344601445040400014840740c4c951810b24945d0340c1181c100380c0c1c480c1000142c0c2089a8880b40144070501c11204000e544a0152040c0f45061f00000f201903000050350a2003080075a40b0f40c0070301801c4900380c070302c0058540316000c040f40141c5007640400340c00040030791511200241c140c0080410080566040120000d2240050400101520043c003039900d05c5000c02c034940f40c2a4018110403030842a1482c1c0c8010b185c107003038140d101e5988140c011a02040080040756000b0039940341010051018201042d19803001805080355030240d04c0da0159114402200c2d03460400c4441d00b20003840040300e840b104038243d91101307140031280c40a140b007028040001d503800e282c1005070101c480b40d100d05007014104003824004000c414108410003c04a2a810240e244c40503003003000c02c0c40300868501030001c0d041140c16108050f20113070403c0080440a011349403220203111035840304844581d07070380e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 330264577 1250 330263327 330263347
    0x7270507030f0213061e050403020f040b0d03020a0c150c110604080313051e010c1209030b130308010b0f041a12090d021005060a0e18070b090f041b05 66
    0xc1405000c01654640f00203440d0000d000c40c60304503011101c0581c0e5251480801107041c4400d821001c081002090003032005000524001800302d20038600507000150140b44040000c4510944d0581600542c2090701d4801c00e03c942003001902801c0400c802076269080804c004100c2c1010010107072081c07004201c0c9407029907030b16048a0042051504403a00d0305a07441d803185640c0540c2c0b04072403195080084034103008100504414884105071a049001d00c62500d6901002450740d06010412002c0540407000940104145002d60842c15641e00b241d03807180360103019031906821506202c0d2043c0084400103480030101d90580d0089603c0c141c030310014100084503402071240d00d00c480300e9584100001e034180011194900e0003258200c4001101003c81038048a03400e541558006207040340030f10402c24007054054020b00c0480001c0310311070040c040103040c48010b0b0803075440d00c80001140b201528010003c0004040112001c020185248031401e024102d400444800e001010420030b41d4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 330265827 1250 330264577 330264581
    0x50310032a0b040513050103020303070311030c0d0507141b01110309120a02090a091130070510142209060303090e130b06130908040311030727050703 66
    0x11940000164032807a030344851081010390081e001d043e010355000313401114058100d01405040b640c001e809075140c4515070710b01b110104a110120401071208102e038400030031003002910700200a0340d45298540031a46011000200301d18044012a0321010070101083c0d001003081c4080c5109003802c42c0018140c84419086004038061035922040840e1a030b203040c2004030b03582450078401c640751282d80da541c031404c000700c0e5921400601100e010504020070b07400c100c059824650040c620410341502e10f40d40002c01c1d40a004100b0243d90007045003088a03007050a80040b080c0500e0500701c200e075000e501510124068408200d00c0fa00c58050b804078103001c0c1c0003454000d899282424454a07032a0305000e88800058810700307203910055000500c10b035054030010301c4400c1d03101c04280f0081d10340313808001380c2c00d407030520014002c2d41d10bc001800040012000f003009500c55001054140842c03001c040c280307401d55001480d210b01031461034a0004c200d030380000843d00d03000400a6103440310002140 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 330267077 1250 330265827 330265883
    0x11210a020a0c0e0106141204150e0a0f02040f0e0307080703030908041512020702181005040f060e39071401021c0b130504140d090e0705031003 63
    0x400002e20000c0490b4000c600c0d82c2c2541030300c40f181c80c0e4002e0780807040340090702880741c1020300002c0303502c20700400d0004602036980d46c1480203a0f4004510400002c41e0f032401c10155071401c40d8884c9510014104500b85400360400501452004010709241042c41d580c80317100b5541d0041004e00001902c0080500a601040d10a504254100d4941c0d85034100045490380d07641e01c09010600c60080034441d0300320750007102c040070341c0074010300180310403c3d4080c0300c4144042c0101042da1141c14000c110703610760f0f200301200070034100d001003040c0d890308102a5240030090000c3c207040b802204108098030590040380040400341c0300c3c3c3c603006400881a044140101a801400d080f9404080c6203c10415005081400641180c165011591700c107800b049400c400c3c00b0941145000114013046603041c1e002d01e9110307004060751461070103070104907802c04482d400b911b00031464800e4188144480d0364130456000000d41450351131070900700c04011042500b4800100400009140080400140e5103265 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 330268327 1250 330267077 330267083
    0x80603010906050103120206061c020103051009020a1821081b010f020309010c0c02030706030b01050c0f0322030b0105060901021c081f0e060d080f04030606030311210a020a 76
    0x809941c481c40c04030f070180ca180c2906c000612861002c20384500e01814071420f078070200001c0c0705c100200d650054020b010000c03c28503285000a40c00165503509000400300d941013507445c01e89180070030422405c0550a03810000d48580d1100c1d00313a10a00c60302044140403904000c080e074980d5000718014010005047d01d10034154200a4620740c00b03d203a8010b1030182c00060002d02000c020306008523405e90b0201006075040d44111400c0140340c1c007a070321038081c40d00d061425501c0c0025050105240004035180502103500014100320042c40b002221032160b007c051510b00c0c01455515201c103c240e06000710362203044002810800b030ba00801c4005c617882c4412084000c010083c3d00050104a0f086614039407640038500440c210500c203a8066056030210400c0e0040d54444206100241c0e0301d40c00c0444141408028081051160b200034000440c07041c1c102107416425468010403140c00801e415550780d000e0381c41c20814000c00007454a072080b649696544a40085400306c3ca04800c2407070103 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 330269577 1250 330268327 330268331
    0x512040609080f07150e011a120106051f031107050a020919140601020609150f04030c020a090506031c08060d0309050406290403050a082206030c170c0703080603010906 74
    0x700c1002900b501e907910f407508039501085003006c9520014280c41e0070f00b890011a51000071034900c1c900e00300c0d8007003000000e41400080d07882d40f960003240707408a45e07400008241814180500c002641130044051030300c006d401c3c55061a9095a504d680d071002140300901c5480b01c200007955514003100e030103400420b0400706004088064100e11800081540c03900d0050007a070740001c83d01c0303100140303401c5002c550409484e155600d141ca2001c0d0300d48003400440401c0300c540c14800150381e8516031031019203190940052141485420540781c02080e04890b40e1002c42c58803075840711a00890b40c9a4410320590b504800e079079540ca0201d070055116089140d04c50f28159000c150014030301c401518451480d054400c0d241d00503a44000c4038011880010041d0f48041c0340400010020405005450010740c501003c1c034800e001600000416070300a01d000036600e4801c05d030496403051b0803508111840550710b03080d041c1120380010764400c0d03d8010301400f56010110b20151000d41c850341d003013038101c401 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 330270827 1250 330269577 330269587
    0x1c0e04050c07021008151e040507050301080f06070507060c0201151202090c0c0c12030c071502100501030b060d020f030a06060303110313180207200307060512040609080f 75
    0x35441d00d60099407041c1c0c080ca0710718004031320302030255002c2405440740d0701802032080d091108100700d801046075600035000f801d071620b1049481d40d0243c240500300b180c480644940c145030760b0510781081c0d075240d500650300000501c125990046c044490450304688040b6984550400503405003859904502d40751080050015882142014541c6e14510844111145403034841d1011054041c0145410701500b10003403c010520f03201c0c50b50300f0900380d1a0241d070305040c0f40e803080604100d11a0300c056a0000481111907079594140b0050311644d9014030100700c00d5040d5214040700c43d40c0104003d008000c80800a415545c0b14504550815402011586c01c0c034503074a8188041c114521080b40410700180b00603821030004030079500c02c0c2002078070700c858051400c0074520310010703134651112055908020b0030340401c0201c014401d0301040300141001c25140030040c11301c4c20085d98000420090f0512140d1005086566855003254011070042610318407030400b1280c6108400b00300381c6180e00019 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 330272077 1250 330270827 330270841
    0xf0a05180d03050408120f0f09130207152304030e011710050a080714060310080f0114060d0203061b21070f0806010f110c03010e16080703051c0e0405 66
    0x4021300036240103c05443c9015410602e024040c0503c0402803c494406d100d020010340002018245411004081c903d29a044644e510708990017130206403201c030101c005030750312000607004078541100d000964086400400d01103152500e8058401000c105c2840e62501d001d0b8881e0388908094a0841d001c446e141c1015031840c1101006031145500540f000000043d110001150f22021991a240400e2a0814000c01c000091b400148040315940ca4000c02242c40c85040080c551060f08240001505203c01d0030101e0024000514152060100d03103d00001030310017182d1039400c401080080503150031004982c0f882409450048403212018401b2a10201d010782d944502a24044d22084401e0003061400c4800c40c00c12120103010a516602405520f44902e040144040c41c1500b0746049428580000c0e094030145140904594007465615844281c668900b10040c858400104001860b6643d401d80759402e4000d00c50ba54075601d0381d0320a046004182c58100720030000c00030840ba1a040d8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 330273327 1250 330272077 330272087
    0x421030603020906030606090a0c0201270528060e0a02060a081801090305040b0901120f021b030301050a05060318070e180d051e0d0906140c0f0a05180d03 68
    0x407000707a2249060354089441e0f4200455010b01820b8060014115a0384030805038004e0181050b034030007159601c4405501c0601c8040304100c01c024668407800c2040114240245440a446420110034038554180300d895042982c1c4003200c0caa1100010070b130840b4459280c0c0c01c0c010401c40207500100c00081031241c1e540c1c0b0801e403c0c400c0c0c21449000012a0080e40d10f03900725043c1500c02004100104803d000807007401010b00a0b0543c149860040303135405c2403a1409070303180080c00f010000d4010070741d03041082050f440f51070701400c100000c608661412000a80c688003c0c840d280c0102e600002103841c8000d06403403144001075800441e2209980c81071020000b1301c081b1060305516078400c1a80c400040040b9410242100c1d66850070b04005c402d1a413000c002e09105c01c0c101801d1801c22074209150024054140311501484d00015201c1c090f05000c040080c004200d541c80c0501088205a9045145c0540c0c900302e449151680c2c54407554041c900060000c100740c5503106401c00e0041c000c040c2c0c44 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 330274577 1250 330273327 330273329
    0x20c0d022202070302100b010c020f0d150c02011a03150c120108030306040b0409030f2001050c0301210f0303090c090e0109061d06060d03020c060c1501050612060904210306 76
    0x317608941280100c007001d6021a8000d122490000c4caa0358410009440d19042c4680b100900030f111052a90180c0e80e0320700c500d180c0b0803003d5142a162600c04016940a102c1c121083e2101940d500c880514440000e846001248441c1c05141100c2d001c100d4032094941629050550540c1c02000382d41c45500c885d989800c00c4030324512070343c100a40c5008900306802003c0c103507507140d01c07420920780e1100d4098504e44a081d2040c000101c1000c605195000c0900540d8002c8511460851b506d50401c25011030208111a104098182103885480044e00e6030301c0c3d6540640d01072070001095401071414a04d00d041981c0107036030650070650303403162421040d44414030007845120100251400100680742c84070388070201c100ba075084800020070600707005500c80c160500c02e1040d19034440c3c00d500002c00c0c0c1d40081c50303032401c1c0703520000b850b160319681a40424007610b41100c116050098200000b041198018001c600400b450004a82040381000c0001c00c512180030101d500b600350305030010f00130421 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 330275827 1250 330274577 330274583
    0x10b03070c0510050103060510150f020f0115030b090d02121c0905030a0810050f040b0406030501090c060810050a09020c0f0102031918120c03091e180c020c0d02220207 74
    0x2400c4027140c60a20107007600811565045003034801c0382290384040c0c03035100e0421007640c1540181e8415040c0c006d4284a507504509804011016141c114104130300605e10050010310164803803c440c1c4021900043d41915008203c1c0074596522040d4040c40c02007013038501c00340b410508040303800e41004004000382070341800540e11401207541389084c1642d103d0480c031503903801c040d1001c07041c401030506412070400080c000d170020401690700c1e0b5445e800c581d0f0100e0191a100350ba4001070080760707440714001ea0082188500a10b00c0f6051100007601c48601d8400d0f0070380c0603030010700c0059040b07041c0850051b00d850900215160700d80384096042c200c1c807820030840c0c041e15020070380c03202064081b81c0399181030300003152007030011040740b060f509003590550070b13000c0c042d50b680c00040181408040000900321640f80300541d915114a14007052000c1c1140318480b401d00903440d000707586c00100041452030803078550806102c10300200c0e0901113088141c2c45040352b200b0520300b134800c1d250024002c1a00c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 330277077 1250 330275827 330275831
    0xf030a0c02010c0c0b13061404050705010f090e010e040f0c081c051314030316032a02030a033e070501020610360b01110d08010b03070c051005010306 66
    0x20344040b5115224000c00400d01c501780300105658001011400785824400e00c0d0005002c01c1e00c4600ca03081140884007142ca52b4051607082c4030740e591080680b004407500341445450141130090340b0900d41014002c818034034041c50001020300c002034007002001e039007142e14070f21015240c050341ca03120700c203401c80c0b61200765241c031103035140342d100f8412183e40701150b2244586a50402c0700d02c2c000c856142001e150b00d0b11091081c0600400c14800c48243c1e02d10a03101d8950321509031061016541020742c41150100e00302e00c0b28000750f100428a89205a41464081c41f200c5000490090112015800380c00ba80480240c1ca02084104903030f181c01c101c1030b1022291903d41d81c20049a980c04103c6104503100e200c10420088003245107001287c0010100210450303001302800301e203880540e0342d8034111058564141300c419507042130714841c00391040c0e005410318403001c14000c3c3c5400018843d100300c101e000000560b54030b102c1d5500b0083c90303601c2030680b0540d15450344502c014000a000c1075828034 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 330278327 1250 330277077 330277091
    0x60706091b0e07140f0306010c120302120c03070e0f010504081501030218060109120f330203010828050601080706090f03020a2c09030d0e150117030f030a0c0201 71
    0x507000716071341e410180c00c2940e1289441241d0207500c1d155003020b807507641070054400c4181c00241007000031240c07040103513a00586699880248030f800740b90180180c2104281001031041d81c5d80d000d203084070740003001d50311901c0c94811080104c59500c107076840103c41e401000b00502401500058035030480380200c07204000c0103400b4030205907801060300c40d64040f580104007081840262420030014a01403148694014041d4640c55081900b40001c000c0496400d030040707140d8100100165860550b00f00114255070500310380c103a485040c02d8400d185c022032850300142e4160340505d1554910b038003109450725075035540505640c80f8080e01912000c592804000300700c21880072681da048079001800e0400d001e10341580c1105051242c001809100300d0704811460030303c4212095405080303100015665100205444421111150900c0e035071a0080c4408480404c0e2405000e8192281040b180301a6652051802c1c40c40c4503590242e41544800320800c02074050650009500000580083c4644 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 330279577 1250 330278327 330278341
    0x210c0f03031201050910030812010510031406040216050a0609210512150901180b1e04020903030417010902100f0212030606040302030102041202150304050705060706091b0e 76
    0x207000c1d40c03240c4a12001c9401c01000b91385051005c07281c003c0500030703030700307050940b83e4643c0e100c42e5001c0c80959800c400e0f0800100039509110100100c02501480c040246e0401c0d4404688003c1c40508034078481e540100d0034071210030b0714004c5850140d5004d4200e0300d80e8811071408c84042d15042c0410b449200544a81050010000794079008140c0265100c529003000401ca0fa461800090300004c0c03800200d08204803143c8a807659036002c1c0c8020920346030002c4100350104152145801071601402d44035030b17003210202c082d18401c40c0ca00d108940150700c0708940070200b407660060b03500c0201e50010f207000030752140f5410b45c0030319400c5000740c07011100041e03120800d481e065030748503580e001603000c100500f541034080000303503800c12401000203152031b980c2e03000a426600b1a4010b48005524940a40210b160650325406401104c40c0060700354078180d100c090311000b1a129440c003070800068000d04100040d8490500c560307100c030781404864800358031007003400103d0140b6800781c210b10303000c2080 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 330280827 1250 330279577 330279583
    0x90510030308160801030b0411100e0301050a180204180b070e04140c030f22051b0d02061207020a02041e11180d0c0b0705030d0b060a0c0602030402210c0f03 69
    0x5000144e8a4240c026481c41e034550031640801030040d01d440407402950740655881461300090402e0599800800e44441d60405007103c40280c1240d41192400304210aa50105096808500d0f0100c41c001800283d440c5100e6800c40701d014010100c0c50200200142513800251001e9002000ea804100042405114584015041e07640c1c05601c2802d100140160b0800c1001c158802c40c03802c9068183c440440c408000d54a4207070f4101d5464014100440e070800039600004024002201c600d940e205082c0c020420368860381c1d04200d042c2a16000040703200f40204038002040c1d602800c1040f4021010041481418283d055103911074101608450316801000a58034100342450700000040091420081242c0900004640e4282151b000088504a00c0013400b4064020400746554070038191104046504440380240709400501c40001090b5100d0b140c001400e51002d00140d8035140d038000620514120705104005c260000112004000049030342407020030700380c81207184420f4120403d52 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 330282077 1250 330280827 330280861
    0x15010e0907150c06020c1203010b121614130509180609011a04090201030f0903090f0602030403083106050436020702210c09091f0b0604090510030308 66
    0x100083c40300306180d010590320340c010140700e18200c040702c0400090f010315140e1508240e000302d61001010407410300b6601594211a07000c28640ca08032401034000ca17024000807607142c0010030302030003c50425030031106100c40c01d0140000804009582c80c083c400c50001106016000b001801544017041514605015102810300900b07800300e41510000181701c001c0c00113080c240c2c105620340c200300b00b24074060711408030900e00a035120026076040400000e80000d481d80f2400840d0f004100c01c00200707050700c056580b01148030301c203074040c000b82d1005110203001c45001825043e401410006019810000400450b03a4100c000001c441e0710030500880d28060b458901c00c2c004410390000c840c40a6603005043d0144000c040c940b1040400122031070803171031a450102c187d400544280503510705542c10747c1d8090140350040c031105c6109200d41c80c050707150003a0494000c1e1141c001100076078982043c0d4025001c4000c2c100007901d4412140c40d80c400c0b2510055011801502c007150302c0300c411114440c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 330283327 1250 330282077 330282119
    0x2f10020c0d0210021f23010e13021f08070212040605040b070318080f0114040201020c190b0f090a0906080a03180e04050604050c0a050f01080915010e0907 68
    0x80107040c507000e0062a40c0b000c10380a0450290011650020320213024410415485034000a0404007205c4213005c0e8901e0b150351012450f101000402c2121441c0c074240750b00c00200084180e00081070320104202d0508014491480c0901800040d042c41d400031781c0e14440c41d6154211002600c0035031001c03030944500c0c02a080055001c02c402e0040c030070035100a1014504c0791074003c03a18110314030b448a50345210b42100884d508104000e40c1c814009014030f901181d1440342508403400d03d580041d68030545100b20070702580fa02003081e9296600d02d03d030f0a00404000001c59540c0050700c4198410364012086203200320034910022550818902c103e6059900c1c00000301100c102c5034a050710280d5640404000c907404a6402044112200180c140074500c20401030000c0d0601d0f250560810a031011102e01a9846c80d004000c203945401100044080c2820910126194049418103002407413010715070200011000040440000c00030f01c2c46000320906603800141c1b141401000c12440c0c490314 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 330284577 1250 330283327 330283339
    0x6100305060d17121306050f06090402100e03061e150d033b01030b040509100b010e2809050411041107060c050a2304122f10020c 57
    0x5000080c0031030080400500c0212049814100740c160091322100049500743d07a07000300c801400e4104540ca004140c1c01118030b132425001d0b032400030042a90f038000204007030300c58126826850806030041c40b40c4c804a400140070360300c8a140406c1004030304140b00032504910003503100002c0d2a03201d1105045108440102018914820754608450b01001c0b40b007200c41d06400c012a1110311a40c0354001144119130007000c1000003010300015040b5041055054095400d00c010410195400304580382c8104140c540010309101c0c50004035102d550410406801038040c21942102d07a2100d0311100303603c80d5004043c2000d82e00c03164000280c40c000d80313004024404009207459a85440c4c0c020341a41d04028034800c0c181890750320380600356200c40300080007140002a61800340c030350050450b08040020041c2101038500d01c106070016200d20310408100011084901040250034412582c401a102d032030741040078605010551030503282d980040c0701d40321172031103d2200350000c10401e240401c02465 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 330285827 1250 330284577 330284599
    0x9050603060d170a0201060905010e161202160b1b18010c140604030e010f09030c0b0304030302040f0e190b091b040b040609080d0305040803040f080f070b0610030506 73
    0x2800b08034035012008560107101c10303000e6580c1012180240c0b51070b100c0e5a0022031118507000b450030031104181c020a4007407100400b00118110b09c43c80300b4003003804a2401079400f180c1c082008000780a40c1d500d042015a5a100110520a50b001d48501a4a08061400d40c40140ca0317074010903840f510721a01c00300c1498080e100d00d01c3d80150844011240101c810700c594101c008592401c004049a0031408294080d0547c502568042d000118400e01402c03d801d1260031500c03000303c00309061141400f0380c9c000000050805101c0c1d01940c000f0604440940c1c01c2c00e890702941d500c010401c688ca00f230044d015038500c2c003210620b401b44503101a00a800082141c42d1000240303610040001001c108100801c000030b05c541541c00144024150746d614549481c1c2080030b02410030b61035206150416083c44280004a44903008481d0050760090642001c101c207450b00398a94000c0e02c030046c4094101081d00418850906032291003010125401241883c0600c0306174211002034031441c3d00308480381d0f0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 330287077 1250 330285827 330285829
    0x2030a0c060c050909070c0c0f0f180209060406022103060603060d210309031202042d08060a020d05160504060e0402070c03030e0109140618131104050f010905060306 73
    0x8010700c0c2c6110035140007450012141e001c10000e2105407648000101c1c6008400300340240d80050402410407410206c3c0320a20384410588080060302a07004e00c80e4144e0403c6000c0880360381102c04215001c1d200980340c0f0354650002e5291480c20001480300300c1e079180040d0034403041e02c0449100f05801800340d030454a400c0c003400356403100d03076104035540807010340a4504e10610a081441c900030700d5034007080c8960645001419881040307801246140188000d21170780300b00d03840108424443c007808030b00b000b240c130501841442036a4807a16542c080e14003403200e030545070380003460f802e41c20740c1e81406a9260f4007202c40075240404440d2000900520051143d180f0558200040460040000d0300302811030f11b411052680581c0b040300070038106032040969582102d880300092441c80c81c0b100e1490300c540c01042140c8107032902d902481680c40c400040f07654810010112154010104000007510040c1d044544e52050040502c0740f0143c0180c40900d40c4910000000c0d07030f902604182c11078030703060 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 330288327 1250 330287077 330287081
    0x10305100b0d0b0405030a0f0203071e03050403210f0216030b15150903010507110c010818030c0d02010605221802060d050f06090f0f04050f070603150602030a0c06 72
    0x3442980b01002d50144000300c0c00c3c6981c11070055001d0005140c4d5076140d0b800207082c0d00c1e00354580c2d400b550014041c00000c9a409039540d5042c801c8110700c400c1240031031800b00c036184241e400080c4240c42c0d40010383d0448502079485101c203800350f19100c0308002d813074209980e52200f034086111419181704007480060000f0a0064010b400c503d0600c00d100040e80001d60803102182e01064801d9021801d00203e00d82409910740000d81c90406036810ba1031101d0054460b10a0100d8034103100c000408140d45101242040c801c0e48820000c0ea510703800d101c20025102c3d204003140200541c00c10f040802c2038600400f5480d1405120044440c642ca00d00c0d15450142881ca014080032480700e4100d0030242e00c504006080106da28240082c044c41c0408144000c90405131480f4040c1d98400108601c841355002d005030058175000b01500c5075600c52415078a0490304641015190084c1c00c000216242c25402808203c6000a1400030981d103517442203a80c0d0045801103c00282c1c0480c01401058880d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 330289577 1250 330288327 330288341
    0x80c01090b060a0312112119030902090406020c1f0b0901050103022d0708031029090f0d38070806101103070f02030d02120a18050907021c0201020301030510 69
    0xa0283c0c0d0a64a9001054408008524424200d01f00000d201e2544104d1521443c0c9000f0a60804102000079a000310b248640000c100908a5a002451392207801d01000311314140c1c600d0300016141c940c003100c0c0e03200103040300441c01d034080d00b445000820b03198040e009448445c0014250000e1480300d440380250202011800c80303070700d171608000280120340c0c4600258800c8001200796900b203850310004009584000c644448280040b140c1003210456010031250204000c91b10f0a00d01007500d00054081d0f00420301c001d14040d51036030042c00b072981c18a0020001c41c0d4900640d06a210300c40d521901c1960111502c0001506c4400010824900900310790254803842c5444041c00c048481114515444000c054482070340350559081145030410126060b200f00e0b1014104400304200c0b000000e014806140d02448420206c040c101890007030400001c003001048802d113030500c40d402075200c007034000c1180481c10040880604140c014021241240c0d03110000300f001d075440001500060010b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 330290827 1250 330289577 330289607
    0x5040b072001020f0a09060f05041203170106120c050c0d1407080d0203011a07020a0b0913090b0618010605040b0f04080d0201060510090e01030f0609080c01090b060a0312 75
    0x40d8120507070302000c09102601e81c02000a1070702ea902c00f110003002c0c0c014022a48040104a048000452056031040c00c2c0c0b001c49182d001c9003141c0481e20702d0244d6038191000307604140f55944400000f891780d4022a1290814064030741001a0100d050084681e44560890040e803a40940d148014180c8034010055011281c4102d0505010043e0340d01c440c2503105110300c04181e50084018018440c1c0f550301400000ca80c20485840c01030564086121642030344911101d6244c0881c41e260a074440000c0c244603000c052204105041030352074a0354030018241c0f440d80c040c01e01702c07641c6042200c01d6190725040e514152256401c1516007081c040b8541d0000487d00c00c0d001091000143c0c5d10810080003281d038a90390004224182000c05124240c4604180101080b28140c8100003840c102002d060641e5004914200301c0222401c0c0032001d018101e00c010308181c80090225615001940040c4103184100706003d03030754880324200324240c0e0150002030282d4603080c0058083c24085e115061139440c2e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 330292077 1250 330290827 330290867
    0x607030201020919050a0e01061b0507120c030606050a06090b07030203040f1503050f010521030c2505030a020f0f01020c1003020c0f2b0903080403060b0f030105040b07 74
    0x401980841c001003041611200806007a20081c051032402900d10382c050198403050700c0c0d0f258076094004050281c0c440301c03817105c104402614424003505008100282c0389504de0100441d403246007035000300e4214441501c01078909440424145000e120171000c41c1c40340d9548510355410041e403500c15510102c0100e040d480304220004200c01a00240801003450f1004c140c0354442c3c03c0700c094183ca40040081c0c001c403075004014001079550700d040c1417581d8180c3c0d1708180c0500b69900c3c160314620511103625514444c2040c9142c80e851135000c203109911100400b160816918018035984161160b0025449820b601500040e410700e01c004801100c0144103d450520304200890000c580c1410f82c0c00010382c0010700c100b540e0104000032082140ca1000a004410b4041c42500034444800d0181c24000d222070750aa0440344600082006160010391890f41c1c0c07640c07450300000402540208a004030082e50100c1c44524041c1300d814861078009021801c107594154003194404504421002d59507 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 330293327 1250 330292077 330292087
    0x1b0c0b09091014090a14010f081603050d050d0e16030c080f030a031812050918090a0b04030909051032060306010c060515030c0303030c0f0d0906020d150f0305030405060703020102 79
    0x250f41001b801e0b00800249032042e440a003409001400c1c403610402800c042c1e004e4100c1000058800100f221041d411458490303105c2c001c40c140f8001828a031072040c0031074030852018000c3d4016001c14801101e219142d41190300395140411915800f40310300d04001034000340950f02035503010780c0200d00043d403811900b012038203080e5038001c0c441051005130000074801050010140c201400c0c0441103c0d400f41e940290391800507003056540650203402031600002001240c2058050f40585015100744c50003442240703440c03000c4280001040c45220b02110442003007811354900c1c02c1c50f0203149642c3c800700c0d21032107400b001484a15440030300b015040103004280000440c2240c0300e11406031f800d2100e5401002400c80806d07181c0301440c0e408920a420820034009144140c8003200c1035409a400b415407112903648006c0020219498046c2415000050b0055294405da0100440034080f9101042e069150500c1c2d2590070841e000043c00f40c1c0c000c100c14420380c501040904100c505c60304c00540340c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 330294577 1250 330293327 330293351
    0x61709060c0904110304030f0809030702060910020f071502070b0424020c0d060902090f160c0215030108150a150605030604090804120b071701061b0c0b09091014090a 73
    0x9601c2100d042d4000f8001c08c507012129980441c80c107801c903200034000c50800305250005940e9101e40500f482c455440001c1860503030b402445000c3c010010b640550304d1040d40c0c1c0e11100318907142c4106100060040d84000b00d001c051041c02e50b000d80d006040312210200b94000925401c1088003405819440399500f5184280e940045031039845114550204004000d441405030640002c0c0000e5404048142082649401c80c150030480e0324092902d1402144140086001300c2c49984c00184510400000440c41140002e51120205002d903c2c202890b0340740440d02e0116040c0143d12206502c90b00d02c01c1042a20a9000d1500960001d10005840d212661031207160390281e4040109a5034504032042804540c3e0300c01c1d94407500700e0801c11303d007900121903501c0b0740e4814044e14060040c03102c0110040031803e0360b034a0a10741d10038141000d1a40b160b005a15603048580d03258803e008004c0000c000314914402c0100f2104008000c0c01000e0140b010090300c1400103000340c2d8020b595988800355 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 330295827 1250 330294577 330294611
    0x3161d0d02120d030b0f0d08030f04290403110607050d020a030e1b0a09050609040f03050904053615070507120c1a0f06150c03040f061709060c0904 65
    0x100c8116240003a00407922806d0203050364141d2041889075400d54442d00100300e010080325407026208010401e01d944030303c2c00300c103a24a030b060004007035000e111b82d8992003503030301c0e00040c002d90003070300d941d0300c03080c00000002d581d44412110705000460a009100700811560003030b02c1350b0341031801c02082c215840c01080c0d29100d0510402c107841d45962a0904180c2000c1c4040f8014200741903090102e0710388880440c00003003000e40000c1107242003075408024544180141c414200e0010000d00c29420a240403a091a0040300300005503100081100c8506211903108030350800a200a45800e030056684c90115000040044060240402000c400141040e4110f510a42141c580d05600c0c1d5460401045a000700d03140305181948a8040c400d8424103042d900d07a000c0030031030341590700341d42040300c000440c081c0c03a2010324180b00218000c13440840d100d010b230090342d40b29030300c14461806540c2c0c0c441c2ca02c0300c1079070103502c030360003000c080340900024600921030070320081d1010504540908407061 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 330297077 1250 330295827 330295843
    0x1080c1306030507022a10020d020d0c02060f03190513050a14120c06040b16050d0b0102010204091401140409021c1b06020d111c2f0303161d0d0212 65
    0x181c810128990101d0300e82035507c00c1d0a04903910040c420100c400c0c1d0701a40c0c507032180010030f0a0081e415030a1003103503201412240c030111030400c8180c8900b412011039480054203942c40ca0700b40c6c1002c001582013406085921451038200c0020724105500d610b83c4003050b442c8000c003047e00e004451070b84000c2e4030f5040c000c04070411184024400f52815080400d04540060140c403020320040c481d21b0211580001504c410f980c1c1c0c1c50001510030380460050f0300a03c06d50348040740390f40c02d00001d01e5041c00b800540904035240514004180240b00d810030089540031500254031621100c0c08000f0001098a5800317260320900c58040c0c0c07000c3c120500c0c0c0d44070382c0550000d00103a200c0b180c10903407164442210303aa0304200340001c00442c00d4040c02e0071449503210a0790340421140c091042c0540c00010010b80803507a550a4a030745842a40c15416126403040b62030075050318030220164940d900c5400a041078644030803815001c400ca420400408175803444083e80c3c441015214103040d04030138400d4078 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 330298327 1250 330297077 330297133
    0x2a080c070501021902010f0b0117090c030d020c0109050d02061e07050115060f0e0105181302041202030601062604050a061a0a0803040b0f03070c1e0201080c130603050702 75
    0x1c503450030f00c8130024290740385039130b004080b41c0c1410340d175100a9802c804c2450035480c05001c0500c0340c0d034514007180e281032007694031035526204007419011610380104074030401003401e07a68944030b592074006000800d070302e80100940114040240007200c01c5d84034080000c001003a02d15600e00079081d250755003903031f007050305400705050240f40401002d604410400341038401c0d8208a0360301c100b0140007a1450003200c2c1d085802c00541d1031201140e55a41d04400222440440119180e035140c0c41c0d015444119013504070b009108950007c035885008001c1a400414109000500808000442c400c000c0c2c020707008851510561411000060b024016140729904251040d40908003200412824600c0b640c05108207820412090003040e0140e802c0360100440440680c0d603c2d210200d08851111040e03c025207001c0000c00400302225a015501003194001d0341d031041c8545807009101c441c1c0c8107071a011003000f981c3c044200801d038025045a40c0c03080050040e00c0070f00b0500c07c24141d103000346c03411036 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 330299577 1250 330298327 330298357
    0x708120306040606170c03060f0a030b0901140415021323010801050d02010206180a02130606030f0e060a0b0f1909181e0c15030c02012a080c07050102 66
    0x5142e00b014401d20340203200c1840d08102d2101030403200d02140d14045d10b822801d0710004009005a26400d000c40082c00e00600300802d42c81d56410000d441543c03c0d100c8440d00d50030809007800f24140091001e00817504518901d1001c42e581c0d00a000030341c0410380c02d90085504080c00181c0c11034100e4414284100c0d0801c0010381c030414400103000c51030507000f6034821006400d2407809030341c1c0003600c180c1c441d5114801d90b61001408440340c1c641120690025404051000201440e1b0815089081283c03040d440900401549062400070741e55506c607046a0b580c0203400003441c08040307401064800c007001d4040110f010554010941400c01e003c010401c1c1900811704111010040c851100400c40e0010a01c0c151502c6643e0965034208004480c450b03074a805000d0414803604040003801001c2000400028111000000d0f010b440050085000b5520b000d100c00d817140c2280074180b10b0703e030301400c00070804440140c040e122075802811138100d0850600100000031400d200520040c0080810 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 330300827 1250 330299577 330299581
    0xd0c0e04180201090503190b04111507050c030309130b0a1701090b0a090b07110118120f09030308060d15050a091506060203070602070f02030111042603030403050c07081203 76
    0x14152210640c440c600a0340314440e031007d54150040719020055100750040303169240c07400d100303092900c100e4840b64170031070b4410148869903c010050454612540030303a06d4000291082503107c3c000c024035260000e000c1661862151026440b558002800a00300c4a000362100d10141821103030302d9107581d05a555045500501850a600c542c0c8060000001d111082c01035541c02003070030700640b000043c072148810700c02040c00290444865080e15419520a0301041d08026036810880e80c0e009000c24101ca131000d400703601c50085071062740e4054136400401e4030341c041445000b580249050392007013019002020704002034001d040c021050500c01058482c01d5081050b0025420348518280303a203805002c010841c0c01000b40c81126400c120010307180d02003030410444404c18a074000794154605182a0351000000c0080e0042e1800c0e900c05000507483d45050003a2208240c0b182030745036105100280029102c1d20040c030800c4014002d4948655a40315007500e4003c50714452081c030702c00841 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 330302077 1250 330300827 330300829
    0x2070b0912011e1d0c0f06070f080d061502010c02060f090c030604060c020f1c0e12010c0314070203091c03020f030a020a06180f03031d030d050f0609010501050d0c0e041802 76
    0xd84e100d044100700090a81448507100084608400c188028080c410102e865030074400c81c1a050080a42c0102c001c1d80c0d50711012883c4001072040340110f54108070011074840880b40b052055080008560f00105a141c58145040381141c0000300803c1c1c151054090940d02a00c05001040c09203202d581c010540010000001e818400341c1508007882d0b43c44201d0044149140070804040d40d2401d0405048600c90680402d6440340341942c0f150302e5601b41803039a030b01c4541c103900039556240584580d071071603280e49030101d8503071003980c14040d402030302066040d1000001c0c40000c000b582c46801200d4003030100c0c540140c110341200714810b0158201e82d11000c10700240d03005091101444d141e4040c40000c081c0d5075052030349403081c400350800d40d035858030014088c2d081c003100300340c22024411661140315100350305010380412140c1d0701c80e040f44000070410508001400394140d1302c05850b45400c25800e101800c1c01407981c21988810010204900b00281d100d51050514403c441503900900044d180 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 330303327 1250 330302077 330302111
    0x319051c0f0212030901060f0b070302150c070b45010903081807080102030133020a120c060908030402010f090501120c140301091b02070b0912011e 65
    0x50140e50a01c258408880c1d446503000c5142800300d007a4861164072921604c00e11401441c4941040e0a1800400d1010900301e085002400c2c03a64460346c01c944280d03168814502d0b2440007a100300c14810014012680050710702030310b060740010100740c1c90340c007865450080000c4000c468251910810107510018400511341e0b19200c0d01001c0c00d0091061502e0b9940040242000400c007034080d103030304c0604480c220f0081c0610001041c150000307540300d584811840d6031001c00b4842c1c44140c030101d40e5000e5001d6003400c0b0f90010000303858002c1c0c90311442c0c9403198075191034110660010000184000d8000980074850001d9690062202035201e280c03501c0050302c9004295455024013901c80b40c10419683e0003c800b050030250b8050129800600b28019240640c40001050510b003000c000411440c4c41544042c40344004201d42d180300c82c4448030241d84805180c0a001d07103c80b070420440b1a541803504001040c1c1140c4800020b40080e02e1001550305500c416100032101d45424440101c0b503580 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 330304577 1250 330303327 330303373
    0xa0f08151303030b030a0f05010614030a080d0b0120030316020a020904080f070b010905090c0105041d100308070308070e0f06031f0803040b0903100b0618031905 71
    0x20064460399080030070a2030001240440020100764843c1000c1d203503500e041c060400c4c0b00794400d821114181d02841c00724080c0c6004e000f5000c5041d5505250802c502e40016400c0d48a60084003251401d02030501000c044d000a20039a030610480d0103410044030301014900541e5000d88014580b42c4c00c1c10f1040403110801c06001108540c081100e00c40540c0d5401c1126410030350164403540d41c0c10704040c5442c858028118041c00310580c45000041c281c882d03404c66889104070100380c44004e49504010741721401140a0044e1092840c11804a650741100c146604064490074145115580e903a81c4007199000410840c0050000e00503c400300750445c101803480c03801140d00b40942490180402e41d60b00008007150141c1c10184000d80c2800007000e47c50000c2e1803441c00707582c4e50b16124058280d45a0100c00342c58041d100d03502590050381c0c01403151001441000f00780a10b0280c1501c0031800700c840c008007845d4580182c0f40f256400218500c01003000b90f100e0406003507007a2005440c520350100d1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 330305827 1250 330304577 330304603
    0x60d0c1403040519050c100c0b0606040e0f06040f05070c020a08030c1002070606080f061b0f03011205011e0e0601090c020c1306051027060e0f010e0a0f08 68
    0x401c0c81804000b5002082400c0441542c01103622848000e0810034030b010209060240c104002c244044101940500e080e4155401090750b8040ea44440051146501c0360f40f01c0c0c0d071150401e04e030124100404249410307400200017440800e9640000c284002158010b403401e41c00300b80030145200c04c50a00c070369040e0081000c100a9402c10004000494951081ca4104144a580021001c0406c030440d03011401424440c0c0c01c85250038003080b000e03581c841d416645889a01420888040c010010404485581c0000341107103095900c0d29144c9a02081415001ca8040d5203460480440010924001c0c1d142d10700c500000c03404601001c0e001d030030300c0d030181c110024090074405020700041d000112540343c0303882034914142000c00202003d004044603000580d1000a004c091181c01c3c0c1e100c403a0345c4045854809900311140c050800244a0301c0610a05000c03641059400c03a4030301e0300030b5860803141d5043c1000d0305000102000200b00d45001c0c0c00c602c80030302899505004450042200e80c0007461 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 330307077 1250 330305827 330305867
    0x1d1302180a0503060c0a090f080c150405030a110414070f140f161a040302240609010501050d0e061611031c020a0e030a05010f110405090109020c01060302060d0c 71
    0x41031502003501d42c10000c1c8070142881740011100050340c410004c05005190f401030480d20142c9a02030151501145c4e407016104e8246800c11a401c1c5c2c0805044800f1190020020704078000c880c1e8441c0700c0701240c0303012603a00c10b07918040302d0b800501965444d4495841942c40c4144070f07400c90006020203110b20700355a840002881003440da50f06000854207000341c030304094840e84080b441c2882800340d040511030101759410302480304054001854041803501c154030100c04840b43c4101e060b03550307001c40704654031002000042225500135070042031051654070003c603603a01d01e406000c0c501f44082d40d040d400c200300c01951079009640001140c0203007003090051031400c20758100081a588080304070509055000440b268040c0c09019500305542001d0156005030686003002030081c6008158020440d0604440601e80c0307c1c000110303019580020401e03510340c1d080c00801e20007900050f2244005d90b42c0c680d00480540c1e200e201505044400300c00c08114010740b05c100414039581c8104028040c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 330308327 1250 330307077 330307079
    0x60a0c020d0216050d11060c01060905061e0111031608070c17060703020a091809050c0916030f110f0d0e0705010905191e0f1202010207061d1302180a 66
    0x400803440c0300381141e401711900903546511341002103102c050780c4441030b8800400129602c0c40041034100204072850104200055940d43d8140211042202c0d5800034440c0f4451107146198090001903060051402c00c1741d06181e0703404584c406400050b00c0070b580009000c12140204460001007801800950042070310b2a8000c54000c0d0b42c45401400520034560042001e61010b0b1140750110000c0800030102c1408800e0000500d004180c24003003610b0501402c10010a00c2c14071001d114000e4001d80038801e40100010000c40041c45102d4801c00001c1d1030302a12400c2d8a0030304d000d044840d10524413691758455000041d0102d801e0381c81d240c001c40d00240307006c20450303800c40b41e4401110000e5800101c040341407010421080c41d030782c0080744031100285403440f03405414088d180660340e104002005543d1034180030f0182d420641d03402030060f40045810711603240b040d13036484810300c500c0d0b500801101d542000606246984800f0400c03059004c20740d001521481715511880710020380c2c84030212 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 330309577 1250 330308327 330308353
    0xc0405130903090513020715020a11010603081b120a030b0a0e0c03010302010503091006060e010e15030a0b06300105061303081605030f07060c0503010f03060f0b03060a0c020d02 78
    0x80c05241c8030b1948113000c071507004052198160115201b83d40c0c002c1c00d1403280304238005a0340c02504502d5503800018403c004100b441b1805208000c2a640c00c501c2c113500f4246000d034003089240f0914080703e40c80c0a141804c0d110517080501034031601005460108440342c950302801090b2a83d070344140050b83c8040244400d16501c042180d041d03070340a203410f0740c0d2556680c0d50310385010440c1e0340c1d031050035192020014a09078070070301c088444042684c0e0205402044000c22826541c5900c039a400040100082012500309170f105640110016000901b00b103403002d0700610540e00c4039208108848070442e101003862005e0a1a0f015010841d13070309062084102d800d012a080c01d00008015100016074500040b8010240f58022580300c000c9070740d00d220301c0211300c0301600701c034208a40140c245403c98450078051b00a0724180e40d00000c84080c03ca10b07685a0101600400040d903000954601c00f02000c1e80b0203201441c0f14480c44400480c8814000800a20b0410441000811174001841c15a0a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 330310827 1250 330309577 330309587
    0xd0803010909061b080901061a030a0b04290301050a0203160804062705011104061d06092d03032a0c0d2d08030604180204050c0405130903 61
    0x55807810440000c1070381041c60010014140c401401d002c04804d801d04086880c1c0c00641c1d144142c0e10301c0000e006032603035645003076043d44851110040324082070001602541c010b0b03006402c1d42d1030080021845005000300000840d805008400d000074005043c2891424240662034010020207802c503e140b41c81140e161a051051418104120b042008034061041036048000400120300000841013204a03040a401c65141800c96040d420711080d0b20100c00c4050542d030450341251685000080c2c00720003141c10103009240c07142e000070103020200d0241c9942c1d11048080c059003084060301e15000180554034881d2940681c0b0036032042106074040d80e0740140008034044c2d00810400c4102504403100c0c03d040301456840c4e000881c0d85988010306c030b80540d0401043d0080d0761082c0c0001080c54101512146c034800103490340324104042045402d091340040c1d41009420f08107005170b400c45c0d0001e0203545054559850002001c03800b0f1010780b130985040c0c04009120081003041c4a00c65401400d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 330312077 1250 330310827 330310829
    0x260d050a0917120408010207110f15071a100509150a050613091103180a030903080903101416180501050306060706091208060303120109020a090801060305010204140d080301 76
    0x1020803107101000d202d402c104041810000c4000d4015291500d80c001503000350041c7c441a10741c105011180140d6061075600700400c80005401c0c210b0780d5060f00d507412200e03807107a20101c0d4002013464100c0c106080c000d003000d009030741d0a0805220703603140108106182401514020341c046c4d03004124030382d42d5100c140207012148281c4142e178403050034011072480b11259901040e40d03113041c02401e0300035000100046109107419940a1140c03200b183c1013070755801e0718000090109404100600204426402510701030100400f20b405400d4166440c0c03081c0c0d915880d201907001200803c0c0081c1c0100d014070100401d42e1481c1500540c9074140781c482e540122780c800e9505001c00000441d140b905e415045550050b001101448110010710380081c201c8200e9480c680000ca408010a040e86800b1003101c000c460f100040d0350b11079081c032401030003d50000c0c40040034040c01a100003440b420a00601c0015405400016101d61400761151024a030300c00d00c0314400c40d14200e25400091100043c0c0f4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 330313327 1250 330312077 330312089
    0x1090608060321040b040306240b09040b0d1203050108060105010f021b0303040b03090f07061106280603060212060a05100503061512060310051014030304260d050a09 73
    0x80e0b0340c1c64503d41c0c460710f4807864203d42c501580008011041c00300799004010040c0c03544c417010048200400b0300d000c45c0711603070059580000040182c2d900ca40380540020130700744030040411a26031103c0d035a840202400c00c0460012a445100401200405001040c010b110a0812421100641000940780c3c0280c14800c0318041c058a52141c041d101001564050500107014507684c0c14504413243d81c8009141d0141c40c0307486141c0d4045101c074401c40400b40d030038002c10000c0c074080d2a0b4580075803407100c0e0340c9442d40b01c0038102802205003000e00c0c02004000e5000e030000580c0e40a041032540740f2400014607950040800003810452034a41800c4115403144070700c2c00c0c607103c2d111800003655002c04200036980070705022034070098401c40c0d507500c1402400200c0c110765402148100070341c00c2e00d104070340c407001c41107250307404010700e44452590700c0c00c0d60300c01001d49241c076440c0c40607180320200c00002c0611008200d080401c03a610100440352011001d030071b04d28241603040340020700d1084107028030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 330314577 1250 330313327 330313363
    0xf14120904152c01080a03080105211006140604052d0d123903020c0a08010b1002120301050f0f0d050c0414100620060f0402010906080603 61
    0x14900e21441002c1d0000a00207040b02d8409150021034070900c100308514080181d9100880002402d840c00a03403103201643c103840300d2801360300e40810441d0040d00015100401001020748030501d00042c0040c0f226000d4041c0f00181c82820002e4424405481903082c0d40911005c0005008684c1c0d51280600c020090300440400b04c3d03046400d04009040b01112281c010f6154100c0c0e10410126020301035030700f0119039a01c0c012645081c0380d48a40307100640c044000f03588000c54a801280700000c0842ca0074080e0044949500440e00030270080f03822544594940e03550360003904854a8a1210181d4082a510040000308a0482da03101184018810b49105400748800302c074a50325041c04e0482e00388402400c89402101504109403500140400140304034503003500039501c0103191b10018050800d2244a03600356052010075a200351070030b6100541d2022090360081035003810040c0621590318540014100d0400344009003803900c194000030144040002008100e8500003044403503600a0205 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 330315827 1250 330314577 330314591
    0x203030c070b1b070f060b0108040201090504110417030702040b030d02070e0612010c020105063105070c051204050405061206040b040201110d090810020a0804030315120f14120904 79
    0xa14201e035580f1800d15410800401d416040c0070319502c0b0740003e20301402040c81101034000044540d110111802408035803140810b02440c242603024180c44400c0124840ca05629200503030070340310107a002100340381d000007042c00845c00c080c05004c1350360358181c004100d4070981c0003001e5140c071558098030103103062a0740042e000361390f0410120b0050800e140200019454408004d019200444802c0c0c02030000c01102056402042c00031200c29660360411901e80d41000ba5403000b078580a0401402c0008000341c10002c610700380140ca404038400020141d07617602d001c041c00180c0d40b008110f1441038025903150b004407070340824001d52160f40020114826525440181c40060740c0c1c445445c01ca111701481201d5158000c0707080d20540300c0c40000c03107003008101c4030441d00343d102e89103107000080d0004000c103000a01a0b00002c807032080c8070200341314480c1c5428004a4407401d45505480d04114418404148214403114a0307940081e00d025000c200180b4036096218840c60030400e000e9503507140303 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 330317077 1250 330315827 330315841
    0xe01090c021c02030c0c100f181a030406150e01060c050a0b0106020106141e010f03020702060d050106031406030d05090117091c050309070317090a0915060203030c070b 74
    0x601111049070140c4180b51a0018030080d545d41003071807000001c0c415880c0504082c90030042c1ca40190400799205106031300f80740c10486811140c0c40440300b070051068004107400c404c180c111240321042c0864180c580c5000e083c0390381a141015100300c1d030300d44824014440718404002c0141035619900b84040b031105a40b6109117008540d55018050b40d596030000318225a040d0001c0049824810100c80055070303007003c201c0f0700e0070024003141040c10308240a140325405002611102146420f0040c10401c594020503072541c0a40104200160313030308014422039415204000628103201149240d510f810f402080d615180100070105100003c2050701480e849803a91000549003884c81c1c03419400c1c490100c6940310b0f07107020224005c0298090000001c1e02c1001964419004840180105803864454484c01141c0035140021107104010070710150303c41e030070040b0003005c0414000841c2da40c000326250245225070020001c40d0410400e00c00400301c140c05844a242d00074101c540789484900e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 330318327 1250 330317077 330317083
    0x30c210206150d0f230d020129040b0a08070b0307080a090b0424060b040e1608040312060e1015020a0305070b181906050711100507031d0109050c0a0e01090c02 70
    0x1d2080d81641c0703111801710307120b01c08610740743c10204c00d400a10070b480e19901074003074180300c0c10403034640d600e62120300b13964038586500300d000f0b50fa030013400084c12a07856008240c18400c0d41e030011001220b00100303001c10907900c050840d0307000002c01e10800404889959002c076074a0060005400222100b044101d00c41018602190001458004220700303903031102030490036041441954000503400700014003440341011241803040c855a10301308680d8681c0d0302a10104400080352105a40d612008550600072280040c01042540e240001c0b851424500403040c007858007007401190030440ca03900010307400c00300755021258031500240c2c1d15a900104210400e080c3e408500b0580306602e081d1007010407441422040501521060106540320901a2a90030f800c4811340090303800704821031082c0c0d1140d444a500680c0c6454041520702e44081c0c004800c584841e1a0396046e552070501c402040810001309040d51002c1d54072101c02d51801103c1010904144910030405880d2001707040540d02c24 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 330319577 1250 330318327 330318353
    0x7050f100f0908160302090a05060a12060b0d200a14010806130203100303090b04050904030c021f0e01020114010e0420040f090b0a091707030c210206150d0f 69
    0x304102d0f524121429100504c40141d0b11050340a6050344001c50400d0301e4a0107094892007018001080861403c2c0c21016030050882d8141c0d601651a5400e15159031818010800c081c000c81c3e11b0104851001c02c0607030070f0012010058070440040000b0071050902a242d8080088c2c01d007032084c0b0543da0f0304c010800000f52850f8aa50580c4004200060141c0c101c0545c2d0990b4084c0d503685840c2500c8400b15081c0d8070982c01015801200100002c001910451990480c1c44c40980308540346d002d21030a1240241d19000104045810009490760303a590900c20f51621224402800300154075002d40d10000d410040c10150003501c203a181d00d4000344522090b086140409401001541140341d9540d0007445581070031200144040b0109011041a005811905421100d005685100d682c12600e182d400080d088081c040a07a90105c0824100c0c140c025404904018048903104074140007030801d4001028644c881070842c2030a0b0b840c0e00c5051a001c00150f002c041c40d01d0259490404802082034 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 330320827 1250 330319577 330319589
    0xb0108130c0306060303030617070b040506180306010e01230f120f1b1507230a020312031005090702030d050411040507030603113c0904050309010207050f100f09 71
    0x400c2c81c00410942d048d403040d03046509041c0190501d00014940030380318503961254940550003400148100e16085000300411034980101e80101c003101408641080e1090f4003c0d00c014014400400c50006001c00102c41a060b0340c2e040d0343c100309c0510024100c1508401c107035008090102c00540c0c0d490081004e004030301d009004440e0928012103130390850003090100c45020340416058044141c500c1c0c3c2c2a601921340c0840350560b480d0301411742900028000310048403600ca80300301d1501680b428004815403110b4902c8255680c03400400039440102e09a200318000c2c030004c0c040040d881d40c04001e503000b03020002004216038440342003494500c03104082045d840752621017440005501075114204803440754495841076561442005038440192035881c41e1400e942e0007441d18911030441340d07408a00f90754540f5620380c0d200004289001821542150f2035840042d0140b801c0d81c0405c84440240812505401504010804203c0c1e112000040c5428040c10147d5080f03090302032004a806010 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 330322077 1250 330320827 330320831
    0x20d0f0506060d0c21021e180411040e030d0905061f0e0c131a0a020d030e10090f05060103030503040b010b041a0a110313062a021c2003010b01030b0108130c0306 71
    0x30041c420061603925000c8180d115000e0b08c0e0380c209007001d0340c016240c40707190404000401a03207800103000241200030142412808200921040c005051288101c0781c0e0250004103c5883c1060070b0340d801e42e0502e407484002590010041200640c1202800d030300400b100d06080d280d0306010780007465402c0a400c81d48810303002900c1c2001c8468102c0c040c2c8602c1e81a9800c640742c441c080803060341107031003c02e110341c0c254203d4036400e4868011900055100c078811145c652040016444080c00d24100380c00031800035000106020600005545140c00740c003e03070462a24242c507240c641c2e02c918401d051207404003031011401e100c0c1c840c00b030003000005000e2401566510070205200466440e40c6000b484007080f040d01c03204041d0740e44071074058000209200c8007201c0030221380030081d40c5407001101c0330054203000b085100140c40340e01c401c491004802c510108032604081007500303403240022070904141c90040624011b0b03910501090b042544c02e5816450641c99040542d0004080c1d0400343c4154 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 330323327 1250 330322077 330322099
    0xf0b0f0d0f06060e030c01030c0f180f1410050316080414060a0203060a0e0108031b07120507050406060c0f0b060d21030e03040303090312030207020d0f0506060d0c2102 74
    0x3d0300040c00c0402c0c414118140e07079a941c201c0b801034007103510f249c4018000580410322500154042d2021103003420741d1010001015640d10210304184050350483d18080302040310f502e0b101d040101c0c2d400808a55424023b045241c0000740ca2007109480741440104850320000c40d003845071b05c2d450712900c031140c0002e46234070745004490003011794403e840c42c500485021000164184c4a160b910741a01d0101c0003541ca8400c8118a4031a031020032040b0b6480d50182c41e10014402c1c140c400040c00e003902c20b6024280d042e240404000440d1150f5000c50148881c240700c05001a000d4010b401c80c40358050100004c40e180c0300046041c40d81c40d00c00040024545d682c080d94582c140864405403a41c4c20381e0240702402c403040b156130b01d03402544402008544014418000161604408111091645401410220650000b481c45005503105440300516400e400c6d00b4440709022040d0710100a0354a401c43c03903010703510244000c0b07161240d508680b83c20360003076141c0b0f40694860249190001e045101138 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 330324577 1250 330323327 330323339
    0x160905030a0f14011107170c0a0f0201030c05090f01140d1d06090d0c0605040203010902090115200a0f050106031b14040c08010620010507110105010f0b0f0d0f06 71
    0x791440c408240d0f5842e542c2c440e803000c29641405051140f1007801038142c2002c0c00c60b5a400821502c6140202e0951001e01c165101c01c042009210119030082e9450715455107140000341c00c55540f83ca000040040401000350162038400121412034000e10b0181400903000c80d40d40164001c90311090a61418140c21344840080c8148440c00c01c21450191001038550300c44d41c6076140d41c80c2200d42d0108403035200e02004103503507a0055a000c0e00103000030584041550000e90a40400d802c2290040141051030407003a900401c0c401c44800407003030320f000801c40306001d59a141540d120045c01c119004042004205080d0010b400559100c0080c440c2c01a0101030412000807601415001c200000c1c480807061400d402101b01c40c2c1000e0f15039005603400e00d001110405c0c90b420068a940d800700c51454a43c007003d02c5103622034a072b0766544103650306008403031500350f52041e8000d6103002c81010b410700c90004500112038a40203000038490707640900e4207044015241c0510b0104103140f62640001e94 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 330325827 1250 330324577 330324593
    0xc0c030f0c12020c180717040503040302043806090d1b0323010209090a050a1e06051c05030f0c10020408010b040513050c010e01020c060c0d090803030708160905030a 73
    0x2804104517004035144448108214424104860520000710000119104003000400c01604140504103982c030b0030380c50f500801c1c10348110250302e10000901a6032050001621901c412580c246030645c504241c40c11000601980142048148114042d6510340100302c4a00030b060400c0101e501405c2031720b5501d0409001c0000748403401c804038961000003004580042c8200e070202e40300180680d03465121a0034a0f0010100185500005580d41c0e00308142501451001c04410300600d102007101402c050601c4003000c880e40518448030b4100118100103140070003503505a000c2d5412082d112240100c04c0b42c600382c1908144907070b035440050701141c41c440642020041003000d49041c0700300d46800b42c0c1c8040d54140f03180041c0141e00308681810440d0710400045184010510444000d50508000900154442d4000c203001e580010071075201242c0100c5410000e0031100c02441c15490000d001600c130020041405008801800018100e0303401240301e0005854003508490080d501442c2202d5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 330327077 1250 330325827 330325843
    0x803060306070206090d050702060c2a030102040b0d0917030109050702190f030e0402040f1202180c0a0e220c0806030d1407020d020306131103010c0c030f0c1202 71
    0x10003401000c1c00656540d00010341300b405050014002c0c04455258001141c0a403c5180e00301d074041d0041000c041103543c200700e40d82d075505000500301074a00d031040401441c0342c8019540c41c0680d005101c10013440020b90151500304070310300c4001c1030003e00c5280c41d0281d410400074081d4000000f00002c107201d01c40d940014400c1000d40c0844500e8204403404000b0a0302860006108021412684002070f1007a0111207203080080d00c054105901e880440001c1c04c0c4c10b402c24249400301d001402e080d0300e0000f4511034030071aa04400c02c09820250030081d90381c4100400b540a012002c0c2c540c44180c0c980c56400e01c0818003600320444164520080031002c1d12110714403800251000010418030b00e0007040000c0b164905441f107034005000c501c0001d4640e0043c030001e90b8090703001001940980c0702413040e240300d00c2c6e4494041490703080914103082205918014140643e1401221494858120071000605509030405001003520680202c031a10f040942c018020800b032141d240b00c031900010681c5c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 330328327 1250 330327077 330327079
    0xf0906070b1f0e2a0f0a03050f0606030103080a1e030203012309010915031403031b0405060901120f090c05151c1e02040f09050f06030c09070c05010504080306 70
    0x4081da04002e003601c40300000ca8024581d00f0300c031000110741e038801041c410219144803c0c2581013403201070107402c103007504220308100d200b1100040d40f100142d070602c501c560040c0000010401c80c10000080340c1e103030105010050048a0014603e030040c1e00810540c000c915000d243c414601400d43c0300140a50020b105421050051004001d9201b0392482024030688004d0180c0304540e00e80650180030b00301d5561a1440c115007100f0100c0403584455802051040c0c0304015550b0303003841c0d03014940c007064248507443e02403800c1c030040c4419030f125011121482024601901d03240b114200c14401001040c0e500b0705228500205101044180e400c2c8200f2158102e0700302c0e50316000304984d102e4901c01c1d440d04298030758428100c0c12025aa90344031814004095031071144018501c044039040341d02c40d811001c0003252801e410000103102e4000c0d01d601028800740010142821800709035a41014811948101d9502c000290b11511500701840d0b5550054001d100a00f4141440102ca0340140c2da25 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 330329577 1250 330328327 330328351
    0x70902041802030402010e0f010e0a0f030308010605040b09013605010f0c02180c0915180a05010f141c05010e070c0f031b06110c010f0501060906050f0906070b 70
    0x41c8181c600d1403082d42d2042c0d0b0103860300c40308011940108101802402031003814040c2600c0820f22030b88030541c00e0000381c088001040f1495007941405003178404143c5c4840100242004284100c585030425110b0021003801c061501040340031124600343c2d00041c448625481019503043d012040c1510300d8203e80c401c1c1c076184040c801d4240c08030740099000c800a90451130142c50458044800300950ba800892442c40350700307007487ca034001a480301c808007000c0360a500c08200b00e18031390000300c010590f96078101d5016803003a02e08000a810030068100130070500041d415403030740e070f02d040c4412210362059440102d1601c1082e10603840080c0350030b01038945c004020174005800e06000741c1d0b4244a0680100314621400c03183e580c100c40342032882c50382c6039031810180540b20004480d8040c081d2042c0d03844980359160b40c086183c0d5801c44145041e10f0314194102001006181d80102407032054440501c2c11580e43c1c046442c502181e07116210b416074102000281440c01e001d000102e0038000c908a280e4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 330330827 1250 330329577 330329609
    0xc0318060307320309030301080f03120a02031f08030406030609140c0c0f0a0c15021209120a051504021203030c0a050703121a03070605160609050f07090204 69
    0x140001804202d80400100b42050079003c900300c0d10401840103003012aa40d488040d00450400842d908141c8a40c1e0300d0758408001070003203401c280301448503000e0304001142404846040444808009005003001070340c0040402c94044180e0880e06a018400380e401c40110341d103540031943d82e4401d01c80d50703002138601880070074601c1d5140101d4150019013811b69029494090441641c0d50144101d59200d1203200d0f0320b00b0b0000814400313101118092402901100c0c50301c078406500c460070003560303c00c5412644807404203442c4841541d1071784506a911032082c0030320074a11762030300f825007401409501c02e1401d158a0360181401c4107200758030aa0380089040307000344000343d0303c0c0000d03146210000800c0c41368601051007100982801406858400c0e840c0c06205811000c49540181d0700d55402410300040c400c6080401641c0c005048a10b041460554540e01d0400c1c0c42c0d80c044c500400c802e03214400360003801000c00c4010308440c14203069a042d9565810f9500007580548181c4c0c884a0303940f00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 330332077 1250 330330827 330330829
    0x2030301090606050c2e140a1b0207030308070c02040905031909061706040621051b01140f0f1206040606030203040506060108041e1a1602030a1d060c0318 68
    0x550b10b07403102400c0244000031b1000d43c8203060b182d2903a4240c03d9008551041c444c20459401822544a0030401010f07032030070410b60404c1070b43c0080c0740074040b0030042d00702e05408550005a58007101d8062800c9180c035205c0c00310403200c0d048070740c030069401801e000300d0070113010010009010344160000800100801c83c0e1040d036120039148141d0300801c1c81080050019141d41803482e80c0080700034800a059500d5100085c40f58043d01d4022260102025036042002404c000d2990350340345d80c031b5044116222010008017064042420f83c0f501d0340001c50b2a1864000000c140c0387c01807403426000b9100c1c402880c103510818803c5031228800d80c00c0001c00208980280308890140d50804c0c041c021950340c50303006540c44e400161080350404006500c0601c0481c4903000f03150154032401c00c90b070908940d00500e04140901401604c10113460a04041a46400004496151031a401d19003281450301d0390721441890420109900908000382c07803040f118000c00103200d8006246001000410808 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 330333327 1250 330332077 330332087
    0x305160615270e0a080a0201090215030c0409020d15060c050d080c0f07020307180c081605030718030b070804150b03100e1603030804052407080406090c030302030301090606 76
    0x50318600c91900c04034a03001c6000107a0003403d81044050200d035000c58840e6240a0113a111042500051b551540008110f20700605900f04684c0401d40150542c00e041020445038031440c810440c11035800900340f050080550040140005803230383c002015551804090402c8501420446490261031000003280d409902a140a551b450007000e041c4a003281d808070460303101d01c00599061041150002c0c00c500c0e201d0703909038070b031460410205440c1620140940b10800261155400090b5030381103000541e4071005803944200a85070100e05041c41100d41049a415a000030700309003410f002b0041c078650400802e80c01148541e042c1480f5540c50604d500490f0143c1d009550b141d04105001c280e40e0025400080a0080364020f690b00c3c1d0707011010040b118442584111301003440700d802c1009010b410700444003004d11211640c01e4007500c20410181450700104400e0500c99a00c000c5004e00240c3c0c0c2c000d80c41c1940c009640100e00d40c0b82d050203507580d0004d200c0c0040c068288580820a11300c15 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 330334577 1250 330333327 330333359
    0x10f0603021603030921020d0f0201060e041b0b0c0309011209020901052106090a0203160f0e0a020c0d0215180c040e1204060f08010f060e0d0305160615 67
    0xc2c411850128207965401c6000d06519001a643c01c6c1000c1d0b1041d80e0010074620700006049103030010302e8021003500f0058198030300c5006d140c1c00e6901d0b0100410004010000f80c40d4007a91101245e8204000b50065005010440d0000841c0400106905440e10720000042030101d0090b00c07041c225100307003031100b002c1c1d90f403441c0025080316907000100281d041c001002c0d540c81080c0140c0c0383ca2402ca002921b07181c2102254214030380d5200d20300c00030079410306002e5035122600042c0d070245014280301503240e6070b868138400d4040c02d15524000960403405503050300d40e0b100c07050040d03403100946808003c0d030b900c0d003020700588041c01d80d001150036104084858612202c080011341446120002004000c24224504403014010845150313501c8003914014405402c10b500c1d501c4070f140080400504204058005800005080b0000d110f1607070404040c0401490880f07046d080c02600f8a0211068003e94040c001c011030300149400401800e0740000e00c01401c001001d00f00b159a4031420000304010b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 330335827 1250 330334577 330334597
    0x14150a08060f0405090a0b0702010e0d020105060a090608031606320c03090705120a0c0e0f010f0f21020a06030e120a0f050c0a0b0403050309011a0f0112180605010f060302 75
    0xc40303640c6d000075406828154000c0440c000040c921000c400f550381400445070001d00140d40d41c100300b001e9460f081f40124050100c6150070010300341807104680e945d100e9500702c040c2c0d8000c42e0310358408026554000d04491089030320201e00810398801c622080c6c121030005215141503c0c1c3c0002c1140c5400f000341c0b4403950125000b000c00e94a0442446848000b0a005020340d00446401c0000705040402c044000c00130341e0401c030380b40d140c4030003002d076031203c1a0003c5458003140401006150240070414060314160800a5000000070f0302201c0c54a040c2031009421001c41540040d03102d07015404244c407000300c80240d40999a0b8014904c103035204c0d4824103c04603c407100c00781d8010b0720401c0a0021004420120f0f072440d011034070381110b010f00881d01200054030000800c070509800b80100522564200c181e98180740051002504108071b001c074241c1002140745c0e00440c049002d400007000d030003039940452040d03c55070800001502017401410741901c0790010005810748203200b120320701c02c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 330337077 1250 330335827 330335833
    0xe030120090d03050f0301080d080f070807050c1519151a070203160b031602010e0a03080c0405040e0d08100f0509060a030b070c0c05060c0714150a08060f040509 71
    0x481c502048188a81510241c04205090010545c40f119081c0258060308a0100414120721280001000190000c01440c0c064403007070705214980d50000c0740700c1d030410300c1e07406c0080c2c0380c14907808100d02e800590900140ca035204401840074054003600f42099200020105004041c7d801c800024032540d2885242982800c00c41180c881c801140058021684000c081d984904c0070b550f0012050030603a0042c100e51000007013030180c0313452814158030380040507000030301c54840300410164030303001350714030183c02e0122041c00540701d140c0250407030b009084010400c20a941040c3c2c482c0c2c0e500d60b0340e01c400f1030110f805038011940c2c4034180c0c0040d0040310045100010b40e18100802e008000e40040c00c0c0680141880ca80800041c2d0040c10f00c912030080703941e0f07070781c1c1c880c0080c01c291a01c5c0c1d0382584801d014900420180703400c1e240125600c07050791411b0301c030301d0317800580640400c00e030380205410f1400c0d034030300450080075150f44007540030300480084518400420521041104031402500d40a20942c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 330338327 1250 330337077 330337087
    0x130f150e1c0b0108071809020907030f1d03120108031c0b0616240e1002070512030702030d0e070b0711031609090b010b0c030912031303030e030120 65
    0x464840075041010079201581d400703540d400d5686141c41c01080e00000c285403c043c40034021700c0c014007034503103640607a140c052003900603540100e100440b01030540e2003003548424107490102410f41200600081d8000311052200e5500e000e03940702c1d04165541c20018501c00000603204e03000000741e0700d09528a130209031960404000c021300030b03d441c2d490690424130a1010140103582450780124070b500076140c5018140901c40640b00000131004004015482c1014403c00003400240701c85007202400070059031400d681c14041e2814105001c0c1d01d0081c0800020442c40c5617006c03029144a21003c3c400f030000215002d00d042d19000b042c040d124110381d00344801c2000c03800c440840c500c03105010303094801070f080d583c4030400c0242c2d03541c11248085444000c0001001086144240145003258055061560030081c840c1c5a114045a0b42e00c0384110b041c00050b1100180222000004032000c5d603900c282e924a4040d010045000c0764610030b51a1110350f15143c1e11442c81c0000e040c0c4140200b510300 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 330339577 1250 330338327 330338329
    0xa03170307020708060c0301081519150306020c150127091515060f0905150702130203040302100b03060702060a0c0e0a14211f020c0102130f150e 64
    0x1500010850300452059241c005003101c4d09201c4603000c0c80104c1003090382c942c10a5507a528041002c1d9103010152223890401089286601c1d45d020781c0d401202d000f00710141c2e107020145070b0044a4102603d168800103130380661135070005800d000c250a142c0b00094036a03892200351522101402c1103140b40400058080b071303516581e171103a11600e1081c4d0704c00c5019003801d030464007200c2c020401228a24040802406801d4109002c201b20048500d448001e890030f04c07000c0341803082103215910410300013281640855441d010314000c000b905c01c2c021522868503040007503a600c000c100b03485500303140c407540d05118100803502074403800c040d400170315164480b950618000e14a203000003041040340c5030f420040f5039070b40c0504401441c001840d10b862203906003c00940d11101001c00c9111a074100400c0340b0a10b01203070000003001ca1000c100c900030140104100a0710490030500415480020305000107203407449030809a0707910300300b2400000c3d00c6010310003920480440600110700c80400030299 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 330340827 1250 330339577 330339623
    0xe0906221a06040212040c030303060801020a14070515040605062e0e040b0604030302011a0604030c15090f09090302010b0306150f030f06180c01090b0405010804020a05060309030d0b0a03 82
    0x1109020f0001071800c04946240c103414801510102c900c81052402042456450300aa9001d032498000851501c0004440600140d00000d0498018900440c6400074050144640d038551a841d80d022885450300340f80010040c14221480740c81034410400c0f8544002d480a0418849100e0141510040104c5c02060b6074200010352019030064845217a4001500c0700e101030030041d40b1035000807402c241c480d400c0107500303083c941615025480620081002c07a4141c07840c002101c5514449080510348107000300c488542a811100c0112181d80b800141461994401c00307a407406075008215403e480350405442d0002560503030f01c90b00e4a40040031180c50600c1e040d404040c401030072600900c030854440c0c0e0030141e04550844c55410301e00d03e1000414400d101d071058180003403900c11f081c0c90501c4c44220103401a130081c6030402440900060454903504090009424010101626850a90903d0b5513035800094000d030443c1c03d0030451441410440c02d038200303999004200064400c282003103440 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 330342077 1250 330340827 330340831
    0x1902010509060c070f0b0d1404030c0206180a0f060e01080c040b0c030c010e01091b0602070303080601021e0105100b0702060306040c1809060303080609091506010203040e0906221a 79
    0x909130140b0781d800070b00344d05040c00030001008015102500d40f1030b0080c031882220411107050102010385000c000009903c40191460240e048481035128400340c090014005d90000d5910707080144c0503004107016121003140360444034103507100d13241d202602c40112107940e801d84e11043c841c003003408140200442000a000000c2d21281203908206041c0b400a0a603941d942c40d044081c1d640c1c80c00001400000300700900d40b4103d41c0c620340081031a104000750f66210501c00034003006004000320344168428407a00650b64840c4510920340841b405c043c034000c090940708200c0f0b50400e0500024048521015140500d03002459542503076074400900000e00400308501d01080389890100c00c400b20b003000940301905801c100000c1caa4103500d80a03000701006401e0070701c0354050b5410007041200002c8c0f596540740d103280c502c03d00c0d81c803400c0060b0314500843e082841480740000410191100016006102d072600400c80340c040c5480405004030410086d0024001503400c2030720601441c0303c404165 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 330343327 1250 330342077 330342097
    0x1a0a020a08041e150501050405160e04231e062223010e010e0a09120e010e060408031c020915070219030302061602070f05220e0a05190201050906 64
    0x55506165980282051503884c803503000703e903620010b00a6007403910031990310212000002d050307491440d5001d880b08c1c0c3d8286c034035849242c0310500903e10504680a94034048d5401d458003140382010301d903050503480132420600c10460030400041c91032820401d55400041341c402040c828810310010080607040204e0491425446c040000b641705000007005802000400003108940d41407003c90042d080000d024080d4031414540680c01149501d405c0544180403810711000c2e2501c000c005031102d855070505550310000c02300c0c001400300004402012041014403410305111343c1090600124044d600700030350042841c149040c103210750f64004200720380c0014807550710316030300c018582c42541440c7c1007180180c000d0400e1100c00480621403a40c2030150b400a4240241041060198070243c1d20485102d41102d40d5440404214003102000001c3c03281d00a001001815001e282e6441070058101e0f80b511483d520070f882d50010391034550703205a0503561030b45802000c00c200304440c0c1002d8010 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 330344577 1250 330343327 330343373
    0x2060c1c060b04120c0506090a052119050625050c030903030403060608011416120902030f0f250521160617090a060c0c050a1a0a020a0804 61
    0x20410388003001c0600b0040040080c0a44d06001500e4480d01518050f40418000c0000f404a0005039607031a031014142c07541503e81c000034026441540b641d189520300f82043c24001d20300301c19441c0c41c03d8840c00425074040c600300c0e502d86d20f41501c0915542c1c1c5d80070003461400b09012001060a100f54020085401000101d03414011340000003425540720b0752080310034954450301003080c0e800c28081d0303000e410b107621451071103442c0c11208a92120089040042002074054110000d242107510112005402404a0f120b02102c611910380e074030589601008244140381c110388540f44001d0030705001c0d43d2010408604c05152034280a1509070460120704110b10040040d848000100440c1004003054030b0b141d605e9520700745002d03001c0340e000c9190441d217591b8103080281c082400502c44200c1c7d68040701c0051020070440003240e0602010800505900500c116002071081d800300120080a070340d0130204917503c4031140745007280308481036035012524000000700801c0d220030000c0c10070994003040f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 330345827 1250 330344577 330344579
    0xb210f150303040509220b0106020102180906010f050c03070c140906030604050a060c170a0b040608070b0906130305120301030308072604020301021905030103050106080f030f03060303040506030903090f0102060c1c06 95
    0x41e481e8401d002740c00c24030040c1c3d03000c0340703019040180c030350010415581507071918524141000005c010000d190061010721000040d80012601c08208940c3c1e0540c114120380c0f182d079140c05240b808120075408040c400e20691010980d14a030100b005401a94418002c1510200300e550b6500940000440360050110020418450b140c49034815481008000300000d0800b160740100300072500c3c541c12101003944503120500151044004480b295903049510039191522600a40c3c01ca03500384d0001031580c0200354894404860030350140d81a01e1081d100c20000d940c5031501110701d0032000c25130407003202402c210009040203800010b81c000c0d0010740094a48144d03100c1c0c2c00164548201101c2c0040d00000c01001448420b01c11000904214005014000001c0020350341d02c0c05202d40700c0c80c101c0c03c0003010441c0e41d64104100da00030040540501d4070b9150100c4c280e44c80b6002604680d005908d48030a880c500d6102044203441510211442d41c108026108941c81c042c005200469081d990703240 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 330347077 1250 330345827 330345833
    0x816150c0204230c030c040e2703030702190f11011119111002060c0d0f0f0203191e090c0e0f070f020f070b210f15030304050922 57
    0xd01c2d43c0c00030948120410307004601c6a100011500184454820070040c818480001ca82c03404480807585544078068443d103440200040585081a2001004640d896218402c00020000d180305680f15002d684050f411440c000d0211102031400030300240d41c00000364001082c407d04120140310603d49080644079400304189858107013405010080045401c1310304020541d0f030140c814120070750341c0c11800b402141c00030b5607582e4040c01134400c0344804242c0c440d54800701c4d8044941000402d00901c5002543c1040c50029407099070170303a11380c1c82c40d007031002d401a003e0301031140385007030052105101d240c0c0350440400030082807004982583c580328001540c403c00082c075038021114601103a04a042012010b00707044881c1d0500800d54125030480f0042030030120b4200c1c116120450150346d1100512080703240e10f00224801811000c1040500210400d01c00b1024403c041c51103050b510102e01c4000c05603240100d03c1040e90117066080018841c29029002c40b401c1e2114460300070a0b80a50781e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 330348327 1250 330347077 330347081
    0x1205040b07083a1a030a03080603030708070b16020a030909020912030301090e0c01081501120e10090c120c17010e06012309040213050c09060a050c070816150c0204 72
    0x140024424400564407107202c2002d8801c40c01c0c4c1e0001d18501c4801140380001103030b2510021513015042c06541e400141481d2803d00c12181c002c0e0740418041d9031400070345860061000143d030341003090550074640301e00d440e0001485500440c0c06440e0b0049a81c42c0602d544069840115116040341d00b00b508000b00a1040002d103028180d98030000c1412403c08000a1512041701ea0b010304000014043c0215200071060102d0101c50a00c1c080d4114514030000d44041e110007590f8a038244964000c003042041c182c1d008001013841035130000c05669540c041000d4428101e08058000002800104070407504035416030000260000041000d03010308014500700802648404840c424405c0c145005001010209404078000c0760112010708041c0c000c05d6220291101a81403284e80d04040f420701c0031f01d80280c40c0080310040a16940d019890170041c660342000c0c1290400d031040ca14041203603800842d0b10040c580030000c42800042c41c0101101502400003090000c0c40004841d54000d0b0700c0e64 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 330349577 1250 330348327 330348397
    0x2120703080f2a180d0b1302010309080a0f0f1d010c06061703030103030908070b0f03060d020a0b13081b010f090902040603020304050f01111605120a0c1205040b0708 73
    0x5001000c1c1c441480035a0701d5a0003ca10f840c00344540005d0f01d0400015204140590308406600407110f0340300c1c0c00c3c2c070040c0c00410f0b074032101801c80c6102058013500c640e40800d541b1480c0362659150144050203010030744d0558800c040c4046040b04100c1c4000003944101d44200080b801150040b031030660760210020201c0c4110f42c56020742e0000801841071642151000707009210b0007005005113441e1a100621034069081d0000410310000301007916903940d0442c40d001d15400900c030301980c580e542c0681901d544a4003203c4010f000110700021289800304052a04140000030150002c20035801100c100003d500c0100c14000e0412020940c0303400c620160020780700381d8800503901d0902d030502601c4e001c1c0062800c5010382c1000d4100700740740300100607500314002001c00921100307001d2070214100b6903114100650401c010800b510b4451340324030407016140c010012007464813045c0d102200c0500c1140109a6007410800808001030b500f6401007002182c107802d5210340c80b00c010710b5401c4103014 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 330350827 1250 330349577 330349651
    0x405060705060f01080a03020304051e04141506130e04020a03140106050a090209010207030219080303040b04021002070e060907050d1a100315030609020102010b060a0305010602120703080f 83
    0x420000b031010504903c0e0f014009580051682c0c850581c0c00075640c0c42240a004c0c0a21080b071949200c03c01800d0502d03045000013801444200c002ca16151504035048580141804208450304054100f2004980c40340c4509407400484a041000800c00030901030400ca8002440200000c0420030f081c13210360f20300881f900045212803603c401c1080100e52500205421881084688406d03030300040c007901166810f594400c550b03000329202c91400c07020341c0d100c01c00c00e0000008000c10041c00412070392155100f100c0c0303c0690496014126591141030154800641c0f032000403034000d1034070210f9564050040d00d4030720716005091404409032814241d00d6107081f0700d80743d1918a80e280400d507612110a061804000c502d14210341c80c0003d0505100185c2403d607215441e0040d64400c5d0048144900c02824480c1d40e1400650000c00801c404d04c601801405070022401e0704070003440441e2000c1d50036a0751b25903207407a900b49544041c440070342003980030f5402c5020390701c3d40d140c002c4481c4510b86c9 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 330352077 1250 330350827 330350833
    0x20f0a0b0906061806040504050f0d050714030c0a0f05191b0e090a021908030f04080609010204050609060307030b0a0803040806090c030706050307031806020901032307140405060705 80
    0x2044612039207494005050f0f140310b541e6680e902c540480c3d902e0710f019403100080340d011803103031102d00303002d42405200d81100d9030358091120300c4c04a02d0303040380041040610402c40e51003030390f4031040c44039107a000d43c00419201d900321505441c01b00c0c0501204281c194003070002d40d03440c40c2008002c1410000710700e40031607158000e80e54002c01d60b2903640b100f4000704030304035410ac0c1916100160300d445da1a51780009120303500c03c000049160004146200142c8040c4d42125a101c070300c245055200d4100f8441c00c00c03039100300350002d142504c06000307581c102c5a001e80f40324205440f01c820020ba9801c02083c0400b0195140c4842d440c503a240740c1c00100520600010b107581e00e0500e0610b50810384000c9c2011001c0d44142286051614001030820440d01c482c0f40085c0c494a8800f0101c010380b1003041c4a1aa103210f040c0c003101400309507401001983c0003603d0810126000e4440c01540e4500818203410b40340e081c03000198040e026010309100740c41240303610b516142d100c50001c6c403544c001980954440d4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 330353327 1250 330352077 330352081
    0x2514010c03230603071e080625050903070504020306060702090c0c0c04050402030309060708040902070326042103020d0f09021801032a0305030a0305041511070210020f0a0b 76
    0x1101c0a03103203030a14030b00c12000c0d9020349401c030f011907902c074a1442072900700700e2290f6400d20343c40c00205640010300007680540c0e120b4107050047c0403649029a0191305a01c1c42401d02880a900075011240b0500024002d49419490841004001c2d0001401e403500000100010001681c4020300c8902c60845c0c01d0362182c41d0900d0200302d42c94a64104002c600039440c240034000981d900100303445810104807140d540c0ea074068a00301c2118040c075488000e80341c4c00803420781c04040e0040045244001030803444615610101000350215000307440181860180e415100410340350050380d01b01e11481420094641000311032554101c50542d486812165034072410242117280c00903445069907440501185154150b45030615080095180341310310050414074011a110002e000e40c000b9900881980c2c3c984440b520094007a101c1164202c1c2d5025080c4812100100e01d4843d016415110382c4031241008426401d00000d040265650000d40c41030300744440f4141d104006402070180303d64141e4a4034 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 330354577 1250 330353327 330353351
    0xb0f04020c1515060d09020a030f03050c0d090e13110a0308030f07090305060705031e01120302010c050412020f061e0c191a0411030618060105062514010c03 69
    0x5203005803003018440c5190100c3d4480f13584900c180c4001160f042ca00284e04515480010b04420195000900109014043c0810b154018010b020341421400a41d82a144040402c50301850180a0704140400d0b0101041a403c100b00f00c403040c452180050f030018500d2200051160342403a03204440034070001040200c0300146400c40c54120307480c1c1c02c12007112400c40c0d4505864490050038202004800700006280446240d82c0382038200c02c40d01c2508140d44c61380801040c0c280c2c420800e4025608021340500708521600c12242240c44104403900c004c0c02503400c0095210f280c032540b6500c80c030240003000325505080c041100100062041c41d68840300c52000c581819006810503034404041910440070a8065240d602c495840404034801076890f450950918080d5420320f5400d80708810410074041c0034050000c0e400c4407801c00320307961603aa810410400e44955011002d16040c8111038003038120f1081e007180c2c4020b1242c0c1600700d24242c6503e01c142141c039802851800030303072680590804 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 330355827 1250 330354577 330354613
    0xc090109030c0f081c0c030822060507030b010c021f02030c010203010605041d010605041403010219080106112b1b0803060103050c16170d060e01050102070509090601090b0f04020c 79
    0x3490b0a800c610801c8117000c40000d40b0207058074501a00340400900040d480600c40d0080200c00c1c160864202c0e040803031030810f000142411a0410042417801082c0a0298000c0c6103415002c1e0b4000c00312884201e89090954550103194020425407209000001801200717002543c0030b0203540c0e80384c9455902c5c028000200d4441000030281003608240148031282d841812036003039401090000070350005072030200340280304000180030ba8a040c0c054000d07005034800c100d181260116665801e00d0301500308034907140c8481180542c00c134000307420095421116084284070141840c100b05002c60504070346440d1000110801303d90300b6034000304119056801d0302c2115004038035640c417541420301c52009800e54109050f4007810400b00c0c0c1d0b9004580026481c00c032290000421802d00c406695104080701c000028000d90f4054000d0100c00f06181c00c01e00d40310b1784282e05c20030081203541d28000181008008107000140c0050360024150113903101d50000b007140c0d14480005040550740d01041000d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 330357077 1250 330355827 330355843
    0x50a080604050d09120204021612090e0a1815110d02030f0a0203150f1309150606111c020307060614030616020c01050f0d2a0c02090c090109030c0f08 66
    0x240700361604184031054141c003000c617483c0d9041c0d80c01070750384008141d40100a07002c204002c2118006850f500b0f405071340954410204c903e0003404501c603480d50aa004113481d0340600000003224030340515808101000071910034155027142c005403100300031400142580c44200c40d000c02c190004180006000d22128081e404011a00b0460841c24180100004614000c820b40d00c5041007450800b0700d607030f9044503004004a0a141040854060b00d40060802c61103510040e1043c90f00400040301c9004801419400400030302a020150a80ca583c0d6100c1a011414100718482484900c00003101d81c03003000701030420b1303803000f4181c0c1401c0c0b400c041c0783c180001d09015141c101d100003080c5454001a5404000009003420343d00e4102655008002e0f00428919104550500102e00441040e1242410400301181030703050118041c5078068405001c134a00080d0081c00c01d40015800c0e002a034050880680b05140c000b04443c1d17642c8581151030055080000314007100358081004403002c000940d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 330358327 1250 330357077 330357103
    0x20f070807150f11060117010605100801120303060504111b15070e0d0f080304030f03090804090e0a0606170717030306040e03070501020f0306010e040b030a03030c0306050a08060405 80
    0xd8640c100394850900305407a4030780c0800d01c0101c4090f1002036025102c0d20310445040d00403242c10f036940d02c40300075002e00e00700c04580c440c3d4a413410114031800d004004c5100d520181e01c5001c016443c105140d082d120700300070281c023007581e81c14000c80c0969940c02800110b100e1450040e480748140d0704900d64120895401d03080c00d51006000011161a5094003540003010f820300c030400d403110001042d401c060124006100310000e010010401690001a50050f8003d9071801004a05a4815002c903942040c01600903901031000f000380300c61070703003181220a0f0150145c0700c1042d204c0d550300b01610440d03000310b9400382c0148110039001400b0403440c00101043e007041408090513800164880c84003800180c010303510f0303000103508041c04104451803240e10000840da24240801c0300c4a050700f003911310a001a1049440f0f505600d003600072084040c0008018000b4100c081e5400d0b801888003031216000e160b201c800000b060303600c0300002d4004103080700240210740f40c54588181010456030804c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 330359577 1250 330358327 330358333
    0x1809020a0e090a06020d150e0108150112060510050402210a02091813080d0e0106060509060a1d06070f1401090314071b09020702041406030c040908120106020f0708 72
    0x1046204001a002500941180700103a813003000001c0c0002421000e00d001081c7c20000304002203400d06012030504907003194007039400b0610780388502c01d4203520a10071022085094204000420103c0d40321581003000d407030600c5007855a03503000c0f805030b81044440203000383c0402000ca2a01e034400005030ba01510002c0b08510b0644610001221000540b000600c454851800141040d40f84550b1004c640d4020385901d0b159490011f1000280c070400840c2281ca5081910009043c1e0180c41519032054000b0481800c10206c880704955842d030035a43c4024064404101a01075200c580003480c100380107240d011405141801c0c01810300050f001e0b4400c0503803401400c100820341c0148074041c0301000014055480303034507060503040b40c00b006103460325000f5100360000c3d03800c074550300912a941c0b003650309018200d14100040c442c0c20040302e40da0b8140d0003404003d0060b10f0640d10010615114215640c10300b020341808403c10a4241c000b00e02590040d0380d101e5580d0301c10095040100703052801 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 330360827 1250 330359577 330359581
    0xb01090515121003060e060a0b06040e0403050306010c15060503011401050a150e040203070c26030c0f0418090314040612050a02090409030203130602030c0d05131809020a0e 76
    0x100c24030312400180d00d02d1005140080386000b034003d54200001c642220050181440d0300164a8407900c00b51440500c0700e262403414840d81c1440410340d01190350305034035100140e031030707071003d45040e07000401035410000c06c906220000307515048030031200026580c0005e501400c24040c142103a1940c52000700d80f9070007000421542d500c00b10b0072000e0f0745c004c034485000c04010240c19180340700f903007415a511600100400c44007035070040827200310310f004020111100c0c070f83c40140d2401401000302c0c1c2c40402010000108001405070051000e00341d1002c4c0b0301d1030283d680c01040d842c1810181c8929091741c4412403030080c1341e401001c4440954012407894074043c0b40400191000c4017011802d4030040c0c4903000242002c142d60305507050048050018010100c031440c00945a6000d10346041e01c190905031301181081c400020f4585240700c0700005c016000307411000740d079590802902c036101c00044c035078041161207001460b0445d2846e04003010035558420f10400685600303c0d00482107041c14681 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 330362077 1250 330360827 330360859
    0xb010c050d05070206162d0b040b071205010803031803041202090604020412060b01030f0603031b022e0e0105091c0c0f03080304230604080a1707030b010905 69
    0x10740021001c5103800d207959914030b2031020840500a9004500b0950050112042808858140060710f00c1e600b200c0310480c111503052442c990400c9a801410001851b80002c0014981d00d1001350000445c5c1807d28001c600ba17804002602c00c02d8002d040e450b0004001d01614085007032036017041c10b01c01c0c4042d41c1414104080041d10205800c030292180f070501b0301040d0281c41d2a4110b4014052070888100801c40718244007000c1d01484600e1800a0725241c1440c02c1c0218910a0034141d941c16501e00d00d200100e0004e02c0105103035003034182d0b0702040c80c040c2c0ba0061900e000c1e1f01c800064941c0903540d03803c0018000504212179240c2c2c05414442c04200b003c82d01c0d80d540d854002c49504883c04141405024103010b503483c112038001d1403031001c20100200034400c000d009140300f603104d03409540034032504100d004d4000510f4584c00105074071032000316002500010240c00044002d00d0070341071801d01c0c0392031209a445d0036a08440820f903140c2e035402055a005100a000e84815207104c0000c6082503 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 330363327 1250 330362077 330362083
    0x1908040915031a060f0a0306020a08070905031e0f060112030909090804060813060f290306060d14060114040e060c0307030c09050a1d0a1b0309060b030717010b010c05 73
    0x60380c0f155140040f00050840c4d13a20003411a00c034501805c0c10a00e26260300d000c0c0b000f94450748102006c1100400021100d45c850100c217026034001034043e02d01150001d0f2042948640481c8503003050040184034103140e0010403240d4004c0c4100d07400d00c06280520f04001c1c10070485504a04081030500125102151502c0100c0701166218602095503546213031411806210002c03008008a007890003207069400a43c01048000b08211801120744031500c0581c4128040b00380c4880d00340c0c1140000600b10700e0010904a001802840e06402c5024842070003818410260807205100c0c051044c06282410507116494000e450980201f00a0800940303200c490301000300001d08254030340b242c03160b50078401c0103003400030a03004e000c03500c4882e2519019404410b0750741030b02d2211103070400013030540d2000d030240f085502c95808910a01c1c442c200070403406447c501006075005629540c10348003070b8600708100c03802044ea6180304021940ca00e000b680c2510b803c000144d04020b540c01082e00452404 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 330364577 1250 330363327 330363353
    0x140c030405090915090136081e04030501091e0c05060a020708010e01051609230a0b0304060c021c080f07170901020405031203010e0a0905190804091503 67
    0x4a40203210b5030740782c1045916104404004512084521040c00411081500310200401c00402c4440702030014120b0300401c26840102c1d98402c0381c001c2084008034041200526030704900c2c001468085211443e02c0d80715074000d9104079520fa555459002c10702400c00503c030704e041501400001500506e80703034120074068a0245910802c40001c0c00441c1a000704133400c0208030810090140060026206000b8031040717130071071a8100401000e851017841030a01006039452180344011140400c10784c0070b03103040000030160b00080e40c000c0c080f03243d034140809184128821500460b80c002d141c0c000078204203020711880c42c20704402070240c10384c1d40c0040d100303540101820180301d50760b51046030131140d075080088540308103080202405101c80040d00280151242601156200907131030011402c0351001f4866a210001d080c40400c0e0555103035007020903241d0141c01129030221032589640d5001080b003c01322000000041c040140300074034001d014040309190869042545035841c1c020500c2c001c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 330365827 1250 330364577 330364579
    0x30506091519030b0405060106020109050709110d0501142803150f1407091409070516080d0902240306010f0903050709050420031b0301091502040501140c030405 71
    0x4031410101003a11076048811241d15100401c1084599a052081303103080709580c1034174640162400801c1d12070050150010003a4088010054103250203500001048042c1102d4101d603c208031801196046000c0c2601a1280c060700e01d140329240010030064070f8110000d1000a000010b4000741041e01da4454000c507600010766500c583c180f000381c00010001c10743c0b0501c1d050700d40052110a2240740b1509440b661168030360440c40350301c7d0b44a0386036800380101d10f80d91080ba0080011160380c4601c000d0040440540402c000c1801c003560380381040d80254201210807955100070009514051051500845124107525107450030328145480a100c000e2105050041401c42000302ca031088240000468109040e645019290800304003d01000d880035201e081c070310203140058801420191402100040003130007440c2d00d540c00900c01b04d2600880030341c55503a030b140000c045070100d800143c0200d15580016503031030509001412000300043e21b402c1c001c0041c4220010172030b0000c1200e041d140 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 330367077 1250 330365827 330365851
    0x90602250201121104051c030809060105150703021e03031b04140d140613030914311104080d0203040b0702130603080d090201020f0313090b120a12020c0103050609 72
    0xc00784c82124940701e42c2d80300b15000300c4107580b054150501016070f444898407a0799244520340392420010f071380d4142070140590081d000380c5180c0c409256100245110f5102e030054442d00c002e227075091924021f002240340b500da000001001044c83c413425000488204a07101e1034101420f00d1820700030b89804022660142d400382840388180b00514844c415203220b84000c94000b403508021018410041c58400c0f4003007048000e000ca80c0d4504074503102401c480140030b40404800d4202440902050000c02140010380340e24045600c8003e0302809400c81c03652031032642c0d06c520b484151481c000e030351402c24046410510061180b412408100c0c0c507010740494061910049100c0480010000d6034002072000d1000124102003901680020310707141d00076002d40b00305080b9164a5a16882806000d815480d0011002c2c40410695848140092800b40404e05103030702141c040da00e082010942a50500d00c141102465198100b054101e466002e10301402503041c00701c0172030710801024000010100c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 330368327 1250 330367077 330367091
    0x30e040f0b0603100e0c0405131104350c1e040f06030b040204060e0618040c33030216020f03120415020c04150e13050109060225020112 60
    0x1266980007014001c80003800c496076801d100040074888100392040c0740360044c49100003450300c40d00b8030965040340d81c084d0091064500c11050b107001070000e00705407013000c403061101083d040a200d104e20381c82000f50314011800c400100c04415891030506c8103081643c000040900540c640d1801e529a600c883c852440c1c0c10240b103400900644081c0d006e41084600e881400814000d107580c00c40e000340c1c0291010003100da110340c803952504004961840d0408080b5003001920b98103198110b5105003c0c4e01e41c1d800c110348070f1503004220018101720701071004856051480080c00300c18010789400c46418114075045403d1402c5624503564200070340b144140e8440860307903440c14002c000c1d001101c1034056940300e44490b440c0c0410030f05003c40c0d000510980b0032030030803401c00344034101140c0c1072110801c0030300f4600601c06643c0140100b809420070000222000080c909004110405100c0c00c80541c8132204141e11020b880b40072000c480b2a000c21450320340150340c2001c1501c22a40584101043c00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 330369577 1250 330368327 330368351
    0x5010204080d030605040b0108040c0515070c03031710030c0306050717010308130f0e0103110d1a0601031407080703050601022b020723010c02010e03010c030e0c03030403030e04 78
    0xa008540c42a962409101030880d84294940d1124017600c008590130480895001d0044401d03180485005240f200000c40510861520000289500c03210405051416203669500c0d2108402507100300c010031225606591608440000302e50322600c60f46036183e00910315250f40500707811510014040c2607403072011a0086108212900c8500d100d01e60b440e546580d689003a0300030740d00c5608500c80000800001054170403500d02a101220407442c8007881590854540d026a00c10410a090b8460302868604001500c84031790880c0108101050214a2a1000003d4151a001d140f02c01c80701484070b00300010250028440768000b40c031403800146039543c180041c0d18114040d00c50b800042c000c644655804c41e040380d00c01c400390070715500707a0700100d03034078034924098000e41c01c1d5181c49001d249135030112070b5100c0c100b2850800d00500d00010150000d0012908607010740302100c000a0b103920a554100c50100b1080120030015030040d840c0c20f00d1506c0003000c41803414422846580c45804190361 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 330370827 1250 330369577 330369581
    0x30e090c0f0f09310b09010b0c0c0d0f02090a0c0c060902120f0102130b070203030d0207080d021204050105091b0f0607051e01050c090d0b1305030a050702030f060601090e040501 78
    0x1d003c00507210920380b070b04481072450414403400d103020302d480081c500301c24580e9407402024a840c070003524950480c1d081602203c000e81100c0300700c4d82148910381081c0c1c981e65800c6004000315015071407070a8425154014000403031030042c4025152814009c3d04400e0301d0b40003100b201129085500051480360074030008104a910801c80c0300c291003107070507a00100b00c0c10740c010003244010b01c03c030340c0010b60386010541750341c0034054003e585a0024000c150344206590010101284100406823410b03444110038002c9800c04201c0716880c0c03140c041004200038091103080d81140c1c44800400012240d0440e80c3c20147c40300300004d000b19090102d6943d40c2d03d80c0700c2513400e419400710a40c0c04240c000c00c941200b20900c1018400e84d5802c280c085140d805040044841200028007500310135081500c480251000240908070f0380690769800a000c11005d00c0a0000039170580e42d101d03070790030207401010b1404034207040c1c52805800c00300500a40d0ba810168075002c0790187c80811006555509003580 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 330372077 1250 330370827 330370837
    0x30b040f140f1e0703050a0f0516060f0f0e0906040b011b0305030609010e0105030a0b1306060b0309070b030105090609060312130513020a0905060d1116030e090c0f0f 73
    0x1000b80318504004400100100383c1410445694401c12082582d00c900c951340d03140c803440003034800d400841c03900001c00c000e41e903081c815a001c0c400300c038466190180780c0022803034903912041c006000492240140e5a000c41c02846a1000d407800842c1c08040d100050004d5034050040c40c4103903034642061140780d0080c01c82c080349d1151169280d50303c5640f81000b4180d5801290f0051207941c1d10000890740c6519105600d041e20005070040c42013605550300c810420f803014102d0203214808007030b40d40008880b4050b95000c0c205203043c0313503200e0511741c40c020b18002480e0030136084c0000070b0005021304e4847e2203080d0341c0f248085814011940741c542c0407a0030840552142035a42100140b02441041040c1088040341c0b02601c0720070490100f99501d000324080c006c07103800080c82040d4100700c2890140050200c003801500e000410b10491078180400f6804401c48400120496400100b8550059240c0e00303900820f03601c841107403070005411490340c86605880c0d180140040f42407503056071000c042e01c0c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 330373327 1250 330372077 330372113
    0x60512070e18040828020a1506050d060e0106090e1009020103020403151a040504021e03070f06080a05160206071b0b07020f0c030723060c030a0f0f09030b040f 70
    0x110b040c20036003009403040e4407030890b0092001c94000d502e410714101c080141452002c903409060784504680d80e0010405442c5a210621030303c900002c2820754030325200e00803941c450f1000096010041c0307011402c2d2003099000381d039010b00e4400351448071035000c60b000032898466140045d0300403040c030050f0000c3c087e507080980450040011112044070582c45041204070b4416480d0304030500804002c191541107800940202c0040320303122031190b40a0b08180584001000c1d6500961280510751400e00558030031400a88185d003441581074a611170b20340c001044198110b10f042c1c801e00044d64072100070780300e401001142034003c0c0000d4a08050482103642c030607440140f5051062009585000c8984902c02e54010024003000740d00d00062800100d0340826425910390b0803e440c000d00c0311290003035407900480c042000000012051000b0400c0308840c1e05d4201101c10900002045844404921000d000c4903070700a1011500d2944240d50155003c011948113031388500e0000203480590880d2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 330374577 1250 330373327 330373369
    0xc1203010b070c0e06011209060608011a0a38070206070807060507030905060a0c031e140a05070e040c17161b1a0907030f0503070b01060512070e 64
    0x11070840300032001480300e180034202c02c0040c03d44031007200031518020382c2c0e064041505104002840c490340e81011400700e0081368001800303a500e04035242034540a402a07450449401c0c0303c6402c40c5801050130020349210380c1c0948211202d80f0a007210340c003101d041c440707059510465079000c0b44140011140d5030355018011740e448a807580740007501600290b804856480c180b8002032042d600c0391140002180d00000202001e850b208000001080c189149904240d02c4401986141072078400081e44a180d24000203a10900d00400002548014048501360381c1000b0600407966405100e0111810f021600000c07030280c004419192012082c0d509031100110404004000c100d4810f14a115485072300c0e104d403582c56000c0d503029403003140c8000900e0400070099980c145070340030b0302083d40441a00c0440f90410303125110000c0701c5440f000c2c100c4666000080b54400c010000016a0042401c0c0c00c100c3d00f400c02e044c804038a001030050129040100f208441c0039503075513401000c06d07442040303c04 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 330375827 1250 330374577 330374579
    0xe0312060625050703030306060318030806010c0b040506090c0d0c030303111216031b020a0b06061620040522081c0509010b0d02100806030304051f020715140c120301 73
    0x1503112013561009601283c0f8002c400200903019025158201d240d8412120440316940c1d400e942d00f0030042c0690741002680c40241000440b62880795000e5405100107014501c1c000074a6403030b00080b082890302071800b840032400090384900c420300a80c0d1389401c003c00c007880340c010096540e014160b902c0107034181d0303031061051941d041d86141d88450f40c0c9981c140301c0d03a00022294041000390030594801030780444c2c5404d0200d00048040c035048000184040e2504d80c00c4542c0308130398010742d0403d9500c2909920400a401803e030074200805006490504c814503086003a000c10040c5882c0c0a10f04042003022501004003140403110040350100390142c007a10b42c0d1500341c00400d0b0803501c0d105290320b0035003000c0417440d100910102c4aa4020100b81c0960015541210040700180159030144800e0001140651740c1416151300b12056641030b0f41c0314455400001d1801419910544070800c800780300c030f0540e550282c2c1c000b035400021103a6540e907013440c404440c5008207030b03c104040f074000440 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 330377077 1250 330375827 330375833
    0x20906030103061a1804020f0303090a06050f0d020c030a02060105010806130515060301090603020f090c04061215030312050a0605030309010e0f0d030206090d09060804030c1406040311010e0312060625 88
    0x44c17240c0258000e55048003541a00403e25640e441041c0ca031a0303100040303140c20040301703215138010040501e040c0401e030b0400714480494400c0c0d8100725041100381e080854501e802a604000460041c0002d180003031741404c0103008201d07007245900003070b00c40c05d4807500042c860f802141c1c0004800b01016001a03039a40c3d6910180c0000c20003400201c0c0b06182410000384a45001030415008907160100f0310b24151400714140d449178005212620314644855000c1042e41c44000c01000a6000e516040c0070340d41c00c800904c0444030000c0001880c44c3c58103105100540380003040e030303450300f10a0802d4035000405000040000f100030204aa004480780d490030304240c2d010030714900400b0114102c43c01c0503c6010305a43c940480d01840001909080c0000d0200b8400e003010804135004400031441c24049101c40d50a040c1c0c00c42d400c0e40032450202c80400c0e00c0d1024400e880c1c443c240b0001460500381e28540d80010315401418191003140003040c0d2020003a0281e4034401090a0301d4100744500c00c40f46 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 330378327 1250 330377077 330377119
    0x2209020408010e1219021005010801020a0f0c0c0e130501050c07050d020d0807050a171609080c011209110604081b0907051903021c02180103020906030103061a 70
    0x10092680359420301601942c3d84000007803202d0b07000a8260400d0820111141e440d181d0030b072140d40c110852180100500c803042d031034420203000c0d1940b000003523914600034202400204480e040142000340944020000ca0a0583c5802c15640f911010b0400344c1c56013400c079000b60700d1b01080580300e940b074042841801c003000c900070047c80c0d11420940c0c00703807000303441d0071307a00c4a410341210004905628002401d0300d01ca00010300410f10f0a0a005084c0c44209100103003200044400700b149a1010743c201c8011504602e50701c00604589004103172005420300024008002908048446030712020142c9c1008542c054210011340b01414454640b0790341c22506945607800c02140c2e40b040541c502801450401c1580c5d20b100340c0858490514055500c042c1a100001c150321203420160b0078000c071441d03010320011041040c0d948500242e16489807400200490908100d6981418410003072038155807200c50560f030440f5006000080c1c00110520710303000c803811449283ea80444903010740ca00c0340b1051 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 330379577 1250 330378327 330378329
    0xf01020c070e2d04020102030d18030909060b0405061305030a081206030c0d02011b02190504060807150f0c06020a2d140a090f0b120a0c09060522090204 67
    0xe44449105840d4080c1401503009990806004401c1000001c443c05120a80107a003280c41031044a140051a280728003c48801034190303102c1c40d070440d504400303042d4462041c402820130060b00f04210b41c03030007120a0480c0301d40e00c034140c010003000c111883c0341010100c0c6000188000381c25258129468944440c00b0303403000481240c03582e10358001c2451410005034030262140084c04510f441c9925130010b64030300c42c10f10000c103002503000e071600e00180ca8000910003a0500d0409450055003400100416101c0e80e410000c100d510030002007103884070078042d16a00340210304001c03003501c004d000100e840a00f080b40140909000140c2c0c60442036002c85105040b20342c00b03d5442c2c0e048401200b01c1d0a03003040404804c0010208040c4440d5541c01030300400440312582012182140c0d240c0c4a80d40101607684805400140402c06510100c0100b40c65503020307080e0082008000b00c0408090714018150043c401003100c04514048180e982000f0303000004002c1c44001c00b103035600c00d06200079500c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 330380827 1250 330379577 330379589
    0x10c030518010c080a090f1b05010f02010e1b06040e0106021c050a090b03130203060a0509010b27100503031c0614010c0b04030302040e0f1f0e04060e0f01020c07 71
    0x24801c1103460310203040c41610040c00c580d64864070b4945401100c4800707809a0602600c040c0300082031000080c04e02e051600010580c40818444a85818005091680d900d106c040541e4100881c4a043c4030b0b001c600200303d002c440e440120085550400720304140a01d400c590b211440d22000419500d400141200c60808410383c094010901040704480d54028904140c0104058210500404c8404405076511240b2002a10801c0c5c034a80c002038603181090341c401f4a030340c1d912428080c11400c207000c0d80e01304220590f041101d020080b0680208500801c00100303c000e100c00c003291960b80c0030b41410f001860000d04907034803401d104414259100304500301d25a060f1400500103950001c10300280078010b03058440c1c1c511385900b51907185221000038021020141d00700004100c0c0002c540d142e03401010344404141040c07600903400000081900d05841510782c8a01c020480c2201c0c0c0114503510660200d80031a50413090803031a0300e05259200c55403455400803a003d2018803002030143e00b1102 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 330382077 1250 330380827 330380851
    0x9062b091101030603032118081b0d0c0b07030914030316080105130b0f0604062006060f0418020307120b0c0f07140a020901120b060f0a06140c010c0305 67
    0x28003040150112070703135844024045604801c2081c0b40000c3c4429540c2d07240340310003000ca1480036103c04d06c804120700181c100c40b4400b0206000c0030204480608101e8014040010000c0c500c49102c05001d20070868401003800002c0300010750150322903000240550350249150750b00d025503070759241d01d941003101c4040383d40c1c2d0403100e0b021856214249841c12100d003d004d00e46140c64002c085c00140c01041050b42e0030440e100301070007554980200030002840c5036a0b89a207121040041b81211078800800240c86a0228040c040960384484504103900e0013214005a031002c0317012520580c071b421840203941400703450800216020801c03050b0079070130320400041d405552000140c100300d000e004c02c074001081043c00709000080c9018446611124500200c40d01c0300c0e8103034006100501f090b002900080e035440034900c10400000710031500500101da21240a44050000c540d000c2680e1040300c08000d112581c1100201040007150440c01030b0000a015010200602501605040d2100e500c105 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 330383327 1250 330382077 330382103
    0x5040519080a2009101406190206090f0706081503011517011812110708010603110103050c0304111921110d15020d0e030711130b0609062b09 62
    0x403034070130b0020340700d070590f1040308112508020340f10251080d80c4800a400c00402c0011240c00301c0c209244000b40c40c100d9006102c0e51030f00c9602e003428204c4141c03030752019a1184005110558000c25001e6200c0207100c207000c4203d280e0000a8094480c8030283e094012400c140481d40204100380d01002d070060400a008222441c40200c5491100f844081d0542c0c1d8a07540700138840e80701360b11001410201e0030448040907150380788282168540e41c42200d01d840301a9103810306507051f000e501e50003003169a049095241ca41c4030386001d403d040c00348c180b00e0504d0081100741242c00c2900c61016010030300c20902e159010000b81404507075000740540d030340107055200801c1450000a01b101d1203620090000700c4224105461010350030014100c09520f4480410380c00c52607040016021040c0540c0078421b2402c404070a0006080501d06102c1e021810100c0180007900d50404030b40c0800e81c145c070001e41c3c590a0301c200020804046904030342d142d104403680c4031048015007200f5421030084030189001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 330384577 1250 330383327 330383329
    0x2604060b120304050d0204020c12030108120324041814060a020301180c0c0b1e10050d0b040c0f030b010602070806190506121f06090b0105040519080a20 67
    0x29044601d4184036648100310501a5003070154090880500c080d00243c00e003250081d01c141041d00c208800c61076810044010001800200001d80e5840c8480806a1450400800d103010702c4144001111913903031000340c0c03d041074445a120090a480b2015440741040d100d10780300c408010710034190034040c42404041040c200e210b1007220b04982102c4050400114070f0510400070740343c542c1c80001844913880d13035400454514410306101e000c00082600348035441e00c0100607001c80180c050310544060340410720a54848900c44854103400110f41e10080d6110702e42404103d40c203810400c8030780c42c01d2000000f005181c1c440c40e4140d54080e02074511035070325003958955442d01141c072401d42201e580f140500840050340300603004400901506146804c003800c4c48d00c0c102d50768004501e8009280c002c000d02d0419445803030050182c000c814040c6041500000300300780110b010300b900c00c0d0744034118041011403904001004100a8064485407000384c10b11f2040800d205602c44a2066030345194241 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 330385827 1250 330384577 330384589
    0x2070f06030926070212030c12091008040209240a0305010c020601150e0d140114060a061b06020307050417010203150d021503070c0b010e0907050a03110906012604060b 74
    0xc3e8102c60300455052010765001c00c20307840d9544181807024041044100b0121406011050041c503d0b407004540d180b02000500010310706c89600e00d0100052242404016910b0409045d004080d8a42c9140c070388410007102a410300c4108039155200c0500200001080019000081305021640903580d29131382e00d03001321180b5150b032401c290000705034113080b50880c98031030301128801d03010755031403108081807990381400c407480c9024002001c2140c0d010800030345481c0c0c140c600644024078000f0034001410946495016a002008064580103c0015003203481102990b00503c0748400e10110a89800300c2039000754001c2d91807040342e0327400010f81081410b002886c10a093b80c0540141180082400c29108075080600004100021201c803040071600110340140a04100c0c44003901078242020b03070503d03094040c1d002030301542c40e14608101080710200b1401c034034070b82a5089030711903851000480300d1141c4c80499214090030864901c0c1540a450705d011302c41e078401d032401c00c1034400704410088 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 330387077 1250 330385827 330385883
    0xc0708070f0815090d050f090d060501170a020102060c0717030a0504060605060304120c170414030d081e06060d050406020c0105070203040803040320091602010b0a030b0f0702070f060309 82
    0x51136030b1180030844510b51040c3d00074064611400403146c24000e100002a101516446e001d80340c4039190300051102c2d0841498403203c80c80c42c0c20080c0600400e42d030000c1d4403000d0081c41c1c1d50100e40301080301c20501050400640c03e900d40c20541965a00c1c19403201c0005000c2594161100384c41d001010400d800d01b401164040e942054000b10f0181007000100c3da969130070201103507070491500310100044d40f02c002400181060305004901c3d075030120b0034540741074a844400010044400140f01641d80840c1c0c030008100c0f107118912400c1d555200215201d8412050158407040c42d250400060145d1075001e0402c0741c020354004e010545a0400c00ca0782c900480c001c003d03040d0020001000040c031001151501682603640d20110048260002108014116008030700b40000c0703441c0b030000c50b90a110703c280380c1008899005d4014216202c50403002c0b4014140c012400301c840215444c94000c012101c010b104210b05214a035031580e030024080c10040e1412900c0d07289104000da00101140400b130 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 330388327 1250 330387077 330387091
    0xb01020a0f061a0303040906170c0f1c080a030c0e030c090115030608010905061605040b19171612230601050c06040507050109090507140c0708070f0815 67
    0x11201c01e01689980004100756507a0b612040d440c1041c0760010344090002e0001020b807150002105d6150207030440e84032000c43e55502d031a4102c142c038019a40d46060b5500c001003015076400714220180c1500880040352020060515100816a07599840d4503410441d50802c1d25982c0c5402007003000103140d0307a00c91018003554880b054400600060003605e007615031103c0180780100d103041d80c5603185821205460410ba5441d0009801c00c003c007604103131108001c81c503d142c4689440c0c601440c107070341401000d0681440008441d04280301501c0780080d1101a400800c0b126280d0a24030054020554450103000100742100e18040d0314000c1842620f003044443c142c507250159003038440024034800101507038144001404100818403041000510482c0314500074400309041c400090180901a80100c0580f070911040001c1e665000449018680b51415440e4403041c80000c4141440580d802904491050403800142e21000c0b00a0f20111000348083d1580699114600741507090121513103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 330389577 1250 330388327 330388343
    0x804050f040e06060415170d18080714010c14060f060d0b06190b0d060602070b211005061c05100e0f0c0409020417010605041a01120207060504050604060b01020a 71
    0x9101428560030509101051080550501d5222468002c000031120b0300210150303c485c0d0016800c03038010300e6000b54271205002e80c000311454000619502c411901602140300d02a000141d820b03402440c0040000f42e103c192a0b04000c0250921035507250200d9480061700c40c1c41c0086000350501020f00d041c0a41c00003101500d80c1e0b1000288014920b5100503140c012400660024540034008040c205544400d07001050191400c04002c2c038060440d0070100c1d9001c0200b08845904010880341c68a000f020740141255030f54005030003010420b1a44156042000010741c1d103011820711804c0009540700d0b42c020403080d1511140b410300200180aa030350301c20007450200e034141c1251441c1d180d0005861412500c0c168485082c142681c0181d4483c0800049505098248103402c0c050800603100965080285046041c01105115a844001418003a408004100d44011501181c0d60070350454018000d42c1424034000313a6440044406440e12440e00610752555840894181207458209610b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 330390827 1250 330389577 330389581
    0x3140c0f06120c0906070b10050303030112140106090e10061211090c0910030b180f0115020a0212151b0d0b01111506010315050a1a0d090804050f040e06 67
    0x402c0384501010702003014424060000e41855039a0b0f400030001140302c2c4504540d542841e6402690140749600018402c2d0010b0005000807110040a1088a50000503001030407a0501c0a180141440d811416649045c100c1a00300c2e0840081d51505030255000c00300f00041e503600d0200211451044018890b4003040140071f41460b003c3c0400d604203007070504e400d00d850f1004000600f01080000b01c50041703622210802070034030300b01000b00c650201c000f1951195240511400504a0b01405607031a800166840c042e02030380300700400c2181581c017500031191040300e032003880e0340c1d81c0110303594941e403646c044006008041741c2e07a241c11010001c400000d083ca140001a980508058125141081000c019514400b1810011143c0048070349140d41c4842c1048000141a500b00025400720244061310801c000c0d162400402d080310807110040c10040d1390100d100c16548100900d11698034100b01c403040900004100400840c1e008840c4200d10740c3d00301e1300b4401034520301a00d6059540280e80 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 330392077 1250 330390827 330390847
    0xd1e0b010e1503030304082b0905070e01080a0b0604051302030625181413050f040b0a020406090e091c020c01090f05061605030408010207060e0105010e090d12060b0403140c0f06 78
    0x891601c5452240c060210a23126502062084814450003501e16500043d010881440041105805801c0490180024083c0c1d40ca41074079500010b0310541c091783d45c4000289290300490900002c943e4002e0aa40039820135002e0554000c00000701e0040808890824428103801030b136850a200c0c01c1c000c40da2401e5844d15290b0782d5140180c000254001c1180505120703245032610440d440350805c1000d460007400c05003030400040074001d04072200c0031300c108024002c450f005602c0c1c908403400b03025001010790f56820b200342084040e021116009920401000d1400d03000311710100641d40a0340c80c1c00110365601541118031009200d9143c00c004100281d854040c03218403281034060003001140e02d065614499982242d05c00582503c00568812000e6000030003070151500619490492610340e0074860034650303c0316220305641043c420450030002c4850201e4110b8030017080f140e030601e1b454070307507a00b4010081c050301806800d9078041c884012020703191041080b940d140740030700f4003418646200 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 330393327 1250 330392077 330392107
    0x120a020109030b3112030e2d07120b07080f06120f070b04180903080f091501060e0310060f0b1e030112050d080103020d1e0b010e150303030408 63
    0x103440d80c070004c2010881c852020440c0c10080c0c00291100340c4d4030070341d0805030506176407140e2090180c00070581040e89800f8240c1c400142c040c0d4001c019140042c2c1544220320400625401d02a071042c58002c8402c00181c44e51480003140d201400703185025069a20100c0448910004450b01211304c806040414081c0c1800b11070043d4000380e4504039038040100061151504e9401e030710143d500b000016040c080c2c8080c0b1101144a10701c500d100707000103641540c000e414104000c00411038400e200d80003030308440040010003140746140b00740c0203241d61942001000c0060051000b80a4458040d120200c4207441c82080d044511003079116010070b08042c016401030b888070400e2010300c403807002c1c00072805542c84001c60080142c44c4500d424030509240090a10320001801c00620100c40f00410243e1900024140c1940d406610200c41c0403600c18649030302d014080c000b4041d0320b0b0001c008558840030100007401000000901e1680c80600ba0400d40d80b444201c1e801016184284005201c6246507 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 330394577 1250 330393327 330393331
    0x2090607140c0a0e10050103020906040608070c0f060203011505210702030c010509031810020d03110d0903020a020102160506071b05060c03070308060103091a0c2205120a020109030b 80
    0x84010380b1911010350340010030501d0b458016102104005003400350082c1c0018025008140a00702542025420030000300c1c240290300ca0101030011607400218454494071034041e02c0380e40706060440c203002e681031820003074109002e802c001e4442440050000d60044007580c0944ea10101420302c840c19440d00003c0100002d0007420543c40300340152246e1400c2030085a1141c20101e0007151281c02041c0190718020a0f0b8001c00d009e0800c04000720b40066004c943c7c0c5041504504000c20b40580d040c8203045607116000860002c0c0380340c0b6980b00b08042c4e0100e40340e6035440c002d03070884030008821070501603038401911500e944880d003000240e00080343c10484400f0480d0342c865110070540c1c1c98020468551052102480c030760800903400c800c058010040a8001c074082c40c00700146241503413105c04801c0500300b405112416400016040c0c000041200c0030302e0034080d11640800406000081c600e400342c05454450b03201c904c25200042400100c00110340d40580d50704024501d5a11105030720100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 330395683 1106 330394577 330394613
    0xb0d050606100f0f03020307020a2001140319090203030d05010315060f060c0f020a0315150e0f130c030f12080718150203070f050f0601080102090607 66
    0x40036032500c0d07404c426030400590b651501c020503840e011080c1401070001d0301700810701720001c10300d580014801400381c0740c050518200340740300c000c10b0004940002101c0580500c0020740003060308045030302c80c00030307095038a094400342d0f501007590801d81007600e916000441d00d130b923400324503c560401090300a181d50714040c140007008200c403900000190040c2e034143c0c000340035542c440146400560740017074150304140c01e814190000d450b0020200040c002240310026864408004051007280203076640d401960311456050101c810100007514200140c680c044001524102d808040ca4040e81d40ca0150300008107000b07010107070040c480400c11618009110702c20303a0315440c1d00256440340e080c03542c030302250000803480c0d400f920314085c05a1890f01c15a8041c8040490407a1518141034292340541c1e884080b464241e10414103100d402c404200004008210701c4108610034502c = true := by decide +kernel

theorem cover : BRFrame.Cov 330215827 330395683 := by
  have h0 := BRFrame.cov_init 330215827
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330215827 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 330215827 ≤ n) (h2 : n < 330395683) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
