-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3545
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:58:20.026008+00:00
-- url     : https://prove2.me/submissions/e35abe30-cc0c-4298-adbe-71af06d021bc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 637410071 ≤ n < 637589928 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 637411321 1250 637410071 637410077
    0x150f1505040603050c0d08090901031b0e070f120209060d0b040b0301110a030507020c0d140f01020903030a0302030405030d02040e0103030801060813030e030a0803070504080705031c0818010f0c 85
    0x203a9640200001c803191480040c0007500403589000301850280b400c0509180704502d0300d800d00c8401c0700490f00303601c0260801c03180c40c1480c1d07000b40340c8080110a40001010303c0a60030140749401803000f458504144201028046105c03001200d210281d01620718150026010685481041320050701030705001442c1801035117007000410b03042c10180620205904444861454817110309001c0f00280001421002180180082c4404a540d00308124a01c41d005035003a550a0303805441c8181408040e0081040c0f13603204200790103440d10003006890944d00e0a040042c0c0700d035150f052981c150f1080000842c2e42c284001404590100c0c0707100e410f41a03034025541e50419a0b2910403d481c107580c1035038850400c4080000e0b820002e4490300400d119a90b0103420307202d111906039079495454000740c84c004041940450b081c414980c00b000850000d00c0210010211045030410040043c65813048103401c004031540040c141c2d0105a00710a0101880d0000b0480c0c3c5580c43e00410090191713803001000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 637412571 1250 637411321 637411361
    0xf020c0d03110901090b030a0e07030602030601020f0114010b1c0603050304032f0607060e010515240307080601110313030b07112802064501030504150f 67
    0x8004030b1000d4829601040e11140407480c201016141e4541000b030252107080e07200c81c0340400402d02485001e008620683c80940c4034104040003905214241c031195007183c0c0351a02c14003c1304041e4540d1030440310b404a010355910910786401c0014980c0300a050f00250401d400001048400030042003201d01034100034600c4403001641c445441c4c2051902104c03c00711303c09524582c0713040c0b0000c0c01d4242c440c4200040318010b8451701400c2d602c0447d00510090203404007080c444c100030500358032402c4c0c0d071007045140981d4040c9000755400050021420410440c0004026034003450800910544001c00c40ba25481420010244009540401c6880d40724480c04104081d000d00c420307043d25468180a4402c1070503580380e07040c2c4070713034036681a0038502d0300a04200050b03100d02c401040305e4050401c1800c4803203116081000780304000d0ba803014510040804c2d032240d03a84051108c03c2d552409203404691030b1618141001c4c5003000450b103403022886e0500041081c4c0b440d82c45144d800e001c014940e01303 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 637413821 1250 637412571 637412591
    0x51b0703050604032c0f01030605042f0a141305030a21080403020312100f03050c03061b0414130203071e030c09050d060204171f020403030c0b06040f020c0d03 70
    0xc1117240f00035072041c0f020880550081c43d864401c40341c2c201c00c2c0c0f042c50005000c81c0d0300da00003070a49000301c0346c4c1a0225010340389a041407140312590058120816038013807401d82c1d410790042031941c08132109000e20380c002c0b501c00c480c11581e8242000921004048852060181c03c00f1681001012800d403415a0601d1040c0d8a50b40200c0f00e1380c2c03203203030190003039400c0c444044c10303200403810001c14030048150020700201c1c407443d45000c101c002e140607200601410000788181860f10b0400703011107500070106000c4040890b0b5000c11101550794101d18250b050920801145030b0b85044440c1c0c0e18014000b00800c03805581c08001e400d00e000800040c80c01d24038118005a0403240800800300c00900c410f60140960705086c40038205036032048000501c4c090703403100d440e0b070604c2140c5900d2005420000c143c0c280030320801d100d8040c1c071034420800c515140c510b40e805090200010b03030041c200703080a80050740310ba456500102610103940400d5540e54201c82c085921545d640300d00c075001c2850201c4501d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 637415071 1250 637413821 637413857
    0x1805040c021b03160512070504020d020405090105090c1c06052e0906050307140702030f01140705210402180f01051002030309100b130f06060e0d1101051b070305060403 74
    0x380d460113440700345041e0920040c44105a208245105c040c8101c032800a0030340c0f0340703100a01c42001c04180050301d031820700c8204108900c0690050f485042c115003070040400c2c2c040304803500c50009101c00c0b007107000c840c01d0020141007140d220301e80c84614945041c0000b03000c9412511141d40ca800c05071380c8801c80800039140402d05024400020300203000240d4400d01038a4400304124803021810305180084d40000c1c42e02d11142048400c5944480220b40514010104580c0003096814040c1c28a4100c4801c40b00400001403101e5102c0c403910049806d40d2034520146018450380d002d81007241c6008400c25040450038800c1d54040d00c0010010101203201000f03072805880b40b84050801c00503140a0180640010190190700c0401780c800c0c40c118844a02caa030300c204030701c030348080740252070424080d00f2041d05000d210301a2100c3d0b10750034005911402405c43c8204d09080c6192210f80b000410711105420a85a0b1840d01c2503200c040309010000a445124602c29600d4203c2000640200 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 637416321 1250 637415071 637415083
    0xc150507120b0414370c0f050c032b0f091e150518101a0d0803161e0507150608120307050721090509090c011805040c021b03 55
    0x803181104003000480c6034010290701d41c91102c4480c04030031003446400c00980317801c090030390600e0140b540c1c0d4803904181203400c462000e10f09400c50070403509024811586507200d00c5a159507611034514013480340080002c06201090700c0d010407908004850034038a5000060944a109640280d55000340b50382c3e044030300140c00c4445500191016140240303e1081025107400740000c0007083c0b420424058000d002c01c0400c6c0111100034006c81c40b00303a000c1404100d801e141c011240510941150403000c0340c2c0c003100b01c2c1d0700f2006d041c0c2500d031003641c10b0204451044011456680944440464000c120b6001001d401c0540c0030b4003802c2c0d9000303d280e0b0007104440d000e20801031765400080c00540071900c1100a1035001141d4103080d0314140071a900c159510303c248990507034480710322002d076640307561100460000d040142e9184c00c2c03074140303144500c0e524040c8801080c1000004c0050034100c1e40000c4010008003c043c0c0240300191000b40017948911400c1903134922940394580c540138600d000030340 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 637417571 1250 637416321 637416341
    0xd0e061f05122b030501050303090108010e150a0b04050102010b1206070c030509090414060a1a0409170f03061f0c1502070516060906030605100c150507120b04 70
    0x8000d40541c5020300340405042e84000c40c900e9405018000b20b109000701d010341508281c5000a440da4003088030000c1d08403081038110502a038024850710030266046440c0c00d0559007080c3ca0f050b2250b40300c1400e1403ca554070700e02c254001c2021040001c007101c0c80c6001d00265a401d80080c401409100309104201d261119090361079840000450581401000a008494000d02d807192400d6912004500348145c29102142c1c484c20503d0307141c106030014000f00d034214025502c00c0c403011011401907400f8a2031000304501c03c40e0707201e862a00b041040c62001c0704151808004a49420310040804690740049540f02d02071165400c01c142e000512440c549400342080e150b81c803640040743c69201c8000110790815205950800001e000309404200d8440b035407541460b450002810201c1c0100044216071040c002c0c1400d21800b07000c40c1d59051036400d0070101900c0c10000f644810b040c98140e06261289a00c4c0c054900400c3c00f04180c0d2240f015031040402d170109120b01c6a000342807000700c401c1c1c151 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 637418821 1250 637417571 637417621
    0x70b0409060918111314160c0c14030703051e010b0303040e07050711060711100e0a0e091e0f010b15070b0a290901090b060d0c02030f0d0e06 62
    0x1015000040d4000210640c4003009400d0461400f620f00c5014200c40d01c502070110358000c2c50b0100b140c0a440c1c510201d1f078114862a10403156010307640c3d0600142801e005141402036078034015101c0d500c00304030007801141c0010848030000d0800e10001c03010410030001003201e50070000f001d4901c0c100001210112002a0306102c2c1545d540300e0110340507082504112101c0440800000c6035a440c1c0340507140c11030003075501d6441003c820003080340c4c0d0755242881001344103002c040c03261140c1d40d0340000c20850b00f001c2010a40d60303403001e494a0800c6c901001030341d41540b40152042c2c4820300050000c00501d6054002c01a078003c5e801003100c4075076120146084124100902c000091140e18059000602210045889614000c003e0b41d081040d166510340c00207800004034461606c514100e00410b01d0003010448003107a8070124400780314000034504c20f2501c2d180c450b02c0740c0d4400c00c1124207001c0441e200c6502c400b900c16004015010100c01d10314039104140208045000c0303807240355a00142c0300d07 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 637420071 1250 637418821 637418861
    0x30f130e15031509010216051b040b100c02030109050d2318190f1e0914040f11031501031a06012312010e041208010303140c0c03070b04090609 63
    0x50881021060060010344c080d5000e03c18000d0071140516002c80c180c5c82500a0b150704114998200310403150303549282e01c140c0c00e00e9400201c0761140d44086c030800c005490140f40c06e280c1400400c0c0544002d0400402500c50307295404c90080d4080309080c0202c18100b078090000c0002c01c8188018042c0c40041c0700000114001c0d011140b0b085111409500059000700c0003c41e55003c480b0700813413159104404800e00c045103013002c880e12504031b50140c808014200505a0343e500c0402d545040188001c1c60b040854154a00b40510424055089032005040300d040c0ca02c0141364000d80c880030b1100300c4003a007010b800c40da07481d2000d49820f44a040b0603900ea0310f1707180c100d402c01d4003011700300d02c8500c42124041121060041c9180d82c001d0191201803042c2141c2d0401d40340180a04801c001703140300f00606440144000303540302140b50f100d0b0218507200c5032103129001c1c8050410040c100c3d203075414814420001000e000c0301c4081c1040b42d8401100300021035484981605070303a00201009000c134414 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 637421321 1250 637420071 637420093
    0x1f030908031509010b13090b12010609020c190f022707021e010506220e0709050628030305090604050409050c0102060a200f0909070c050606040b01051803030f130e1503 74
    0x3d032303c12207015500610301c41181d00c5440686023100c03469040060181d0300091954600385040082c0494044220074150003a8010344416800c0440354500901c92801076000c092a01a2800030b00c07644d100d8845040c00740d01b001580030b5502c842201746000307901c0c583d018005258406100340c500c41d00e07024100304003050050010900724103402420001180d91140ca40160310810405440075141904000485082803400c12514080041800420504078102c007180039030380e51005c40c12290701d42030054880500c000050014025904090741003498400000c0602c42c0001e130314030304480c0c2a001c0c2d4941c0d03225010002c0585103d643e0199080c03408486080d84110403400800041c050210402d00f007601c408009404d0110680d44500002d0b035489030a018081c00748103580d0050b000311010800000c1c20720001c1c019000d225400e8503125001c43c60800203803001e10031510007814108602e0341d41e86813400c943c29000f0050043c0c84a009d01c5200003010010760750742c2e4410385070006001340541381c01 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 637422571 1250 637421321 637421339
    0x20a030212031e04081b0a110a0b0a0c170c03220602190f050d0c1b120221121308010212040b07020a15140a0b1f030908031509010b13 59
    0x303041100c0711301d8100244a18001c4820720030380381b880e404000d44480109814500242c030940c0d0b20940c4035103d488010492004004121403144285003013265004035642010b18885c00510813120b40d94030300084c4c1442c0740b4004002404d6a4041007a541d40d003040c01d49036615041002e018060144c0e0042c4107174036504040d1022850054415503c80711840055507a40e4140307200505150085141540741000700100f0f180301300011803406004440e00c034649807028400031088030b000b07030007804510711214484d001c2003041c84881c4014422500300c218280c0380c1d242e81754841c108008603c3d800c404089040c0b00d060013220604507a00d0700d03200841d1141d0300da00107090005454881507110711581c0710000390445440256202c600b03034002074041700b800350040d4a403200800c8881002d28290024180350b03039411030041036180e01100e10070416500704050f4010007042402401008006c010040c5082680c4c1003030f15800c2041d80d40809599880035803071010f00544d0b050400c1c0d601c03a0b240600a1401d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 637423821 1250 637422571 637422631
    0x61302010e041e020f19020a03080c0705011d10060603090b0c1606060e0a05090a02030d2601090c030c0224100b1606060605040501021c020a020a06020a03021203 71
    0x58006400c2e40343c04044001c0504a902c40e00c00310f04281008507503140d85120720721030201035481c0d03400179140311300d19035074000c090320070080041c030402c5000300c1c0c0c007000d0081c25803007490721b120400403220076400c00c001c020f0381c2c03040b0129500e04210306101010600a00c2070040312049a4400b00808941d2244160201d16422030141604425804800c0d80c01180e000c0c080c0c80c0003440300c0a1564450f0804008078010303203c004000302016405030146400585000605c02c0312610649880086002c98a5494201d50028202e540d0045429000070540d222182d01214280c2440d07102001411400c62003640c035030aa0390241c05d201c551485100e203141108052340380e0700003050310445034101e40369001080703243c01c170302508481e40c00180c030307504100121441404040d04440c1401b500381032500700001e580719006540f01c00d240c1843c095076003540b4000c0140c1842968014280403007292940310082d540e100d0ba00d801c0d001881450000e205c41c0424000312800b600340f0020310707043d0300c2c00d070b240c04d1416803 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 637425071 1250 637423821 637423841
    0x20315100b0a1437031404050a0201320d1a0102060a020a0e040f0b15041a0c0f1507020105010501081e072003071104140105091003080409060503061302010e04 70
    0x242c1a400311000358180b880d01e002c0510382442180c4c10152640e9030003001c844801200d107900211520501000c80c9002a203410701e45d81c2460032441e4015003856030074500181c4120110030301d00b140c8011517100e190030017601034201460010041d01007852102d00041c11064801da0150300a41d01040c49030206800404844005040500c1701c000322102080c00c8075200b41c5404625a920382d80041d075850614225003080400c011894102400d15421118021007051203c185c102c001448410408061001c80f4a100e94a0283d58070741566444100c0d0002c8112440300040d4a014000f240c07540c004c0c401c10b4028000c504e24140c065502c41e41d4034440d900013a00d5a410f1184c0f281ca20b8443c07500c019406260510340d40003550721002c161400300c0d205603401e000103128504240f0107030380c010a007407400d504440d07003128200b003241c80c0c001b102c1106210682001c1c0ca000385c0081c0100394075400d03070801d00884a00303030110340f815503c06203514610358625200a0002e07103030402d070100902d40341c2c000d5034001d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 637426321 1250 637425071 637425097
    0x30e031506100306030c0e01080f060105090604270b0718030f0201030905030c0610091a2b1a01060e0906030a11061c0603020102060117060f070c020315100b0a14 71
    0x2175225181c804180f4a581d00c00c600d443c0d24800188901360060040c1c0f02d6541c84000140500c0d41400006490713000d0040c4410b0141d03503102c00d04c01c200132001040c880d89405e80c0307498000e50130583c05d00f060350200845074100824580d402d1007001840045907041200d8101e5400b09080b0060340c0110080c10303141c08180c070a44024499118030601c2880800d00915002c240a0466854516802d01382d070751030840b440760310082004200d102c2e150012610009090b0100718440d036015a441a2503000c03210b0710252046140c04c1150380400d180308100c034103071407568460b00707600000c010420a144c2d0b4101c9569825030030030744c200c0000580c0752483c0050008001c05590134100c500e0038118100001c002c4449845446503410015540c05015503800b500a01074802c280c40249103005940304006050001c2014891000801c050301c03945944d4205940141516400b2041215600c1e01c45015280d141100401c21000942c84940a003128120981c50721106003008029082d610160401c620175a40303 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 637427571 1250 637426321 637426331
    0x40c0504090807320f060105040c020114010909110901030510050402041e090615030302030f030a06050d11040f020a27030c171b010806040203040c030816030e0315061003 75
    0x122010322a003044000e135504070480d1001e124070203154183e80d164801c0070740c000d10b44241e010140465411b064950546010512546001e000c03401000000c0501d00c000050f1000031070f0070003881e0410801e29001d081c07075000c911078860800100040c20300c80108180d11541d82c0a401844503007010380c2c040d00040002500568103892080c40c803103030b810780410890760746041400308103007840394220f0074091158a06880341155400b0790307244289008099400303000720000f030303e80702240c020101901c0003908105001d421031400301420608040c2301d51055040c0044080d60b188144251100c0c03401c02d607100c20703514540c0c07814007000425207a140301c00300c551660040301168010840030f00034a0405500244c4000c84007510341000140450780001c40d07880e0192640aa0380122500d4215908413230040c4e480d00c039803a010320f210100f5400203010300c101282500d0240d2850401d000c038030b8004e4980c00c404080702e00405445010201500c81b148041d540440c04600b412601410140e00c0c600300054 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 637428821 1250 637427571 637427573
    0xc151905150901260c10050333040b010309210e0d030215090304060c1205070210020102090102120f0d09020d1509110301020c0606040c17010902090117040c0504090807 74
    0xa02c1550982002d06100c4d26441a0b8000e444070340510300c8101c2440307018010041c44c010010b040c5900b44400c0104118020000c1040c1c900309110081140031000c2d84111a103c9011282c4e040600404e600e920076881e006800002e54040d0007156040c591080c121000010210b4910b00145d000c608c85100f042202a4004200d480d001e4941ca41c1038025001008807121744030400c89901d0005002c7c00c0c0c036800c1840100304a940000126204944c00b062065201c40304580c02c4559000c0d806000e035000388031540942e6629010b600801d8085801c1c6c0c20b441e424803403401c40c5042ca1180c8020514911010041002940320f82c1c0c2c48000715500c000c200840100c1d40da210040c120840308204001e19640d403104404001c03400301c08c2e940c2c03044103038000d600b00207070f0445107170b2200743c010071980c021505d802d540c850181c0301c2c1001501219400740001384c1540c580600000a40022000902240d040712024410f0040e440070b061040b948011010720441c14041440060903100c10119400241840114 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 637430071 1250 637428821 637428829
    0x12061f08030a021f09080d061a12060603041a041406010503071208070309170705010306090c02060a0b061c15090908070f02010c14030c06060406080a14120f0c15190515 74
    0x150301c42d0361f00d0003282250a0682c03003601144100d00104020908010404c85480c8201c40564080002c458a0707480b07a441e81840d00007408070742080d0310740d4401c0b8000c2000700000300f01d01e201d80480501c1100c905a80360b50915035640990700602c3c4080320140c032407100041244009044c5603110749800c1503181e5945842c0d045000710652b0820140c0c0084a0a01003564103100e50130041401e01e40070b000c100c405940c0a5181c003009000b0021040c2c0b160908103003500d0301030485025400801c0e601c0c2030745e512040104010400080300040c217040050000540e074059000e002c3c8074503001031809150803001d654148d110f0512120417414003c0e60464030b00416001001080503a0914014541e200030811480d8203004009001c6441a4034017a000e2101003400940b0907840350380b1180c410f544400001c085481c1c070130081c9010391007000000e05c0e441c02551200c0036003140c3c5202d000b11030308440350000103a84031404441008448010030100034401116807c015004003103c55555805510707d4046 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 637431321 1250 637430071 637430077
    0x6071d1210110403030f031802040207050a0b190e0d050319060b071a0708012702090a090605180106020c0904060f050108072102060406080612061f08030a021f0908 72
    0x4035507860104003001819000040c50700700300c4547c0703170030090301120078000344415404240280c0125800304a600801c1401c0024425a5801002d450080c1c9001c42001001c81b084030720b0045450b00304490211800c000154041c82180179450b4181103683d0014840400e46804030120445a225a00083d0306500f050041003a94080c5000e01d51443c80306112148951000d80003804004440004010070740b5405110241c01c011003100310000484100d403680a40601c181741680710400e02d00c0003800c07d085034450b004590301070700c0440b0301201600101030555000d01c01e42015820a048060492078040b050550241c0b2544000409074500642d0314102e80c0240c102007ea6031002009000e540800e11030000c1040f21410300d401010400d50104019000360b00c6074070184100b00000c1115603540c141807a0039203c07081c0c21211503144c075040301c4100242e240c10301403110f4a612408142c490003c0121041c8221940040019006140304108940d0b040f041c0752507880d580e2140c60703000588250003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 637432571 1250 637431321 637431341
    0xc0306240a0801060e0a090c0504171606020303100303031d01150e0604020403020f150912010219090e060f04020c121e030103030c0b040807022106071d1210 69
    0x219894020320407000d003001c03030180c11a000740003c40d1035510940d41c1c2c50115500391040e844000c102d007060f03071000351814015034105400340c48984210b840904000501086424811b900c1081010b60381d59080c1e031039210969092114207503001090010a019410010038040d11180307694a500c8044009800c449a905540301c0c03101e0141d004200101000c41d071150080c0303045030114075140c9180e0004000d403881d020300c0c3e401450b080e0000e82c50102a0300c1a144684400342600203c14001c01d4071074004c2d44900c62014020540461108030302c0d102d0b03404141510b10b120850300660700c1c1c21082002d019007484100303a00039020841050100018403a01c000c004070203030016290380c60104403a6424034000e00d0b04661100c00d01c010000f280c0d00c1400c0703180180d04281d010805846a052207032191280a0002c0e401c42c081e0200c04012144510f44c000003182080b060310303055200c2c20801c407203070244d18521052200032140c11058178035110f0140a100c80319081260321080403d20002c0030741d0381070342c2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 637433821 1250 637432571 637432639
    0x203071508070201060b03072f0708060912091507060b1c0201080a0c17070509030a151b050d0b010528110118290c03100e0f0c0306 58
    0x50100c42c6809011340c201030303d424500315056140000d0018408202002240030040103c001c0d01510761102c01c18641ca10084002e43d8805a1601d0102d82c0d079020a8130a03e055108000c2c0302c14843c0d0003030f01900c030001d00040c41c00d410505039000d449125005540f05486565a600c56075240e6a160040050144410740014120054500014145140080000b034206007811001c01c105980490760f48001d00517552100e4064541c1ea400300c0c0c0f280914050f10f1341600c9500c50042c10b00240520702c4c01d900507009810f0025038081c001a401e0300c2ca07554507500100b60248240e0032034000c2604007840860061410506180324141c5522404041003d5005031000e6010b07250601039010120710428800380c00203002d101088000341100c0d41c203980c005000342100c1c0c94043e8040e500120305201e0041e400c022502c1da410036000c0071042e41d000b5074004009001702c1500003941462030914074451a00b44000c86c1c039554070700c4c07040e4402d6030004180a41c80022407295031080c034910302c0120f1004115403 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 637435071 1250 637433821 637433837
    0x2011d010b040e010207050a02010810030605090c100509010c03050306150304060605190f1e0b031f0f0303080114040e0a050606040c0914040e0f030c031201060302070206120402030715 81
    0x1c144421a4111605051030781d004000c03640102c0d40000d2102580c550a1a1160407603446091a104600c007940008106900f00414851744400004d040c1146210854120040610740c40081c2c42c01d1045e031400c10302160b090f910f6000401e000b1009158800009051032043c0c01a15800b10115801101d0461700d0725079885051019003844119002c900344108041030090782014050405200c1c036105a91101520310b02203004000003801c00c40040c00d9070355109486e410502056000ca46060390031645605a0740e5002404d40780640034031040380d8060b110069aa424201209400740c074030400190025100c0c0f48004000000f001580e50a40c0503001030882420440104405d5441d0b14140c841001220340c02808444004505446905011140010340c0000c01843e241401503040410038140004241c130144103402200804c44c28440e18804c0060b680c0350340e0103400b280a00d0b080070b500440d0510a03c4a545041230b030464000d030008081750240d03565441c04181e800c1c0401003800c00500703d5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 637436321 1250 637435071 637435091
    0x15030f06091d010501060c0f0b061f170601080c0409090618150e0309090106110c1e01080a0e0703120509060304060609050907030209161e0f0908120d050702011d01 72
    0xb84515405010381d854400070380b03001615489141004284060602e107444000b21b00c0358bd541c015070107220748648140c21100d003034902000c0d201000d2107500f01700035090340c030000d113240d80314402a61080d03207410019030604e410082c68000511000000b11840380d9228103507402c104001e00d0302411180b0804404011002c060207803010b0f00c1481c0c40070b80e8640c0c41030000c4801030307440d00280c1d07065864515200600a6102e24080d1070302c000e13032050541120266400c103048641e030040380000701400fa00d07040d02070340300c07001100c040b00c6c6000b44540540e0400e0fa02440000c250080301108400c3c1482c0580c01c19050314001500c5920603981103614a58554081001007500c0c00703a1644640100e000d840002d103990080f82030310f10000c00c90003000e61484070391a0103078000c1c4004481c1e030140000000b191883d011000c0e10002c92200000081542d01310006002034000903440c0210740c0343e0a0340b0381445440302c61000900400341c4554299502c6444145140c10301108819100c4080c40c00461010f442c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 637437571 1250 637436321 637436323
    0x20306030d0f02070509041b1415030105150f1209032a071701141905180a0201050a0e0d121112040b07030311030a05071815030f06091d 60
    0x72a400c00000c0c0b010a558000c5600d801040305411500152031a000130782c3c3e02d00e4088507016006e444456000540c64010802281d444544540c005041d101a04151410701c03003040341b1700003482002e6108400404800d904a08280078200381f180314405c440c01c12034000304040300600e0490703400e9269031000c540c00e00304580c0c143c440001c0fa01c1c220141c00b801502d1514450f1107009600418400300707000304480410440942c4064541d210407160040903091002020302c2d524599080600124100700c041490380c0743d903034014035407a40600000c09070315516500558140e0001c1160078180b20800c40103c03083d86800c100d107842140708294249508242e2800580800079440c0b00251170b5100200840809004900700c40035959142c01d82074548106183c03c4002c0d220081c5a0780c01f0030004424080c4003180d83d00702600500c0c1c1a00c0d95181c0716400c504e0b5070341c81d5a0178030984085114441e5031910440c003131b902c041410301d188903010500701c0c0c6909c13543c02900c21068212688189401303d21180c408 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 637438821 1250 637437571 637437583
    0x2a0f0d080906060d1101140906040303030504060b040c050d0b030c0409030503040b070516020609030c060703080412051602010e0a030b07020a0507050d080a05030901090c03080301081011160302070b04030602030603 94
    0x11a001081000716445e00b031200e114a000c0c060510025003c04041c4207a07403030a61b0080e00c801408140d640d620707454010060300064800b02c0d0068142200b4000d07920f0f06000b00101c040c000c0d9103090500403404d0481020300641031881d50103000700c0c42d0407990781d10f0b00c0c0602124540240c40700d994030b0901c0d241c0141c40e410001c050708104442072140160024050401d84002601100c1268075400504d00080c189212045d15540c402d4001502d00101608415224841c5000d07031252218142c00000139101840b81010781076031200844031000041d03014070301140340c00d0070241030381c0c207200e0b01c1b03650b0000e1902c0c00307541c01400f59100f00790303440801c681001031201624003610504009805980c0c3d00c20a4014010000d060140101c001103a500003548001219504121041c180550301e080c0454140c0c800c0c0941c0880f40100d0401038110f0016005082015081600f00b23403801c0d500d05d50300c0050038507140b4118118080e605000525001c0c040c040c1c4013550044c03100596030f040c04001c05151003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 637440071 1250 637438821 637438831
    0xf030f0915070206070e152a071805090f0708010f20070f051204030c0306050903160b0a1e02041502060408120703240e010501052a0f0d080906 63
    0x1440d403820001e09a60200704d05800070060b04203000001300c4400041c003109003143d400f00000501007880c46150190004840c0362501c4004c15a04070304402041d00e40300c0b8840c2c0a80340d003d141f107512020114410380c0c05503070701c02407032015119070032000003000d4140001a408481140e4444000385d90003074443c810307886856074044098094810021600c03801c0e0141d410080d16014002442e14240b003c00e020000aa140307000e130695803952280750130300c0c01c89000e00090307036820b07d80400501000400422104150004081c1e01280c80c4641d440045001005014803840b54440c003a89122003010b0000c070943d05000c420140c0c907682000581020454020800d4046500c04418007001c110b401088038a022003190780361003030780d5880c407040d8040c02080c54a00e8075540407400054082203c450071038241c441084003480e96980c0c4600445640c0a10030070002240d0050800c1c0e048100503501080c078900c0b8150680c1e0403100013119650030103038222224000300f103124041002c90601402056840 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 637441321 1250 637440071 637440103
    0x90b0a060f0f0b030915040305040f0e0903031f180b0f06070305030f040303111209120306030d05180607050a060506010f0522080709020a030f020a0c03140f030f09 72
    0x5190041e00549000b080c400c000000600001003810300c0d200744010340044445040b025030f1810031b898010510303441441a2084008840c03008188284000d4803540a0441c3c0d070010f40c00c580f10310001e204213a00f0340501081445960500003002a299510508807070b0a1410001d072840c0c0fa00103001e8000c0380312181d5440b4240c204504030010760404281c0350031649143c10200760380d072903241c10741c0103050705d0801ca451035202081a86802d440310b6082c40c41b07200c07440c0648401d0659600803140502042c0e41c11941500700740d42000c2c007030303202c2c2000d45114541002641c0c00c03c90303403501280483c0c2c450310003524160411401d03036003402094012203070030080c05c1c03a04016201d00c000d8000e105008004600c100c3d1160781c5c07440108104100c6040024062030816a110303503a4543d50000254495030a010100e070501440d1280541203100383c4480c0e4201d030715840c049201d10fa50440303100540e0f84d55240d40b01c0b0103000d8a440e40d606207016500c58a5410000c0106080c00301e0010301e0710100506a90031 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 637442571 1250 637441321 637441349
    0x19060f0501110f0a030503040f0605012c010b09060f0f0a02030a170712020714010c03020a02010b010c170c2107020405150d02101202070b180601030b15040906090b0a06 74
    0xf0741c010006682c0c00c2d15815281140c1c9a80720b0746007900fa031010029000e402c4a05050011034100351440301e041e080c0345030303140802480f0030311316501030200380074850100f0850090041c0c42e20350814500500014858003034451801700824101082901f207450303240010fa0012410880d10758000064220080025001242c980b610003c01010b104d0b450038154001500858010100013a03404065510720710f400c0207001c08246188014020341040c00404015802d0030300d40e070055400780c08020b0030a500310410342e21081015491650030743c001c0c1340050340d0b88200944600c1207000392034000180e08100f00840d68a0085004110640c1c43c0600100c028001c40e04105c2c0d07590340d840321030001c180d0b4140c0740c0b000e9035a02c1c40c0050702c0310605420702088850001031900108101c0c140e50b81c2c0f058000c03100c02c10601c07640d1040d80395200c03400d00000b00b06032008000329814440903901007040120051011884505950340c14054840301e0000311031a0070364406100088002d8001c42e00030704544100c0c2030f0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 637443821 1250 637442571 637442593
    0x90603120f0813380a0c03020414191206020c101a01110c04061205061806070804080f0a020f120c0a030c06110f0301030b160e060319060f050111 64
    0x1a90103c0380100800c507035038420380c1a40c41403da01d5440088a4600d81050f00d2028290089403103503822194031032900c1c03401e000700117054001d1013034409941082100004a0703c012003400040988000907048222105400003003404144240e45100c51240b00c026844845410510746084140c50000140c1810a10708902400d01080c041840c94000d2038000f03112008080c1c0d40f428010030740d0866800508000c0b011a564800c0c461040c0154401c10840e00641c5d80c1c210b00c02c41c48044c40c0e1006115403c1600807640c0c1c2446080e8003500140541e080502d80240486184402d5111481010250700410207200700110103100710410a0206010039140000329902c00d5201c151140004040c0000c502e01c0c8800d01049611a400700b00b004d2010315038440e241040c03000315400922007142d00000c1040000d601a58000e00d01c404001d4a807521800e0075101020000c441e0030041a07204880000a106120800d03a80a0f2000a00d6611410790900b42408001005801070020a0f901c0d9840000400c0c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 637445071 1250 637443821 637443841
    0x30909050402150d1e02041d0c040506070303020f0706050109050f07020d0f0e03030c0616030603020a09110c01290402071502070510050903040e01050306070f03050c04090603120f08 80
    0xf41c400d00c2820340303960394584446915005003850f28404074148a2021803a4820b50154014000c2d58100d050741481210864400c1c80003640c2107840b4846088e00340000c000d1401d105002e0101c2512900f0f0260802c40303007680c04e001035040720364165000b5460301300402c8000c41c82d10480d80c00410068040410f842c12140c060364900402025904101c030039081c061800380318180754480c1c0e0705c4c01004d03241e40c0c03003c048000b43d403001c0680d0040440b48404401e4510140240725100c1101d42c0940b290442c149000c42e150000c0164a0281c030565400700620201200f0131b100c0e207402c646c091001d1045040c03e83c1c2ca0501041c18a540c290b000d0381c8104102c1011448459808000078000fa1000d81d59401070720704182040541911003841070304040c14845640c1011001d8001d603288610940000d0784d8840070107649500940e001d50228401c20800b11a8902ca0b8010039440300881610034680741c0e0303032114401159050f0f401503070910390340400e0654603980410b8250003424546042c40071820845144 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 637446321 1250 637445071 637445089
    0x2205030d200705030304080a031e020c1e06031f090c12090507080a0c05030607030623120714090901020a09140a030b010b031009060807092304030c030909050402 71
    0x22801c1c1000e94140c141c1c008108120100141002034160703a1074075520b08250f650340c0c1540300102c0c0418064890200d1180c0003110040300c1240743d90050140d40007050034130075240089640c09480c0a1982e9000320242c03907000086014051a20212200c0c541030100e10b075004485400441c0035600349004006010380c02000368101e026410300014114415180091030000d1507481440e15004808800c2c040c0314001e0800c40441e4420790590707056503150035040b02140c0c050301845507402e10003c510100c04043d80c1c1c1d118580c10014003141e400e61302140c112031030041d10394005c003141c82c07202c89541001d0410008154008241c0f00080d400c2c00c50140b409004880d550042c140ca040040c01d1413603055030f0361250324008641240c40c001c515615000b014070310b41e10445520080580418001444140d18070900044a0a00d03000c0c00b049030516607164041c046001c1d43c101d51140e03100e034002480d07044000050080d031107501e0745c1d04809407900e005000350700c0c2c1c0d5106850503440c000400000d82c0350047d074 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 637447571 1250 637446321 637446347
    0x110102041206050903040e0c04060906020a170a02010b03030c0307060b18070f1421130c1710061214070b0f0c150f071d03070b090a03082205030d 64
    0x450f56503180c074221403540c0150b070721004d414260002030244001c411070040041d00c11964800000311348030ba80981c0d40303181c080401884507101017804410121020302808180c500d620010822656090000b49141c2120341120926000080c5030750801070390744a12050b40c0c20075600141c0e004604400f003a400c800c0200110306012500180c034088610466524540000d51100f180e125199107211a241068080c00d01894401c0100031030280310903803414010003a4801d03442180d1608002400c640ca40403d4410202440350104101c44401a406010f002e8034000c030201c0f402d0040303130a00c0c2259010f0b002020400b6005070300140702c4509884104d42d20009018007541d541c07070711200e0451070980c44034403000c5122241e10501000740c0c0f80c1f40001d4050289541c5010b0005404403d000311500f441d00c1c00c6a250303004d00800c00c006109800546100c003002042c070381415650b501c510fa03450344004410000c000d0b4640e4001e42001e08003110402410003600180220f0310720042c054004035071044 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 637448821 1250 637447571 637447583
    0xb1201020c19021305130803100e1510030b0607060f050609060618100c0b150907030605011b1a0c070201141606110408120903011d03040e190204080d1101020412 71
    0x200041c5140c4505a11b040002c0e804620b0700d030307203180ca06200420358105001e2040c01c0361a00c00403c01d01d50b140c1d02010b803500c000070402404810551010f800400c80149501d400035002c1c03040d000491980e00c1140d08225283d01c01103000d150410401042c03900c0140301c14841d0b44d0504c440786c0280b9001060401c5500203030f803914a094404201641c42d84000e54001b010491441e00300140e2504591001c46541000d4540000b66203503c07006030260350040c05070703600099006c100341004000000d6119032541c055100c40c1c400c1d1461000e102180c01e0200c1c0e505000c5200000c0032411541e21070280a41840403048060a0040c60749c4251442040310601509050311812000b61240d245002c540003042e280b821600c0b00f501c2002c100705290054404a407095183c40d25a1a40c8103032044060003003440100694030341070812201ea00e240c00064445004001c4e507080c040424000340c4024009016130100a2101e5003040354014628181e1074500e00b010b0340140003c1041c1d00b2980001464242d000c2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 637450071 1250 637448821 637448831
    0xd03091511101e09080d1104120201032301030524010f0e070201110c150903072a09090f02190e0106110c0d0606170109020d02040209040b1201020c190213 68
    0x103814aa540f4598050603104540b80c40300e4041048142ca000b01280d181c10361090080c03c8003868802d050f0b010718400d24000c02c004120540056110340e0081d0060040343c060701d004940e0640000003d11001d81084840d90301211940f075000300701c00c00c40340c09106200000100707036040112102a44415114142d80840158041000c60b4002e4100e88241e021310a040794540040d0704003260b80d1018000d90604d00c0015502181881c80003004079000e582e080501c20001040c440d94484080100c02200c4402620750a000300e80303050305005524a00b800760500303c1e111902e6004201032034420b22454000c0e590101010404401c06924680c116a050300b82510f55041a07020f87c1d052090340101c05d81d010220f18680781c2004119480f0505441c40c040c90225101d42284405080b2102080c0c080d5012226150610040c1350030f800400300c910000d0804100c1d6888040452010981c48502d1f94007650080340b1141e10400801c0840b004401c6982180300841040d0040744092220340707100c44c81e4a0710b031 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 637451321 1250 637450071 637450091
    0x42003030d05270c12070806040308100b030112030f051206010f03020708120412050c0307110a050409030e01020c220e0106080f0a1214120a0b0d0309151110 69
    0x8620088003030740c034a0300c04200342e140c48801c0703a40ba202c402003480c0c031510504001c0410000c0000e2406d0607a054034009245980303d41c0c0341601c01c50401010700150f1004000003140d01001d02d00554001d22200c0c1e40d00c14001e41c50b03e0080c0c00c0400411950040000030701c82c1e00030040045d5000c9030001001c0c00d00c030320328140d4a8002c8010788201c1c032002d0005200043d4041840081c04204c074803660290070004401c40100300d086810380310300c10100c40e0f554024040400820fa40c852944416080241442e403070b95600c0d0301003001d80d01110030a402060b2901701c03041d03140d6014030a1113402881103400e032000303004507515a5510044071b01301242d03031907452100142490f002d42c419000b50641808a80000e50020b004d590b5a02f0481c804480700c204643c4c0011032136008190724580c08144028813070030304030411240d404032880180b207c042c1c0c507180d0412610350740300c0880003108103009691b100f04443c00c00502610b482e0403085404104401c90214168841d070202e5801c2c00864400d20110b062444 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 637452571 1250 637451321 637451341
    0x3020408120304080d1e331a0c01090b090610090b0105070303021303020a0314160b030109090c0b0307120509030a02030703111513030e010207030302030418060b0301080105042003030d05 82
    0xa0110454005140890f118034444590343c1ca00c10f08000d1903811f0161108420a41c5801c0305c0c80d00c11240035060583d6180070030500c1c030003c0e060000f0030b44000500b8201035240d0301651003081c0c4058100e60804000c6c030640710146150007000e00b10809041c02104150030009100344505400a410503a0214020814135500b401100045030001c05100f9000e843e4100b001c4d0944c500504112030f88150740341c1c04000d1440030318520840d112005814110ba1170444014090f102c0c5150403078100c8614203010640702080b102560151000e41d5a10210a0740001440c00f1940003030038112003544140490000294004200c400881c3c1c186810341450481d400b080b860300c4089060a0303100b40900d4100b08544040c072201c40b003424003994407000141003810041e42c88041d24000540160000c100510140c7c480e000c507031204001030140065031503524585003085410a8000c1d1515035120020f2205000035141e2125402184182280e80c0e1800c02e07000a0b0740c0d128107041035643c0d0313446400280c1c001103 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 637453821 1250 637452571 637452611
    0x415120c030804080f190201080c0c0307051204090b0a0302030714060c0604080a0e180403030519051005040b0a061b080910350417160303020408120304080d 69
    0x382c407140b519240d81d11180364580b10551a40560454030548090000034198078a5403808603406840350b8040b9180d02d03441e000c0541c00b00d6070f000c180d8482088004000340d0100401220200085030560b25141004502030583e41600d5416101e904840001c2c800744c0c1e4041040001c89280456804101301a84040b41540c000c08681c0400c6000b5030040006000600c1c004101d000e40b15901d82034580091404c000c00b00300c00003500d00950700c07a00001380001e80a40c1c07015802808084108000d488416281410b540381182c0001c540040c00030100902e0416005108460104a4406820900b07002c0028419084000d0228143c01440034800c18000d081040350305007040a00354017011000c081c13016000320288140810b044000d041c00000110a0401a03100300e20107009840450701c541d1110303021018140c0c80404d94280c01c01540042c0e0324402c0c020514a413003034401503100c618020015050806c1a595070100000400c208000150380c90100d07988040303c0a000a1034220802d00c00401603 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 637455071 1250 637453821 637453823
    0x207030b0c031f09200a36180e1207061107060203150f061602010309050106080316140601120201030906090813080f010b0a0e0426090108060415120c03 67
    0x15480081c003013a0b62100e500024002441d5a4402403030125150400311180b082e4201c190010303180d0314a44282c1d00301c1100c0b000500160816072442c0c900740e4060100540c6c020740c400d00301004030701002c0070b48805038003a001200c41288068424001100c4000b040da00c1011401459680d46104070400c2c0b50094068940c000c1c0c2212045481c0e151550100010f501d00e0f09090b4803509090364074629030729000d0202c2e03001e12134403800d400260080d6801034019000b04201281d440d52500d80c0445d041e002007000c2c0840c0c8005540300610105642400710030b142c03000c140241c0c69000b00005002842600a040141c81d42c2841c0000e41120309042900041408034002059180005841403000e5658204442984d1128094440c034500740c105c0e5600300e441074106036800c194014001c0103211440e00f0003680c000c0c003808010140b0042003100b4140c558980d03040c0484100c000c075a0840d156405102d480c0d1001040c3d030f0030000c1103648240b60442600500c200e85a2040c80d842900401040c1041c120081d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 637456321 1250 637455071 637455121
    0x5072601050c0a030f05010303050f0c0703020907020a0b1509040b0c0c0604110a06080103110f01020f0607030212060904020a0b0a05040810050601141314040b030d0c0c060207030b0c03 81
    0x34200000380035450760000580c1e900007402e02401c1c0007480d40700d1046c64122a03045c4c030349902c1c120b0116440100c64005401c503850134010030f080080075803140200759204550170b50103000319000d03c1c5060310810001621361605491a600700b0313859078940040042d0440c2d00500043c11030b556444011110744508025014140994001d110030403c03059071134034118804460440841e91507020444142200340700107001c151a40c03000400b10705185640c0005c400040c410342c1d624030400c0340d4540ca022426954070300029400980c1c0b900c8040307907334206500303e02c00300c0d1a243c1a080680004540a1050003101460507000030b200000d50300035421200203003400c40c20b5480b03940ca0318200c44003c0004440d0b040c0400d4001c102820341a0f10402121507405205224251036401c00203071a07007207840400f4494200f507407000e41d082c80780d404100e01c140344001e903078841c001c01d640c510b003401c410f94648d40107009642c0a82c2061000542002006500c2120b400c0c0080e20707556040001d0003030f180002844a44 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 637457571 1250 637456321 637456331
    0xf030a09021908010c030e100b040207080a09030204140903030a2406120b04020f1603020118110103110a09050d0206120720030a0906030c030f06140103050c040305072601 75
    0x7000c0c0c2d0220368041151102c0c0005c000110500d80141e082d60080700341c49a0541011181d0010000e403540407264024001e4001804c11903241e541c0b02060740428140008209419410011460940074904200011820044883c1000030071240d9a02020340101e511035181c918102012a04002e275440000640c0c40a1030099a0b4107005071406008a801e00540c40c105903a00443d03050074000c071031000705644070161801460190703c0c00c04d0380200c202201155203400010f46030300000010750340c4560050345030080480c0c03005c0000d41129400980310010410038001071401c0794104032070b007003210703411b03034000e946d500580c40010044c0c0f0407486021815000340f805d0200b4194044061848040c107152184130a40c1001070099586c0120075102e80058000c00e4107010a41c41b035040301e00030000c1402d02085400080003681c041d5a29900044a03094440c03805a10030743e40b50140a030017440355110989000c0c00c1d40c40e030340d0b151205402500280341350f901200c8075a503e94068441c0040005008100c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 637458821 1250 637457571 637457599
    0x90405010e070b09090a0501030203030723060117100c0813291b0306060f0901020c0406030b060a1d0c09030f060a05010f1d0a0b0a1a030105090c030108030f030a0902 73
    0x340d90801030303a0318042c030300c8200000c038521b440703100782d90580360000c000398144206a580d41014800304240458088104007244803024010840c2c41c1c0030b00945c03404481400d0300c00a120b8940b040040c4004949810f01030028041500b0800554202110004040130041542044025002031440c00300c02c1860725030401c01d40d091400d000a004a1420480c144100c414160082c0c43d4041078030019445001000a50b0000e0030060083c0303824039060040ea605110b14200003001c40310b1680c02074480e041d000c070070082203180c0000f008000c0c04508140c2c5c409074011002c8031003014402003407010640da0000d81e10300305075800c004c0c0c039102d101070404441103842c0a00410015080030310401e10b0000c0d00c11000b04103c404212030800e600f00300614960159503030650000540380108046800440303044000c501d450983c0a800d007401c2e4041d4079030341d4a501d420203000380300c4d03401010700c2d13120350003803006003c070000202c1214a0741e5600e840c1c1c203859881d038405450044c0349011000f9408400240044 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 637460071 1250 637458821 637458839
    0x20703051605030c0a0b03060103051e0915060d0f0609021909020d0501090905060412110a0305040f060e030604150f230a050601020c060d0f1532090405010e07 70
    0x64402c2502a1848107032a1010f000040300540520a2181e0007071001540030352085d0700407584404981c4242070401481120403500000589a46e41b858002440494203500002c020710b40080c4240c0e9122000401501c410420000305a002088152202506000c0d9561015240510700790300c2c40807441960b03290014002980580d2200740d481d410400000740d130480385e00c60807044940007400392607242e4440d92102414251f88014809008580b07036a40702030f480812003040d103284240c90701640d440c10300d960b1ba143c480d0386521031002c00045034102d0742292004a1601d4010303600201c040103000b007641100c4094110a150040c0181c545103d000768404455450803005004082c00401360300c40b0240a4181d901c100c9503140980c3c0400c507105410300b8810b0043c81c0016404d4000101c00d0030051808040c1c8403404422007010701c007002c0c20b010318440303805c015882c8003080c012020000070108140c06000c100307100c201c0c0316000d01400141444020b4011203210710380b007425211030a898008030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 637461321 1250 637460071 637460113
    0x90304090c1107060306180b130f020703030e031e0c1c03060501030b090f151302040306150b04150c020105130e01170c031009140d050a2c040b0102070305 68
    0x10b030a2441098000a0f83c0d5000b8440c07075050307074031100b1a000d43c0c2d00e0a5903000c0192180403001034010b09001c0719004540d01900c03600c100c22115010150b0f841ea59801c0040c1541d201411000890b0402c100712003004040c000303042091041840115258420044414201390f1210190070807440c0358080d5900c030661603444a029101c0c240c03400c229001369001401540e8034100c0300d64a44584501c00f01d07000d0300302c0c00c081c4400e84000405800000362010410410ba130080d6100b11400340c0c542420025070415000900040d0400c1c0d418941801d00c0e120840a030b00301c500c0e00d44418403040080900959128400b280c402412102106038104d96500d05104c106609118410003140d00c5250040000c0c0b0200701e05018245c010021718145807014104c1000307044004e42210140240082042111300911901c0b202200c980c41d52900c580c41244042c01010b10030b99105540c420102d034580424500980c4e100b0b00400c240c40c009520301d40c810060b031030030101e070304050014402c038403002107820784603085 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 637462571 1250 637461321 637461347
    0xe010c211202030912090310020d0c0906020f06160c1b0602010b0604080325020d0b06040507030b010206070c1518020a09060506030114060417010c021b1305090304090c 74
    0x500c0606504401c0d80c2000c90006480015240e001119480c0e101c0540d0009005c6640b40213041e01c0240c0b0390900ca6101700d920612824100540b1200030703034444d030742200702c3d0b034000c0000307002903c0c00c0d81060442c00c0d01e921008054204002100a8841c100c601c18507080246c280e01c0035820703020329440f4003c41c6608900d48075440040d801e06c6000c0019062440039101101e101000850420340303c25001541c01004448611880309040c032564013503914000b200344c400e4000c140e080402e0a04000b44419100b00820f0340e000d0509004000120ba60b0019209611006900d054030840245141040301a10402c0300d02001034280710044150040f0718070784515051003110700703950150351070951070700ba12500d100711a44201c091004024181c110544116800d90051803c1d1500380c80d001c49100e081d00700200418641c0d9240c070031446040d010413107041e41c502001600314202e000d080000f0103020b0b40d6441944415144c1d004200294420410389000d0032001ea010f20410b28106c01c000e0200c00030070b103 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 637463821 1250 637462571 637462577
    0x260705010b0f060406031a030102040b03070810030b060d05161d10031214042408060a0806060411190206070f1d010518040c08010f0509060f010e010c21 67
    0x1140c04050300d4090082d16120300003620712030804d407502e002540245203483e80341030154141c903200300f1955020b1004001419501902980700c0c10541c0006208140c028066002d01c95200d000340046103586803802e5100d041111800e40c0c002e0245082070600c01c0b0891a2818440e0b03c0c030010405800607003601c6100f034070704110000241d4606420411078105844094040008403417045e10440c454901e0b201c00e80201910303285020344c0ca03140c1d030700c03145000a81c107910b080e400080103222945c0038214a801c044100c0d04042c52a0903d02d01c6a121000903000912a6075155883c040780c02140c07080c1d0b030785408002030044059034102406510340b00225881400198101d05038000f86018195043c4d102c4002d00a07a00b810b81c0d24801511154041c80054a101c140501d4070701143d550b41c080c89030390003070030360b112903055240c035015941e0b00d8541e82006103d42c0514042220b9a21a69000c441850091910842d045204001a02c3c60040c01c8009013600002030a4200701b2011ba04020403c010349035 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 637465071 1250 637463821 637463831
    0x60b04080111120402150415020312090c1e0d020402030112030305090f0a12111608120903060a0b0a08100b090a05040f02040c020709020c01090b0114091326070501 72
    0x8884919840f508511000000c00040801e02508200a420b45c1c0c6807801080c0900e080c2e02d070f600c040e41424201e5400001680000ba40364043e10381c401d10f080d042a030003002401060603860014410b800243e01e41e9510b4020703049512220341c0c0300c904651003580c02800455895031948803d0f1141300c0807100030350101c0e06001c0400c100300d40003d0f100700151146006001d00030055a150f448000c1007030007000412482c80e50384558100241300900c820b494100620b0b180c50700e01400c0d181442c1100740200b5401c0410300c03003052181c901240c400d0f07112004401c000b070340e001010001a017000300d5411a4000d0310491030410410041c4c1d41c010420010300310340681c40e84d90782c209044255030342114014100301e41038052000508180d005100b020399180141c0c0c040a4682d8440001c90300000100320321030b910341c441c0b0001c2c00310040881e07024040d020400c807246c00c034803008610071030780140442c8a0304c4070302c04010080c8402c000f0000d2098040d4a00000c0340200341d00142d40c56080a402558903510f02 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 637466321 1250 637465071 637465091
    0x70606030c0b0408100e030904050106111c0e06030a060803030408070c090209010c08030a140907062601050d030504090c0818071401180e0a0501031a1003080f0706060b040801 77
    0x700c02d6404444e1680000c10002c3c03c12034180001d00b07002d04c41c104a40c071040c441c02e541e0307a030380f0b00509019003003e680324070889001416071460b104902c85540c1c5100c01010b40c00506550180d10795281035030685d6050347c0c944a402850300204080d5100030b403540408814401002000c40090071014003644120b00d0254940895104a102d5400d00302e000c0344c01c04644200044445000d141d1102c0f907480d00081c01e8184828920440c6422940b0880c1608450b1045c042c0301e80020130050907901411118080d6000d400c0540c4210340180902c40c07251400c50782d05800c240c07007003003281d01a115588051052440504d00a13203005170076a040600d5401410b14084202c9002501c0f0b01200c480aa02110740c002900042d0351055000c140c01101246003500032070303d0802003001c41d000d00132452000419600d941450440c0040b61a01850b03156514814800d03100035400d00301090740d0f00403ca1503990180c01c3c40d080c026204905009040e0303824550f0014555080201500c100c0d00110009d10030030070b01c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 637467571 1250 637466321 637466339
    0x210e0406030602220e071d090702010606021203010509060d0c1e0314010e0606040b0a03060908030f07021207020625050703020901090216060c090810050115320906070606030c 77
    0x2038043d4031641544a000181854400c01c5042c00d0050a8071843c801c00250b02d0104d84234420440750341c00581c1d141d8900700416581080100d020002c0c5001c0079080d541041c0c00111415400340c5500c2c4141c4219612800780920725a074000100b045154244441c54203041010081e1414801610309000c09107103c01c00e40d0041c050f03680e10116603000780172240d0361642004000c0c080760780803d1300054040400f2001400601c519900c1901402c1c40d036440e4540010101512200280800119080103646503030003140c1e6402d5036030055048803e0341d10781003002035403480b59a81c0f000c500300141d10048007070706110000c1500d0064038002e0340c414030349a80318420181a0b03c120008000d04d020b401c1140c0d408074119600c1036010102e9458903840c0d103940c500450b85800c044000c480802642c50004221108080c2d4416014400c141001c107403202c0c4812851404a50075500c1007410020241100c0d00081c0f89811a5100d5000410490300e91207203040100040040780402c5a00c640900300c01328810b09 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 637468821 1250 637467571 637467637
    0x3021503071b030504052701120201080a0504030e041b0f050426070f061106090d05030f0a0902090717010b090d030c08040e0a091e210e0406030602 65
    0x81d0a44950700782c00703003107000d02c003040d071090342d080d01000420b000c04a000e81c5d40c80c544072503682c0c03d808002d0380c425008000e114141d0041e40301c884c220101104500060340c04c0300c030613540005c015600040650702c0703003001c1d10500710281907594040c0c5400050781079002e42c503103004c1031001c0742c0d500c0d24140142184255018072550040c0c0b0344a042c3c102c062801d000e0700001c0745181d40400f40039540103075580c000c600108100e80d007189000c101c90b2110b04c02c5400c4104481503224288000500600b604068040e14901c0040d202c07030040790020000840802079500440030055010f42080c0302e80c9002c070002000c140008000c0c50030362076078a000140740104401a942e1401000700100400c021565042c2d8007440c4030784045401602c24071001800c08030703085899110322801140419076100f1481c2c0301785846c08601c140c01c40204100d40703071404200b42020a0311103a43c3c241c01560440880141942d41c3c45500c4406c584c014140314011040142c01e8001c0c0982e80740b1154481c070800c0319985040c2c0212 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 637470071 1250 637468821 637468831
    0x80310151d061b16180b060a0804050a0c0e07020d0806090606031807140909030a1706040207170d0606080412050f1603021b0411030c09040b0d0c03021503 68
    0xe01d11004001c958601a0b0081a4100c6415050980407880d02052800c0040209001405005a210800650080c45c51511048000503000c02090b01c04078000b034103902552102c6410800c16030009010030801300038208006402040805075959209041122004101d4441005026102c03040707400d240101c850600071203004203001e107140d88e074009210307160700001c0c848001d84c03c503012070760100c80c4240807010141c481c00845101c075104040510602e9039000d0103914442c0d00c20420300a0381a440b031240000500d80520030040307500d48000040c040d009551021f00140000c1c00c049200c0c6030b20700c00608a100c102507041c0519942e85000362408102204d02510080307441c4030300d0f01c4481c4180c00174400321251215043c01c098051880c0300d4480080001180941d01661120703d5030746c4840035a03c07641030111000e000351006110b4240e80c50101404050605d0f40109094a1680d181c0d00301c0d000d2020007a244045680b071034100519868500c0c8400e034050b5020081100b80301a004003124414 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 637471321 1250 637470071 637470107
    0x80316020f0609100206060306180604171e0403020301050a020421020102070f09090606050a081203090c0405040c170a0209010608130c0b1e0705061b0708031015 71
    0x9148680c003404500515040019403202040044040310740d110b03002a40b1090302c40c0e00800e054a845010700d454000094140620200040c2c4205a0503a00090386940540c4c00140441501441e401c602d80a00680c0300b40707001c0129540b900c40034200035201034001c80340220024400750321202056012441140500f00b80c60440004107003036100e5942107510618818811111341554a5101c12212640c0e03401400301781e500e40a184084c413103940100d4000c0c010444d02c14075407619002e01c49a40e40300116038113129041c040f00040204c0c500f07100380381050002800c1440030b443c1c0b0f0b01c0c0412800806000300c0a07811420303044008000300014090a0007030307000c1d0103510240d090803810348040714000c2038200c2d14013180030788030000750050b88658028000f181001c1e4642962098010b0301c602c1001c0e800300062420700003003011484c0010b0b841d402c8101100c1905d40070914ac60427040e544030300d00019041d01400030901032a0301d0b41410a904a03030031560b003890f001c7c007a608112119900c0781400f0440d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 637472571 1250 637471321 637471357
    0x1052106010623030408160807170d05060103062105031903090c1401080415020910030b121603031404150509040c1701060e060705150403090e04080d090f05100b01090803 75
    0x6400d105207088560780c0c080c00600e41000459034500d010022b522038194405040450781c031000b440e5500860781c020001f400c040c010a414802c5020401a5082d103809604802c4680201072042c148104c0d07041c44101c0c6186946600010805000762a00b80c0c002c9500b01034040000030081a1000c04982000e0305070f40d2016162669195030680200c0c0002c00c422082c5d0030481080e0f01d54604454040d4900c030b40c0c4010401e40500070800158403040801c0c61415000300c07040201c804e070481c410300240d1381e00d030504542409800300c08100d640100d4100507014074515520b80d401c2c6070010040c14045104a40a208003030844070211550280c000284030074030428801400030718000c000034103c5520142040d030600782c0b15100c8510b064291100107800703111510038002415480040840607040c50010350486041a9803200c4040c0315410380c2185240e0f0f9815903408200e200c0ea80c01140d203422004a9091944060f800c0b00200414019240803c103582c07000148810040706075401c01604250f2522 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 637473821 1250 637472571 637472587
    0xf06011814130e030315090a110706051b0c01021305040c02150702160b120a1515090302090405010213050f060d15090203040f141501052106010623030408 68
    0x4000195140001d111522041001030440f02040510301c501407500104040341d4158091015144001e000031119038101208540c502c5c82c04001c90740c04550018000425548034045107000c21306e14201c0c0c00c0c0480700003c403010003a8054000d040581c02141c4c001403215a03076810401101c40c0e0044040250300a856024012810098044da221960740191030211580e100000110304151304410040070300421040c040000341003403194000800002007010300ca8801c000d08100c0580d10480400708410b03599521850700c940d00c80d10046a01404118090030700c0e1030700a01035004145800c1d00f0300042e450020b0a8902038090310103403000603008500e0110038002c150085d00c012040f8101d1008103020000c1e01100354402580304a0041016078904e000d03502e0460034040100c002180650300051a19040490765a40c075411110103c80d11020090015a081a4801116800002e5010f01000050107680003980300f10200440021100d099940c0c0b040c2c00c2c1d0600060301c1c094100e070000e0094203 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 637475071 1250 637473821 637473829
    0x604120c0314040b0a0e0910030f060b060a090503011815020d0209100906021203040c06031d0a03110c030a0b060405040c030b0103030e01030e011404020919050f06011814 75
    0x400e080c000e10300441070741d034040003000242d8000e602107290068000b40f42c290035540800050b0b60700c0c104032003002c428103040c1400408a0741074000a00914072106400c001c1004a6010043d040b80c003400058a641c03100e00081d221030700c03c2c4103003030083d420078648258282c401039000e404180d01c03010300003990011120300300c029041091803000e5164200107100c3c40365680b204224a0004503914102500d00b04103000341401c1203804407074a100014010301c0001424880040d00f5921a854006081100d40c1d03024150380d0040420070b0818007865030b0003418945c0c401d0b140030342c0c99800da040b18007090800c012301d56180c000103c050200d10b000000704600d071030160045034005006d650304140c821f07182e4039005246602a030040f40450059492590a0350301401360303840144251000b00a41e41c080c01070b0008e80e040040c00203224241d50000241c0c650800108061102040e000c02c01861601195158009038142c41f51804505600039240501c02e441c0070100030707a400c0c5080c0340c2c005039001c0144 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 637476321 1250 637475071 637475087
    0x1020321070306080a05100b01051801030504080702130506011b020120030702030d0207090b010309030f0f210f0e0319050726090f120318030115081509060412 70
    0x1c101050f444210014400804100c0d07006918051405840d40303800510911040b910840c030041c0c14004244240070380044500311ba500d03101c50a0a0101d1136a49900e884880d900c15802c0003940aa0880c02486070031640743e000c1803003410b00780c0380c0064200c4a0f4034005120040d514000340004c0c01e030415030600e0000010040b0b507500e100c204880c1050755990010b8203160f94501d00d0001a8000c0c82c08120350452402114034580083c2000c016010607034500510040214081c2020320006144650b2464806c05094060240c0400c0240901c0c0303015408d080540a082c40c00d41200e0704144841c01e0f03484001c001c03241800600030313000d0401c0070420b00c2519541c01011054502544142014107441c03a00300fa0400074805d01f00c940c2c1d94030400350f170800c03610649500d6054043c80a006c10202d180100100700d401c000d092090300180d81007810000b030701610700070300360001441d80103e00040301440000d800c440501c1091024040b82d0b20314203155601c0200700c034042c010703101c1d060705c1e41d201700d00540d04 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 637477571 1250 637476321 637476331
    0x20105190b0303090d212303060a030813030c050906101b080406091e15050d0e0703050c0112090f1e020301111902030319150f0f050f01020321 63
    0x1580c0c1042d09400001710040b8501c101518050480d03111000740380d5104001000007692818588141c0007030160340541d0061008414a2551000001c01d009a9030103030040003c65000301c0d0955224aa40640c04808010340300440e0320302088034000c625403030460505440340c50007424058000d0b0b4600001c039600303041c8501c80301c07090b0000285400403418040c02072000d04000c3c0c40e411503240c60280401c0d100b08424041d4044002c0b41070082c4009140350f00300009009403494500c0c0c41d01c0c410300b952402405c14609900c00d034402c0ca50004200000420f0032407004000340c84141940101c1d907440400d0311b520a40092150600a4800340025088500f46c90b1045c08051419000010b90340402e084521111424000d08002301e40403408440035001c004030641c95201444c02c8d030903e020800960802d000b85001c155884000901914254007082c000900202480b41c003181d549000d034003071043d05030049038092403130041005840d500000460314940d0100007407400010308020008800700001d44 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 637478821 1250 637477571 637477573
    0x9060e011211150c2802130b0310090c080c06040b16060f0f0504051b0f090a02070b070c020307090c211107080c0c040912030903021005091c020105190b03 68
    0xb900550b1560300007810080c0d034014001d14105c000a00140f11090b55020761907440b0307040380007050050711200d40000f403100c503980c000b0406010300c0d00024180421843d1288443e4901005072003403110091149080329110001c0c0c541c00f83c8ca5105124051081d40501c0188841c200300006241241040a881141c051100007a8142c0801071401c01e41e40c1c50030410015036100c4060005102084c40151640306400c2505c0c85104038040200d11b8040748601c445118600b2003000a94510341d0ba0115844113521030398031a02c600e00410060060a00070905a0007441114004500c408461080300700c8018181c0b101000d000005070034440b520034003100304180c00e40303864100049088003000b400b0010b101d821071903210600010400d19006281071254810f81c01c200c0d030a800302d01c0106602a17046400e1601282c0c421141c10305074607024014562480c0c0703518101c2040301c4450b011446049401140e0b018000c0030840d01401c0742a1034042e10500300d8807183c651052410b60842c0d2050010300340c007030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 637480071 1250 637478821 637478839
    0x18010609031214040e0709051f0318050601080a0c080106030b13060e0f0a0314090916050c070b0c0d0801080303012102090a0b03070f0305280212030409060e011211 72
    0x1800c81402c84d0095401008100c00c13200600c03d13001e422600403c00741c0320999104544042d030150680300d100b030a030b04003000d0596a00305009501510680e18040d45d0b0030200b150b000c1c0d40e4a03400030744d8034190324078240c6010107826000316000b5418003410342100d80254a0154544a117140c41c0c1980c4000c050858040f691080d4a07001004240805203008807640090701140a190601900c0c2550300c15031401e80810400c0004465a43c00e201d954000018042c0500d030040c1040042d502c2e845410b901c41c5080c4140f04001452980c5140104442407144c4140c4040180034001070f00c1c42c0c082030003100c105800500041c4131161629072030403807040341e65401c43c0c550307886600850302020b41614034420254464640c005075040c00c0060100420362014200da126286803101a260340715a1112541036a410803d0f071007a07007800c3c3c24030110540040c42c903000060940c00e0990b0300c5d4441e00c501101a42000030000d030f1a100c1180340380c103d56441c91810a03519041d900c806081d04a1078900d54810300c84 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 637481321 1250 637480071 637480097
    0x6051206280b0309010c03020705030403080f040b0c0309040f1a0f0112110703020c010c0f08030a020f03130c090c0c0602030705121f090b0105090d05010b030f0c180106090312 77
    0xc451000030b05140820703e580b13040c690511401c0d108000e4189003490700410801001800c0001254112a00100c01580b50280181c40801d40d02c40c4e40e00c4102c84000c0404c6c901003a22000c0010000c985044a0401c6125180c4183d0070640d80380c4e10300c88805030b0901d189403009040020070888102d405247c100a207107000702d400c0084801001c152500d40c500400c803c1d08068040107160001d11017400d15401b0701815603118101e400d07590720020805040071000c51180003041d01540e25200401c60300940f01c1c075040c550039001c00c2c00040e0558110301c00420005a06140c1c2c800c031915107859548940ca090306c1c83c4c4442002c0e40c0701030032400802800308181d210060780c2e42d503038a01400c0c18108004507114609400320001680e03800110b0042d01e03014114410780c0c0c206c003c4a50115081e0f88014099510b41071142c01410300804090301405007081806001e01d02040d001c809010481d80030bc81420009500801c2000c00d003d4440414890311017071002c40c00811035045401664909411500c0403 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 637482571 1250 637481321 637481389
    0x21002070c051002030f030a020915040905100b09130504052b0f020303060d0f03090e180601140343030b0a0b010909020c12040e1006051206 62
    0x85602a260380485900510040c68043d140d039884108510041d030824a440c0380c00045840090009030070320b507002462280e60345071710f048071441c1104000519100e031307600d00071500509011a1018003c0608000104642c44110265519504040d2851460317034802c1d40c02c0802044043c000b610603100312a007440f025507200c22648001c03013a00403289696003050001410300c00c6030601044c295003080c420403403107840e41e429001c0690307000a4000c480382c1c0d240c1025074800d111a04070084134000c4000f04103000c0c0034010b02c4003101039034404440c0075070390381c034454118010002501e0340d00d50884103c1c0b0101124000000850100311034407241922181c042d02440c042400d109080200c603010f0080062040b01006654020811300090109414010000f0000817035805118503440e404100c604070310034100030101851080c50102e5503540c1e180c1c4205203100c001210b10698200ca50103010070220b2040f0181c1c0e82c06d0341c3c2e17900322101c1910380f0003c000b40446a056500701a02800a1751803d9200c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 637483821 1250 637482571 637482577
    0x608182d03030a09150212060907030f290103050606040b0c03211617042a0801060504060f0e0a1a13140105010203040308071101090302100816030e0a020907021002 72
    0x1e201c3c001380340010f502d014200340d12010f121a400900c10f1100c1141c5420880740168049400c4403454015521079200341c008084d413840044090746040e182005c28004400700c98804254901000071a0116100440a9600444000e50060400e0204001e000020740c017500200905006032814595594880b84d01e44004415141101500d2400d2000261212140c140000100e10f0101c1295280c11664815100c02900c014031314204180505414201e0311940d405000c00d043d80c01841d40d42e201d40403406031032140100c6103c2c6180c4100007980c1c0104030343c401e04603034070910040340c10368070030003e070b0000c0c00b04208100c0b80c2042100d0500c20750b0340700f108200c8424018000010800100214179850f00c4050b0811415580100018000b1410000c150389005600000d0040000f0f060b40c01201c494400ea0b0000703411408448a500c12260411319462141c0300c0058601036404020000706c095510140004015411540c240310160400a425a900c60541d0044801d42198115038a04980c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 637485071 1250 637483821 637483831
    0xa03090516061b1e080405031f0f11090f120708030712050a120915050103140f0c01020a1b08070b07110a06090509040f020901080c28150e04050406060608182d0303 72
    0x642c101009c811a501e451050410071401d1b458204424205154050f0301e46c0320380080140b02c2c0b00d810403108541e9942441c003490803600c41082d100401c0e565001580d40e6041020110350340c00300200d15104d454400d0041d035850742c03956640c0c0d0040410b044590001048815400e0314000840344c1c0301d20940d0000e0161900840c424002c150506e6038500b5602c1c1070a5404c070200000382c00210380c4044907a400100c0740e540c190004034413649003c120321740b0b148407022980880081d0041000025a00440e1070180101500984405000480d000101300300c40107540100c4001c201e03c0380045c011820880012036000d44980001e281c18416600081ca029509078400e50881e07104e0001d1288504040c0030742c5040001c188240504041600644248849107025049040d540c100b4410170491080840c5889920041e0003000755044c6030904030050301040c00360301d0100b000040801e5600e00547c2c10294181c0380d880141141d201d90044144104002c0000a0540301d800381041c03220708403e100641c055 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 637486321 1250 637485071 637485103
    0x180d0507350c0303041406041203030902030f120301060c03030b090412020106120f06090510180309061112030601091806062007050103020a03090516061b1e08040503 73
    0x1031000c11045141c0740312401000726041d0418640e0a150751000002d070b80554140c40000c1d21840d041c4030100b071442c061a44000018007080040c0024581c041d80000380d244c0c0280c0070b407a5144440540c80759501c0154038200c084140400041101a10030020340c0a8144079160102d2050007420004106020030307601a0f1354030004050141c0c202e9024070078103004100781c40b00251b405c600e64039040a00106001c01404e030644600f4850704022050201e007031050000201040a01c2c80e0f078a803007281265a86045020803460b80011880c00c2c000c905031128a5003040080244410380c00c0a0f100680001d08001d050002056020032202514155071281d00020b150004800e480c0803801024255100b0060054401c0235407540400301c008a540f4090750401e00740569a0702c80107030203c000b0000084007411034000c061004103a8400c644028040301d890780d841e20b010b50580e0b0028013007910051030041ca001c8a840e8032400502d010780c40c0700b01480c0110740d280d08055a032408642801a140440c41072 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 637487571 1250 637486321 637486379
    0x90303041e0f051c03140610020a0803010902030a18050316030306271505011b080405090108030306040b120a02150702040509101118042c0a17180d0507 67
    0x50641035080c6414055940e1806000d05000d06e01a1382401d88060002c6010b0f4212500c8524094000c05c0511003c0741d2180c000b0b03a0341d40e580c03003503100203410603154003006602346807180d61041080d50a455140d82c11038061851710700c40e400b81c8500c882c04400308509244c8c84080004660b0662441c0501c482c02040541c01c0d03540050130314000301c07016080e0741d03581c1074040e040901c05a41d00c0440030f41e41501800601102c2100c904051b90a809280c0c40301e42d004d6030407800411131910100244d170082c00203503424822800175504001c005550400c8900d0294028144d0030003624003e50500700740010078007000d00d0505203030003042c10344034200c4034940c0c1079102d001e0806e04400c191050413840101250f0042c00c041e40c0070083c0003c41c500610541c4030b2a144c15000301d800802a9070403200b054041d040ba01c8205840402503200c1307043c2d24041c0c5510750201c2c1c40010b2036108404440301100740003a000ca0318884070b800c00402022141054071103115004d80400c0c5410001c7c80c841e6003820348070303804d40c0d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 637488821 1250 637487571 637487593
    0x4021c0f090606090c08011e080d050a0807211805120c06150303040e0c0d060e06040b0a0b09120a0f030206181b0105160206030114090609090303041e0f05 68
    0x3050b030300f440e0700c6441c0e000d1902c03168802ca0750340500c42c0c505480b01c4681e01c0d21003e401c00707100300000074683c128503001c1c05000d450341002a0044020702141d8910b440b00085552200700544404032440c481500040c0c41c5600303400560b17081ea115442e404c91201e038030540700310700c1d4445030714000710740b1280e81064500050407000303031504000690780881c5004040c0c138407666100100b5100e00451180809559007a4081101032100c80d00f9121000d410701030030060150345c0d000f900003695051700c52a015502d4050000454107210010805441011703028030324100303200d0b05101581c1d4000391043c20900642d80c1e50f10004582c1070582e03042c14040d6000f0065070a00038078081407020b003203040c0881c41c0d1000c0d40b04010361000c1c0501c41c070211030900f049512200b0415021980300c8400300003d500038400000400c2001007441a49814141030303c40c0d00e0140d99500030322503006015140c1c507005500900c0040c000503946400c9006480050412000b0038165a5803150300d40a018401c9a594200900e011 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 637490071 1250 637488821 637488833
    0xd0f02030706021c0e030a020a0303051506070b011404060f171614010e06030f16050f070507080606010c020307030816020d0b0f0901020924040e010803030406111804021c0f09 77
    0x161178924a01c0558500158840081c0d035903511000000c003415215000a06804c1000001c03118000014045c03640da1702491602c1c0d60790040c00d000301da90110901c60141c1407400e1520601c411340d401c40011141041c10030724582802d2511603803c6c0d14900c5071003140f0001103e903c0075500104148103d0807041000308001520b0804600308250040c02c05104021038000041e600d55000182603449820200b2410811625449150304eaa0002103000038060100031000440c03004440000c401e86445485080c011034408001e81c20296140c0d04c203003410300210340c000b8024041c12030102800c2d88000c2c2540e01180880100d0701e02566882407000400142a002008240d401070505e4001c501d071001c0700340080d110354410107160300705000d2200c2d1009a16501f03412500a04a0011034110b190380d030300d006680d203078401c45044030070605043d0500309111088040c0d5055814851400801c000d10b003080c40001d40007214445c0c1031200c0760010031541c1441c0c0c1303e00c40c2080a0400702041007140e50503c8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 637491321 1250 637490071 637490081
    0x309141e0606010e0a03120905090907050a0806010b190c0213020a02012f16060f2403080f160209070818030405130504020d170304170c0d0f02030706021c 68
    0x80c14889282100303144d56903030320f407048181c940c0800901d00095401c2c40890307000c0b40304d400041c0c00146a2007401825680002c08208460040b0307602e81866848185054440d8428401d600701c44805018400d02a0b13008500b8200d866010f240030110028250001034058030307400050b41e400c560024814060590a00130300352140311140c0c81d01407480f400c81c18111104107030030140c82c00c058082040b0408241038641c3e201400d03000001401420107030f25450000300760710703032010640b00fa620388049d060b8003000c0c0b00b0300100e94120712a1401c2110000d80c2d82c402d075001c00d41501501030f845903130a0050342e501e04503a010320b0182c1d0342d481ca945809030752040c2022142000c05c00a80c000c0c0000c000aa40344c0301106c00c0400304e02404181520b0b43c0c400301d554600c1d0400001c2c4a485a281c3c43c03043c40c00c9141c00b9510540c041c12038180081228084201c092080c4c092000311074220b04404420f45000c1c212013003100d0128030481e460300d0115140d41c022030701b140500c0d0380407514190480c00322000500407 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 637492571 1250 637491321 637491331
    0x3070c17090f120c0d080a0305060316060e0a120b060306100308220e04080a1202040501020d08040c0b04060507050f01110a300221010b0a0309141e06 66
    0x41e14015036400040ca403201c0205000d0b11a844034145000352110600c90022041070141c010340305005281361524458110514210021749410700258240c54006103081201c900402402102804d100040315250381342c140380780d0030640c0040001114120100e5002c1c100b40190b10500c403034200398013054103120002d0a02c2c129419410018808180481c0841d4201d2130100b2150310581c2035180c80850061182c2d0119806001c0c43c020801400b000e00000d02c80c030f00280c1d559a12620000c0d4512040340114010203005a2022000c80c01d117a004600c401e801074020341d04000e19a9442c603402c10030340d01c1a04028000340010940c0b6080103410013100a804480c07400a01a11035800c110844d00c2c01054800410400314890b031800c0504200c0108100c4c14a141c200701915200c1002503002e5070001c040f07038044440c0d1800e22918105040103141c141c4c0d1403070444902c5d000741b8075800c902901c4600015182001204109550390408000c01481110701c070f1010300000e0200007105e414803800030300d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 637493821 1250 637492571 637492613
    0x1a0306090601080601120b0a0801140a141e18010e0c0306010806160c08090307030f3e1807090f15200c09010e090c030a05030a0f110303070c 62
    0x824041d517680c01c41054200b5029000380040c1401141d0001106241c89a21044a6500c0c11020784400403403040302c41c1c4035041e0000c050000340703520710503d040110101d48401c3d0080340d40440a03100f04c4c208071100e82008050380c1c03488070b8031400010942103609011025481d0742c040c075000b41182c2800d01c6410700411040c4098903861402034000c40311400720080c0c2804120328502448100b081640964020030009012500303010f40ba0705c0e00c0a034000307201c41c055586461a01c480c103a260600350300c010240c07408070003000b201c5260414108103014003242140d4041c041055904070001c401c0d04c1c0305d120b00c2c0702e0b0350f4030902c840c40c002491340600c03002e8000c85251a208904002001d8110101e080180301c185400c01c220503943c000f09007403040d020440c5501c0140f180000480003c80090207020700c0c1e070b600640300031400a001301a690006000002c1480c0c0081c49a851414003901d50350500500d6428900c2034110500c0c2042d0843e441111200003040e02e400807142402100100c05101c81581c0e1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 637495071 1250 637493821 637493837
    0xc050d0e030a0f0e130c05040308040617012102010509060c102c121b1009060f0b010206040605130507060206040302210d0e07050d030c1407120b060a1a0306090601 72
    0x1800304000d00d44000c1e17005030141c0c990b5034445683c0e103ea4111001103410050440d00c503038403100000c045c00d61070304400794281d42000c00400c01c9105441582e100302c4507490700c140f00300d00390390054a0a03048140600e034429400c0c8404009030b80300b80061003040c0926000054600a194045920090000c0300f00242c0c540980e8168035000b00000c0000100c1d245900390381d10b8000841c9540e003508602a201c4405002d81c082e02c40b2800701c8d40d04240032144c03281711b00b8010796209100c0f12080301c50074454107005070300100110700401d11603445150401081c3d00703080040642500d40a00e80300301640b2a40041e48a0000c000903d90f040c0003555901400320680c198040c008404120103001d4609101240e07603803403044544055081024a0041c0301c05884410107081d0780c100513100441c2d500c4166805668400c8000c0201030205241d020741e01c0141d0309070341030009a262848140c03001400c46401152a9074003043c1851002015001c14264401056481c0703011028411220406884107040c40300607 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 637496321 1250 637495071 637495097
    0x1020f0405041a0a1818031e1e0302030408070b0c070309050604120204050916080a020301053927041805120d090f050d0809120406030c050d0e030a0f 66
    0x309442c2c0071101000a0403104200b46400c0f04010410b003640e00310741b0009444614100341d080455654030300801c03041c803650007020380410f41e021120714000e40ea0303c0c10400b00c03020030305002e6400b5640041c007414a623402c10000ba5116045020251071419001c28089900c004065000c00520043e0400365101400c041c500103424090100041c402442140c132100050304a000400c02050f40f82003500e003810480703503501c0f00181c642a600b00185d01950070f0400044090300700840a04000098003000d41002140018003a88094509000c0342d80c00d10421045894100d00034042c3c0000c00e082074410350301c0703401a00b004215828030039a260400ca803140c1380000300d14040f40c50421144244002c664600d00604202e0040550b050300421806142402c48280320001034940202410740e00e9080460312402910341e916800011080b0749800100010b01c5164800d8104001c044514200715041038043c000e010241d810900ea80c002075400800c10141c031640c8203401300010850f81c00e2000480c054 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 637497571 1250 637496321 637496329
    0x4050102060a0504030309020415061701050f010507080706050a05010f08060709060e03070b030c130e01030f06090303110304051c0311190516030e01030515010203030a0b0f0301020f0405041a 84
    0x20040002c0d11180c0d0300e038001020316029030006030b4641e5000b4410043c2c608202800b40380c6030b07103074040d42e000104e21024920a0307001181486040c1c0303100410485210341c0303080046445074410031017200d000400380408400101103001c0c160140405507404616981000b0b1072442d4506540e008441ca580700c1414868550740044010044d0b41040c039103442e03a0020480424508901a40a08070b0b2002c000300b041125260080030f016503240989085000c143e58090000c1070305000e000c094046050251940e00150701e9031310820b4410700c41d003004500340211981008554004503070540d407542111220000301e135014843d80740102c409045c01c022010500c64910f2660080395081101842c03d50404020300e805442620360034100f1204c01c808091407458001d28107141e42c096140800d00f020301080c854401c0d402071011242069000318159610b4012582c050101c101c1748580021603e214107545403000c4c0020501e01c0440800e003a030b44c1d45880244402c9644c1d419400884818821004070160f030303 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 637498821 1250 637497571 637497583
    0x6031203110912030c030a0309021c02031b030c040c0e031509031804020c010606110d08060d030f0c0803090a031101110919180605180c031326041a04050102 69
    0x405541c2c07081040783c0070082c1c5155200c1e102c41c60b40d25100224101c1d40150703140d000707444218030a44080307442c0c80c6880041c00d881c1c400305400030b51542142d800080c041000c01c580c0c802d14200101103446209040c030125044580c0105100c001609204580715507050030446c44004c1d030790b5402d004d1000e107440b160031504d13801180030f844540c0010382c81c405001c0da1130340c060f80c0851403036600801800f070303070340001810070f20000301c4504042c000d101d084422039004210300c6101c5c0754040c240d0310340c6001c941c0d4100c0d801030500c0703100380a1201d50704070f042c04103e01c840034511070791320a40100010b251a040c05490840004071a0342c0507130510903021107a400700000d840c1070300000e4410762074141e0090710a0140c0d2406070406c1e01c00d511a440c09281006641d04400121035050b15074041100044034800c483d020704844010840c4810800f103882030031100103080500b8010301c00d46240c03181d158665040c20103842c20100705040086000c0c8500c5046665072400001c220350340c14501883d00c80041d481d03807 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 637500071 1250 637498821 637498837
    0xd030e0f0301060305030a0503190203010f09050603031306020c010e190509071e02010b0909060411120a140102030405011d06071b120225030809040e010b0d060603120311 75
    0x1020210314202900e00b5001503001c3c2d5032040c20360740c444116540050440c1c00840399200030900a14003406009075502c21241a208101d01d24516142010f0840020b0704001d404550188010031035084031000c2c0e00c0054002d440581c0c00303080484a400001462000f0f14210148246c4003082c010261040070754001d0304031401946c249802d80d641d100296810300307083c140035071248103074145419102d034190301031551314104a6410b45962221424683d540b01c040b20000c1c032005103002141044c1c039144408142c114240c40484d02454000c5d525045003103040b4140180381d03034000c0140300c00c004080c0510111907a072210503070011340b038007080b05a507460050107140c01e101c3c99864130400c4400c68209420040c1e00540c0c1e40341a00c0007038400a5072030745001c03e160781450041200701080403000300080100c0750040c518a0900030364400b00b10080c141c03c0b610942a40d0384120004181d02c40921854906005810000b000ea156050030300703103071004607c00c0c410180b42006201d0441d520f00103444440c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 637501321 1250 637500071 637500079
    0x8012c0105090907210209150d030c020a05040618060b030408030a0e070b0a08070e01020f070911041a1b0319080601020a1403040504200f071b12050c0d030e 69
    0x82c1c44501403641130034403030340040e207102c8188a881c40a0100082074000c2e05031082e10301ca802c540d141c00c05544502c1889020303d82c800254120080072912400038000c00500040039659015502c0000a084494951001d10b0514000408007480c136020b11984008200313006c02c1c6840e614142da603855035444000c100021440d0745100300c044480e010072910001d044401c801541d6201c511401030f040f6981100d016000402c01c1c00140080c0d440401d00f241e10502010084c0162418680c0300000303070103075001c1e21058410034800014500c404544100004c0100101569248101800710503201d003951a1180706500c01c004105400c600310b581e0094010007450040c1036900c030301d070040382081d40c0d4100c054207102c1d81c45910515860044000d000b00c54085070b003044040740010811035468001419108040810700142410301c15440051040c54880d10980840003203280d0041400c00d26078022480c0204061402020050100500c1c0060481128518482d14055500901507025491f5580c02 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 637502571 1250 637501321 637501339
    0x3073204020304020321130314010b030a05060c220b04081c170606120901020c01061406070b091015060824010f17040f0302060117030d02070309031208012c0105 71
    0x2141d02d0b50000e40b11114420b0a200d01541c0d92400c101c10f0682003a8113002c91540b0744624bc00440c9000941001001e900c42c000c0d0031035990b200c1254246401c06443c0880c0c1070050400312800c2000d00c5455405800000900da4403141080e105600e0034103140c41502c4a0382d55403d0304d0f0000c40d0042c00f80d522a1043c0b040303076052646c905011481c240036004541c1c1031800c10b074062000000c01900900714045e0f40300000c205990390354840e80b80d044031144403a90488001c10041c3d011a400010107984100c840d001c0300c1c500a4841c2c00030080710800b15000003034060b9108203100b21580103042d10740115643c0c0400340c1448005141200b500c958100d071906101d400905d95459038060407450100f07030000700c501c40d001c0c545401c014007040501d05046006006040c00440c80340c0d0040c81d03c0c0e0a924003000154142018a40103c0082d030040c4015000e00500140000018100f08088200001c5690b208000381d49800611010040010aa007080903428030306603091506202105044400c2110302ca25 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 637503821 1250 637502571 637502623
    0x1507020706092108070c0302090c090f04051b1c1802010e04050702071805040c050102062202011202031e15011d0402220e07030204030309060509030732040203040203 73
    0x5882d80c1d40b0005081342ca000c540c280c14072070905024022a0700070b4803603003840d556100c8401560711401060703991025001034600700720f0400e80e000f02d82c0480c940311200c0103918580b2140c1e140d50040d8003540c0940850410041204120b80580700c819041d450001003111080d50003c2c0155034a1280c29000741d689100194055100700041c3d0010a194072030384540751211031022020f00400c480994600c03400e0703000040d20303520004149100c0c1c01008150440049200e5800d0024000e00405138104a60900080421005480107500a1b0044071304100d10198100000e0000381c002800700480d68100000714026076040111005465494810003c1d80703610400001c00900034090390440060b1103074850554480c1c003082c4c107010b9490f80c00c001e40081c2d41e040c40480a0b489180402000256800e10801002d130081000e0010000300031b081c2c3d07216a883d0300b22241310803001c00364014800d60b5140305903541d6640f40e201000034401a203017980b0358501ba4000c0ba9070780f41c182260b07022138203202c1c0e0061 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 637505071 1250 637503821 637503869
    0x501141207120c0f031401030c15020c10050702040506030d2f150105011b0f0f02040207052e141315050f0403110a0f0201031d01060305150702070609 66
    0x20700445081010440d110034140c000300b1580c000c0500f813000c207160906043e8810b00059950f070407683e00039510200302d414481c035005003940112000301940702c1d405c0510b00c01ea0300c0340640007180c0c03810342d9003d8680601d401004107986003c2d08440c0030760407500c080d120301548083d50f2031020740501980341c2e1462840145140c1c41250081d4490035001d540c0e040403002c0c90f400d58880c12504240e031440202c442c1c0355000040019074070401014903c1e039001110000c1c030300180003032040340002d01c01400c08016494150800355500c1310070544440000da083c8000103011110310b030034140c0c031004000541e41d01026101c2d0310006001817144010001840c410000e03e0325400326800310340042449141003405900c440301c101624110003007001703400c600ca411000000c80303249541d040740002e0640b03a030350f40041d401801480307108803010f0b04080701614134107000d0040400079807082006187c8040d000300744110000d800307800c1000b10340080508011032940403c0d540140c1c3c450b10403c003003a4404007104 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 637506321 1250 637505071 637505087
    0x2040b091e060a050d12230405040f1e0c09140303090f03190c08100b0102030d0c0504080d08010905060603250504090617070801060f0b0304050f010212100501141207 73
    0x91940b05c0741d4128407008100c0301c108000c442004035251054114030301c5030000590030030307201400aa0705003800100410314103900035426542c0b940c000040d11002004881c44140300c1498940c0d421030300c1e03250426080d40e0080c0742c00010000a211401818841000603489118a0254a1003140c040038455003da4043c8040e60401c000407200003041000340c0703040d5607000e10078480c3c0085802000394030205140c10340a8100480016800355140c00340310380a05004080d1401810104181404003041c0800100140c401030406034503440d48941c913003a409002d50301c1c010403090241000b03100740010740014664000300742000d82c0d100460004e66641c219614051940000c243c14100b8100060803201400700c20222580d600640304030a4845035080d0980300036200358681210713190b0b010445100c400c4045c64000d0300c101d05071030084158a4801703099030080840e800d00c0c4d00d030701c40a0140744076841030010300611080c200140001444507a6100034012240b4103140c1d0a0304000280c8154429082 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 637507571 1250 637506321 637506329
    0xf1a010914150909070f0905010503010e0a0507140c15340c050615010e0301060303140c1908030f1008061306090c03080405040e010b0d02190305030406080402040b091e060a 76
    0x114441480c082d44001c00c621800e5086c500030941004c1b01081ca54403d908484c1a645100300d1410991541d1005500400d00100450100400140c0300c00382440700f20001d15203c040d29005244400040600800b0352802070140440000c2c4110506c006500b40390f41d02d415030414602c0c6002a010240007600c9000440c1c3c2c005126001e100c0401c88028140c40b508207586000780e94a00d26091114207241c00c90f82c00380409004900442a4900f900e0303100d800521000314488151644250160780e1441e010908900498001c0d23804000c00c0b00c444404040b090703010102d002c1012140b0720b0721602c6511000c014003a8800751a59000440c10f014568110960103130744580c407030307100540d241400003054126005243c41942041d40c084003e0905000310300103810000c000310341d00196a4204404810403505030080c0c85004000000422420300c05800140909d403683c1200c0e10f0706104000c21074003a00074251040d40e0130410b010841510740d0152103903c1d01c0842249480d04d807800060005140380e40 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 637508821 1250 637507571 637507579
    0x1180e0c030406060e070804060b120307050d110319120605031b0108090d02060c07030c050f010203070e0a12021228050c0f03150c0d0f1a0109141509 66
    0x10030321440d9829000210b120754040c1c0002c21595440d46007400d00408180c91280c00121880041400700c0d5050b4040e00c91444010b0458031000c07045404d25003580c21240c415560398115030b039015130058201100c008401e5505019501d0045407140801018071544020401c100e6045140c500341d01c0c080c1d1007100900401411112140032000503a110401400700642c0003a0703100300403400050340010740b46004900d45c1c018210b55911491001802d4102c000c0540c10064440c07150070104000b8072131245020303007040005d6601c2c500f684000d80700080101c21140145a8070034204030340380747c141c42100c10a504035445503d031071542d52441d2402e0285480d500c4410b4090702084845800307141c7d0300105070300c9081030b14825a806c508004c2206540455a030b01a000440300c28901035080750001d03404150404114204608506031b1002c444914540c4004c40d540d13011504801910b0300c0104035040400d29100c225903040100f0052000c85003401c680c0075481250514445000c00350955a403c03030058 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 637510071 1250 637508821 637508849
    0x4090204080102032a0d0b1c030207060e0d0c0603091a01080c010311070302030f0f04030c1409090718090510020a05031006030e0a0b070c0b01180f0501080a020118 72
    0x1d0980303000794420ba4000700880c01e43e186402d01513042000310201d6020b90301c412070521086841000280a101c2c1001e50f02c00c031a582c24058010000d820071110714041da005042050406201400c01d16030311680d03a2080c07908451001c001040c4112000071307940d4501c0c0c0030a6005861401460207040da210301074102c03242c2c0c000416184d00025501405107026681844400c03941e080c00d1605202d04000500160010401d10702c03c602044c0040c4100c21030110030a24241c3d503622050514074030f40d00000d5502c03002066032901e40c6401030601e47c100d40708c40b015020403031400041ca04280c2403c04617000c00340c1c8074000300c0c0c14400107105a4000c260403840940d82c44020050041840d8404c540003071481440080c0072500728443d20900e03030407c0014000744003070651a225032541840050a150400c089041800009481c2e282141e000f0b20005100d081d051001000ca001903a6010180094503482c21004206884000800c56901502803d064540000300c44000e00b03010300c15041400420001 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 637511321 1250 637510071 637510079
    0x30c0a0305090f040b0607030806060c1f0c02060f1f031a090d020f060f100503011e0b0f060904150e0103140c0919050a2003090f070b040b0d0204090204 67
    0xc600200a01c03101151400e201c14152400c020441703c55030700940d0401030500000001a000300101c0b5007240780100082e040030306006005240103404540a0402d02c030042c0585140580b902036060944280c0c0007030b012500e0210300150105030000d000019050100410403220703c0504546005590000d0442c080380801000d031080c58a802c0c1d500c01c01612030030209059407031010498084882c144005090251904150703001101001f403e50302d480d04a007400015150340c00d2180029284d40400e141c801540c00104503030480340d078440714502980d601680f03060b06e540c0d02c804a41c400e110464002139007903081200300d01d46080c0c5401420102c2803007400402800200101c10f031f0306182e00f0f022a60314219040c10310030100e40946a0b0300031034115905c4c82c1c140c50595000b9560050000348000780001609001401070545e0015016180300004288141084d0501103048015082402448007a143c00c859200c18403a900c98800c0c04078000c07500c030991030708035011035008026a1074155102e80e25 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 637512571 1250 637511321 637511327
    0x1c061a030f1f030c1d01150503310201030630140607080a0c0e010801090e0f0d0509130501060f08090a02130614040b01020304120f02090c070c0803090a06030c02030c0a03 75
    0x4c0360140010b45e0001c9554825404084003426040ea05c426030034259411850344180d84642002c0d0501400144408078144d0b40c0000361840304100e02a0504160b1800942c000902141d01e260080f005550701c80d02d130b41180300d000241d2010782d03207200c09140f54062580c0c00c10b64101c4440080e01034182c0200814008410b134407901040c012050307080100b01c00f0344045400e403000019602a103000c540240010001013042d544a99100a0b40714265074030800d00c00d64003420f1007401ca40900c0821030210740304840741008950001001041a0104040d505180001c0d18800500d60074100308602330700040c410070002e000078030300c2f964082c01c0c031004170300d0884a6002030300c0c45004114040300d00c0c513481c0d5004c2c903003070090441190301038000d0340c1f03018180a03140a002c26010310035900e02c00135141c0c0b0001a03c0700e01c02c842c0b0800000c0600d5440c2e0300c9610b45002110030f241d000711115407050004c0c0f40c3c20b0303440120314400c9900b2410000345540080b8000e034254003601548503d28080c501c5d0210602d0b0f0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 637513821 1250 637512571 637512593
    0x15300706081626061e0a15120c110d05070b06060c0a060c17060f090c131a040303020c010504033203031509160207031103121c061a030f1f03 62
    0x859852000400100e038540717000c42c1000286030302110f11682001400d50740d000c4a4413002e01071030404d0112950416407019240c0c4441d003203000405501090807a000e052005910400381490014508900c50301e0700c5110074000303070481d8450040065030806004007000061090741c0c1c810340030721440001e2080641024201118510700101640c002521071a0003010a001d00100505400c035070707119003421016507005400c1c0903000c00900322000c00c030000b02040c00d880302640815026911400d501c2c00a04050740e684020341441014071091000407074034a461b41c0201c0041d04040c0740304182a4055069200207100580d4034080001448040850025401010241501c0c411b41540740c6a400490038821091a000141c003d41814000180d8600240700b24480040498500b010100c00485c81644400285148074000b100d00c91011901f03801048000c110b60021030001d1a910399070b154132440000e0070b01101501540000d403044407001c0081490620740d0480b0b8004548038644004850 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 637515071 1250 637513821 637513831
    0x9030607020709051302010f0e04200403021002060906071407060207080705070e090a061d06010f08010b01021b040f090b0c1b06070903020915300706081626 69
    0x3904210001c2c41003905c90003021249070b4103035200d03100361500c0042100e40c00e100c50103803644a6107500710103006040f540e4541010b100f4000e8400d039102e02d14810414048004e58138881990013510420820000204201790b0080031424000d02c54400e008152103284602c00c4000c09451000c50710300b09000b81032010707190091040d0101c0b400f06440c0e04101540080458150909510510078840018603503005520020f5415901c0355100800b48242070600c41e00740c001d080e03081004001000a940300340a071500d10a802c0c00500410f43c0350030103c0354224107040075070b4080c9880304102c0c0c41c00c6801d0740c4000485038000340da2810340d0a01c91a01103caa101190550141409000c1d0b0311000c2000b15001d40100e003030741c44124034036107190700b4411015030003084000f24244041e0103904c0b9480f20350f940a94407011505035000c0c0701c0720720450124541001083c010075401441e0500516401506072070300040c2d00c0f0103d140a181e4140304607951116050030800d084600c1d45017108800c08118030310b0181e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 637516321 1250 637515071 637515089
    0x209090a0503390304140303040f03050d0f03060b030c0a1209200405010e0423010e0115060e010f12090f0c0311180a020706091406040308010506070b1803090306070207 74
    0xc0c0f0340e060103200c020103a00c48950150010042005038000c6400ca1a1400401800303681c2003903aa000301c44000ca401d0b50041d551504640003005d101c5902c0101a118140242020000a403d20482e449035000c01060001010b500042d04686107002d82c0c00d0121341c41c40c01005000c0c0705410b1500c954182d071050b1280380404c440038045005890a805610706032041c110307081c030361030b60b03962110784498480e078140c0400c0c075000d0560881401e6081c06a640c110440900104181807c003040c51202100c503840704040203d40101e40640380c1c0d00110704480a005841c0c080180a818272064000b01201c80000705200914800c400801500d10000011a03009152980d030180c84079041c0007800c0d00d9920510200700c10345000070382c5510395501610545000e8800007c0b000b640d99550340c00c0c1c13280c100d220a0701c1c1d4005c400304402c00d94010a15805048203441075800e0001c1c2d41d480d140c00c88400b40640d1296245000000b180d01c1701002a0303410100d0080488400f030410301d2002c0c2d01c03201a07000d60125 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 637517571 1250 637516321 637516387
    0x604030c0c0602030901020a06090305070f030801080c04050402010c200316090c050c0703200a1202030c060f16021903080a08070c02060405040510031407061701120209090a0503 78
    0x91400401a1405d803107044c0c0150041201650380d2070000d00710198120f0501030305000c000080340d072460746000c00501c26201d90042d94180031555140038000340c41d403031050341048100001030f41d010b01a00031240d4442e0f0130750003140b1600c0000b400682250764913078142c8190b11360308046118440301c3e08125502141e00f0080320000c8001200e0a00c603001240d50b295001c2082000080c6020702c1c1040090f90304544e154582e540380d0009a841d1156900c1020202c207850100f1081d8541440310380c0c0102c400b2100c4614011941981103c9401601c1c00117840d1307141c1000050a41d01c1c0e00c031502c4050b04402da16102c15584915011003103400c501c03000800680d40f48001101b03a4006c0740d1541116800801490420745031504000240100500c1d44402d44020031002001604851034a100e082903140a001402e0601c28002d01d40859030355000d40311009117004000d0040c0b407984000d4455010340710654070340d4400c900c0b00d28020010500a000340300c002228414080d80c0d01030400c88207a801c407401c407 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 637518821 1250 637517571 637517579
    0xf0203010603140c0a1505040b130e0a09060b01020106032004022215111203091903021c0e060412021203040905100806240d06090602090a17030a0309140604030c0c 72
    0x842c4c25a80e91511b40814003c100a21110f200640900540000d04098035202038440902e1a0302d50b1040d41c2e0800c10f10b4442402c0b508102080c0941ca24010003031008000451640e1960003c20642803030107d031080412140c254180c5554044070343e540d580729090b240c2d00201034520300502c01540710340c88245803241d17000204d0f20722032228000c441610030010400d550942031403410300d5001804c2030398144070b03105e50b091000c034200007a84902802070700a040403140121406450030070000182040100320544104c483e41c0360b405881c00d444103808801d4003e5012301c0840c103001d05c42d01c02c000242c400490f0003d9203107880d400141c42006c0e805d5144034007a41d20307800541d5505c803c3c2c500b084040319505658000b0180d402030801d01c0c03040100b10800032116030700d07100c003200c900e010142d60094000030001c03018102094840000c00d880003201c100a01c4a81d0380070344078059485102e0070182c440b4814400c1c000d10030101c04024050b0408c0d0746650501e45009040d00300d020004039010108640001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 637520071 1250 637518821 637518839
    0x2130e1012031d0d0f03020f10060b0706151a0406031a0108280903030506041109030a1b0e07030b010212031005011b120507111005070f0203010603140c0a 68
    0x1111441c0d058032955041625030440720b070f0142001c0e00c0e560b0461200b0300508081180c0b40400e600c0345010f50090711403282e85248071401e25401410000355241080c20401c00e00f840c1001701c5143d00d4200b46c0c00140c0c18103000300d40c0c6036129240d10040c50f50740c000349440c0c0c900e40d01500070021a0216201000340344c8080425254007002c1c050180c2c0820402000501002c0f01c030b01d181c0600900b008400300c0104a500020001c80e8440c0d0002d0300029510410003519040030321030307004011045004c40e41031910540000e903030307080c031044014910005540d1341c800103a400f800c2e01c80642410090010b40e45060760f40100204401ca0741540103124580110100e40c0d0000101c0b0b0088040084c0440e01c103003407074010355008510802034030106040390300920102e050030992000c2c504c1c1564409075078918a05040c0108290340d4041841804160460303800305030400111006683c2c0300584040c2081d00b030002038010581da41c405840d110007030840c0081444007107100d003194602102c6441034261a0125a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 637521321 1250 637520071 637520099
    0x91005060a0f0318110d060e010c09060207080304050d080c100c0c1a0c0d09020f10020c12060c043503030a0e01050402030304050d051e030316020c101202130e10 71
    0x1130720041d125911595607082c401d440d00c0409000d403102090000c0c23402031032800c40314900286000103205260600030158144040c41c01001c2500085003440e080c507000803006d5003100310041c0749160004507182111018800c00e03a05007800b4408009490351020050700b80c00b9801c1086804100300e603a903100c0b050310b207240300380208040030b1101c0c1417502d040d0b5094000d261a080c140e078880944442590140e80303d6115004d601c200e40d02410752060203c080c060910040c04040c04d0581140080182030030f4018251412079521000045015007280c030710710810070100c3d1840542c40042c644036292407000000660081d03450b40402c00c4259401000c050803a102070324002d50541003004200000d00c0d0100d502e020017805201070b17514419850303400240c018182100c29107e0380010007001915418405100f400403080d00181107464000000075035000043c0d141c030010720000c2c0f40f0528400d501075041e82c0107140c00f0340c41c81a2540e00c0e00700030b00d15142c0c21100084a24200324011078114000305803 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 637522571 1250 637521321 637521323
    0x3180f150203071101050f0d020d0606081b090d02060903011506110c0d0f060b061603020d0503061f0917010f060b04060801170312041a0a0c0e091005060a0f0318 71
    0x1c08801d0104150044400347c1c0a01c842403082d039000d012500e030044040c4000d03e0340c0900d004000403410310f802c8002c0e001c040001c040307840c00c40382ca00041032050b803100100c4800100480d0b120300f1001c030600c00a0254001c5101c03941c1c0540c6020862500808509030080a0f603269441f0b50113040d07901780c079056851800091098108030203990309000160300b03803864490a4410003010071403c00400c040b83c081e0304844e0148111096480c0c400b402d058052101c103109010a20303107107145241402c0800c003098100130005c040b500c1d01c03540c03402c0441d101e0206800134050010507104000d00301c1001c41e01070b00f0400100b105181c60017a00141c3d00b01c001046400700c4030304d070700e8000d0fa0f0b0307181c95602240070074080400040d44c0001c01c05401c000003071b11009441280700310380700d107403c106880e0409110100140072641540c41e1200c0c60740c10b980c2220b1400c40401040b0f800d10059a2200303440c00a80744a90701c80b41c0c001202244194202d50003141c0c00c00c0659241e80e0401c00195201c039a1700f10050b00302c0d4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 637523821 1250 637522571 637522583
    0x506030715021209040e030c0312061804020d03030b0406082803090b0c030708070308010e0f010e011503090501110903062a090609090423060c030f0403180f15020307 73
    0x10903400f88404010340b6002500030000601491441d001d43c1c1503034041c1c51450165000001c0d03650004500000b220f03006074040d1002c50b8000c0005080c0110210058000313440f945d84440300401301131003900000c01e04600540284407880c1e0f91094107581d5a8503203056440704581c40d80c4900c1c1e00101e01014003c4076015135550074a5454401503003900e40c011030741d0344050f00081204401080420004008144c030030760300c2c1001989441c000b16079811000c0c02c0714510600348401007020900505001303041d1151135800c1058059040001c1c2e000300b070b101c40024490f50030840810400c00014000d816080026410341d10346540e0000307031005909149107100c100c079101c4260442414500006013001050161045160401c0540041c08900701207030100c4040344410100310701402e0101d940740d1201d800000a08150505405844060000500c5105050901c80000e424940700d140340a0790a291982020720311520f400c9030b954042c502e8058040b03802030356036035168042d01c0001162842d5800c04 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 637525071 1250 637523821 637523833
    0x110f03010b0603010e04080c0307120e060c1f02120a060e0c0c0a030e0d2001120612081608190306170322080d05190507020604142101050603071502 65
    0x7145c002c95900140c0180d038122000e0007001c140b40401c0000745001c81c0030f806420b001c40290710000b02154181410113000741380c10b1000341102e00d40060602039100c01815100320444010b14210000d01a28140b04001004070f030901010462942c8290103651050503d45102e95840001c118984110001925154000303054000400d100c0c401d00d4240d0603004201642140c0380b40c66000b501c0640715807904c80a0403c840c0740c0c4103503800c860344d580d03140310340036040c421f180c81c022005460f4a6064070242481000040f0714805900f880d03100c4008591202003903450b02641c1015a25a4882e03800788800f00349058008921114190b00150001e4000f000540c90500401c0e1402504019500000d040c035a201b1808100f9840c240201842901e150f51200d07142d202000354607c95000e550100301c01d101c0208031800268440c1e80031501541c10780415110002d4081021489501d48103500701845991500c07107803460720b010340005018100c1101242cbd0250b4444003e400d1440100b000940585d10103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 637526321 1250 637525071 637525079
    0x9031e0d0c05100e01090c080d021606050f13050d0b19050f0105130e1903080c1315020a080f12060427051606031506050903100e0a020d110f03010b060301 68
    0x81d070031130000b5074041c00000c0b4020301c0540d6000310300003158116143e19001030400d01c190503410000003210f44a40c0e166009484d00c3c01d0400713401445014803110001d9000500000b1140f019032494009080c0901824a41005410b00c40900340c4256022003000800c02e030070484020003030040300d0084034102c001103940d9203441e04200c4100d8041c0c0a6007001034072a48001c420700350a009010409009580a680c9000c46245c0104110320051910398091010f026507841341c2d1141d6117203000d44480c0700d104020300e2a0240260301d410040c003001820700c00c00040004984031354501800c01f40f40040e03102c10f1a40c65040403c402d0794190f080501c0c1c101c2d15000100036407907902110700c08a40c0120180d610b03901c452244a2a4139a0b250450008262601e58001a8280c0101007100400480c601282403445e440c00203a25030f4008000320001c181c9a640101d010320017480030300c01036a03006102400d1100c45141003074103e551215124440d402c2a45c0700788071400e06008198030080024600b078a540e0130 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 637527571 1250 637526321 637526353
    0x30d09150c08160f0204050c041401110c06030c130902040f06030515090c04030204050a05150904120c170d060501020115030c0b030702011b021006060c031205060609031e0d0c05 78
    0x103541004d0702d000c0301c48804031000d0303140d80c03042c103004144030f41d0f40316540c81c03c004800c101d42c080c40d0380c0ca0f41008003600500c000202c0225131014281001c840c0140d4a4880800743c9080f40140f2226050000c00400002600f488640c024400c0f81c20b685529401d0994175601a01220011289600507070380080503140e0714078100368111351000800d0019810561203401081c11034400f120300a5009a5503418032030020b04803440480030b420207c84040d000e2a05d9681c0506149165040c031040c0300c1750000360000c0000d0120440a4100c040c0b51036603e503100580100b000d000e1600c40d260148d40b0788401207052045581110059a800504e04201c0c0340c41c10b08010629800200040110756071448a144c0301c0c3c1d001c05401900c00031329030091400c0500d10170914122405540108144507403a20042c00080c0c01c000003508000050074001941c0e9036100205441d446595501645401f8203050a020550108004245d0000c1001100d1512600d004291410540103102900c1548030a03024914000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 637528821 1250 637527571 637527607
    0x30903030612030206010f05040b1c080702270901020406090501050d02040f030b0a06081506040f0b0307090c140406050f0307020c0a0312021903050d0b03030405030d09150c08 77
    0x446032800291403941c0e070069401c100c000000490068000b00d0041110940ca502010081d104c00c890821010130507200081084150b03901100b20424034044090078801802d040c1e50781b1603009070070084900301d1102c003c10080c241c04480260100c00c40089060b03d00f0510035a0151440c5444001ea1541081c2c0151030907000484a240d016030208004a00050010001401144901010425404c182c00864140c1d05185c101090750341c00501c0c0c4401d1040780c40070b4107410070320039030f800030b48000340c48844405040d800c140c441d0144101c1000040e0810300e503100c601450b00315a209000640d0080d80c2c0012481103201d5400002d0082c48041401c0b072110380199007010301030040b10175030503801c00820000c0701c035a8001c1c1c452034080c8444c0320400350140080341011002a1024001c0340c1c1d02d80d03001e0401d00507404041090b0f55503003040038141d00d0410842e4041c1ca0000d0484202c0c800c0064000e180d1500c40c040d013120900c1941c2a840b0315400780c0c150104203130703100c40c41e981401e040364841a5151 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 637530071 1250 637528821 637528823
    0x6051003320d0f200303180d08041119090f02090a06020610050103020c0f0109030e040c030b0d080307090e0907090501090b01080a110c0f0616050703020607030c1209030309170c03030411010e0a170c100f0309 91
    0x307000020001041146485031083b4100e0031200561200c05030020001d1078400d6502c2042550004401c01110700160441d480c00d51f80d0901700141c84d40d0080070340c00e141c0b561031004500c0d550300c1e009621050581207109841010300899041c41030440c607400440580d655446030507040071288084000003080c010295601601d00c0c41d1006a42e95140501032810100341d441030750700d1300325007001d2040f58194000d6501401068906002110700080001d00660008080010480d82c850900d0200c0200d8400c40d080c054110089945070041207035080d4031640282d0352084e07224101350840445070300610541d01025059005400e0740e65501d1000e4024002c1201500d040040e080710070126048284a4510018020390f40010a061103140080e000400440c504100711014404010070340d80020440343c0c45644803074100d44103000359005841c42c1e0b46080e40c1c44c0e4451240800450040006038240c5542c0001d0300485480c0782448082c00340b01c80c006415040090444240007940e50f0184d04804402 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 637531321 1250 637530071 637530109
    0x41104060602060a270803010302091b090d020a0b0406050903010506151b01060308301003020105090609040e060405060f040305040306051003320d0f200303180d080411 74
    0x40c0d800d0203505000d03c20340711006c40d01402e01000601c00d60030b18100d141d9114041074884080320b101c00c40028818000c049406c0d22a26034568401d0031900e624000500628500e500b940e202e50700c0b0740d005000b40c0c201c3c50300c090080d8a40000619140751140350b001c0c404104010241c5046d0118212164980d140c035941580f9640350f00e03000000a101380001c001e41d18040f10400e68050350601345039140b4142c8041510189154810300240002c40300070402225030908041c0e50354001c5002085241c0260344005a12914019444190b228041542c81c42688201e0a54000e9507034500880241c60f005c0d200580028420301c4244005031030390784856001035240c44442da549603607039140c044680a0115169241c84403002c103000348505440905004200280074154141c520b04000b010284889070003810880c01001d41d9110300d00b41c59450141e4088001542e5983c82c081803416070070090324000e603d1390f1007001c03402c8080c0c610400c280ba01070f0342e0042c00208911f004070b08010350003611381038071703044 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 637532571 1250 637531321 637531361
    0x909040201050f07171911030a2601080d260f130f2001021912140d0b09070c110f041d011d0d0e090c0d14041104060602060a 55
    0x210f80d10a48500a80305c50203103480d9503006808551540c03a0704040007006000042d40c002c4811038004c0291341917010b00380381480001072000c0c00c402d07080b000c00c0021030702c6440f802e00200700c1040205e551040d49c110b80d201c54445032030081203004040d440e1541e1200c000d00450201c1c1040130310323109483e0022071420320b411460080781c840051190300088211200ea41c0186180d01001e003c96040342c201109002a00741c85d42d2130500301c0c04814801400501c0c4010f01d02d0a1030501d8020061441c0d404980480d4949880d5604400c2d8010914010528403c48811000515044c81141a01c07070300c980c010403c1101c0c0c1c209400780300c0000d102d1040780340e001e030b11400b00305641d100d111603451984003107400100c1c1d007203040307200000d050411b01c041002941004148080703c40d04040ca00b00011310584001e0000c0e550003845003001d00684070f0801c3c009060000d08465081208255070099014002c0800a02103074400c1000710f0b00303030b88916009a0030180000741110700035070108074030f0400b029400d12 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 637533821 1250 637532571 637532573
    0x40e0105070c0209010b0c10020702150c030a020c120c090406290a05010806030a031b0b0c13060302040f06030b0d05060903030f0a050f0103120306090c09080f030909040201050f07 79
    0x820340d0000c54800002403030b694490810341c54050302090040a1034070400346080340d880c491544400d580c2244031886500082c0360340464803116040203500036203101c115212448084082d0300c1398130100706640180b08001c018104d0f450301c00f41000348035900c03c004001c4a100071060007081000200706980359076a0396030a105204116404a0602c25691108001c03201800200300307000c1c03016040b8504020f00c1c8410404c140c0c800041404825415090400402c050a040c09000000da10030003414180b105080c072404850140240c06010503110303904040d2030f103075607085041740124440c0e0180d102d18100200305681c080e500484203100090300a0384007141c40c0d21460b10f000020307940f4044a900000400481c102e4400903150803035503000b4140020300706035180302070300d01e810300004e410301c941c0d080003c020501070750100d0010300350064107000300e0b0340c1c0c050068610143c52048051034090b00180d44101e580100c12501601001040f01c00103440e00e800458039500440740040c0300d440c0402c0000c0c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 637535071 1250 637533821 637533823
    0x15040515060c010b010305010906140904051c081e04350f03061003020403020a051002100501030501061415040e0403270906050f180a09230106080327040e 68
    0xc4803040e40d0020404c455074900040031160140d129809e401c1c80c0000601141280107203983d2524000c4030400d03041d40b258105241094148812000c80000700410f0005c00740c2c014020314403515240341c00305030b410704488c552000810200d500603c1600d515500403035040015964104e800b0f00d003594400158142c0d40030100503172100131207005101e0302108020907458584c102040c190918035041d4106403441c1e02165407500d080c050380d4861044040b2441d10706108210707008a200f00031780d084c0455652810681c0c0205020f00504400b1400e103455072409081c103801c0911500700e24054a4503292134503060019140010300201d0401c41c050400c41d29120300020107400740326040050014592078807142104842a940c81203004401c44403000d51141d40300c100d94620902c0d0035008007020b6450601d0b002c02025a060010703d0b4110342c0401c0c0642c1e807414081c4d4101c107582800204051a10342003842c2d0340303009503020511b00601203000c641c50300865a441c100d090801a001195a0848113101 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 637536321 1250 637535071 637535077
    0x109050a0f0b0709080309100302280807031e0c02030c03030405070e0105040c0c0219051c120c0c14154b0c03070807050f070e1504051506 61
    0x1569041c8400c594a01845200c01105801c601030303041c070580c01440c10300d184d0346038040c01002034462001d034442c0054250194041304c41c0300c100082072210207642e041c0e40188881500f05140005040300000030380d200d0184c400e60031000441c3c007405200c40708480320358018110700b00d05c06086000902400703507540010405075004900c06d4028240403030500d0319a0602c0c45050740814401c900381040b95042a0700320801d040c0c0560141d4100e240c444001e204088034411661046402041e00d113511041844a60000198540700d9a00c6010b80484d0706011035046048200140503005282c0c0300b00f0000101c0881400d285101508500388084c0c1c4440440c015000f0341ca1214200c00c07a0110103043c000e0b010303079146148680c8888075041603501210716511000c41c00000c00354010008200608810410985003840e620807460b551b03555a528103542ca50520071401e0244d84106400452400e0a40c4a154402c403444d42d0600ca1000c60902007001400e4003600d40c405500641040c00c1d0152245401 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 637537571 1250 637536321 637536323
    0x90203270607170702070f06170a09051903031e0e10050f1605160c17010b01020d050f0c0a080318060f1609080613060c0206060d020405090109050a 65
    0x68480380044012a20400e00800e1400c04140c1c218404000c29240c2124195021086810f030100e900d60710903109900c0c02a5039002151550f1048000156180e03019408640b00701403500e010840c0e403944441001550b0f0750300002480d58210b001102d2207101161058240300d40603142c0402d1400c480441c054500308c10800c071004e13036502d8030ba4801800108001000000d040048100f24900c0d20041080304a40c1c060720903509540050b02d8032442e04c0c42001a120200640480000700f40c00ca4904801850b002d4460101c5904012070309058500062103541440b0380d068010342200200c0f0341088809034000da100b02c800c04400c0c0318ac07904020003003003090ae1040c032800c0a02d549062600501c680c1700341d44080044141c4c400c02c104120140004078003a00040000d10a61103880002030955440310241c003c01d83d44e21070003003006050700903820416038040c0205c40400c032450460700120303200e80f000ca43c01d031b4006100701242ea006090580c04207500502d01d000014940002c1e1b92143d044c03c02c0c180c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 637538821 1250 637537571 637537591
    0xb0328150f0b0f060a08010614040302060c010605150403050a02040225050607020606040b0a030809060f0d0207110d230102250203070e010807060c05070b07050f070b040b1b010204090203 82
    0x102e402c4450810150282d00c21a040303560b6401e000c44941c000740351081c140202e40420647c01c40540518141d0382c140e5029690003000240c4070380400071200d00070071807845001d1083c1d105804920040d080c1c20100d60940390044042c000d1402e00741c0038130010794800303c1d41d191500c00c0d903d44940d444040340c040d4801a481180036008509001400920382040603140718896843c01140840c10f40d545401a41140c0d80411119102c49002c1d0000c0c055020f070b500c0d812030030b03400041c9500c0441c030a68000d0040920412240e0000c00d0480288524002d804100900c481808140c20304401d200c2c0064610039802200094a40042140148440b403100b0100102107220790900d042149014000f01010704030304040e0705040c0d858a4007541d6108554800e21060001c1c0b4915503083c40703420b00c950009402814580d9599402e207144c0301741e0724000101c50804500440c00f01140352601d0b00200d8040b00c00080c0c246003003000c8140000d200078150040360700e0540d4200000541c5540794000f035881f1b041400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 637540071 1250 637538821 637538831
    0x6150f130906090c1d0a030b060607062c03030c0406031523011103120106080915010f05010807080f0118140703060807060519030f1d01020301090b0328150f 69
    0x30301c094800052007180d0300c64140d2071100294991200701b07440007226041001031006803aa007020603014400c1e9000900f00508141d4000f0b40510f460703001003074038108400300082c030314043c031221610780c0001d84602225240030001040118442e400601500603c41c038001d402e207682e03c0c461a41e44000d0f01c8a00a10900341060031107642c3c000b0640c086800c560320145281c0701c00640b03864484da005000e10821300000c44040352810701d040041c1034510310300d0399480700e0a50f194040403000e84180d2050500140361500021422031040c1c4100740100414009040740da401e0000a50400c3d10002c82d0017a00c13a6100c012801e9020b11041503400b031131842e10300184030350806005904100041d00003e09101c002c0043c880d0340c0c841d080030365005c2030640c0360004d4028402c1c0b040ca0094580e24000c603840c80c07220710b41240c01920660041d8100c41a004080041ea280310f000e05031a42d10b4240e81107034494650707a22b4aa000910f0721400c0585100751030072034452914002903011101c040b180c08008503516 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 637541321 1250 637540071 637540091
    0x170918060a090b090c03041a0705030105040e0a02210f191406010605030c090406170d031802090a0510050910030302010507080c0910020f101406150f13090609 70
    0x4030101d80034126000040c03140441e00c0303000c41c2e000403015050300c0c2c51003c000b0010307092180078030885035405803100380c0500d00e003019140244240c0080c0900d0344200d18080e0a01240c40b000168010b00540c090319607034207140640c3c45c0710880e07030b402000103800d8010040f0821854505001d840754030401740404141c03c41050401051036204d111410440f6800713400184400b540000036641e2101941141541d40c4c104400454003501c0e02d80d000101c0b403450030448000d00c050214080b400c124090703404011062411039103201d04910a100650807696110109412603441c0c2c0080c0e50000d20188600001541e032000301c4c410440403980e072095030700c404409004041e420b0140c1a0096443d140100d92400c100c41009514400d004c03442d880b070641c0e0780b080780d40903000b803010b100f200103c001030760b103d0300044c2400e10140c1143c8524604d10300780400010094034104642180820050480c14244aa15030540c0c111364050071800d0608040c1000000c1d03000054080c60340549200320010072003070b0070 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 637542571 1250 637541321 637541329
    0xb01030b10290d021204060e030f1b0a051e01060b0f0412030923031e0d110c060316030f0c0e101403010b0a02070905040305030417091806 61
    0x644844800c4044100c2000300581180c2101014030407401180d80740b0b0140440410a0320403000050006800400d0050780701c40c06142c0d0a200314080c000511a801c1a181180d46a1042d078811f8034000c0d60038010594010011551135084486ca60120780f0b001e52540c5a140c40e14500000748280100d580301030117500007083c051030b0010b24801c410141003070305081e29850749020b06d00401c9042c440c8880d041301454480c40744100140f0007103540280c43e16003001a42d400101d1080c080f8083c0c410f100c22100c3d1900d5131041c200c1c0c40701501020f0104140e20400454510803c0d1034500c900c0e2164130740c0c3c10100e5503124002c600400d4540062180c10325080c4014041e01c031640140c01840341341c114400e0003a60000c03846440c012088500d9040c507111100166241c041003440d10340210f42c080001314a03803084000411101000303400315262190744034141c83c2510411100180046c1d01400440c00054070200303400c100c5d410800702103051126035030105400c40f84a80840000e9400c0070240011828 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 637543821 1250 637542571 637542593
    0x4090c0b0a11210c030d061518150318150510120c052701080c010201060e10090504031707020106030b07020a081c090f080a0e010813020906010212070b0103 69
    0x1980b20090401c02d07032165107001440b912081103260b21140001d1a100e44402401254141e00c244c0c00e08100781901c940c0340150804152610ba808203440b85c4134100f00e01d403441c54103003c84158005103d08884400343c110080e1078200321607041c0c440000000000180c0711b448a2000b00210400041c203440c0c11400002c01c0c180c0780d40402000b503c0c0c0018a008140d001041100351101a68400b103111881403140f4890008510805c1c030780c3d2104000031425500100d014099284240d00038415075480b4008180316070420703030700304102c3c13240c2c2001002003104035009203502074000e0070100c010100045280000b40e0045550790010303555800c080c02042902c12070703181c02c581076100420140d100341d034407900e0340c0c4290b81c42c0001c180d1408058401008036604081420b87d0b000c5031a03c2004411b10b0034810340d40042c040070010400314a80144103511a65100d4410003c05140e4a031014498080c014008400f62000f030442c0505000280f00959000007802010321803001c07111658590f003001c1410300 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 637545071 1250 637543821 637543847
    0x1811040329040206070308100504090309050306370b041d010f051e060a0506070506070809010903050403020910030b10080c0402070203070519150816020d050d0b04090c0b0a 76
    0x603201c80c090001603100c3e041a01d0040e03505090080e030036200e02c84480030803240395009a500ca8100400302d020198402904c400b125015400c40301c4503150114580c0d1201c030306400c42d145d94404100b034030f8030305000303800c45201140c2c0482000a03038050b0207000c40c0c01d8840d01005540a450000442892040244070340c440e000b903d804204854244118010308010a80100f040700709503490120754190b48100d20540180740041495a9418440c6031440c3c59039021181400071422440009800010600030300b0718003a0f241d61141e00d064203690130498814009004c903112a20741c0e02c0044001007450380014000c0602c240f41c41034a51a015482e89014010b5403440e0040d40103001800060300c00140103004c0e5001158015050790b05100c00407207031056035008101c1440c1c1038081201160b00004014000c14940f183d24034508850310003603a6a2010740b40c1c7e4400101c0410030002d0044503030f4010042e010b4010070105001c141519402c151400982001803010720005c1c2000e16650000c1e098200c417 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 637546321 1250 637545071 637545143
    0x90f06081005070f0c050c092e03110111160f050f0a0f120311030d050103021c0510020f0c01060b04080c2b081603090f0803120118110403 61
    0x51800c2c0a005050104e0000460140300a02c0681700400505105800780c03550301911080b92031a00c1c075031541c4a50b143c10844203048480c804065052100c0007010707c2a030b9003082e88403448802e901c004407903000f402050020785000310960800181c8034080090018803041900c5000941004200b04c00610100311082c07143d400c10030108070500035201c1d0b91040b10030140403d00c10405d18202541c406001c015440000e010001d240b00e03425815a0156040e40c3c0260b445512421440008062503850602c0241850380440124541595644c004282040c41e00d0041070030819481440c50039034042d0781201ca03031001d0100c3c00748041802000482000e00080300c08201060549400e44c503132007491690341c3d03503580e1460121800d2084281c2164a4907c148840c52150fa00d0b60800402a02d0640600d4441c81000e01e4002502600003003a6a841c410682140307003503902e0604010000c81850140d4043c882c0c6500c100c1d02c1c0c0c1c192400151008601038603e4485007007012401840090541d1010086 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 637547571 1250 637546321 637546331
    0x1020a0c060c03090f1b06030941010204081203010b120703090b1305210a030506130510060f030c2f06090a0605060d051c030204090f060810 62
    0x6000d034051002040d8541207a4005580707010810101c002d07101e02d40303001d4642e0505000c0725080000c0c0c02d10307610b03c00005020b01010151655002c50130340d01110000780130f05010040600c901500d00c401e1880d5081e40428030002c2150807043c1e00320b0800c812000c03103030316540494104014034050102d00502107240e80480d255604188038204076000760001c1e074107108101800038004a000b0303417106461a07084107503040e0074600749444424550704d0f60b4044540d4090603a641000c0311006400107408894141d81500b40300480c0003c48c000c11008100380e9000b542d09034250404d070641d02c200c40c05140441185410981031440c068860500b04c18010205881c00700008001c0f40d1203201d40a0075005503803150344035801c040c203a40b50011a0f0307a900225000d84018000101c1001a080a190748200028010f9070f590900b0008242d46004000d00641c011040c0349803c82c1d48842c50f4010030302030f403c0041c1025155621031044030f001003240401c41d030343d915040c000303884200300c10480b0500e07614043c00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 637548821 1250 637547571 637547587
    0x10605030703331d15060628030b0910050603271f0c05090303040b0c1615120c09050906010e030a0f0221060c0706020d180c06020102 59
    0xd40c507441c42c0700c050511281c180402d29083d14800030807030320510340c00036156429180c100c034030000c1030f07891605070010a00400c41c1d21991008a0202000d58114407407000c2c0e42d84540070b00c2030542c03204500420b0241080001d0f440e5400f14184040079507540d5800003500d030303059000d1081489010b0081c0041c251911820011a40e5000c1100d521200303503c0307a0180c0304c0c0b01100c04119555140807004a5018540318800c0004210704540e1000003001014006c00d0420300c0c1c00d072200c3c46092a22074141e00100070501c8502c01c94402003a081070043e048680a42015240d1041521686c105440c040c00d0300305200c1c00c0c50b034458016400850401030412000003656005000d00002b882000e018610440006915a0140340002401c40003c0d09a415240082c6040b0611000041c803c91054180d035030a00b102d00501b1039044801044d020083c4405d48a4141c8211a03412119044a1042c0c00300202c003610042400f0307050b05110a0480d4500c010758902d8400c2d06441640c10040840e841804140 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 637550071 1250 637548821 637548823
    0x5010516060c0306030f0b040c050105041a13170708060601171614040b031801091a040609080703020c1203130605090a0e070503180109030c061517010b0a050301060503 74
    0x80019074401c00014141a0184040d8040c1c103541e8809440e20080c2c406200500000c980c01520652144600e8442607445e00015625402140a03083c01741c0e0080d00075118000d5100d00900c41d0800300d50078100559079801c08445400100b04072458103800c250b2040210300d00400c000ca42084d000d0801c59902c16003c032080303848540042500f43c0c4079026004901415024062840b90b41c50045007550740c641d21002c1d8181541d0060710a030315032886402034182c84013018416010039960050162040407001405000240c9000e80f082e01d240f9611041c800c00542c2003070080c41d104d8400d802402c44940c8800070088803009000711041c0e240c10800240071008414142e6909071a03260401a4940940d40042182507544e81c0051022042c141c042c040903681180256214410320741c01c0c0c3c030440b05030741406400e80e065081c0040102e0227003106c0c07800043d03894000600500389040500500c40d52000c62080c9561403002c030f20070b180d40d200c01000c1c0d141080190040545400d5000344841484c100100e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 637551321 1250 637550071 637550107
    0x201020906160c080609030703090b09030307080c2506321804050906011503110901080702011e0b0406120c05011b0c1d150d06020c011e050f01050105 66
    0x150000b1040211010400007a8074020001e015180d0468005180c040a002c0d40c980c00868140c1c08240395850004c0c40b6a411011141c12003c041d001d0341c10318005a54002c400d42080da10740005005010bd50b0001403005000014010504a40050140d20303000020381843c240030703860b2039840b070341c100030016010003604074a6141003400c0440340d841b844011443c54109885c0395596206080c0030900000d03030740010300d0605954600d120860f00d24081c04094080741c0c40d2280408400d141886900101d600030200303e070784032020b070001107900c010508090086401c1440c030040c000d69078900b461124200340c400c1da0050000c14000c540708507401e49072211590b04600c103c60400c62500e154291a071202141700030350a44c41541c00002640b50041e210700c00c00c62542501d4444e403c030340021680d00344030011001542c00540320841282c91522032901075400094100740075901c07441346030300307981452003a85012035104800040508219542991032072040c0c0c00181041018040900c41e85020060 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 637552571 1250 637551321 637551337
    0x30703090b0906090604080a030318120e0d050a0b07021903020c0f01091203120c0f1b020301020f0414030f060f01060503130b0117060f090a062f04060306060201020906 74
    0x81c09456514200000c1d42070f2141c603e50383d800450100e0002000b10b0b0004d08000002d110341c806001c03902e5083e07101915001502d07400381c043c00244070b20492031402551700806521015003e1104014241c448074074024000400b02c035004507400411a41c103905004100c0340051841c40e070000949240c500a540303c0e516050344d48500428442e000040e800740325000c00400807a030451105088a05000d01040b0901c10501c030041d0030261403014040c030444201028071004c3c0ca40c0801c1011450411014284c408401c82e0599820400c8081c00d40e10f501c041d000525105008109428001c01450b003059080007181800f640400300f4011401d03100700c0001d06441070f5250540d01c96480754007044c110411801e0140c50781c100c1030008030300f15011002c1085035001e21821115280c40e00544204012412201d01030550018010b842c0050480e03041040201440181c00d2048030000c540560588070300038445802c1b16000404100c444e40500520006181c1c9000840c14202002d01080c0c1c60b21074100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 637553821 1250 637552571 637552589
    0x201091e090203060d120f0305070302030f0c031819030e0604080c0d0303151d0f01060f0c11040c0c020109080115140d051005010f0b0c0a06020a090e0906010e060303070309 76
    0x4010f501c036009000712446e0000540c0b01d413071b003c484010301941e0031128428006402c1c00006202c0f207009000b1079028a1140030f40e00c9595071402014040c075000684042110345200035a580210301c00c001c00d03c038140b108071550519009519015004d0741106805900071030090004100c094000314150012000c181d82c00c0b0f520030750501e411001481d0b80303075842040f04041640482c03202c410070f03c040c84e071074800c08821600780c40c6c1151400b1029001d00c1803a0014030510010044184200401d410582c450352080303c948035804009404d07192030090010010f0001c0d5400300640da4080b840307000400c01c0f407008000040d585410190f810b450b80c050081d0914047ca400d8119440303c2510300c148580240c19521a2440340081d400034100c00e00c580309007401a4040454034034040400c40d82e00c00c3e0720303500504000380345a40c0c40300603400041d1160280b0484410020313040c050b8210f02c2e44105001c002800203581005c18801050b8000340016000381d006012401c0000c0d0400c000f0350a40719560 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 637555071 1250 637553821 637553827
    0x30b0d080d1d030d0605010f110c010513121a060a06020a08030c1213120905061c020c061617190f0b03100207050c0f0d08090109090e0a0201091e0902 66
    0xb100400c03402c50380e041400b40c103101c0000c1c03203800c0c00d400d0742c008001d82d5400d80c0d907031005001c0c2800494070b02103618401030b2150829a0181060342c003480080600790b641600344d540b140c0d911000e448066000e030384181c9400301c4100c030b20140402100f139103039070158040700c16031001410904029070398040c1c040300801503280040403400440c0e02405480c0045040183e125007881e0600343c01c019180c403080c0031956000c1d0100411921ba000381c00220543d076014141a0910610411a841d044549904440705542c00c20184c0c148900c2441068800d40112403683c4c42c00702003002c02096015104035001d07101d80c161043c80b07184104580c2d691a074070160701d8003190106c038030380e02200180610700c901742e07040c032615a44111034a138540180100a0042d0706840c0840d8440041c01120101404156030040d181e03210080010042c001420f00ca6a040c500f90050f0354440d80301c45c0450385021070100f00c80c1e0203a20900f04540e4401c00081c09805a10b2107081030403807001c0c1c040c0510b50356003c0c01d24031603004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 637556321 1250 637555071 637555091
    0xd0609141308090a080a050c0109060f1202040f030506040b01050d0f080c010f1b1d010203040501050c0f01050112060f060b0910020a0803070906080a05090a0803070e0d050d030b0d080d 81
    0x541a1000c0f6040200a11041a9a03400180c4c0d2803002000c110341034041c0844680140d030089151030125805038850010841004000301c454030030038009a2040740e820300c0003042c14580006050065071007800100103c3c02c25040803154100142e00c09441a8200b0f02c502d000038010440c0000c016510072011610f40e889041024050421070a5001350203140010f42405803003030800c1d2019a244a490314103282c88112009181d280b00320079800e015070310070403007001503502ca200281040000182034030400e800c3d04801a09480e421307881a080714000804010a000700e40c071484c2d0340003917031100401180b4940744043d01c00c0c0c003030701d040780f4800e580710611a003201d8001c0c41b64450050f4081d0300300d075403842d0540024003400300d41e000307510000b0f00e94130001356000c8841c400e0317601407100100100b10001107555400120b0384003c165004010450302250500d4850300a200308051061025060801801c0c10081c115074841812030312404000b01d9510200fa03020381120800040403402082c0041c0c9 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 637557571 1250 637556321 637556333
    0x1b0619050c0604121403010819020d0c080c040f0b010f12060815070f020706020a0f1401020307020a02011d01120209040b060304113c2101020d06091413 67
    0x200015080680105020081007081104c8003021314083c1d40c031030f407060814070081180e80b8002401501c2c80740d802481103d4290030310617124080288010010140560750741e4441d00b6a05056015412503070003490200000c4c6868010320400614501082000c0c1c0f12400009105046449843c0c5c14001901ea410140140b03a030408005003e040c0101c484a1507d4001407032051002c442c0381e00001c8100c06604a1944007048440c1100da09a004244c292019124040d40c91442c4404039440d54400c0c00b4191003041c280040c1d44070b18042d4000e04078180d070070300001d06030400741d009404103a003000100c128180c2c0c000d00071198004000000580b0381c00b2400100d001070591a0480341d0050020013008208140c1c803140c0d8000d60000c0ea0440680d41000f400c00c0e9040d0007400380c0c03105a00b6072012038107001040c0028540442c0009060105008001035092202c401003c2e00c07420f20f13500041d100390b1183c10b50181c2c0000b0303c001d4104104800f803500c80d8a0300c0d600003401004880424604050074000c2d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 637558821 1250 637557571 637557577
    0x80f0609040204182603070c170d0603150c0207050307090e0a0506100305120a080606030601090f0f29040b0a0e040f0f0e0d0f0c0201120e010605031b061905 69
    0x1814588490b034a090360800742c4001414070203500c0c5c881040c001c820400c10446050324010a1151116014983c0702e03038034080b402500544590b1846814055100d0301341144c05588003c5010b07106402018040b030803920b05540c1407600b05019540075403010000303501e001480c0d00488514110000707171b40c041000002e08001d00d244000d07169105803818041e82460245002007128440c070300301c0721041242a9007242e1409090b0075403001c20f1500340003c8060a1500c01036600030300c14036144210b01d840702120b802c08080e64203c90301d080302e81a0240f202d081213564001e156040c010340542001400c0201c0c031011320039406208400800070445002050040e0440c284e0003a004006108242002d10910010084403003000043c03418072403e030360030901c08074480204010311356408000076075a030000e451314440440d04034104540316140f50b0350900284110301118500301c2c00860300500e820704162404150798920024040c51011641e9155600d40890791940d80001e400807040b01c0c00407055440380 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 637560071 1250 637558821 637558841
    0x60f0a060c0212070608060315160804050c03060108030a12050108060109110f0703030f060504020a0c02121e010501060e0117160e0d06060e0c0906121b041401020706080f0609040204 80
    0x201c150803000c40c0752900040c0003413247d0f10a5040394a202881c2d05124440001624040c1620703602e4140d81214a1141d100035911a00401c00c81e0b000c0000d210102c2e1038000c090b03104040035000401c06240c2680c0c0241000a10903030031400f8051075051040098407960180701d580c00c7c20b59144244034240700071200f83d4110b10781e0400c40d1600c0da4018140600940090b070301d0388849914015011a2a280510030740c0e08845140d60740c0c0aa1880c1a424040e040c200c900000303425201d60240c2c2540603200c4100034030002a41400400c2d03952400c00c0150130040300040450501c040081d10386c0200742409240c1d0750060140601254129159905556000481d100d1527040f607200c000780401e00040e40c00c80c400701c54411408400540d1a42120400d5000c2c607004580e009a04000032041c0c036103c41c00310381d0410009040c40d45282001c001c0d0301010740c000d0780001e101e6402e442031007840d983c06106010081080c0d0a1982492402d40080882500000c03e0644110081c0f0013040a548456005890074 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 637561321 1250 637560071 637560073
    0x201090510020c03010f1a12010e0318120f03161e060c09090b0a06110c061b1213050415090203070302040f15080c07030509130203040605060f0a060c0212 68
    0x14141c0101c1c020344802150440c035000790700b04115600d41988034840c5284040c8280380c603a214200090411040007001400c40c00a036480314901c0f450a41c01b840201640e800612003c45138141810510180c0007038040482a980c0220f02c108000724808011035807100703030a420140b20340700607203070500040d00700700b04407604400c00c1c4031710104001c1d00341d00c03d0040002c0c030b803151018103985020380801c1d240c50071030041c1c001e1641c81e01040070900521001042d08030001c1641e120003400000300e8803a40112140c410704142107016400225424003000300589801c078501e61404103964007462440540c1e11031039020365601c80d42e800100e81d02c2c44ca080f01410b0140d01c00c1d5900e0030200d0001300130350041d00034142401e11803000000c150740d201d0b220540d00e0800703890b40142540c8100c0c52000c544c0040100380e042c0102000380c40242d5585000307400003500d00c020016102e0900d41401012107030010000c5006a00c0f00920900b29582c40e03400704101c0e840d030300d04072041e107400d407001c42d502d45500340c050405 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 637562571 1250 637561321 637561339
    0x30f040209041a0a0f050a1a100314072003070b060603180d050c010c2d260118140c030603150f01030b070f08010b07020d050312010e1b0405090402010905 68
    0x49038426081542d40032105017040c441074980b041c0001c101e4000c0c802c803031070038840c00e0f021541d541004408074501c41d40314107001404100e59040c040d040c003c02c0301c9510000e0050128619000c0f0360800c4c0ca500400040021810f154840ea9000304141020742120312682c004800101650380c045c52640d04050650262003071543d507060f01502540141d0426000342d42403200d40c41002d4030a01002480d00b140d10319420444440140c210581d42800d20404100f00808030913003a5202c0c1c0c41c20101fa4480c05003004c8140b580760003000b02208040920f0910801c5c101410020890301894405811842a2001c9941d0b61144400203107030013443d110020500b8130010401401c0501aa04141204e010701203051490352038400c204c1c6c0400f546040d0303d01003080c6030014060b9901c4040640f60644c40685107030700c4c1c002c160700c403d0301e160880c80031880007400110050101e42405c200445c0c005025503a01e03103010608510341d000c0390080707000c2e6a004803800c000141c1907a10490066000300740242031205 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 637563821 1250 637562571 637562581
    0x906070f0f051207020108040f020f0a0b0c0d0302160308060f040612060b12030706051302060301030b160e100509040609181e02090f0402150a0c020411030f040209041a 74
    0x14121807000e010386450042011a9101110040c1212000c5905950307050042d03071196200800749203041d0090381c00c41c4045102d00c08540b81e208017400509074000343c250312810703000070452402c012000f41104050040c40302a1840c80c107105810b04103079050902040543e20000829162038028049541c41400d0500004d1540c4c1c041810303510b1a8002c0c0420300030185100140000d060020003006038a500c20001c2e5030101d403c6500054012081c41d40f4851050360680024109810030303042501c58092080c14000310401c0d01080c403180d103007241040780701c12300c41800094501191981d96818881f0000300b800c2e1568441d84400040c02004004001810000c0c0c4038120000c3c4140c800c58002c0300c2c410959042800000141070010b07401013406e40709664041c407140c1c841d0780282c41280c000c5d11001140c1c0c90141c03441d024100007030450303407054203c81141c0100425210381c10303034a00782047c0402c140301240e00503184c0940c0c01034055809400c02c1d2200d00d01241030314010b0700075038564000c00051207 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 637565071 1250 637563821 637563833
    0x30b030118050f01060b0313050f150a0b0d0c3005010b1e0604060e0f0a06020f07120503041e0810020409050a020c0d0806010203210709150909020906070f 68
    0x445040c0510100d40d0340980f440e008a08880f40750003000414038050000401504182e01d0900c942486070094411007851040750074a4000c01046407800485c407001000383e2412680300760005900120307000e101003182500e82a1a82030b042c069486940c2800c589822000d424141340007102c0d001c603e19050031a1603051140c024450031301c0f100d102d260100c00d2540c103041078100305e550401c0f004022500d030030300e07045060f2a40d80c00d8043c0c071034200c1d282c0c0360f04c03900c079981e401025802400250060b09107680c610703851a00380074054101d02e83c00c5d000d080350ba43c049030000054800351151040c2d010310b01c0d0102c40b000134014200f54003034642413044520f4524403025a0b0060411038541c100103101a4540040142c280d0040e99803510181d4054040074040d41d02c91100c040e0088410b0040c2e034608440092105c01a12440c1c2480584100140c107114055522100c00c0c0000c01800050a04a0500083c006c103042d115101e02c2110a0300440d0744070a41d030320101269642d5500642e50800d5441d030340341c90 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 637566321 1250 637565071 637565111
    0xe010b030f0a06050708040317191b030501120f020d0f0503040602010c0306054e0303010302030c091e091507180e1e2a30060d03030b0301 61
    0xf154100e081c480031856a03800b440f0003d0041d5803685442e4901091050300c008204c400402c1e00100383c008400c209400801031082901020304156030f100c042d10500409015101c069200c4e00044100541c1074002c80c84035111401d00650446440418800d02c1c10142c207002c03002440a400c03400b000a0018155405512a1a4030460b42e24144201980c1e081000012019001e204c1b0043c610f1101c1c1500c01c0031410075140c8a0fa003114841500c4c2655205e4504080e440d41e60760112541c0004010301c25031a04011940741c0780c00882c1d00705840d11740415100e03ca2840703111000c0000114801117a00d45030203112403c004581040403400d180b41c0404000c1c00030341c015801c484a140015004200503501e02082032043c40189801c1030851801c0b240d4400042000700202e60705413440100703c1402010442d600c0e0f440c2074498030f081e01c800c215080b000c801925604000e032450317140d02580141c48040420030b80d11020468450924500a0800382d014041201c0c032030350300d9460010060052a5400c0e41 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 637567571 1250 637566321 637566323
    0x306012114150c1e0301051e011e0918060f03022103070b010509090a050c1509030609010c1e0815040f0905030418060b03010506090a0f0603060302100c030c03030e010b030f0a 77
    0x3144d1a000385820300600316200a019154014144000c00046042c10060b00d00160ba41817410301764154021042e1200401c1004070000005e101c400d0400998651101080b410021120304110040c50038105800100180c0b0000b03000712540071041d03c2c101c00e81c003610380b010b0305001c003925903892003403038044122007090191521545901002c0b400030080010070114035644a4018116a13001c0c1c0100700e00b6403146161103079040010808000607440521106010790560341c000300f40e0301400343c1e016220207000000396000302618020030001e10b610280d1a60402100d5062a42d40c1c1c00c1e07000440d0140c0094020180b071039003000d640c6820880000020804c41310710900103100e104a03038404070151160342c404c0c1001040d041c0014801403801100804d903800c0024086a007581d6940c008401101b5264040790229513262030410550400b601586160269480c0500b0084010303600908070ba0b0415102804069907000e11f0807501c2c1096010000807040107040380c04d02c501d4820101c1d0303a1030304904 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 637568821 1250 637567571 637567597
    0x100911040e010203060d0215130b0a020106080312010e0a1803020c040e070e0402090a0e06090a110109060f1409180919030f03050c130902090306012114150c 69
    0x10301d56900e030410700c292400b620b001001c0c2c0404201580800024030803d44140c60148010840301c182e0b8501c1d0000d84005010030002c0c0c90700c401c42c01030083d003100d0345640b00000d1904204807a00600003112500c40c1551006c0d0700742031054442d0814035004081c070242c0111681640740300d90003410340020380005607601c1240c082c454020001d401d00d0b1500f240380706110b08210900003150051034907810450340b0011500c400105152000c0b035a528000003542c0b021103903000240300b5402d00c0030b4003281846012007828290210f5141c18401040d2024003280d2008201000d0407001441042404917441001c0040541c81c0b00055080600402e80d07080e83c2c072804030306c99082d0600038245040d400058158054a8805022101130025000707454018019082254100801d1043c0e11155035148050715443c40c0040c0c079081400c00741442c249042c1c002c42026a181b10a0f00c448001d11184441c42e1075002406c0b103100a5003400031441c0030040003142400078041410050000b080b180036040082c01c445c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 637570071 1250 637568821 637568831
    0x307051306052d0703030f090606060c120f05030a0507020f0d050406081003020a05091e04030507060f0b031b010c050a111f020d03180210090f060503190e10091104 72
    0xf92464a10b00c0750307001ea003e200a820310030760707000c0b070700990100000048082e000f1814000070394560040726201d400c18000725000c0c46e81081481000380700c0a44c41e078960700784400405902c0801810a0000410000c095929000055010b034828030034140c800b640075084a0000c2c280c40405801e98003c3c2c000d090010741402d0019030310200041441e001c80750007900588956050a0a10040070340040c0800c28092422180c8480071000246292180d030103583c07002e03201c842616041f0b007a0741ca50300e071005959040c00c88081e410356010504400c00c0b2a12100d810a41d041600107130307031095072040003400e1030052003014410700c140310810525418048032000880000c0c107458512843c106064032005074021011660028026403116484020801241000f03d0031903000a03018201c1c07000350b20020342300010410030800c594840c10082d1a4a0802c9811440c6c032004e089505400440e0060f0055111451201040003d00000c014412070103414410720b842030078a08004441c0441045c000c0d440d02d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 637571321 1250 637570071 637570117
    0x30a060507110c1507031b2f030705060c0111030a150819110604030204020c0a0b130809061b0d02210f1c021b0a05060c040308040308030705130605 65
    0x108220301010402003081101c1c134900d80354611355821000046050204040151022031180d0700d901000b50302c0740c2010240001c0e4054020134010840c1c800b400c2500e0314500200d0701d984c0109181c001c0d00d42c16100580c50300b074040f404a0141007940c900003051303c40042405119081504003140d43d101003038001d0310341540d03005800e55403100e043c1c0c54007410003d4203181002801284c080c0d001840024401c50500d43c5980015040360701401c014115580017a200382c04214424a48962210020b5002030502040b6241ca501d40e04c01ca1022074403541d000540c0c3c403810b0281c0c02003029070041c60011646582403d0368081d40c2d41024001031524048062010061004c0c008111100407802e040610b00b000380306587c0040d90300030b0828160400d030702444a5900c0318a56441130b0a07c0ca0300c1c0000708540f104c2c4e418400d042c2240a400c05903030600c2000240045007000c011138088a40c0064220382d2595400d0044030b40c0c0c02503100e1100b1021814000040e9540c0c17110292040305401c0a40105031855 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 637572571 1250 637571321 637571323
    0x901060f02060a090303090606140405090d0c08070602040918060f0218040b18130b060f0d120903021005040303020c1012020c19050706020d02030306010806091302030a06050711 78
    0x100300428016841400096104907140c0c0202c0c3d0780920901700407440c60560703a41c06c8142c0b000c60704425a04c1d6005c0c000d4074041d103054020583c2103590040a00014241d4140080c012501c0071009050540300081101c1000082d5048400a29504100308181e880c13241d00c0208660140401369070642c1002a0540326a030300e4801c59a10380c0082403113050303100c0745100f404042d0500c1812154030460001c001c0402d0710f1400c403224880d101041d100740c10130075a49041456200080d101d180245000c2800e80880d4a42c8d25482120a402c41030404000701074402c2120b081d01c0702d410003034000c82c2000f030104200d50010054019648281c080c0d032611850b04e0140002810000c1c050800280b00a0402e030344420154000c0c0b80c80f02c80e26050710b42c03003441003051103000c410b043e07003c48155000e90800c0080d594180428000040300348059450f50902c000001c00801740540300a110b45e003064081946480000c485284840e8060191510141d0301e0800307400a0a049170300c14040740301d410b031494035410 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 637573821 1250 637572571 637572587
    0x709061d010905101e0f180b090103050903071212054611040801051e040b0a0b09071d0f0307030605100512010510091e1a060a0c02090106 61
    0x50306030b4503288014074140400540042e42207194040c080c410440750312443d801a00c1c900703005050344136824800700308680108008804c00b101c000c0c1e84071500080c4145142c880450b01510800d00e804145615030325805415440340d004001d21100c84501140031098009a10303034074003000c0410800c0280d9844da02d0070f00c140c024080e2040a8440d0506520140b260700e0303989034011540840100b03001750301d050b05908480f68903007610f050003000304003004980c0c02401015401901581045c0840401d44440310703002c80090002040408003070000f031418285580300c1400810000d01c00115801c002d0405040f9100c40c4142e600510b06c2d00b82c4102e00c3e801c114107029003002c0041c009003828dc2c03454071440020040502100070030b1054900000c0c16540321080c04003044003034400003c840c00d0146048030088000c1e4007200e0454104004035500340d0758072a41681c00322700500c0200305c10a15012890b00c01c9100058a0390000c0041165002d0651040340030b24010300c25074510440342d80303882c826600c0701c03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 637575071 1250 637573821 637573877
    0x12030e1509030c0907050c0114010302090702010b0d170f030103061a01110c0918120c15040201140d0609020408010f050a180210120504060507080718051e09070906 72
    0x548036402000c0f09040c00c00440b03a0103049450314504020792489184e003980c004a00b11002d00300c0c0100184207501e070521190340c1114050008002804411003c9a4000c00da4800903059500d128020510270a101049440503c00f4484080d074960710307460080010800c80c4103c194666007000d4045045d4018a016080d510f21000144280c803920400c0001110300104030000e504007884400c289844100510000450904a8180c80c1d107a07003981140340040c4088480b20194100c0d00303000150740c0103614500040f114814040c0d031030310745c0740c40c1c8000b40c44168400d0007050310010b400140318070190b02102c80705500c00410722040d19140a45400d442e51030b484480c030500740c08480c400516088444c81078000c05410400080810544100100c1704121000d8800355103a1040129180e03102c440164030460034180401c2021030021030098070402409418010240c401c404403619074201407881b81e90340700a000c00e12618200c14004c004494a03c2202d01041c0281d1041e14680c400e1058400c4076 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 637576321 1250 637575071 637575073
    0x603060f022d030105060d15080606100306050108070305180a1110080103021f0903210806190303030510090213061428050919150f090b0c010612030e150903 69
    0x6909117020455a5482446040c1070310b80d4454404643c4003140e0a884001d11059001e09414688902449080d94207100c1409c00c0500d009018042d6030b8103d40c44982010345440e0001d81d40da00d00c82c4140070a007000ca842c4910744a0384270b981d02089401c030070381801550159210260106044000d5034210000c2c08025130026080003942c03014600041034441d14074407441c080c81c20710b98a441d9000e181c8600700d2020030359010000100f08140d04030910981080d001c0d10740707a00344414100c09001101385800000c04060f260804143e041c024403800b0ba01a1501010841d1782c1d0111118840820701c4500c51400410141d050307401d0b04409034015900010710040c070074001c41582020b4681c1801900c001d110a0060602c10b012194a4912400660500d0342d2214030b0b031181429101c4256803030460b1030360201b120302c6034180b2640e98005000c80403a50194030180c0c49200f203542c1c82d800740185030403202101009009079001c0c95800305012041d890141c8119051103500981d11a03d449600806501 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 637577571 1250 637576321 637576327
    0x323101e450f0515011d150d060b210601080d0201050106020a1101020111030a02030604110307170907051503100b07082d04090f0b0607020f0904060603060f022d 71
    0xc19070704000146400e10890581d0034108802d6515131100400f030b00001a00350f02c3c464280001c03410b02c040f82d07401162041040c860520880002103c45440c1a80241440d44035a154451910342d04041c40d81c202c00d00d40b50020740952007500e141c0d070f10340034420a2410700c504440c0844080c010b1003194103884c1542d015046100540d1a01c00f0029040d0744810b0440d90f0350b18030640c7d5002c0500103140100c02070100943d80b8245081004281c42044420040002d010002d004103103070070410b002400e030305403484c0c0465580c81c0c400352400c1c038590340d00050704042942488000c4051040056201d0805000900d9070f0644a041c1e00d4468020804000e0140c002009100841400203805028240e034004d01080f01c00d01103080780c40160010f030700001e4819282e00316805d4111503030041c0c2c120b030038007030700da080c140a40d0340c0009200da401043c40f07074050340f801c00201e000d0000036001203025640144d0701740410045540150000e40c0b01d07003d00038500c6074000d0040d241c400d00f95102210705803400c4a40742 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 637578821 1250 637577571 637577573
    0xa09170d08071812060f0c09050d02030f0105040b040c0f08070b181207090c0c02030c01110f06010e0f06061201060f09050a08070323101e45 62
    0x64103580035044405002d0704515400180c1690303c3c084014020940103000369503002e01d4504156401e02d81ca980710f081c00c0c0314450701c42e07962202d28981120001c44103006400c2c194001300781406040c05001180d942402c04000070702001e241618040d0f40700713611105020396140e90f24040d021460244014039000120108810700303c410151264032861451050300902c92000204043c00040c5601d0458000c544100600d00d40c92081c840106080c0c10708400c41083c9a000075102c0b0500c1c8207150601110042030b00f1862403c010792100300c54003500319a860358460b100004000d1089901846400d07100300000c40c2d500300b10007030710001d4141800c3e80c4016401c082c02524242c111140034401c100c0442000200350380c403080359000414100e80070340102030446c02c0451070880f500004821a00914080301c1499030300051a402c45c03526440009001203003524020303c40706440c0c10b84070700d290400200d050089102c0d10800b40c42c0300c903d02516100f05d047c7c0f40c54845036905480031082c1c15620420740c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 637580071 1250 637578821 637578827
    0x2150a0914060403081009020406050d020703020102070b010b070506060f0303030f06030c0301060b09040e1903031830081317040812030403030b0303070c03020409021909020a09170d 80
    0xc0c0300c034414103119005890400100e0302d4074408440640000e02414240b140381204002c0050180540f40001e510741820301710040d040784038080407400c05a0340020b005d000d02d4800c0d8152064658020340420f40c1b569109520704894000582c140d5450003034202281091a040031407101c060000340103941913585926549088200080c6596014020100d45001c2c0b540c080c4103000281c1120409203842d03003003000511044940d4000241035a911460301d8125480310444045036207545490046040c849000c0310040001016600034107207412800030f182c81c09040542140080c211565001001200310801c0754100401d8840b20701500c40400e000000c6101900e1705a6440e4008802605c3c00c0d640d020443c0c9400845262040b05082c00301c00d000070580d140c0200c3c50344881c110300845c03c08000b41c03a00f2130305600c1840000d1060740d8030200c00003107480d0103620711100b80740e8404501a1958545070003019502c641c061030001441120040b5407114540405161010000c001f0b0124401490080d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 637581321 1250 637580071 637580081
    0x405010f0e060f10030e0f0f150a0f0603150b041b0e0319030207170604110120060a1e050405030a0f0908070303020c090114090c0d0e0102120603070602150a 69
    0x5a50083d20039160400307180c0360001c40c440c07005080d42d000591440b00b42007040c113040c1c8440a00351690441c03c0e00d5684200c00103000c1c406000b04c0000100e140d01c0d511414802042d0004854080328105075002003400340e024001c00700b28989010030322010700c03200b04100442d01440041002c3c105014002029103205004401131450040e08803001d00f00c6480002045400300c00081380160f00c10901400401d404800c45510380b14145c008020500741641e42c1d090841c0d0202645040164040552103800c0390350b1848400e2107000001d65a0608240d40264050704051100b141008800064805003034945c0c468584250f030410051030030f00603036142c22150180c3c46941c4800f0040c11100202d03003d5403d01c41a4019803186d00284200c1c0c614005129400c50140d20154641e00c031a00c124000c0d44903403114135030290a101c10740e40c1e41e0b8241040c0348003e001ca4000805550310100e01144035240800945010720001c070f048070503c950b9400300b241c3c0d4628030071140741c801c20f55402003200c1c0405c1d6048 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 637582571 1250 637581321 637581331
    0x10030b06010314150a0e240f0910090c020307081204020409050d030204081b01020d0c02210c03010b1009060e0d02040c27121434050405010f0e 63
    0x80850500d50992291169100c1610801c40744481640440308904c0c003186014000c00c00c4011203107052800969290382014507074007039482001c0c4607110b00c0503956492100c0c101240004c00e01c001c41e06043cac0e10411815000d01521441e2813914102c01c071501c4c000016034007110f0740011194034001116448450400001e081242c0040d1200c00c1400080d2041c8454402460155801a142e03458002d150380307406603881c04680101d1f40c0c50617114060340d01141c048155031641c00c1c001d4900007640302003840c2c030940035210900086450340c041064403006c84c124008020440080c44600d03a03c40c1008000501a500140842d003034480c2004980e0040e52000b0361084000c2288158011540204060f201440c25241c00141000341c88840c6200e0b0045e200420007410420911090900112110028122078007400c6001540c00380c03000328404110b4107444802781a60301c01c1c4034010750085805001c0640c94034002d40d503040790104403401d040c46614122901460081e800070302e000d0300506a100d011744 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 637583821 1250 637582571 637582577
    0x3010b0a0513121a01050405060d020d1109070903020f10090e0a0e01090c0504050f010621020c1605011413030839070503121b1c0201050a050f10030b0601 68
    0x3800141d0f481c207009036005001d00810415032200380a8681c01102641604160710692900302070058907180d50f54010766491703054400c41c40c3c0c0c0c801c070b0408882544142c0c100e2a800542d038020041c24540c090a0301044a100390703103010385858900c003000350000300e8941c0c200c006420b8074420442051030b000065040009000009114040444290f00f50744060f40305444010b4507440c108000d0174039118a503484404140d51034141e505007000200b4120300380e00103113560f07100100d49030490301700c59044610b500d000740e040300c506038440036428800b81180c0c42800c0c041000b182640d11044004400c84101104400c508020175003540d54240540c1c0080444041034804e0b58094454034110b03620701900e010701d0006d2024070280302d100452410426402041c06500b295401d80d062060703070820b8807000c040e00700810340115240140b4925000308140007100d05ca1004419a29980d010340c4818003451442d4018032880d592440300c40ba5610082c0c940c8404032032029401c2010070314a1954a400c580149 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 637585071 1250 637583821 637583857
    0x130c14032521021309170403061a10020d050f0c0a050f0f0d0225090f050907080312271c260f0702030412060618090215090307180b040507020303010b0a05 68
    0x268090301b15070401d420460b461a40c940c1340c0c03010721075143d0100040000c2100e40008440785080025140c000c1282d52805004003c240c0140020b01d140a54401b91700140c202c0da5010814180591740f14040340c000c83c024010012078070002c440114020810b02c00640060101010f50140252440c0c00b400d807804845401c40300200300e240660040800d80300034a440402d00f41404010581416115400000f00c2e600810411010412042032580c0c841c452460401c042031164412081e0340082c881d0520300e82c0a040c0300201c1c1851080d084d104170007041da40d205018400a0003c043d8961040000d110791613201000481c140f1055403501c1c2d0003482803040d40c2c10180d0391004410084107030380c0f08071742103601c848050007007646180640c5c03c03a500240742030142c0754084e0003142280b8032002e80600b4480c4000741052450f00d00b0400d1760001c12480b003c0c5000b40c44d500d406400105244003040b481176052901103040341c1c3c80002980d06032035030071000381e14100c99030300c007a00c0990100c3c103800b042c42d6000d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 637586321 1250 637585071 637585103
    0xf17250b0f03160c081c140f070e041a060711030102040617101d070c120905280315110a120513020f0409170307080f130c14032521021309 61
    0x25080b2070323025880042c1c03406024102210301030318940c0d4505855002d40d2405141200008190b0301c41c1281e81030035520250f80314600d050500007404281c3c0758a070190300001d000a0000ea000a001091101c044400211501c41e844401d250134014415008140380c0104520018a89100e14981000c2c160801502c0d00e006581d9155900b01c05440c15000320703039015020400d41c03c084030314506103441c06000d4035501c440c1c02e07206103503500316000c094454062a41800840c1c1c040f984500071b0314089901a6490350301e01a03008140100c81c1d010b066025080c2030100d24400150403001000903802808000080000b40500000b0030405409559503400600b02d41c2603007030010021070140c0d0181c0e80d4403159113010070008442c41800360090007402c0841c42100c01184ca00c0180c0d00540700c00700c0c20000d82c1200e490010303150036206907800038880014110b00080184640c0da000844900c65040c0c108480099203114191010900194000c2485194000401e055a200340e10540c41881702044040301 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 637587571 1250 637586321 637586351
    0x30e0d050109080910020a12080612060f060a080c01020a0b10030812060307050916080c041e060905041437060f17250b0f03160c081c 59
    0x142460030f5810030000144800141402180041c20420b94002815120350ba5034034031124101190031030382000000d0700410856998026044040b1000104603401c0d42803034048810b481009403140c9110b041d100ca0000f507544000728101c034040d84160003502c441d10b040c1d05d80741c40c012001010410706115052012001404d5403000c2e1a0007a0300100135801072a103030060502d440941e40001c7d2040107044c0804c540b04640c8002e29080d9441c5260003503103500e07030020342451400303290413102d580301c6400070b400c0c001c40302200c545c011100030b580d41044040c0d903542804200c50309407202030703150000100002c66400e0810342c81d11849007002c030329124050304d800003001d1200074490000a02500d41000300100071503910110007403c001500345500c400314100c43d6944019000c1c0700450260420440500d00c4040c8c04110010001002942d940b50646803684800d58000c0356071f15041c0030303050022410180304080c0b5900c2d1550002401f440c00c1754002600c0d0704280802c60f0019059160901d0800c0c0c510 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 637588821 1250 637587571 637587581
    0x1a0414010905060f10050a031502090a0605070204051b180609040510080d050f0307080912030c07050709090302030f0d061802070b06040902091f0b03090f070909080304030e0d0501 79
    0x40100060212810704c10000c40c440034014041982c28081c1c3e400500480c0d031242e124604603648440485804c8c045000e07013101070b02801d0146507000826800005250350044003c10b4050703c05c9604020f95600d4440020040c1030519941d1200340c802d0100c44420110720050003007162005001600349200e41c40040c0035a901101e0800d0707941c6010070f003000a8041086005084401404e206043c9050540418050301009082100f0401c502000c503c25600c248070150180000243c0140c2e0f80c40c2410a003d846d502040044440d0301c03800700b00158400e02449224629580342d4055458400300d65a40144c03500000340e0044055070f10000001c2e580150401781c0c0c11480441009a01c075241c0b401c1401151100a11850007641000c1d040401603980710080d0340d0065044501182a0b1200c50b245242c1042076005408040c5000052090300100001d1260400515508440303046403900d289000341c440d1086c0040900600340b001c42c0002c0e0058000400c200310203054121102065103506003034031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 637589928 1107 637588821 637588823
    0x9020a1b110d0f060507020607091706270307060c080109055103010e1615210b09130f0206070503160605010f0f031a04140109 56
    0x3c25181c40e0240a140c00c40c9040003545040007010703684480c1a11240c01060f2014000201248080c01c1c0c029200d603004080c3c400c40c1c8800444011038040500010981e00e000010100040410009040e0781c50003548081113070005c640c0c01402259068210300700c4981804100508140d24400016460212000103503c4840800f0051601d8a140310001090b0701c000c6a0040c101075040c0e207076610003500320020080c000b2590880c9541c0e60100d0461403501080071010880e15040c041d010b100c400762418000c0c4840802520301c00030b100b1b88a0052640343d51400d00c0240d03400c001c5d014541c400301d000001d202030211a19901004915524002d11406c000a0340c10100082842901e0240c5506200008806401e1610070040d120074000c075038401801e60303c0000d5014035041040d0032660080c0401100b0042c0343c4565480040060007a1413041250f0b844422018007441011282 = true := by decide +kernel

theorem cover : BRFrame.Cov 637410071 637589928 := by
  have h0 := BRFrame.cov_init 637410071
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637410071 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 637410071 ≤ n) (h2 : n < 637589928) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
