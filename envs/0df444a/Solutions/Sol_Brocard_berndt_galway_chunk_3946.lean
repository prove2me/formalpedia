-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3946
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:08:09.787728+00:00
-- url     : https://prove2.me/submissions/0e1f8f84-3ab3-43b9-85aa-9574a4a4f5fd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 709532374 ≤ n < 709712230 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 709533624 1250 709532374 709532377
    0xe060916030308130f060606020c011106070504090510080303040c030c050901030803130606080d020c09060a08030712020307020409120e240f070605070f08010f0602060f06030f0604031d04050906040602 89
    0x2403144007448160aa141c0d1200141c9489511232400f5800c40c04a07039089503040064200c03440c0d00a0050031442c5866600036040d409903010300b5900a58440c0020707201c2242200c9200034114040131603480703103814980441d00d09078038001100c51580c0d10400040505042e0090341c10b0300d52041381c0700c1c02c1d9600c80c040400c640c0c823030600c2038a5041e169800012814014031072001d500800c0e40c0500300f80e034018010320034129005031126000e005628010401d200c400f100703503039140b81d200700310981c5182901c104a26600440201a5010b8608000c0713604001e01d1502c40740e00c0e0000e5440d066500c8682e1820081e076004031030517100040300c090040100c45c0424500901000316400005800c15809842d0042100d030104d5814004c035070012107141a4a030012051401441c0c100d80e41c2ca80305080c42c10094075060301411034a940710920700803860a40d418043c0c071b10144404ca0485a681c501800c000306442e40600440555003180c4041c0748440c1800d005084c40340f075080340184035544803513803104002d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 709534874 1250 709533624 709533661
    0x60d020f090d20030303040503030c0a11060c03044202040e0a0b0301050c0c030909070903080c2508120d060503060901050f0c03130312020d0e060916030308 69
    0x2484420000207003140e54811909107042c2c000c034000e008049071030340c0007154003400030581446075100b4400c000028000000f16a4410002c2405a0306c40b5011801951700d03841100c0d6010481c0611707420071240e82402e01c051481507001b8101130000c00d654161080060b09411244a034910032585010800c0c03240001007402180710703800041c90180c4c0c4484120031210155031281e11141c440c2011a0b00745424018070703407c8507400039041c3c507180c0200c045a540b4800c8500581c0103040d0301c00012240d600400c0d0700380055800c61b21955030741412514198484400c80240070440254440006078488030445080c1901d00201c010204842034100c60303106078000c1c1002500030740c3c50b5407020555450070b0004d00d02840d800400030603e811320207154a11010000d0040c001c442c400e200300040742c00c42d03031001c5182e40d81600b0418658228030502d20040c1c4900405540882c0c1060554480000b00150283c42110190151a4144c2658041d40e156080b24400940010a0306001c90703810700360709034011030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 709536124 1250 709534874 709534897
    0x140105090918010908041a040b03010e04020f060d14101a0f04080f0a110603040b010b030402120613031106090c060d0b030d050405012007090906090b0115110606060d02 74
    0x2082502010b50a60780c0140085401c0d540100b410040424090941c2c05060b118880040c00c080c1082401d4419000511965080c1f0840c0c502060035520750080309070381800c0181810360f940d4900c00803070300548413034545c1c4400c2d030614000142004c946080142c00b0b84000c3c45103100c090b600708131514507507000088a020411402c000002d07410f03404020b24807401c0110b801604c0d4042403401c240d0b107075264000303125008881c10010080000c0c40d00e48101d042d0b0b018034095a807030303032501c0c00410300504864a11101e248100c42c14800c1a05410300c0841c0302c50711990b1184805140301003900d40b1a202691603440da90700c0064541d101e882e14202078210341c0d0034140b00181c4689030030300107440c004030300342075901144d00010705010300e5031702000002030100042c0200c0c004071486c0c8211640d50510b0300c034210596949001140400480350000310b415a001109179466585540c400c040c00d2150603903030801304c2c02041008241c5074010502c80e20880c4020304407802d000903200d00c01c019520812101d08c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 709537374 1250 709536124 709536151
    0x91109010e060625120801060801060e0904030314010b0c0c03010b030a060903050d1a01092306031306110a0f02060106170612031c0b12100b150a11071401050909 71
    0x2d006031300030381c3c0b400c400c60300810160039400d01290300038110780c0c010303040350040056060040c02460307080158403030320140544404a465440341803c4004008110030040c4000c0030301c0000901c0c001100c06840542440d00580c0c000143c40802c241c201c499034003140303406820001c001000709856500208440d80071b810518a0600c00d00301d61411203540c4981e6003291007000c82e4546003568007100074400740080302860050011790145441c60555905125482000c000002401140c00010095030080c0e002d4814010300e110241c9229842c2c0040c030032180000c8880420101131407001900b00e040b40c1d101e840e0b404041c01400c0104074101030040035150004e10158800b04c20800c1040240400300710811040300003c01c001d4110180c1352906007191140c8520380b4410000030700031580010307141081c20f002449003440008034440b02456a550700c0000804901c0c06849508644e020f0a15449802514101030b01d07a02e0030314038024001003660014030706100100450621001e0a038000110f40c000c803 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 709538624 1250 709537374 709537417
    0x52b051e0102070627060f18030504080c060301150f0e0d0b090f0105281b200120090102010e0609030408150c09060d0e060a091109010e0606 62
    0x300959001141000c00c0342e500150f4001800001d104802403260201c07000c51450140c0c840002a02c1c000e400b0141210340e40e99a5440001055803000c0b8050810301d00c01514030415040150450b0480c3c414500b0314003551a80da120383c500031040303034141c5901c01c2070340014040e8058111800e0b041d2541c0c9105000c030113402d1080560341c00c1c0c034031007007140f08180d00c030164030301a180d030341c2030032a01c06040382c56a0401081c004680401e0b1000744054103d0130441034440921051400a4102010010284d100e030320508040590312010020314003996503044c81c86034112428003403c8984c9a40004104000310925800c0102c00c0300003020740300d034144000301e007129031070301414104541941c142d510b0f6400040c0800154000b0b10101c55a074038800c40800092400054106403031007000f034114803902c800241d00304140c00c9988081c0c0418036a508484d154903140c00081c00600401c641610545040700111300145440030465060b02d50031481401103803520303002d00140742c1142c036082401c441c03032103180c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 709539874 1250 709538624 709538653
    0x5090d0c120509040615031b050a0e1305040311240a09030c0209180c1c0b0c07080a0c0215180130090605070206010602030f0708040b130f052b05 64
    0x388409003a221140800040300e072203001d02112320007150f0268940d01c0c2071201486540203c160b401004450800740d114498020000e8050b002c8100c181d6112031800c03080c80700b4540c0c0714401c09620f21402040382d524204440807000c000312003c2c1e48511070401d40e0b00040000c502d9070068000c161190030f1019406406900058800404a92800710313101040e2003d10086400c2043e002c1c10b4100b41c07040c40d40700034041f0450a00355002e05010709032200080200d030035943c5a20440c2c12554010010342d03112200404010301c08440451f007648241d050f448a020000007000031525081404605142201d51000c015504061070002106102425440c001c8030f6940158032900348030007030080018261400e150400c02c50300083e1070075046500100050028980002c00c541c05082c00e00354242e00d481551601484c0c0e8860354005c040c65240c0481e6480b402140742e40703280309803090000c604180b9a218400e1040050190140700d0f440c0d0051200d8070b8030060a0038141510314001c800340c0d0490500b1021 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 709541124 1250 709539874 709539881
    0xa0f0f032714040f02120f010b0c06010909020316030b0105100f0e0909010b131e0506030304030b1f060e13050c0a0c0501060f0b03010807120206031f0f0801020d05090d0c12050904 79
    0x450184c80c1c803070781007000390389400d40c1c2c08103000d055270080441c240103452410550350a1705000300c900095450311400e06540e0200804001d00b221048885019604c0785820900340c0d50a00c1000d000d404407465608001d070007294640754001c85942c51101d144190410070508000c064544d441a5688541c0c43e42143c45400d0245d02100104030003160688005005018001c08070089144441c90038052090681c2c012040b14201e0303802841610b196150106501c04488807018001c2c0401d4404000040940d0030011441d20180704070f0303004030507c0e010016039090303d204440e02001101d0402ca54134040d40940071100a89000c1c200008035292650118100100c1035000203c401001100401c00088100310b104094195200b217498401190341c081f90032400060018100803010b0382d080c00108180300103920040050182c1200e406030389200d598000d520036400803803a50304001c0029080200046d02d1105e8520307035075810a405115032200d0703900003416440c003000c00ca010020360b24565590700 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 709542374 1250 709541124 709541137
    0x1503210e01034229071103010906050402031b010917070b0a111204030c0b030c0c39030a020103200301061d030114010b0901020a0f0f032714040f02 65
    0x105210841d50040050f50804089601050085411030b07201c0780e1101003071461414603556221640d8851002e49040c420304841540095007540c03034a520a0280003103500058010340c001d60684050311030b150745444000226004150204001d0340080000071030a40894045245507000e990110b511201c1441c401e500166a403000901c98482c0c04c1c102203000d00400880f4415000b050385810303d15903803605070228601c0356002c108000b000052040d16820103c900004405041c2c2c0c4488412102c0201da0241452800a106201600b041009000c5c1003400031500c070010000c000b1034000c0c1c4e0045000c1c0041c00380c0079003805411004841d0a00c1c1c11800b1314080c0116840d01203004080300c0d00c1010218944100c4e074800c1c2c0c10b00c2115182140120ba48906441641200c0341d611100040140d160402034103004003904140003601c414840c88900d01c5050b64804e64a29220394002c400140c00c150180680000c8421502010440c00c264a0b128107407066001d000880c0306403990f1b01c0b1000300e81162 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 709543624 1250 709542374 709542461
    0xc1206040308010602031305061c05090a14030703050315040e06040f02012c040926180301020f03070309030905180f070201020f07030305060a091503210e0103 70
    0x45040c04101a00000c007540035003020320007141000c0101d104031900f14880c0c41920f004000000c0c0b03420b42000401185007405100743c1041c4a903062119140d607807500a03c07000c0d19107140120705c60880c40340120407103a4003600360381e51900f135440741d41c0d410107032014a198240d031240d95054041d010040c18444140324500440205c06582c0c81800003415501090322654050b02c000020080420002040702c0d140300c8047d503000891560b546060904407201042013004180c440c03030108045100000100040980c440d01411070016800500d4243d025071804035403d42002e10010f2601c03403190f400210014021f14081904c2c5984802246482011100028030402c2c3d803001c1000c00040a10225048402e51008502c2c0c41c1c010106507040c1d010340d1f40001c00701500c40000c10001e076035402c2c2400c06080071810400c0010740000d21412480300500c1f045801401004480e801c602860780c4483c0c0d00203183c0c40d00c03107286400d0001100103041000081d01c400d40c040d4407481d00e0381040901030001d40d809 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 709544874 1250 709543624 709543633
    0xd020a1e0609241b0c03271d0105090c13030b190e150105061b030d021c020f090d030507050d0e040e060610050a0507061401030b0703020c0c10020c12 66
    0xc07603c6512040c00c11004100e40b07081607000402c12403d1040c400c050a0342d031600302040e0407245400c44085800240b403040c08094400d810000d602c950300070b18101c07020751380140e403658100010b040d1990750910900e035010740e483d000a08074010321001082e10004102d4441c80003070b2a541d5101050b00305442000c00310000e010804184101c51244007079400301070000f80002c032038211503100090014012180a014082650410340844001e040c0da807882d0003043e00d13211803e00c81e40c1402034100380750f510a0f4008298442c09000c41c240b00b280c050b040200700751480c2c01101000d121000c00c030804200d0402600b00103040210b08140060046807602e5030f59031090941c20070410007a0341083c10aa85a500254140011556040c100405502c504d0030803e1302c40b50541402c1d41d6034014100060409030074218640e4054001c8001c444c180e0340300e41007602254031030034030031800c074001c0040c140c005500c8040745200b94501004007843e400a1441103c031091851030110710806480c00110100707030700 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 709546124 1250 709544874 709544903
    0x30c08030f04060b0f0d02040213170a21020d1b0204050a0501080f240405120f041e120f020a17070503010b04020c0d0c0c0e16030e0d020a1e0609 64
    0x2d02c2c0c06851310481c800c9582d881986205ea0024494043c8260020f1145500065006580c1c15504442c0300a000c240303100640c0c1480030625030303141c251064049900003103803901c45100025035441c82000c80200c1d070090a2a00c03003080c054905848001900090801841c00c860043c1c0c3c981c019144a0007154101040f00d515180360703d0b00d01200341004c00720603040603003035200c11580703081480006c0410081400e155151410800c3c20f000700000c407615140c8001034002c002c401020010012200030200010f80c0c018208812491505280281c005440000c8006030104040e0300b04000361500007401d0000c400d039100c40d44017494042c40310000180e0021141000180380a1007217261480069178250300e0010b102c0784160305c4405801294091110440840c4144402c4000300d0014020f002d101413001e0402c11b80340b50b401c0740d10a65043c002820400e00d0501078001003841180076211340c0050050ba0703c0c5a48072101031290400c0e883d0502c2c25402d001001c03403824081c1519050141b50064203540 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 709547374 1250 709546124 709546133
    0x4090c180603110904180618030801050a0608070c03030b04020d0f150b0415020304030203060a02030105030f0c0a23040204060c0b0703050c07110409021e0a050d1e030c08030f04 78
    0x3007036108400341403910400350799928060040300c0810100725400036100007055a9566140c00070a0050419480c01503041d410b0458541c02004d103600a0301d4400c2142c2e81e0341d08100300300109001c1c4c040000c403024082040c00e40a5600100050310905011031650700341400703e42213811200c00d4070003041c1c80380c0002040d40240d110b004025034418104800c4641080401d041c144250720403d40d1400d900340c3c1c4008003920034003d4402540e030003800e450300784c2080c90304035021b50000e0140382d1190103517421031401c0140000d420780840c80090000c070040340c41c0070204034150000c0c0306c1c00c61100400748820300c2c03c0c2c4d0359440204040d01302502c510303c3d0207040d03007816220842c0040440040c189000e05001e40b10310180c00350b84250307900041180d8441c003a400440e018008248000b5003045401c9540281080d5100300b036007107401c060360000700c483e6480080003010039405101400d4011880c91180d04188654258003041c1d0280c01c01c0b030742c107241035a02d07424264412101ca400c000b104105000410 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 709548624 1250 709547374 709547417
    0x1c1505011805100e0a0317070209090c030c0f0406080303040c030b070f02120a090b07140d03020a05091c02091602070609030b06042f0d0c0915050307020304090c 71
    0x2000050311450050b0402000c2802d4048031903141d010f01000f1541c0700465a20041290051540008006e820b801170101081c503030f0304035100c124420840000000c0038140000366a422a80d001801441d007480d0400c180304811440c514031a030007035150b180100342001d0400c0158015882035038803055040c03a60a025a44443c003811410070810000761307106801d580041c1400010101d0b0a000341d80743d44110302540c0c82085684450390031140406d420301802515002da80550540c0015504a4200903e0440803486584030510100b041403100c44a10f040c08881c070700030140040e0704403118110307030340000d100703074400300d13800883c2161010b08005103560601c42e20340107050506080c408075086a0791403942c80707001440305004580d40e2600301a41e21568011012210502c0c1200c0d540d00c5101d41d60f0bc00340e6000800c070004081c203281255003080e02c60b2445100300c0c1c050180c1900c0d0030804010440e481d40c800740c030031030440c4021b00c40495402064030400a802d460307a140d02001c0030b1035840e042c00e130 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 709549874 1250 709548624 709548647
    0xe1b030105070f090603020307031b050c070602160b0309070b070503130f06121e0f090215030609010524180f0904080d090c0f08060601080f04020112021c150501 71
    0x10002d03150311010ba01600103143c002905d10500340580c0740d94400300304a00034042e04c000031010144c4041c5003811650490b00400707202000b81e06a03000b06454800036070781c0786014a1030031058022401c0030000a400ad00155401c60f0000050380d80156582040011682240c0c200b50380c83e0b000001c1e00d0b20225046180c45005001844c42022400d1509001401c54440d4400140e80c040c0c8590580f810480414210209804001c00c00c00210304020255001041340c070000301d001c0d004240c00c4c0f4183d54564020303a482800014911401d6071700b008140b20944500d68980070381980205025000d0350603e00103001c00401c4003c490700050b000201704201800304041190042040d081400046540f0306c003203c0d40d14a269101007138107074441ca001d610088040e40241c1e502e848001011480d00c0c40030840380c8c0120000d070b031582240e4a5100ea03050b02800c0581d0000c0c041401320b03000d20b040c450030350090801651401e58000c01e41d0600603284040d135102d502000d0214000b90750501071580c001219541 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 709551124 1250 709549874 709549877
    0x60219030c0e040914070b04170105130623090606010807030207020904030e21011a030714010c020f0603040c030209071701050d050313120210031b080a0e1b03010507 73
    0x5003604190240500301d40007082c500907a2240c24983c1804826051000040710b0481102c5d10303eaaa01c000c107900d90050300541d500132110690820b0203000500450b401007021041d011107000d903c2d03a44d840140202cbc3c0c031440b0078406508914000b904041c00c014032a00c69403000e010b0034580b9100040010100804040c103151040c041c6801685070f174103039a030380264982825078201c01c01200040d54011000c103118400d007410a055089100c040d0481e000100140358500c5035825030034109070b03d8034264028125503001606074600158412841031002900280640c00c28070b40030000302d805903104039010355040041407002c0045003080c0c1801540580c443c5404c2c802d8040c00803048000642c10b01c1454814081000c5081c280041481101d400d00803025603076803055139601a100311a04000c100b40d02c558440007010003600d000340a09540304c01380c5101156090a41441602e02e044050005030200d90f0350005415900710802c00c01540d00110480042642104401c041c2580e030000c00100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 709552374 1250 709551124 709551131
    0x3030f0f060b03040f050102040b070c08061303020303070807091805040506180706030b18091c0f0801050105130e1e100b03010308071b06051c111608090301050406021903 75
    0x40482000983c0d070071a40c031100e4100c054409050642c064001c5800c031384c281c11000510407003041110360b0b44200311807409054840513664a040c60395500300c510005005a0410400039401e248980c4106030b015840c0d0610080c25030b140c001d054852100402002c1e50756642c0d1003031005008042228960010003285951b20400c503c10083e0b40300d2500d0f1080c1c0381810380725800070005a40faa01400703c5000700c2c804980c403514000d12116924502d50800c051240280414280020701c24160105001155205c1c114079900e084011240d42e0b00c607006c01011400b0381030000c60850b012035809401001c0e508640324450000e940042030000015059800e034881d172807010029041054240d0381120f4000c40041e45502c80c034189194500001300c1c0c152002c1c0f51a490200702180c019001d40825100d5108000810b84a511594112908110a00174100d02880800c562041c440e1080030342e1072142c000c145c20481c80c803020074207480060710211503064010428600d55803081040e407600320920b16091 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 709553624 1250 709552374 709552379
    0x3406090516050112091118040c06050a02060708060d05010c0504140409020a0303030213090c0801171b21030c01061d1303050706060b0d090506310302160303030f0f06 73
    0x40c2000b12800d0002040540340c178118814081c00c510800b000420280031100546000046d5110141c01202c044880e2121840701081072841002031700d0001340ca0ba00100001e0701c0b8480203440c55600206055800210045c00c4070000380700380120a6040c403242ca41944590601040d4104201a103104a00440ca4401c0b10005a9a480004421a07400d403c0050b035426840160040078519500b200070041e04103515004c03a41c4d48840c210741283c0d0b1040305491541450400c16440f030414180c03203280d00902e407a00360000d21301180ca00d500c01c52006e085003c2c00d1126004c60742150403c0410a03016507417803000300b0416501419806248022000704829481c1c0061001c5450003041d4000d000c106020800c0c030708104c400e0303010201070100d00c200076807141d00c91400a0040d210034901100e1a0040303401150006800f40d174400c0312900c6140c29081100c1c0c0c065161800d0320b5a040017a411440340242c80c40c0160668820040510700a0f50042401d0110204d0b0030260b5001d40311010280d4903000b000c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 709554874 1250 709553624 709553627
    0x903030c050a080c030a150608070f030e0c090a020d1a030708120307080406140109020a03060506040b04060c0c091e050c030c07300c0b06031234060905160501 70
    0x11542d001c1c101051301d0b504c0c0e8490135040c0b130081c0340b00802c1c4200b41d0240c0c42e02180d0540c100404a201e08820740d00c011404800034002c5040c0c50300d190b0b00d80c1150303100e804d4006071403030049441903205544d51001801c0a4030501400c0c03e0750222100c144611207032018521840c2400e11002c005807010300f005015106055500003014480109801308202456000c9010820380e5005200d02418900d4070000c1542c480310306a0007540f04544a0340880d04e41103000446040400944003150300c0e017a03096040618001042d1102140103100b1104078200f400082110305003481481a01c084868030521583d060341c00c901c0440d03901034100400810b0130710400c04c2d0302d801082124100f5600c0f018100c03228030541c218503110f220402e03c1d0501310303075502605440e50358420741c5e81c20346138081c4e56542802d0701d400d414035881f00305100840101400c1089030404005540c0a02e8a151418880401d4007009070700f00780390400d41f03518089658a03200c5d0b0000080c0a001c00c054503405e06130940408009280800 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 709556124 1250 709554874 709554887
    0x1512050405191103010c090905070e0102100f11030103060e12070b0c0a1e030b130908030a0b03150103060212061c0201031a030609030901020607020313210f05010903030c050a 77
    0x40a0b41c032294140005401c103c030040e41c080562001400074041051540d0300a00b0395002c5000c2c40050b140380000040c8003511074076169a1000d81a00641581c4940084003c0035065801d117040710540c550101c190000101c0c00294001c3d40211400a0404000030743e050034003034081044e40203210244001004180c410810030741050101c0c29107a512191100d0542e1910f280c910800301c05e0803170810302510650542c00240703034144122816050300c05080c40c0c00c0200c3d080a803001d000403000340002807844205130300a11460b00c000f012505170450285001d508100c09800455109402084c03d01e031910348001c100c1d030020750442d800c01811900d0012070006242412001c0d040640390700544404500c1e40c00258550b54000e0183e804030324000003100d5990340701c0f0140f1070040c171450000a007035902c04001d880c441c111121036500c0309468070010301000050302e0051300c0b035418808140400580240d10100800f849980007240c0600c0a0601a085170800c8901000b801420018100c0303d40c1d11a0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 709557374 1250 709556124 709556143
    0x51201060305070c140a0b070f090b030601020114070e130b0603040210050c071d0a0e0712060f050403080603060f1e1b1201080606030c0a030206221512050405 70
    0x50000b9607661003650480321151210000f40440c2c0c4128180741c10a1000308070080014064010b4441c59280c0381c01c21505007840e5028140000e21015013030250080141c001d6820000520002c80c000147d21003610a40b001524204c011502c0b80a030030f0a40d0402d0782c0801502c0e41c820808203d580e01d0180030940a2000400003807003100d440c00325100395070182060700d245980317200880e2900754880000c640c860194000490040b42400000781c0b14016501440c206295a5070140c6aaa440c01c02a480e160034aa1011103130315481c0c0c068044060107034803800c0e220341d000e0742c1c400701c0904041c024103040200c00740030b54040c882d0b0002080809446200f00c82413500e0a060038421540c0c1e000e058400748182050f0103d049500001c1000c1c01c154010200c48c1610000c40540c5c8007512001d0030076907030340082e840d20707504108844420400343c50460040c08c00c00c415420107501da12884841030421044a4011103d15045081841d5290764083c1c0c0100c0c052004c0c017403c00047c1850740780d0965800484 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 709558624 1250 709557374 709557377
    0x60105030a11041805221e12032304050303070c050f0102030403080f01060c03140f0d09060614060310122a1401020d0804111203070507090c05120106 66
    0x201203034501c01d0550211004940041510792115181d132804400106038111010303002c0d0a045c0812808400195404004407a111203021002c0156661050081200303d002440e00848281a004103030307540328036007980c2c0a40e50005195090b40c0d4030716a490039056a4071900f0100f840410001500020840707400c0000d40c00c000070f4496061a0840c94034644020f1346030319500200500c401c25401c16801030252141c0703091407030180e898100440749104020070140000b100c11407100c101c0301042000f010404000354101d884c00100140140984035076120440303195070780c1c0104000b094102d100b01080c01e107041b1034007031841c10311603402c104091260041040b4240d4010f0181f080224803e000c00340030a00b0405111410080b41c083c03214180d040c4241a5070301a00c038000d11042d840031816004040e851b0312000620344568680f941d1902140c3c60311074020011341200d004500c030410240000522400007000c540e030500c0041019103509042c100c00340a000d21400b201c08030420612415964103 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 709559874 1250 709558624 709558627
    0x60314011b081f09060608130c0b0711030a0b041b0b03340507020a0b1c270c0f09060501020a03230c0c040b09130201030905070530010212060105 64
    0x8038280071110f0201a841c1e0030b4205079941c0001400b215640000003107803071545034001150303200c80d40803002e00a0188010004c0791501c0f402d000341461100078180441c01640d0002c9619080400700b0319141c2c00500903201540c2c14004c000810642d00e2021000760040c0e203800706001e2410140010700c1c00094150800b0310500e1961458659024181009400c03040f14000c00d103101b002130250140c1c2c0424030990045080000201d0300c02e681800b1101c4000b14611002c2d48451514900c400030304414560800070310381580781282c103040001d0701d0702032180a454500c1c40140703040e031040ca4820741c55020044a0342000e008000503a0003007203620600382c150920160507072103450140a043c00b610070101641341d010503940c241304400107c03e001c6490603102000701c00f03194420030404160071241d00c450f04940401d184015446504002d403e94440e10445801c41d0b00d40c000600c42110142601903940b403d40303088038140a40c030040c00000729014000710b140042584202110b010000c2c6043c2c140b080 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 709561124 1250 709559874 709559881
    0x50c1213062019030932040b210c030105010509040b0405070f09090302010b0d02060415021f02090102120a0c060b0111010603060b031e0d03050717010603060314011b08 74
    0x4428502440003200142c600c0e4000f0402c48000e1010410070540c00900e0308400407a01e52480340890500c20301c805c3c1e0500700351140403000100138103800c0201d40c206440381440b031101d440e0b88440441c510242c480541d0040c810072000b0b8034040e03420b45614072a038103080c01084180c030790968040d01b01ea0002c40c40b510035079603420098646610340d8024039800c10048000a200b030131700c2d40b1038801035110341c2c0240281c040d55020000f40740b14102d0f0196009100b04801c00407008020b0080c0102e240d00e0040e01d10b0440c11081d0103810002d04010040820b400083e000300960b81800f0244282c59000d8025082c06000c0e0001030015950781d60080c0001d50301c014031504e0340e0086003070304660000c001c0240606a00d9181c40009084001c04050180c1f1614100701000c000d52581c00707414076070501c0285006a88070380d046000e0030300604024240149019150282c070346043d807180c040e061070345001c20a41d1552510b203101910707001c55040180d25007070149540c030580408013120410705180010603600d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 709562374 1250 709561124 709561157
    0x301050414060f101e0806150c071404150b03090c1005090906010e130e010e0106050102031c09020a1d0c120a1104120506060f1c240c050c121306 64
    0x5c0303500043d01c0f1050704100411034041e44041080c1c4203240550b64859a200c02d540c81e0703c281d0140011700003594001e50000d03c90300b101110501c00c60702d4024008140c0420007624140c2c4000703160003e850703805001040091501040044100202c401d071040c544070300070030b00001c00c540641d0702c0031441880000040b41c0d881e8484c80e28021011070082041071100d103411501d000a00f48520242e03115402e143c82d803a20711700c040c81070104842d0b0680145251030101d50300603016028500f010200d0a548951104c00768540315104005048003141d01141403110720a40c07290170300000e013407881d96882002000c3c0c01d0030300048a1608105000404a88c01185005c1c5403014091600b02e803001038119004036060240001d0398901482c3c00b918000322480c554000d00c0f0f40c0484441e004042401b1000484000480900c05c0c1a40a800a041400d0150300080240150350980d4240b600084001c00d8040007404107000440c03003106d0b40f0f06094074046a66600c40301803540c138403e00381806009100d040703442d07 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 709563624 1250 709562374 709562387
    0x31b0301091406091612020904080d020408031b0303130f02030c03011e0506030f030714010b0607060605041802030c120f0d020a1a010f09020a20030301050414060f10 73
    0xe41e840b0001264030320385890010383d186800c031390f8041544204150b00c07030078002d081030340b205540b071080750071095541c04e0b000d0090410004c0c0007201c1c41c640410130344030481c5640c40680040c00c80c500246668040c100245000201d1500204860750410414080114001c00940a04c1a4000484810180d10b0f000103800c2c4101102c0f44d5405509000700c00b11540b5642031030580c038083d0307800c1c00c01241d128402810344e511003003000d0a0322036208000c810f01140c00603203980101a503980000c11150803500101c2c460b0b402c0818100c0700300f600e0302c3e0103202e43d180902603540340341241482c4c80c0c140203071500000e942c1e59564000e14020261903180d031450200a201500214946808071000b02202c0c0304025900d64000100366400b990350300007150022944c01c0401c0c1265210681f100d00c0c40d0500903030000035804964810140510102803459a40c0340001544500c61030308060f40e26036140600303202c207440c00c29030804100c2c410b4100b00401582c0342d1907100d80d0308105450051a4402020003540d24 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 709564874 1250 709563624 709563641
    0x330801080303061203071212111602091b07030903030e190b031504020c0c04051e041209080a05011b020d0815010309150b2d010c0302100212010f050102070302031b0301 74
    0x1c030a5020203030720100303030044140c200c8e40030900307410000c0030f4080b0b000b40898003c0b40910811003140c10468009868200c000c550040741103070039100c0c4002480121a21780e80b2424003140420880502001815009540c540003000141c64403540091140c0035160014814045c2d4a03c011020020609500c0d02c40c206250030b0201070f00442d62071306034502241d510201155aa40b046040500096075800c54003a5480c49200034003003640c00d80c40350742d5411260101c1303d102e40100455100002241101004003018003400394000082024941c0005801c1c032908508140075036004604006110350703c110722586c44001c059148e40f1030358407000120064030044030040c15400310b800000000301070680c051b0419520480f001c00781c0400b0f9056808151030070220010b07880b44d00504c10035203540106016200c652080c4191182e20141d03100020803030304144c8141c15180b5044005205807808466000702508090000340803c030700c0e690000340d03038030401c2903070721230f40c58040703801c9040380d2025004400c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 709566124 1250 709564874 709564883
    0x80a0f090b0c07030b0a09020604030b06010c081804110301060f1d150a03050f0c04120609080a180503070b03071b060218091605090609010933080108030306120307 72
    0x142d610820740c1543d620052400261840700b46900441c00c1d408243c8074903100755a002d000141032501d0740c6c5072049248001400b4a041c0014902e9281c0000d5150005204980344e400c9550445501c04052008841f5207165000d03402804000500c000d6403c03045201040300a80342c07040d03440c2c01510740c41840d80d01c08001c0d150020001640b040348a00d1700000ba0080c246241d40804c4940d44a0a07180c5000b5829900c140d102c1600708803d120444180d0346000c0e800e4003075100401c3c0c07036081d660782d034203980d02c40e1005000041d410820140d004d02160840401403408030001d0035003600f080090f00c42c0d844041c0c2001c2c01c0c05080948280740300c0074000b98020300ca0308020115240c0d1100d040030101c1c2004022103d20031720541e40000c6d4400d440c1e802d502c401b45500e0350b503035090426004c01d00c482d035440112800c0c107020f0168030020f2200e49118000a01c842c1d54030041030030b10880903d8081c900710440031901406900c00060280301000420f9030ba00c04000c0350444c2241c100b6001060451085460261 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 709567374 1250 709566124 709566127
    0x10509040e010b1005190203070c0605160b0109060f0b07080d0e190309090c02010c09090522080a0e012c0d061a0f0a0e0a020d14040501050f01060903080a0f090b 71
    0xb213500b81c011024000e00450920090b07848102e0100807030720b13403044c040010503400071104240f1100e40f088000d0a10a1504909020030704090b803110540e8510907405640300d42e85132042841010461401c0030010303d42c049001d800d040803a95100d5490240300724010003166181d00200740c0750360410003540c55506a5110f854045d9090500510740061405810300d520704080002100d02d105204070b0324451420354807402030034186619000501070180408055030a45521f90701021400004442c0c4d0303a10440b0344503a50080e050b0050400d605034180c140c140901080d418101503405404102d001c43e038003290b020f00c0c184100015036145140d0f1009807415150181c240010b12030b503d442d1f412048101c80514606000f0310811580d81d040f4013650281006001c00303d4030745500354003e4031101607002e001044884408407142c0d85d4031400c03a03081e00d00740e4441d000d20016640401c005405098503103004451a400c1d611075003620300c1a000080100011004100d83e0b0754881c2c03c0c501302511f40c250280d03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 709568624 1250 709567374 709567399
    0x40207050a1718060304030c060e0c06040b1201050d0b0a0f1107201e0d0204090b0c041721090307050306090d02011a010219050312010e160905010509040e010b 70
    0x2c1120742021045a0042419401c007410030315103001030780d11642d4103540740b0100d5002a07640202034588514440b090b07200318059903400759185e60240000d000c0c00c1540d1070b181c001d40b07041c0010740101a80f0580c0546203210180000c1450108442e40c800050034021440c408610103090040c00112100e00020743c010428004128880c180416100707401e07600e0f0074141d800c00080002a000d0348401c08029030f0310140001c03950500101144029000170030002c0c00350304545805a05150845e01040c140e0320000d414040034503051600041d11003407800074400c1c194540103141c52189c102c140103c51072400b1a40041031758003000f810015000240c143c0b101810300c030000a41c0c588004100300099400c00861206000300c07101c1e00070502105900500000012590144070450141400d81f00c1d40404c028014848020104460007812080c04960683ca400c0380b001b6101c0541d090450100501c25a00f006541c1e88241503503040e5100b101d00003000107140360814010204450160741105004408 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 709569874 1250 709568624 709568663
    0x102070b0a0c05072640091104030803090303092a010c1b060917010203150108060111030c1006060c03081f0f0308031806011d0c0c1c09050103020702010e040207050a 73
    0x4c002c0d01d1000101c08414802d6148050f00c0c0300606d812120310741501e40341e000c000e003008a070090310441d05c13a0380403e85080d4590b00c6407a03a40e0302c100c2d0006200c0d84000240700036510100551004480171100e00402140c05144c0107000d80041100e160401c524070705400288052001110344401d0014011459030b56a40000b0341802100d2045001c004c4c000d90f90184e0501060084a205000d4441d02100780110704006440742d02d4040c001174100b1141011072148520308100805151010300e009101c034164824441051b2481500310504000d400400f9100098100d040240c019500076142020500e0048000c3c1c00300d03100340e0040013031210000300002803014003801180a501b0341c80010003200c06000040f582c4210a03c11110006a039400135888a05034018564120100000440c0b6241c205400c6c40e1400c40392003001545455034425501c1c0154000f0070b6040240030030f081c00d50a01c662130f00044c0040e10040903e5000340e80019100f01008000d1001e060b120340e00811880254603800d20 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 709571124 1250 709569874 709569907
    0x402070f03090911070b0c271f0f0f0201021606140c03040c09020c0a0c061e020d050f07080904060b18011d060d15080102070b0a0c050726 61
    0x3001e070003051219001045402050081404052030381102d5842d06515a60780c94076a5002006104000700501c400b807a1425070b040c51001c140c03803611029220078640d8040040b1840ca40010394582070001400c3d80000c1e80166451144030001c3c24002d480c032031204402d87c00b9210f400141034100b4040c2a40d0420042c0344d1f489058403003c000c8906450303640e84040e8454511041c0c801030103c1510032400c1200f03844c545c009180f4040c3c140d0680c4d441c2c0302d0656401003500360641100f8040b4078818400c0c03848aa02d95482400741140d8401403081c140030010152948c850807295685682c0d00150b004180075188044400420001d001004256915182c180d0705410503d03011810300f200f4080301d80a0340c89038080c49001c91484031980c00240481c0200401c560064403040100c944401c00c1890554403240346170000c1074060000340c2e5404503481c0c00c180002c402007032219120303d008008050564401c00703480c041a80400650a104c5032582d00f100709110400c45e4050b050700014148610030302e0700c903 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 709572374 1250 709571124 709571153
    0x50c04150906120321061d010905070f0e010c0204090b0a0c1205090312091f05070f030608120a121109090a021c0b040e030304050105060102070803030c070b060f040207 74
    0x207030100101919400048075024041e2805000540c000a400b1010610044494039614400300001441591010f003500c066020080d6030062a804c100100322000741c07802201c0d84000d052030841c03803c200f000c030040e105541d6100c032103040102c2c20b8503500454035035910030800070307410180d41c0300e441c54017900080103010b000c0d134800c0003d080ca0402214540c0c0c58081c00b4003800c00d1501440c01c00a1443d0916031202c001004a0801d02c01c80d41c01c0344049103000a903085603041d401000c240707031601c240c028180c0100c14a6480c00c140c80e09030308104144001c116094500714108840383e65100790301d81200e05140407200c400ca42e038586156240c0014449005204a240c01c0d65580410b50310154442d0807405124040d030004066809034070484240340d4024980310b08001d0000030044401d185091864000729421140ca0307640b001800302944c0c0410a1070010440b42c03008600d07502d043c1d21080110b000d031210041c203590740c2c180031601540d680c05102203181d01c0038004544841d000d0905041c40310000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 709573624 1250 709572374 709572389
    0x30c160f050c060a08070e06071407060e10080a0509010e06130b011706060f031024080a02031b0d0f0302060f06040b011b0c030206270328050c0415 65
    0x20707036004040f0f042c1282525441030968a445642e9a98a6030603100c05590761603d0391300c12010050400000e4000c0345041c20041403100600442381081400f609512403c0e11840c400d002003036860489540c05031300035078000a0100041020b03242da4284502400e84001c0c1882503018040410100c2d00041000c04e5002d070150310000d1321070341e03140e0715203002d070f29040c100f1402a004400016003a04001121142030000601154041d820035103101003100c0402d120b09070031030350550440c906140440700c440058444000501402c1300d56a0000f940c9500f4200008101411a46980c2c0c0070380e251469200d402c0e800c208011688a82840c000351505130840b0744158501003800032402e83e0802e4480d084a403001a113070602d0444146403914046000580c0450f4000c41d8020040016207865001d070603540c400b070000010300050308000e803d60700c030300040d440d0007503008881002d4114858004c8110405103407600000c01021030401d42e08240c03c03e151190094105100608400c15a0194100701c070340a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 709574874 1250 709573624 709573633
    0x11d060108070e3703051e070501110c090f0906070c1e060b06040f05011214040b0a020c0109050304151e08090304030f0303050a0b0d020d08030c160f05 67
    0xa40006407159441511440001000c00001403a00c0c04d01c01c0c08148290111254560180d0710141a402c403a051075400413280d01c0380100c2001001000c20204e03c5600c00f004102c0703078150002c007101317a4a01c40c030700c101410454444081c44110310203100340e109070040035000321250314204c0700640c64034070292032144c0f035840f9403000184510700c24480c0700001540115182c0940c00c80060308080c6400c00d410036036410756100120310096031240018001001c0d80b806044400b403034100050a0400e00904d082180d034204042081e0494801c04500d40c01030744007425107403903200d402900d0024010354008403207561a2442c0c20050110000140088500c280c0900c000c01d000702100b20381501e0003c0d10400d206401e1f04080d80c90070f008a40242d440b41210701168100340d40c030b8407140c080c0302121400390082582e0340c05020754002030740600c5050400c2542e01c0301114a0550100390700751000703100a00003990100108031101c1ca60030444000c96106c007450443ca2460341000520107915210441c0c0a00c034 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 709576124 1250 709574874 709574881
    0x5060315210a0c030308090f0a080a03020d0504150c03060b0d0e01090c0e040317060d020108060a1d0603060a0905030a03090203030403080705034b09030303011d 71
    0x140501100c0c4604039680814548400840034440110005824500108601070720462208410015200540d004500714016103280d81000381030300001030200d454a4009a500105400c070015884482d42e501c02d44082d6903070404201100203001c1c120690302030f0360804052000380320044d5045504042c2e08601040b02041d45d0f40c05404440700340c400c1c282490303002d0042240100c11544985148100e800001c22146001d540f6401220310540100304c0301034180003400b06040c0e021900e42d0b94952117a0801823141001d4001500040442c1c0c0000d04100c08940010030b85d4a42241442c0102848000c2074952950304548402c100411189940130341328600001e88074101c070b130103442103d035040400b0310720303240c043c103400c4000e03041c0078034140d815101c1040008005580071000b4044030340036402441e1504020000000700005c0c1080300909800e001450621920708602d84070902071040c108080f03404421080c8654a0042c54915035141c000800001038031484464501039181c0380d910954800d5070b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 709577374 1250 709576124 709576129
    0xc02011406030c09090a02120303190606050d020a120501120203060604051e100302100504090c080115032d021909030807080a0c140c03191e1506060306050a05 70
    0x400c4a215a040d0f024140007034143c1404010660094950816248a085242c01040c6c43c40d601052021082e40000704200e440701304800042c0c0a803981780002d100c3c0c90318010300181107004140080c17807815030020b14600f00c8c1e402944580640c0f5500f40c0144030b50360b52844d5210368a0300c0354030203a01a010725400610a03140c24440d00788030310020300000c10980c2d804050f040300b008004000b9040d03e05000000301c05a03680c00041c5000c2101a9115542d45040102d000180c440460716030341441068401400040c210170b1507030712034154620b00025000400710346c0d100c003903104000702400d46107100f20541c2e04c01103540044c10041c07440d19900311010613814013150503010703074800504600b0090000e4030014442400520035001c1600d041c0440400c41c0c1c4500740300101007208083c0a500002c0d0703100c92410b040c8620782104c0305c04401e41d103402200f501d0704c45503540c44032038201c5c6030701e04e107003aa2007009040c12145400501d09501000203503190f01c8090300428139401418407035122800d0009151 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 709578624 1250 709577374 709577411
    0x181209050a1a07030f050c03030f150907020a080c1f0603110a0605300a0f061707090b030f0f06010509280c140c0304032a03330c0201 59
    0x40310942c0864501401500e00701d80c500b00106078070741001410442c0640c900000c0000c0c50140065600c81c03189800e1a1113041c8400c004203442901550325034040020080d0042001020b2a0b00501680e80d21100d02402c14200701d18400c40800c48641c400d51642203552130760002050b03a210b42400400b14140701d042202c0c07100c461080c8400900700700021030001d14a80b40c480c01c442c6030b46040c200349003107131401b0b00c0c56054111180d0144668901c83c007081140d180c0100b200816100c0302401882c40844421901c1341d80f01d001d07000883d500c1d20902c00035520108856000c4002c42d400703950342c194050343d015132110020720a05106540c000c02081440d1141117892505c2c1701021010003540720b039907400001030304000d0343e203109101d000030080c0c40d4171f0394030001400d80e001001d000c0c59880d800d5180990411090a1203408184180480388910341152960b40080c3c03500580449e007048203040d481c01508000980100c4c6072071042d1443c80080045400880d80c0340d016400900004200e0003444086 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 709579874 1250 709578624 709578659
    0x50f0105031002180a080a0203120a0e19080607050307090602150f0601020109050709020909220201050717161e0c090e010f0e1f110d181209050a 64
    0x40d0001da0305a001d8a81c1980101001d1144040c0031400c45030480c001845e02d003803544001110b4001e00c2e031800031880c09100b2a0075980790106141d080c0380c1d0041000780745411900c4020b00680c80c82151f91035220008030442c00034040350084600610349101c2c01801900300380c800300080355404030302240c0c00f400465a00d1010916130401002c5550b0780c0550341541002400c494103555860103600040340341440504080d1204990241e82e5281603418450786000040421098031920b05030720758015440140944030743e4092070403503202c103854100042c0354660304007414800d8800050061a0310a600c1b601c01d5920702901d1610707240e414040f0310080b4003240180081c0380040311002442004a00d9104014140d4a10000200c0a490072000c9084030000712203640700380e21414100810007009049419042801a001e010b040c0c0e102840c000c8601074090345000c02a00c880001600004040041e02c40c83c2c0c001c0c41c24207120b0398161000c2c080051601a650003400d280d00c0104101003c5c00c5207024 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 709581124 1250 709579874 709579879
    0x19060902100302034803150105091c0203070902070c0f05010f0c02010f1202030f01050a06021c0f050d05040b0a0b0a030c051306081606031404051506041803020f01050f0105 76
    0x81082d80d0a8030800c0560010b11810400043c80080b2101d28045003451080c030002c00703900c0361703883c10308850303a0f01c80347c3c1c20114141c1000004c03c00c8078002d4035000b10030f000e407034103c01280e8031214151001a0074240223070401d1040e203102042d01c03c20301254256a0301204e440300e0ba24940e45440361f00464926107191511400304032290b585030015441050354032445082464070b00042c412001030101607a00030faa600b444020380302e0040c4040d24250b07800c1001421507000514142c0390008112540081c41c0a1190a00542000c0e02d02542c0c003c50440b15100d21301c507410005803a0034901082e107100b055454503440391520b0404189804c2a06038141030302d07000b6907a0f04115103040200074000c0d504401801c052a151000050307e000c2c1042604002540b514906094a0600d00010100c842c002d03600450b4135000c02c2030101260300403c4d9948044d83d00a8081003943d0b4010114000d0000401c0c507031014080f20102c42c0a041d40411010000344200000303100c82d0302e60301035840c120242805440ea = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 709582374 1250 709581124 709581151
    0x302180103060b180307050607051005070207081c0c0c0e1005061c020c0111130e0606040b0a11070807061218020102070509151503190c0509040e1906090210030203 72
    0x4d81406480d200780442c034000400721003000d612540854800d8110711b03022522580000012040d4030214090254001c00c5031006103502458000d107207566000d031422078a01c0e1a580d00401a06510903241c4801880e0000c150315078850382c5800d101130140b001c413240d0882c401c41d0385c0081a1403030407030210360918140f404070001071440f410b4004001e5008000201c1d9640da40c104001e01d4142071000780840d80e0514058180440c034004900300c6d00c08006041070700c42c3d60304002c203125002c0c070030040d681d46050624292909180d40c685103450003006800070707070b07043c0f04400c0001b6155610400728804801c0345242171081201c5101103c240c815420300090258010f14000e21107802c03c501301e11b502002d118061407282c142d6801040e401c1c0d03400f18203621003100000822040c41c1c840c14036907103e41e00d0040308100700c0e208110020143c1c0605440c6074866170f105c400000b4100c074108903400d030841520b01640c00803202d03880d00c00018000e6010403805410004941c02d81c0e1802031003544e00c07450418120f80f = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 709583624 1250 709582374 709582387
    0x11b1b110a0315380d0b041a07020102030408040e060d0213020301060f09210f1b05040506010203031e0601200a02120303040b071202040b0d050702100605130e0102090603070302180103060b 83
    0x10040a0242000c1304c0d041369401e02100d01280100c0c9086008a004001140d4891404040c002c8407c1c4010114001c2da07004100b1702000541e500201c03400c4694089482103541c41c0c51000a03c940300d00e0390007035480741c02130900c1d100e01070481c1d00450480c1d07000d4031540710000010b042076428a038584101d142c01c045809030383c50442d68902604100b1481184040328a0099030303a440245204000b103c0125010490207000da0304280c482d80f134200001f40021401c40c901406038001c20b0b200920040b200c3c141c00408900140d00802c0011501c079001c0060700da840e00149402591028111000c5e446000d50161071910300c0004412a40110f0300000654155561210180d030580701030107110340c21543c204000034030b03c5c00010207031945007502200407506080290b0f009282c402c040440650345440c040d0100055510102541c1c0c1c107241c220030202d5110020134000340280034240c5801e400400000401aa00c0d5150340149603c500112403114000c130804011000c0f244203003d1285800c2040000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 709584874 1250 709583624 709583711
    0x703020a0905070309080c0d080106110a0f0201020c040c0e090709060206010b1303060c0302030a0b0301020922020d11040f091401030206220b070203011b1b110a0315 73
    0x103540f00c90103003004120020940d079900e0141d40000d081701c070340da00101030002a955102d02c102d40140420701c1c004e00100302150815451318040503000b02036800c000a600b0842e4000d010440302d10000410811020645040203002001323080d40c000d00c184104000a01c0710b5000300b00380c4c016180e80b580105030f2a0300341075598180d503000081d03500000e8007001c00000012205d000307902c1000615500980c0340e040800c9000c0c262902c000300c00d4426401071100f88415212201d8225000d0844c0a1f0081110302104014000b88181c400c07a0886506204896035440c0740d5074001c000302c50054160f4501179542d041818115a0201c03014440196114010005860200c020700b010314500b50820150b002c064562102032681c0d40d01240300050042a5502035140c28032a52002d048524808560403070700103402440545c82040c194002040b1110b00014420b045003044040d00000c0c0a142c00185ca904040b030701540c5201d1200407141c20148408007004441c0021040030480c0071144142d800c0c2c0c05103 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 709586124 1250 709584874 709584881
    0x207050303070812090a0503030a022512050a1b03020f15073e0106150e0d03180306020f0324030d03052e06032301030204110705160609080703020a09 66
    0x70901c42e854281c001f00d00140002c1d805107001120059956812810042489140061000911a80031142c0012a0405605e10350179411441e09541d2010400401d4a420100706003a0310242c2c1020300c038008150700001c600141540440840c0c0a92038801101251080100d4804e4002500305000350051280700076090382600094200c0d400b4090000d04004080301050000c6100c1ea445180810401c0c00ca030b0300c684005c07642441c0a084041c2082d01145d00500042801000c004034190b0b4039810481c407100c1013024561008083d540c07040907004044c403a80041d07030341005910700700312150360001013003081004040c000741c040d154058805d0400c0d001040700404100f41c0301c24918290082d9112800709002d00c04c021000c040700da5041100040072914042c080c0701c0080c440b900081c00e405800544a411250304540203c2c2d1405030385140c02c841d00034890000e00500c00e02262200c85079020700f51409a8025035036000b011a079030402c05030380e81128403000e500400380c03071070a00c06031a0301e0b003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 709587374 1250 709586124 709586131
    0x4110a14010806150c01150f08120304050a080408101d060a0f020d06120c0b0c031617072321070515011e06030b060a0e010201140c0a0207050303070812 67
    0x2d0810405031048107050140e944240304074411703a55030301d81c882480111200120040c01c01ea03424880f040d030604010954401e040d038120303160b144001c00001d040180401c500040d00e0760010805440316954099260f4076084d2410000002c1c0c02d01c0140042110350322103000c00550040002e101c203403580480d034002084004400420035400b0001c4011107265402100c00401007030341000c00303054280c00c20703000104098020601520b0b040048003050704000040e186030744501101e5400e80c0e1510b10f042101241c460308030942c0000081801420300540e250724000e0352003488100380d414400100c0050302c1d0011008801d088030305002c0e150809446100240c410248127400301c6980000850000351040d03426800760310743d9610704040101c04030303051004800919941c1400d1241c034070181c00154482c01103800072010007005000c0340765140c0c03013500590b5806100c0030010380303d41445e40c11048980d0141c0c1042d0094411504000b81c03c1c2000400c8443d0f183e0444250782c00c007001c0c8190511600d0015 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 709588624 1250 709587374 709587379
    0x60e0a03120c0c060e01031a090c0a0207030507090c0e04050106051e040906030605220809062d090102160e0c0f0f03160e030c010207090e032104110a14010806 70
    0x10642e400108294000d0700078108030346418003010000400142500c118210003210111586032590164803003200c0240c0086802400b16120b4208070000c071f10304101a40064114401d1100020310a191030780440a000f11075030b505240400010240000c1e01c00070b1082c034001410400c00c02143d59100245444c103105050355041c40c00c0da95061140a68107a0340050350720613a21028008a40005011000301880040e0390000116aa859428007402080040b90041c000010150300b00314484060242144440d001414aa0742044200ba1283c001001030b5016102e69900c0f044215614024001140c01c84240c5000507541d15200c0340d22600720145400e11500180b100722200c19032400614030540074150f2541004450342401090041c2c43d45c9024020f412280701e04600366800302d808c1e000d039500750102040000350f8400709890b40c400c0e0019090703c8d512080074500303900311101c5018040d074052819260751845d09002c1290400d4244228403102c4a0300341c0d200b00039400b904070154800c000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 709589874 1250 709588624 709588637
    0x1a070507140612010f060e09041208061810091d0309060d0e03071b0609050d060b0109050d030201060f06081003030c02041107080712030506030a0b0c090303040b040f060e0a0312 78
    0x4404020f20061001e030801001039160301e00a0213240d40c0101812081c060032900b40c00c20b81015101c1c60311880e45031803100308000305080000d820303440700101032280c083c107000e20b1a00b0346010030150090b014240940c00e1550f050208600054103105d0115490340c5551003e03625044070341d42040075036070010000030741d0980c680e400c000074500140b02414880f80190500990130003441070540c0c819405401c42014014070400a05c095143c40302e01740b40d0700c0c4c0e1098001580c101d0110060b02c1032a030a5105640c401b0114450370f0800d41d06410144c12510104003032484280c46a4058031090800c80b0b00381c000c40480031003000400c0c03265140c61390043c000b8100080c5103501307444080c941da00514003501c40c88030000c1d020b01003080f14418554220f00c1c030f290030803503801d2080c0000e440c0c140f000c038080c1151f01d84c81c01080010121408072011440001c040b86e0303559940e1043c1005a410a1081308040d020300c180014640c0d016400d401003504009010000180c11542d031201100d103000e0203001040b65 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 709591124 1250 709589874 709589887
    0x5090d0c0c0f170106050a030c03140a0605070323010501050a0c03110304060507050d1403131a1005011b021f0201020d0603110a0504090b04030c1a010306061a0705071406 75
    0x50b07016800015000364403d03000da029014291500b510041d9001038010081c6010420108003644c10141c103407980442d02400d41d8600c4240c49240c00242d00b405080a86064284444d03d40c056208500340c00c12000340210450040c021450000340034480c0354007040c4c0400402034070500c030740c9500b035085104e03003081640200e0301c1d1046480e5070040e81091011400004242c410f0000c02c00c12285d10b030010340780c10f0300805191720300000940009080c28640704d080400540400c00d14614190f0aa600b01e0301800c05440c0124140801200500c585070214004045130051140c2420ba40d804180d0060202c184500d84d00701d0b4485000d41d030001020440d5400d0049059440281c0103203002035000c1e000350840c0d2490a800c1001c0000706520280c403607032600d81c04000151820800c9a441078250a101c1034808003410303c00d4000c0b00300d2014141c1d80390907038008000c000655010301c0980f000c07071040102d100e83e180c0d0182c000c1e1040000c00f401590181c0c0040203041e142160b4202003180140c0310a08014 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 709592374 1250 709591124 709591139
    0x4020a0f03050303100806070f030e10090b06040e0d0c112803050706032c031308070303021b31060e06090a09020a0e1e04050c0306060405090d0c0c 65
    0x103a240c00c111003a4000005000e02111541c06560180020101524031402c03d13181c050701403460055244280354a820300c1c400001d0742401255030301000500184007074100e85c03500480d15401213a003144150714115059110382800100c186904140da00c3d0240107144680b1804c10400a02e8401540b00032800e40107040c3c0341c86d04200000c5460b42c0c140b10311229003540380003800d01409402c40d07420580b50040321884c0940d0030366035440c40c1c15041060414041031303030822070640c403541d064203d132800b2130200001c8200380020103504681c02035080c0d90000b031150b81610000c180c028681940280c056441d1008040c190700c9441c0c03c44e00c00c6519280c3c107803451441406030f0305144d212880003031400d410004142489088142d0101103080208000308260380080c1520420740554440103410400040310310480014140c161940d007c10b140052500d450070035030383e48001d0203450080c010000803c006040c10b0190324002c03284c0c003003d07041c50b071007600b821038400b4165001920003004d44040080d142 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 709593624 1250 709592374 709592399
    0xc1401110705030703091502030912031e1801090b180301090210090602070b07051509210702042d020c01021611010801060203030f010e1815150402040302150304020a 73
    0x1ca101d50091501c90b400f500300506003000a0b0b00645051400200144070550b000c070481e04558022a01a212100d000ba001459030141c101d41d100e0188a444980041d8240349002d00100c00d03101c0e18004121a540b0f00464007a0128440c035091203100b404055440c140c04124541440350160002500c40e4079600054528058200180003140c60702d030041c030251303906004120141008401079850109281c0d940356a465440c011019000000b4000c81d00690040c007204c1d007442c1c4021403070044c507007045910203800d5001c0070003244031768a424100350003603c0d90903c0481d40f801c002c540803041d4031501c4208c0060360010f030a40b012075600b0002c4091300180f980c08540c41d640254295011105000000740a481d41a081a0255803052080084c500080c54030039040d40c0182500545030b4541c0d0030710706409002601030019074011802000030702004111494400c0c0051440d642104030740c10144030807480707940406500b0030040c0c551406003c105c00019900039101034440c00f071f50390b034441025441 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 709594874 1250 709593624 709593637
    0x15031401090605120715080709030c180f0e0709050c0912030a020721031b061407081317030606040b070b011e050f09073f0b010c140111 60
    0x1d07503036403028065800c014500c4044640d000d001083e10b00d0518461660140700d50082208111034440010046440798101100450307014015480c200c0d1100d9001000080c5107005948aa00d40600649580c0103802212245c80caa00302800a980c10101c40b20041d24000f003001d104000e0412183c0c400381c5274481082c210125540145456079080f000003400c02c038966102142c0e0185070602d00c1c00280249035440c000c02e0341030805098865213441017002e010170041c40680f80a1900303100302011030085070701328421180307070791180e000795100e00c64007580a2141d240a030680740000001c10211400300b004541000d00144800d0a150740c40c46040800c0d4050b48085411161850040140c245001540c0c000c54190102400417503052001090f6036052005066104021322030116505a0082c00c0809901c4001c0c1a440100c079000007181c400001c1a00d1200700310201c0ca03800c100d0303504181c4149040900165030300700d82924036448280307500e03103840314001d0213550301c840008120f8440d000034501c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 709596124 1250 709594874 709594889
    0x6010c080421020f0d08040e07121409060f010815060409021908161508070c021e120109080901050f09180402011211090d0c12050705100e090115031401 67
    0x548a034a1060145242d24011514040e0000c200303142d000401b401c09030f506940100300b82201d5540d408804a6104401c00d0142032680e20380710407600c1d1809030051482c440e40a00080301d09540350010840400c4000b4811580c66400c07200300d01444000309506c0a07008600248046400505500000e0307640c0b0100e156000040300d55901040440c005100040345200c10328400c1d103236070f442d048070483c290302d001452804000e0032000040314076000c0c4100c1190160080c00ea40b500310b948404603000512040061803261050003520074086005000b43c01d1111361005d00c85042c03503019001510960071201000400c407c062114506070384804400d02844200200d211829007498000540800100701d01060558145170340e0300c540c08000301c1241d00b101ca06491043c070035131260408502001240d0000103000c075041c1e00b4181405000240d441c2620400c441c2210008010b542c02d40304861b005400c1600319644200410038107014900120038142142404500c00412004004105000b40c10501 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 709597374 1250 709596124 709596179
    0xc110d030e0916110303010b0a0c0201020129040f0905100914120409050601050702091b041802030114060301030506040f030c060f0e010f020a08040b04230d0305061806010c0804 78
    0x242c0e0f055002c0020002000306002451865040420b048500c1c4200500c1c541031002c400008001c43e4805d61000d8a1000351181c402c64203001000340e01c2c4440f5004201d10700c11402c2c1000003242d4020381c0b15148025a111004042180390549801e020304480101542c0d92501100300115504043c02104c401254041c41310796a642410180012244003070821810800c044c0700300c01c0181c4480b01c1ea1070300002805400485084403034004461482541c1040071420300e45041d00c0390803581500510706884440d8905402c80d881c80003402941c2c0024803020f030440d88490041030204000c20340c4060814020302d01007003100141d0b1549816a050600700d0341c90503a55a0414111000078030551001d261206025032505034036210041850b50040c00140c607800040d4080303010000e030a00e070060380e01069150002901b4040e081c89490318200407541c2c01090400c40001e00a103490f1050070a9024549070b110344a455400046408414130f600440d4141c0e001c020100e00e9a11800f0300f903003c1c0c000d880c42c14 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 709598624 1250 709597374 709597411
    0x51308070807031d031b0604080f1c0804080a0f020c04020714060f0912030613050106050421030c03081905280c0903330204080d0c110d030e09 63
    0x7040e800c054a42c00c807013100c250524072841d540206104016861010081440c025580002203091103281d000011501c1404259035039580045810030700c2040312030850040110030369042d501d00200312001449280100441002c042c01030350001c5041c06c8a03c1154107829800001c101203900900702610840b005035000e07000e004042004c0c0d40d010800d000c645090741000c580b5169030341000c1c000d920282101000240f80c0b601c1d42c800c2d800c84504808810300c5613503541d25004d4040d03031003030282905000c2e406041e009048840c038861802c0030360640e1410701c503001503103040761030420140c07054080405284551095041500842d8042d0500503c4a11548070341c0c0700e10b03c0760002c41810001d446040c5000700074059007042680742141e0b005100d00c840050050100b000240f00c1c001c64a0416180300e020b802800c550b80e01070300603115100c0866038044401d00c0262001101000018683c2443e40c020012504004420326507003442401d00103803c219500008001da04226941d03081440c215804 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 709599874 1250 709598624 709598627
    0x91e1f0f17010b030d030b011205010b03180706051e1c050a2304030503060312040b07030e0303181201020c0f0f0c0909030301030321090321150905130807080703 71
    0x20300d90100c07120030007041000075101c0440d1716031003072208044c2410f9a40c406070a05900502c522400f0308480c2c0b104115640e150049106550002d550100800030100311595040d00002194401c8d600e05490311030030040d921000d140b9088550034900c0c5102024803e803031584005c2800d003400c600c46104082a6032a18a6a05048400d40c4803030059992126000400040140c100c060b007085d014a0001c0d503e54aa0012a2404409070a030583c1420006030004003241e246002d0308025109a8850608540100c02c040d03076400b030600840301610004540307000e149000f42507000e2184c1017000150615180182c01c60610700c09884800c655040382d0110060001c05010500d90400202d61000d160700f01a1a0b65550780814040201481580300280c540c0b0007000d0801c9241b0031401c44240800d01f10f614000700f5200c140404404904140010762042900324000c02c035150840c2003088021a1400309004007404014121210007003191000e4008500a0030007041020700610b203d65480255180 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 709601124 1250 709599874 709599899
    0x601031b11101103010e040512120108070f03051e16091d0d0804060902010314070519030b010c03260c1c02040b030c070309080d1d091e1f0f 62
    0xc101c0e5456143c07140c0851001080360961341502d403448020525580c9514149281112100695280b00804240848031070030b0405001d040e101c4500649003a103a0310240342c84501d0807400003e1240e0001103a0310419480e1403140c40c2c2e02d007617100c2110303a1087d2000c8180e205147c540c12100c031107905c0e8505400c807803d0200201240c1c40e00380f070003040340031038001c0010026a070151000b40082d4460010b6419680f00750024a1648003080c0b40408606205a001d0200c2d07000f21946a1201d40d00c10501c515a0f0082c421000c9074201a103664140c910290f50480e084452152020950380c94441003403205241c40c03048a12401c641416107039103d40d884030300c10102070040e801c040d5071401040103020070b28908040d260041401030040385c80e65113070715054855142941111490b40324406110158551011450130720003402c0c0490440300001c0c0c0140510700f441211071801c2041c4450104003801540c00b031031780c1c1c03207408200160802e159105944800040d5540721510440a580050003200000d02 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 709602374 1250 709601124 709601143
    0x13121d030a0201171018020a0305100303140f07060203090328140f0706050421090b091207120303020a090b090130050f090c01110a08030601031b11 65
    0xc00825419a1a82c0000c1180d0007600310040c0200d001000714840002d0788140c240a0900000590b40b40255030700c10400a41122486c5400130781010042140075500d081c841d41501c0d09580c4008103103410101344003440d403003915848040c00082103050301103000c0b80301540c024452003001e15640c0002a00303d01f045035014841082040c00d8020110b91190040c10316408448072010035070301c6031b5403801d01050354011590050446821320080004025140802e503a032440820511490300d03600503002c0b07030450202d0050311065141000540d6441c5480c04540a003d440c501c102d0b032409841d950b1055981801c0c4004070080382d000b043e05a030581c3c0026244c000350648003403003421b024000c4002000f070a2164415480e0000d0301e09903456004510b03a4483c1d440000c841c080c4120305180a01c12411001280c00744154000d041d0503105561042d014105006140d2004113804e811645601c2980e80c0040d1440d030505540d00c51884024850b60ba00344c81143c410b4440b450a0820300091a05007287d48 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 709603624 1250 709602374 709602379
    0x7060b090c1c11090d1101030f0c05030c0309010207051207030f030c0c060e100c18060e0d1103010b0a060804140601180f0222030c06080c0304030813121d 68
    0x60080442d030b00391010005405a40681c0c0c04108401150b40400b03041c402d0030907a5400a68104031207050001035040d0744040340c002e0741d013000b001e402d81440c001180d9075a941c0b07400044e41000410641740107240650b401a580000041c500b1050343c1d1030f145480c443c045c00050388007000c207240040c16088000e40c0402c1c62642000d001a44018900034500350000300000c24660b5105d90201c40010304116055640340d030103c0c01c202d803001c0c010b006030000035182c513103005018070440c0102d0b41d54401d0080c4030850344d014102c810701c5100340c0c0e108a003803900501000d40565881007801c14a503200c15000b0020255034441e21000c3c101800c04080401c071f003282c00165648003000400c00e460034505280004441c010b0f0000f00003c0e440a40d0000c0c0c4248802d20304039120480b1230000e0140c18001d20800c9921407150717101d43d1691000c007a10000341c105c80341c2c1c008031018400034001c41d0188a0b1540c0c0031003007400712090b50003030740c0d14280110524851100001c1a00c0b510740c142c0000e4008000b50503804 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 709604874 1250 709603624 709603627
    0x6090d020f0601031a1305120c1b09010501050c1513060b0904051e07090f0605120c010c06020a020f0d0302040f08060603250b0703050901080109090b01171207060b090c 74
    0x454507000f800000c40c404400a81c000c1c54002030401c030120021151b842c1e813040c19664150460b01e5510810303003000c0848403013402184022981d050160203149a000e401600c41010b680c42c0130019211604007608c2d41c0203d019880340307030f61031030f001140c00d0f803040e10b80202d4a80e4000240c1008000c4441403680140640004d90600021a20000303101002c0e10a48010194050b2020071440c205121503210202050420800c003000e603265400840c2518001c1e02d00340046090607118a540d41034000f0307001d022520790703000840418542e8005111041807401200c1c0d100b445507030140d152400302a42040000d0b40410144040786c0030a00c00d0008082031381c003c1407903081c0b9400103605d611215904061105034000c0a0518180301c0400900034406030120030780306c48090074054240c1d4840d01d00705000070844c0d400884c107030301113114100b0002c0d04100701e01c005a0030701d0303034203041c94801d4401440380788100307400030300603000d16401409000d10035900800c2d25200d0005102502c40041d00034408240c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 709606124 1250 709604874 709604879
    0x80a0306080f06060609130603080909070504120213060312080411030c0609190b03100f0e090d0c02031e01060f060e100f0912030509031c020d0507060e06090d020f0601 74
    0x2070b00c01c0d000381c1300305d030f21070382d6496100c0c0002c074001000a407484226040c51800014401ca00c0c007e040c8401003074076000d070207070394040c0300702d5042c800c5009010140044c440400050305007044541d4041c00f145400003000d50b02c0743c40c0e841e40e003c43d0302d4040001611007020041000b42c50b101002070844298001c152030307030b841c0001a081c0e00682d0b000a011354070803080c0044040700c0745078240007403c000318603aa5a08103598500c0d0461554016520740f29210003001840d14a03654038913110f5102d14021b0214141142d10072030381e0010203001070341e01d803190398940494010b418210161008101000140f031515120454210030041c0c0e002d00107000e00700d0203207402a111401151140105860700003200c86602e18240d0b4500b120303420900c088034120100c031f001c164000006242420702101107640c215a00e110f407005c1c81081c0060080143c01c0018030194060044003d0081c5500c80c0d440440c031038401ca0007603841e0920845408502e54040004045465014400e98aa0071007030000707440c0301d60 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 709607374 1250 709606124 709606153
    0x702071e05060c010207080309031b070506031f0e0a090203060a09020901030b0406090f03050a030b1f1409100201050103120509031c120f15081506060304020319080a030608 76
    0xc00c80c4101801824000360784901e410080d0b0484103095404030b0499100c1c206480465541e8000900e20410600700000352200b030b05000039035104403507004040e03526503a601d09041e404030919905250391745800140101e460703c0c0c041040d508c21140240300242c0c3c088107004140c58007a004e00244102440c2803016000350300c0340103925054903084081540319403100d103040300003005009070107840303c0c0c3c1c80e01041c0101903004009108800d040d03a400e000b401c05450402601c1814207034004030080300341034808110380c001c80e209414656021229810710074040081801100c5c07189907040140d646030014000c0103004005501072510320718002d0f041c4000200400c0d500d62803a003410115086a044000da41445039900040d00c19282000b0f00240400c000303010301900b441c1c50318622494906c0c00c04038046500241c0d402080d80182d542c100c490726034005015495002401c00c0e0b80500801c6101a007180324444020b01e014410741c1d4140d41c0b990200c4004084030796a401024075904a100c0449105 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 709608624 1250 709607374 709607429
    0x100e010f0509031c210b0a0512100515180106021501080c130b060c061b0703050304110d0506010f0905010b04031101120204170307060c0c02011e051c05070207 70
    0x24000748880d542c00c008941c82030300c0c54101ca940d1900d40340042c2c404645c0e0700850b070300214013914080e40c8501c0c100e6103900400070008a800b41e0300829601c80e9008004d58802a00000d030440d0a91142c0590040384401150041800c400d130000520360b40b03001000140c2e810456008a6030300c0c0f00070410030b941848443c0d078a90705045405482500400c41c07040c40c2d9141e80d40107900c48c036002031030255100c000300300c441d480d03850071926004480c801d524075040081604c41100d100715071550303565145a43e20303a103085400e2444041e994000d00d10080440000c0c01c10042c5d24040d0464100c3d100b1403c1c541401a0242c50058009804110051108000242c264031000700005024204509a102c4400b0100c009015580c030003100302003110100e0381802d0020000303202c0c00b4001c20040c40340b1585a107050364040f00c09240240014219180518109281e124000c01881c8902c3c1c031519005049030380343d4003811007684901409583ea000e000445404020300700003014031088500e003494101030f480e0700170b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 709609874 1250 709608624 709608643
    0x801050402031b060703120b0d060902090906011802180d0c090506030312070305190218040b0402040f15022d06070f0203040b09011101090503073c02030c100e010f050903 75
    0x284100102e880e80407001f6030300300c00002c030310180400c600b854050400e00003034100e60701c040e03000b4044100464120071010691a041c1c407500c0d05041c0400d81e03070704120b000a51100c54820132501070900c80509542e524031407040b1280c001d000305c4541d40d0420500c60120351002e042c081c400e9000b00f08040c16200c40060046e88091a03080c002080c3d95510b00d03010103941504440c0024603c0000d04090981907007030103091000f0b0a640410004018a051200302e100320b010f0481e500b0a071072020024180700304102c1400002c644191604009401d8181405e80703c00b6503c00c022030202e140001d9494400c002036588180c2900e042c0c1021110141c0194491189000d0101c080307038000741e00700459019031005032040582100800100502d41000c2c0d481e0f4004e89000c41d00340408600c0c49100307002c04015244c0d4180d0203c0c810310080111401c02034485000710040760140030300035850801d65210850b0f0540701501d912071054400a04000401c02e00e0755540744000d2110a10a0007520340b80019501c02 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 709611124 1250 709609874 709609877
    0xe15070c05040f14090d0c201036030605130b130209060612010e0907050d0507060323060f0a0918021002191403040f060f02010b10020a0f021203040801050402031b060703 75
    0x10007030741000c0c00c04c0104d040540c2e045c1d001003027014030241a40d44015041e40407a1025020240d0020350705401c85182d03408842c0e203c00d0882d181c801e001090b19540070741c6e0000c1c80620303460001111961a4030b0845400c80c0c4614066240100907400c0d410081141640310b082210701e1031400f0301000794502402010301421204800340000900100700400c000d00151100410b400320b00070841c03400c15614200360288400080c10409441c00c0c0000d1081e810300220520802540581d450300240100032030940c1e106984241c0b0f14030005031b088880e210f5a011600d107111404560303079003401840f404031281d91902e030031944040c00c1805003030310350f502142201c0d5100c0c94042e50b14061501413407543c000d6804c0141004840301d40040c00540020b0b1000d50248550000e019801910041000f90071072080240003507000341904c00f0010701034841b45d01c162072000f40552040c41d500c0d4909441d68100d41c104182a80d9540300784001d5140400c1421940e9003003c16464000d008000803940500940f28000c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 709612374 1250 709611124 709611143
    0x30b07050a0c1101020f0a0501150e0907031b0f08030304060b0108190b1809070807080a030e091b0f070b010510050f0c03070614040201030c0e15070c05040f14090d0c 73
    0x64640c5e10a01689480894101c1140d02610302400c10a00030008412a0803402104000005100d00481c1701148184a041d000e000c000d407440d00c0c1c1010140c0241611515010000d4000c00c017a598000400043c040d880010341d00ea20b490320300034044030944036186041c0000c040410540c560382011080a0803030b42c07140030903110000d0700449c1401400820303c40310681c0d1402005442c040016120b002c0301c034508101c03a85296103450441d1030364441038000d0001500210003000904140c10400c0d0066020403102014811992096880341c12402400101c02d400080742070a00c04c1d20900a40580405c8528540c0c0041e9001d0183c8070b84122103000502000103d04181c01d10420f106070398000f41c0009041c4003c41a800101d180c0c0e290490341203000ca80342c02d0041103a50b01c00e05d0840d100407000313040c5e6071101c101800c0d402400d80206004598412030707544041050b440314080c12051400221010403022030b01e6803500030a86006088080c0e40c0e10440000182e07591001a00780c00940101045 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 709613624 1250 709612374 709612403
    0x15080121030e09041412070209070c02030a1401050106090503070b04050d0309090e100c030e07050105030a150803030703060b0c07030602031b0a0806030d020c0109030206181306030b07050a0c 84
    0x64880c01075820b02e95078002a1102003105001c0210300c228541801007064510000541c1c41e14442c500454601a4010a520001902050080b007958090900040c116411203081d641d8000d00302028002d1454182d450b10010881c0030b40000d00e50b0f015060441c041d007101410203003a11064001d500c10544a034000e503800b0340a25004042e40c4004d03014000c4140602da00024196980b912403a40e2455224500030400c0c3c000e074403900c03c80400005000242100902d401e0044a168001034070541030140c0d41c03288604003598203102500204210301c041e40d242c0c80d05400207000c484a541c003900e45001c0401005042810206c2c004050381d502c150b0058803525544542c1440b51042c50710141c080b20002418443c1c0c5800068a91241804a04032891448403a004a8541c0404011303140406e207020000d2005203401c074050044540a840810b0800802e00c0001301c5d08000c2d2649402420f95503c41402403007510a000e030f601060034184035182a1142000402040d50820060000d44400112 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 709614874 1250 709613624 709613627
    0x5030a05030304060c26041a1302040f020f0a02011b02030f0d05040f12031d07150e19030c06030e151603060308030c0417010504020f0603100803070b011508012103 72
    0x165a1244401e07140440801682c500c504480d9421f880a8135000c2401c4151000301128403174103441074001a980b0300b0f0f0300400c0d500b0b10014101483c2011041a020700083c1035000140c405440212040da0020a00b41c901c10400683c080c0c0070b141800441d0000c100369101d9031081d00449840c80c0b012800000c040d41c66060035603110303646120080048803005100e580c0641e06800c00080183e10807503003c1480f401d580785a40e5245d03180300c0c00d00c000c544a040c807210b032400781c0710329401c2e0080030307112900701900b82c0300480035803000390811036020400c2d02c030901200340c0c10300c100d240c80480032004041c0c00f4210031401a544034000d08050508824584840e11540701e504240700031a808010341d61242170111030f9112940140c0580b001f040c43e1900c1151810405004050245801400924035580711006000e8540c0c4005e01002980510030400240c1850400c002e00324a402106000000d5043c001403424203816591ba000c02c100c8a10b00502182e17900640b076100c1902d00030500d091620243c03a0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 709616124 1250 709614874 709614887
    0x102071a13050906100f231903092a121a13021f17010b031f0b12040221060601120515010809010e011a0a05010903081e0c010f0b040605030a05030304060c 68
    0x504102e501400c0750006030651139024048403ca0a801d20001c8c0d088803804038103c641248020b81100590300320310000c2001020850019640b80f42034034a6103450b1329411189040001c2d0480b4a1440c2d5010300014240c40352041f504008101011480c4800c282c002400d0559004100c505558909083e5640e07580210318070725107400c3e014840a2070b581d64a11183c4203030011102015411402c41e80c5140c0c644460503a4800e40d00440d09040c100b5601804540300c201e001031040384c00c149080c0361028051130340310710310504030004002005c45107450400100b0800d6aa2000702c1c4207400c020a2001c10952403462201402082c03820b1220341e90b400008a01400d80c01c0d80f2600a54078050020700c200300768042d24007240d001070f20007650b080c1d9584011910480244009446034105002d03450254403551180303100030004181e0701e4104400c000e01d032401c660021004900203503a6001c071001c54141406500d00914045014002e220a9a1140b94903484014402405180d8030036401ea021030080f030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 709617374 1250 709616124 709616147
    0x6050a0b0d0b041e0b01020c0366040c08070e04270501050f0702030d02070203071d0912030106020a0303020c12070c091a0d110102071a13050906100f 66
    0x1a04100296260800138002c00403101801e0043c015078200a00508000a528144841d82d400e0540d0414150000c941500b003000c140c13103440c405c10001d0f0710314a03240071803002c40310240754a0940d00c0e00341d042e500014046401007241c0150308210803a5440d40d00603407441d6028000341000411411500c0008009154011010a2000020300598400c881640d001e007a45803088000700800c1e121840c07030840f00c60701100c0041c0140e10404c499000c54085801a00915102400729042aa21124003001140c59000088200c0d03038020104072058104011042215400100e030710710315418514002c0d200c46e0a80b5014040c542c0000e401425068101702d07031254000e11650003500d52445240502e04035050784140b055071404c16240b008500f900c150388203000c160007881045000c1030b5a4500541d4949a162075055020b1034200090141106003181c1c3c00344000e541203950790f03004111a480701c807a07541005004104d00340821005c0d0321a52040e1181421900302817410b0380380c0507022070303c0c03c0300740 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 709618624 1250 709617374 709617401
    0x418020109150219080906271507033b0126011203020f2b03050c03070c0203071d040224070201080a0e01060609150306180203180307050601091a090f060402090d120306050a0b0d0b04 80
    0x145000380c0368cd8604030a00000340000d99440c8034004005001807031011408100410b000948001080018030003808054154420700554841a200e9035140f8200a590012a02000015064140140d16a100c460340d42122824100514100120f00c40710350b020040040080c80405080901556810040e020080040ba9482020f401c440c0c000c82040000955089000304425941c100d41507029020366a4840307a5000402c0c1042403035001141c20840140c107070989140d6860a04601c00028050400605078680301c0d04000ca180c01c100800c800591500d0034201440d2010501010030050b0200031180b88007003001da2a5141c04441c1c0c040050140c18401c2c0c184000500700040100206015040f111441c2080010700c03a011400d000c2a0322541c0c40903840005500001d03010001090800e40000c005030005040040351808142d444440810075214448185484980e580d818010351000c0c00b42550340524151511080321a5805a90b1090a46a0315110490318603100d6074401d44090401 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 709619874 1250 709618624 709618697
    0x9010b0a0501050c21041802040611150402040903110a141011041503150303230304080304030c05011b230c1009080702041802010915021908090627150703 68
    0x11140344200075401445420082501040059145c8001140b450b10300d448cc14080c040c5d650343e0307500f00001002121011000d01c40701c2d90f00708240745010009614403d10a070394400300f010702d120b00d0300e20785181012100b55040c100703c40b6458a8110400303031411200020400b08685080d11404d5019003246542122502c544020000616600c220446540d21800d0040d0980c0e030044045c0007540d03c82150301600d030100810100303000901c07640113400c444d070291000041c8102d000d110004580310030481040001c0c2411b0411314100d5107801c00c118101c02c4010464a09200040310607111085e100c4901a843d07a0b5091000034000d14404a030754082d8018000c02c90038602124007512400d1003201603001030202d00010401c001d080c0c0000449804940040c43c1e04601100740c1d6801a13192081114100c0042c4441112038551a0241c2005d80c205007803244090b07800c0030b48004101150900c00e224048041c8c3e02c40d45030501c803089503910754040c41c150170040b204500d1524078041514003243c05021 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 709621124 1250 709619874 709619909
    0xf0909070308031003060605010309030903030e04270302010b0d03080402090a020c01020714190b060609061c02040602151b03130f050d170c0d091a09010b0a0501050c2104 75
    0x10303501612001d45e44103420030840582c440c0011822030f0002640100070681d510828004680640100892403000800c0410781d0f4141c0e8440d6010301101d00103100c2c81d4030045610608050f028080c40c0e035648001d03220b40140c491161401490002c2c0904084d02030005540410b045a950360111010001510000e66480c88513150401008180d0280d803240d500442c21084900f0b100341261400e04c42e080141e9a0481e15071104000c440d80c000c0082c140c1c045010050560752035103688246c2c040410b4000300503151131501c01301070700b0810125410b04108910008001000010340c420910706c803240205580c0b039594140603542c14240d01c032005401c0c5401815031504004000400b40713284034190340c800c1252840c0d90701c0d501103190287e80d01d220210040c460301d6006103540c2d00040400d4080c10b201005120412018284c101e004d80d2000c905944800f0600280d0401c1e02802c4d0040c2400e10b066440d00d41240d0946840741410000e28890301c0d41c1c200c45484400420081c0c1d0060305084281d42401350 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 709622374 1250 709621124 709621141
    0x6090302010909181502160812060303040e04031d0303120109110708190201061806090b0f18060f0406081b0a0e01030803070327021e0f090907030803 66
    0x501840100e000604514000c18100c045006241449108501064150015980d0b00f5a054011503045541c00c0e03081c4404000741039080c1d801c00b20280038402840d030b138400303001c0400320005008080900941c0100300400103410340c2000c0a503c01c0d0107103466000c2c0d902d5040741c2c0106030011034026609d8413010600400e80c25140001a04aa424107010040c1d0722001c08000f4141c0501c00c400382045105000441181c0c20000342d64140e002c480c8000243e81351150600040551450800c0b01a0342d5a060140011416817045400e840c100b00c0d14151340c40c0301e01001440c2201d42403c0740e01c1c0440c2c44400300c2d0550715400d10021201000510901c00c2c1a11060103668520001c54206440038900c01c20304001d040c180385d50340c00d54043d100c03100c51980c01c40d150803085070b00c02343c83c01c001c169440700b54481070784040104070110301a20b003200c1d130791100500400c40000c014001c02c00c01400c2080c5030303522a9a844090403409602a0740702c9030541e451180e80c0d4104a003640c000f41c1a0b03030000041003000c1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 709623624 1250 709622374 709622387
    0xd0e130203150108070905010e191a0c06060316031103071701150b0c070303080c0702150c06180303010611010f02120f0c0a020c150c0a03051c1a06210106 68
    0x3100301303036140348561340d81c1c8008407240d4a2522805001c112001c088501c1402c1c035a64034a2030041c6903444243c51030740c0e08811080702900111004a9a401103511407142a090010780d812990840050810303d2102e060010650600d20006007001c0c0040788880b4252010300c1074100410203142c103052007100043d0418041c00814003603c80a10f1030075004102c5200703034400e40e451103031010004c1001074115901075a01c07040103002d0b4900c54900380a060010b1351416145144c180e840d0314a01d444690865085103407001c0a001c50301802c5c0d0002c0d408000050020980e411550303946800041000200d4540b4010b051141041140c9400094a00d4100500e11003107030095115a050100540c2d0b5540800618061000d844005800040100c041890800d40f9565140c540c006250314264403440310a00d41215040304901046000c9107501c842d981e00c801d070000811182e40140040c0c05644a4440780403020030740f80344503600103d40d1441914881c102c00340c621107040c0405001d035841d4035028200 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 709624874 1250 709623624 709623661
    0xd030207020d051e0106051e0409030c0c0303120c03050424110f0403050c01171b090402031e0603030f0405130b0a230d1208073e01020901020d0e130203 67
    0x291b0801c0e00000c0c2c5402d000d122041d80307118603420070000480500420016140f00721054040003105c113090782c0807412401524008500c00c1c2c44050381e03100c14880031800d48900b01c1405040c1450842004013060400ca0059646124840450380a030500c00c0e054000305110202075888000100305003151141070030081c820380303005004a4144204080c011600d01d18160761142858402501066441d1210014a004145100d0019041c43c480704041022a0401ca9040d850321041d0150002201050044507811000a130701961501a41ca42076450500c614441e05005c0c10348034048421041d4035034407403102010010280c82c400d82e914500c2001c80c210407070040c01160803180300a28280790041d80310070415408180002e14105e0010203441403100207107600141302e404417032402440000000792040c1003464030740d0984801140c2c1880491941c400340c1d41c125a204001e150307075070784c2c002a20700c450f1212850040d00b0007001401096a170740802c0d04820140340040140310000040d018031911 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 709626124 1250 709624874 709624933
    0x507031803050447040b03040b0a0c0e06070312020906070c091104050904022e0309030206090601032609180402040e16050f240c1e0d030207020d05 65
    0x100100720a0a4200c0500303c01d070000d1030b0340d0008010000f180c086412444114520440845c20150348104c0d10f0b9840c0d208031000c45141c0444020800c000382641310387e002609480c68000d448200031030102e44640301c4c041010b002d1060300701440c1040c1046804540c0007500107420b458449070546081e1380c600100b8020425824280180142940002c809640403100010a1199a83c480d5000e0101082d004184809030340007010301c101d900c094212010b4545d00e015900054201d80c1410000e040100140ca044030640118004002240c004085104a80d80190322543d030b24081c00305643c0303c0d10074540348580000505d40c0790f20781c2c0403070044c5151265009650900038a05008000c0c0c2c0c440c0f040301001072003144c0403241801a42410400c2104400c400340c503542a03126102c415401200c400200801c1c0070100207007020310309200348240034802460740c890100825050340f98903264052901f544042690203e450000d55a41c1c04401406540120a42d100000000423216128942c1d010b45003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 709627374 1250 709626124 709626149
    0x8030a0c140f1c050702060406030f0b04090b06150711013c110a03023016020f0a031707060914070501030c05090a0b090a3c0602060a05070318030504 66
    0xc0c80a00131004c8600e201c0d0300524407494a400c00e04160b006010040916010b15624070f0007000c01c1c0c8840c0b2900d4680c0d03000d50741044191810074100800c2070030b11140c80c1c403010010710101001451070b414094258009007008600c2da000804290106801c48102c00281110005820b01482202c80405015007403617848560120020820540c1d4040c0d80000a00584c03099400c200500d00f041c9800d01c0b1840c44178401c045d207500b0b800303540b8281e4002c0000a5030740344924014400310719000880901030602aa00c6141d460319540343c0b04803d0b150110a0341000c580050340340c0400282d540f0030b120090f0f1001500700c2005402080070341d610054024540400d1511142c254980c1c003410548240b00c100903e00c0d070003a4207180030700c2348540102a1041d00181e984030b011071601008075060010025002d0b00032024030b00c1c00061400d25203074900c0020f01251400c01445050b50102d80c0320b521003150307030b0013041d0358032004401c900500511400d0099510858084002c1507407140087c401c40750000d003800c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 709628624 1250 709627374 709627423
    0x90b220e121204030305070306050d0b0f1e070c02061204030309050c0301020f041403030c060405390402180411090301050903040609170f010218040c0908030a0c140f 73
    0x440e03251062541c2e01220042c80d030006030002c2c0c40307500b0042c3e10850f5031401060301c90f40c0d0008100c1c15112010f045903841c02820070012480b040300d00440d80200c020003090385880d208502400168030140c806801c0215040100055480b5031080300c1017043c070062401403918190600a0003058107220446560207007860561a42c90705000340c8841ca405968101c0c03a180c60510840190314580c42100d030076000c00d0102001005052050600c00e40c011000f034515080c1c030309418140ad18945078480d54170400341c00200c10980d1840f01660b200e0303c041d100143d803500030100704000d820461851b65442400c2070782c0e121400e00c4030303406005100300a600900c515184c1204098403400303107010341e10024860000c10410712360311150002400410202342c402d0b007181d101d00c02c2c0c00e982c0008000c20303c140f02d641112640d4109881001c1d0561440c0c60100c118504040e90140c9078461050b0702010016084242828092240c40f90b121b113808136000c40c1c0c2c0c01001c003480c150301c0340c05514280e00403000d00e04a0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 709629874 1250 709628624 709628653
    0x2060706021207020607020327120c031608030306060d020c07320904030e01200a020a0605091509150318011803050d0914030a020f060703021201090b220e 68
    0x2d172400707402550051410407400d0610305000c8005048140c000c04211071a0484607242c618000385013442010252410950000a040c074088001154980e44809984104074090001c426260410350850311039969004803c2c0030b0010b400f840c4407100d03131402488400a201407a000400c5000421700c101c4151450072092241c10039501180083d40040000703001900083c8184901424043c05040000c1071200c5403142ca0b8560240d505200b0440d401240800305510749650118010456032600c00d10b092507210124041004442644621400c0499050f4469489007444100411055542c1c2d480c0d1130708400000c0c0d507200301c2400c40455480c004a2130038144201c0007440505030103807030716807503c508030420000600040b00140c81c01c00000c1b24881003440b06000814143c02c46600414911984000039414004041d000606061041003003907840c44c80c407003c1703504403200c8140000341142c90b02d01244640000500c500c84203010703c14101084052a40803000c103140110495480b00d504159 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 709631124 1250 709629874 709629883
    0x20a12030e0601090b060705060a06031b06020c09091903050306130c051c020415080f1005030c01051806040e01150804020607020d050c090a020a020f07031205160206070602120702 79
    0x100d240030742c2c20080040c0701360307500c82d0403175000c5082c00b8165501d03040302500d039581803c80a417854580035480360400c105111100c8012030250311034848003400c0d01e00d0800040c2d035030800c411000707000300e403031800140480034240050605840b010403072248200c4107260040581d48112552407041c4d04503032030010540032902c43c40302c0501d042d03142d0078a001d5040b0004040420141070550ba51034080002040343d10301e941007124a0202911401c0071350410020f80d5a64140051103940000d03c2c62000b0095503400113a0f400d0609020300f01296940004000c450080302003c800701c2c0c200d00002130020700e01122401c62412100c0004c40341100d5201c0e2001150881c5055802951105060001201510303001d510308026920801c1180c980242c00404240e040c902241d940c01c00319804a0b00f003c80076011b011840750300820a0151400500b11b0b03850041d500c84100500c0f0400202188058070f2000c0c0c1c15074003172056002400d031354031803a543c54000b01030750101008000116021000c100c90900001d07 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 709632374 1250 709631124 709631141
    0x1080a02032d01020a03020d0e0f06070f0203041e08190803040b0c0705011b030c030e120304030207091107020a2918131515051225020a1203 62
    0x28080c000c0c15482c00d01140307070a0590140c03148800115030000803084000d100404080b500d984016071603020f40504c3c0f0040340c003251034410841d0420000c0703948215022510700e500404606100e2248039203010100d256000d0368005809002c0c0d100484074504800307100302003c45980600702c8401070602c0c00c0c02400c609034000010502001480818006462448050382c090024080340e8103116964882c9829281e40b0120300c42c41000e120b880d8980603515000300c1c034000700207040c1032089400364024250f80702d005d2054601055004804102010320031300c2528020100003100303101d4107884140e1540f06078045001244254030030007000503015032072444050408248901c180450b20303452040606980722080d0301000f600c0144d03d8440c40c2e43c43c080c2081096601020004400305007050304807582c141500003460300d501010f081c01740198040e08641c07a078911084202d9040c2c461440000051180b83c1c0c10258030808100100d4003943e00041d4074030307000c0c05122445910311003024180c04445209 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 709633624 1250 709632374 709632379
    0x61d0f0303061e030607121503050616051201271a040905070b0a05040f06030506030604030e0d0b130b0121060e07051207082a01081e160801080a02 65
    0x10300c0014600d1800c0c5003030340307002a0180380d40500c203d1400c00282c10301508540ea0310200d14103054000000d95144030300600f01a100002d10030310341c00c1d80c44241d99110000c080c01c4050b50340d00880c80311580302d101a1114054212050440344d40c40301a8100400400c403800a104464040002c89095a6024201c1d610410764207020b100800d0701b040c032028018103142550341e48500000060500c10070f000401720706529680d0f00f900c81c0d040607d0f91390700c230303e03160321150805040505011040d500441c1c40da4105506061400c0e85821050100d0801c80321810003811001100080041002c2c8031102c01d0001c07807048114401134ae032510400300c40c510f001245035120a10004a0a0008400354003050301a044442251011540c2c6c40001c0c002c58100c120035a8603810200e4100b2450704c040000f5400d040e060380600d0354000078007401034071599100700c0c200e04209813503011800c040d103c00c1c400710030b14000da856000c1034680107044d0004000d20601d100300040e41d0f14000146164041408170085900 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 709634874 1250 709633624 709633627
    0x40b01030201081b040801020913063c0905070810030510150b0f09100f0e04050a09060f1d070e0411010210020a2f07031e0c03061d0f03 60
    0xc640046903600c50090200264040c00d0a0218648500c0805000100424000940c5d81d800302411321924280c155000f0704620b00300b42040c480c544040030036042182c641a1041403510900398902d800504c1c1c001400d444100d40140801c2a0388560011482001d41d525141c40584609641000e00c036003911019065401060000c1801c1206400c51000001405185040c2c03a48807108004e065120030741c0000d041400064600403400c1000d00c0c450403071081c2c20f1110169440700e40140080e500710700441d1007a45d607072001541c0001141d010142ca140c1000c01048007840400c0c11000a18080c0098048100300d15510345a8980010b4004141e80300301c810000913480d1690b07a4844602020400f5056008144210310803048902c00b03010789108a0340c503400c44c1c090300c900c000c8100c1440d9400e816100d2103030301da0941101340040c861301181c0d48244040c04618181349084040420002c1c007c0501d9100311001040c440700c0c2e0000f070f51032001e5841c040e08080724012440d41d252843c1c022420107820 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 709636124 1250 709634874 709634879
    0x10080f061b0405031f050106050f041806031509020a1403120702010c05030c0106090515010e10020309130b030105060f010906230a1707050405030c0d02060702030a050f0f06040b01 79
    0x1030791020703142211080400d03818107440e0000a4201100c400c5120318000c10040c000142a01e60301980380141001d040c007514004064203d4042845280580349680507000e2407089540c405034403880003503400018501245444048040241026400c145e1248410072404100921102114000440700034003c10f80c442e0a00c0f18680c0c03031740100b1000d034180109808900c000c5007007440140140740807040001402030508668204032140500810000c86402428807020703600030103440511b030021134042c1503004800400304d28602c00c0300c494581042c04608020040036a80c3c000314507500c0120024400c5565034000d04c0415092599810f001894900040100c103004041d5180b5141204803485801107800030385003480d40c001d43c0c100c1c00103a4250130403200e82103031051268010216203041c40c0f030a49404006680c5d07080702140f091040d10340d00309030001c5640e1a0211841690701038281e90f1100d105040c1180c48150030030704080da80c0904403400000c82d03c040340481c8269030103c5075040d985d0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 709637374 1250 709636124 709636141
    0x509011d0604020c0a0305130f05010c08070606180c020106120812040c030b04110f01020a0834030e03161206020c01091a160201021e070305120c0310080f06 69
    0x158090070032600503074200a04103540000b4000703c80001d005c0d8940c580d0340c824140c9010b01c010047c0e4011803c03420984014041030ba84000e00c0a205034114998030740300c0d102400c1c1203000382200d92002e0307001c1c0d800303450105107002941c10008606100d50003c004555451441400c2c88081c10001030581e0402c000b0042d000e6501001d944c3c020f4060101803051903103030f40d14461000c1c0144c8003a58010030b0003403000464038140e03201c000500340a04c060128a800b90381e412250307020f1002d80141469044060014a00c400c10043c940c4250381d0003d0104143d039410090000c50b1000e2120740030307000e40e0b146024600d9955110b01c085031b1000708161914070294403824029001141d0401d0f255480750050b07404100c64816900850310400101780c0281403525030326480c41070400d003000c1564014842c049904203d08003a62591250301c0807665500e440b864111118823449030f0340032000003400184000145200e0140d88070f6028001c1254143d901c074032000f03503201c008a4503100d940e4402400545e204 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 709638624 1250 709637374 709637429
    0x1315030c09080604122606040b06160b2a0d050f07050703080411090f06011b03081503070b0c011506030207120e061c050f0a05060d0b09070306180c050901 68
    0x86000c1c503007500101c15046c40302168046c4402000044003000c0c0a2008034a0203102c0d50000182c11590715250055200c80c160341d0f030003424005002c4240000001c0d548010582100a00103011300508000c9981c0c00b41c030340c0207904204086201c1d240360030300280c4040b01c903511190050006031074060408a6640c0c0407505018020400c42e003116200b94400481d4460705031990003a0401c1c81c100081e40b800c6000145018440f030310241402231003a0f00003000c84d0700000e200d038000e01210b601e04c0380940d001001c2881c000080e406040102000210344601d402c4c19480310752500218400c4020403551441c0c11800c0c0d00a1003805001810000300c40c624440c042c40c05503082c207201500c2c1c181404002840c0c04002c1000e08107a43c5001c2d201c0007006a00003c900445500071000c04041005080200224020760110315004000307182000205001d50410010b07240150340c40705062003002000802c1e01445008103108403056041602d01040a00e020302100b8142c03a0148410004900c0301040204d40703 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 709639874 1250 709638624 709638653
    0xf0f0b0901030f150f0f0c0206010b041205071a03012313021b0d0e13151505070203071d090109170f130906030c090603050d141315030c09080604 64
    0x2d50000e0f0713914090300100c078011280c4440390380000081c10b8228003c2c1100b0b4440003010072085410000050048403e103806803010754841c100003240551356440c080340f90503125044090580105d40c1048001208103009605a801001404145c82c1000002c000c5400c0c001d51840c2d40844280340030205181558007515070501441c0d40a11078a20315162603050005c1e80e0300d03520004000150700041400d00340c4101d0f041d0007281d00108080948600c1001c1402d000d4022020151020000c0c159050f203e2016140495001070960f010075030350f4200f030f081d0032244010b80c088600e182c6c400500700006c103120300101d0076004020600d1303a004000124410b5800408000c0441c1014000241c034010340b81042c1e400b4110803400011600c0c21810105d0100085510080d030185c03d042080c0001800450321f20754031522410328006051144041190b40d01600f00040b0741d00b14a04070000e45050b50016104444005840030085c408080e1001c56030b500d114000c082486e0700c42e0010800258000d241d0076007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 709641124 1250 709639874 709639883
    0x171906090b0703020d1a0a0e100902030903090406061706220222080703152a08071d1503070203071a0402150406021b061c0f0f0b0901030f 61
    0x2210046070361200c444070415620503000a40c0072a071441d00000314820100f10602d0602c401c4030500904000800011640c09599400b10540010900e01e42c0b011003030f80301810801c00159200c0c03901d851760031b40c3c03900545909441141086c2c00000e44d00c1c00b0360345070b041c00d880d103c03000209581c0340f41c1800401e8103c5d84592040c06000e00010000725031a102500a8400d20404014000c812001684620000380c0113035040d43c021940800009003030007904000124034080c0403e03a030140c45c10303818200042141c5031044030414402c40c8459a84888074901c11403c40d141c1010300303014589071138000091130301c02a800c41142d40c0290403441800c03001e10303404605441160324104542c0da4006800c8003000301c14002c9000d06051104500d4007014241c032418202ca0f07c1800c00386403001c025914544407422800c1c002c0907203061441a240c240032a008141c08500c8112084004942100104803000742c0754580e074034040c0400360000044c083c1030796600c1d00400c00c1c0340c1a401c50703d88160850581c00b0446 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 709642374 1250 709641124 709641131
    0x100203130b1009020c06041b06021b0103151e09021905031306020403141203070e040209030703141005090105060303030c0f070c030308370b011101060f050a171906 72
    0x3c0d24414a00062444920500180550382001e00d00611500e9101404008405402005211140c5d001825030303038208080008030402c001c0440142c0080c070140303580b01e02e041e07150301010901d44d00c42411004c17048dd00c4042100380d01d6803948018203c0c0140c1110b00c030090740300218103003164414000b450b0800140b0466010b25019944c42e5401c0341c0c0a40e00c00c07a44082a080f5101e11200180641c02d00440d000c0d10551562401140080c025903402600c00d21a0b5400708004529860402a8a01035640031601080e407051520749903a8a030030b2411a000c1c401d0810380006c1200760107001d01c41c0201c0001d80118155150b0000070a02ca8020b0100300021304014044240401c0d042d001c480c0056000c0d449698840c101541000e41078107441920014044200038090b175040500c0d104484140b04800c070000d0008550001200c2d004181500c3c6170300c543c00c1c1500410000306401e00e0604440088075450302e02941d5140140c540303040391a030203110780c015260b01c50f00b00802c0001c6800c4903100d142c000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 709643624 1250 709642374 709642379
    0xc0f1009170c0901120804060309110406091a04060f0302100c060906230f1f0305010f0c020106060206073e011407020f070515090603010303030905100203130b10 71
    0x400e203480100021071459101908901150809019050140000030b107440e90301006502e412115120703a11907501010f0366081c4207400c4c0b222860900304456002032003807080300d549444581c0076002d117201240702c1e485482003528841c1303001c1c8241c900700d40f164105540da13140395800300040c44500a0030030061040104800000803c584180b041007480f403c1d0001d80d9198a202c980d1000000c1a000c0c641c0359444000d00c200120178564203607002c6e1441101e00d02141d512888044103038003a5100424644c02d051540c2540210b6820a542c61200ca80c020441c0ca135507008100d94520050702c041000c1403082c111183e048011003502c400f4200c0f01c141c400303070742c1c40d00e0200c40105511101060110303035942e0044c10a00240380c1407458001d600b074802800968660340c0200d40b13920781071260320300c519200307044154501c044105442c10000002c02e510384960350b0b410040d01904000c50102c4050003088101c021201041c0300344c2e0b0003140e090f112000c0d0080b05070f540c000c1c40500900500c003a0354070130000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 709644874 1250 709643624 709643639
    0x1060609061e110f33060d03031e1a0402040303080109050a0908030c09131b20010c260f01051908011802030f010207050d0503040606050603040b0403110c0f1009 71
    0x80c074030700d5041d01004000c0394481d17000c0c1046903554107902c0018040d02d0a10603410640c070382c001980041040b00c00c06022002480e054004260100401451003841c40204202503020b0340003003c0100030b0b06840b0182108801003001702e115500000b800700782940011300a23844140d03c090307440320007002c00180c0c0400f5519818103e4200715001c40034030704001001041c50a001d0155191882c0c5070380144480b04501001402440402250134200003804802c03803901500280e00d9105020600020461508500f100802004800310000300c1040014200802c0728000c80c68107104025064810f2216403c0c6802c0001c038080c8060f92010700701141002050342d003806e206500d0707006d0042204910360940c0d403051508040c2c000303040c0410703a4418400c0d800410f001195501d10340c2000e1401d42e65a075100e141c80c900514283d04042c1d0081c80201c1080200038048550a01803406603c1782c0442d2030072003106581d80c0c540c41030b8107a08440381e1326842d151380c284010b0302c800d6001e05040200c980c540340d018 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 709646124 1250 709644874 709644883
    0x8130812010b03060f0d1e0201050d0212091b0f010825030b01022407081f06053406150810060603240509060f1201060801060609061e11 60
    0x408190800001801030905d031601c41740c02d13141002e489520032100c06490700050317484500c6144004065502d60380085a1003003041321507140c01d00f00d003151941607420b88541104c50031101c4460500c20b0040c181c95030012210b040001c84001080e94041e800c1076801180c0c24900a807a91059049c1c80080701c3c0d0442c1840459014202e07259400203040030070b10002840c0600c0700600951032050b11040c0300c400c11b2048e03142680030005041400840c1c880c0540c22442010750682ca90580c0c0d44040c012840c00d6004000744045801c6078521620441951480c5030800055600900300c009603920000028229030481e03450704249104168240365603a1a503400c0401c2103035000d0203207948039020300049415110300020720341c18420400c40c4a038032100d104140b04943c043c1e01e11034081c0100150041e51401c0c0500a810700c0a01013183c18080c070594903010308068000c1d00f00f954203046000c07030401d10500090b0b007152800c0c2c0e00c0d4154227141001c801c2c0c221425070010070410048100551400c5002c01 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 709647374 1250 709646124 709646129
    0xc0603231608010f031e050a02060301080a03170c0d24060c050106091116050a02100309140c0f131401081c08011805071701120b09010506010813081201 67
    0x1a10390079240d2540401001c040e8140c11600d245080040144041540b03031000300401c0043d8078082e60340e5032403414494608102c01c50b009510450000004c00d054001149002c00c09200780ca421300410710810302003514076000c4440344455501801078803c0c0300c105402c5042c85480c0c045031b002085c5402103100c2803030782407500013002050b14403044208200e03003445400001c20ba045402c02410810901c4194a403143d00800d9202c103440b444240706100e400c0c1308100da0140c2c010008030200c1210304018000e0802280151507001040400c034040d4800400c5801004800400e00820f51024070204400284445c258160003640c4001e50003170003128020303942c0a0b14000c40100f4001107441009405034589050f0182084024001041002441c0a100a801c804404045035035500d10b401140c0c0101521b1100c0d0140ea41c0e940002000000400700180d01e90060102c0103003030b0b45080002d4281d60080d100240000c101400140c840004200003041c10351140854a1414500e1040b00341c944000380c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 709648624 1250 709647374 709647391
    0x8040209130204060b04080c041506080702030408010204060f1706060d0e07081510090c0509061c090c0501020d03050c090d0f06020f0a0305070230070501020f04030c050a030c060323 80
    0x905004001f4100540c03000440708030b038240003d0b40f041d03a405400000ca48601024030035044007007103940c1d00900550b80600020b000854903690f4554000302035840b0024001d01240424660711a015442403181d80f08001c013400381c902d0300c2d00c0421020003d00491005041502683c1130214180700f0030f00028006d4a801134802005050900c06645031183e00d0780014070303d41c1f619060340e0629422406842114204650440d00e4103010504035031602030040182d41c807945001614400c00c209002c4007800d8440c203900f100d4103144488030580403120103992040c610001070242540b20728001c0d03480d481043c41040070680c0280940d840c101030ba04004002c0d40d048601007500e00810b0707818410198803001e54802804204c0c01000c00885c403040e6900380991844108500314443d5249004403000d682d4844021591002c126414840c15040350104a031400c4411800141c585440e04000d015642c011810100f07081c0741c00303403d400400b2030482600001595821014020401507203891261030300 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 709649874 1250 709648624 709648627
    0xc0d080c0405280b0304051c032301090f11040b0a0306050907170c0a08040b04060e0d03060f050916030b0d1a060102071a071b0f06090806090102040608040209130204060b 75
    0xb0078600c010103003e950840c8910840520404c40456000100142095098030380c003024a40c503103e0440180c0000d080000030808400004042071103440c00d110304032030070000204070441100341c0d864180c0c0c4802c0303e50200100248001e02035281300314018140d038481400d0004256550700e0200c0d06400c000c54000c0d0100b141c8040d40541681065902c0c0e40c01b44440c0090342c58820902c1c0042c0a500d0003030000342010382060001401c11940c1e90046007070600e40004c517908481305840090281102e0300a9220080c00060000355504040034454003031007001007502148090710364128000e0005d2003049600104401000c404540746032410901b04014a11021007442c2640000e4030f00803040c1e00c80095070716002c8116101c1503481069620455100440030403065002114800d51125500310000c52a0701100000d10160002d9042c804c4600d1001540d0301343c0d48455005080740107512581d8086a141800100180b405c568090781c010a03242501c50f0280c800e4001c40c0c01c417a0b440d004500319990 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 709651124 1250 709649874 709649929
    0x20f18100807080d080c1c0e031b0601050603070f14070606050414010302090a0c0507050d02010e0708060603060406050c1905180a05031903020a12020c01140c0d080c0405 75
    0x1082c0300280107020681d00400400d24814001854004010111426084041503000105424900e94070019801410034024241104483e50301d9a110b0b10009001c4109058000100300c804560301d8100d45008100a05543c0c451009480e8616071008000070041d1801009415001950103009424003d000001c0c0d401e040c1411f1208941c0003100d50000d140300e24004000580d950a0300f95401003480501203a000154070060310540128100100240564076030320740b1180d0b05500c404180c100c01d0301203906469540040d0358a405040d96025010340180b0002000f08445030441030304000000d005502d4410040c211104040310b1021010000d03e00180203030000200d800100100402102d4202c601860300b00045d0751540c81c6814000001c0c6081c215006040c020b00c204d00c40c0d1034005051401010890720001e485a9142030454081110664661400c103941c00559003c2540c26006102c80c01d5644820f403255000109030080000040001145a4488511400e005000007840001421 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 709652374 1250 709651124 709651139
    0x905130b070203090a031b0b0708120c190315120b040308061c02090402010905150322030c0b0c041e09050702030a02030a0e040626011104060c020f1810 67
    0x403000c1c15003000c40d801400060542e40c0c1d01829102240c0e400f1120b4071510000c112076414802c016070141c081c00c03d0204408040c01a110010b2080c1d0b0500010300005980708004000c0c54082c1c0d130030359040350050001800134280130381c0c081512040322075019441541d560300b4081d86240a0740040b600c4103960000c0c0000c042d080261903400071012260100304c006070984602e80100b0505d40607101b400c6030b4000c02c1c1503900840090000d000701800d1fa0340741c1c000684a80f01907510586124030f612642c030356141d20399a0008600e4034555810f544800300e00405480340d2a0343c80d0017924601070654100b01c000350f0041c11000665105240354666008a07140c10f1603041100d030014184030542d0401c206110100e607011048402c01034140c140820500c0070000454002d14882e080a5800e080c900042c160025440c2c0a0b52407507030504000740800080c40030062800d000380d200303c40200705000320410041c540003050001014010f440b5144411001d8048141c12009070303071860034000e40803400e001d00c4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 709653624 1250 709652374 709652393
    0x2090607060c0807110a0b1005031c08060d0b040f03090801020d0903140a0903080a2705041a0907031d0114010e01080114160e0d03020304050a09060f03060b0307090513 74
    0x10038541005c284050300c07202800c1c1ca5605441d001064105140000303403c8004001040f0043c00000d021a94902d4068070802e9051114860b1200400e034000e00007803140c0340002c4007085c1c10b41d015000b41c00a49440e0b5901100100b2080120706000442d44045200d080900c060843e0b0b48141e0f0000ca2114054203007c1c0c000040080d0440c209041040719511040d0415190801c5a5010704502c1d40c44152071802ca404e4070300300324450050301200070980221160940050190f070f20841c2d0803c00d628030304580060029a1322180ca801003210400110142d001e81c4c800c00b800041401101d000240c400482401c5a00038040d81c0901175081c0300620042210400280c00740451600802175403006040c10724800c08020036501000300c45241103100c103880307081911282000500240320100640c41e010351250000d00459010300360500c0c000a180019001d1001110411340400b0901030540e00c424000d00701a00d03a1079054402d9200c000b4a5068512945105407112801d03004801514500345561 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 709654874 1250 709653624 709653631
    0x114041b060e09060904030c080d0203191b081f0305060406060e040506040f0c1706150d020616080702120106080606060703021e120f070606060c080f0d02090607060c08 74
    0x30032031a440c00011946840c0b0003c0d8200d00b0031582094503940da860708480242400d20003d103c2d01012035000f4481c0d050340c018500074010180c9000b40244061a02030032154200400e074000e403050b5000d0180f6a0150034050b403c0414a482c440c21002c06c00d04510340024117510444840d80084104800c2c81118800e042c050b00401d0038940950500b516103a50310303a00640060881b003014260b0008101030b0303007a6032005000c960700b04c80055490070541350311110201d039070440c1889000c82d005d0f160324110300314010307039940106014213040040c4000c800e03942d9030800480e90364404100c40400760f034a042c4e8120020180000108201e410140807a040600180600d0f004510502106c00025004201640400680c1100e422980c90501060345402c044180e20035806000007052003110390300c0d80050043d50301420061016541c1c0709021551188030b0781c0064603a010500590203112181c10083c40c01c0540000003509244103c80014150b50140301f088030850fa0341c1141010054005200c141d0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 709656124 1250 709654874 709654877
    0x7050703020f0904080f0f04051008040201080702120403150b0619090f0b0909060310051806010f0b0406080907030618021806090106030e0f0d090f0e060102030711030114041b06 78
    0x15a0305044c3e03901e89960181c031081120b031b6080031a40c55a5074490109607002004028a0420221100c6001070309140c01aa42603000403034031000a86400c1c000203099291140402e4024606891900e5021480382d400301600000c2d5150390103401c02d55502005008050b50806010391408010180139084503040d500040001059210410610071a803040d214024403d0b54012403540e0f600d0300180c1083d90400003500c60343d1070001030010110b6032510021194803c00e045034610b07600c03100c00c0c03220a00e441c490010410000c1009000091295061603004070b1810201c5480c60348070707910741003650303c10300c2c07a01e0301c41403602004400e6141140c15890008211200791500703060080c08030f4000301c1c050080100381278803044440c0100c481000801c00301076401c42900ca6004202000419615040c81030030059041c501c004a02070b910480028000c1e60142c00035483d2107215542d0050485106e000140d040d565944001812403440b20080d21441c810035000b80110b2030060022441c2106421440 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 709657374 1250 709656124 709656139
    0xd02011508120702120313090606020c090907210f05061009021204241407030b0901081c1101020a020f19110d0602071205130504090317150607050703020f 68
    0x100b0540080454000d10b03010f840740c41d180000c603518186903101307021518081c170740f061000040300116644442d0650700144d007900c10042e140010003112010903240000c03140c0080900304221400c4c411000c2c44800001c031119404c06203515500d6500102210941c0c0503089032013000f50440c02981d0842c05052514400c40c01c0c500029802d20503064020001080000150303e8614500003035500c2110300d10b5080410b010240200d082d5103038002d000d0301d4001c08a800c100300301c5030510b42010341e1f50584203900300a10422407412081030080da03c03401b00380d06100b5007001c0c2251001c001c3c00101079401d66500100b04070002d0661551030090a000341c40703002581d90010100291000e48010200c1c44119030300f0380942d60500b4024000e10800c03500038421500100903142c2c064124014080800c41551800c000c0703070b9a01c0910003507940322207000780002c0d035000030f0601d8010a075007641c5d088074125010f0740c20b0215060100360294880c000548290340404402c108610b40454250018081918082c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 709658624 1250 709657374 709657393
    0x3081006090b0307081506040b0c01060611030f030403031b030504020a0510020c1302040f060206040312050103030818010f0e03090901082e020c0304240f02100b120d02011508 77
    0x350320303d010142100d030400c0352200214104034503146a88405010042000e50386544c1c94840c800d455008140200095080c41800a800b50003900171444000c40c00d400307945882c02e09600b0740c0c0142c1c401002201419941c0104a1007250f51a2031010503c2564030700148a00307050041164031095a880340c1d1060198240c9911030301e40c041100003130800190758124900e1040c80700d1801a00850304008000305100c080041ea04c0d43c000783d0540502c1c0641c4403442c0c4240c001d801d80c02030301c0003400040c001c40c00385004182d5001240d4940012903044500008451400160810a84c0c441d039400c201564400304a40c00949821411240107040003c0104414044a211684201402d000350300362100e1003680448210581d4044a11260a4105490f42c1d952a0a1181c61400c1c1a6041c508140c2043e01c060541d640512160010100903400806500005085001c040c0c404140c2841e04410509580390800700204610740d5216450b0700081040c1c54440d00360080329401da8044410355101c203924 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 709659874 1250 709658624 709658639
    0x30a05040201032d0c0e0315061003060e13140a0506070219050d050c0307140619150306020c150c030702190f061a0603180d03060e060d1403070308100609 68
    0x2a04d9052038000011403e082d203204152051007180842d1500b501030000008000f090f0003462070701c02d120031031740c940c8500c51a40049044911034020301c001c00404801060f0039131000404006624070403c03000c640d900401c02000c4c280240003404403800d81c1b0071018403220540610644403400100411400086116103c00355140415902c040501500107400014410b06100300e81c1c03019040704205c140300740e84046a6580315000c03a03250100030105c01200d280c840050243c280400e03c2c03455034450780c60039070312000700135405000c0c11403580c41454004c2da0900514840107101d01181f0340c840e5160b2811f008040d05004031426a1a0980050b03280d0308005010483c0410581b41c0000f40000d424003603041e01c0d5800c0703203c1109241d00c05000700c104403c04030702460780400d80a000060b5200350154007015015203c1070700030400c03445034100000b041801c201c00f07500c1c00d40c2e010b0761103422060542203030f00d0b045604c054400d8002600074001c1059500e4441d00b100b00820841c5050715040745440394 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 709661124 1250 709659874 709659941
    0xb1303060b040e150a180c060e0105030f070f090f061709010606090b03060f0d0506060102010e19020f0f0d261611030f0d020307061a1023030a0504020103 68
    0x140211140000c40480d0300e1208a130300000c0e110741c6e012002e0942c0000382c108070a00819602c0380f0303400500c503500c8006030780d4864000d4034014541c3c000040d0464581c4c91007134a444209120141c10031401d40b90003e19400300f0420f00300101815110b0169216030101c40801841008100001e07980c1000d9040010907808280801201c003100078842e102e460791800145c9012400305500d41c4034151804038002d04c0f00100d001401024240c0081003480d44069865031140c070110040817804c114804040090700700402d6103007210a00130f0980c05101e10703110004800d0980c4900039113014000c41c40354003e00c4104001001e102072454900d0f4103141c0881200f01c042030f62a240240100755114060301507403802c010402e4002d0054050740c1090050b440000d6403038202d91819141d15041c502612001055195212106100549000e280300d41e081029170b0840d40090006007c1c0e090b800c0c0b11a10381a0182c00745000f21000440411a030500d40001000d8520022000c641c0c2a41d812403090101e1a821 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 709662374 1250 709661124 709661143
    0xe03100b03210403150f0204060314090a03020c010c020a0308030f1e010311150903120306030d03090203070501030e03160f02012c041505133903150b1303060b040e 72
    0x290b81203030281d24001c95502030100780101b21421400402c011a41d00e405800c003102c9800c40a041c080d682c0d90b200081c0740d0705c09401c0400780160300201c81e1403005520031398000883d02d00142c40407030b41c260340340d0b62543c166200716007640040180300c1c28450108440f200a40c410700c80e80360300e600c0b154155203410400d9080c2441a0f0303c00c00c504038040009614103401d0301c08000d002403c0d507111810110031102254412030b0030f588240034010344800c00c04d00910400c90034940140040018a0600006400030f00c41d008d4058280d101c14050740c0000007071000036009480c031981e8003448100b06e92002400d41e000c0c0a00d14040741210b81c5400c45564031800c0e8040451030f003100d002c1031681244409031441c8c83c007504000d07003109202c00b000402c01d580c0d40100c4c248801c88c8105a03034200b07234003104070300402c0744400d600c0d95500190385ca414442d1103a085029041c3c002100300d44010f64400840000340d0200100d00403075a120207040062100030b02c1505001034060310709101140c1ca40c4d82d11501e40c407110 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 709663624 1250 709662374 709662383
    0x5032a06030a0908220f1805040f12020a05060705040b16030e03100618050c0d0b15190806063f0c040e0a0c0509010f0e03100b03210403 60
    0x100c005200c25030700e5040701d1500b1341c12000f09903035040c1080078840c10710000c1d601001d03000c1600400041e1959503c0710541140c06030507039400c0c101c90034854140601000361003502c1c808208612000440c0e07422001a489640342d40040c088038005152890405c1c60040108080c00820701003080b095103000c04660a00300421140d00d0000042d00c1d00f684e4441c0000c01c03094042c8110241182003801c19030102c820380f03003440000030708640c0e1003400c10192102190603603468507040c00799041d220a607400442d80100020716104201e10715062844d0786800014000300d440c003100c0c5001100c19046002030f40c21000544101d458001c0c601c884240c0e001e1070070783e600c008140c0002c01842451443e1800a000541030707a4001f1346046c180a0154540c026000300d0341424040008140220384a1290701c9980c1481e80324141410141c5006556101c0000e01c54010701072984480c194542d4103000c0444a2840d14900092a4441c0c2e024035140c9448203010a601810008000c094141088283c40486e54071 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 709664874 1250 709663624 709663627
    0x50f010c030908010c200d0c021c20121b19050604060302070308090106051804081b07090b0d170c0708030a090e06011b0803070e1905032a06 62
    0x8901e8102d8004142d90b008401a500c1d00c080d0040c03466008800100c2445209103044080c5258840c4035121458010301c8804501120280c0c801400e142060340c1084080120051100302203441c0c10244040c8118003140007003010700015404e02d40300d140e000b100c8240c2801044a0140e2202101c902507000e801c45203e5110b08500440325914035400d82c000e05070140185071a10796480e0080c0281d00805011404a802c0e03500090070188144107460032140c004096802c40e01c5029603240b0702d00400703842503c0120003008600920500841090540c1107490000c0c10000d14042a45044603400201140b0031038112201c480441d07000041a044002e007490025510082c284030603181001b07030345c07043c0c61600010441c1da0519411041c500102c5501c01d01500f03103541c403100110b4101c5030b01e818030040f6000f021265400324003444007841d0b1003002400c2a50f01e480b40500042d20301c0d030301c0d40b400c0000390400b28000d01560030240818030351b01c40307001403a4880d0000d011031203100c00300d600c0109006410 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 709666124 1250 709664874 709664897
    0x80f16050c0102130305070806221509060911030f0703030c1e0c230a061b0305090402070c210201120c14040e070e0a080d08100506120708070504050f01 67
    0x142981214a00e000f0080101380c01035407450b103540c07941c03c203115840b6136004440c00119010340003810368180d404030704c903008015002036035141121001c03020140e4815560b0000301001951910409020b6800b030b0f40d406051b60390700c000301480d0920320302c00800d254104000030400640c008180b07403106075101c8650081c4c06180a07400150001d0b1035405042c0364060400050042c50741884441d48500c0500f01254042c140710520240100034400c0100048045000f41c520780007071131410b920140f1900e056803808900000080598004410a4130390780c928860401004052803014102040c026001c03000c20335a94002a2848419002c6407030f030191a0f010010003071380b06c6d07113802c240c50940c840c25549403500c440b0a00c00014040742c02d040440c0c041d1450040501c5c003600610206c509110050600000c20202110921000f03003080c4500440b032500811140d4039940542050307007494074071000510304484001c010f5100a0b0403041404030030841401552203440050240c4003080c2480d404d01076 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 709667374 1250 709666124 709666147
    0x40b0f0c010630140d0c060e0a11040c02010e030406020f060f0705030103022b082104051b01022812030b090601110307020d0506010620030414150a0201050601080f1605 74
    0x8880742d150b03e0b04e40c0501c1e003000010a1301b04180315031560241d10f040120101c0200440d40d00c14070440041c01c13021250340c5524540c41d0641014400e01501e200100d03e81e021086807a242d138125402c80009a0050800e07090505001c02ca400c3e4071500303558020300341d0700306480068032034403040c04080d0003036004110f0078582e144950043c0404031980c80c19a03203540580d0030840426002803400c3c903030144400100c03503214020804414099030304000544504180d118094022100402c210380c1540075005200c080d006030554041c0c8112840c00b00c07086181000d24101d0f117181e45500e034000600d4035044070220341e40c03107107017020342d2000c1d00b0300742407050b0510501d8039071442c09980c10080d800171142c3c1d0b010b4204940492542d04845080e111000800c04bc4820081c1141e038607082e004c000c1d80280001c005041c54200ea10503650303006040141c0007464a980e0703641e960311035500480503079152003d000613540d100c1c0c61103500009000d4104820b060104082002d9209400d02100b04080416440c44d0302 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 709668624 1250 709667374 709667393
    0x3010e04081e0f090f10021c020703020303030112030306170d08060a03080c07030507050f030c15190906091703071515060c0b07030e0a1205040b0f0c010630 69
    0x44214520b029118110580740d0800c1d0740c4002c00d030602440c03014032800d682d4104010007150640158001d84584500040948551407404500100314401c0d040f0000160711306000443c003030b0544064101234404603050140c20382e900355002049135002d1801343c840104003c00c0101d420340307207881d2165507030312800700103014072400d0b400181c5001d00c00115120f0001e0000703011400c0360710074070a075104243e4403010480404a908150b6425800c4078116000d245040841021200fa5420911f400c0c44a820b44c4071000c00c00e0010030401052500a0911900b074201e1a032200a26002e07021120741c00c0181c0c4055200d000d0150700400c00030b120201202e02d48081e40103075840c9420300d1911060181d890000603c40081403c1c00e070707044504540852a002d00c20f0040f941450090001014403a20640c0c0b04581010300004c80e504002084c04080b40102640c0700400341141030007010303510b40c0c1c3d90a840c2801c5450715800301c2c0c007150b4049549451040860610640c01088940741c3c50050100d04050345c41 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 709669874 1250 709668624 709668667
    0x40b030a2112020a020c03070e10050603090f06091b0a0f0603020c0c1201150e0f0c07060b0901060f170f220204050405030703170402060301090509030d09080a1403010e0408 76
    0x42e5002058411003c0d0740025440740001d8201d045903031075a59402507952501c400d442072a0b1039404504144010300744030b40210b80019101080300c40e4840c400d042c840c00d01000303642d01261500a241800040d801c003292a02d540b80d0300711070340440549800d5020304800c02d944141400e01d5004209110a024203011003034901802170329a11254205440d094002c00c40480c1200c40300703000881c08142c0104d2210b0051207260800340c00130103511050381d41c4400d81c21a110440c0d00c4d0303407103ea8a4050b40c4582c04200e00a0945032605118483c4207100506100444264100080e2072002044083d020310071300b01c0e80140d05003904051303c01000c04946413813089190f000c0c2d0464148814442000b000200901601e030003179a684003103134210038040d8840311058402030341c46032046c00103000c00c0000e80d1010760070018080c112031074005100d601006654450b01d0640708000e0104018001a42142c283e000501c1c0da0100a0314660401c050407619071405000138100c56404101e500d0050302e008010b000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 709671124 1250 709669874 709669907
    0x1213020a09060602070803090d170d020d140c1201030209060114040803030601030615090603023103050c1903332702090402010819020a030506040b030a21 68
    0xa00c41d1104014000340c0098400d210061040c1240001c4812010054654001e0000d214800f180d8070f40d00c852100700c2c644482505211000c00500042000c1c03440181051b188685001c07a00c074175084103000340303007078003e2090b0a10502004692081d00038455240d0541707034104c2e010751480c3c0b24980125a003800c456402c28440b100060701040f1214004003a41c81598240d800748216a29412407041507035400c49082d0100e00042018014280a40c0150240075a5442e02040308038125106000380100c04412111001d100c2209005105051100701c03040e200075160303840452401440600745074038902c4040d100d90325298510b52414107020010784600b64091440300c480c9040141000140345855603050802c6101c0d910400301403c461100700e0094008006e0307180c50369031303030015920440014510090003512848160152255202070811182d641e0303000111494402c0c14001154010281e080c444e520a804140000e01030400035101c1c2070424502d000c030002050001e41d20000444007041 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 709672374 1250 709671124 709671139
    0x204080a080304020301060b2a030f0f03040b0f0621160f06080703090b070305060a0b1602011d0a120305040e0408190905060a050c0a0c060e0907080c121302 69
    0x60030301c0000380c050750180d40201d00030064166207403101049845504080a01c510300340e01e000c41c4020700504884403a00504050b0381c90000071a03d82603540d0b00c207001800210001106200900c13000343c2c8003540c8000301025454807810101c0000d4103480b074503c4600001403d1001170114140d003407141c020480003080910607410380741e8541c0c0c05210114001c1000241da68400102400c0c4240511961590403103540c0c02692038410003100a050000c0000780c0028483e0800030340103400030020414a00d00c04000c00d00c140c5103100050040071142440c001d480342c013402c009041c0e07071605966004c46160f540d4805007824146001e4460b03025950011448192002c108018086e87c0002846450480d46080d2410907541005803007000c058000d4580210082c843c0b40b6a940c055002080e202c10b1040031511240d10907620741800d40c02c7c581001002844d0404040281d040002c2010f8028015041c03910903032403c4030601c507180c0141c100e61020b10344c0c00804030f102140e1042860740c0d0150007a2909 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 709673624 1250 709672374 709672393
    0x60c0c060c0d0f05070305070605130c0e370b1302070602070611030f0402210f101401061413120b090c010e09040b15100e040b06031e0a020408 63
    0x20380b03455803400700c01c01003444144107051441c071803802c94a01c20752507114242000c466032606401048000e10001040c4410507104010410b012564401000d6030304414003245000550b100d8055258100f10840010744d0100c68414910229055917654034080d0015000380840f00141d011800000c1032810584002004001d00a03580c0003002d5050080b8000d008902c030000001d0702c6440116901c55088007008007041c010700d41410340c0d550000100c03000e83c814244a400d881d0500c0c038807400307402c55a4064191890240c402d03005e03d80800c515070700042e80c9503140290141121090348001807000400203520705141da0500040005400041d043e060300309620b1074418926207040d500741049101e001b00d405281d40c419076140e0180140507200101c55201c503502c011418001034000306c1c0380c03054003e144240d40c5642080c031380c004e021640c0d101142142c0c0c0d401d00007240d404200c2c0718042c003070400800241e543d11505509146900b4584003800756592407800000f8026a00030a540d8081c14408 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 709674874 1250 709673624 709673647
    0xa0213060e0301060e060f01080901020d2405030a03051606020f0c010c180f030b09010f050f040c0914130609080a17061f20101b110705060c0c06 64
    0x401c0e007254010740080044549503030b0b8031041d041c800c0f1107141d445121290701d500c0c2d951003004000e4000c00c08400140c00c01041030944010746800d035000010115a035141000321041c0005007a0040c107050f00545140751181d00d008203244100460000e00594147c00181044150b5048940c4440014402e0b500c0741010300c1c040c0d0103072949a8005000400000317400b01034142201600003202c060480b803c0300303a807075903640c1c40200c40010484440c6540c0c1c4d40144240696600071180300703810b5050003094070f00d410314000c02d084036960040050103203486070400440804031003554008000f1000d0310b540b1141440e090002c1d1410140084c035522000c6017030704146400c002440e01c854100c603000034169590509014501114a00710252002c1c074003c0401c40314001c080340150f1148210014101c061480005c5190440804401d440c045d40c0d07003084080c3c0c40040e043c10380401824541b0f45030701c007103240c2c05c107988042900030f45100342d0000903014101c0078100250428840e029005546030001d2090 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 709676124 1250 709674874 709674887
    0x5040503011a0108131a010602030301051c1133030105010f02010e0303060f240703080109140a051008010e0109020405091609091e050a0c17060f0a021306 68
    0x6124001c0d03080107800b644110b65102090003594044c0c4d250480340d40c8400d415024034250000584800080321840c1d407011000111443c040c0005400650384ca514000500c90907d44800340b40c0010b02a0b085000005800e601981001c86800c030341d0000c000e20b04c00710320000321401c00008900300d8410b1aa0401d06404d02c00914101d42090b01d0342c41c80141920f00076800e940381c031030844055410401c0050380501d070280201d00f880501410030b801c020070229801002c60396401078541c80c3e4101050203410582d0100e142c9016003070161081c0200411a42d002e10116006010251050b0f16080002c015140102c05180188841c10080c02000a440c01c036a000748000303082640900e003844002030b16814000f90400320b0300c1d0b00c0311580800c00d261526480041400c80000c40340ca100283c07510702e00041c0b4031038400030607005601a200c2c45540e49410f180d907202960018004001440066020080100d00c039039100d0900c3d0200c1c03c2c19582c11440e407000b4800c15400440010a81e03101184d455072010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 709677374 1250 709676124 709676129
    0x403030c080601020718050c0405060307230c0307061d0a08070209011d0a111317010f1a04150f0305030408010c0507120c030e06190909020903150403110d0504 70
    0x440700c0c0301c942c5424004a032101c00b0760003031821014100c02680300307000d81940b08507480503001110703e06041e00c5500007070043d4005e449617400909880e400f203400b41c000c44030f0b8094542d2581f414503d41030304070444035124022034401805865540307810440e40c072081c0c10102c5070300e141c01c01070f81c415046500c3d0070442500102020380c028610000003240700490108001c480050302c0e07510801994900070810040c110a0600000d0717110248080b0344c00143c00400440585070640c80000b110b00028805400c580c04440016187c034107203121012042032044e610304662030162400b0410500546088250290720b90000c41ca0502c412400418000c012018009682c40b54000344600300740b4090440d1103000303070603000e008403040d47c10303050506004081a241b8107101e418034814503084070000403030303503080000011302e801180000346000c241e007e8500005088114421428800c1da00c0120b0307510b588117000010600e403d5008102031500541820240c2d500c0c5504a41468007a00c3c4010401e0b0440e2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 709678624 1250 709677374 709677377
    0xe03030c0403060e01050108072928021605010c0602070206040b07021c11010309260a090e040f1212020f12010e070f1202160f030e01090308070b060f03060403030c 72
    0x44140c113040d8018010541200c038204006d082e5241400e01d84d12002c021f4a40d000c80c0e05860200208210300400c014000100c403c4581480b0020074640703e90000c0d00d8140284215045601c04261381e00c040250700c400e4440c20319000020f03045601d0020024880c60401a601c954003040c000760780881e40700200b114910a442c4807425444080412041c8402544e000b050035051403e800480e511991003540780b103008861800f00501b5002101110b00c1815000001182e80040d00c081032503080b89011009002e2802da041140c82c0c544c440d10301240301940020146503402018a4155124401c2210b06645840d030455550180780f00c001c0c119481130003144414002c4500005140d030502850301c0c400c01d05900d88102c90f40000004945000c0301c0038070000d001e03600f400307100c0c2c0e84120f2032540c1d44414440c1c1c050400180c0b241c200509240078540340503040000340401800003d8a81050355006076000c03400a032903494080000f46640141010160503219010801040c154150022070300d08100d03 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 709679874 1250 709678624 709678631
    0x91101110a0b04020f01030204030204050403021c020d02030f0a020c0a180605012a0c0f031a0a05010b07030c02030309060c1e160e09030c010e0f0105090a02100c060e03030c040306 79
    0x19020302a190384a00c070340648050b900400003000350916003090104041d0501d001482c041e125400101205c2083d1410f40c01030380302c41c0103c4501148407060101048090000300325121850034020342e0fa10814840f003141c1000130a180136a01e0003005482590413005100040180e00e940c8880022000f130504480c185082040c0013403107500507140c0400e034120407142d0706902940c2c001000c6440f640c14004480540c4440d8000940d40034404501018600c11800740c2440f110070b000302c6011540140a4035947c03480d1000400c00b0301e6000c030442d00b006a060030402d211041c0c0e40002070540c01030b2a04607410150004455000100206071052031405222200c582ca40400c0303680b523501c0d10400c661100c0c3c0d000c68441403001c004041c1c041c56100e40000c00703c91800342807018880c03d45040303442000701540441054880c421080c013503154080e2844000700002d00460f00054110403602028000b030086203803141080c48160340200440040c03407403c69582e0f04054a541c000359219200c245c034581e15 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 709681124 1250 709679874 709679897
    0xf120d120b06031603020c0c04051618080c0d15051302100201150b0d0609090c0e010e0402010822170d11030118230106031e050405121804091101 64
    0x1002d40c1943c1c0200e400740b103243d6030b0401c0d5000641c029405902c50601c203100e481280102039403180200c91142c0c0300b000c11281c203904844c501a00d441d8032010307440108480d6980900440500103200002070348100d60b10005c40085041c41c040c00e040344500702a4441c141004c00950030094610041e509109503102c02d10707581d020504074200d80a19001da0900081c10800304012015071014101c10a10090001003141d51002e5480441e12440700c02c9440303212240080102c070803411403490041c81146500546403415500003820351100506a03c01c095000026604a601105000504562001242c1022220300c540c8000715001445d12040517420004841a001150402e9034103d8070228450441d400e12404a60054141c1d900144c001e80c1c200b2840030f9494880c1d8005500030702c220b031400503a24480e00074003648030404544501100381000e081c00002034000805a0343d4280702c611880d11070300c4500680d01d880088000443d441420a540c01d021701c1404120008003a900b602ca0001ca07a8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 709682374 1250 709681124 709681129
    0x120106051207030b0307090f060807050a15050a03060e070305090609010908120402190b03010905060108090c09190603051c0e0d0f081603020a03031103060f0f120d120b 74
    0x82880c440d1105000448040390b15180603401c031211300e201c02030681d00c800391034070035500482e168260304140494a54004102c06501488440060501540c400c3d800f1030620304220a4550300d114214100715000801c40310303451003544260701605000c0c0e00901e060901c54001005483c1c103640d090744501607071000c100c924205204044440358030401c01402e014081050980d440070050003030740c2140102c200c3c0c20501403d4500c1c000070700f42e06080103403254100300c0c00c1d80456200134000c0741031084450a1021800b40005d400f140b00e5801c80d00b00c04503690300303020720a40150182c1400107190810202008108012a054011414400301d00c010110f4812045a000140c90061038212a99107442004188070900c0f2004003804fc0c160a072900450f1100000710486602c1c081d401a0070559144040503890301400b1004044140114110b060407400104901c07800707c00144035040c030302e40019403900d03403280d107000c060100300c259401e240410034041c00714102d90000503d00392500081100a1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 709683624 1250 709682374 709682377
    0xb070f020706030c171009020324010f1205040f170a23030106110a0210050309100501031e14010911010801090c1e0e03101d010b090f1312020312010605 67
    0x35092585d840b0309224003c0750100c0c0c29440902010a0425264401316007049503000550145030f29510307044004005e82d59184011594040341c1c2e0401c0042a84482115072220090b0104e8003046000540740c1c680f40703000403485540f0040142143c0b218041c048440d01c40f0800340c800c01080c1e80700c42c80e0180c0d0f1450881490704005d21078100140d018070040c000c40e441600c82095950b4904104d4040305200d40018000d44d22080110002039400420089803590900210341015807901081c82075504664036000314100300714003031201c9040c0901c0300c000e02110000072084003c0041c001c000008460600f2803e5500e545a41404910300c90000980c50000d80708200442119039168000c21541c81c207110004180c2121010410825010510707c556040c0003210310444001400a144010100c3d140041031003c0344c1c80710340b80d01d001100001511342403001540406d0001110b01399070b40c1d44010011200c00c40c80c010380811160110320000640000003400321b000c00c1c0c8007104c03660fa603810003155903 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 709684874 1250 709683624 709683641
    0x510050a0b1f030905160e10090207050705300123040c0905040c030b070f02071205030708160506090f1501033512040c0504050603070b0708070b070f02070603 70
    0xc1c100d540c000180b1482c480e902407a44140719200340c80b0242099801c500159801c0e400a0030781c04403080611007040c070380c000c3c8100100f030040c00641c00c2500e15204d00d0386403403051107032174004c5601c0303d25000b20006c0362481204050045012411045d15000780700c3c000e2442042c20003900e044203604520021030880468030481e0301c00405e5800c58204081c10740a4480544229403904c1e006030044005034140a07030702d108400c1076840880a0038101c0000b8034151442e407000044002c2018001c010030b40c040304407070500c0c3d00375080a955100030351200381c3c0c4088084001c2c12500514061120907003000c6a0300c84c0c402c440c40101d0307440da80d100d048812046400c0c0300081c80a00c1c10130035100008500c0c1185054006250a0802d4209410100c40200d80c01400c01b100c0c2a0941c3d41000100300420103c1e4010b040d00b903400300000e20340031000c42d0b030340c00301401005000d501c013091a001b041415401c0356030b034030b41c000d004d0112410480e03400342103d0b84150503200907000d81000410801d10900ca6141c6 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 709686124 1250 709684874 709684909
    0x7060215060319060c0c0206031602061b0f2508070605070801050d1211060a060819050309150c0109060911030c0f041a100801031205190f0c0510050a0b 67
    0x500383c40d40e86590040c030014102d40280508218282d0260b034841c40030b50700c03c402111000601c20565030700241090300042c5503000c40703c00e01da50a80b41d04151030a84481c2e403889c03540725a0b100b54800824240345402d00c1281e528100702c034558000c1064102c040c1c6040f45c4501c4080c0030949804800341d4900100b4040d0030b0b002120811400c0c04192a5402640c2044580c00c14600e0307126a4101c0c503041102c00c0301c54071481911481e0400201ca000c21844081d0103102e20403030441061035075a99160b214800c171852040d495280d1820904410004949229801e040200480465444c0c141c000e400c0450341551036940d2080c036001a03003004210284001402808440005825020400203110008050700202150b55400740f40d0b031590f140405100116480340c0f00d1641c99407400e42d10245514040c801000014040300300c82c4001c110160065a440f81800c900a64094000300d450386082407015055200d0100004d00c488030b10b0388407500601c0074403800d00000b40030105222855100500848 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 709687374 1250 709686124 709686163
    0x30507150e0f1c05010e21030f1906030b070e0303070c051c020301021c0b0a031220061f090b010507140309090a020a03050a09022808070602150603 65
    0x100340e4582404100e41e1018010501c922018680d10f00d00c03501c2c0e403440307002c90745a951b03a02e00070018203007040440280c241c6c4191040c0c051080c403c07032042900014001143d103c44010116586030468503180031440c941c42d00c1000025603a04049182110582d81000810014091808542070101c215134040b40c005400c0c03581c1600c1c00c024428184000d5180444c2c681d840700d402c8005a03030a0000b0080051005c0c049125003600ea4105812940041d04091050b6803901c2c0420014a00800c401c0c20501641424810440035901084c48a02c041d4820003890103001c04100200352420031018608150502c2c41280a0b1141407502c1180c600740481400710704144494000584e2003615003060100340400d0341d0500b808070010a00f81c0c101034039400b007943e8000c11364a441c03607450f10402e94014106501807060850540100b91544a8001884400b8203000381c00c0c4184034900e04910024082c0d002207504171070390740c1002500e80c4030000c0080924103503c4040744551030001101d03800380c83c2c4e038007c40303 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 709688624 1250 709687374 709687397
    0x4140105032701021c0b03011119031e0603140d09060909020c07120503030a0f0507053c1308010c050f0a110a03050714010c050f0901030b0a0f03050715 67
    0x418420b0b22141d29681e50340800620100600310252915001034000c00800c100b58603a0406095420143e03111844000c1440b420b501585058201141c9501034100000c042200080d07080b017001e1071024540030f40382000c4000081104116905682502641c1503c803d01d00b908021580c0403503602c59035000500c101005d100b00c800c5540100b03003c852010447c0c6009a58074103070980d00c0780c43e81c420f0702c1380d4201000700604034044e4001c104180e0302e106001c01c51403900d4030001c0d085002d01d0382c2c0030b0400150782c5a5031080d508402290400503813004046d20850110a400800715448004940030b4188800310000d4401414003d4411030050b540302c0c2400d006400f030114449400c0308a4a03010041c0313640800c0c1b0509000d11600100c0c034066514680d60b800c2c20300f0300d080c582c44401800d008681c50b0803880d0740759a0340402a82c904280e0b680e04250f403090444012400b40c8004022030340c1c0030981c02400940c030780c0030b23041c8503085070300c02d10a991071159143c0340740c11007580d09480b2502040c00305040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 709689874 1250 709688624 709688671
    0x50610080718090e010509160b0d0c120911120c0306040f0201090906080717030909040303050c04050a093c0203040606380405010c02040506120a0302030414010503 72
    0x2c1c0003208119190900000e541d40082c141910b95403071034030106954a030107101850100b4040c0c2c0345c1000701000c007120701c685003440d1078000c1d2003810424116a980c9084080c50140300e8070001c480500b021600b0b1142040c241090049803600a0003a4826090020301c080d0300e46000c07031500386104004018280704d659a881d03407008405103442c202d04101441030f001c902002e80e4455000600b20301c00050664501707145e266190381d001c4808240e125801400604c0c1c82d91798400c0c20780d07801079061a0110703103511500e0301232020780540d811180d0300642021003ca4404a164480036050202c0ca074021014400341e002c007410050071001401c0c02c00310042068400203660340003150010301c200000100d4980d14128020038502014054080d010299800d2441103106c02020038050046c03a4014601450180041c0414919840003406181c403400041e00b030f69503554003c02e000c50000281d81d209009490000d40303a6000c0c1c00303000c1d00d0f0091100319444da1b510560980c2e2213100c0300c0355100d007007855101c40f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 709691124 1250 709689874 709689887
    0x2d031908040b030a09050f070f0603050f0a09061e02130f051e18010608040204050106020105060f1306030b0f0a0c05091c2105040611010e1c170c09040506100807 71
    0x11513601502c40c2d400380006a000c0100301d2640010a0251140c01e08282e00c2c9442c0344c5140c0e005400301030518050026222640c020740360840c0510304001200f0b51a03117010405023500c2e98990f0701307a4510840509002c55142c0041c54019074103042250382c151103a601a070300c8500340c0100d64120b040280381d00348054011506c40ca8118004003a14800d001c1c0e0140382d50410826003204000843c1d0400340411410103000751405000980000d00031842c00d44003051101101c0c0750b12512404802085041081c072540c400805903402c23030324035601d03031401c80c440b80441441954a0542e0904d01012040c90301c3c41070081d90300d401c2c401030034400c07007c015507619841e441c4e44500a13101200340c0154681582c880341c4542c49812000c1d2140307900c0303030b1500f880a07000c0b065402030b15400c0e9040060603031101c100403030703414000c000110140902c54a1900c2c12220403540b9220318811a10700f1003800031003d84c5402070b0071101412141400659183c0b4140b00c140e0240580d02400b050b03402000c941d0486c0100d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 709692374 1250 709691124 709691131
    0x91a010f050c030a0c0201260705070227100801020403020d0303020f21190509030901030c170411100203070c0302090604090b0c030f061801060e2d031908040b03 71
    0x26003070703081c02d5240b507105080da4841501080403c244410010440d40c2107500b05182c008401003403040d1401440000001400083c011010030600150314000c40d9a00d82146c403920741541a09410354800140710b402000040c0d40211024606003c005603481c0140211401d50b0740c068500380352550159001e80107034000d40503c12141c002881002c907010080d2146001c01180b60303001e5903ea0401002113110451a5081c1c0840c950070a1304000c66141c0001c00c640c0690000c1c6800101c00740400b50854512000441c120125100d04041c001400f030700480403076000c40c0c1103458407030311450f900d0160390300d12400b0801461408031a00400142c5090846c503035018001030008540b4a9965071040d44c0032800300c80e012902d82000c802d10880e94007018200d07501003800d4581c0c41140e002a08071004d07c480502c2880c0801500c0c50044400d078603601045a990304081110398408000b02d480280c041c03041114550191041c005508403c0c07900c580c43c1d0396020380081640d440d060815071040c10950004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 709693624 1250 709692374 709692377
    0x21b0103020d0905100f0605010206011202240706050c04060c15020f0703080a20070b0604060312050a021b01051c091a0f0906271609060906091a010f 66
    0x2e02c900828080d0500428a03034030300c00d0018010b00e1180485420840e9030f203900880406140c44001e102a98000905906451100c4281c0403a56403138800108214480900348030b64605503046030390000c8089000d0201ca52040c0701c14459a41c500c060b180260245118410006a031442841c000c10403109104c002025441005440d02309078440781110b651001030202d00241c52401046881c0b6542e21814000300108c10b20b120240302c060000600d0780c002c410016000f1410304010503c1682d465001d840190741c05500b0440e480c00260000d0216001b00180c80054054000b210012040c011001800740005849aa05041000714130b41595108041039a00c4a80d40d04060408905052100010f040c01c42d02020b5582c03400f007944403042c62026180745000e40c0080305110a04e041e078000c21079241c020b085d030407411341440507002e480c0440c071003420710030515940d2001c51300e02d002d900010191a100081448841c0da00d6540008071a000580300a8900114140700d800b5807154401c842d503041c96 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 709694874 1250 709693624 709693627
    0x1c0315050105130f0f0302010e03060f1b0904061206140c160303060f030c080d0c02090f0a1b0e043213080c010507030f02070b0f0703020c0733021b010302 68
    0x111281400410712942201301700e405007010400856030f2211038000c00c102e040c2d0292413682480c05002c06820005020f5204164404034a5919602580c0641d40c40490041050106556801c00c1d1314616846000c2031740c1260600c50310a88500c13880c015180548034141c900c074078003501d014910006049000003107041503100d580003e000300e621002c90b00514000d0495064044c50100c645e07180c84625075030901801200150200560745180c1d5190340301c245403020002079950708803120010020740030904c0445401c41c060078440c6504c00d103141114642130320200716070240950b40042080041020300d44112528194403c41c0d041060841d4110748c8240c0d000c1d980b00c9281c2d032118459003124001c407046a54030000c0104140d03040c040e40080300000f5804600c1c200540e00d4800030a10f004001005400c1150007095400c0d01c44da0445000003008016145001e484002001c0700600b00104000159001c02d00401c03000c0003210200300407a00f5400614a0340c0c7e08a005080005040010760305040c0e0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 709696124 1250 709694874 709694879
    0x405060f090a020f070c0b03091c0c020f0a0810060e180615011107030302030304060f23100b0c0105010503120f12040f1a061201060f050f211c031505010513 69
    0x307a01b10140034080344444c42c0e0b103a10305001c84919100022403580d2030445442141030640e40c103c0303114a1195019190401c5411304580420100f0110340c2c0450400d21540703142c039084480c00e50001d41603813201c400e00b031501e8075203e80c007004903401428010917640200300032806050006200104104044c145404c0e20320444070220b003000b0b82c6500a8025030000000c1104001c071038428003d800c50901c1c0101715284489001c501d540300c00303c8070160220042d00100d903038030b00c580c40c04000402d8200d0902d0750314034203815501e000c1e160070311403280284144185400615902d0065503001030142000c1410464140810a003082000c0e00540312030269540302c9022500c2c552a59108078400351940c0c500b4100403090040465a2400c03030f4229034501070040c8045c8003d10315240407500101c43e0039403044600c07000100b030500420040b031340340307041c200910070312120100f442c0042100508440e00010307030b00e405c00c2c4c042d03844140e02000c000440c92020b2045d0340c042d9020380080d12501100301a1140c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 709697374 1250 709696124 709696133
    0xd11060c09040207062c0d0f0c0b0403021005090102041d43030903201b031e0f10050421050c1b0a1d01120305160309050405060f090a020f07 62
    0x34040201d03008000c1c410f401d0809006c004101ca19414152031030f0882070000080001011400340c02e81c02030003050400e02241c00c0c18820000d040461114800800107400d188103a107000750302c180320301d0040165034218080042504490b55128aa02c11a00c81c1607003000c40102c14007640c19031091601041d1240c014a40c030602c80c0c0310103081c0340503480000b05131a803410068090315204044007400079103c502d06007150703000700f030000f8640c5030100000315010040700003d0500030711580c04428144c5421900c00d52010003c1d920520b45d44080554ac0c07041d002c40110800d9450072039024240104001001040b00001d50495106c1e01d40c0c0d1402c107080c50070b501491824402005031126130340741d0a0128084510b0408441801002d0f040b030b6070360000c4c40040c19509601e00520411780c00392104185842458041c800721212164005049180c0145900c1d029002c1551070240301c0c095458100081e405003000e1030314540c4c102e0014420025a5503010800002e54040061500f2585043c445000044c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 709698624 1250 709697374 709697411
    0x1020429120a0b040e0a020d060c201b0910060c0c1d04120c030804110a03080d0f05010902040308090f0f060d02031f0f0b030a021b0d11060c0904020706 67
    0xa8400701000b01d08002c43e41d00700029103405c1522258a9008074054600582d0785421054049600c0080031640500d600000d4807000004491144070183d0740418a421590100b2100621040f4955103000c07840482d00340b0803980340031951010420344d568401e0242030300403054001103a103d1a080c458803901d03030841c481c2c1d1200005420000400e40d078180010480340f0f440c40c03400c28009190100076481c1984001f824900f0150020f01002814000d4024681319a652180a5600050200c0d13884407800d10510003404202d05078448a4600700000c10840d0b918001c480890f90401001414096080b080200d06002c0b001851360051500401d08403584912000d401c82c020080702c0107850b8a8200000c84030320b500b910255021101c2d04405019411803042d5040c20b5030004100c1f02d48a55916502c0b000902c01d5540540c50007a1105043d008881300061034038440225540700c40300c580c8048002d40d078501c02a9030f04040e95105002e44002800e0587c05001d01d54024040458110494698513040 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 709699874 1250 709698624 709698631
    0xe0c1e1306030903030f0203191a15030702010c230306190b0915070c1503020d320403090504020c01330b071211030c2d0102042912 58
    0x841d45070207400f418144c140c4201d40400d5150b0314290f195203080403003000444407038207030b590020f030741ca0001180d015210a107503000c088026144881c800340c450320a4885420866054006600307002c40340e14005d109040f500818400007480610b400703000314240c4c0086c1c0004101c0303a007140f407000d42103441ca0001c0c2c000320000d2032001d110968801a810074400403415448101020f5482004500e0024250a0b09042180c010035000320f0480300c4002c04030007901c1210709569040c1e00f403034040c020f107020b40d0703990ba40c100105003c2403031800d0403c42c8543d19000301311406800710781550420456410b25800a21b00c4541100c000149150340c8030400f14401401114045042c00099490341301400d04c0810034007400d5406500c6080251680e075216140c1e492201000400812820b41e51007842c00700300f40c490100c001310070fa5520701e601d201c41a0910180a411b10003c0300040751244040d1018401c54050303907090400300e0003c04458602072005c416851042c00303001401c10041d0f0350f07810f20b03c814900 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 709701124 1250 709699874 709699877
    0xe0601030803010f14060f03093d0507020c100221130506160206070201090302040219081012020d0201020a0503030c03040c0501080c0d0917041d010e0c1e1306 70
    0x441c3d5041c6040c00100400640000d040c01c001242c40c03080310382d2414207480d036001c2c1c0c0004265032036543c4d241d44e0342031801c584a005c00030a040b91400000390450004c0c19924411000c0c41507200058942c0042511403d44004001d038005030441e010504200c01002d410714502d00441d40850440080a05207403400207240e0128440072034000d5008248841c807000410040703030200d04280051502904e90105260000e00c1400002001011a40607a1350140111303001401103489a401d0803040034000a8042b070a0000f0714194006000d42108030420001d4440224018007820056030074080b406050700e000380d055104001d20b000000c0d40810055205503160070b4400d88900340382c0b03807208414100c2e420080c14405c03440200710709a4001000d0b5407409019000c0440c42030381c5410202d140d00c0380021541c002040001c1c002c180c03281d04040110002c000860800541c2e80da80103041d07505801076580d03114401042000303964501a02e01c842450040c08290217203072a14400d444040f144880d0702031030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 709702374 1250 709701124 709701127
    0x6091e0b060906010806180a0902150a030605120a0605190203130c0501080115120f0204060203071e05120d0605030109111002010605010207151202070605160f0c020d060e06010308 79
    0x7601e081180c00140c10080a00f480c1915003000000208000410308102001c055150001101725801d50016076020303402030726211292614800785691944511510004a400c200002a0030b040002d070400300104404041c0c50b4101507a602d00c80a440301510b02160300d401c2480380c0340d9008a83c402103018010042c141c044001c801d2030020306600142e44540d0500001000400540c14000703000ea040420307a00c0d2210707441940e030b122580240300b0381c10001c04051010601145490300040240a41e03030080ca2103400031140400380302a060702c5248020125001903290607590314078030014001914a00101190a81e01d400c046801c4914645007640d491818003804100344c1000103c0d10b013554440d00c005d1025500382000030f9560080c2e4070070001c0c410501103c514541d032150304110038030100740d034040d07585645030704000001e4401076802c403040c0302c1000000e82a80d80107a4803518500c11035111031135180502e80030400003c01d2510165140364885403030100c2ca400900851b0b01861064202c036 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 709703624 1250 709702374 709702381
    0x30b0c0a110312131a01031103010e03070c330f080f100b0d02040e010f1e06080604020912010903020d030501050d0c05040c0509062b09080706091e0b 66
    0x1007104501c2145000140c00420030014046040000d65a20840380e101e11400d001d034620b00a101001990901540c2c1d040b104004401c128070700e003a0044c0c0c0c0074100d0090001c0030035542d600d6200e00c031b0b146004064002283c003c000c600041504507480d0040c1d031869403061005505030300624669001480f0000c4c000303403960044181c22400f429000100c0403000516840c0210201070307520094052103d10410200c0c402810014940443d000780690845604540d652450b82e0302c4e03801d0b1a07000b20801d900385420703446440ea0f00448918215000ca50700e448642d10b484041c0700003944a610420381180c1c4040f940b6290392424000e00c144280700764010b0854440d004000bc0031114180c001510844d0381e80050004240014201c000350340c4c0031500000e6007801260305550a11501040b6a00030201240300201061011465001d0000100650092442100e40402101d1110000502121060100381c001c61001c0c0c0c050034000340b05254902e4110844c0c0300100200c08ca40008440c2444420f041 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 709704874 1250 709703624 709703627
    0x10e150702070b0c031806190207140306041e050a14061015021e0a020301180b090111030703181b03050c040209030606010c1a0f09010513050316020a030b0c0a 70
    0x1480041010703072829070400401019445d22441400040c1c000e412184403440150b03030341e00c42202ca169000600d01a06001c02c84000307500c9403158440c0203100f00c040c0a0700103090a02082081c4a640c1c09032001145220314894542866042c2c01b00350f0f014800c0048e428002202d031101c4c00340200342800100381c40d1030f02c17001c015042d0b852a0410040911800c0060f60801c0d00043d403d40c1c400c0c448020805400507030000989400281c17070b0081e5056090100c0d000c0780091746110184030380d028045640c20707903542c11700c441e00ba1007030090140c030000741c10000160018841c1d4480c002c285141e050461045071591240c40d80d840040083c1406011800700800802038100607805440e07900395025410010001300081d00c0c1c04005184038103000903c2c0082d420406003400c0b0341680c0e180080c141c0300d2410101d44000c98401c040318942040d600e0400443e28480c022000c10212646c49001145840100012550910386400e000c9801200b40d080c00710000725942050b61240405070006900d13200480740 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 709706124 1250 709704874 709704883
    0x406060306090b1005190c0f030c02010206070c030c0b0604021b100609110a051b0106090902011d030a080c010617150c040e0105040b13150503070b0f03011502010e150702 75
    0x640501c03880d04038500494007030704001520412103402e0b4140c00c081c0c6e40890305a882c000b0007000204611100f02c0b40d1b03002c06801c030102100c1d5030b00070b90890340301c0d941e008002c1c1d8044040f9940a000b0403e1000400002800211001d600c64400303000541480d11b0485042134481e0120b040c0c000c5e81c0c2088d2030032403000d5840c0c80f50070001e003d402411f04c582d100d0950007003944d11644046200b00000080c2c401107940c204445039500d130552000070011503031707280d210900a14030b00c54201c1c0011120321080c0d00600c036290483c0c0580200034080c0261203c19940c01d00b8562207003420728000e54a03448000b1b07a445c004407802c03041000c0c00300900303024081107114280e8030500a261481c500e50a200c03d001860104407403078103549007a1400101c02c1101ea00003550304841054409425090044d1040350704111006103041710750617000c440425031103c028848074000c5851040980205100421407000042c501558000d83c0e8000011003c0210f56501d080c403018016010400b001c50042c00101c0c0da0401 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 709707374 1250 709706124 709706141
    0xf060703060b030604050a02070c080a0b01090c1706210a0b1602031b030d0617071703270a0b070c1e0302010305270a2a1a09040606030609 61
    0x103010801641080016441400040c00c032901461b03580c00006c200072101e9040360001900f0100700083c00d9650f407034080c0c3e41c0d401210704442150320400000742001560180003a13001d1070340c58403403013548085903109801c900200895448010540c01d40580c0f18119880c01032558120054840c00045051a80c0b14280240c5144d110b50f101c070034440b02d515804010350317031091513484402c4100c0d1402c090345840c500a0070106c0403101d180041c00140350801d03e40304036998440c0401c2c2c41000d940d03a008809849074030340d4099040d400410298010603c0043c7c1c0010380302250714055030b03040d58400402c880c0030751908420414000002c0c034000703009880d11044003c1c40c0903e003140d000c006582041c2d5900a052100a0515455802061420b4600c82041c45040075900400c00749820800703255030790b006030300b0f01910400d50460012110702c000d000ca00d41c03200307a0b00121119662516080b28139002c0480f503000003100c07041c455205c00f039a60303000703460060029507404030300d01d4100102c1600721a001c4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 709708624 1250 709707374 709707377
    0x203070c06020307020c0102120c120706150b032d01051c050307030c1e02012f010c052d03060f01120908071e0f1b08070e010e0106080906061003110c0f0607 69
    0xd0050b58040c580002d904190980d048240f00d4403048a841d040b8090003c5203400030415601c00d03004903204501c3f201652040c800000c8030408203c008110090072061407500303000c80c141d4040103003c50306001e8085c0b81e001c08548031610050f1140e0b00d450303046400081c02200001e400850322414001c074040e15400112810714a0341203440c256001078120700c00e041074611010b500c2c0080024580a105ca214200304140c0000e01101c404480020000d50007500640104030441542c80e4036560000c003060303d00305120311200d1554a030301c030030801840304000e0741c94100115a101c562240c0940d00810a2052007a5030700303500e4a00b01c0c6004440302d01e80c1c41c15445251200e2030b10b40045220185105200d07a000300343d031281c80643d140c604403801216040704040388140d0000003034048040e804036048810b407113015040c0e6626408115030041080e1038502e010340c42500030507581d103840a0340c40d25481607800e000403101c030001102003a80d081411000b05035003010001408000c030078003425034491260b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 709709874 1250 709708624 709708627
    0x80606030c0414130c020c0a0609080307060e0c21010c080c3c0301090c0e030a030807090f0902130e1603050405070305032214060d0203070c06020307020c010212 71
    0x1801c070007072500a0b885007111401c0010010195074684401e0b11960f07040400003403020703846101c0065034034008452818010b010360603000038a0b030b03c6980001e06503124a40998648111070715064060684903240352070394064800011115a107a40340004203001c4080c16030b4032900004542400c46404041c41c4d0103205034201040100091407046a40c1d2484505003404040205101c07091807160203036100070700182c820b416000d40401040030358100d41800c0010f02049103039410841c0e510f8818901c0503090f60022481c24000b9000d6080d02c1d5101400d850321200d0190380e000e108480d249207600130880d050b40007468186071821042204e003d020284d20a111905003e9405c4104044518860040541d941e02203420088180318a00c003e68202089a032110600c0c15000700c8494850441d0540e80382070540000d940071581c01551131241c0c02130201c1e09103210550a5006944010301d4502089500031a1200044181c4091402180c16a0003894861400c80019180c0040c0e42c4120b83d80600 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 709711124 1250 709709874 709709881
    0x237090203060a0e0a0e0607020a1e0803040b091504030309060f060f15020c031c1706060d0c0c021008070905010e06040501110f19021804030f0503060105070213090308060603 77
    0x9a603003c240489183c0510001280da07002c0c0c004005000202142c003882c05182c0030310203040e9000503d00590307801406005006182c0d5949541e04000290700145890400c0c00024003080d00010300a9000850740b054501d44d0a1106200046003c219411404256582003c005000441c40b400e10080300c41c01080080383e06111041241ca8950311580200c4140c03414081500d031310900640641d5203000d400c48043c081c0031a0310382c151101c0b58011800080803004d4800c11196601000d034040e40340a400c0c2451700d000e080c640d402802400b0300705000e10000d00c2c00d450042c0c03123060401101c001c0e55500c400e0507090000703005010310314035400326042003032841100c481ca5a806046504550090925406894030504018289140901a07850500601c8203a001855901c0c0041606610845140c1e00010140c1a0400f0210003502c1c0030b00040d40281c1c81c1d08449004000071500b0a4050402c01e050a12030b44c0012071082d200b08400f041c2c95120034a000c1007542041199400c030b041100c1144c214076 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 709712230 1106 709711124 709711129
    0x120708030f030117060f240909012004050105091009120501093f1202070c092d0207030903061109010f0302180607023709020306 57
    0x2840c81c1c0104c1d442c9a00072580c2032250074012007903109900c2c0d0200c510400311003807403880c10211407101a401c403039803154600c9209108150020601d140403c80c44004a070311301c08071144440c801d100601107a0b0308441079440d18002600e400304041021102190000340c960321420610008865030028440107400503082280160b103180b205480c03401071415a2440c1101c005400c0c3c04030401e11018a42c51038022001c84402d01d40ba951080c0c80b03543c0042203a0204004072070425103040d0030404280c05028000c19004012024900070300102d5074403014040721200d986005500058072001c16000c1c0c01031748003860300300c00c0c2003215406412045407142d10410703181e4045602c50501038022446402210709011254040c96034000c0040c05101e07040d0000c99080760702804044107180e202504112404402a001e00421140300104060080c4000b0580145040c24010802c005064 = true := by decide +kernel

theorem cover : BRFrame.Cov 709532374 709712230 := by
  have h0 := BRFrame.cov_init 709532374
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709532374 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 709532374 ≤ n) (h2 : n < 709712230) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
