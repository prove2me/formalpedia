-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4491
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:47:37.907774+00:00
-- url     : https://prove2.me/submissions/eacbb39e-f985-4c3f-a0a6-486e69a36a51

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 807553956 ≤ n < 807733812 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 807555206 1250 807553956 807553961
    0xf01020a11010b030d0c1115031e041e020a09090308070924050a0e090915240f0d06150504060f031509050304050913031806020607111f020706 63
    0x921200d180e042c00144807080c4c40c001030404101d422858581000c1c40b55142c20590701308044101640054600100d240c0c0005400085001c1c8030b04a100c0c0390590b1703880c4010f6125080443d4040c00c0b400000d0040c0711030821505216840c20f1000b04075030101d54582010380d04640800d4030035400180c0060410030015088004580030307054016064030050840b04031094507039480d41c2c101c410040c020900d1807429010303074404038040e0b4006081c900c407441d210466075900d1550500c04140c071003046001c40d11000103480388071484400810340b50400c03488401031060b1400c0640d401904a900e194505010403414894801440f10305804c00c2407035468601040309481c0e4940041c400303c100d18801b0800508602003c4040f00b003181030101d841c02944c140f140c11030003a03034461500030a007101084002c0c0748030404100d05902c00e8076100d518040e072016030024071801d8040c49002d0303840310300402c00250280840204520601040f80c0f020842e0a44000142d908500719070320305030300414034208100650 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 807556456 1250 807555206 807555227
    0x2030c060c09130f06080718150b04032406080a0323090103050a09080301030b0a062103030518160e150d12090e070c0b0a0b1e030703050f01020a 64
    0x120740399030034030882e0710000d040c4107688600007030300e5079460044d080101c0d815041840104400001e5903a01a660850700401401001206061520f400211280d5040d1141400c040e102d800d120700382040d05617034071048103e052001d510045641c09030320400e0801c80d0b01524001c0c041c2000644086821803a0180c2402c488084d040400b100185580100d608001d040d220000f0092038041030680390302c00c2407402008842000391400b0400000441844020506230380207801180c82004942da541c80d42210400b40000c80032084541c0380400c10100c0c1c800d0300300c290000904507103140000c000401441c504070f10f541d4030380402c0c502e00710200000035a103aa82644152526a0407046002400010b810080c419000030141e01c03204483c610441d03c1040d0001c00380048a0320300850342402e00c0e020301240c80e801c200b2140040300714002030200d000350051243d10180582100280000012641900151081500c0d010f20600d003002001c10410445044001d0b9803500040e80d65584070b10061114580 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 807557706 1250 807556456 807556471
    0xa030207083019111605010605193b0115030e01051e18030406120f1b0e040908040e0a1503030203090103051902030a0b10020a0c0b090102010207050a0302030c06 71
    0x4a02c100940c00064034074440304401501c0300024400c0940100406901620b4100c0e00082d40075103811080090540c4281e040c8c03002140d41808250b40b030b122103016140c9034042c007000b44c0141042e240307402642601c0c00d4440461300c078014070390030309102404101c104241d00ca803070b42c490094001445140c051140010081c0302d407000380f00902d4982010f01481c4e2401d03403030303416004800001942c0e84109180c0e07800c1c0841341c1c0054135900da5a4400003070000800ca00e03c3c0b240035203801c0e9845000d15291255065881e4020019405c1100b0300109960140c0a02091508562120380d00300028660000900140810312031101c00c6048c2000b07028100d036800201500d0340c4d00d41ca0801c2c801b0036000429910380e41001d19000c1401e540c0c407a8090b2803c2c0032a44500425400070050041c00003107508401204c000950f02c100911000407000c99a41002c102d001d8404030409206120780000130004046d0103c041c0009450602541d9507149481400d4409500581020071403512901c818000c50750040344 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 807558956 1250 807557706 807557797
    0xd0b0a12021c0203190605100906082e09030305040c080f0a1709040903110d020c0105040612090c17010c0e0f040504050f10020d05060d170a03020708 66
    0x90540c042119202600c000040c156841c011682c00c55078208104010301c085a800b030444000740789070250140c0426158002a80b40c0082d011800c88a1407141e401100c50090041104005021780e81c401c0000c4945120413503c2000f42a00c3d200c0603d0164000d194803a0f41d000465180c203050041408081e9040507941d40c000c181c032007900400000d0ba071204660080f802800c0d46010301029250740c031a40301116042400d02603c2e000740350700041301c50140a420310503102800c0e5800000ca031191803070550030b80810002e1009018032481284240c080700301c411b400281c161160307228041185110307400b8524485079802601d51803c0e003801001c2490b40e0038180100603e030740400150304101d0700b080103805180e840000505006040054050481c44001a42d441c1c001d00c001c0c2502a40c040b02041c00801e0070b1034085130083c04d00c1004260704a03041440d0031301a10691110b1207c541c00510000c040540900c002800300344c043c8000c12104040140c0070007403e9002d030400c1c1100c015036280b65066103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 807560206 1250 807558956 807558989
    0x12080a08250e1905220b10050d180308010b0901051b07081216020126150103180b040f151e0c0f0905060d0f0213050a050a030c140a03080d0b0a 63
    0x201d54005c4c0c20841000300b0b0844e42c0c00e09507004600000d2501b0420141d100000341b0188038503540200c01001f1002c080321b000d01c001503080c100d41620082c0c0c11001800280880c004002c0102c40c04044c0a00c41d00500d801d51070700701d52600700081c5100c0321030b05a507190002d83c003c2003200e004220b0121850346851195050585804852110000c40d21010341449042483e0051811018026000040b00d2011085150611011083e09410202c0145002c03034504904050001d210140081240c1d41c0451500d0099980303035102a1500d420120840e155030b00c0a5505d11070802c0c40c016880091105e0001000140a0310a0304042e40c030360984040500841856035200b41d83d112105000340c800c140d450a6840ca81e44081100400ca8036051a114910102c0c1e1040846c00c10b6100404480007101d05041050300c0d07004208109500d071000514040f045c5508221540080f024000d00300401010140d022f81e40c0c0d04c5502196000d40c403040155962480400d196140c980525406040d2100d5604800c5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 807561456 1250 807560206 807560209
    0x13060810060914011106101707030b040215210709090b03030304020103110913021b240405011e0c0306062c0f0a03140712080a08250e1905 61
    0x342c18502521400c415204107444069002e21010801911070208035201d07850040c0441b807500d0030a000303290900d511400300d108610f01c0001c0c000207880d0084000c804540781e030390030401a2520b202c2620360542080c09040c2210a080c22180d4100d08a13110348d50040c0350924004000325820340100c80d01d1460041c04003c10b880020075a90b010f9070a00340016100442100042c050003842c15140d0b2161561310039200f04441d9030043c00c10080c40380340304286038050102492b10788100d01541c001c81520070034058403c910311019150441d00071000001d02608100d00c0703154100fa60340340c148407141c5694500c4442541446041c00170708041c40c0001280c03030034140207035019030b0721901c00c003119800340c4c14030100e41d42c1d09000c000000c60080003c1c191f1a5641380c0041d0344801400d1500b0a0f01031820b001030036803c1d1000c1c1140d07296000413800e141131480e25007a2850040a060408900c0f410764031140c00440490060031542002c0d201d00c2d4084c800c14013040180120080c5c0711a10500c00c400c1004203 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 807562706 1250 807561456 807561467
    0x4030305070312270201021c09091a030d08040804030203010606051207030b0a051908011b180f0e15090c0318120a11030d0908121522111306081006 65
    0x4e5560b0030511003200001030004078509441c00500c0d050642d880030480c000c2c00e810101407421121022418001072404010a0950700c21100c107807501904103d08416109104860701d0f0f0703100f0310031000203003040d40300d801280c210b03000b030f80110011071400903c007540140321114266004015180c1030280c0c2c2001e10100e500c0a625100e0940035091810340740c0d81c0800c03c0792001c00500000c10007000000740c03c481c81c18041104001e90b402240244440b20140c003002c0300c243c010760310700240da8a0024079040f0040c0c08035030000c05142c4080104d6683d041e60b95a40c0c55021300a1141910113a1070b8106224a10102a130b400c07071081c5140c1c058088290256464410b0300c004c001c0509020011240350b11103982144603101e4080d999901c2e00c482c0504216481c001307040a44d00079100685142e940c29090607104034010340c81a80701020030940d2101c411000890b01d50b400d103800003c1050500700403100c4140c0c01c01020350700d03812003092040c40030b0350784642d41ca54041e001d8048171240902d8400c1c003601c07 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 807563956 1250 807562706 807562751
    0x50d03090b0901021005090601090e06160c02120d1d0d1e03140415090501032307051c06140402070b01030f050a0b0103200f030d051c0204030305070312 67
    0x501c4900031645008581c02072140d0913018820b0b000c1403280303140941255440362401d02402d40e2592620b80d540c01c5849001904c3c9115443d0b002440e554101c40c0c130001e541844240030101da0000c21240d81180e011401e02560409642940300c0c8580c0440c1c1111032060b000548034994081c0c00c40b540c5840104403e8039440f48210000d00c00215065100d050803120004c17080300e400e4071b154001600054410b07001846541c104065502c01c546662a90011810b880703060207004217240044401d80305101c250702a0f203400450070b040017031400c28140d1140c0802810b00301c514214175074070300003041090310b02c450071801c40768100c9046142200c2c61342d8001030540180000303402c4800303035008041007060030020004e038980c004d50400403e6a403403819071182c4012041500c0c0d5815281c0500120b41031500034040800c0b4010b004d010715400000048a4503001801035858203da220b039042041d40c0144010070103075000b0f555082d61074000e400c1c0540140c0000240304400e40c03900c10082000c1014186004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 807565206 1250 807563956 807563969
    0x8071202061b0307050f0f211006080402060301031b05100207080105060330040317030a0c0207230d06020703020a020a14030a03030c1e08180312060909070b070f0c050d0309 76
    0x242c80d810540031f0100d850042440743c084816800c201e00400b1030b848075090784600780602507208003d4a400c01100d05d47d009541c02900f040080c401070000030002c00842c00701d90110810341c07181941c2c03000080c0c80030883c0244580903801044080c4031006003030141d01c1d8401c40a0700200400c500043c85d0015030002415015840c0050960b00d591812400302213500940d00b04114440d16090101340855135401500d45070000ca1628000c0744515002007209030460300031303c648150081781023100035031002d0380801c1c1981c080f6481d19410001180352010745843d80c040c0c0d00600006401d44180704005800b0f41005a510040c82800c81e42650005910307542281c1c5440d0106130806d1051059449680e104204c0c00710350303000c860100c0c5040d8803a21007441000c078254114201c21070310300b4190300c03441000b20300400c401c2c100c0000703545818600c042a810480f82d40c1181e550540c1da40400210750841d070400c4424500305003801040c03040440700c0c200a0007086421100a8400395030151210f4020304c10f80 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 807566456 1250 807565206 807565237
    0x1082a040c050d0c05030f01080a051221010306062d0902090402160501050f0109020702010c0b060a03151a04061d0a02130306021e09010f080408071202061b030705 72
    0x9040a4403402c00d503001c4002c5400c05200f4103908000151164000b01e85001c10051048000130340e0000c00a10303000d5254018014080300003c009805e0a42da2140032002c0760101004080000007013245900c40c000d41c05000b0001c1c4c2070703090400410440081e584904080c9070112401c20409072600318080803200d40440050b074580b0001c1c04140a8043c4070000407489511241490038848103400c13480c402e600a4492a5260307072034640c0d44080380258040607001826556003e0300195031001603540010000f001030058503a2a5580b41420200d603500003610341d12550407035050b1808031080e40c0f50050495040c440c0e541007a40d1031102040c9401031074440c00401000c1004410f60b54100da0305805100103160000f0380b03e042c4a4080d43c042c801689444401c030032607a0014007144295208000142c0d548179042a6038034080307c0c10076010780140c4501c182080500c4c0014090220940b09030125000381100f440d1588a02149041c0888000d170744000400030400242d90010850f0201000c6220b503 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 807567706 1250 807566456 807566471
    0xc150b0616050d1416030e060a030c02060109050705071103030c0f0d03140f04060b1306080706081e07210c090e06040903080c21090309190501051b010b0d080301082a04 74
    0x311113a09000c154207401523400140d10003403e80c103400041d481c0d00e41e90210350781c3e82d076034074140002c490084580f60001101800100000391842030f04030280c4100804803814845220801410312262851200d2990301501d04010b14039014001d035502c20250181c14506407a02c48000100600c0c000c00040969030703a0503a00d0002d070b54504000b0020810204100001034465064a5075034080340640740205501200180810060603130002c0384041140e41201140c071030302c400f80c46412141a541c0c83c8030b4a408018510842c003403045000c40d558559901d0825072600001402c084405400b2a01440c00c00008001294103c0f00240d0000200400a6620001c6107802d04a00a0a0005140d140b00c090306111000300e000000c1c080481e000c83d418160040f05507041404107440348660790220301c0c24000c1540d0386490220100102a6160002c07a610071000000703041841c0710300017181d6011b004401440501002c0000c41c001c02d541849544409640d1140c0310300149d560701c0c003c0e10a40c1c54000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 807568956 1250 807567706 807567713
    0xd050109050609060703060515090d0507091503060b060a0206242205010b071a0a0e0102030717070c02030705090c040b0a03020a020d0503070c150b0616050d1416 71
    0x300340c0a5607080815038000b41000548151644000e9540e24002402c0500c0031400d440c0100c0d40128a0306000300c0c0b030f4905088a000d01403407004245066420b8003030400001550107080c0681d0b01c0c2c9008040200c5007a0f4254a0081c0454040703103403aa0003984188150082a81c0000c0c0041d00204000c201c00c081e040070002000e0a0740700700d0030325504405005013043e0401c0980e40c44412642c0940340a04c010780c1c0300d03610714403140503500f0080c00e118405884114446404103e881c1c101103125400300700b5007802c94819003681c0c030a440f0100083e40340a80d00b0003c4020b5290503030000585d00d4540f159955030703000a5640d0709240a214480c0c038181c004500200c400c030084a000f0000240c0702d47d201c1c0260340c6c02a00179049080c0d40c40243c01481544482d0381e00c07450841c1d02c0f80c007181e00d940d00c003491192174015500041052504056a41e82420070455640c0c1015000706545062224012451440c2c158100b86810383c403082440902c42e01c03242a0306103007044e242540c803660980281c6030b0003800e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 807570206 1250 807568956 807568961
    0x3051225052e0c050901080f1f03050c0f0a120b0a020904090b150a031709040b031606031503020a060c062009190503071e0302060a050306120105150d0501 68
    0x4440340c401c00b14065002c2d020300e19400d24006501ca49440c1001034422800c81512284500d2100500054100740014a1080818100d5800a10460000803a02e90341c806e1481440e101d40c2041c1c505034840c0360140b0301413608500216030b40009580c4030080c0d41c500010307a60014a803c400034101c10012002900c500c4070f46e4180c81200350003e20503c59a646410035001412091301c0c0300384206044a803044c280e0800d1030003802245e80c803124149010801104002d01da401a5000c0d55100362200c1d80440d4959040207006449208070061410040c0b50000146c00c444018401c04400b01c500c80007000580c1d2000300780786c2101c10a0800d105441081c0c544280204040b1005a454071103503200c0031580d82c4080040c08030000152441110281900843c44480090344500ca50542c0b119400b40a1460b20070042494808000500c0160585075400180341c0c4d0008a5500c000a1000c001c00800e464003001100341c0c1c1070a10002c12807824031a4a0000d064011100980141030380840e0724204107095 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 807571456 1250 807570206 807570223
    0x50a08180f0a142704020a060212040311060d0903090f080a2018040f12230f0c0f030706140103030504031b230406081f051018060305122505 62
    0x3070042028070070131804c0744400840981d400d034080c907800b400100d070290000484075981c10b198944070342020b18642d40c59440070400354071f2942141d424006402412a07501607580b619203e51039858000342081002020b40040340d1100c41164458085e10021401d0082d000d2176040241c1d5035080350300d550b41c01040740000601c00e440e501d11074400c100000d0202c4c09207100c0c1601d00c64140400000140181120766002c0c94032001d040c1100010000180280d9000070b112620802c81c2d001c1c02c0c04490b07901513042003100010002e00703400004850003000120b01c0380d1240c544070304009110550640e18010402d001da800000c2c44041140400c0f2403220740d0702c85520007000c03025010141c0f40f41c9600041c03203152080403402c0c06a414601e01103041d01c40800d07040c500008511812103400b078000c41101c0504409031810210480c4600d01150341c004c45502c001070360010b108045242c0c1d1552809c180b40150380968201e60150500196800006080a40030300e164010322840c0004200c1c00e002e418004070 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 807572706 1250 807571456 807571489
    0xf0c04051c110603160c0512040e010e06010f0f140d02030a0c1202031308160209091c020303070c03031d0d030b190b25050a08180f0a14 60
    0xc1d9040c1150010035288644200d1290101140d003650301000d120580c041a41c0c848218104040e078a40480d104200c0d111500d401041101c002080ca201038a0031580260489100c950200c001031100310341500000c7d4000c078080c1780805403110341e80d0004000c5000901000308005103805015668a010810303203002110380305c401c40d504e017014043c030320041405a5070503000c140d4000810304107000030703c2601d03c80d5503c5601517118205658a542850f480710220b01c3d0a104501148005601c07000c6460340b050f440440100809442c00101e403144000c0780030008110360080040040c900d51040300c41c02c015038582004941d030810100345426049181e56002102e00c01c503030140c064164150020400d9140c00d8a4081d23060f0411108a600342c02c02d4012a03110070300c00c03c400405000b418581404800c2480301034007014025555590500c03507001e6003a1116040271442c8144004010404441004211410716411481001251400010740705890386101d80fa4285040383e141c08900c80d004481 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 807573956 1250 807572706 807572719
    0x90a02030706032a0e280314160614031801050a021b0c0901050f03030d050c1234020c0a080d030c05040e13020d02040507020a060e150f0c0405 63
    0x1c9803a4010001d203140042d030015007042c20001100d407502c80b036135aa0840c90650317440c3c0c2d2212401c000c1c008107031040c05880001c1e10101c10904c41d40d05904040360080c6100360f543d039051403d001006450b0202051003142841020305040040e107803c03400c03140c203160b4503030105500c9607280490300a8820810005016035420321081001c19469640180100000c0c5040e031228041c1250b00c080d030f1035150721405500407042200510040c41d002e88482040440102124505016480d194050b960246d680a122040210b0550071028590350703510746c450b5920402d09025440c0070740269001d012160113541c180310030140c10304d50a10034041d4008259003e04110417041d561040c0a40e10406107404000081c43c0505522100b0321a01c1154221410702c0503100c420b40700c0030884c0d02113080b210b80c01c07a881070b400c40c0d420740141c071280603480c812079460f0060103080070a03060a40503103620700740b4202d0039081110250140004240c600e07400c076884168041141d0740b003000b24047c41c8243d0b00440c0d80480c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 807575206 1250 807573956 807573959
    0x9081306090b120f0c0412030e010314190c0221030406050108030301150e010509090f0f150d1104150807081501061e092301080115020312090a020307 66
    0x9440684400c44856564004000c0e42d10103070194640a0301d004180d50b4882d8001040ca481c0e03445080581011003450303207500e00740c0c0d5441054a4000041d1084000c02c0300c451601c3c0d060740e018820140316803008442241b82d032034056815200b0402903401244920399035400c28500b0b502c20403402c240e42c0300c40c2c201949118100061026140c00481d01180c01504003000891045808020340e41210005120303954004608030059403480a0068441d041000a20200240b03a0b81d01c5c1c1c1ca1400340030000e540c4005402c1c82c009804514600500040b6000070461604080d40c03510b0048000320364000e034080080280d03000028000e02400c2c00d006550301c9852001048a00008c15607034100c1e1641021159003c6010a0b0045a2002442540c012407041d00d010300c1000c050145500b0b5901151a14070440340e00e82d5504508000b001c1c85039010000301190901c45960400070150150100424484004250070002986e1b032003510442c8282419010115a00000c1000210402c550007400d80300c407103 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 807576456 1250 807575206 807575227
    0xc0c0b0c0c03010b06070203150c120f070e03070302012114070512220605070314010b091002011e02090a031202060708130506011509030f05071d010b16060908 70
    0x464102070018800d518014480c00030780750241c211003241da4017038007506a825007480072034988100180041600002007120349010420490341d2442150350001001a80c01c2584c0d008040401603141c0500a61001c0000d0000d40e800c002c1c41c90140b81c0d001000000d014080d042030300035280c030382c0c10744100807442d40c144900690400080c08044c0098451210720b95030701c2982408496588181c2c034005c0d180e03642500042685600400ea0003500d07030401064442c2c2c0c240324030000000990107a8120314001c50f82c8440703482e14080400c1c0d01c1c400c5200034016001072206c0102200f40903440654031a07400150342c0155101d090b201303801150001e414401c05022000041d440328070480ea11400240c400e00010500c1c0301307001d5007540668000d0006c0c041340c0e0a00c20100c101d1388074902d0160620a508100000003200c030384107485460f100d80054841c01e0b02c0c00101c101280c0403000c140200c3d202e0710300107110403008201560404041c20944011035801c40c200040205050705d00a0b0038064002640703000d0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 807577706 1250 807576456 807576463
    0x5010609060e0606040b0901031109120703030f050c072102491407170115090902060d18020a12050d030c0c0b1b07030f020115060c02010c0c0b0c 64
    0xca03008031841d950b003552594204811071060380500c118102061180c070400354401d50010006610b400040380c641010600000e8001003086050b5a0356842001d080c010181e0004450030000484c2c1086814406c1c0014000d4840748603004840400240305910090300c100403003600b0306160003a0144c3d1420303505c60031900005150382050303001d00c0c143c0044402515030000342c0c0010f01258044140d52441550764541d0310380621070b0640c1c1e907489505008201183d404030000040d40c40d140c00005d0030b090404003050b04e91401d60000c420766240c41d241c6400b41c4c03103100441d80c2c1d40900410010b00c0c50b913103030b1314200500c803401c4010f9000307162000301040e0851481c0050b011203000e0400c4940003a00088102c05448500004c00d000071600809000040c00150301c0c03982040d180b228940c0d240c41580080d82a54011000680004681e00c41080110b40c0a1252070b880964a0302c2140260341002c1000c0c144100c0c0d400b00034100721840640e08184040115846e0107013880c003040351303641d860103050a9907 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 807578956 1250 807577706 807577709
    0x16150c05120f0717030c0301030b06030c0604120b0f1b0a0519110c0405040305090f04020c0102070c1706010305070611010f060b43031701081f360501060906 69
    0x16903491084843d1140c06a0301d091700d200d00030700803910389542e086a546143d241d40240525405101c3d02d100030311903983d03800161010300814a1000c05120072420709a40d03440e005444003500442c040148074220007541100d020050351607200995074046000200c0301445080c3c00050b490703a03040b2603040b00c40d601c101d103030207910030040403225140c000100b00700031540c00f900c004021540c204101c51982c24041080d02c0300ba10300900045c101810056881e0980e400114112030902007004107001a03c4004050346001107400002c1c06d066055a80d00381c0d0340c0e0308a01a000c184880c66040445140d000d4200300c2c00030400a409206107581d0307007100f04135038109625400401d10250054080c03030015510114240c80c1000d441e50709050442c010100c000602c0300103400304540c2c0012151182601450f4900901d40080100300641c0c0072500e0003512621014400f000a04051016042c0307010390702d80c2e250802454680e2865501000b0600c500148801e8005110394201240003940301e0303041c1d01000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 807580206 1250 807578956 807578963
    0x603020d031419200f2d011d01153008070b010f0803130905101a0304120806010210111b070905010f03020604180b0a0806070216150c05120f07 63
    0x82088441e884003a210030817884000e2140e40801d800d201890381c01e0340c49108941c04d400e2036031310213911010070b03509460701845007000910720640d42e0420240c007441580d1003107000700308101c0326030706181ca802c88504c0113580039090210f18404802c94051520310008580d0b52180d81c03140c2c0c5038441d16164046010034841c128028003076080003e0a0600407040b64100600060842c01881c140400d010051030040d25004426040301c10119842c01d11324401c1001c2525034500795140c0c60203241c130b5030b00079541d116007408010400042c040300e070340c000800408402506034007150354203280c0400001800350820108003520140700005294002040c03010603036800c240706000a03a20b43c6114084081c1030b1100940100d0200720801c100504400030311081401000d011030b80500d0f03030002034440390058106c070696400c500b06014003242c04200d0081e6a01200e41c2d440000ae20780b0107041d814145a070302076000d0103010030040041000c2803100000d085051883c041e103891184101409580100318103e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 807581456 1250 807580206 807580247
    0xd050a110406050a05121e150a02041410020f1903020f0f3a0801080105060a051011160e1009050f130f02100815040603020d031419 58
    0x111a420503000340c0d07054610184c11800001d00d03002c18000300c2e60300300454001d00e02424098544c0c4030459550b62041a40c80c030014039a503000c494543e01c140e1070280445170b142c2e10410003040855000803500035121812162038809a0a0320016402d0008040c0c0300642800fa4410920048002100ca03142c1203007c1c0c1d0803140c402e60400600b40c0d0b200b00800a01c402c591000141c8034400c0c0303440c001502103111003001000e400000d01188802c0380e821a070b6183c04500d0110040c00050801d104243d8010021074503c0c0030945400d000c41d00d404801c0100b001000004076821504003000c20100004005c2000c041d426203035500e0745c1c601c48040a551001464203055000a854030706400b43e607000c0c1c802c5480010450300c0d10000010b417082da00400f2202880c100c40c0b1070b00035030744a40d0f500015070300c551690066490705074a07042902020000481c0f02e985044000e00268688580803110282e040c200302072071007100c104880f20f5006201c14044a00c480d00903826005034403a0801800400d0340030b15 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 807582706 1250 807581456 807581483
    0x90807150e0c0301061820070507170610030303053d1d0f04170d05090708030a0822050a1401050a09110f120102040909020a050306070f0509040b0d050a 67
    0x101400e840c49485030541c0c0200d01031401301c050ba161f40c841714008801030008020a130320b14544c18219005603000b0381e01c640004408129030400305242c00d6030114140058019440e03e88402c01031401079003c0501055945c40024010b00e040b149090001c6030200018040390041c10122001ca16910f0b00400404910807000102c0d48450000d02e000492040c0c01c00c80c0b980d030780d45071300d0f20800e100a01c251050024007450000c060551070051040349001c0c0c001181918142d410b0924000701c03540071001d50780c0100301580381664090465500440642d20040a5603482e4256402e402c18521020b8007a00030700042c24200b0112061076811448428024041035540a104000301c52015401605510700420007544501e031416502c0c0e80c1c250010140c08651040034075003400c82e042508440e00301c6035101480001c0d45088c00401c8014007084000780310f54540024000d21244c05980c03020203000c0003094041c4640d90b03030382158850a9018000010340c42c1e0600b452a03071400c103004181c80745181c0740c21 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 807583956 1250 807582706 807582709
    0x308070e04020f07060b09071e02070b03040503031008030a0903080904060545010509190203150f0a1d0c0405041506081e18010608071409010b030106020709090807150e0c 75
    0xd80d42300e03200c980c89400c0171440e003802d1640301d048d01c40903100842c050404003040380b1045401940c0114043c2000310748915202c4d28840c803111007600318100035031041c041511700c0c650022501042c5c0354802a001d403202c410344082405004150043c680c81842002e107000307002070105803282000c40d445034a851131514108080c0e01d40c0c40143d03c0300c014110030300c01407182e8104406110740041c005070892030100c0c0c48a510340100c5c0c1094410361207041113585504d02510346a84591281d1800700ca91040003403800d40491545001d4016038040b0658440000f4020046042510700806000e8400c1c0300b9882070f101c400007566100d00800380412a50004251145038070001e0691401c522061444a82c540c8040e40101440506d44030700c0964840c1d001051002d0b060214500900201d00d407040c04a1260742000000700d4143c02407001144103000410141c0d0340011501d0413600d01200c0016041c50038203092150f8458460080d2440d241884c140314134480035802800d200d02c110040e81c00030b041140 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 807585206 1250 807583956 807583969
    0x3370519180b0304030216080c010311210601020f010c170115021002030c040f090204080606030f0703021507080a0c1707030203091908060103050a050d090b070308070e04020f07060b 80
    0x8031410601c82007004140207140303806005640090107030040303400660001d040895a0529074002e540302e0340080070568000e5825003e02030406030020000c6080101164080e05050f1416030b070060081c0205000c581681d00a0202c9000a00c580000b405044140d0300040c2c58655103401e11020b6100f10307400003564900c041402d00e0030081c26800b418000c081c0c0603480d0083d41010b003000450140800c00050791284d48000f072401070891944c0035032614500095070b8104a0010010390180d04650310061000f00d0102d0307010244c0394112444c03c40c031003e10010113520f015059004007000000034880050682200d10040001d11855050300076018004030008107010300301008000d68418040d4146910380451418999801c0c0100c1d01c0c075042d42e5407110762501c1d400fa0720540c0c0d56003040f000700b01449002c7c094070b80d4542e0181040c0d04001d02c0d0a850034024400d00001500f008900004180010321482d64440d0403c002481035449180c07a000c902d02c0c5504c01c0704111925031414100c402c4074203220 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 807586456 1250 807585206 807585227
    0xd020f0909010204260604111f0206010815130f030311161725050f01051e0606040f06110c0901080d020622021201020d060306090501150803370519 65
    0x220046c140300e44581d510200142d9041d042c266002d49245000f1384d00d2200c0f1050301044504650040120754906101035040500c2031004400045054041001d4405106074410034561b00c1500c0300003015a504080340207107110388c6c201c5a07c404c001036005d5018641c00f03240c50b500d03016102241c20328150300e480c021b17079204040300120100207144004e10030001d203030904503006005d001a14007640c1c0c90201c8600b15481200c011030040e80c4205c40d80311050703003108025840700c429150b2a2515042a01c010120540c81c41034004202d0b1a4140988403030080c08030564806001d000c1c442075584801e0383c00d440782c0240820302c0040c441c01d0005002c2c24028100d9031030313018008000040b00fa0302902402403c0f00005c48541e4190340070404048074075075910a07000114052400000c00c40028642a402d46079221046180c0381e904036000c0c01800070110440b40119110b01303030490002079400b26034400d02c0d0f25004003904c00f10b00403201d800c400e401200800d01c5030040c001320381030307000304180607038400704036 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 807587706 1250 807586456 807586529
    0x30c05131e021c1a0415050306070305010e01090b09010b03180d110114010e01170f120a2006011818080702030c010f080c071a0709092003060d020f0909010204 70
    0x100380700c60024145540503003032128021b100841240e49900200b8034085051b034286000075034400c0104000401800054050140d81030280401d40c1940001800c618060059003064000040070846212803007004002e6040b49034142d40c81c00084200c0a4158203600300224019403c046a00c1d180300c035080d2070a416281d640a6082c401d034200107040401e01c0326608500518070540c2034400d824101086281070841d200c2c54056500c0d4400d03140105108010145000e44c48900da01c91401818049921419038490401d1000c5110409a4860182000101c0d003030800c903006205005110310740d002040c1040c029400c0341d5580c0c4079034004442c1c810700c809980000405001c0817510943d00074006008980c014424040b00c03480503403a41802c40c5080e56208080f5480c44001c011424150143e91841743c2644428600084140ca0302c40d464400280000d209900c07880000c0301315500c41e000c03104040c401800503003040c503103103680c40d00030751250150200072501031481c08580040025031990380c215 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 807588956 1250 807587706 807587741
    0x60607020d061a090a0e0c0a030519080d0905060117070f0b03150a0b03040b010801050108031e0d060f09110a0c020103020d0b2710030c05131e021c 65
    0x1c60380318080240b080c0114820725900c075100c11038443e035440c0031103801001d0f0ba20b40080c0034201c00781024904a481d101c1d450064040d920100042100481d256041d00d680c900b81845420982c60240d40ba80300d203401a00701a4030f05010722051200029078681a24181e01ca40da5814140e0714003da5282c0044c402c04a1280403003405000a040101c059130b004901c1d0360240120f00b00e030310001542c4030b803a82c004c0303c02c0c11008410001072110b4980e40d94010848080208132075410f041100c2e44921a00740c0944c1104003010540e9611021501240c0b0f408050b0002004180e4807208074403036001451040200007400d2200c003129107801c80040320b800c1e211070344802d03007441e840d540154041e4001e01508401166100320302404d5403520341d2111a000312064035080d00680c3c41d4050081500090101c5484420010050000500b00189181600c0c8100d41c0c800c0d000c00448402d0015200f40090500c540c450401c1802c00c00044e03401800c40407020416140200003c2c501d40000c89a07d2641c2c0d4460f401c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 807590206 1250 807588956 807588979
    0x100e030304081608160b10030203060c07020604030605180709230405100c02010507021605030d14040807060f08070f0c0b071b1a0702061b1b0a0303050402030606060702 74
    0x740c8071801040c1a102100d243c9a08245980303c0e41c034183c104121000c0307041c000545010412184a103501d40c000308184149039843c1c00d40d00805c0e61a48002c0010401a0780000c01c1010b40d0798500680b0020365100405104900e00711500c00c0520703244c100c280c000c900c40c0c0000443d5103121800781540380c0403105020301c420380000e8902104c1d184090000e4526004914050003a400326024014048130142c0000c01d09083c0601c0007450200c9510301c204603400c000606009680c0d0120710f410740b0001514040d9030450200a1004161242da80490714a00c0341e800300180b1281c1150803000508007a1304c4000755695044e1082d112043d0060022001a1f10b0032802c10001304245880da400007841e140c0a1002c100c3c1c1d20712280503100f10103058421040f540c1c0703500f54440202039440e80c004143d201424160401d41c01090100c89011880d020702500400c422285945564002d04485c00d000c003110100d03c0a4200a001040b085c0c1d02a80a40120000a080d500b8410100c800099018050b0360003403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 807591456 1250 807590206 807590213
    0x60c05100f1112040c08010e120904060f0e011a0301060813060e070f0e0a0908070b070e1302130b0306010c0602091309051b040b060421020406060f02100e030304 71
    0x4194038500e80480c1e5540780c0141c008a11120040c141940c802907501515041600b4802401441070340655501d0307044c410802c041c442c020a203100d00c414400822512400d5030740000d005083c2e5500700001d00030082e100050142400c00d14103040f691300109002e125206030400154500c400d000706070100328040c0c0131440080b041200c8181990040400094010b1991a09810720203190f20100034240890814030500c01000c4609400032700440c0100030200103561080001c1c0076005000c3d00c20b0400c1c5000904041c0240b6102150440060a160b003050803008100001d40084d40100c807084800c01001c50100580012039000d00c134143c50700c82e41940d26588040c040d52100c5203041e00504850001c0e00700106c40e000301c50020f4420b40c003901000c0f6615814011a19080201d09d104504295404034103840c0d0208071001e840001072162030000c00740e80c5050309164440b5000303422500d03015000402c45e9100540c1103c0310350507825a15082c0840b0080030940f80013400342da0450700704201143c0007 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 807592706 1250 807591456 807591461
    0x60e04091106090102010f0c051c020a140c031603030e010b1e060a17130302060c070c031403070212060106090e04440d1113030605061c05070f060c0510 67
    0x83c05814800499452050320b459415281616219030104001255030703101d000801e100e6001640f40c0703410840c1440c0c0b40c040018550b41280c08000400180081c600104c000705000720742000c002c001c0001904440e51500400030b00560204003600e500e00b05040700c0501d403100320041c4101c5010300868005542d2002c1210729032001024005121114100ca038030300901062462083d54035800349104994107050190400708010064044c4c08420030400b8002200a5844000e8070f400c4030804003503c54541c405803841c4201d0802035030103000400aa48174020014004e416142c4591300c2441450307132540400d07124a010341d00244a40d4402103440d5500e510010700145411321800c0c00c400791402c3c800c1c001c0449500c1d0901c51031104000501c2000541940140d1b10b00d01300300070704e051412031201000790a101c1d85010050410b0745400c080ad02c250b036000100704004400440c4552100e4240c6002a070320070443c4100744156405900c001080790081865801064102018100340031040c00003000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 807593956 1250 807592706 807592717
    0xb0303070c092f0d0e07230604031e021c021e03070302060a03020a1407080d0504031211030109060611060a2408100e011b080a061e060e04091106 64
    0x40b065110001c000b14020f00129183c0c008640502e819666041402c001d4142c0316150320080e20355000040403c003489240703403480341803046241086c1000204c3d20016646102d554009070214405024009444030b90024400205100716801c0d207108402c100c080c915820741003c0a9070041d00503101d42c04510060300e0b0f003154100028266900c017a200d0780040e035241c10009842c40000e90200d5061019a000107421180d42c0000d400b8500b80b1400b90b407100d40d10f00c160300c4141d500c5901d407000704040500500460103000384441d4184106004003a070442960024031070042298104040016800c1c0240a6440717024040e46c090503203980c45502d104050b00c0a060720f010109801c0e50b00980e07411210941c0d8020b00007083c06046051040d02c2e81500ba24803201307602d5082d900d0300c25000715401221900c201c1415085c04c2820841d90b510040c44000c100f80e600c5a001484000d600c228400c41d44024801554459180d02c4000303007806080c08211039622a00804846c44601010100d2412401404 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 807595206 1250 807593956 807593981
    0x30702040203090a1712060f150a1e0c0b010f05061b0f030a0c020301051501200304050a0e010518150d0204090c031101110105100b0703051b0a060b0303070c09 70
    0x45444500da91000107030b17481c50b081d80c0041c09000c074030914034072140081c0c00e8000700f0071600a121584600300003070416030401c242c00207d401c0065141c8507280680c50400307503200c0144020040d03a40d1980e000c1d11800b11074200702c481c014032100119200103008400d00580303902500060405685001c00086090300c0c140c0b40781d05100360151440144c0c000c20082185200590703076140406000d2040c50300703540008d4144480c0c2d410300644802d039664801c5071102245101d001070985034440812143c254400c6410468000c0709901e404200079a01500b5141203441c241e40c1d645815905850903494204140d964040c1521159a0202c00b490001c2808154078001000068101c12541d0383d41301800ca1a03204590100c81ca004099041d0b800140c00989020708a00030f10280c981001c81030f01d52a8140103800300700c1d00104000c02450b200b14161002c4c04c070030408000d228141340013040d554403a24282100c00317a05054840b20281004001d49070b0f0311fa403003031505814504040b001c201401c2001c600c00c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 807596456 1250 807595206 807595213
    0x906080112080a020a050607031d0c2d06040e090606090408070303110d02030a050906072a0302030c120c070504180b0601031e0b03010c03020c070303080c130e2703070204020309 78
    0x302040d4240151406080d0907100010155075032b1400ca03520303900031440304c0300030f400040d503084098850340308000c6820940758541311056000c81468070304404281405411040109000c03d03484410b541c00e5024546200132141c0c036030388107002c200000f1000c440c01884c2c100f05110000010b40203801c420b5105543c5400035013441c4804102008a1300112017003c21079459400f40201320300148101600001c03e440e2000a03440740e01c841c048103203107495050301140003681141c811f06100340180c1d166114424280c65a0502000014065030030203214000f09006a1000258510f4103100d8940d4240c0d0380d01d401c03440c00301e090b00d929582c010003e0046040c10b484996020181780385410810340131140c84e000042c120451400d0600715001c0e5038148051500c1002340030511500000d05070110b0b43e1514040e8051303559080c00c4c0f91103001d050509804001100b00100c0e20000c112540341c80b4410762881c0c1d032008000141204041701c1480c5007890380707400030801c0748050704180e00150351002800085 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 807597706 1250 807596456 807596473
    0x60c060522111302041a070c210308010602031903050a09290f01030804290a080f06040515150912010506011209110405040201030f09080405010906080112080a02 71
    0x5600100a078402c85030341d49009212500e03454594040f81d144004030004506050600703101255503500010900e592030004075500c810010a280b4210103080000480380648000d87c03080844a6144807044000c186440000314040d4800016103030707440e1441c030792000c03c0e004220040e80145030150072182e45a85410b0740101003803000032035411144407040d02c0052000d03441690301d00d40d80040d025030030300aa008010004182d84800342e40950394240600000300449005000c4458012219040e4000d004110045e4194001c42414816400403410814680c1c4400400080340c5085405008903135035200a64060705001c4801d480303407060016050701d0021031400041c254001c20550311402d07034640302040301c6940e10510240070aa41000c0504c45a01243c3c0c4030030182116640d0f2502650b5104000b5095a100390802d20010901071010400301d0360500300021150320500a4901280d5641c41c0050401c1c85010164103e503051450320702034855669074004603502c684010701c01c51192404 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 807598956 1250 807597706 807597751
    0x4020d021810090c090803071419080310050409051b12070b030702071d0c0304081c14311a18070603020f0306012f1f06060c0605 57
    0x100c0c5000d104050400042685010841c0f816596041544400c2210758031040010400c00025116160fa1004050309429000082d00e0b19001c4084004004940c20030340050a100d00036000b036000c2d80c0704003400c1000649510501c819641c100c0700007800c0340d0040359420303070150142d9005145c80c2002400043c50001c240d019518014281c0c100e00741c040400414005019010440342c4000d01c0b010009007148d0341c1c600d07a00b80c41000c0c0107041140b0090300200160070000c0c0c1000316241142d8503050b03616070103030010190000741240180c1d550f40001842c04206815480003009275215084284100e00c1c001410038040100001001140c4c04080d100c24607503d52101e0503040d22a400008514046044441002d40b40c07420300e500103414184100561000546408226584002d081c2000c1041ea0303410192000608000285e070402e11450b01103507581d000d000b00d4001e907039240c40b02080e00c1180c640201803049a443e0311600c0040794042c8440c10001e100c2d90040f6a100c40340000c100061451001c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 807600206 1250 807598956 807598999
    0x1052118030c0c03010c02070803041404090206120a0c0809100b03120412260904091a07020706201915050705091f121a100504150807020604020d02 65
    0x38031590b1504802e80c0149641824400c2100c441c03c0f91009011292819000603141d11942c010304812403407404010448d92a540c202614144d4040c00ba507035101140e003903d9160807010360358a00e486003040d0f5510110752240c02107501484d22200030b800106001d80e82ca100174400080d00c1a0940141c2cbc011104000511002e07100501546102850746e0480e0728140306119000c040e01c44060003003030751580c403000101c0142c0340740001c00e40c1d0001d6000d00c1070910104150000851090903201c0108102d10b49030b000c20314800b1145d807504d980e050441c614950407450943e4a003410f07082d038895081c1403c0c2e05c40740d032030f801c640501803407881180800220342e19040d140300f1240c0b00c000c40d4000401e883c940c14044549480e80580d040c42c0440c010a00e07900808894169104041c03036515500f03020264030203408080d54844c4020f006081c7c111100750041e2058011340303e03142e107400354a811801d025018000b420b03c01d200c80c3d805411180c0c2c496080040c1551502e0007640c0040804910349248140b54 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 807601456 1250 807600206 807600217
    0x60127140103051f090b0103170d0f0f06060e0303090108100e041a2511070807140f0904050a02040908250c05030f070e070525110105211803 62
    0x154044c2554009040b882a580030040702c039024403500d81444c4101051040d0078003810340368801e001103100c2c060844050094003821035200a02c501d0500020741110702782e80301c40101d140c040410b00007560b960905443c400441580e50b40c061b00704028010103584904821588090f11074840b080f2151180b1000c0110041258115503102c054071103080b80311448008a5804015103003e150810004414110001218400d400505c00c2c088055261010117002020203003240104850019554041010017000f454050740e00420b52111510450300f0000c504070b00c55600800108031980844e0709100c004e20790300006841e070150a100c6079218916103017451720603a640258030440250789040c603074442c21301640483d12a070301c146509074031160080350f00c07411500000c90110302552082c1c2c094880f4400d1241d000c404516081c2d5281408504001001e00d150044081d502020000401528548149051003074283d884500030000d20303403c0009598042001c10308054802d150720b2550f031654005 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 807602706 1250 807601456 807601463
    0x14030a1d07181d0d0c0201020c060f090d02030c040903031a010c0503030c13030206030412092103120207141608070e010b0702010c0b0a200f121b19020d02060127140103 74
    0x3645c4000306541c5d04001c110040301c8100c80f1280b5102c04404440d100e032103007264280c0074106074542c8400b55038003806903640c4800301800620228a082c58001c0c02064030081d441004d2038141219039195100b6020040031540c048000e5155440d02d04d07900c80143c00140f80b06003d85e1b21000040b0041e01e03024007442c00b882c032071014136086014418020301502002d4000003005000310410801500c02030b018007080725018100b458940c0e480840600c082e00c121980a810310900b0000040d20001c005a4138580c00c10018504540b1074540090a499000706e10a02c0c407044034441c0140306c4c4800700c1c401440924070505000b5a00d6401365070301d11807007504880c0e00080704c0c2c0d600d69009407032800a18880f01401040e10142c039101e021801d50005000701c480c4d050644405100141604441c64500420014124809516184000403503a42400700e4240c903030060242d00041c001a0b40001001d0b8180c940101c01c050041581101e0403100710381d5000060403035500d550a1006a50781c0b0101d0301d020314003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 807603956 1250 807602706 807602717
    0x708040320031c0f0c0b01060c0204060f06050a020d020102040f0608091e10060e0c03010603021c060308090109080a030909050a020f0d060509090307030e040504020114030a1d07181d0d 81
    0x41098003814003051801e10b0002d220031002c007040050b0004111b2415074880703007080803038810a40045002440d0903081110b0054040c81c02203452604803000d0595a0300c3c0b0ba08540c485034102008070b090340034903caa6000030381c80c030109100060103020340a52010321030f4100d4a200e0320383c540503240d4811211803a0140d80168810b04401002070141c80b02174000840d103217895041c000410101444144070b860f0406501103588503e0848100403660480078116091110a4803070900e22103d500141c1d686021400901000400a501068004400707030541c44111000d40f4101000d005003400410305510943e0802c03010340001080000b42c80403842c2c83c800011010304120034400400c0b8090485820f03648103101010010380d015455846250302a50301250545591005942c88145200b209030340c0d0102208001c0310b20210341c00207100695000709824048152509551101d0943c001c1004401d405601786400d1586074019105070101c010100324000c1202c5c002905006078210030200294 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 807605206 1250 807603956 807604003
    0x14030f06012c0603041a070f0905040b0f0f010504080d021e070503030a05180d140607050307050703051e040308070c0f15120603082b02070804032003 66
    0x50340082c04400368110242d10703100380e85080a120400300d261048682c400c000000c001020041e880ca41d40c8440c0718130000c20030072400e108101602d81c0809002c0d01c800a1012180029189064081da10902601420301441c402daa0702c2407003002113022001c81e041c021700300030004000c001008031042060319980a803081c0d120130304205078651049000d039045e50340191014805035402100701d80903e42c860a1440c0e90368103000001110a44040c0c00b65030001510382801c09204140f0052407003c0000d009a42007542c4458007a0340c980016201480083c400f8007000000900480040c2401c680e00c404d884500c81c8021940e50142e4001e170021140c0c0c80020600104000482c0c140710051311400d4a0a0040c1c0d040c80712150380e542c0380d61000c00c104070713021080700c44840096120f10003440d0800b2049540703041c800f581c4151010142c1000c188400c88030f00b50302e08144030788203440321307039500c0f1030014a45803550b1a1580c043c0311540c401c56401c503482d8030400080d9001c1100c8039501e02100c8507003144c503 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 807606456 1250 807605206 807605209
    0x909140d0302070311010c0e0d06110d0c031b05090f0303040f080c13140a020f120c090f18061210050f010e06010f200a14010b0a0b0c0c0f0114030f06 66
    0x105090300c0980c45c4d40c0c1800658251a50008042207001c08190350704a042c80e103d040c1900a02046408044040000211800d508c0d2054004405280c3d294605100c03442a030404c0c8c205a103105001040015000e215103c1d151800070000540321600804882c1030549850352018400e005505c10140c590080004c0c00b800e0501a546c2d010355051a607042208203290008140c940b0030042101800d01d030300043d80c04a070240542030342c414145200304900c0c68508501c0c0568036074481003680d84520300b0118152440d02d003190100703c02c0c0e0314070409074400351588818007003809000004e130b21075405002c43d0049a10418840c0e10721420040224000a5144c003000c40a20746010b40711504001d0b0000d51010f11503041000002054441440f00e00918680d0f822241840000440100700441c110501369034000305403c00c11120101b00d9100c074895694040b8910301c1c0c462072280b01c000d500499900c0310709240c0010000705031a4181801528220a00001c5040c3e03413040b00d6800000c000f000902415 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 807607706 1250 807606456 807606467
    0x30a060513030e090906040f0606030b130b1014040c02030c19060b0108010b070f03112407030902100305310c0605030c07062003010303090e16090909140d03020703 72
    0x1005000d0310014414100101d04649620001f000540b851440190346000c00810b43d00410056800c94000210390810000301454040442000d90741d00040101298106203221510000c8130f0201e031140124003180070501c07000e89500340640c1e056002c00e00000e40e00ca10b060000100600d1381101150b90303070860740307841c604540390b032340300141084031000041c824002c1c51811510300711340100340c000c800404c82c03508031114807a000000240d40a08000b81e112400005030704943c201a1400000e036a6903840130880858140c600c1c0a544403185c40031a21790140681d12a6420491104881000c07009241d4554005405000500d2080c02c0b0500b408082c004078001100c043d0100d89441460350420f8400701840d0702511f80090201991503002c0143e0848100b05000c034800e850b500e0b07544070f681d00d0802400c1c5071840c1c0310710041d8204840010302c8080da08950100180c11710388680d0b50345030030240000010100c4810444000b26404050301ca820010400800c203d441c5550150340c0c1d05983c03a00410 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 807608956 1250 807607706 807607727
    0xf161419090801060b030c03010302010302030a0e0f010c08090a02030c0607210c11031501270903080405120703020709020309030c0a2a0b030609040203190516061d040b030a06051303 80
    0x12805e00500520600707030149811641125024600541c8039107550070420003d0903030f0200d074240ca124659080c4100b50064000ca820440c898981c04c3d81c2d65120304001b91120303002900250315801c641c1c48403c0c00d01c1d0100c050003c441c0070b0b0404850391054903001e80114a2155526004502428407039030400010024100a0107407d50142440d054140080b411110301030161400241103d440500c0d102d90705a0703468070a0400403020301600d0030900b400381003000142c074266041e02901d282032121001640486aa182d0b2580c02840b401d85481c0c40f250003500068800c2310035000070450f9041a127005c100d01c1400ba4060100c085c1e41c040c00800009a40540d0000c68502122840040002182d000d042d0795009400f0355455900e940c8520000b41881c1440c51160201701503000c41034184080007030b00100d01d03105030300c10741c56480e15003c0517a02d08101c0340501c86010070402c0402c11034101038002d0405c0f1507000e0100d4032011540d9072501c05030759085607505100ca03408500a014590320442c00038 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 807610206 1250 807608956 807608969
    0x70210050a140f09180a110f0a050d06050d05160603150509060604050a121e020303030a0e071211030d0f23070804060e090f16141909080106 62
    0x30301d000c0d08580068601603042180140c100c9011070140d610002010859a031114000e041d07102c143e040ca41032040000007901c50782400c516103507012880406410885616485010406080800c6a0307005c03140c2c0c0d400b003c000310140307484040c00150350300c030111b4180565104101424041250b60f0342001d031180c056200c3c408160a02c031501030b905078405007170710950b40140c0d09c6c6291b55881d0400315005106030342c003241d040200d01d58005000946521302c104414450b0712130b11918081040c88181100e20440007a43c9500704001141815076181e000078001e0502405881a440d81d031024242c1c1d884026600b501e0301c046000015409140a02c070a06140b403040c2840804041c0141300240114203d803003940810402450460340d1258610561b43d0070744c0c1c80300c155a1f0342da0b2514001044145040e403050b01901d09500800d1603a100e0f011801c1c41060500000a18400146c0c000c031810031818210030400041003004090b0507000c0c94500700751f82445d4981c1c0740f072146401845407c65556a2224 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 807611456 1250 807610206 807610217
    0x20d1e05070f0507050102040b031306060902070c050d060b03030f0c0c120d050c0f0109062f0a140f0c0601180504120309020f0301061418040c300503070210 69
    0x25103030040702600190500740ba00507104c031043d151480c02481a50040704490601008100007904c005560545171446408113010450b42c40030054142e000300d5800909801e5039400034880b6040c24501d40003031a000d002c01151503d92400840d040d5403100d200f51078184000105a40040b1040041740049801614146146a0ba4505040d1a094100e1a0204122001800c070f090b8003420080c5003450720041c03000f0000a4075070314000c40140140c4060010304a80845d00f84054140840001d191030300040040c2d1400034101c1048940890300e9420b11103400c002e00c8110002d18015000d0f203d40d15908000f0301c001e50424190580142c0d402550410380d82c184410000011580b00110b0640c118a0402260304030107840080c82200108200940540c60034000144260f280f0346c0c081c03407005080c2c459a0058034088a0b00706c40c42403c590183c0342951441e400c0040201450200048480d03900010661095400618100203111041517076294408150a4190714100100c20a08000342c140b4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 807612706 1250 807611456 807611461
    0xd0623090f06090601020a0c080102031005061e0a05070606090509060c0703090e06120f060a0507020a020d020f0d0b2d06010f0c05071d090c010f021b040b04020d1e05 73
    0x101d071000000341090f00400700b003004510f5990003001281030715540b0051582c0308c2ea0b101d0440500030342080b107207104406008440001d83d400c1c00804c4038069070344c0000d21b03d11b40e01e10100782c1c13055038000c09240b810007030f0400400f000700300c0f01c1c400c5d0030117030001010101c0c0c54100b100409241000183c050500040100301c810002030b009040031084070100b404869085c0e88100c0007800301903d028200540c4e0140481d064030500006c01ca640c42807408440070072182c2c480d02401ca80c0c49155200007034008a0703006c019000b51500100842880070010480b11881200340e5070001004825580c1050b000a01c1d2848841600300300d101c00b0392881c01403413500a40c82c05100080c540704109180009000c00d0121800034040180100b1000d40107424124441d414040e0f46a0a1404100c800f40c2c20b0b80a0a055003c0641c400c80500101c2e1441f60300600b07041c02c001e0040340800948800580d8410350796510070906888074005070482032941c2400245c0710340078903071843e0f105c41c81c80f5446101c80c0c40c100c01c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 807613956 1250 807612706 807612721
    0x6013f200d0b0105090405090d08160f050c010b06190e060f04210204060f05010e0901060e010f0c02040f1d01090312020d140103080403120e060306060c030d062309 72
    0x240c6007001040903011455962110060300c07140329400d51160090305003c10000c40040008a03104118035598804040d90354007036249058400300940e41001810aa2030039040c10f10500240a116205200015a0410240003e0083c1c0d00c541e4031142614409412005500d82048511003640c030182d58051134046a503480402d588124081d508001440300701016842c04104010052298080d01c1001720a869542c3c072040e82c119813041c02c0c0000c3c000e508180b1603003800300b61340381200c0013a1202070102280c03000544060000d455560200141d410a0b400965141d00507448418040c5400017003950040c2000880003200301015405a8103104041000950002d003100b80403404000040c1c5500982e09850080d01455440c0784400c0403180001c02406000001003040300c3c440c0780d501100101d07046080d11301041d8190400c5c1c1c80301c4240006801401e001d402040402c10103c2940d1501e17540a980500301c4400b82c01c049408410001003098a222132100c80b80001340490f000019882c1405 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 807615206 1250 807613956 807614021
    0x12030f090d03020f0d0f0207150213080a0203060109090311060a0f0c0302090306150607060905061503071a070317131403131e03020d11030715020606013f 68
    0xf40458051755986614280c540915410740d020198005008040c01e00188022006500426040c807100010750f85d002403c1040003607075140c455400b03406000d09130b1030480071000401c0c92100a40c140013114001c903008440034000d2611409088000084208102c40c4c04021210055a4481818410801781403240d900240150303200d00b440b03e81b181810280c0300841c00c0c1d8000c4280c0281210f04200c0a641001b4003c43c0c650f00c218141d00c40c0e418080507a10130580c0d03a61143c480d0001c01210300112421020b040c070010310300c05000342801c80e80740c0110381815860305e0080300c0141020b42010014410441c44000411408030a0f800a40c01c044009156a2180c4e4552044081650790310034965528100009080300545e0020b01802603011503050006100441c0742226102c0c0c003800401240c054585000020030300802c0e030041c5003d42c1c03520b00565525444501d49444540c0c0521056034491100080c4100c203c0802ca410415081820a00d4181c0d140ba102981940e10480c408000c03031840c08 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 807616456 1250 807615206 807615217
    0x50d032001020d02040b0705190f121809050f0a0501080d120f0207051e0303010605040b0304030c02220e011a0d17070804140108010302090604020c12030f090d03020f 73
    0x298401002203840c20389440c02803140341e01802e4842c0c004200000c8100e0707000c0140034058040c4003074800c40003910184014240b0203200c0207202c00c901c030101501041c1c0d10301d81e5030b11000d004c1c00c0001060142c26541c001100309940074a1001e904c0b9020000f201462983e000e80004841005000c1d075410440400d80381c1e9440c01a4204022822400901754981500000c0b203a01d0300502c01c41d902c900301d0a00503150559000d100c1241c2d029044005442c2c800001200d048611540c0c0d11800e090905004509543c0701030030075400c1090380959203015070b13a8003002c2c080d90110503d610b50b012131144032540640c0c12914076100d1503458070301604401080c414081202c0002168004038400e580d11f081200e40d6004204181e00c0e400100302e900c2007080000051064a048508241c080002030300119100102404001d400c024480c0104a29041136005413003440341403019280701d03040b240c0b460502c940085481700304540701078003441080f0f001400507002c6401645015032414900250304d654034800d8 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 807617706 1250 807616456 807616487
    0x30f030911010c02061204031106010b0c03090409020f0916030b03061509071206080a020a150f050f0f0c0a1e0506072610081c0c060209180901050103060501050d03 72
    0x5003c44000315502d00c0212420700c4800071011100d8101424001c15000a44032070034100d1045d40008500c04081c14103a9100c0242030700214603100c0c1da142840082d000302c1700220307000301d070b60011451141e2b20b01c40c4803881200c01c0d40d00e203e0b0b4644d80401c020f00743e61180031010300030741018060044d80c000b01491001200c4043e118142c250301d0307450085a102e00401e00b85c24940e441c220300403031000c00129a4400b154000c641c015030701c60b2a01d61044412000754082c40209100c0702c01060000d0080c40540440003642c0301a504200c000d484032241c036440030038021502d0b0050702d0020b0410603480344501b01b0025004400300c1003440c641e02c0c00e0b51044081d11140610081d081e0101078a1000898440e081e1802c6151007050b00302518072070002c214500880c030580c01a5507202034015620002100500c5560f501e0448074501d40d11a04000e5201101058100c00421410010034601d000003500507001c8c3d1000007032661544c200702e01200d0303041e040140308840e800c20f0640840e9014800f89085000d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 807618956 1250 807617706 807617717
    0x9050c090904030f0e012a0212070305010504020a0b0406050d0b4c090909060609050708010f0603050c071b030c0b040603060f0b1e1312030f03091101 66
    0x59101a4411500410100d1035004a03024100000c1560003001030450598a4035406445013007032005403808040c0920b01e401141081000903004000034222100765400179003259082500458013601b072a0440d0800d8456a4603901071208500b03125403550010701c0c0032407030942020304285c0010994801c0810040e0025101e050600c080d81d12526003010f840300c2c0a100d0004590855035000702e90718a2900d55001041078030301301c00c411015482250980480d5a2401200350a0429840c000c00c0100c0090f40c8040d070760240410142694480d050054045441d45a807561510f1142100e020045c0c200e9010141040f090060520700501507501055010b01d80301c1c0381c000b210300726581000039548003400000d110b001c0010004100b41c01030090740c01940d0144441515564407046400007446608110401000360300c1e00c0401c500c030300781c1e20901440d048501d07021516840c003800640b82c0d001300c1030340b0314100c0c6210205604111030382102038490905004200c040e4540030b50300100c00d26210305021 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 807620206 1250 807618956 807618961
    0x60c09010f14091c140a261b061816050d1104050103030305150a050a03123006090504020d150e030c030901180b07080a030e030c16090e070905 63
    0x2111205994800303c015280e0410801c104044800140403403905032130703103600980210f805910201d4141c69060304a0404034004420081c8401c2160380340701142c0c103901d810320410600480000d81c0300d08c0c0580d90801408181441e1075010a401c010902d0024147d110003e214060b0081114100881d2000c035000c6180264904002d1070003d40000f03400c3d8030900d060b00100406405500013406101d100c04c0c0e118400c0c41c03040500602e914140100c0da801031085a0410000e0705038030341c0c0c4201d44080e152102e04c2500d010601c200790801c000d04ca9615610030850f071103070038031140309140050200300028440c7e41090f80110340d1030000c0380d80180c010a82041e002c039150180b504940b81c1d004032138007182d076074001100c0140d03202e40000e40c11a0000303030301caa0f0b1800c08040071800c401c241c4500003070507032a284e45617954801e283e0198910f00c01381034846d03a501d50004800e20107056842d03988006044050034013100a5a407040a80010704054600b0940c202e03120400a0190192002200c0004064 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 807621456 1250 807620206 807620237
    0x70f03050a060806040c0e0c1326070608010302011d010f0f031b0c1e3f3f0203130c0308040603050609071e0c050d020f060c09010f 58
    0xc0c0059008180e06121365800e000030425415441d808541000042034016228142410401d200b445040000d00140240a101c2403203501c101400307542226800c84840480700d403819080101d141d1011002c6151400108150350304240c820f10f05406129856914081c100c0002c0c0907100d2844907042000204150641418040c1c0d00c589480341040c661940101c095940c0140f1000f5240b80c1192178201910428440300c0c500c0115104803035124a6140c600c02189001c404101c004420244c00052040305c500300c05011060380d248200c900369142c0c0742c110400307601607404085a2105c4900020307164541142300100b0340007602c01d00011407003d81d503620303000c010010710f80050074060414a1856800000c00c040b5200600844100b0b44043c082130f07803001c00700281d2103411640030001c50450214141c402617603d110210038802420a8040c241e03268840f90b1808060410340030250b400410940c0142504100c0f85034012a0070380441d02e00000e1000080030004202c0814052043c2103c081410 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 807622706 1250 807621456 807621461
    0x207031b0f05030c0706031113050d0501060b0304110f010f0e0d0309091a01080c0304030509210f06071404241b050a0b0106050921010e0304090b031203070f03050a 72
    0x41d950007000322915007003501c0c14252140d100e4803031900030a103800c0380031b0354242d4443c042d690b0348c0071a00c200107001441d003406d000107243d07840d5045a0035580c688022400c0740f08440694040c90040d49540b00d0303420300c54248940704488401c66410f10520810407000c00398052a012441681694400c40c4000603241c203444205094100140d102d081800400c0741d01c641403041c81c850f8200340e840d0340072601c0c0c40d105403441d41300c103990140004000b0465029a402c154040c03092103d0143d05081040240310302d003605190114092815076005a0b00340001036900c90181c400d40000c000001d49000e1a04070680b1022401240c0d80304640c5080f54101c042c1030154105c6046260210324424140005142044d1038001c0444201c0d04070045000103c0d0f01881801a544001c03000740490000388002d5500b0410080c440e00039012940d2a035910001c0b461050018000503c0360318408251100720008141c2020700d004d840c00d500520500800500503400402a01101c0003400c000500c0c3e00c40c04102d001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 807623956 1250 807622706 807622733
    0x2090a0509011212110c0607020a0e043c020f01140a08090709050106023f030108060105060f16050a170a09060e0109180b0a0b1209010207031b 63
    0xc0c8914a40d00015001c500e2080c032407100f9105044980c605844004103941808802c41102a0f42d171001d510448607060407001044801d00007011861304c1a5584042e07084904115002c03200107101810600090042e14000180e803a03017000500003d9041d1614101c1107603441c50b01a10807424040f0300d000e2039008010801103c040c40418641d190b405003405000c403402510718900910551400107416513143c41090b050b9401c03540900b01c44803001c2254405882c030340c20242000c0000600c0c040300c1040c60528500700e0f030700000305a500c075072400c00390a007030280591003640101010440d100a00158104079512450b40503001c1c0020105803c203d4a0250f0002e0300400c88144210810440c4e0001001390600310495500d12045a0726100201e8640840452940c0869802031062040592801e11072080000303441001458040c4000020507000c965808012401c83c00225042e9140b0040c42540d48202500e00175440c1c4410307030b039008028400e1b11450021440f15089024200f0912125546 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 807625206 1250 807623956 807623959
    0x9020406060f0801060315060507170307090603052d18060c0c0105071e11160f03020907050301080c10020c030f0106080f01091220070603060603050f040507030602090a05 75
    0x405103440703050107000c0100d042040c5000c10700100000500c140319000b03010141140009440c180c51421030161107079042540100c0c0c40745225001550940c802c040910b00c2102207966400c9403910b04030b0040d003100c00c0646113031400d043c05000c052a45840e00c0201c0385d0403030700c56075a405913641d0803030f00000c001010950b80054040c0c602131104580783c0d200030f0441117003a10f0080140b9251040c00b942c1400890020003146610040f03480138180c0205460784048100138103443d16040c0144501c80b000382c8540062032000c0354040c003841907041011180b54822580e040c0b4500e554182000c1d140d803440da00c50b0082c0f042842c0008022801d20034003d010f4055000740c02c4450600c0c0e00b8030514081d143c60301030b0780c020f03206440d100c03402880c0500404100d15081040081c002529032000c40710348405810b0380b400c1c00c1c19943c044600c031204000040040c02d455270b000401703505000000342038407006082c1c54400c800c0941448041180444c29030f08481e4800030040e030b03c200030310204e04501c00e29032185 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 807626456 1250 807625206 807625211
    0x9020301060e04110711040b010c08120907081f0f0617070302040b2713021e0f061c1508100905060f071d04111614070506070201030f090204 62
    0x2225a08540c2002c0c8181045909115002000c0c4508034140100100509005101039150300340f401d107544081c8481d4010300d0081c1999149441e1068280d020b1b102c282406401c400422000140500880014040c0c02001c0d042d00407044600300c44032000341c11848001c40e42c990040c60f21011503400180104204140c0d6158429404030712901c466517403105a001e54100340100099142020408041400d0074002d144000da446908101c000341c0242880580c0ca8540c403071401680c0c40035000c0c0c5007643c802140c0180403104009101003103030760301901400b0b200300303014032079443d20441c20300155140d51a400140001075035400b40350100c0c00d58001c0789140580340c2040c90440fa150040c1c6d040900440485400351038407201c0b061481000c42d0b2880014464003807070b840030007940d80da4000501c401007011402051921701d0603010750025507004040600500842d0170884e00b802d000a0a0503100c01500c0c2084c617140120b5038500c03403094000e0405564541d082c0920415a00031852650060000c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 807627706 1250 807626456 807626459
    0x307180b071406240d1407150c120810030c0f051507021f1815020609010501030c060e120d0507021305040c06030b13240806101203020709020301 64
    0x1100c050380140c20540e02c44501403620365089100151503401040b0044052052113880f0708048559125445915800b10800c81240089820010108420203007003010b030101c146030400140901c210641d40105100704905120b0116101d50f0451740d80038123900b0403180541e211361903130500d842c042d000141020701d55030000c5240c0195031000f4050360025200100d101c203420314a181da40c025010000d500c98070075401109010561040d02051142c00c1c1081c061886a044004850140235040b6000303614001024182c05541003215941040d0b24000030009941141c44000d0441958010042403054015004505458242020003081091420b60300401040c4400410030ba03c8150140e22844140a0b440203140291042501903680f0445c074004403460010180e011700700d0b0405040d802998500010480c0100e4000d00e0264a0400c0750216007024240000b0f100d64070a070450382166000100704805090184a20400d9841c0c0c030703000d441ca00d00c652404900d4146650400b045080c000b100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 807628956 1250 807627706 807627719
    0x1908010503062d0a0615110a02121f0b040b040b010c1101051309050f07050a09180f0f0902190503150c0f0c01060302030d112e060806040b100b04030602030718 70
    0x390050301d59003400c100452403840b10854441c1c25024400a0076080100c682300180340905104002c07400c110180e400b0420418840c56046170b045103100403558550383c3c40d4880d85007a1007103103101e031000c40d81000303e001d00c44002422507802c0b100c001c4c40030300e01c25181e035660ba006506484d41a00d21071711454a0300e1b1100840005000c2c2901c03000c0408005601080301c0d1401541607401d1881a03684802041d4500424040d40c158803000c9105610ba846603800c0c65607065000d580210b41d140f100c00301e9281c1e218814002d0040043c2010003042030040c4080c02507540202e04441541e081c0c2011444d151512140b00e085441582000c88020f400000d1881c1e001006401c58000c4a0003182520140405008280c030003020b442d500d1011a004041101d812222214560785242442c0d8800c1c070540084c807140e102154840d80100849034081402c02c010130042e151840c0e0f0040c081d0b21702038a8913240c0244100326000d1404010011030f004070009203240d210f0b00740e00782c400320107850390180716580c3c08 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 807630206 1250 807628956 807628961
    0xb06041e150207030b041104090c03080306090a1509050a0b030d0f020f060c0d020a030f0c09031401060602060601050309030c0106030f060c09050906040902040915021908010503062d0a 81
    0x7241d101c404240001079035040b400802c40c0e80c00c9130703082180780b80a6074030f55540c1d4a14101000c1c9440c0d03c15520b48109020403c040f0142000c1c600c1f07080c51695a050410802046400040082c041e0030704000820110b19074507803101c070480e000500c004c90701c0d45428400c0b070301600980c100a034051140045015050381d000365a4807404400d41c00751650307030b036140103d10b449410844003d00e0f10b5a00b0402001c002030390760300601d411240d5241c002a06030071500104280e901e002e00040005040c540c2c244240110240740b0240c0c05104030080156500c0c00b40041d4840c1401004181408808000601141402d004842d40d05400b40d0081110340d45a18005582a08282d4103a400381c4c81c2086c04e903081d60250b001c0006a6a0003000c0070310640c0c5850421015044095040307800c0b0362503000c0d1200082c404103170004420b10840000d82c840d501d02d02010100742c40308a201080001c0900100595140400c48035001701e00d0038a003c6010010182081000c40720041014503243c00341d0030400445200e9 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 807631456 1250 807630206 807630209
    0xd150e031c0c08010501350a0623061b0109060203071d0a3804140a151803050d0e12010e0709020a020106120503040f090c05030a0b06041e 61
    0x16412a01c070800c054988048490031000c030b1000c90f1121005001c00d40c012030b0036102e100744000040311403101c103401d900461458a00520081d460790814050105850302a84014210702c250f80000007036803804100c040044e80003014018900012040400e40e0700c2c91640c07950885000081c401540c0301c0c03070020000e42c02100c0f10b03000501c103482c400b022a0b050344603c0059032001407403015407508085180d218490912a03054007450b441c3e140c0c40d451290b402b02551f80e0900060341c00c3d03c4030b207000c21079410049206200da1207400c1e101d0b41440144040c50b440c4100099034500b907403900d642d01501c20026a5150002341083c86a109030000c1c40b50300c880b9412411000b034030315418401364205500d090f11031500c1c8900050708036003814007002000781e0145c03000c20024400030a5255558a07031020500041d0310030380d41a0800a0103014101d0340b06420001031000a500700300032001a800200180405402914a02d840e103a018999503140c80580700540080b61400c0c03130f4200851010702001000c0e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 807632706 1250 807631456 807631477
    0x2b0c1509050a0b030a050603010b0409061b0306031a091009051006050402340c030506090f030f0f0903160b070c08060c070b0403091508071d010e0d150e03 68
    0x80c0215250501000e03040c03c8690407003603a82141c03180c00d440d0340074080080c0940e80565030f0b0240c82000303641e40d0007000e0b0701c140100b0001031552014407000d04000c0003c0c2c0107106240c1021810000201c03100e0786505e402654511020700d80e21600a280d0422080b0340c0d24004090602c0c0f07004c014004082448009a900402c04205081d9500288010303806810104100f6419128035044c201e5a04082d083c0c01c040e6842c03405c0706031000b580d60302046c050b00c1d0300300b964194859402c11210076400c10142c01c02500110080d8100303c2c20301841e1035184100100d5040b40c0d8000b0400c98016141002998400701038100c0401d06542c40f00f401c0003054001701c0040d01c00480c1c82000041090000c1a0240a064000d076071901c0c01050f510f800701c19074400350046040015030000000c3c05c0701181d1950109440e0360381c80c07402908028500410f04000c04a50120080c1d100040d81c03c160f80246204600c2007003607a1404078000c05042c40500d001c1c1899103504624240079040050080100060184041 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 807633956 1250 807632706 807632717
    0x40b0d0519090c05010f0c020a0605030912030f010501050706090b0c0c0d09080c0d0c0f090c0f030e100c0216080d1103040e0f180f0706110a022b0c15 66
    0xc44106031080e00c00d40d840c0a0000d5800b41020311007544564504569201e032030a01c0702641482350f0109440300484d9101000140000c420700440d04000d001941412842001c081d04505000d9032045034100c2c113200700b83c140800000e80c2410043c00d80c2004100503003204d072010141c50017550250a6500072560040341d405507076a80344010f4060003d810a0303458032030003044100c542c24148601481014000e9039403d0b04070b00d002401c0d03c07100c8110b4018141400c0042800307001584064296035043c4030050905003000c4034203046900004641c02c40700308010740072034140444a0140d041103807027443c0c8075840061400202d03180e00b0006041c0c004880c1550307603684081001650359140c1c000c9000d4003441d0606400411204036081a90701c0d08000706e062a403141c0c10500c401289440c9141030b410307209410980042181c3c81c2c0001c1401c00341c401d950090a0007032100d0b03000580310000200c144540703841000882c600c0031040305101594a90010300b60003c19210240c040b10a145400e0b480d00041 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 807635206 1250 807633956 807633991
    0xe0d0f110307150203060301110708090109051c020d0c09060b13060503090613111c051501060f27080a0506010b0a0e090a0f020f1c09050c01080c040b0d05 68
    0xd00004888609030060041d00e100d103402c90115000e94009003840c0e80c0b6640b035403901e0002d0043c60009103a058032031038802e55201520800507090700d800742d001510461807640c150390aa0149945c02804a81c11207541039030b408a4a400f8810b4246038009003074a602c3d0034808685010848010041240500c0d100c6140ca59208401c9030588005c68101c0a20f402034000714022a14204d15468600d1240c006c1c0d1580709440c0c1c001c00c1065110200c282e03111041a0582c0d8140b04050006d1010b0801c522003404480d81400d2001c1e0070021480502d000f00b0070051117a51140302c40c0115408001c1d48030440c14182c0c2c0e40c030301006644044040c030aa07014041c4500008110580b0320484104000c00e4840210580c8044100480e01c280103182180041c0c0b51045030000725503a10041c108032202c0780c40720b91212001c46101070800d80d54500301d42c0e03191400d0750a0000c0b490015510a0406c42440c06500316940c0680c180100d015650120030b0304500441e201d54500c500342c0040f03220f1410712a0300f01115 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 807636456 1250 807635206 807635237
    0x60e0c0a0e2e02030c03030703091a04051b04090204182306060907021501090204090608061b1e03190b0603061302090f1801060305130c0b0d0e0d0f 65
    0x4101d0450002d00d0808030b5800581802e004035031201203420720380180c83c2051031100c00c80b0b080d0342c0202c030050000380d03072402c001d801c000415038142c54205402c00040c005140ca9500d440d50360900514182c0d042840c50741d03084443c0d59a400403100c1750340c0a8018810010b9070f0300c800c081d20908203000c85041100595001001d162070343c03a24a0412048005e082036100c0009001841d100503140c04218081d060503e030080b11454103e500900c091017005a540789041d9001c012181c481e04070704d07001c0d0014000e01c808000007140d4800c044003540000d940d45d514180791400381c01905895001117105c0442080391095070a410340ca044640041c06100100b00d41c41048501d11044a545501010641e9034045040c81075020300702003903000e8054040001100009000c4034944420f4080792a519401409800d525000b050b0304480d160002c0805002196182c00804445004190707040f4000301d00d03200705590030341002c00181c4018040d5204040041402000010982905004180c0c4000c054202 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 807637706 1250 807636456 807636469
    0xb06090f0709050103050c1b30040513060e1005030d03060501020d0806120a0615171f110409020306041a0303040e100314030d0513020d030c0303060e0c0a0e 69
    0x75078159622003111034202801500144005002d200106805100c184450781c0103c00c610f141c10b40d01c03002030143c60448403403c221a045070000c09080d04489c442076510070544030581d419a2000c840b0044040001c00e24200100810303402003201140b407105100d0310501d44028141518800c1c1c003500d0b441d5080e000150141c0f100c1d44140c41c0103a0105082ca5442c5100f5486160450030040c04e400c0c081510111b507034504265843c0907070b1095039410304140c03268440e40c50380c0002e01c4012809032520f0f0b000d61541381c0394a1081da0a40604c484e1034005046100d0640c0440030b0b408005441700e48130398039101110001e404c103c0304a8003c3d860404100d1240042c1548080846e40080080d03142508000d144841d01030050028031642060701c50100c0000d4689420010901b21a0001c0d5110314603050b541064820140c541040014481c286101503154034400e00c40c155014200aa5510310310715044005289652268002120190512020032000f0000b051825481d0303403000c1c1c0039180802000300 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 807638956 1250 807637706 807637711
    0x50c010e030a120f0e010f02120906060102060c0f0c0a080d15030c09020705120706151d010b0315120606041113050f180a270c180204120b06090f 64
    0x300b10f407010442068119600454180345084001148000c000320f070040c290303841c07030001d080304a802203140c04145009001c1160b201c1a01401000c05003450340c0040e40b1040043c0810790342002c00195000c504401008603850140b60303208407000c542650034038455503040403100a00c03a5081c2882c0d41a68034036a1454004c0e00d8004000486492900c103801c00203501041d4102c2d100d019800c012103525160300d028002d034601540f03020590685c1d05081000c030203000d411004030704040100c4042900960000303141943c004044480d40d0391105408078180c0740ca00600140c0c402c3d01c11048606814000c1060f500130340050303c0a01c00320750350144122842c0509840f8001400f240601000349140c0002000300c4d03400c002d44142c590715020420061140030450b030300000079407103040d074041d40500e04160441581038005084c140d004195140c0740c1c100031611501c070309400d200302d4088081d1050b5040b140200603542e0786a07030b03440f000c1c03400300c18500d0304548047c0b203804403900240b410001618444d2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 807640206 1250 807638956 807638977
    0x1050406080c01021c120f05010e1806072d030f1512110d200a0501140711010905040c02070503070906050d03050331140f07050d21050c010e03 63
    0x2d070740410b030000742014000d0010005c08103c034488580d15900d1840c40f966026081d220400304240d8106070002c00005e4014091060844030384401300c0f018140032898a806c4101d0385881180b40c0038140f089030b101d101484400d0ba0381d2100c0181015096010b5002500540d50b901c014003803080ca206000404200c03a10402c0a00c00e000d413000400180d09a6004050b000c008243d61402c0445d600d0300281481d4850081c099001205942d180c1e51a150410100614003444c14840107924882010b0081c099804010400c18410300c1441c0b0070380c003030b030600700140074040e00400440700c1443e0000c1d40c80d01035205050080c05120804500441680581d41c2541e40c00b178401c01c640809640d08452541c0010300c251310003441d2081103805425080c0040b208c000d0803181025010446090a035404502610790b00050740c41041c03410725905021134076100702c8500302c0390b4042d40c2c11103040544160011711020740664404840c0042c3c9130341c10001510349a42488002c10403a04400348855803803140c0c0d000b52 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 807641456 1250 807640206 807640213
    0x10602031215010c17160c03050705032b0201090b1306050c07240608030d1b090302100e0f040501080610060f1b1b15030e011401060f2601050406080c0102 68
    0x54007050040c0c54079485d41e41d1000003c2d1034103021041a482000700604203c1d084501c16404109014040208001516003100a401c8400c20303c0b261440707294180c0b1001c2105190004d8880c071088c000e6200f2100590028007801d990300d050445032031503051000e0101d8403107280801140800c2d0100068a5030103174401d5902c58180014490103420000c403090007408180c84034000301c3c10b080144050111440311610204503100c1580301c805c05000d03411004410084074200400141e81e403020043d81c054101d05240126403801030100c0c0c1018000ca00300381d04203003000000038441342c1c0001c41034401c5a2400102031383d43c4e1910401c44515128240a10000b0301032408045c00207509101700c0c1030548145420560214081965603550401c0d6102c80c00d05410503864107900b40d094051040a41000d5000b003203000c111541c101e18070a4103001e030108121100001d0840b0760b019007038a164443c0c19070b4400407601d00b4840c030050960006d002c1c840c025810703e20002820000003d01c1d0640d680c05130040c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 807642706 1250 807641456 807641477
    0x4020d0303051305030a0c1401090f0201031a06040b04090c1803060519141b090a090b011b0b06040c050a08160909111e03041e06020d0501060203121501 67
    0x210080c02d00640010040c142c1681d81800258007003004254011041d01c9205207000c440c2003100b00c2842c040d01c040d000d641410540c200056a00e8580000180c2c24240000c1d022004a50756a500358040041c1d500b10000140109919080d00050401c17118416000d1000070754005080780c01903510901504c582d104141c00b800000c405403c059840480f80c0f886088001016085074281c07101440c0881702c0e0110182030100c171b03282d003c1802d0103000b005002c162400c210760010510748507080c451000300564030103000f60968400c500c808511018001c07132101d549140d0415070768540301524001d1160345005031030441c250113501074560565070364607201095a6002690307105800608400400c10485510220b1040d0315886040131382d5400c885803a840b03c400b0385601507105206911300181c5802401008000741c4054004990b2404000700b102d8010860724042010f4003901c0b0000b6841c9050000100d28142c1c00405040c240201010034402c40e00d84055200c01903032210020350004012898 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 807643956 1250 807642706 807642713
    0x61e0b06160302151611070b07060203060a3201030b090423010f15050402070b01050d05120328051902070827120607020601140301090506180d0804020d 67
    0x14900000c902a00544010000e2480070983c1402d049580300c4200807015085d8801a50094400300c143c203410300140303044c50510240c00c00d94062580010403c1d500000000c0d401e0300c6001e1042c0080580d4106040c0e10200b48107520301c44a030325922101410074454a10109600c28003401100d40005000b004482c3c03038648440c044900c0640300d00f6004240d002901e21400000d00c5000c26280765007000060400c9541c250804000e440d5100742e120b2801030040d8404141e82d1403000341111300803a2503580103001c6203072560800c5170708080010904408030070400c040190030750040203074501ca29900900c00402d03080d0421580c003030740c0c6039040117400818210003110a1f4020b1803294018000242400c032070001c1100b4103503040c800b40c0940c134401030750480030341804281c030a10302c0000c401030802803030a06002580c0e1681403180605005503e00e000c140da880a60080703040b180c001055030054504050603000040c04038011950f240310380102141100e1007400c00c035004560040294544203002d85 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 807645206 1250 807643956 807643987
    0x1e1106220f06111b0f03190804050a0801023c0d06060933090521010b01090e070c03090e07020607090807030308040803060315011418070e1302090607061e0b06 70
    0x155400e401d40b00c0c1008546100c4190341d0034031042032023068260381c3c0c0c5040c18140102c0c040e0b039511144050303006001c40e10145e800c5c04030b030703020400140010901000c0c0801c08607a9040d55990202c4c401c100026008400b81da081d0490000d030340107500c3c2c0c070700b0081d580d85101e4407095550510580304018070101100100f40040e03882410703121840c2c0344900c513403600001150380c0780c0b074007911082080e80d0100d07100e5502d080c0940f503a0490301b401c1200c1c2d02403070080c41c0c1c0c0d0165030052003141001200f0921408044c012140c28018203041c0c0c10400b0140b4004401a540300410742c2c00034081101c042d8000b881000c001085d409483e03140c0d5640e07420303448503610f0043c0340e0005810103a1500a2161100007403c00106803402000304026264598405a007409070a1060480008004110380708102600b500315506102d9401d054035013524105000a284009005020003680d110400140210500a40341c1202400c510041d13120b078001c00700d00160790119902e00d004250041d0007442071099003c40304 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 807646456 1250 807645206 807645229
    0x90403140405030304080f010507050309030f0d0912031416020d05031504050f0f090a0b070c030e30011a100203040f0b04031e1106220f06111b 63
    0x10350165080644035400070b0300316082904131034166442000030161450007401a0b580102090800b140340d030414145c11341d1a4480e40140042d400000140c0380600ca6040d072001c1c4145401502981d00b4202c81c4500070003805803030b5200340c0c642180f100803518064a0244076561001e0790b030020000c090012409460703580000f00069441400e501c4074500c0c54a13a4041d0701e01c2807020b42000050340c58114100e54103800c01030f054071459030110000e840043c001c0390f03610b0303005500380c180642c814400349000c9400d0f81d01c1051058010604161042141c034408444428071685030f0700c3d5000c1941404601c42c202c1d9829610494039080c2c00c220a469403c101da4110182c030510310680b8034098503440303421421810342c0d100400d4104006000c0040c42110702c1844100390703d032901000c1c4080700d1386139001c21101c10b9088620518000512541152080d20350380348038080c0b0005044065561100384c4412007203441070340042138a1080340140d0700c1010070350040101106502c01222090002400b02c100c0340c4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 807647706 1250 807646456 807646487
    0xf0a050409020609120303010602160e070c140109080322110f01050d05010b0417010506010e040b030f07080d090f031a040606050910050f030705060409020307020312150a0b030105090403 82
    0x804c1004402d4854400300308036040340700000d598951520a000f4684244d01403140352510031004240520b4050016690300302101d458114242042d504001d00e4603242e10901820355840e10b80700c43d007082800f5014501c502c2e082500c450031003806040d0603401d090180c100505041d150b4075490214508030f810300c200d0040c10715190303060600f01c030240d00c101c82003031300070f41c01000c40881c08100c29190b807010f441040507007000034461420040006000585003541d250b01c074a03124102e03001c0c90f0310108a10240e02c40070700121005285d40706031942d2036100500489000549503400400c0300240983d507602203036405101c11030340c50f85030490b4441d0818050801c899a548401c0300080b15a50584031a0203403070310039190805585400c0c2040300c9003031189445d5019420440c0104001d9907900251011030302401005a0380360303507141c0201d043d0310440720801441d14031141886142600f900c000640b0307480c103031002c11a950300d868200829003c24450240d010120100040020b842210340c00e807002c48 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 807648956 1250 807647706 807647719
    0x1404050915070305010e0726040809060409020d06170a0b070302121609060f0e01110309030a0b041b05100e0411040801200306060a050c0703061805010b0f0a05040902 73
    0x2007015025140010390b407200009440f000180f040070200000103410080c14142003402c900c40b81c00742c40c1184071030f0f44041140807500c40000c0c00d08c22078500f01d56030303004000e248a94851711881c50100039000b40e2609d1864501c0c0c544003082e85005a800f200803200401c000305030705555907a81f000840301c010003507000c02d0340a028940c261005040c280d4000d01402a0b21000748607044401401d411496100104104d41c1056100c0c0d401d42000c04a80c01c0c50302807a000c503003050301000c0146548035a44c2450303014414000028184000c070040580240c1c403603591281030503181082000c690045000b8103a100d081c90740b9034900d03e40038503200008290050000b003060401049054807641050b03124084036510ba5402c00c514800ca0203d16104140e45407219045050042c0030414034014003800303109000380044e40e07503480081044000000c3d94818424080c0518034060051459400760080302c1660900c50001d06a20301040030301c65001d00a0109a00c0b14030b0719003000094881820b0507a0000c6 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 807650206 1250 807648956 807648973
    0x4080313080a1205070357020d02010e0d05070f060507080603010c090b0405150d060815070e2d150405031228140a091a0414040509 58
    0x401d50006000d0310442510354414010004902e40166140240f00c4420145488155042c1c000a501c0a0b804044000084803c085021058a00c5801c0050341d800f003814005850300000007041e042614685060b038203070b440c0b018805d081a0700342c84402c00769031510340005900202440c8264080c001d80b80c0212200002d0380c2c000d45464085850644000000038a42030800185003030900941d00c0521551400b54501e605d03040c02000b0314052801078602c90000020712000c0540c60030305560500c1c00d8030004201460f512034030b090352440d1012458641e0b0403017000051341c441c0520401044030320f0280000441362001003d006206100101132510b2200c0f4026901d05030700c40d01c44402d00380c5030707450040303036614208802c0628020341d5016072844c2c80300404c5904030603003e00d11800d07100b03100c007510f500f800707013034840705480341c02103264503401c0741d02d01181000b4003a40c05400041241c039020315009030800640001c80540c8550300600301008298101a00740d030805a010f0755000914000751504003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 807651456 1250 807650206 807650213
    0x21e2808030718050d03020a062a0203030108070b030c09040c03020f0a050405040e010c14130b030412030b04020c210706020c0601080c0f0f0d02010207050603090d0207080c030604080313 82
    0x141c000b5103006000600361841d120001da42c007100e40b00908022100c4284245040d070300251398400004005203a07030b80311101c0c0744000043c80c0f0803003a541503200c00c2801d401c00040e40256241c00c244509060384c801c5603800a404442002107902407064000b149141003082c030244400351600d400b0b01c1c0200f5508004400842d0b0111300a44100360031969072075079031440d2000b0081503d4111080b405183d25124807002c006411484084d405c510881d0754984038075030605001c4404019501907680b900000080004010740f08003030700f61008250310100301b000d100f0030a10089000d0040034601a91000034482006113441c0c415104648820400600c0e0452990f02c6005a800074400501c450b80000014000000280300756480288103548811101d10352000265118006d40601400f465998460f1400c0d03907c00c1c02104058007019000a076642400380030a5900d0030481080030060082d00d0002c00c450b030000c078159200040081c001c0c110742d162a1500c0a06a002408a00e203a40d030001402000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 807652706 1250 807651456 807651473
    0xa0908030c0a03120509061308042103030c09060801121b09060e0109180605180f07150806130c090305010c0c290c030601021e060106021e28 62
    0x4416901020b450380d991980340c0640424640e0a403201c0c0d683c204410841d2404002511580c08120843c01002d0741020f400e140c032051241c0d0300b058203c800c0101c00ca000004e0310400022056120f07075070801c0101c9900740d0489261142c0d024200000700b000700100f2440c05c64602600040c0d01400b41c4400081c0743c18403031107248581d6400260031a4451104100b481d000c02c06003070041c80e400c8002e105411001642c0350480101d0003005041c6aa40c9001c0341c00780304030300c24a100c040b0400d0221206200c00c0d0b0003403951807000388243c14045034520960000d807440f5901ea02e004035001341c100200103400100e00000340a50350714101c1046120180000810000d000b6200c14020903251610a0166801d1000c1541c01d82110066401c2401803051420561a600b45038003848540002e42c503901c441c00100d0914180c1188e11240003904040c001c00000c000c00c06030304943c0d0b1034084a58a03400320181a00c1c100c07030202005400c0d08006180c40300f5046000c00702a4104051501144030b8100d80c3e109a00c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 807653956 1250 807652706 807652717
    0x6011202041706041b1503090309030210170604061d06270403090e0402240412060209030f0604050d030c180801021b3f0301030f05300a090803 63
    0x40b544090144814040220031440d00c0008140345c0c550310500f03020410841b4580c1d071b0090800c05645000300030526204003059000340da40105040b540c0940c0200c010400da0b1080f040c00c03100003210300811803d184c0b030b00c10f2000710f0329880748c09071403040320a002c04080c0800402c01500480d00b522880040ca202c0c3c4e04014a4804a10501100d4201824000c01182c07164101e00380e80c842003001d200241eaa444003e2840b030001803d200c0003003c8102d580c81a41c090780d4003e501c03850302d42005208006280d00500070780c02c0194110380c00b42002d95242983c40394240d030080c1c09501300c4503403d4004d92180c0c00c0301c191313102242805042d9a82c08115211340d4403041c4c0c041d00e656540400c2d618510300316260f0000368140c0c2c0400a00075203100188500c030440030040080310360810110144c1000d19103d80323040b87c84010886040e16980d590034078028020b48036401300c7c0c1c0c6010304081039804465800140300d140c8e0300032032807135036a18260801c0841948290302c240300b442081d210008802d00c0400044c00c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 807655206 1250 807653956 807653999
    0x15040b0f03101509050d0507090204090e01050f010f05150f0706020315010903020102060703020c1c0203030105011b0f03030905030c010f0c091205210c03041203090b120601120204 79
    0x95680c9000820380d5080d0311141c1001c800f40078501e0480d01c0e00c3d540b01000c2420750b8022204145640d0030340c60030320700e400d1255220000320b60001c100001c100a840e440a040902140d00911982c0ea03060b040c40c0342c42800740540c4910803c480340902290608108903a00241020385451404403614406103950f00710090440740d580e0000200f0240391410030030225007100a00382040043c1c03c690010b510b030703540281403c0170542c0c049410112071504000003480e0490800401900300140c01c0002d440307503c2401041d0225841c2a21003003401e40464119054580102c08540c490744255412000350a5441e0190360505c0103211441180d003085c45074080b01c40440702d001522800714400907141d5400341d840b21a03440144140c5030041500031940c14001d46003110840b28041100c442e040b0a8040c081c140000c51101240114402c0350071700c1d00380485c502980350f080c0d91954401d20b01c0018130402004d68000500721b4085407040d4021000002c03800070050015081c29203c07102e400c4010110090030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 807656456 1250 807655206 807655237
    0x203010f0f0902070b0708060301060f030f141c03020f070b090601080105070c020a050d0521030f0c04060e010e1f0801150912080c1c081f06020c15040b 67
    0x108400715148030104001c00c80040c1c154103180241d1144e1000c90b20090a40060140f0308000951550b0298445000344c2102070004800c039882e802c107000700e101c45881c212401550b200b0121200c0340006800340c48245003101c60200e00e5841d070005c4020703402441740040c1c0e42d4401d01c041c4e40000e45804020744581200360041c0000c0d898030100c10b0a4900103003800c814464902c0218015031210150b400a0b82d0040c0ca048199103800d20f41185014200c81c3c03c211500281c00541396030b103400f9401140030300d407480000e241e6615640028000d0f4440c034428207020520b41f41000ca840e5014002020307503014001d0943c910310b03544180c0d250b07842540c059030300e00003261403006208804180c2500e6620f40440d02d06800c01034204902c03039010301884107010f404180d004c981c1e0501c042040255007410703020541414106e42c0e0409014010010585000c2003a900300301410316102615011041118220390042c4000203060003032050521a0315502045900100004904180344400030f04c005010340f18007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 807657706 1250 807656456 807656459
    0x501021f090303061a0d06060801050607060e0c0607050321011214010e010f0e01060f082107050a060504110405040b180102091f0801081219030b15040609080616210203010f 76
    0x1103401c4480315003282e070278032002000501c500d44848055074030550307200d034001600a241100706c618020000e070740b45a1005000500d002003080100240c001000f000c3c00501c1850341d60102000c0c070381000d005e440b03000061400041d000c0740c40049482002107280c03000281c45030a142c2d40034251001000b04441054503400007803540340c1c09104010003050740e025443e0502d410001c441c0d8580f8154102c2c01140055038400900300701841d002c50b10040d90100442c2d0907d1070501d4440c020303190483e07080c1c411281007000a042c2d0305041c0502e9215503413005200080340c0e03c0100701c00b4008074800321103003251b6082c80608c146031513640110303000403440e01001d00b16402c00100100140c0050300306602c2c0703400c0041d04400d07070041da5044c1d44a007030752102e089010b0800b215003240101894052a03510150f445480c03103900304510000c2003603070440c2e030318003180d5602d42c01070558400090b1b0b8039400c1c4902003200319400c031b0b10031020382045000e41c0d002500040c004060f884160381003030300a0000c4003c2604e0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 807658956 1250 807657706 807657727
    0x90c0219030c380631090c091b0c03081b0f0c21030406020d0e010c0c030f0f21110c032502012003090604030506040b010501021f090303061a 62
    0xf10781da030b0358401c040c0410061409401144c0d07848000c41440480141841440c002c1c500002c40c0d005003401d080e1000c109016a0b42804c00303031000f41d84a0b543c030052a03d044d5101448211881d44a81c1700d26417120300b01c00c011503604031400240145281501e01441d0340390069484400000c05800b102803051940b140d00d8a803280d4140050542c00c0301d40e101c07602112010a210860039260310640004d0010780701c50312507591740e011704110304181110354030b40740a02d0020b13908504511481c0b40030f99201d07a03108500b118103850f8500c0030450000131621600c0c03100b02c20404c040c000b1158010301c8101103503044810940c030001c7d8000b00001d030b502e9000401c0502449184811802d9102c001c5c2c8210480b110850300081e010b02c0c00404180c004010304880340601c0e07041041140d24030740c80581a9540d51343c1c3c070b081c003646600003540c0440b50102d03100000205907200203800354005141c2103c10703c140c0340e000c00321002004425011810f042e201c8000280ca4031040190140e0096010011070340c4140d050f6 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 807660206 1250 807658956 807659033
    0x20306060603060a09022a150a0524030307020a2d0b040b0c1516120203010f2102090c0306010f1e030b031015050a090c0219030c 57
    0x4200c03600401c401d00402402e90b9030001408100c1d818040016616070f68401c4107183d6a15180c40407010540610103500c040500013104022000e40014004094503a0b04a1100390303038051310350b00f4001031404010f800b0428400d00811101ca402000c403807800107290b01003885018036501c41d0200d8080c0070400b225141d0680000b000c00300b541180f4100301820215583d80b24000c070301442d00003420100300b402c50184204546c040c0819a064859641c4c50110410f00d40445680741120028200780d418629001035802503906940b420021414418200f076490700c0061440f4800b4072010086824100160300c036000307010f0042c500b054109039607113004400540598904c20a140401031200c24841a03a80c01c8111980e81400b40d1801080b010701e504000b07072800b82008484d42802d45025042408141450121811030310f064508400403640c1e21100401c0b18840054900582c11080d240040a0140ea03100c0b15098030a00b000442d91119445624007444007994010000002c08400c1c241114612b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 807661456 1250 807660206 807660211
    0xf0c061205060105070f080d2a1b031b140318010216030206031f08070306150e0c0702270f06030a020d0237090b04020f09150c0f0a020306 61
    0xa40e41482141031003000208144500e29000e459150400c1c1d03607000b00110481110b031102881c0c8801d0184c0c10b10f03c0b21034580741c5101c1000700c00c1c03501082c886940050041000d142001040c0018040a5489490a550040c28400d880c2c4200302407a40c060005075130750048000c2100c00710700854440303401406507203040d00c01c403031800e06552180c400840c65900700d8103000192035054400907201d840749442c50804d122544145192502e420101042e40500066180d0450b40180d00c103014111811940cec66650946000d50a003102c0c851000a0010400030000c000c2e81b440508030029213104410b100340205000d1002009000980741844030f2000d046041c690840c40c210080c1214101d40d9000907100d005800000f80900921a26840c69500400060110f9071203c1d0040a6640100014a9029845004040016203095072400144c2060702c00c0d200c5111003c3c2504e45020f000c0b0040000e101c0e403503501d600f03500c502000000d900100a0001e503403114103210041403a450b0070310400d070920000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 807662706 1250 807661456 807661487
    0x30b0f011106070c110402120405070905040305030714040b0c010c0818031c090204110703030e160b1602150702040e01110f0d0b2707030504080d02090a030f0c06 71
    0x765031075104040001c02c079039030080e8031030808481e4081e042c40c2180e80091a0034080e644548086400c6218041c9140d0240c41180315100343c4218588a240d503030100d5800b5280500040d40610005101ca4003641d40320000d014000c4d009420b1030740e070f401003900580c4008020701c0c190f51580b002d4003009410083e1581c101070b030185501041d0740713030f54411980c1c2c0c010f11100d6400d12168400c2003d00050030713030000440c0398000d4014000380c2d08144940d44241d0100d041100000d14100c0036210f1000c0126400d90009561400703401f00c01d1601402d1081c2d0f801c001038074001d00c0340022a01006984400c0500c2004d80808101501ca803d240108000c90312141300d40b09107641044079000d80c0d03014120840d440e0484c1503918030b485000d01c802403c018000d10383c410347c08c034014004008ac1030742402d07210b10181003034224800040d51101c500314140e4105403802031a50394280000c2d5540072254001e84903000c80a44180d00143c1d5070b48030005080781d0240c2c01d90301030440c9401449015800080b00700113140 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 807663956 1250 807662706 807662717
    0x20a030608062802071a1812130501080402040e010f06061409101b05010e010f0b011b0b07121104051c1e080405040e06090106080a03090314030f0a030b0f01 69
    0x80b0f00c2032030380009041084152402c3c2d4005108406c20034200c40303c00321401c0b400008a180c3c90008224046000d00c206a4003a62191036519245030802da002c544a50851106040030b140c9041c0065131001d0780a00100d0348903484032a0403030f190009114085001403d6080810400c2c45e00300041c00c50a11114400c002140c02c100c144030310307218440b0b1502d00c000d451406e201c60a052680c4c10034180e03c8090010284d50078080308105403d41500904940d80c0d501d201002404021030066800717034140781c00303640f503040a000c2c0c01000c41e00c185042540b203070850030100b9428607104111421503a9810300c8020750100820140114140740b40310f1554000d902e0300200a01580d42c40d41481441c030a480c01c01070603ca0354200c0b0800c41040705980c02480060024009400340071000e82e280d5a04a034400002d6182620001c1c0900c400180c099006415496042e24141182c86841c0c1514164030011682c3c841080034a9070340d50840c000b0003540b42c4ca07030ba000454405940c1084210b10200030418104076 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 807665206 1250 807663956 807663991
    0x24032701090305120702160b04030314030402130c032705010e0102030105090103120909020a030e06240409020d08070c0303020d080709060f0c0206130503120c0304062001020a03060806 81
    0x30307000812144407260401d0070b14105d64500c10200e1400340c010341112036440e20f042c400a01641180e0103030050320711a85501021908540c4000402e001c22038020794841c00d150810004a140f6a004d030003401e940c0c0c500414818481e00d1030841400120a041d90500103400c18042881300c28403458100e000341c000258038651501002a1080c0010701002d00704582e40003200c4056402440102e008200611096403205602213018005091010041c041c078084c0d00f00041000c0e030f488440409500030f9071900404455204140001001c0c00070089070006801d01e024400708507080007400c00700c3c5c032a5040f0a0002c2c103503d070003420918940c5084062007421414400d003c1d810180c0c100990b1010b21307200c03107140841003045450080001019400244c0060040355800080c19a8826944144c0803140740d4542e4000032011f038854006980d41507001031201707101c0300b845a030825000101c0d02400d1030f501c6980c0d00141d422a48032801e110080b0750b4988081146100910071298024025240c104012 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 807666456 1250 807665206 807665213
    0xd080a0603021f0207080714010e0f03061f09050405010207050d03090210121508030c011104210f060c02030a080603061b030a0207080d020304050c0a03112403270109 73
    0x10440a4035039030007407442001c1c0f401514800c01c0074000034030390201124071640d60341303003421145c0803407501d078900082c441e600304841801c200c50f4600091501030014207080d6281041203a600c60b000c60702c20010741e05000300242c0b0400d00d0003828080e502030000140c0d00c0d491494001c0ca481042011081410300348107074540540e03168010450b40c0071950402c145514030500111005103007030f82c1d82c07120500c41020f0128481030004080e0011100d040005c0000300b078500300d03500803800b0f03610820360000d440a020b841543e40650034880b0551044181c00544440c0e81d4580c4180c80003001d174a80142c2c80403508180d1140d105110a40084042c0c0c0581132504100200000c0315401100000d42104008003040100170182d040311035040e0031074020754542c0718030b4003058081c0d48180c0e030683e013030312441c07a03c41c0c490320340700011504503507116a40b1440070b40a1424003546005045098581e00002c285180c041c5031070350002d500c54400d0080c0307000c80c03030f034400a80706401070f0025104160703a15024030724000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 807667706 1250 807666456 807666469
    0x3050a0b15091918061419020f1b12070b040204060b040e04060c020f030c0703140d0c060b03030906070503090922030e030c1807120902090703020319020c0d080a060302 74
    0x3142020303408a0b0396502044041c4d0b507681e60f4240100034074a41114004400300c4658540c4c054040380c900045006201c8105800b40c3c0100106018401c9041100030390000050040e03403080c00500c8180c032504551f50302d2909032a08452400da031088560070802085140c0ba101d03180c05003844080e482d08050911000010480e03000704002d004d03541e11492a0078450017042518810030003441280c2d070318001500d5854a9030480c0c4011500111000e004034441c1c40c004c107110740b1a510941e03410304151500e46410000c1e01d410002c1980600081109404030f8540c2c10051014078041c2d0000c1d50345a00303803402c0c03216440e07006207d0306550741c0480c0948450f420003850103003079940604c0c1030100030309d1103000603040107010940d00317a100307040b20b030810561421100c40350f104900c552581c4259036083c1418100b6102c503044000d61000b010b6001410135402980036540010003900e00002030096224940126800340c00000440c1d400005801d030000d611829881d0b01030010300e801e000f21451980890131 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 807668956 1250 807667706 807667741
    0xf050a031a090c1e040e07050d0f08280e0312031906050603090f06010608010305060126010c020105060406060e0a050103020901020a0503040303200102191803050a0b1509 75
    0x508415840800d2400b5030030403101400c2070f80144459420260706007444804c12000001d00d00a900380726050340d90240104002088030070241203824170f85100c2c0d40e080d0808100040c12150b0303c1d810701c16129072107505103e4182000c1c01d440b003150580e40a00003c0c101d01d103d02000d6100341d011030300c44030316000c604007900e410801985440b014035422070200c3d0094245500001d41010011041182d20000000d90700d4200c0902415501580d0f02c03800220f07041e03d000d00001d0615400803004001c0340d00d52035240040d05001034030401c40d0040c41094a401c0d03d416684880c0180c1d100d500b485814501403003608014901ca0401c0f241000c0d840012a01c0380d0803030b100b80d40c14981d0108407500940d0081c00908240d55004065943d610740301c0c6006000800d800c55024084071043c3c8085480d10030510032a02554451550950251007032601140c4000c0c05c4648401040e44d004000000103070100180c2600c035224544070300c41440c0c095401c00e191119600964440c000450502928807807240d103905 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 807670206 1250 807668956 807668993
    0xc0e040e1b0f040204030b130605160c0b0a270b100317160b01170c06030408160804090606050322080f130b070321020903150415150f050a03 62
    0xc4000482c2e400100280a564000f41901400c3c8003082203c450713425205100743d201d44010000d9840e4030f058510340395801700190010810300140310740443c56081a065010300a143d01081006200203000c8414004205070000d840c2504010b03802c1000f0f10481c264002c484028064035985546c844201400c01c0040f0741d6600340d40000c9024811045465034040140c22908081c0296034415038802c41000c0760b0400315150207400181717a9140390081c1228040d0390003650007400d04621000040044440090880c1c0040d0104000141d44401d4000c06000304600c2d1100b9459140c0584003040c00070400005224140041c0b024238000f495120640300a0604106416183e07043d240444040781460340101b255510049201c504041d0700c504a26a20441100500c2450050101c0003003079015031106613905401441d01e04100c42250781c01107074068081d81e408021581080038070350071942c42c40701c010101084000c0602100041e028540020802510030108551858513102451000c905904 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 807671456 1250 807670206 807670219
    0xf05070210020d0b09090f1203070e09090120091c020a0b0a090902040306060503240705071104061e08030304030f031806110a090e1311030f010c0e040e1b 68
    0x114105003013075022030581d0074081c01018450a19481d0706aa0301410321301025281b007502802c1944449000c10b4078090919901ca0084d0004e8040401807582402007a14030190350381c8005141900000241c0c4404100c0e0030041e9035284001400e010204248181c2000c42c0c02502c1000303001621002010700844600340b42c610303180d650540c002c480240e003603481540d07080e0001c0380110034000d0560000c0b086840440c2141c9910403106981c000000903000804031055004002811032401003004091b41d0380314040e002184000f00700014100c80c03e81d00010301401e0104600c2401200e40d102c443e010f000e4450003181989403030395004207041190703010001019100c4005502e8142038100100394194442420b104008107404802440d0b0000307000ea000050150ba00010b20700090311186008100100c206144484103031941c88031140917403e0030ba0144140c0a1003044c01000303128190142400c0d5903955118130360b100401090700c1c244850700384a0707000340004000d0307000c5041406802413010f4416 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 807672706 1250 807671456 807671467
    0x605010206011d131403031005010c0302100c02010b1e0a0b160f08072004113f090706020114010e1b0d0e06041415071107030204061202040f0507021002 67
    0x40c2c02803043c4480d00205441800305d200d8101c0003010003e94401c1512032000e105040d524801110708503200d147c090b015030030564403401c904030342c0e030000e81c00c00e4110b00020490585400108054852080c42c4d02e00701000060008454a86480c24074002c050031b00d41c040c1055012171512030f03001d001040080c001c0c8a258100d07010000140e050b82c0140d038100700041c185407081d442c0e080e0f00030408034001e4495840c080b07581c0c41002e0313410240c0c1d19260080200c0c0c2c01108056800288002458110390604200c00c0c011100078022038003a14801c0540501a206052400b4806400d66025858402c0800440b40040c40518250046250f000c44140320001c04c100284e00e80c10428451004c00c00d2216081080d0708810030b100007007203030049210311180340258200c00c10880d04c40e00b5080f4503620940c0e080c00800d4259203d071001030981c4030700d5015100e600da901ea00080132501554054240c400314402050290310381403140120710b6880c44400c0c005131415400082d01c41101ca110f010f1403d601054 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 807673956 1250 807672706 807672721
    0x1200f15090a1707110909010b03060612030a030e07150f030f0204050f0405071106090a02010818062706040f15090203030a030906020c01061d15060f160b0a020d0605010206011d 78
    0x313600c05210b45c00340c5001840c0c240031240078049d242d44200207001e40301d40400b2940b9810700345503640104420304059424504606801c5000c1c0030040d0010345584038104021560f1004402c5480c0d503ea2152582e109104004101034152000c1e00c0c4040c8050b84140410800398a808000012601d000c032000192a65840c6080e100c1903401407000c185841080c040150400300050400900340c003d80303d0408643c0d07440c0407c101207130450300794a059005034021450b0008011040d003d407000440c000c10300191015102440c280b001c039810707560540d2000b0044203101c0242d440303002c0d200d10f44406000b80611600400d0ba0380c49a03400d10300405585e500c0582c10710410342d0541c3d07440c40261000b4000d49a030351003030858188488403641000b5901802103102d070700c3e0400f00699100f502408260500b410b101486581c5d4000c81c4100a44000c0e4503041c400041f0300300360341c500c00e840600d030068aa80c010b074160012039140ba0400740c1590701c4240103001c101c00420a003110a8003d05071010740303644002 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 807675206 1250 807673956 807673973
    0xe1608120913050115022e110412032f0c06030a020403020303030f0412090f14130c020604030306051e21190b131101200f15090a1707 59
    0x400072040303180f9107030002c0760500050038004000140c039800c8900c0c008400d030710041c041f85484515222400c0400d0000d00038103240d00308452003413108a00c1c03800e041d0344600420040512080440010f01e146404528032164a140c100c0100c10140544640c080200042582c9115007032011744503903804000100e8800b0290115006140e011742680d449060802c43e0500111080d01e080741e484d05040074030f54000344103051000c1100c1600da200c44136180741c038001e88130281d000c01440b5040040b00b1030901c02845640110001e00d440c41d40100b406141a04008044070740b0b98010910680452103c01026070000305009000c0e20208c85210710300396200c00d840d40c84400b10352149954011044010280e0003060200c550050040d00d20103001c0e07807000c020448160941d800205064000c0040e84215442821f440c20f0221031414000750083e40035240d2481e0404c001ca0b000c1300750b80a244c5010300d032200552a10f401509034402030032601200e40d100705002e40440103407545114003044080c02d012618 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 807676456 1250 807675206 807675229
    0x1704030e030c0402071b0518040f020f0406060e1807050d1a040e0a1502190c050f0601080a17040501020c15091008011d06130b0f12010e16081209 64
    0x4104540d0364010703103040400340103184074501c1d0346c900310701d4000f455041150074010840c3d040f41d1246050359840d500c403904c100210809903080361191440207000d4582d84180e0000d400d6a840e048502100c0c08100f203c0103514002a050000c5400e040c441035540010079a181e40c40c03440e40210f1501109625090f000e0a081d01c1e00390b0040c00c125022405100c0440d042956900943c00700206110699610741a4803409581c4100b107100849155502d45c4107840510046101d84e09880c0313400305408259240540c2230700000b810b600300301540070400a0384038010129500c640400d50030180f91100203500c42001c0080c06003d031071346a8003421076841c00412203085070360040181d1048a150240200008001d0180c0d440001d1030801032207022030b400301036510411005081c501c6c0c0c8040c0d48501d03030291044030368841e0003896603180402a660741d14842c444104140c80001114011154400d10303044042807e2452808070a5090140744c0c0049036100d030005002401c0d680d1070900001185910280 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 807677706 1250 807676456 807676459
    0x30e100c030506151c09030507021206060102100e070302010809070308180f01020c0a26030c25030c0302060307050c0d0309050c2211071a0708071704030e030c 70
    0x100000c0003200340d00366102c640141c0301552240c1c006035901c03151002d0751188030350400510703260701c50048100d10740ea084152810311038604682007990035400f242d56540400b0792210304d50401c1042005550741005900700c0041c00301400d01c081c20000b50200d13101ca03028000a8100025180041c02030303503081008400540c4c1c01001e040c6d85003108845950498022608248124140c21070604558800240e40220400080c20014160720700071072a0904085115400b2110b0b440781e104c2c0070799050600203042030a4028000c0e240d0018400e50001600e000c1c2540841d43e100d900a052010600744a0b1040034cd03903050b240c6640c1ea40703c00740166000d000d00301020500344038508482d83c100707034075402100000744100304a69004080f14204901030920000b410100091460ac40494015641041c3d40915229103520b02d41000c949401d42002c00d1050019103150780079040c0040340d5489003210343d2008891400d1040760214400340d00201401400280c00c0142003c0c100301e1540d400d01c140841381c0310 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 807678956 1250 807677706 807677711
    0x30402101e080609010b03010305060f180304061d060a0504090e03070f11091b0706150504060e092b0e0f1225060e120102071b03050f120406030e10 65
    0xc1d840c4014201d070000ca8049015113140030000503900d02074003e4a041e00c3d44400580b05039a6608030071041ca400c000c04015180c0144000042810010300052001c1c00f0580c0e65105491140c5800802c00c403240b080a42c00344e4010801c0d20005da5220040d17405a9454420200321b4140e1040600e20710302880e0b0010308403005615540c0e040204103003014280030741c25240e0314841e5441c0e82c0f45000c680c0560000301c1015030101b0000c1e0005026500001c0d1280d4180c145618041e2a4408501111955041241503480300401d009c2029030420901810585900700d28051865001030351182e51680702083c014011460080f900e95a07c102d51049917403409000818400c842c1e120b070b9652690010001040d14111094243c204541501580c003924460f441e41c0306404c00207001d01c11200c4807001829841d5609003d40c4001900c50380c6058120400d030080e040c1d050f82142002800c00a0324110f07124258072880e40c5000c0c038000c44040c0c40c11501c0034200012682d4801d60701b42e042100d185141c5600a1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 807680206 1250 807678956 807679007
    0x9090c04150b1204080f1b06090a021f090b03070f140f0f2b0c0f1805060304030207080d1806031e0e010605090c0304030e1504090f061508160903020603040210 70
    0x60441b1000c681c010504400c4070031703d40700c00074031a480e80c1152b0800303504091714407400c141e40118903440a01c7d502c010324046e03c0c0345594141010a81d041510000000742c80d00c45080e1009a101c081080004441c0021a180c41c1000416904500c0388503020000c07074601040780400410412829002c081c0500c64540c00f0400040302900102407100001010812075083e0807000c5108a44804003010086070482c9110b050400308555500003c10480031440b49660115030380f0001d00c03845008804a444543d0440c4501080300306210142e040b0b50101403030403061140e1441d003841d11a40000c01e4080008002e10120b80180c09400150000341c0c00052030030070301c0030342c4214400462055029a50b0113412421260810110008a240711310f810642400306021804941e80026280070503a0301c00194680d94100380d408120944180801081c44002000480b8501010300c1d0500c400d03170b00d800c400f00ea056a00080a074000503002900030340000030000030581c0210140f08807c04800d03081000d08 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 807681456 1250 807680206 807680227
    0x1c03110d05161d0a0b03091e151b0d0902010509041812030209010c03031a0d0b180c030307031107090203240d0f0f0c0509090c04150b1204080f 63
    0x10860b0400d00400201a81d070460116040c400c101142c00d58024003180301076240202001c015000500902190b01801e01140d08030308100c62a0120f40c41244090030030440c00443c60607460800030700801d500130410404075204c4041c481100c40b01c000e4110001a007040c5400101d51501581150507006441d09016511010038008034900492054107282c0007078080d07882c22010380c000d01c4c0303889003c18800d42e80d400009002e034200380102540036100c180c03549084000a4420319503010b040c0c0304140c4500c1444401c50425070b032000f100c4600c2d00100b0708010480301203643c1e44985000601040071250510707502d0302c0280240300c01001c1e4500c4c1917450741000061038404e200440503960140c074030043d40207103c1c28046610f0301c43d07681106071209004c40039120f850040340b903220b0440d00c42c0303650003020032150f5500082c14050781c5214010010710300da0805110072141c440d01c0c1503012a40409003000041640b0b0101c0f0300d501c0c5940802a01d9454030b00c6d0203811400b071040600b56907100420421100c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 807682706 1250 807681456 807681481
    0xc050109060216061d06040308090c030a0605092a01030c090b0301140a08010507050706180203160501090e0606040303030b0d05121305010302130e181504020901081c03110d05 77
    0x3c1900a0204000c0c0c0310307007902d00000c9404241c40c000c44540040c000200821b024041076a8004010020b41c0d041080100c0003034203041e0f410a0840320250f8079024028000070800102d544800106510295600001c40035801e9040151140d810940c5850749040c8440c401c4082a00804020402a03269612400103a6608110709110f600074000254001401030050180034010501074a0b140d10745007190711000d0180c83d054913001862050b00402c0401620100900490340098080000c4064184400109008040d0380402010000071042c880075a075007208a50859606040010b80c40e9a44800310b103606000c008050036500513000f0300200c45900c08000e1030840e080141e00d1b9020707500c03a00154200c4c041e803100d0303440c1c44141017800c0c4580e107101c40c00b1517003082c0c104e0903020140d10031142061901030750306066000240359200b40400c40c18040c000c0c5002d485204050b2410404052542211601c90546201056212545044020804401c40d01401c0102d90b05000c03038503004040010 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 807683956 1250 807682706 807682747
    0xc1e090906170d05040f060e01090503030a03060e1503060c180603091f0e0a02131d030405150a32030103050c01022817130312030e0106030c060c0501090602 69
    0x41c90003400e02d0f050409100d101200c0988000c002010300700c50a00004556416242c5541030503c9146a000320742641d00304081c101413841540c02103030850900703550906014025010035a0b18461075105042136502044056000c05061420345c0c9602941e00889003c1298201894100300b0000500010742d030041904800040801945070300c8a0354030403090100c498600c1800902d4200002550052400802012006c400d0800114010f12030000c008d5101c0ca1413600e03001c140c1d0000604000c83e042a100c0c4400f110880c8080e07500341400300001803c0503800342c6c0d1400c50301c080800d80d14900301e9070340b10104031b4602c02007403a51250384a10b4001d1741d44007000421800341c4a4044480f0089005000400b03c0b105450300e1031101803900d81e03c410f0000e01c0c0461404d0401010300000b0201c1001c0e0404034021809105c1c0c901000320012070141c201e40d4400d240100d0760341450424808910230400380800c5805515151940320500d0a141c0d00401c03071600010881d900000b000718060811011284 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 807685206 1250 807683956 807683999
    0x315040f1116031707081303020c030609010212090105010f0e220b150d23210304030f1e0c050a06050103050738090d06060308031005040c1e090906 65
    0xb030384e80034011200000300b00221007500000d1988400101c4546500182040c0940b1a0040350b1482600d403002a003401b00480c1d01140c161b5000c15000740030000e5003c1d450308a0f1515000f080b155041c500000c111001e01d00511868141c000040b030000d0786c81c40100050344090f91113800b1120321901d85008544d07800d586108591107004070b081600d01d41100c00b4440c0590101d010841c004c401104151207d0301a100c0ba40c4074050a1012a54948030b0010031491034008070b000b0790b4030707e014a00509105400c4800a081102c4003507031880da83c4c0c0102411100c500e0a0510048481840c0340807860028403e60007891a4103190000041140005000044d1030550392452040f0340e400f6400100e02e500c5d984c88804d107060102000c001080c25400a000c0c2c0c6001170130260a460081c2c59410560703d142d44210f4002100000b00500c04205403200c0f0b01400c8122010300515030004401420640d03009503103605410303400b8801003040d0049a0010082c030314a0414440790f0b94421800004407980c0300c445 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 807686456 1250 807685206 807685217
    0x91503060e151f0f08030c0601080a0c050906060405061903050a180b1503030f04050906060f1c021605010902040f0209010915020106090f0507140315040f111603 71
    0x220200402c1c41604440c1c58003002a05942d00c50280302505501d0985103000000b04401003240740a07003000c100945400e03001075649501d50242d45143c10300581c040c1f0040d4200400f0440040c2c0840c00043c11075801301c440700c0c1c85884100c0003820610a81c2c0c08a50310040010f03964540100602451019007042d440802180e86c410f01504103845a2403140c0440600c0d00b03031560b0015500c0301443d90001c0d4000342c144110b00441d000300c0e1842c0e101860031050748801181c10030292034005a01c1e0b900c20810b44516003042c00c03c101005880c0241901080340c90f00d441e131000d40550156041d00c04524140441c001501050300704940200140d500680c0a03600b000001446a4018000c0b40d51548041c1c0d110000c251401a080f1821240450490119500c0c0d0000042425450048040c42081540c00140d2030401c0d52001e80b00c410b17080d1540c80b029a051013042030b489001c0e54850041101540c02182e811200100c1d48000c0006151540310700102040010100100e20b040c80c920368403036103d1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 807687706 1250 807686456 807686471
    0x30c080105010e0105070209041a070908071e09050a0b060f120f15060a0c0f110f0901030305041505040503150601090e0f1305010902090408130b09030a120909150306 73
    0x1103e41080b619090f5000c110300308280401401e044140c6540315002e0010358204c0346c00b014208904480a0f81d010002801c982418400004240b21440c020625a080700c08900c0210017802c0800d0002d10030079906503a40c800142168509801c41840101c008004940d50790309102610000c0e00480c00701044080c030640028a400f80c45a0b40782d000390700c4803c8030348020000070100100350340441010070030801241c03d6080003561044244a50078858034080050120443c00d02440c60700c407182d10741c4103414400040010070b402c0011642522101400d01c0081400c1d01d000791001c4c8111340c0800d03094031680f00240710302d001e0b03401d846000751402d90ba02420240d0b81c1d4103101d60f6030010fa65000500000c03501007844407001c0102988458031030400443c2200c1a80c0018404d070138110350540380c40c40000342c00300542179100300b8a80070308541910300341085500b1001c00c0e5900c0303082c03c0081201140c212040507480c0552203020003404081c00510050105441c0001c2c03d88040c4002c4407881d003040b04 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 807688956 1250 807687706 807687709
    0xa09060c051015170a1106030f01090c1404080606030f0a080a0c03031e06050405092a03150a0209100e100305190e0c270a020d140106030c080105 64
    0x30300010054221000300588071007150520001c04040c80804008016507500003425090000f909503100100d074042c107001201400c0c0306030740c00c645482c07044c13280404004200b035092400704010705540c40c2c54800500c400c08103e086e00d01c2c03400b5071078040348250003240002d05a500003400c03d11811f000c0d02902d0302c008140c00c032a076442c6041c800051904c841807244145103841100766951040c02482c000c01d24400781e0981900c0284811041c100d055203070407050104e810036005880d00403990400601d00840368520105101003141d42138401255041110b41c1c0903a001c1118641d01100002070705841d061484420000703510400400b030140901c00742d4074040302c2c060710401c0b1141c00043c10600c0036440c4200200c0060500804c00401d114054545e402e41d07594a1260f100000d4014004064a41e60b0504220140282c0710303900c108188254030b8030006084110413582c22074040c10b000340e00c5007800035803e4080e2080e140100f201030418030000468962541240040200a03210308549988810 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 807690206 1250 807688956 807688967
    0x270b06160c06050c3721050f0d0b0312040e34030b03010603120e13090804030b090f0a080403030f020d27080304090b03100504052a09010b0a0906 64
    0x1003030070410341c008450041706591407000029264001500c0381003800c0620703041c2d030204800d1120544080c4d50b922020422a00c5045104014103202d0820504100c01005212400d00c40d0702c0c4051151500c1d011503030002c0e181080130703106000e19040c900b80c60395260700c9844401c0004031242c010848240d04000c042420005040b0130000002ca28103100d054961415805801d0803004190150343c0d406001001c20408100049202c506980700a804105081003085140807900010b130154901004100058820070442c0c0441c3e0780714400700b805507104140c86040450300c2c80c05900900800103401e04000862000303100384c0e03120780c44a842d03000404804aa81e00020079032100495641450301d86002d0b85500700746210302c04141031000c074985420000f41941c20580c04032440300d40706c500c1c003075803840c00b8061a09203540d510020000b0b450031f40c5501e542c4083c07030120098040341d0404880c100d030050701200d038043d0304054407240035942e482100c101981c0c0070011120010b004024013251051144 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 807691456 1250 807690206 807690217
    0x608010504120e010e04230f190612020103051305060739110d140f120307080c1c05042f0105030c250f03120501270b06160c0605 57
    0x183d4804141c955042c061000418500722243d81c0d44061010b240c07c02040c0e07520645c80381000452440442c14002228141c4186600107240740707900b04030040c048111194611401d00381c0910f804a815210300c0d0700201c0d020521030b005001d41c00344100704505182c00c200c110f04460b1410015401d650841d482c030300a50801410211144415285560041a40a20040e480e144010701e504406d400c41c0d076030b004048894061603880ba03007009207400240032042c042c000d000c401c40d4140d0303455450003050090800c0c80041201a0440d4003080a42c1351150021500d84184d0b42d102d810041400d00342090400001c100041910388509a10480c2c00ca001e4982d10700880e040c180c480e0740c110380301c031030f070180e6190000d0704c401c482c02001b0313017260440e280003045d5a441c90307010b883c42403c070032102d003401031a005000c074103580b5813810100100501d06c0c41102e010303080d028806801354001c1011030884c001d8640d1101d030070740c03028000c211f0381e4000c4d84138040c14401921600280101e02e44e1a4015101400749 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 807692706 1250 807691456 807691459
    0x1502070b06040f0f14091e12130506030f040b06030f0a020d260304151107030e010207030602270904030203030f131b060e01021f110d0608010504120e 66
    0x4001007000c1d0b05068002d801000b42140001c2030001440c1558400c450b21011005180448641880303c00c030000e000c0c1c00201c44400185003210881c00b1a025a19015501125a01c642c00034a2000300700000a0b440b02070500101410f40c4d07420310349421885c07080c06450940d80c1d001900040764081c80d002031000003a0714000050041030701d580d000c1281c010582d080544990741d0703040170701010540d03505010490b102d50380c03620b03a101d08143c10054800b4940200c050030743c034a00003080e40d440c0c02c01d10a13980050350514080c20031400500040303040005d568002000d2034000301d500c007120300160a40b8443e40b50b050030740308a080361141c1009500601942c002d00541c108001040c00c3d030392035504035139002c1640807082005209543d41c450b05819040c94400d00e40c00785c00300912000380d00946104800100740700400301242038840350440d54005c400d2a0400300d0b40c807020004041c0c50b000668018003d0580200841c9569204072406854101c800300c03504805581c0250b010b40c021410504039180 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 807693956 1250 807692706 807692723
    0xb01121a010518040e030c0d030c300f0c0314130f0f17280806090907051201020a03060b040f03022110090308060a081507031b020a150207 61
    0x10540015150b5612200f07403420008030f6181960940c4d142e60048420001c0054002c2d070740c440c04030054505007122030160398205400c00305403083c0141e100f00e403c109560708030301411041c40100d480107109115244844100c1d404e050002142140a6002c2c504007009900c0a11000502911040d200f076070407505156240c0100c40b4031070201c3c0d20109a00100b52040858039411400c03515040702640001030211115200005e08030300100307094403440c0c03120807451480701441c08943c3c000f03043c0c00c60003083d580c091710250000440010301009403000900b00500012140b07956110103602039400f101d06240440d0070200009003044261046900710740c0d2000c1608002802c6508208075541405a005402c0658840900c3e02c0700007400503c540203480c40c80050f10b054189002f800e0350740001c02c80c6100d110810020894000c0c0450f4200408584511241140e9150002580101403082515403c3c0b4450a203001d40682c00246200303105004190044e40400091010303816031150300300081143d017 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 807695206 1250 807693956 807694001
    0x70c14010b0907170a2f041404090506151908060f0f16030b03010f0c03091209050d080306030a171309020a0c02060c120d091401020a17150303030403030b0112 70
    0x10716a42c440303003c000046d5900c170b0401d011001c8418004e20401c181031340048000070100100100785218075400d520aa800744118600b40d11065100e101c010140840101c0070281c6142c0303691f6980c0e081030304130001e80718214401d48421b44181e94900445841c548440c06a01046002c0040c400c1503224072490800c003604038158100c1100640000005503030550b4a40402c8a05994680150080e24003280e40006064541d818030080074101c050441c01441000b240501485d22104c1110000903040660560740b40c03145c80200c1d18043d0f80200241c540322030b407114910040ba0b54001086c1c81d0300e00501032035080d40c851400d801244105000305001c64002100c48006090803c06840c2820301d8406840a00786111008000c81d48440003400f1011b9072028a02c00304072501049c0004610302500840c10944241400342c101440403125601440c00c074000103030241d00e0307083c0d07594040700040c0590384c40342018078010380a07000c0c940245003c100c4d2a00d13030507074210f418800d01d94010b611001032140c11 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 807696456 1250 807695206 807695221
    0x82b1206090c20151b040b04060806040f050702031e04080a0303090b0117030909090c030a0302011b0507112407061505031603170906190e0114030f070c14010b090717 73
    0x10269004144203c0c5c40070301c40045e51000f11000380c0000c2c002d503152000c140c030707042d001c0008070b6034041107c906261a004c144000a6400801d4800030079a001e410440c4410841c2d20010a000b80d60215142d48942c4034800f040641c1904007811b13881c802c0040c0c0501c1c0e600c4030a0072000c00d602d2407103851290310902c8900100d25140300b25a070007445401c2070f500b183e40508040fa0401134401c0041d00542e449940c01103102442407860314509c442c40c40e2990420074103903600040c9030003c0ca1054490454070700c14114210300c030386001d11409041d00810b5503640c0c440c9400ca01504030240c584030040304164000a545c100496134407000000c45020985085c21952071604c0c0c4404a8258a000c00040c00091507030349807171000340036090740686503606110001034000c01d52100c500d09c242c1003008041861841441c40d0003176035000ba071058031440541c0d40c1c0d480c040b16400700460003d44003400328900b050400406510a0000c41e1003a90501d81030350b03171408144c9030b03075044018402e2f004003c040003a804 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 807697706 1250 807696456 807696481
    0x903070c1d0c30040201110304060e04020a022401030c09050c030a0f06050a09060306150f36020a09050102010506010e210a0507082b1206090c2015 65
    0x1004000030300c0b001001c1c4600420760303ca4125140e16504039103003052000f50740c2c000311a080d2060782c180045103400e0803c0380081101c49403200303182c0115000f0a09440381ca000b400040012444c0c01c1ea0310f01004103001103034003122420720007550b0241c0c5c40800894498114040c031440f80341c100c0c003403030716688036892100b008111158054070403070b5a91034007003119502e4000603002000c10600104802d4110b04014085494008040d0078045120300f040154240c140048000c450b0f0700c107187c40c20001e8224101d165075074901c04d885000d140300c000001d41d400207903003d807101c01e180c1d54a00c1100c40c0c4860040e4200c0d80300b52000c50110358500339682c82860280301100410742000407895040f42101800f41c6002c00c0080219100d4000207000d2101e5101001281005015a040076003003a0a1031013585400744400f05901c100101c14101641c3e0000d0364010900512001008022140c49010024101101a030b8040c529241c400c1300e4845110f0001007068098441c0016641c803621000d805014 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 807698956 1250 807697706 807697717
    0x3020d0f020a0612051012021e0907050c010b03070303080c0913020307020f0f0712030324080102181f0e010c080301060f090e04170a0c0b0903070c1d0c 67
    0x180d4041030340d600c20058807410181c20003000691101a00229480103070801d955000b00008a0907203d07a0b010044180040074241e07940340c0507181c540000c0980074034090394030140038001d50001d01d00400c0c000c4540e8002c0080c014003e030f01000f040740340c21400070192108507910014000440c0380d0302003012501d0110041401c00c000511030007100d1807030500b81c030683c2c0040351500d0150704030a00d110181d03141406109040032a4a002d05080e5050024012503424203190150805a48807440010507006441113070070001c180307241a6880359600e803190b0103540113001e0120092285a000201c1d810400e44d010001660105031440100c0c0d848402c82e060344440303045604019401c5204008249114000c60103031106507214100c80400c61406462421036601c11640c01e20a0410040856901c2d0480f541109041a805030b0700d146c2503000321070003078110030003a04a100034000d01c00c030706070004010300040c0c0c400c0903682e039800d64680b0f82e00050728050460054491100000507201d000d42c20040c071 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 807700206 1250 807698956 807698963
    0xc031302060903010f060f0e070801061403070314040f1103010e030f031003020d120921030c03050d0e0309040b06040602060f0717090604020310051b07080f0a020d030608011503020d 80
    0x60502016004da03001d640c4a980305841c0d10385803860900c01102048d581a6000d07400d420085100e5260038001007001e0f6aa011980041c3c0000c8013181c50144203405c20910800340300080291400c1c44d003007607001c400040808540e0300300d8200d4000c6a50074117009007044000c841000d1824041060b1006219500041c100c0000700d400031400710050760741414408d142030042c54010706448240c14060a00c00017900400b480010b0002030915010030091001d0540f58149081000500b40340b60a40b40c03030244181d6000c81d5410285018010480000542014041110103000700f00f124001c1c06443d102d140540070058210741c00084460074501016030700003045150810644000b42c0c43e00c100f103541943d412410307411000600c41940390410128884207a40b510400050511901a42c4201042c5d00c1c10200d402c0041006d109019041061303e596120420013141d81e1880540002e41711240300001d900428a80a00414602014403071441c49a003100a20744000f82140c0810440f413031540002c8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 807701456 1250 807700206 807700211
    0xe010c060b090903070b010603020324040b03060a0f06050f0307150203070f030906080f01050306190e15060907020a0507212a080a0506070813060e070e0c03130206090301 75
    0x106090302e41c001e480c0c0c400d07920b9102844d101c0f04a031404d401d0040041e4409000c040c01801172250b42c0c83c0840c40182141c641000d2040c9220384400410302400282c0380c425414010034003086071000d0150005440010100400c0000d01d0300d0740d08000b01c0c15407001c4042d801d6808a001400352a0640a408030b10301c505004032400c1c042c040c1d0701c20343c00030f88140080340020003820f0108441500141015000329901c4c8424100d98140070120703943c0c100c020105002c1c0118041d4401c2648010380c010f5940702c90020503034400c2075403510203500004007a1030160003100e402002841c0b580c8003069031242c040d0311102500b011ba24001440c110044c6c601c0141c00b4030041d401006001404c0c1c201103030703000111300b4081d9100c0c2c09100c2c00326102c10210741c442981070f040800446d000940c0401e01550002c4c1c03900b8030000d81c2d120408031643d1005c00d83d00041c0001d02c0d003084800c41543c00034100c002c40d1085d2a9400c1aa60f85445030515800300303880000903110703100c0f0094018034103c80900034018014000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 807702706 1250 807701456 807701471
    0x1415040b041e050a03120c032a0c0b090a031407050309150f0d1a12030f03071106040c03120905090402090402040e19050d0c0b0f04020a090516080a0b010e010c06 71
    0x10b0030705103600108124007007445c11114074002c84050084140076011820b00300202c610400340100c0103c00c8000c650b02c4270744040306081a01d4050ba8245060a401c02e007003a4440c038042d40280d82e241e0315000b0903004125080c4410502e0300e00a81140c4445512030003071030a04d1244420b0080c240c0049000303500c820b0301030003215000d013000e070040c1460401c01c88002c50054001c501d481c4074030862a080d20b001e26050030003140c920200000b1126800d404225050b543e550b0b4030011a00d81c2c1e550003280c640c5000399030900050081c80c05022095038011050355407e040007000503107450f0390300c2c454150041000030004002d031800e05550307a44680054408914044061002802c0100c580c500c0c0052440b00d200c00018480108159803200030a410034800c1c0b504ca0740c6a1912140000f44061420118240010119110407654a000b044102000d021506140700c1304d00071003141d41c2400000440410025115844a00800b5188481130312074001a0b08100c0c01181d4903070b01c1e02c20980e1243d40b68040c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 807703956 1250 807702706 807702713
    0x51207020105161803140f0d024803010b19080f060c250210030618050c0a03020903070e100503070821091c1415040b041e 54
    0x46228501a500009070340c500b40c440c082041000e0040b42080114000d9084004220140307800103036904008010701c3e84000084d01840c0000c0b8400110a5005100031010199000100181210b0020020a00603c09014154070703504000d45200e07507010354802c80000c070140001603400001d0014001080240344100825685240841187c0f4510080d1008211000c0f00744818031f04071180d503000e4501070134110080042c501401c1c004d81252004441c002c040b10240180b0000c1807640074200c00b04a001070394000d8005c0038248a40f0300c004140c5041084210060700c030320f600c9250706060250602d904084120000c1d009076480c103401d803280440c080795040c05120110303c101035803d80c1031141410031040c5070820406900441907a4003840c00e242000d506920403005040b05020100d44582c15140001d0038072000c0036400368903070703c1e5403903000c02e104112204100000c61002280d002048488107803030015001c441c080c200c1600d0901040014100c076611309618190301d00c1c445542115501d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 807705206 1250 807703956 807703987
    0x210020d180c05100e0a033206060109090e06040b0a0209031c1403010312080a14070c03180b0d020304020a0b030f150d05030306010f02120a0c0c0f12060c05 69
    0x344160b0b0701080c41c0d4000c2000340b070051502003c42d041c9103030090040d0341107400300f4025a040d0000800c480112244c80d0200381140d0a04810401e0500504081c1030003c81c0c100d40340c030810f03903c42d400200c403003a0124490805014034451220624000d00540c1e40e192140c94584030043d0000c10119000c0020b0182c940c0c0800035594440741ca03420107002c86035150340c0a0300c40741c03010454041040b014001040810340030001b0721452140b030308142e9820754500f03000c1401018441801c80800c80110103100c5c100790b000c881030303411034460b46406120074403514050070500e00034807814021a504000c08040c0b00e41c9a0065604907101901280b91980c0300e5000c400706070400c4136040c41e091041d00800c40c05400072501d84c03103200029501c005a004d1103803509600d80c071009107180e05001d80c000007214214820450f16200140080706207454402c01c4000404000c401181550300a86008010034894a0b00c0c2442c0300300d50f18000d6140b10403150f650317000c000d00035803070001c000d00005000f600c202c0340945 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 807706456 1250 807705206 807705251
    0x120f1202040b031e0c16021f0215070503160c110d030c0b1e04060203060f09090d031505030601150216030b180615040b040e030703080108070b0a0210020d 68
    0x6200c0c0940f039151102d1680c842100c4040e29690b5490028140070001221a08440311008100110161010070b4008508400002c952a43c22042c86403025031219602003805020b0b03a40c4071410b4502920354000842e850b01040c0d800c080c29119032041e0a5001e4001c954034005640b0a0028860110081e03002507200c1070140403c2d40460210b107201010041d586402591080104001000d844203182d40301040c0000104004c160320340c00804203226954207105003080302c3e0300403c19801c0345000004030f41c40758031000052020034202002412000c514186140c00da070400350081103180e190090030003251161600450650040d0700440c0d03c3c00100b00080c002443c01909121100d003012043e40c0d0142c0c00505284103103800a40501c00d01e01142080040780800448011400079003480c0014000c3c0940e5050702d490344400a0368104041e0028451030403291402e040c0c90b00c02d0344d540d040d60307034501c1040c4c94000140c0052600582c21282603010300420300360210001011044040000302d110b07920b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 807707706 1250 807706456 807706469
    0x6030714180f0708090703030c02010e0f1906110312040f0213020d0207111804080903120c0a020f100210092103061401020c010905040b030f100b0a060c120f120204 72
    0x1002c1c200045543c10001d0183c125007004010107025285840007403402c404c1001c000c0c1000400050f0241580d81d6455140002c0e0b1300800b05400008408911035a4900d42c1c441d060200c0c02500408064420200a882400341054100c2030a035489985000e50314010b810b00b240d0240300c810400d80018010b00c0513100f99000c880300160f9607441410540b1684040311a0759201e0060b0440d550a05036688003c2c540103a4030030841600c034002c0034002400c1c00c40e80700045804490129080d01500d40000b00942d4550003a1001080200003c050003550425002c950f40940d11a001540880c401988000190f500504007544649000748200d5159131020510100080e241c12080c0081d00402e012140060824002400801c440100181c4021385611505215130fa4840320880d40713803420b04c0344131003140c100c00035503040c0000c294140000f454009420f500901c400c080c0451000d00034184060400c2e00a034a12482884048044030f100e40840c481408222540c1010080010580040e00203001c5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 807708956 1250 807707706 807707731
    0x3050a02090a050405190302070b0a0504051206040203061315110909070e01021f02040e071101060e280608031c050906010506190203090a031a0a050603071418 70
    0x10140104000490090082c2d4105840e000601000480009443e131003440c03d410524141c030304e1030a05030704000b030301d074442c400d030100000d141e030340440c2d0210007072041e614100c507800d0f200410940d003255500c00c100d90080d0503600040c00b0030126100710100c0103407a0311030035803603002c825a4103c03081961100c0c200b80720788001c04035242c1303c1072800c5074146070700a11a10b041d06406150500003566034420b802810840c05101c110802c004001d83c0440380a031880e0420508107040c5080000c0201d80305041d074580341d51130004042820955011410700540032060148040c10f01102120302d0003508800440006549600000700000d06101030300000f003c03c00c02207840780c3d00780800c0f0151800100714615039000680148107e03521720040d87c0b40b000842403440341c0d802c0480d209a01d1803066055266216810301d0b80082007002e084003950801c01c4c0402c0441150b110000984255203003601c0e0b003035158000020501c84104043d4410a400314020546481c054129a2101c800b400540c3d40652b40c41c07 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 807710206 1250 807708956 807708973
    0x402040b0d1404022b06060608010513060b0a050904091a07030b19091d0111190206072316060603020109050109121b0b130f06030b03070509041b0305 66
    0x10076901c9a4441d000c54080002c0c0c03980f03000c0d070000c0d00440456062521142045a1601c6130050245825590b250720610030800036403602c2d8081d203548001d00c1114402c1048c4a00c40c0c00042c443d00480c012681745101c41d908010801c50155030a4100d808483d80041d510301d02d02c0045030100004508583c1c0c1c1d000311038528144004010141e49206c941507001e4050003809501307442c903002a000c1150010031001400c05003038400d00310007400f215142e03e010341c20141c4280a40d80404001c201800802d602e40b5811500c154081e6160b1000b12641c401052052201102c044205030030080c030100001c0e40c1c0c0d80340458a061071000405e038100d043d10000e50f01c2d41d0910443d608012200054102401c0413001035141c8109600ca81c44100b0f4000c1c2480c00e40d00c3c054000c5ca402000102c05030440e075800347d403100303000c070b440081c0036040340304902c552840c040700054094000c0c45a4440001d014002d025000d00342024020712610191045138130840c0380f410343d041000c0e2403040d003002e184240007409250 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 807711456 1250 807710206 807710227
    0x90405062d04060b1204150b030d020d18051f030f09030816020a2d231015060302030408070c030f2916140414011d0604120804050402040b 61
    0x82e5410740084d802e101c41080480c0d00340b44103200260340942e1080c84180c54510180c1c401002d011030792507041c5c00d48111001d140da001e801041e00d50b03145820755030f40d050958007507000030018a0740b0701c03620b60096a00e0010300c102c035070407200000d00400c8030306000c00c500301c0510b0070b02c080340c54544080c1c3c00036400300107110004412800c13113113030032080d0706c0105100030b802d44400c9003484c00807400e480b000418548489065803500b444020340d9402609042c18124440031550706c11803c0300a021060044081c292240222449221440e1444142441390079007403840540082d40060b2058038090020300426000600100e11180a1071143d04e868076a141145044a1020000e9000d00c0c14003645a003940500c5410320030441d40540141c41014030404041010f449a80c00c1c44103501c607480b0b000402141c13148094480b030005403003c1e07950403440d62424411101e0041c840d001d841d48040c040100b003207001f2642e007554a801d8040d0b44091324090f921400507040340d02030b61040381c0c03021000c504132a10 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 807712706 1250 807711456 807711461
    0x60812180301060807060810031e12031109060a170106050c070614030c030612101b050906121f030b010306140f180a14160803040b090405062d04 64
    0x4082041d40288040c40c1000c0d2000d17101c07507050098208000d501c50000d0b100780201c40e4524011608600000d4090b0340031a0350f251000714882d415141b9040c0020b48120682c82440341d64403c21501500b02d00b07140f42801080300560000c0300410801240300042d0307a0403801c01070300314001c00e89901c0d91aa100515680c803400c217861648590244403100c0e4442000032601c004a0f80c0c04456250816540d40c2e4500001e210004c412000300243c2c8038a4240d88145a81c1e9404001d45c1042026091250040c0c200212024071030808443c0d0852001d0000c00e09200034814030980041c888101f218083d0002000c4403090460f0368010303100140c00b00010014401e051054206044103010b00381050f2908180000420740301a1083c45804030b0610084502c8800344800e0b0807040c0d0001030b0105001c01c003c00c6036070f070308594400c10040055540700000c1c0f00d2000012901210b803d14113060a29119208100013480014021500521683c0006030014441c140b40d0a41c20b0103100c40355203066000f02800308 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 807713956 1250 807712706 807712747
    0x8060c0a0504030f02060c030d05041b030213050a0b1c03080a06061b0201090f0e150102030703080f150d1505090d05121f0308040608060d0321060812 66
    0x80095040100040c0a5882002c64042c2c80d00035601032540b10741c40c03011502c80d206410060740170303000201e041d400035852030f0001070207980196500c0d550098007c249591a00c4a403100070741c40040d10f4448070211a46410003503204010f403600048a148041c081607041d00102448020104007844080402d50025981600540c0c032850400110b414504098825000300300d03440001d8580b61984021a031240f2608405410034814104105590f80078040b40243d05079070400c044601c880b010182c035440041950744103501603a0741800c0ba247c4540303000c0754500140001d0b41c000d030041404100380e2614072583c96028898009040c0d003400c01c000314811a000500f511456811101042c0003869000e0140c03540d12001030792a6405481c0c0c01c1c070b62030580c29420800144900c45800001c103000701013004c0c05c01c40710300c1d840b494038950b1100100003000800c0384001703003c21000b030031072228840c002400e200407200d081c0c400244030342c440580074946800503a0808580384005070303075140101c502e100c4c0d60 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 807715206 1250 807713956 807713971
    0x304090f0603021224040b0f0a060b0f070309050409170c1c091401170a0c030b04090c0513020403120f050c0106030c26100c02160e0103020406150c060209011101060b03010806 77
    0x5c00c281080c0d595000342d40d402400004400391054013041c070351b02c0ca99101c0001090341c00041f80d5103941c80c3d081404c0c1508618400d03004a40b4681c0005100d00300345c0181140d00c0e07400000480054041c101c085040d40041c0303040b12252044080242c680e40d52500c0c084803140060b200c2c5d012151030208600d28014101e40c000c0c0c10000c2541c1c0f04140100c042c5000c9070003e0751444045007601c04620200c0041ca0007902c02c135405400c160840c0b0511480c0340500054480a0780c0c4c1000e840302d040c03080b03401c0c0d1266102c002d02085d80900780f5003d0620840540300601c015240c44e5140c103141e1034806081d80c0458106481070002050100540710000c1d840c2d690400340e480503104405403003a00980c0b246c3c054201c000d1029200d507111000310b8400d201103800b00c00d204110f03200e030740d0303d89400808080017400200d00030707894420701051200d020101c0c41444107103507944d485682c41591703d90019400c411819418803500d2114144c4240007805400c026103503000c0c100d070720b13580750500340742c6031240280200 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 807716456 1250 807715206 807715273
    0x2090909010c0e01360608010608090a1e080d050f1602030d0e0f030309010b0108071d010c111005030906070c0201020604080702010507150504060b010504080304090f06030212 77
    0x3145881c1d004104501c29000c04d0038001c1040b10080f055400d18021241100c0b0106405c407410000807801000f64825282c0d0b9035180e220356a00d402003980d1040081c1c8441d081c90f4000c1c0d41400008000c180b4a0351043e40d880c0702510060712564511403990410b0340d554054a89034001c010499007082c2e000c0342d20051000c480050f010a002c070103501c03441040000084d458981c41003003054141005032201501c5200110f964920b44941010b009002c0c1c0f4200318001622032010500325403058100401c5021401c0e81c40d80442c0005005465241c01104211401c5921a01a4440d80d460b1000842e0407050303521003903680d190401440742020001440c42c014089541100300150743d00107682d0340d000e036001c554659101031a00041c0e074a8060204014201c0928440303520b00607003030740c0209002d41c1c4980e005104440c0d400c00156454041c50140070707050ba000380000c0020a03615080560f800044d184001541501d0760045501600141c03209106540080440020303a81030303440c140c0001d000603007103 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 807717706 1250 807716456 807716471
    0x170c04050a020a0504170307020d0f05011b0f05091306121b0f12050309090406090515012103050903010212061201020406090506030403260604150e01171c030209090901 74
    0x60a5405a0701641d07850128081a1b540d48980400480306d045400420305c0901c07408600e003100310f011100f94121007a50a1602d048149001c2c5c0181c04001411501c49843da6002c00404803103681103110450f6003c1081400914840710a2040c1d0020304264103444907003960034100310505a61500030380041c0c41c8020f004100000c59250700c0b1003590304000043d43d103221903060003461402140255548001014240300400500b81d00203c0c40320f11038011b0f907c040995204000011509100b050910000b025003420034101484101d4952403190401500705010380e0f0200e822a00b00410790003091030b0020a106072850a00341d034107411041c41d0003e5140c2414150003c00052861044500424010001c9410140928400d031050703e8200b01d04a0702c0b05408410980c95076058846030b000300c0ca091032440c906c1d6207000b507500c2943c0e91080559079591038050320043e54200c22017100c516000d80740d6440035008062211042500360303590003603207030807980c000c0044940015003040c0c1141e1400c44d5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 807718956 1250 807717706 807717727
    0x7230708040902030705131d06010804030e010f020f100c081b04060f05091c11030d020a020f01020304170a030905040911042d020d320a06170c04050a02 67
    0x71601038070321094000d40c0301d8461150a540c980201d1480c01c00c04900e0303000114040c0d4241400c20082604000100104d842d010300544814101b0345000d400520584d0380c56a13694003c8000c1c00c0041501d10407130301c60361540307501e03d030815100c48102d164032601e4608405040da4040b80060f0848000f50142c503003403001d0f070048220b0748598445c0e08107200141c141e40c1840750003982a25a126000361440f410030100c100503065411107208104e0b0499042d018951142c18001381c00e40241710a60000c1c0240344c1d25400f040b1003108882c1c00d0b0b070304510013000003013100031484550880ca5140c100040840414914007e8140d1803913420135402a403030300200002040256000305586403041d500019000c0070400c0e60098490301c0740c6070128010400d90600a11b1003d94000c0101d4024039008000c0d105041c0e0349800f8000f004c80d10b140458100181400400c941041c4032a0002e12610700025681d80d581d4a0980030300e008001380c40c20380c00c04e62000b015820940a0a60700c41d000420031480e240c0c9210 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 807720206 1250 807718956 807718973
    0xc05090414091e030714100c11031c090804080d080703090b0106080601020a0203010608030d05150105040314070f0b09030f060907120f1505041506060c0f0f0b072307 73
    0x8641103002402c0c2400b0450300c4240704442d0b6054120900c80310741175500c02c0300d60341ca808041034214036034071b000344048c9154840d003c1c80c4d006011a502540c5090b84e18a00b10041030348403590207420b03d0f41c4011503800112511b00420040400f80050241001c0c0440094900e1400030301500c14141807400100010301e001041c0760540c6d149040551403501c440004030724102c1d10700c2c80207416620b080070214078081c0c004040d000410403400180005e9076004030840c1544040d1100f5804140248814000100d22680b0301a1001d1071000302c550703040e0340d0030105420204660020000c9500011240a91304080c0085c0d030003803201400821040c2081c040c903960b07404080c45035010382a071516140b010404081110030050382c101d403a000c81c09103440f048800920068404844020910010080c41c4040c0c0c01400c0c00c451a07911b070304002a01984403440c005114040880b02642d07240c4c108800180655541d0f8040c060558610078200b42c000710700008085244019840e6941c01d00070003000a10b081c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 807721456 1250 807720206 807720223
    0xa0b0108121209160305060108070801110915070b040818040524030f030301081c0c0c0b030a110a0804060f200a11070602030c010f0c0804060b130c0509041409 70
    0x70140422a0740e1440382d201e0a254013000e4401c044185140c00000303102e000284117041c6c42500301555010f980e50304032103007280d00051196024200c14020500c03c1c1c81d0070000c1c1e901a400300b003882440c203030b0b66541e629044481200c08481c4048003080490880802c9000d030b000c074100541e020421802c184040c0c0302000d0041e51a00d00c2e0811a4105c2801501e041c0028440d06101038210703501c2e540c407540341d60b48038000c44030148440c02c40582140720302d038070490304048001d4125013103020941c28900c420360391740d00081407429910b8980c80d0701195285824000e1404900507078a6141506180c42c1103030503698889010303042c8074249100c540304010309055100c80c2e00d80e02850190342c1c01d00c20406031103030004003074894010301400000050440d0080014402105010000c101c00030300040f54504076400100200d000600c132800150028003a0340c081c0b40d01800041480710100140035a180a40711805644000207201240030344143c203046c0148541c01840e00041e036a645044a03941e640c03149034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 807722706 1250 807721456 807721477
    0x6080a02040f020f070c050f060a0503072a080702040501050604180207151e0f05071b020a03020a2d030f020913152715020a0e0904050a0b010812 64
    0xd51003420a0800350f581100c88134100c0c0b0001e90b4803160301e1306140c51040e000c4d101c0d13540141442d2003500860b1910004940d40b4101e0b0343c80e0706003903880c1c101c804c903514140042403a0031060400301c00401c1d80203040038151090300c00c40203e40e494416105020586a06038015800741d13005010910509c92489510001c4442c800c00c0140c03101e0450816500c0380100101d09030f12a407412000f41d400345035030b00320080c02d200d40840c103000000c40542242c0032250100c3e0240c1c00a002c160312191a484a8525901494001030106140d280c480d000a0007a0303070b1311390000c03906800038240504000003000042480203800d0650000551464451414000010302c009100746114000070705010000079410000c182c0000c8004445c5d400f80744850010410261b00e406480800e0a051941c59443c8000003030340c40d80400765441080400716040041d40200c69a80244104190f824505071600030300184128040d00080c5201039582c20480400507068000844513080031700380f5140c2102d0b001c100c803000d144 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 807723956 1250 807722706 807722711
    0x2105040911091201060609061d1806030f0a1101111005070f14070203031b0a060f290d02100909020705010f1425090b0c0c01090f0503120c0a0206040e0a05060406080a0204 75
    0x1c0080c3c0d0488032014048425442a010796042c00b100d10700cac000091162006404540c0c0c011213030b148503507486800c030400420018402c0020728995110b03049619000f41a42d00300e600c0c211000c006c450948404451010000b02405007004000d94041c0c0c1d511502c02d201c10109180810680110380c8a209088158041101d40100d094403c4030410080c0f1491383c00000c20800c0f407480e040a2750240034011004034a0b8041104041c17502e944440390b1a01c00c480041075208115229801d104030380e880883ea0406018681000090810352800142100c030302c04d900009e5840140c0425104640d50f8040000c000d00c00711040080d481c1c01d11003002c03501c01070bc0516020016070480700305c1d02a4616023112008100129203446c0700b0800242700000c0e003d00740c90340101d03039895029115901546101e00c540c5903105502801281c07501d080140500c424003000e442030800190003091440d84540d00c0700309000310303071410030a040c0161701c1100e4020700211400c0c82020300e4811070302e81c0d0fa00c20000c060f11030755 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 807725206 1250 807723956 807723977
    0x19031209110d0512030903120105150a0c081318050106110607051315080f2d0402150f191e05090117100302040e0307210504091109120106060906 64
    0x40401402c181c0c412003d0205591b031078807200040e141d810024060748207001c4000082814544480040110500c2965960a10105d0041180c0d07103190ba52095803c8c260800803038610350f4005504402414580000700d2060600e0480340c01101c10584c8078900b00540604148445c01e07011416a410610614040d62241e60081e80b615412540740c0c4942c5031040d880072440251074001da078180c400c0e1010308404406a80d88840105404100c0103045201041c8601d080c601c05c07407010519803c40d00190a51a041c1091b4158504a51104891320003014000c1040382850703440d0002444402454600b162208261086200500180d400c2a4081c03020220309000140d214407003407442c01a100c0180d880034205000c00c110540c80a00041e40075278109014240c0c0048000304580e03040c2c4d07005190151034a00341d0050580344410840b0002007103410000082c0450703940c0070741a400d1400341062076175006420100004c407040060300611302d0341090001c10049030881184000c40d03c1504181c050f03003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 807726456 1250 807725206 807725213
    0x70303050c0f1903030f140c0d0212180d02120301060c14070b0910020303061c020121050703051602120a0302090a0806070305010b16020f040b0319031209110d 70
    0x180d0001e40001c240302d002166880c900042e040030b0f14031402030320100001d65201003881e00f9191543d1440b040e0901c0034000c96600d076021002071100058030380c4018203046a85916800445080d075103140407a5080041c2004048103200d41848042070340024640754122482054880c0014800c880034000016290010f0080203603103428101c2c00c19050f41c58203a250741c0a450a50880c0c50824026000340710605525400041240c0c0200e4004245c8000e0302c005c00c900d40d07144010928100d04001603551071100d07082e03041042c1148118840000308291401e1000141184d10007000c14182c070070050402c0014603000b26142c1c0000e00852055580c40141c224150040c1c400c00d86003035000784002000007101c1801103a80c4d4000c0442d079178280700c44c4c0d0740c50310086d80e0340c041e5003443d80042d000c903200340c2d0062034402000c0002e218050804580c10143d540040e051440060030040d0b400044880b080030187e100c2441c2000655001007003103098055200c0c100b940e428403600d0744c05280880c07484000e0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 807727706 1250 807726456 807726463
    0x10303080f07030207050f0d081e011e050a091a04050105060a030902030118030305010305010b0609010f0318060921030513021203040306020703050d0522030e0406030203011b0212030405070303050c 87
    0x526401c04112281c1c40b400758403895036500c1030f000a40009d41300783e02107039085800f0030420b51034164840e0324042c17903400c24580090701d1000b048601031b8143c41150015894507210444002000d00e18000903c2c01c0750180d0030140c4443e056032447c415072810006000d41d944030030648400c00f03110f14001447c11124804280100b170401803083d80c2104110300f80080640c5904114182d81c800c8000703000301c4a01d181480060300a000003c0e000c100c0c9244c00e0720056210381e03c0642d103113a034083c1d01142840c3c0d50300e612007200c1c9841c0d02926282d44d0720081504103c0c1014034000000321501d0b0030016841c084081420400185030020310070742003031000b06984001003050f00d01030b42e0061011035590410b894051721030303801041c052002c5400d2200141490102c00d1000d40c203040400601002d011940c2d4048401d00030207030380154416511a03011001d03031000d20a1111440500f64845030156603000b002e883c02030314030384140d1190310400400001440c04200c413004c49602d418195115007070b540d105403c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 807728956 1250 807727706 807727717
    0xd090303020f0a2021010c110a081215060703030e063301020705090a14010e190c0516140c12030405102006041a07020714011701030506011d010303080f070302 70
    0x805408001c109001170301e040d80314401442823500c03604140c050044500307440e0380d0f00d81409450003105026610001c401d441401364024201450080e5031a0000e00180081d08100010340000342d0783d090300e20400c0e9041180769003100003070074408101c01002c1c08401100c00c400408a44000e800c071382555550b4000c014001c06848018494030043c40c0c0600da6600400d0000c220401c46401000000303412800e0744042401501f50549004100b0004456a0058808051030100b000404c000c00f200200402c0d000701d040500c603076905070f2034608a03001d8030710b04a028007116103e10400e103403284600400108803000c031442951001d4040c0c21256054070000e0340c1c00c59509071401c44048041000b5004250b1603c56407141c02248440086003004000c0c3c1c1c0000c48030b140151b07008500c01e02c680395452001c5040008149000da070082e13075020101d0b40d80c0c2001e074401c813100c0d40514014400b00c03101c040321000021202c000c94034039601d103440090140340081c00b40003040341c1c80f50104001910175011140d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 807730206 1250 807728956 807728989
    0x6030c12061403070e091b1f0f03060f0b0904050606040513060501093507050406030506160201090f1e08040e040212010e07051c050d090303020f0a20 66
    0x2045944104100c03a0110b10103503544280194540400c5000e03000f42c00d01e021b0741c10200240800682c40342d0710b20b580058440c5480e402042e1400503190b401c00c4842014443d0380c90750b5410480d481c1307110040c0035151950840c00d40d000c000742c4284a204916426100d071080704031404545601d0358400315060741f10729000643c0005008402d611483c025420841c100d640c20381e101e05890340d651038000d2103031800a03d031f81c0407d03850395a107601110780740a03140707407503098002981c800564540000e42101c9071136004442c207411007020404401c1c241014001070b100240000e00030f210841d558990b9800c40c184006042d5030302c20740380314407198800b070741e262140d07a010f06900d84c0c4e1a2074280340e00c8000021070b0202d100b03c03c07044140d0074100040c007600b4818611200104400ca08040800c001691200103644095051003c0301020610420507048803852940b40c9484460950600034184065000c81e60f11a038803448038800098501c4810203031503107180d05103041e442000000540301e00d140d42001d1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 807731456 1250 807730206 807730211
    0x1b07080c07050307060c02120f010e07030b0c031006080702071508090c0109030c090b221401090e061801090f030306290307210606170a051006030c12 66
    0x44100540080200100000c4404984031180d990342010790740c2c0014003071200064a4031902000604008000c04140310120701910640041c00320441c1c02c44a465250f02220303400342c1010000d00c0010010745401082150174540b540c5031445110007804038034452041085031040010340164803d10100018042ca16090561191807020007402c000c0142d500c80d605015909102e5038a40c0102407038001c49500a4407041810b180000d000014501c00740352035042495201c421102011405420000a0403000d0004e0004014140c185490300140c0112a040b40303480071040750103000051466102e25421086514202100303007207809441061801045014030304828001c0540681050f4240c403050140b065024681040a09410f6400e030340e0f400d0448020030201d000c0900c07411880502d000440c05014900a1030a4254101c810950202000500c40210500d03441260020f5582094510340d06120900300050814132084451041d94180365079804c0350084a401407148854140345040304 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 807732706 1250 807731456 807731467
    0x60a14040f1403010516080703020405040e0f0705090903090d030527090c040e0f0a06031a15041b0e0424150206010f2c16030b010e0d020103051b 64
    0x101c03101c0090340e02503801c0425000305684040d040c144111481a88031074022a40b40032100004ea51010b0007405035001c064080001040c1a02c2d00d014240100036000010f01c100405e140c1c0f441d041c003040da00001e100c2c80b201c40611401000010540d0a080021540c05154028620381915144100301c402801c90000101d81c01d4065801c40e04002180c0c000da032000c1199a4000036a64144160700540c1c91001140c00031a0f451000e940c0c800c0e6010090311070000d08603841e038454120fa00b090621116659040c2e0b010003071041e16100140d0103c480941d02032242c2d4844a901c04030000180c152001000382d0300c40d16480c01d03619500003920042e03140c44201c0302c804088900009082c064003400100100303403401280c07060f04c0090000c0c105c410405854100c2818510016003049038010961044c42441000e414010714412903a40251002c10596840c000c0000f40501511241c5505a044c040c506044030b41070f460307c25000c0403482d42440e0018507959120001810b042041d4200340b00320501080 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 807733812 1106 807732706 807732719
    0x40605090402070c0f1e050a051c0623010e041e080d060605210c0901050c0a20031c021b240d0c0306080606060a1404 52
    0x151820030f41e62250f01c10104641c103d091444c0c45a941003156645200c0d00d84402d44a10007035241d000e20f01000680b00e01c0c1c4034418180103030713a80202e54030a124410144481194040700400090000012801140c80301258200d0340c0c1505c03400225041200804c003500c11a80049684c1c04421440c100c5403007a06912001c0b900c0784024003400340741ca1024000c11b40584003c0da43c1c6901c55029541810b285103100106408115540c03090208000c5900211071034a01d00f03080280e0303202e039070010891030080c0200e00a000348041d1400c4200d00c0100900c01d04100300c04400f15445000a404403440c002c42c42c2c002000580e11104120044560100a054004030010703e203001240b41c02c1c420300883d100c0e03040a82040710f80010404001031031485031f407140c03500710700c3c04100c06414500541d80c0c440b00a00541e02c10040803c102404910603070409140004800c0495200c940d2541c = true := by decide +kernel

theorem cover : BRFrame.Cov 807553956 807733812 := by
  have h0 := BRFrame.cov_init 807553956
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807553956 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 807553956 ≤ n) (h2 : n < 807733812) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
