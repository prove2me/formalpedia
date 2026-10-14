-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0689
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:09:44.373221+00:00
-- url     : https://prove2.me/submissions/9310fb9f-bfb6-4ca7-9816-e1ef70935785

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 123741007 ≤ n < 123920863 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 123742257 1250 123741007 123741017
    0x109090204050912190306080316140105060f0f210304090b0108060f01030c090f06030f0f140c0a110303040b040204230106140705061302030d05071a1510030e01050106 74
    0x300003164080c005c40f140682c1c2d01d904d81d00e000e00e10040c20350061030f0751381c4803090702c2c0000070f4041e213100000c100301180a4030403100300c2041d030009142d00d4200c1c1c0c012601c01d03410007605050402549041c09858084100040c0381d404403003458800c00f6082c58521044d68403039403005c0dc5c00d0055141902903440514020b1a003440f2501c0c02600282c1c1c195010040c40b0305250307454050091030751040315403501a26450300720b0100d1b076654400c010010300302e010300b04107070918020041e8100c0d0064029580e00060341800400c071520780c5c04a60760960b100ca0038034014030403080d0141b5010002880a588900d004070741003c00c5240030300501041d102440c250001b041104003040d402c5a44000b40241900c20f54034010003043c00910721b17001544175000740500988503080401031441d06000315942964801e4094416000c00c22405071410301a95600824407104403008861221022442d01e03403000f2681c03100018494180d022504000f2101c1d544400a503ca902240581109020b4203004164174540 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 123743507 1250 123742257 123742273
    0xe04090201170c0f0318120304021e030c1005130902070b1614071101020c0103020408031608091206040615060e01050309010603020901060c0507150203090607170301090902040509 79
    0x280804030342d203501104100088080f070140308204003594130b80c24000b40c04030360b641409803000c418524640d280c108584190382c040243c441070b81064038001c41d809814420580f1169901040c064106e0b441c540c1c01d4815203035085925640e903104821240c540340c84540d6550601a20070028604139001880210700400c10307a030000780307148900c2e03501110800c1000c8001d030007100111a00c00314808252405180441d6560912040400e04916110240c0072641090aa130005405a00036803142c0c180681080c4100450102c0100303240003520b00c1a10b15a140c20395050018a0000d849114106075a020320200000c00a0511840c85200c425200c4040701c80e01d00900145020500b0300321604000d004004100a05403d4020901442e80104408415a15481c00a04086502000380c601e03201d402c10024004000400d4120014113a42c081d51078070645500f4410980e001000484154144285240701c5c4410000510301030140c8490101b0908802d004100640d0400340502e0302c82d4002d111 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 123744757 1250 123743507 123743509
    0x703151707080f120309030904060905011d071d0f060c0102040602120f03010b070201050705120306031603050a030e0a0e090102070201260f15131401060f2712030f0e040902 76
    0x1e608941301c0d14140d40c480c1c0d01d555240800b030644c0070f911b090342c1d0080d04114001c41c100341139411413030603602c071a0038680011910140c200c07030701c1d5010b0760544003003a9032042ea000d41c5000f10014110003000903010514540c1d102d4041402a40089100d020a96020074148001941480130040880c500d0008900308001501c01403124031041c42519603060300061202d0440e4020003d0b01c20f241d0304003058aa0047c5868a40785560380110b40240c881d0299441e000350108401410b501074075003020062840c1c03480c81d5010b03200c074021220078070f5100c001860f00142842000d0311081c441c2040d9000581c54200304d1001415102c64001200345400082c500048506000d41c00d40354003482d100d00e5101580c07141d0014091040b10502c255410008003490650f0b19103103034008241d403000703503984030b8581d0ba40d84004540c40d0101000301c20005024151404070046100024441044101d403c84042c80ea2520700109001c4064400c80c08680808802070300590800440444007500340d5050021404a80c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 123746007 1250 123744757 123744763
    0x10b0303120703051003061401030b060d0b060409050109020a080f10021206040504170a0206010e10050d030f0306150f09080c0105041205070f0608010e010503150f0703151707080f 79
    0x42c0408100b41da154001500d96645c41512801180c00000030015510402651411050240001c0e1500903210012030700e03c0c200314003030b4a03021f9000301c0903449580b40e5908100181903a81070580d52036490f0804540942e0300d030080d4000410b1341c0b000900704180300300101070400c00d21404030100948140030500914210911159124004480000c0d0654841ca0044a00320101030403048051020070701070303040d41d00011a541030b1008680c2c05440e540c0c4040011070000d030700c1c2c0105604614001840b0700064007401c51390810800768180440c2c5035860b040c0c2c0b544000761542c44000081d00b0710003a8114150000c81800190484002401c07000001c10000703000c61050b0312511002418580505c01404000d002c5032001c1c10b01200303441d5140e50781c3c5100420304d407402c0c050780390342d141c1e0351000151610300090583d400003585072000300540d54519602c0c0d100140203020005141e2240640040c0e50030b000d410314090a0345650b44140103030381d030010501d46080394002100c42d5100c0344803030495035400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 123747257 1250 123746007 123746011
    0xf150314150f060118140913020d02060a0e030a030306031a010302090606070503070501020c070819031b02041808180d0b010b0f0d0f0204051008041502030a18110102010b030312 78
    0x400d03072402c0c09855040049841c145d4900d404044403210a20216072042c0d4401c1203c5982c1081b201c0c0d90550b10b07086a04001078000f404003d50101c900380f0b680d40182440c4001e00014403136410603031403026404002c07a0804e20600300440c0000c1d03841c0070610401203040c01811400004850000c41c40d030640d404580029070140a46100b03c1c0081582020800300b042183d500039440380c002e54840320070303030103007035030390f4450300400d26035020f003880742d110785c00302c1a04e03038151150140d60300085203844c542581800211481c060380c1054030f403030000c2d0b0105000b80070b070381e451403081c014295070f401507115030180c4451030785989200300400040000440c0909050a0550b0302e0b084940ea59011941c102e00040d10070460700c0c10100b070a1009880001d0591f90240c011100b05950700c9011503d002c100321104402150300070120450307a040c00758481101c0d030155520111048001901c640e0043d1a138064136030802c01100c00302c0d00043c5040140d40c1c28014810101d00c01d030b00450400369a8a1003940311800 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 123748507 1250 123747257 123747271
    0x1f020c0c01140d1401030b0f0405100207170711090c0c280b0c0901120605060a0c1401090602030415060b0a050306031c17060603070c0b0a0f15031415 66
    0x384107000a41000385801c0303d0103466101820050710101100c40710010500340702c103803840c0b4030f1480010350940e900c840280c49a580503000d03008401030b42c11400000d400954042c0c9071041c006296041c1c40042c0b10003082446c1c0220301b00a1241021010080601401004038000e9581481001c040b00800200303c4030501c1d60340704400b00b40105584080c030f2407802502c0070345201a01014040c103103140b03c000b8100b00100307a85000e044110b924070001901e405103d1181c2141c01040f4990000740700d00b0f00084030500c5a259142d004485844680c01c0da811044240c07581ea5001040c0410070074004400000da1111020a1219900c0d011045000d40907128500e800e0142c0040001c001e66018021518400c0c411500076800000b4030b40c0040071020b181903100c2c0840d441d500850014904501a207203d541f0541d1752540c4000541d98a01404c400500005126503e0b114a40301c01182c0b8003070101c0135040511480c100610358100181c165201c202c004c5041e42244000e1032810071080300480d40056 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 123749757 1250 123748507 123748517
    0x334050405090a09050303040804090e010203060d03050d0905012d05070206010302060f0d020f0705010e06010305071205030c0a1202070b030f130201020f010504031e050c2d07081f020c0c01 83
    0x3d07030b1030700d8800038114100300100580400020401013001d610054816a120f6030001c1100b0341c41244854201e1005031101a4481e1220645c40c00080c40359004085512080c580481e6000b41950303214292aa0b100c038845070380d11426403000040071079190003038203075101000074491800c01d10030103034845c1c1041c040030b030040303200143e2141070b12450412200401c124120840d5900305216481c032054000c210308490950a1030280302c6004000038806060300c0e000380151680c1ca1400384110810300c02c98104481c0342c001404075038a007100501c040100f080c06551204010005504020b04100481d042072016410500038420002d4084012603031203110540d0221300381c000c60005038581880a59026180c1d800c000c01c10040513404141151000000301901401043d40c08056400740104100a221540030980401f8543c0700d45e1840c10300b140040480e42c20703810540c2a042e043c45016081321307605a000c0520b041c0c610a0751040d09942c0d200040046003400f419010301c2d62903030803164480307040207 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 123751007 1250 123749757 123749761
    0x15080c0d0905070e0f01030b010b1c0e0a0507080f0d09180b13020d06081212041506050d05030418020a051206041104030b04050c0301020306010504032402033405040509 74
    0x481d04003c2807004d0258074100c81c00c249001c40303041d021200700740401c031050b8004900005900c810001a01c0710540700142c4610110903840a410040815980c0b150a9200300691040483d200340328000241c02000c0180014004222080349850351082c0802d042140c0781034104132030646440e407081010840040441d201440000007a070b40c5184102e8005424400520002c5208540d4030100481e2001c4055072030798892802d03185103600482d41c6420320003407a40005800211041c1c50700030790080503003000501c0c0e80c982d0b01044544828140885045d4070004050004401015421900d894110030640c68846000c100a0040c0590040400303440250300104099542d150440118583c01400d12611995a030030200f51044098a041c0c2d414012402d50000034281030080703038800c0c0d5068595a103058590740c0c4103100a07108003117007141c01c80d40007410450b090b994002940140c900b2500c045480911960406034003602c0b0010003500c0209003443c0041a81000c156000c0f00d104680f001040e07 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 123752257 1250 123751007 123751013
    0x309120d0c0b0c190c060e030f181206130c14100507030e1c060e0703020901051003020904050403090e060a0f06050f04050d050f06011a04030f0201110106060915080c0d09 75
    0x140c003074501c00c001901c154130161200190300c460004c0c42c0c43d0146a003030042c2c4a50589141d10391003090503204484504008400c05080010000c01f00342030043c0c03a1407681010512113038204602640c240c106910024000c2042c810709140301d0f809000d07a0120210390750384035000100041200301c800d40602030003041240c24940038010300003082c81c0142196941d05c48905043c040819070303c2084409078a41502400e8051000a900c4180d07036001d0040d100590a02040068081403600c0100426808000040039030712140142c500030303842a01d0751481d1508100030400f0700038000340154040c181d5004100300c10324044074400c08550060624541d20340300003140c2d80f0b00780f00300d800c410b4100c02c05000010402c10009031100d84e1046040980751070341d8850001c6680300c141e29180c0c900815090000b403000ca14a0410700201e20710506000003107050900c007550a580a90344000c01040c001a41002006c1c55084c0b0342404142e40c3c07801d80380901d080036959206004544941054555896000d010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 123753507 1250 123752257 123752281
    0xe07050306040929010501260106031508010c0503011a0a02060a0b0307080f03130509010f090c0504030204051311040c020601030b04020d0503030408030709050609030604030f030b0a080309120d0c0b 87
    0x3001308411a58110b0000d89103001c50149000c1c4203480c0003420301016501641484401c0c02d24040341c55052294991030040210060701e04500040301c3c251802d000003c54400c2403042180f0168961101d0791a985000d030a84080e2400c1c0c0000701d410b038400c00058038004d6012800c103502130740c190784c0010001030680100346444400d40004a0310700c6540520032504e03000002030020304401036541820f880e2071310288071110b1000c0c070410300400d03038841c820f1001c100a500004e0700340000d0701c0c0c01030903d5170700d40000c2c007a2001034035400a1042d1504190007803003050048a21020000d50b0140004070300360500039070b500d82c14030000c1c1c40050460046011961f5111494040b240c2010450f501c9003414144107a8035881034491601181010300000b403503040070000d803990032000401921040d038030340d00c0a030381c02c014640d6050101030351941c0f446d015030358200030040505142001141c44550f818280020700400980700c0320282e200c03403c007940c0b0b04d81c040307024040d40703910500030100b94491310ba010720 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 123754757 1250 123753507 123753533
    0x1812081e0c0708010506040b0301060b03040b1b0315010305010602011a120102070b09030c15070c030f020a05100f0506060405030a080c01140414160605090d170304050109020a0e070503060409 84
    0x107140100000061060015080f1502801045804004101c80700c020942210814400c1c200d8405080c000180814044444c45a004050380e8100c501e031680241d1100c2e06034012641a00001c0744800001c0082d6814816180503221a000070030211070050400703031702025003540310341c07180c07071a12003002d91400e007901135034001da80c030124140940c20400e28040d129003203986108924480c031002c80700d0010300c21009501500c002d0700c4d0840c014034151421218140d0f149141001c0d4800d959500001a600304084000c480d2410f1001031010601500c001c1683c20103000c09100d0b40040c0014401d90342d010031200162644609903603503039043c58405a000d0200410401a818684c40c200000c1c0000c1211081804540c00b0607601030007614188444648102c2c0910b2000440501c40b54040c0e0a010000c0581c1078054011207810502640c41e880c10365208882c111303010303510b48ad510750460030140f02d081d001c1c24900e11030981c0703454851001030a81c00010a03944c03240c0c1d196440310081c4450250248 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 123756007 1250 123754757 123754777
    0x1090204050c0405240a0c050f10050901060504020319020c1f06030b0a1b08100f030507050103060b180d0311030a0905090901150e090102191812081e 66
    0x4040742c42e11208024064015106050049910807076088510080c2449902c042c01070035051814082006000c598844640c3d000301c0c1d142c8910740050380d002008004200d00400c0000001c40e035031800711581400e448450740003034007c2d4014424400000c1404d1b10100400c044041e005031684520ba0f50249850301d001d9440220340300805580850307411315003210013628000c48408036a5107541c9201c0c407c0b00d201e06d0418a400001d98074120720030744a05e1129030000c0c0480b070144801078890003603404d0042d05910881d03842d4002c4004110650b0103008850061840e91006800d00940c4070003044091810101c0074400c4034642030000405016161820031810014122500c1e01c0c004180640503442a010b002c0c805ea183e5000140c1151050045446520030f41c80c1004000345007101c0110b0408014003260360b0f55400703010319000048070820b180f00c00141ea940d044445041c080d10030b0749642e6940c10802c1e010320114074240c0070807514402c80e0159000701548020340c0038000c400360810b01401280d4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 123757257 1250 123756007 123756011
    0x2060705190f030822020d02150a030b0319150e10110a03201602030a0219060e0d0b070c0201021501060f11060403021c09030b0408030117071a090301090204 69
    0x40710034401404081284240b09845491454603402c5a80704111003034a0035800c0c60030081640300050802c10841d055261014044251003c074011b84400543c0082c0302000000750794415001951804202c0c04034039600c484000c010009840d15504500c8900e0014900703c6034075051030200c02d0030304001240c050a91214108410110083e0481e1030307034440000400000e040040c113209420000c1c6005c94254501d072200f0707183c0400d05008075590082502d050f603050085084510158484201c886a032510114286ea050b504100c409480440a2482103009088800501c3e0009003400031458001e4454201000070101300c2c0300407807a003805030728815602003080000217101500222000817030600c603155922102c000201c40d5a607010121070280c0103900c044c0c07540c0c04c000000400c901810240389482e007202512900c800500075410359044450090000040020140e8200b100744000c08031405018403d00c2c015001c181c010800700c0d5000c41150000f00c0c02d85942e800d41c410141150301070f1003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 123758507 1250 123757257 123757303
    0x50114150c21070b06120c010c0203030702040f060e07050306060a11030702210c06160b1f1203080f100302060a0210050108011a0109060206010306050a0603060f050910060302090402060705 83
    0x2140b4550740081d4801c483c21a80c031008501c0d81c1c40c0028410442011510042c00c0039004000115480c0907060810303078050200308040000360f152401a402c1d498861038010600c640351518125003540700500d180304001040c01030001030b9503000c00700e5200c5002460204141c3c07d00380c0d229411880381710b00080d80111031b6542d001d00c3e988140720041820ba981c500380c1c0c4600c0024824048144940799a8107040d40b5102c3c0201d000500301d80b2000d8100c101c0441c1c030030100162120310440105103030444c140c49001060320001701680005583e80c090b2265000400600b0076014801f5000309a001c006d1181c1c078042076204079035100304880c90781149010428080d65070754000e254000c040c1140d5402e042032041c01c03040d045501644451007245c62560003400b09178078644848004180280040751410f89400000021981e02d003c2c20b4800120210001418104582510324241d601881c0c00021414682c0c00c1001d41e0711556060f50068041d14500d98511346858498284510184148a14625000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 123759757 1250 123758507 123758563
    0x1030612050a0210020a0b0a05090a0c0305070e0106090506030a110f04030f0c0602030304030203030a0e0c0a060f080603061b030a0b0d0b0709060e0a050d020103090b1306050114150c 80
    0x6070381000c1c10f009590198041c144000105d8684400000103800c058070b510202c0d19440a0341c0c00180d101000c0c206451041c1c0b0765a03140e40156200e41d1050307a084d804184180400300f50100381c4c81c0180700909005210f41d18010204e074240c00001c0c2007101d081d0392242101c007103d401004440c1780740840c1041c95a5a5203a10b0201903000080c41c027541c0980d0341d0000441d103140000116400f0710713010f07002542942c0d16840c1c1d14000d403449941c5202c25015030030561256071204030102c0050305040d121002c0004980c04020040800142800e1190f440082070080b07a02406400040600300b81c803200e5565a11030345440003401180241e2604151010307007540c107024021140c0d900540155640c00c52540d5a510b0454003800c2445200364009015001000146082c020003801c0e05c2c818100420310340001e460b07060101500312010812511190660307020480b0512900c0d025041085810100b102000003290792011030102d00d13040310b600000c40503001102008080702d10341214041048100c0d01c02 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 123761007 1250 123759757 123759763
    0xc0b06010c170d0e0102181c050601060509040b0316091a0927070501082d15010f050c0303060616050102030c0703120c0f0f1403180c01022404020103061205 69
    0x20898041d0307480c1844000b13500c1010b0084600d5080d41201ea5490307030700c4007010080014190311030420015070b58400c0c00f0000c0d0041c040d081c004d200c1c1d5240e594075003003003a0501043c0e034003108100703100383c001000140c544559884403200f03890051200282601c1000b40d241404003c241d4210b51000241c420010208214140d00644100c0001d0712003005049002050b81c40c0c1842c02083e000c50301e07000000340c0c00480c0380241d01651003045030350b40484c107140b8500c61100070144c0b100c8a450320f0781504105196000448820700703d043c2e18005240c421160b11013500c80c080071301303403a200d0080000c007800001e64042085501c01c1e0403400071076a03802d001000c075000341d0004200300c01040c0c0c0521080d01c0380c55240305082100c0d1554032801d08944501d04100d0f4540a464440c00c1400110060761642040e0301019502c00e00701d04404040044c02003c03c607260810b6020f20504550240081c100b03c14030f0710f0fa10f030700d910b14018000c0b44661100e01c0141d002c1c00300ea070494201e42600c100703c10b0a00c4000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 123762257 1250 123761007 123761017
    0x1202070f17040b1c09080c0f21040b0a020718052401050702010c02030106090e07170d05180a0b0d0203040c050405011a031308070305030f0604020403030c0b06010c17 73
    0x40e241200c894403062032410300a00943c495224501e900b402905440340040c1c4031001c000c0c2102c44006840c5e0308580e2403201503006070001080c103038404101c030150240104050003400b074500540c10030600c040351403500c40c1d200714054002c10003404101294400e00030030804018280341c3d0041c0d200c543c142c240d000011306049518840381010301d680340c01c00b4440500305c2c0500e01c0041c3d50389403411800e600107540d0440c25000407a01507580b180005001205440b035440a0440e80028003d414500500b20140c007070103120061b519040810101107603030b00002101c41c03d454000d00d10f060004910005541000540d00500c003c03240001c424019452542c021803240744a000c841550316100c000380000c9071402d015080c50407030350392040126124018080c540c0141d5403540c00210400a5851900343e40040c102100420000f0050000440161054551001c0c003500d08500342031943e2801082d001c51002c019112400101c08901180d200d0300601003d103070400c0e140480d0741110840412907070b00c1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 123763507 1250 123762257 123762263
    0xb06011812080c0d050307090f0302060304060506210f010e0c0f090c070804060309140d0203040902070807020a1212021b0603040302101a1e130e150406050f0105030a031d011202070f 80
    0xc8c0200455403100d404041419a038015101c28116074403562484000c003000343ca502d60000d0849003020074510f817269541c1d03044d425100035100c4400e0030f1180d9401d450160002101c40d411452080400e521200c100070502e010444407003e041d280c108202c801d5216054000e01090303000100880c8054040d0020111644503040d0842d042460405580e1a008518200401a001004100000b0113242c0241c0f0f1800d001d90142882d05046900050712016240d04c00895020f40000d110305102200340308008060f500c0c005050484000c001d06000541448901ca00c14900400403505140c8200108442044001810480c58480c1d1001e4101c25021316031161044e00c560040500c00450002100c014400c058072840304010741054035030140c55401940c03040ca10030100b5041e82140310f0340e03029024038000d010006013410150074070440d500701604420f0080c2c6c001421880004d50003480d504214190b218210303400a00c8100480303181032241e404028041c00451200240420b6240580130588 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 123764757 1250 123763507 123763517
    0xc09041b0f031205030f070818150105040501080607021c030608010c0216060e0a150302070c0603090c090605060d090606080a0b10080106031502070302070e130b06011812080c0d050307 81
    0x41041184c05100031a01c04159490340404124054004c0d19000d400601a840b54007070741081900080c40e003089480c507170120030a200d0041249040074400e40f400751501401820b4580381c0040040d503102c041d4604a9400140c52105280c468408e40c001c20103450079000070301a2145041c00255a805c8185681c6200d40d01c102001990602a01601c041500c0c0230306141e180e00c3c82c090007501011b03900440201070640030440e1000080741400c80201900c1e07140c50014040800b4101000c2c035040c590004000c0790f06e0034074140015074448003504c030302042000003c40d940e0303024034040014060b242e02c502054420043c1d54410414001f20300c91081070301a00036000c0a541c1c0e2500c6090303400900c0054646074000358100c0070b50605070010540309010303004407061950741d901030b041000011250305020076408441103081101c9003001da41c0180091811205c4d0741d40d904040c80c0806a0303881044603446003140f0603000c00c58210156822250070a0564821101c0c80380e000e00642e00c00c90703050380019 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 123766007 1250 123764757 123764783
    0x504051501020d0801081518030408030a030b030a0b040b041103030a02011d0105070816020c090411030c010309020609042007030e0307080f06011404150b0a020d0801080c09041b0f03 80
    0x90f1046920328100c403000700007000824141046010940e102130484070500070348d0001164401c904000800040000720015556180303030304c0c402021134150b00d14252003500621f440401041400d000c41e03400a42003140e004083d1140c1c0f80960300300b034000c0c104c15094040411110003144d0190b2124250030400e1024042e00d00003201c2c001e080715800c0311460046981e04002c100101c0341072505c0c19114403030780100c80b401d4000c20001030100358126001c5421200c00650032029080510030202004407e08051040d641140d000582a020345403442d4062966103640440c0b02e903a40c4001140c1212100c0c106655840c02d040003800541e81d030340941d01038411404005440174002845055a10780c940103420244d08200c41814481c414460304d560013611444074400300340320041d1146c000c00240d00003664031240c20350040d081c1a40e0223401010f20440100410a104000c58525540c140071500c0c2c000b40d07030f80c3d49821460f29180c20510541d40e0502c10010a2815113200c012090b64094000440d184e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 123767257 1250 123766007 123766033
    0x213050306010f14180c03070f031803180e0c2d03061e03100912022a01020102071b0509010902030903070308090f03280f050703080c04050405150102 66
    0x201c0c400e115041c14200c20319410811104885008110070600400c6032003e829400034050f82e0380000d98560300c907484000305000e003880e00205680303c50101c0303040900440a01c0b45190080c103a4030720015051007400e140c1410351075042c24407000501451940350300c5500f4050400003881d0440402c0c01c105021240d03020751642d1a213210304000c09100c11949185958207000e015140441400000448081c2104600260360900409081e07950103007001620100b0390030709404004800d8440c0f819900070f025a80e0581a054903a06101c94480800840350180180104d0091141d120007600c40180e4558400b01d1041d01c00b1600120f6004864030703a03c503601d403185c0208a2000340c8000d001c2d03074010081103002074007482010b9400441d02e025240c038603aa0610150843e031140384a00c82001c0c04061580060384c6e02c02c1d40c001980c2031840c080218011210010303085103e42980941800303c88000100061a80c2003114058400900188101d04026500442d1a00c890a60902500444ca0500c1c94 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 123768507 1250 123767257 123767263
    0x203070e04020319020a0b0403151a0303040620030703050408060106021204180617010b011d180c04120b09010b0108060a050616080705070302010807050c0c040e0a06050a02130503 79
    0x6590000c002d801c6150400201d86445032440d03600705d0300100e030f41b200040e6017014000a80700550054009441c9416a030307544101316002e040050b44100415020301e80e05443c00000d4400351900c6041c144910041410180b05040c581c1c103075030000e8400003d42d84101588200500115003211007111016601c1d0340d81684c91340c0c81921020700c2c805041c030013001400d900701445005008101f1000a0381da0703c9414806426030f00114401680e9101d800c0e055095034008950481039403c041000c8003885804002605100383c0b104041c01000c201010401c17400741a421074000307100400740d215685a50b8500018111000c80d00319001e0b5182420250482d4003560100c1e02c501001028403a003079040c0020001660804c901d5801105526030071000000d00800091042d030b800f80004041e014070754800101500001404030381041000e111001c0c03c1940005e403d900048101d4020901031850b084051412110309000b07000503007440c040c00042046075000b800b411030068600303602241c9500034140e0b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 123769757 1250 123768507 123768511
    0x118140606010c170d0c0503011a041a0703021e07061b0f03120f11250506010317070219080d02010204030201120b1c14010f0c1d03030c1006030203070e 67
    0x1000c10104070b810000200413060048500e491005035a0401803c4000300701101c440c60071070400300c1c20010060100c005882d804c8107800c8040c0f940c00385040d0803e03070031404001d1642d810007650b8601240400c01c160007445911114036910f01c0c2c0e89142040350002594510f401d00c9204003049050910118111040111181b5290001c040c000501600d94044520081072901a500c5690b03a4000325481d03c000e024002803c03240c0c9000545550200452412518200745c80d001d41c7d003c6010341e200000c4c00426901e04403034200a000c2510b800c0700070520541c0c41028070007540100d40c00300141d1030500075804202503d0804e4119103400d010f0b2007045c1d00f01c1c400c600000e030108641d440304010000c0e0b40d4020500b4281c0192807402400c0345040c861000141c01102102c003040c0c465003038180c0400901c120420810200d10910100e41450005008956084400c0040340c981c8400303210380361030030130440f0b03000307880e85003100c43e0050060040002854140000ca10a003c5c0210000c0c100c0c0c04152524 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 123771007 1250 123769757 123769759
    0x110d080a1d06340503120705040e041704030210020d02010605120a060e030d020a02030a020c0a0e04030818030d0614040606140310030203030304060b011b080d0207060e0118140606 79
    0x3a01d010751048800003030b840f440703070000d210301c1c03000182004024111002d520568030540003513031503a03800003600e04015002071840b001c00000b44020000803070580000f80d0803617003100ba5540401014882d020030744c45140c01c040c6d04441a000070100c06940003881e41c2d8000c40360341c02081540e8850081103214100305081c00c02c03d9210081070350120b10a03034044140c2d1240300c01202d14110407001000180c1c0c21007407030f11025030008205e2a0805405010258211600301c80e100702c01401d10000d1041801e000e0005000c01500000258101c00c8014428071404041d004407501d030400084030740068503090286551401500402080741d00b403d0103400c0980e110303130f00e410320421071101c072003840d5400040c104200e02014803400009070320140006e42c0518000d0401052145142c0009813a2801d501e401900d000074015400b00850301e0710054074004107e030300c80076a42d1952424920f0292082e42118251540b034640c000d202c1408410900e409107101e00016102c1c511501c1501381c4880b0101c4a107 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 123772257 1250 123771007 123771019
    0x1a060111030a05090a030b0a0608070806010302180a020702090108031305041a010e0a03060f051b07020f13110d0207050609061b070819110c0d050705040504110d080a1d 74
    0x6070b9080c1d0044001c0d02032184080d240d11703207040c0e40e40c640312501c01080da020b40c2181c0d9074010501c1035010500c40040503240c100001d22030f075451603020078200040075050800046103040826400d4101d6011110300301c0d001007100c21696150660241c4903804a4400790148005650005050030140100300c03034604030f42001441000f81d10011340303021003d5148950301610600002c0005101b502c42c408403c5c0b50400c00080320301d0f003020b10a8141020208445403d42c0a01030f2200503960000041e02c88201616107040f80c041c2c00d10003101605051202c03a58885003c1004042e8910360b80c007414030325010f0000c41300303541c40c0e4090311074985205441054446140650480d41c1000c4a0001c0161912440c0d0945ca09090703410314801c0c0800a44094000500010920f40c2d108810022000c40030780031a180c4c1c1b03031a0300c150340b5103965a07258032880c2d0041c2d48603030002d400c0c440e030305914441480c00030b4003a4600c0503c501d00711320a0f6000c401400082080584416105064110b0388180783d60007a0030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 123773507 1250 123772257 123772267
    0x5100c140306101103030c03071407150b0102120a0503040b060f0315040813140f100912020a030203070b0301061404031e02031006181a01020a030c0501020d091a06011103 75
    0x34461140c203840b0283d001d00c03041046060001034100000d601c141c8440071a152030303081c076010081c50300650000d003411110040c0704082c04610300c0344944c03511450103034000424040480060b030500b52200412825000b0100d0001c100c69000700065100750f00c91240410295510300421082d52a00c00080c0d4041c0c2c07240a40d00641150b003c031142d0864015091241026144505481c01e85020b4201c40d661454102075040a8105401c806414680c00c03525280310b900d00b40c3c0014080807040c446e00300f050366441d48180545d1240142d900185401600391045039441c3c8181d009264028803801c000640e4417040c00c09070740c8203441030740c0560b03a09c18a0070051407103502c2100303201751800380c1c266410700800c2c09036401090179100703000091903040c4090714007054030503c0a04840315a0380c100c61080181014589607a070106001d50701e03540c58103100c140414582130441c020300130181400c030001d150851802c140108000229591032881e88004e5195440c000116203003d501c031407800841d030043c88 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 123774757 1250 123773507 123773509
    0x21203040c060521010b040501080a0c081302060f0301030602090a17190201030f06060305090d021c0f0c080a02060402040b010e030d0806030c130c090510020d2a05100c140306 77
    0x80180404c906995007407460200c4c0d1a11000001c83c20391200c10103e000060800c0f443d40c010298a0388508059010401a040301f540a882c1020051031058400303210b206174021513a842054032031407180c803804070751a5a11707450060f00a50059105500c1850900000100c01c031070005a0b401c50700308000907181640720200c0590500c1e000f400c040b0306041c0c8a684007a4204030612400d0020300456601080074141070100038102140c40030b000702150041c119031100940f03074545106507005180f0705060300005400f4100c860100700d80005150003000982c90308025400130b0481d004034022101082103040700b00040d83c540c003918640c40c0d09030b00100741038104035002c0c03900d55138412009010b844140c00010001091080e040064055059940050b403035000d40c00000200607200c19600300c000c512002001a5a880b481e485940401070312240c42c6c103c42c002045a501c9841c115046e00c0300400003450311984407414034081030842031800c0c012498880c4112002c0644142e0b206d00300b0b00d1919044 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 123776007 1250 123774757 123774767
    0x10803040306020f0423010f143a0c0807080708150109120506150f0303030c0705011401031112010501061b020f03071206060e010515030714041203021203040c06 71
    0x1a07130f00c0d0501d13040c40005148144980c4811141c1d030319501700308082c081240090140301c041503800040042c443c4411a40c1d40354402182e030100c0700314040b4100c40d0138860311151074015591070341d01565041c60001c140740f00d19802c161442203840c0c0b110f00041e620058100c5101c642115880c000a081801144180b0800511003102000615000c4803040d06c580c00610507050b03c0d0760071034503603020341300f089100f0030481c8416403050800c0742c49000491080c4000b95403404007410a0b50f0b1041c0014882e070800009601400751058036222400c00e07507950b41003100340f02e01d00a15041c0116407040c42c603441d0701018030403c0d050f0740458990406066a03100d0007003500d5a205012a0002e10291400840b0b54040201e000140112181f1f0501d0000c98039001c2c058611a52080b440000f0400040c48550b03127020302420800031841c031650702d0b565640710882d00b131082d000011248940009021410050110f61850800d019800300c0b45480c06000e0200e129100456015000e84183d00c0306020640c815 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 123777257 1250 123776007 123776017
    0x3070906030b0d12020c01020606061303120903061b08060409021f230c0d08070f030504080d0e030903070515030406150b04090c080903031b030c070f05070501080c0301080304030602 80
    0x20f4800c0c4019142c2c3da8a0b1100c00075007414120260707000f0407895215607810091203501c80429a0154241048500318910a45131808014245824000030010b017500c02c0704454001c5401c614240301c203441c44c038544c42c06c0802c41c80b8003100282c58480003401e80d0520f401401300056000d4200c810700380d080000d0100454201d5440410800020981580084a002c40d50400c0000c41c00307160b51400746020240c640a2019030110502402004000c1c0b0300d03411135040382c007030314503428085450343d51407400a50b10f108800c40390000c0c525000080c1e5050b4000001b52200761000d90841c3c0501c0d4982040003075014540096410b440c8d0b0410001340081c2032a00060940f0310150744d100215038460308000141d03040b0780c000c0ca00013940c44006500103a030003040310f6000600d07580614990f04103401c020394030000200a0619144001000c10041c0b1500801c40d0036064120141400801a038580240c0b58501803103a540050280c0d0302050200e205201100c0c12100b281004520b020321b15603c800194002c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 123778507 1250 123777257 123777259
    0x1b03070309080301080f0c0109060f0507060e06040302060402091305030910020106030c030515180a021908030d0e010b0306060306130606030f05010c02010e030c03040501033908070503070906030b 86
    0x4808076540020040e5003c2c0d406000c1140c05410508041d4601625206910030802e040180340d0700c007000341136084501010b04013041d150141c0c0d540041d05104000d800f00440d021401c1c4a032400f00800e140c2d01281ca68001d5108960510560321402e588110491042001500d1508200311603911446d00c0122981100c0880c0008141540e807504e4291100e14580e1099170181c010880745154450200c081c25880103603180c00c0c001ba105501c100b40e40c1c0704030028009005074507a259808441c2070f0001404e0090030400e040302ea440c00c0303228110000d048540b90002080d800e1085990041c540400d146200d044050003d0140e43e540c000c3c0d02071051100328054940c0b43d5940340100c00b00e1541c00601d00c4050013400041602104050000d08680c4d1111005215804c284018002d01001004a9084500034600820007290405a411040700c0700740c2e40c100c5004a4007030054148203200c01715560000161035041c41c90752440700940d6540300031035503200000c0e042d1000340b1855000303500070404818 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 123779757 1250 123778507 123778511
    0x708190c0905090a141506060d0f0e0106050a0504020a171012060c110703020a0510050903010203040318060c02010509090c070b0f060a0b070b040b090a17031e1b030703 74
    0x2a584002070129682940c10164036040008207800340501340c10f0741414031140800400e190780c6650001201038001401141c844d01c00001d000d002001d150f04615030b02e002492041058500c1c2c1150207009009500c2058042c0c0d03039895000076640751034821303950505942e842d07185003602c0e180300309514510000d02140c1f0005000902007a8181070191102d8018458a0300054041d2607260251a54111045070784442c0c0c003643e414801030711101082000c499080d01e071b5183e02c83e2501c10a4546d40120b251007509503201000b08000c0c164070011a00343c0d40b11404110080d00d0f2a4581111003c074480e034082e0102d0b10421500329203040c44078900d6801281400d89078100000d0b0740c1c9502d1a0701066815890100032842840440d180550780540144880321042c0e25000559a840d0032205008001a1107a800c6000164600005000d10f01049510440d9401e46100000011640d9001036072400040000704c0081a0002d414144240c0985103402c040e00f00c130348a07041c04c0042644018107030802c140d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 123781007 1250 123779757 123779759
    0xc120115090c1206080c0f0402130303030e010905160504061703070305070f05011d101e09050705030303100608010b0a0e09220602030613020906030106030b010203130315050106020708190c 83
    0x520381d8403403030024120300ea000d05002642d14040041c0887c50b903050520441c0b0400c0000b540c6103030070143d00100c030380c1814003164460081e82c45600400e64030b40003800901070b089040b100414400b0f44482a036200b1501005403584405091000c905100c0c8112000c0d8410054072010034003c501400c4070030306c24200448044116a9400d0945200c0c1c0c8161500b0b5110102c140c0c0080001e0105030b600c400040410408118103c0c0040540d23a42418108041a03503000314009010f4240000c1c406800040d04482d581d081408124882d000644141c07800502d90308000709600da000310884100201554807800c80814400410582100140ca00b103441146c0e01c0542d101e1804000f107055816006110058403840d0100904c029107940b10702d540300a501c108540040b555500040e241518290300d07000502ca409040141d22b180319200014065940021002080107240d08072a00008000c050502c1940d0361810160fa42e13295600a01d0700d1504030710721440c036000002ca44000e0302ca0140d0f042d51989 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 123782257 1250 123781007 123781037
    0x180f0611040e0402031c09090209060408010207050607120c051207090504110406081308121302030105161706010207060f020a021009031a0103081602060d0e0c120115090c 75
    0x25074825405840e003010300004000a40c80c060142101100c40030440c50060043e921004018601500030189295400b08201c81161100003e50300908007500086649186905003d035132950220760341d00003d481042c40c4180e090440c02805021240c0e83c640701c2c00c1c01001c00d640d100705c3c840100401e041203980d0b280018290340728000c07170034060300f010711072562541841c4009140310001041040441019440f580020305030200725001c106020b00c09150680304c000c9000e011401007200079505600305400c7c09000c844c00c24040c03924000540360118520101c0d132042c2e016000480310075001d40c000d0241081250301070208481d2240640c41076034404400c5500203268900250320840000b00360920174010094070f04d11484050f20703007105083d825850f41d9500b1039039210b4a24058000c900d00207080c42152034203801c0d1180810125424800c2031309050f20a569004d00c041c3c4244901210481500310800600c11002a4400405544a054108290440a04080d001c10b0341040f606036540650 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 123783507 1250 123782257 123782291
    0x7050a021008100803030f07050f0705070320010305090c1309021201020a0f021b0103020a0507080c0f0607031404061d030a0203120109060e130819031d01180f06 71
    0x480340540702e44800d0300745000c40c03a09210b607a030080b046951040050094103002816a43e40c0038a4170b291480d41c64503c81018400380c00313812001442403050100100400078484440355070300b0100c0f20070012185840004500b40e41007969450f0254109091035082420100300e082c4840c5840407001c06c2c1050164041a02240c10300b0118503682d45c04940340c102580d101400b207050340e0861006000f01ca01c0101c9403c90706d10000521030616030300080030b01c40c00d8002c1054521181e00001426168880160080d48034000440071104500840c80040c2c0d94034083d205d018400070303c101c0f91081d0b6035240c1c0c0d01c6100601e621006000b0f4024180c07000c03003030880100700070300c50904698041c540392202101c40201000060b003110f5a400d04040c401c0c4012150f0010700f9900c02d42e40001002a04443c3c2020442e6220300d04170640d1240002c2e085888003500354208a0b0002e050199035010481030038801801c0340c40d041e1078400b502d040d4081c0b102c042108803a160f08041d00a050002c1e007000303c580c54000f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 123784757 1250 123783507 123783529
    0xe030c0a0305090a080c06040603050415050109141b16050f0316050f0a020112050a0b130207020918070303200102070f0b060a06080a1e050106230f0a030207050a02 72
    0x10000120300e0f01c14200b0f000b101004100ca0001800644107242c0041d03101d0185008201c00c01d655200001c060104203801e1031415140e40311f04021a5845007a81c0000c1e00c0c13410600e541040c15140814030440d981c0301501c0c035204601c6040c2e030408090200c0c4c2c3c0c01045146805442a2007642c080c1c2e2104076091000780b02c0800484e04000125072640740550070400f801c1e643c101140c004442e86405170340c01c644134010702c1d9100040000d0960711103207040000c0c11926420b5400140d90004203030058695801404403034003c40d1256410307a2143d80001d0940f0001030503541d140c000840800002e030140c000340001c0c0700d80c9808080254000c0d80b00b00d0880e0400354040e202c2c022003041c0542849581d00c000d81d000030050301d0150203a400c0a5010704000c20180600a00c542d44541310b1f299111400c114010303c0080302010722503940c0d038400007040b0302c6c0202e0f800310041014641560754194103000f20782c3c1101c6c1d040a001e0501501c2d030001c0d0b000713400c0514161030a000d041040383c0103a80c0c06044103 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 123786007 1250 123784757 123784763
    0x20304050306070e0907080702120d091202010f0b03120909040f060219090501050307083111040501060504030b0c0d020403050a0c090f060f0b0705120f030106030c0504030b04060e030c0a 82
    0x411022184c01000010000a8102130900c60700710184140707244c0c085036400118041030340b0039507140b0244103e00300600080e02c029098501d111130032a901e99043d0410508401c85c85d100744600e01c0e4a408050715031030302020940042e8410002087c1c1801c2101c0700640c4036000b00d6650070158615198501a6070001092001c02c000002001a119070403c00c5a03000d014280b034280c1c01c501e4030180180c10040c01820510700d104403011000000002810461075289011002c0e0038021134928007140d003400c1c0962094411803e010004c600703680b241e42500d0071079400400d5403400351510907190102da400b03c1030383e1801680070400840820310811002a40d54130605511401902d007101d103d00300c44112600e00341e46810480108000141c0c3c40c40745054034810100c0b0795032a0b03294070300540f820a103e102e0840041000c01c004aa40c1d1216010b076040f00c1058a040c001c03100807040c00c407040d11031404000d00c40001d400c00f090208015920441e400030a00701240e1800c0b070340c0c420341444e0203c614821 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 123787257 1250 123786007 123786017
    0x90f03042702030103021e0f041802040c020303040803041707020a060507030e010e030a060b0402070204180309090603080d0b0a171e010504051c1b0308060414010609090b0102030405030607 83
    0x5090104810560800c08050704011400c65065600140c1e0402280083c2c0e50208101c00c4a801b20740c0d1582c5141d0ba005600400410007a100c0852041d0380d122662402d0344524a85180a140c450010088921581c1d00c4420340c3d180d90381c0c942e40e48416140031050b07a0301508041c0480b030011b8442c2008a406070040d500c449803201480d150040c41c501089040c01d0402454099202d816100080c4811481e50310102c04100f040300d03000860000d0052000180d0702c1400c0a00000c0c40c60074a603070031a1071600a030740d02c003001501d030909001034891a1100400f4954200f10030604c0010a80c84400360070703c001c01c5c0901c07180c1e683d4043c00202034001c06070502d58010b001d102901c400459807000d003e020120090001d0703d015114503440c2d100709412280540110f034244074003580704258402054103071481d0aa80341d0313403e0800078031a071b6044403007500461920b8147c010702c00d0642c1c0c02504840d03080d0360b45000c0303e080400900c00b505800e10384034150b11040c4808a225a028041075101d404980d9075 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 123788507 1250 123787257 123787289
    0x9070c0c18020304050616120e0c04090b01080712080306040b060d0903030b0a1e0e0705040f0f090c0c212d0e0919020f0c03030f100f0617090f0304 65
    0x1700340e04080f006088620344c3c10248000126842d0441000c032180180c07454001850394003d400c1c9414081c1c4003840741e51103858104120200034803000c203a4181e44034a0200d030552034440d6000c030010f0001c0e030006040f4032000d0001955528068200403010400981041d0030001540341c0641618108481203000c030b5140c605624003400d101071210001c01c83c201220300440480101c1d03a4507200c807402104181e211410014120501400c226401000007411065426a451010112800c8030f4040d0307514150408811420141c42004110719070345c6c000c082c180d014903408050715601d4115081c40d2003401710781181c9089900420300d2a903d0b14442040c0414001780b00180109006404001070380300e06c0030b0710b00f808440c6d8500b0090003542281c50100503034420307140342c81c04220f0091491542061100004112003000603d8100e03000311090000c485103a40c54007002100a0351900403c4009009001c44140d422003c080c0700d60448240402e0380c0384410070b54a560309560140c1c0040203284c0c09014 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 123789757 1250 123788507 123788513
    0x90b0a0206090d0c0213020c011503060f0c0504210203011b170106081b03040609080301030f031404081002030c09101e020304150e0a0f12020a09020909070c0c18020304 74
    0x1018420407080c600d010b02142c401940000c0c002c0548804110b01b681e4045941b40d045d1609500c10541e40d440345407044c60b2a03941e0315002c00903003511103108184d01e0401d201c103d4400c0c0510305840070f0302d0400c0a041008094100d5130003000003400016a4959259000d402c2200010341d80303401c2ca0400ba607190202038200c6202c0e140e80603810783c041e1040104d0401000100b038110341c04030754014041006581d070f9448504221000e05814a00039082682c00000081003040003194124070501c030b6103400301c076110852000c8609006903c24038480b84c0021303810000500c00d81e4000c50344024100c0700c0c41d0402015802055200d0ba042c80c000707002ca06c221074042d14007090031840140d80d02162006510706400c00d4101c0080c000014602c405000312006802029501c502050014000c20040f2440541d924801c150005040302001c0e030041000000c04608004d150003100d55045014100c1451621003140c1140e500305031a0054402228484002c2036a510380c142e0800030380060305000d80c50703051500f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 123791007 1250 123789757 123789763
    0x50403140f1809060913140d080601030e07150507080d0e0102040302210a03080606070605070f030b0a030b04020607020307150215061c060f150906080c09070e0f01090b0a020609 78
    0x945850701c10103120007040310030740e40c00c0503180d8000c41950f1b01454600a616024114000380b4085814500484060001e61075203d83c03924481c031405da8060009404ca182401d48805003402050302c4449401c00e41d49420b4004c1c170060007001d100d000802e1510035110381402c2220481356894440c1d940002d402c0041d03141c4503090003503240081d03400307020070809000c00c0d0350344145a140090910411a0000301d2075aa00002e030340350180c0042d002d07c485d00d449000200340340380d1440e15902091920440c54198101042094152940f214222285465907020060300790400385040b40c0c103101e502c0e400b0518401d00d41d00f0b26403148181d0001c010022804609489180340141440d0003142c02c0400c0366074010608003080052600301100007201c8025440c14400741408182000440c2c0361482c0c00510b00801c0d6200c0c0080300d6071002503170091448a000c0100d5030b0800c0e2050b000042003850725040520342000b1000f0200f40505055690b1580e5080b92100364202041610140e0030030b10410203400014 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 123792257 1250 123791007 123791047
    0x913020d02041a0f09010e01050f0d05070809070b0301051e130203011a09030c01030c020102190c05010510060804080c010204030f061407050c0307060b040b0303070c091109060a03050403140f 84
    0x19105503040044c800c51075645070051003c40750400008440018440c2d015404803407000000f002007030307a103814031401310000d40010381e800000510843d0000300444000f02d950320030394009490707a038a0751740703018104007900c90091425902805c0520414120360790f480c03140e410018002d5000340c7c4035031400c0e000d04008150743c440d00b00d00312002c005e21000c1c0e54000c03848076904107003403d0000b55a81780a00413402400b07003901c403102a1000c0c03500154900d400072191b0700351600c100020300241d91004007841c009042c620480c00411512004200001c01d8500a811103081e200001824a0395030313154001440500803045e03c946540b6020070351a046080d40492f8008014105a840c0202074800c4503a64812684081c00c0a07603610803005459841ea04003980c480e070001c0481c1c0c3c50310b0aa0130000f1415080e40700c0c600219150120b4206003142d100c0c01c0e14190340c001070600b07040040d010410b80141c64010411420001170b404c00c0035611410b9005048e0b690040038100b07071940c219040107a80440c038 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 123793507 1250 123792257 123792299
    0x1005030d050301031209150207081b01230708040b09010f02060402090619050d0302010507020d02010504031715040c03020406030e010605131d010e15010b0a0210020913020d0204 78
    0x1248003000c049580000c1140d0440c0e500004a4462a410180c12910401290050801000002d600a1049034001b646d50207a41c000d00c16220f80840040c0414210109461207074007180c0a110300d101e143e06c1c0503648254804140c0b40640c41c203d02e07642c0710b4025900c9504140d50001c0003061b401c18959222080e00c442415900003886641041c0d000144404d0004003882d10801002c420a40300348491300650b001084d0140082c020000c03c4d14010b80680f90441c4e903c0c3c018410b10040211140c8140110360095030180c41c2c40329070403035950b207024000b1801032131075111851403034290109858a1190300b402d43c110f582c0040e103d9081042c01800c0d1003072410014500e030706029051089680b1004c80c03404451201900003612101001c1c1ca115900d031200384c4100d55440e080345c000382620081101c580a820300001802c1c103a0702d0f0108004030f80100e001450050b8881410b8620b45125580108510f100c02071056880d07501214418040c1e911551040e8110354005c00e0400903010340c1c0011050f9105 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 123794757 1250 123793507 123793513
    0x80f070f1104020c1e0708120301051f080f0a1d0f16060801260304090915050c07060b0a120507090c02010506031f06091103040c0501050a0c0303111b06100503 70
    0x88040d44950792150200c00280c5c441181c483d41c424003860400826006024503400d6070141d040c1012080030340e8100348512070181003210015010744401c821a80d8000d0300036180c0074040d0f01d6940d0740300c00c00380004156802c899070314440c000c200101c040050510b07004600c003c0074030400381d01400d0f05261441031641d02c2c5882c000401c0c02031f0f503000f10640741580e1048a21290340880d0941400e45051030403c40601404001008a161003503600807481103401400c060799528490749805d8111401141e50720305c0041d082c000351001030f480f40c20101012200410185d40c59071145503050504105000840382035000003000c221039450390040c911810751a00081100d41342c6100869107074143c190410640f00d0440700310342c145d900d1940c03110015103020b0380100311003020800005450b510641d8280c41401da40d42d0002040c0d8420b004984183d803456950308001102c40d40c060f40980210301e402070745140c4c103101e40000d01c900005010055004c1c1070041c1300d036050000000126070019000306000350 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 123796007 1250 123794757 123794767
    0x319020106150c0503210117030f0a0c020a05040c0f020609010902010c02090406110307050705060a0b130f0608060a090b0106050313110607050f0c010917120304080f070f110402 78
    0x151411044900007403c0c1403201d41c00c9514586181144506804a01560f040c1d1844800b0b110102661a042e103100284071124001002034940e44c0c1d005003e04004002410054208807a00c5090704900103031020f40820b94240d1a003000030141c03200c0b88402000920b41c0b403c00070b0001d0341005003031342128458008005513036241e00000d081800aa002038011000385000c207080007115802403224603403881c8202c4d2a4208801c1c010101d80c403822069445100d090b001c102800c210b4401c5852806004090031002404012028080e007803081300d039200242c1d1031303e00040141c01031252501c2004110302c00038001640e440d000d4045034068005800300601481040010312410f803c02c8c43c81900504204162000d5600103040380c803070607400814500824200c0e0103031a8002602c5070310000e00b40c0b11810540c1e1209006003402e00c50016808080e0700c42051a02400e80030801150002e004039191761138151502c0080d42c1d43d6111440888511040c0301940d002d214400802c3c0d00c0e42c0314115420b500d01 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 123797257 1250 123796007 123796019
    0x403030b0f0a03230a0b010b09090106021f0c03020705010911150a020a0209060a03150c3903090314100501090b010c0210051c02090406050d05030301120c090e0319020106 75
    0x2003813250158480c0c0200103024641605010043d000b01254402160301480da1601d01c0e424007504a848514001c5d41c0900000c5460f500210b442e0303018508080b078440002014903161400351500b41d040c0070074181c0c00c0142c0004540c2c00e020345074103140926601620740301d0040c1881105034018a42c00d600060500c02080803503408100080401c0e011150600789456000004459094550005001d00300c2004158440e01c01c9800ca00c814034010745420386004020750020790341a0411034050202c03040807104101d0250f2004019410900910b030249941e61259641100400f241c40c20003059030220f1040d45594401d07014035805000e4101007848045415000038100000c0040002d200d205001261a400c3d88184191481e03014106002205400200759440095000b081c0c803c0c00b841c10160041481c4c1002c00000d50741c00e511800541c50342c7e103028003a10660f40c04410441e0800c4406100140c2820540103444d41d0311031710001703140e5034500b04118400c520325040140040da41004010042 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 123798507 1250 123797257 123797273
    0xe130902010c0f1a0f040c051005040b1e030112050d0203090f090615030a0903030b0a0b0304030807020307020a06050a020c2202070510060806391606050403030b0f0a03 74
    0x11684500d642c14608541c1c6045151107244403c07130500d0364114000c000d20800c004200900450248030300038405034541d8103201405800005080101d802007000b00102d5070104014084202010390fa0348451140e444041c081d0b9001703921614601d00203440542c00e20406211800d5403051a00095241500c1c038000b00f140803403804007040c03103031000b0000103081c0e0b21191000c1c080f4540212803581e50346400b4140310000d00c9a09030a900283c50800030104a04154001c42c0958024000d4182156540c2d50115040e10005240710110300007800000c0068075900b0240e405003111380c40d071030b8442d201c1d004024640810346040500c030312001c0b00c026001c6500e00d0f5a8a11b00840242c01607035481a90910500d03050342101104001490b141c030005d00e0a00100f0b201d40a00c10300d1000c240d20404008000a441c1c580b180ca0304680c00b40101c24072030756132010005298103030115080c944900c14545441084440494042e0701180d105c014220140c074046682c50001c0c2e400310307800702e800b604549038001 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 123799757 1250 123798507 123798527
    0xf0f060507060902100810050301020301030f02212e15030213140c0409050705070c05010815190608060103060305060402060d0209030307030f02010f0204120b0c0c0d0e13090201 78
    0x2400000100481806895007000c078200d030b00500480303182942c05d00c00034000c03041125421804080024082580d2a040c02206d0403607400c9140441d00340010b170200107440040315140c0810b490500141d034580d4000384101400b030f081110364000a64130305503218400c626804031682801d890320a42c0a5002c90300c0c1c6c000300c203a03901512100580c608020f040300080c8140704681900d80080c204226071080c041c0c00030001e0328240d810030320080d00d0720b41c019102030203111001440700c098400b0602041d4401c1c6800c0e54042014000c0c60b03280104040031130b12192248003030080c0e9840c9408144969a0820dd032250031040c02c0c6400c0181c42c1c69625003d4440101a10080c8221000540403e400c28280c042d6650100d004041e82da990740d0605e80500038a005d069128099400c003200b00210940c54402e03241103904428241c095100d0a541c1c0f0212036200618928a81000340404040e50360100b20503d40d0003155156034643c140301b0010441154070f82c03001d0940c102d080403140d000603603018070452 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 123801007 1250 123799757 123799769
    0x501050601080f041b0b07080408100b0d060c0c0b0a09050714180907090e030c01060b270301110a030b12060405150403030f09030e0405091b0d030e04090803010f0f0f 73
    0x3c1104250544aa80301596035880400500004540402400100c070006d20461b2040310491b0303145043c4be0058000d135403000d41f12560000305100b0303138000704901d900850b00c80d504a2030813010b0380b04103949800d40408140c0b401c90747e442d5107800c1d10b41000010004200546100740c4e600c10f450070b10320000343c0a501c0c004844506105110701040da114420007008002e456001d00604c840d40c4c0410b152a80c9030420040e03404950b00300f10000519140020440d20710750082c0303140e203010071244464004250300d800040da40643d039400910107402441ea000d025a4400e5a801291806040c2c0400060310b294480d0541d42d50818000c4c003002900004148c88540007154144905a0b1103080a4008015a1000542290500300c008042542c09151501c003030344111010072103500c0e80e0001030364607801d0003002030580312900c904c2c0c40d4910b840d1040c4075890b48680780002301c4401703075000320f8269050030404840885011005208050300c0e420810082c3c0b1036112200c1c100791401c039400c03e0804040c8034123 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 123802257 1250 123801007 123801023
    0x207110103330e18060a2922051801020f04120c0b03070f110a0213021815030106020c100816110d0906090b13050402090604030b040506040501050601080f04 69
    0x1034110500155070350b40200b10506156200d8a001c07058842c00c02c15112140c20240074880000304034030094401c91282c2101080a451503a103c00c140400c05844040003541c022201d0741007440c02c48404e0700c5040d410282c0040031030039050510301c210100e00c003180061256401400320b000500c1c80a410340c0c1c2140c8502035a003038450781a042c42800c1e040c03150426600d448000040140d840e8000d045e824402c8180d50310007102c05001069692100303071100000798003d1000e40341e0094141150060440100800d40070340c09103040100090000c0842480b00301410390100042001540502208600200944071006001d5444030003c1c00e5420040c0b495020f403841c244660300c4648a0001113000d88000b200705d4111000300b1300003604140c09031041300700043c241d01022441001d0742c42a5090b0717614406088005030f0070281044040c3d049070510f1034108509000010100e0701c00b4810b280540d02420140030b4608150070080c4c00d451005010703605000501060044078001b409105501036049005 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 123803507 1250 123802257 123802331
    0x602090d0503030a020702150a050a111204140a050d150903021002030a20041a0c0a1e031716030504060b0405070203090316051c03140703030207110103 67
    0xc000c11600c800c0584184404410072600c06056402400c40038000c07910a80400201140d01c01240310700080c2100045003407003800801805611400780341c5240300c0c1926184010304244a00d02d4109a02452481da00d410031400c0c1401d001408501408003524100d102c40d500345c4038200e04a1059003011049507503100100c5c01d040c402c1c0301500c01c80720328070307802c2d03640b4207200a51401400c000034510380c007070802c011a0b000b000c1840c1d00700c60441c6c05501c1c0c0b45c600100300400514070382e00001c1301c801d00d40c01541c400500080150090f40c445034201d405402c010803503400d0040c1504921060320301001550b500344644419041504c106000c0145004506075485203449005401800f03110b80d001800e1006100e0025000703c007408200c44141c0449030a024a042145d85001c541d105040d042603445110f45c854003a0309441c0308070180a802c00034060506c00032210060ba00c2982e050300007941c00725200d4104134448100d061802c1302442d0500c00c48005164403c0000c543c0d4401080840007044 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 123804757 1250 123803507 123803509
    0x80304050a020a0e061201090b07032003040302012004030c03060b120f0c030f0a022404030b0a052d07080a0b1512090a08040605030a06090c0309020109060e060304060209 75
    0x1944190303406840c2c40b644540e9102d241c13111032001d440161113a501244c0c1407441d0349051241a501d1a040010030318940c4481e04294010024030248411080246030000105040000150700030b80c42940001521022025601003400103007080c244010f00070002003002c10252600708007541d400840004902103034500040050440040c0602c003401100c48148078101c021406621184d800d034240c03260780c01c4100c0c1c0c6549881000c58000c0d444a61080b40c00c100302c040d041421203038100e01000c00c2c40c3c141c680d2100e40c5010000c481d8200d54948481c100000b41211500844103010320303048907010300844e0700e1744102528000b0248802c200c810b00010383d1590720380d08001120301024105020503818004103011035404511101984541c2901041c50a0350018040f070406800250380d5007020704007201220720f940081e00c00061a502e402000c56842402c3c03040000c814600e4034000f0b03920030a4800940b41020300d500c19000e00c40d007070000031a0340c0c986004699010f41e01400c010380d00c4685c18 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 123806007 1250 123804757 123804763
    0x102070312030f0e0a03020c100e06040905060303070c030f0c06050708090405040302012306040b030c0102102a11150106020a03030b060d060e010905100501050d050403030e0f011d0105090a08030405 87
    0x2581c4e814003441050035400c181b43c1c0200d1004840081900d840c09401c1e20301d141543c0d25500d07540495080f20040004106a940302d621072034101030f000b01600c1c40c02c8000d07110401d8141050f0020380c0c83c039041300c0b158020070102c854010f0041186060090814102e51503000d05400b8280005008a88407030004081520030b40c040401c51503e0400111041450401c080072a00c3c21580c1b54050741c80c02440326200d1900052541c1004016401010015146040e000103042c002008003d900f1a100f182c480e000e04600801075190215911000f00700c49100d0810302e0030b00403000c3c0d65000b803040b40043c4011580803804151054150074045250319080e008151107104585110704554504107000c1691122150024101c4d1070100c1d00340036988130407240d9404000c6600c110f43c0030881c00c0080005070210740e045030f03074854040d040004000c1c0b9a00146403e1510000907182d1a0b595109011702010b00381c2e03c510101c1d40540d000700020b2070000452070392104c4800b00501004c0c2c0c0440001c080040030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 123807257 1250 123806007 123806021
    0xa02151608060d15140105180615070204090818040501050f010c170f0304021302030c092106010b03070f0801030b0406110d060902281e0c140307110102070312030f 72
    0x41010004c1e9145400300500041c43d4488880d68844840c0000040b14a0001c800302603c90111f40b914400392502820000340038482010000a41410310036900982c3c3c4602c641514a40036083d03040d65600d44a90080c8126160701840e4401c0d89131400620032034503444081c00641d0707000c0c01c0292100c103141c1844071490322110700407030410000240e000810380c429005180103600c00e4070200070300802c0c00150010790104680d1007000345010f0200d42d0a40c13411030000070369a01c510a07089220000744503200d00300042600b001c1840303c0b000060004080d800340618080c09014904001c042d415036807074049500014001600c1d494540402da4107183c140c01c2220b00300740c10000704002082c0d032003810308003030741100d42040e409283d040c1e200031051031040c8100c4d0010340e00756240c16091070b800c21100d00b51155130341c0c0d0301700300240040c155001505400010340007e2002000719111209403820000381c1860003041c0d030464001c000108001014401c0c1054225068100400d0301c20b0780c9811749004040f2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 123808507 1250 123807257 123807263
    0x70f0509120a020a080304030b0c07140604030806130c020714041407020f060c0c03030402040e070b040f14301c08190b010c0b0402030a06050c0a02151608060d 70
    0x140241d14050748400007441c020840c82507a0718244643d440c40c05948902542c40050017400303800c00000c2c1209031101c014081c0d5841220707402c14404060042c40d2904a08070f50071404180810248030483c038007840121201d01c0c010710180180c40000074000d4613000e5a10469010514030f040040c56a55290045402c42d104072100140614216200070750741e80056141202c103008940210b408000310204a6882e5030000d401980b039604c0f140d003800700600b07200d5079844242c024010003080b07040e040e10041000f004902e80a8a800c1c0c18410b40001c800e000458252240c0f13600c0c0100c00c0c10049103000c0d035001211380580c40d42004109079041e070520488a000d540790012500c1012229900014024002c40120404212070030000c0703022400c48030300d0f03600305001c505000042070010398140c4603154018405000e40b03910350825681d0700b00b9200d040d0340761101d940c40811024040d9504001251042e60a50101c500b40c4c20419182a8106600b0800c0000c204055000907032545540700100d0890754 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 123809757 1250 123808507 123808519
    0x2030609060703053103090e01090b0a05041503030c0c0b070b190507050306100504080307030c15020405010c02040f0e0a0506090d02030c1c0c05030403060c09120b070f0509 76
    0x1608203122a19a0422541800800e19100202e09940070101d4680c1104061214a103903002040c196466400c000d10012000c000c80d0710000304e0078084070900d0b54000e09405070040340c50310341c800802c180759495070400c07401a880c20f400e034000304104600600c101c82c0c00d8180b0008040f41801d206034110100e8000c4420709400091150402c00c448010602c56070041041c0d241c184400403218041d03c40550b8010000f50003400420114504100303121440181070030490725113599000704a0458100e0b40701600403600740ca940c9418003012689015032401c10368802c40c5020705040003e44004680328019000f580c2e6805803001003252544011850303400c0d40d007111074580304da01d041603448008888224a41c01481d4a103681d0500000690f441c1134044405802661740641c000440c0a02e600411030400c150700c3d8040c00890002d20080000d50f0140001040400c80d503907014080035010303440016084094100040890080406560841130034508150703107504d036150480321070007001c0038185d102c4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 123811007 1250 123809757 123809761
    0x50705010218041107050a0308100302180901052a070c0305061008010612021c052d1218010f0302090a08060105040b010503191503060c110c0a0609050103050a09020306 74
    0x640080e0240700340d060102c40a0019681544c05080e1501401d480241541d00c0a0501800280034415441d48010303100c10035003a0700d641e500002d400c006010100d5404180d19424015562000c1c0192980140030840c01c43c44501d043d0b00424400003505c800900c0b0382404038005041243c012088402180c102c4110741d29410040702540310b814480c400c0008075840c00c00300040710a00520364811558004040f10524402000702c200b004045440840d001e0240120b2003544100310103003d1418a44001c0c0352189a40d2001010f103440100380000c50168424440d40b40c90640c1c024030540c01400a02e448140298023407019006800b039035903102d174400002540881c001c0d0002441c1030484c3c07421101400b0300d84030500151f607148025203905182040c498031405004100341c001e0142592510122681c669507a01c655085030303c910702200026105060700450002c0801c00a103003000300311500842940303020400740c900ea40030300c601414541c6907000216100d020b540500d0304c09401238240c42c018 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 123812257 1250 123811007 123811027
    0xa140901031d0d030e01110409021821061e0403111e03090f0402040e0609090304091409061605041703070501020f07020109060c05031602041503030315050d0b070e010507050102 78
    0x18080380d0301c1000001e1605c20300d881c02c003405002d038542c2c402c1c0e00e6554a15003401d16110300065407256881d00050a08181c001c0d4039510740000810307003075001f0000301c9441d0111115031800c2140107004980c1841e416003d90305035088050180f40c01644c181003a489040e5030b51030040c14032024100f0b104c400ba0001c110100c1c07410000c002043c00240c200e0305000c40180d9071082104a00450050010110050700014030030305000905030b0300001e0b80c20482e03080960351071410056854414600801d21006400e100d01c004c001c10405801ca5112070840b00b118032440300c020001d0285114808080580d1050a40a41000d0045035485078201c0000d5668000d0f20090580c603030301007942240042d19003240014403134130030394455001c1a8001c01071850030000814100d05100f6094060f40d215a175108a0804068040c150000039442500d01040d26600303c031403110001450b0340144e00918001c07030a000000d000030301700c42d800041c0c0e040030340c25108104012204c6002d00301006280f0f40c8001000010 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 123813507 1250 123812257 123812263
    0x210050903030a1104120212150a020702041413030509120a1208010503280326010807090b0f0405040311030414030616052710080117030a140901031d 66
    0x4240f1560b1018098150000e00e990540e00ca14460b4078051a0020100300051401012000580c190358044940307042245150328098030060310b0380039806074001440011800c050040c140c0c2c04a00034007414861074135115484207004410001003c000002611100a55817001041c103848031000845e500c0301707500d01c1d000c1d42c036141e08030b088404280c004000041910300021061900b0481d47c0341044403a0000e0224401c800001c10102c0c14414080c0c0c081d40600121082ea10690411a1844d049940f400302307071a0410410350010352030582000458212a00d6508041455a200352000103081e66141000c440c0300f00102001c80d620b010000f80014440d2084500d400a540210140c0d4003035190682008250480380c1520700200f8014085071940c0f51498107185c201000804409012150740c80c00100d40303a200146010115000000512084207910341c0d85220450400003140b811074240000380c400503191100307204044001132005103a900c01e4110896000c0024241d28410b00840b0007152 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 123814757 1250 123813507 123813511
    0xf04150815040b0a110d020d0b060c101b05070803061f050d060b040e010e0a0f0e0304030c0909020a170c04050115080f0106080705090102010902060301030c1d04030801090b01021005090303 83
    0x1950503803543c0461102281845030503074044070444094604016400050003135000040107075031040d80d030121400c0b5501d4001c006c00030740c07800320b025001e100300d0a06c00310111140c03c00e52807408415141c0400e01190004101c03010680c11000b141e0b00c3c0c0e6940000560034140050900782c200f0595140c50704401d4000300900880410000c1c103010007612040b102400e07002e98850442c0301d01445004000302c0d5039021421360004041440443e012454440403025501c1018081134a60300000b4100140321082002001400265805201140141c1c00280110f891402002c5960800c038420740f0204604015244031403001520030302840d07a458581d401041c00c040f000d600450b09100009240b402c0341e041150590b602620307080416210000100c4443d049203d8660541d941e91042201590f51440694000c6205120b4210342c5410803480420a440c00800203100203406e9090000007500240d044d419582c06580008885242e440100d1408184041d18051706180c10300703000d56440e010000314 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 123816007 1250 123814757 123814763
    0x8210a0c1506060509102a0218090f0f010615030203070207030c0b09040e030a0c1113060306020a110d050301090b130f090506060f03060402100239010e0f0415081504 73
    0x101d4880036215040d51180381a4001d4055101c1014007204000429400084c647c0d0000d06182d1a503a0702c0c114403e200d18007036401c0d85050f84007c2100010f44020040242900340c500024403a0300e140079081a00002800701e91014503801100061f0003a02c00c02c1820002c0d80c001460310780d4655104c40302e00c4154082e8460354059800c040100030039500000c00c494a4240316036448007581107503101d1481000308806015070240c1054a2901c0c149014020080514060700b070050360750601d01e9014280321042c08003401b0503003121a9007803415801c4401e0f41e04503121000003140c0d860705080000da12015441d0210546890060b03660340c0301c0100d03482140410b00c50000c0392129211802007088200d2140b02c00c0740d06601600000740181400580c44c000d04c1058012291512a800305038a50f0b0041804010b01d1960100242440f2941060389840544800e0030801c85400c6101c010600d198070040c0343c3e500882e1201115140d5018010002004013051800c0d28841c24500c02d850603001d05c03d6a0035 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 123817257 1250 123816007 123816019
    0xc110604060c080c04181d0d02070e01050307080303010e071407060b011713020111010209030105040332040603020912030d0902010305010509060603011806090507080108210a0c1506060509 83
    0x9213102103840215803e868007a201038800b405da02d15072102a00c20303040441c01400e242d1420504040c0c04112071000749030701c3d8002c0c00072181411504000ea850582c80248203500044003004080c0000c02281e0658038104404d4441d1380d600b034800d0b2090307015113031001202e4100141c43c1080c0201036200c00700f00f01090361880f0313084035045a25900040140c030300084001d00c0c42046001913001d41c82d01140d1003800c5c070001d400c0c000e01400080c2152001c0700c1c01d402252502c11200c00006032040c0301d2780f00c5240516190300c5a00000a1074005014a0190500381580040e00c0c040c541d075a50100010100c02c0d60032207aa5071f94513441c110142030044000c9010900700b100100719440c2c50340c0c0041c410741c0080e001c41d00f0340e0318000807101501d00111002202d10b5544102040400b294042c40d0322032100c43c5c681ca003895140003509490140d4482404c4070011800008000b03501280c002c40d400041e051034460b07481641420700c412990a0300000400e81490100e00081d01900302c0c01030140c0f441b0072100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 123818507 1250 123817257 123817261
    0x4060f0e04060602030a050702030703060603050303190903021504050f010501081c110322080106080615121518031204110d030806010804080702060307021c0306060c060c110604060c08 81
    0x9020a840d01c0f401042c000d60030910029075a030b03109074040c0444070f0004085801c2e03142c0d02e888174800c46146420a85490708000104641d46582d03690600074828003020801050760b0729100251202e051500110030b80b07035030f03a002c201031200c200300e400c42481101d03000b00310030b5a54002a95441d400c0c0d01516041d000d0070a1564900b9000d00100700d910681e1102441c0380a424440e00040e51000b000154144800c0c1d08010690000920454010346101c0380142224100380041800054142d40c2980c032820b1a040440c02920b800304480325081040548420540c540c041d4000344043c08102c1340f0340612000c90003020b0a00c00d00c422134007941c00f07002c00800b212045014440703080c200c140c015021400c2ea070003080e40307544180b130141d038000e0154041a05100483e4001400c5501c00c0d503035000107912000030101a9880213016101c800b943c0d00702004010702d03028028000c86225a000303000c0d2540c80300020742c854003c60303588c0c2a15008034152a41460b1501c1c20038011300705801751000013115000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 123819757 1250 123818507 123818509
    0x2040c05070c15091508040b0f04200f0414010f05040203011d0901110d09030311030106120e030d05070c0b0702030a090504090f0b0a020702150405060714070b04060f0e 74
    0x200311200e8640200708022118200780c80f852003c00c2d0030003010104400d82c10005a095030003106008400e08590302c40c1c0341410a03003440c00c1107030340140a146006200e0402c0c000010f1486081d0032441d0504441000e032420200c000a035004000c08046420504141140541c070700c07485a02070580700c0d400300d0f00c0d0400703440c0d4081c00103e0200f4007031495079400a660503d140040391540690014020b4004103003a02d0202031180b00f500844560070080303071645050400c0682500641601d510f04060050035503151100c000d010307245035400403c000755107428080803d44180220740812805001c1070080c1e0414110003000d0090324141030b106110344001003005103202100300c0324404440c0d59200741d41824031007004014941d4010880b014000181e800002500b0010424820700030722000513140e6900e8010b0001c49134550021130b5420404001c14005582d401c0c0c140c03501b80d40c01c03220125042d40c00005491800c034068200080c142000b050000d442e583c0304801c012751406696501c001004418 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 123821007 1250 123819757 123819767
    0xe0c0306090d20030d02070c09241a040308030c04031a040201021b24040513050f0a02090604080303040f060e0d020703031d0a08100c021501030615090203100302040c 73
    0x4540e82c0081c46440100100480c070a01d6503c6982d01d0780b055030710f03212008151108a901c0300c103040350000c50418082000f20900d1241440f111400c03070441c107001d01c03c4600c0d0302d045c03103135402500c03940d80381001c3d81c010703000700e543c01d4801a580c044070880d5030b4103019502c40f100c2c1d00f042c030088a1010703102100502240009268070300807a41a0001c010f00002c6940390038446c10f0b00e01d4800d401403038209a44603180a8213000a000181e006401039859007854248117104442c8080c155a01c3c0c140030510444000c0811a550b0004e417038100161030b04040c100260f52031059500c1880b0905c8044280020f10941c9181e01640c81c0c8900c0b0104141140c0f085420384803000d43c0498005600250070420110740038170f03010b003011030000003074200d030458003400503d540c040c03600081504da00407160800f2040c1c0e20720071950340d00c2c1c1c01e0006111742c0f402d0f030013044494001400001e101549960b010320440075402c0c0e250740a81044002507440b881c003425440c1482071750340b00c1a4401c500303107500c4c3c1000740d0103a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 123822257 1250 123821007 123821023
    0x1e1b03020907091212050d1d10110904020901090506120a15120609020102010209030106030302060108071d01030305090d02040f02031e07020a1e0b10080106050619210e0c030609 78
    0x2540348122030708815105d00c1580314081e054607050000402c002c031b11441552190704100d60a6011002801403031252052030240d062124989044c84c1c03420021058143c00c0a5540c0120210b5002d41d4a5801e44012a0141d50030b503c00c1da002540440d60060710701c1d044170214800d120794142001030b42010701d007401c0c10760700a101c3c06011449510416001c101190044010705004ac00094980034401010908485860b4020750068000000610080200f40221401451943e99800316540001441a920a0103100040501100096101c8680c5528201c4542150002c008000400301c5003a00e002039801143c17008222402a003002100c140464602c0d80030760341a50042c0b12089030b983c0e03215110450b04641801c40d01400801d00c2c0003c0840e00e4043c0f2810541c0c1d44204004c2c1384c240c1250070b441041c1c000511a40041c402c15100ca0364a081c01c9602072000d2411762075000c4a6a18404070201e4444038144503401e0401e00400c0c2c0100007540050f0000680407107041d0f80c0e82e456030588030202 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 123823507 1250 123822257 123822269
    0x807020c0901050103090f0c0603020405031c140318420106030902030109080309030901110c090a0903030b130c090501020102040f030b09071502060a0e06131e1b0302090709 76
    0x40007005010f5940f10b070f0310480d40c0070300c100161010312950740c6414031800c1013a48003200080e000a4103001c107081c2842030000c00b001103e4202c81541c188000a80100c140100f4802c00394800300002d24030070b10f03080e41618a00580300c282c0d0380400082010039540055501c01141c81200780d400118402408a030f00351024580304c010302840c0c0d00384882180500b0710386000380d03410341d02e81d4801408114528000c50040c1201d00041d0b903628500400944180698003d0f40b231103421640080400c0d40310702e01c4607035120564910020303c9001924003a4028034840040c1ca40107070250604c1642640d00c0c0c0c0c001c041d5240c4e00c1c1c0381d120a00d035a52004a080c0c0c07040740510b01450741c0b500340c20000600c0500c01103070407007004401c0d1002992143c40361072801810108071401a80b08100b44481080144201800c08200707101810f020b18200c1803240700d04407080801801c4c040d100405044c0c004d408502780c00600d0303102501d00d120251404050900072002d000503841200c000c00072414041c0104d08650456003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 123824757 1250 123823507 123823519
    0x18100206090705041109150a0e060a050a0513080f06010306050a060803072919061403190309080d05030906130507061b020604180608030a0215090307021f0807020c 72
    0x200b0300c810304c00602074001c0000c0400c60700b03000311070072541c0d8241c0000f01e000b44081c44645a4807083c9005000c4e0744085880c500640080021400366076004c811689944031504207a65030340c5910500b00e4203001c5684c01014580188000f81031500c0022130618100c0e40034040900c07083d20303111020002c4031168800c0a603141d104100042c001100101c00d100c59420042680e40da1244400c1c81d00d803004000c940c80b070440d4140740f08204500d9071510514026180c50280c0010710716000c03000c40d41d5421134291100444808020490030144901190b0010b00350000a481082c0c0c030480010303040d0b81040d40c106030217010343c0000400406803040140d40b415002801030008130315040086c2c90f611580106c0318001e6600d03a4001000d40c4603540140010300e1030b044241100a0020242c3e0102c44003508481c245030410403540080c207900090b00d20341000c4000c0201c905440e800c401c14514842c08100a410003000c1e05c001c3c04008100f4030a01449080e522441400e0b507448a00f00c0e03c0f01040305620354498 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 123826007 1250 123824757 123824759
    0x2010605010906110127170a0903030e12030d0c0912020604150219030903051605090c0c0c1201050708010b0a02030703080a0f060312090617010302040207080d02181002060907 77
    0x207071140d000031074001c4c02039000145002907800e025103810b0000d9009001007841d041400100222440e00a00d01e0424101711030401c000000000e04030885444090100020f62101490980d04c2200c1c0c210182060b0b011650748400b0303107160f000075004120320b40001c00c2407500d00140c103990034890307011501c1e40244090300d0103090540ba949031200c1d16440c072045202c0d1070030a05c01c0049009219680c680a61105580c091071890511300e0318400042e958413100e101e00081003191240783d005030308100003088840c0c550000c010540d10301080c0c11009580843d40300302e201c040e418198003840c0154110b50f1800681c1c4e80355841c5028030711505040703500580c020044000468425401d15030030840b90340001c1040c0240c4c1d1040310544205400544034000c406104405d8144c100468400806071400e0020030501d5419082d0710b5050140720103401560001083c00400a0ba402111007241c0c001d541151070308642c9410402034241c0c03048d0f2601452039826000007080c0006403039407007075001600801040b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 123827257 1250 123826007 123826019
    0xc0403060e070e04051c0e0f0f0301090f080d06080a0302030909042a060305070c200f090108030c011a0609040e031902010516050f03010b09010903021c050d020106050109 75
    0x24016012004124026010b010445035410101c4078052401000100b0741215103080000754868811144410b100d20884003007566200c0745001c070803400c2d04460380c130340c49180d01c000710f409802a028021b221020079480c03c000c0100392800341014469000301001200c0d1140030310707940d880c040900a0096442030200c09036038500a584140e0040c4a40d80001d214030282c03020202c800d00c0784040d00420b030305000c800d110f1039915120703080d8040c13410700e0905c032580a40c1c1c1b03030303ca81a100c448800180c0c58400d00d10303c0040c0c4590000320680f000180c9070b28050740e502e2940c9500d94200640c05003141d402c14415610400c00750003d024840d8008002c40d02c1c20300c05038108401450500d0031013400303020902190a612081000550415a80350000708191401c807015000303041581700c0400a00c801840140c0b90284901e0a40e03045d0740ac00c211403030b5a49000001a9080c0d001e640c4000e40c4090036190f411154a80c00780c60a600b184904100e8206042410045c0d02743c3d04107001c2e4600040400404001c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 123828507 1250 123827257 123827261
    0xf18060606030207330204060c03030b0301061503090503040503030a0207030b0109050714160b0c1e07050a03051b10020a03050a09110126041b0801060308190201021b0106050f06030c040306 83
    0xe00c281c0c0b03c11000c0581540b052170002e0380c0090384840e000c240200000c600b03241e0540900758001c01c0440081060310b09060081d50100c80401e04e030401c01d03554ec2c3c00c1400b000003c00440d0040d040050480c0d440315a0b40100a43d90911400103e030880018000010303186114040c65024802903154052032400c3d1a4242505822a4042250b03c200402c2e03180c002c100a020407500820440b660701c1c1d80e0752038200e00c480c646100814170080c20f64040000202041000c605404920307030600d0819501d6646480c0d00d05081c400c04006462805500b00c000c411003651f60041c0b1048950343c90604c159500e042c0940f040b221030b500e0151a040024182e21017940c414009051034031544442070054400948001e204258103d500b01c600c5215003000701c1070300d88400c91180c0107201c1c1d140248585801c582d40c02001d8080c4046881c1303003880203401c41c114a8002c6d01503802c0b02030302100f030544803050b11300840d029001c40e1042c5400345080c0345689020b41018412244113041c600901c43c601859543c800d40 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 123829757 1250 123828507 123828563
    0x215060f060702040903030e1203010815060a030c06050a0f020c010e0105030601090b03161b030c1212020705071e0e13030c02060a030608010f0506010e0108040203010f18060606030207 81
    0x1078890410010440180e640d4030a804450b8000d90740080d0781c80c0b48a42c418500003064018005c00f040074001084400b600160716050643c00f400700000c0794132004082038141c0c3d607642000300b2420150a010401030b42c0400503041a008076034600060100024003039803074030b505456003800507a07122030ba200194040c10041d40c000380d06140200d89a030b62818090a240c000307940200e001024042c411042070361041c10b0120b08001c411300304100310740316070f00904401d6640300c0c000d00307540915400c1154140201446e5441c00c00c01c500075581e0b80c90a1174203580f5145c0a0080c50b144500d06150070400c0c00c0094101c00a590310341e0f00100b00e0380c50303a280d18900010406001ca040050710685100103888600280001c14240d032000304149081c8903401e429030b40480a00702c04c42e0710300f00800c141071380c0c04078a034092070000382000c031104d0315030303001181c094084a0003101d02c1c3ca081070344000c041c01d12440141d9000e4012101001960b841d0041182a8030408070068010302c10303005102041001d80102131 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 123831007 1250 123829757 123829759
    0x8010e040b1506070507050a08060c0d0905030412050a021516061104031a010602100b06070b0402010324051c0506010b0309010b0307030c03060b09010b0a030209131406100215060f 79
    0x20341c60300380b2000045103940321203011101c941000c14200700c1c50a002c54590003a000e850040e041e24508840130301118003c50841c807030710646441944040c0b18061040b0340240c01c0c80074840b030744600136041040e036800c421041240110620b6071804601d01031318042e1003036130106d0010851010000c0c0c0713030000601007400b0340340c0d8400350420001001490200303002190b121607108840f010740c90040c01070f0502c1c001d4810240001e081069049090391420200c505503a4402e464036000e889600040f0001c051501e06840d00c42885c455a10726400304c68070007000c8980c00c699007403d0740300c140210328070100c44100051443c1e100400501140707000102841e400300903017000141102d19200041d141150f0355100341d900081c0701c0c0080c01880510700884021080030f50310303000103515041c08003070180700752035030301c41010b40c00305034503503ea62620700d10300312140c2119042c00b412540351504200706400707450040c801c020f0040d02c44d034414000300714041944001daa06c000079644d84020700c42d192036101d20203 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 123832257 1250 123831007 123831031
    0x1305120705011e0507020607020c0d1721012606060d0807050102040e0109060b07170904060f0e0f100e070f03020712091e050609150f0a1e08010e040b 66
    0x3c40000b40e0714600d000d04505030304001007014200281c001e400c120f4094017035800c541082c10300120307544400750080c11003a0300641c14045103c81c44105a103e000308012070304880e500341c15101c52010103e002c1c5050301c3c5d040d6070400d010580c9200c14100e07201100d003840001d80011000801525103002d885901c0e5000d103e0342860728142c0d54486003260300503084a042d0520300c4005000141c0188034000141031146080c030302d4805107444800d0008020300901020050028210130b040e100e43c0c101d40014800e50032400041c9071900360400b981001150000c00540b0504001502c42c481a41135404551408069000c680c0b1006001c49280d014045450141902041002c2c0029407002007106080352030303a5070280190928200140045000b1580040020104014443d0b1794603a4204c440072a41150f40e82e8044020301107120007401541111981d00001052407100c1c90342090100e000003240a200c590020840b150aa800990038001d600c204400800040c001a101c1c0c3c01c07071350704000c8003511 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 123833507 1250 123832257 123832271
    0x30e090a060b0c010c180b07060b011209082d0a1115070c02010e0a06050904020c011b0521010608060402070204060f0f0503100e03031605040b041409130512070501 72
    0x30034640e502c0902d503804181c2d568108105c003a42d01030310440c85000c10011642e101403401140c03410b83d0050000140815a4545a00e10036a018034102d03c2403401940b418019010642000c003900e420801c42c00e04a00350549221209104c886400000e42044802c0b40e03041030308041007140d902e401d400ca00c560502c5406180b14002c4c85082483d8030405940d0345140358840d8171302c001003044c0740d000c442c90b000714488041446032540010603079400c01c00986005840703a982424072400f41c500701c60310a01c8285075588450503117a100b0010803c41d05611018803912640c2001c1c10340e01d5230709101d80380010b008640880c40625154005101701400100041929904c5800c403807840f1041e0f074061000c00015450401c118102400000410790141030108400102401c896880703200003481c0c0120140d50030b50f40076546003d5420381d4080c02c0d214880a49850304c84000e4104a192602c600d84a41404800104a1450b000d0790401065102001d0046440c00d000c8403086504240402c940315500c81e41 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 123834757 1250 123833507 123833519
    0x90b040815041a0a0b04181211210a02060106021c031a130b0f030a0b1314010513061113060e031009061a0108070206240301230112030e090a06 63
    0x112850081c000c035140011504c0641d010441125114900c0c10307c110001584180071544a0000b400f290f041818498148c01c0300034155130400d42001e89060072202c042d202541914010b20107000c1000d001d408540c0982d03210a0142c4c0d6030504214030320003a44014120b5400e840c42604012040b0700c0d540c0c1e420310008802c40004d041c151080b00700c07a07440c80d071320b080c402100d141ca60061020140141d02913f284c013060b8440c400550401003a0404400d072001220003000b90fa942e9101080d44100000c0000b828049403400100000b5030048d1062414900f11100d44001341c81240c00801c50408a81011032600d0301c140d401c590301d29000b9915004030302400100025078000c00c001c1510943c00003c014030340b140c0310f903081c4010301035507070400c040d59041010b42030300058000e070884400701040100c2c0c104143c00c0980044801c4929800d9400e00c684a1070300e1034000a13241c2d49840030040b043c02030381c80e1407144030540010480900018072080b4080880d04055814a4001a1030240480d900352186 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 123836007 1250 123834757 123834803
    0x18130c020f01050c0403050a0209040318080a020310020a050d0c361202130213032a092f1210090c0201050c07140c030d0906090b04081504 61
    0x4459000903801c080030409025000f0b1250580c07054400011a00380b60461320f03500e507100b0100030000d010301164008038050501910b4950008038a00010840f111f072508500d42c0c941102081c01c130300902c01c2c1d1031720f000524818005e64089048603550b00c0c0c1808403500855000d00031000100040c84000d10b8841201d04899401c0043c29042400741044840d07034004542c804d2045a11865001ca072070000140140d9032103c2ca2809045540700158448107160311103c50000c0550008001c001070020103e42240c0004914080d07844a580d413243c0c06a56403000c1064a1859100301c10600c9500d80c2c041002a81d00d41007501058002c0d00b15040409010310b038445000103442c0756003406508081000440e29500400d150340c111032000303000505103880310752600d00401c4001004956058504403040c0c2d8200b0080355200e1009046610061024101821202ca41e024030070018950070b0020820512880403a0202e90010b0001c02c3c610440071651909607002070022110b10741210004542018a0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 123837257 1250 123836007 123836021
    0x904030e0907030c021b0a0326040e0402100f08011520010204080f07050f1203090a03060c1101060f09050702120a051b0a0215090103020915040f060804081813 70
    0x945001821400220000c0d182003403d520300703003032016002d07074045058031407840c80e9088136070000d4001840e49070074000c540000d1000000803004270001c180060744080300400d55024030b000791460100420350003412100e002203621840046076120300104200b180c8400c2d04060307400c0034a00301d007103080040c0c84884441d81036910900560b401107000d003c41031040c0402103103074122000900b0b0361403a0801050441c5c091000d040d104138450060745541920500c22580f01c0000101910b500c2074580c40c0c07043c0188010056140002c001c06005c3c14449014031411058842e05004245494030700f01c0810043c0074010800c80840c0240c200d410448440d48014110900d500d80361203803140c0c064040c403270ba02107440606020b2680025045000b5071030301090620b1080b07054070f82941c0c918010300141d0285c807600042c0ca0708031040e00c80400790a030000c8040e00903a4511039078042e15980e525403c9070b01800945010f40001c0c81044000c01c4040b8585501040c4100a40705100f458814580803080301c0c00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 123838507 1250 123837257 123837271
    0x5010501080106030b010837020405040606030c1d0609090703050a050a020310021603030c030605031f0b030105040308070503060406030b0708090c0102060106020a060207050c06030103120311180904030e09 90
    0x103d81050040044100469024100d900002c040700005480c0c00d100c013401c40c0c6848034000030065803d02c5140540131140c0a1039070054024070107418141f0b03080303002740010701c42034890342c2d500c0c04080b0310313a90000301200402d01c440c1c8078140a51540c3c0200064824040c0c00f2081a103d07070340c0000000f61090003201207950090001e400400c3c2e80e4014141480400308640f0301c0548104003801000c501c17080744054182e0140340000e02100c507550160300038a000e0b040701d90700d846250040496500022204404600120018085415000149800d940095038000c02080001000461440c0302da0043e580c0300b0b80007400480c035103030740340c80300d40e082502901c5030000640312800b08080b01e00304204800007500d00b0b20003041c066140980c001c2d10790710043c0004240c03075000120745092020811400c80440c4005124550340c1d40d4a01d40700310030318002e248000100703042c18080e001e00050481a00c1c061032107498880048804141013001000000700101c0170f01c020000340454540b603a41105216010b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 123839757 1250 123838507 123838511
    0x20928030501050606070c1214060109200406050a05030a0f0203151008090309061305060c0705030709060b0d09050a1703010501321e0d02030a051807150c050105010801 74
    0xc118106182503d80c0100114041d4404126050000c3c8400c48070b042140c680c00c2c0030a2a11040d07142c0035120716066110003e692181d00004181003071513070700010070640b5404046c0ba80c4901d98201400900841c0724040129609000701018103001e600115070284860030002a44500709110304101c1c0c10988450704010481e500100395800c000c041400702d2012070408c0d445514100c00000d0fa00c0c400c520259004440214500b000fa480d2849030102400d0f006101c191903d24140d045942d03081f0b80e22501d4840d22824000007030040061103203c0958640c181083d2410301002101c002a01040c982203031240706049012001ca02c140c1c5800030020b001d92074650307481d40740c1300005148401c420306604030076511880002d0f441800b0a00035000c212102806902c840b01e00004107c9200d2241045507000c1000554404a030036590041d80310307981c01d0400b00207548980d40b0300008030483c660000c8050b0701c1502c0a000c0303000b408107822801070032460001900c210640e10b090039294282d1103100c00d41c0d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 123841007 1250 123839757 123839759
    0xa0c0804090218010e030c03072102030a140105010b0307080402010c0206040302100305040605010603020412060c020705030a050f011b020c1504050618040605061231050f06090c030c04020928 84
    0x907910009401d17001a0460082525000b07440029841300b000384210410510f00c6c0320340e92110490b09950b0290240c0040c1900c68144650410b411200050035510216520341000440c0ca00e0b103030004d9078000c2c0c41c0caa031500d640d80d46503030041d41e801e0483d8000382d81c0f140d018880040143e41b800104504d50619590110312800c045ca0f041042c0d51040e00b001c0c0501d801400288140d0140e4a12401c40c070380c01c5000420080b10f82e2500307034117100041d0040c0740c02d4002d25051100b0b2100c000707580030007101403070000c00c003a1909101c00c3d000480301c04206801038000082c504001d141c080c22400905031488007680c5442da948000072003030b9102d0030120a05660540c0380541501e041d11a2000400d42600c00e54030b001b107502201c14290600030061300c04071040031514032411003042e00c041d800340e00b201c0000e405031400d424196618250302d64040301600c19140040e403416400f0078205141380d4050010511403c02104100c00380d000142c42d41d810840c0361070300d40b0f80310f92480010303440c210a00100030505 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 123842257 1250 123841007 123841009
    0xf0406201b010c1d0402070203010509031210052d030f0f0c031b060d0b0904032f030d0c110a030c0203121303080703020a050105150109050a0b0a0c0804090218 70
    0x28000c1d40142080c0e49403080b19654503401c2800b800150700c039071400701201c4401d4000a00240900302000e0b40541ca02001c02c0220034000005150304040c5484551080c2d40b041c10044100d005802041e40022158085800b10030381b0301c02890307400c0d8003200800e40c481070b4440803078035002c0319102c00c000580c4201c0030300303000ca64140418112040240c0203820f03010310645000c0d1000758039400710340c014000084c05825065407507002c0000040c000f000c0c0402c034105418010a021020b00c00702132180343c2008018035001100320313100103548450011b1030501240904a038000c001c001050018802d41400d12607141e081401880e4030075109440d0b0301c5032001180140b602d840c6040f41c41c41030300e20041120740c5e80002112100d10881e0380c4500025603030800c900e0304038141100170100620a6080c01c0070300090103807400102d44c28900a23a84d807044243d40d031040000c250402d01c03840541040401c90542c5840c031819402c4000c5014420940c901035a44694070200c2c2c3c40741807844024240e07503550b8952 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 123843507 1250 123842257 123842287
    0x705090109060e0904030f110a20101706030703020d0501140f010b0415030f050a0b04180c03020d0f0c1e050d020907120b060a080603010506010f02060f040620 70
    0x14003010f20300030b0007004510010901102000c0c10150034002e80c4484034603014030501d80c8664031246003042d6080c00c070a51a0401003a501240c00d0802114040d00074101401c140803109510b0841d0750300c803004502d40301604031544002030701180c0c041c00380b0140032001d03031661581c461011303108000001d44a50071301110070301080b000e00b69040181100c0d0041004c1400b0000740c03800d07a4000303c0c4403c5034101c0080254003c28001c00807125603401c100c10886000c1c030a6000c810300500030348007405000d0044d50040c3c062401054000d007100b40c10341003880541020340307124007494400e103003e640b554001d480345040c01000e540300002d0b0300c981c000c81060b010700c40c2c080c01c03004200559482552400b2a40050005d03003008040327000708084100a04551f00d200c0d000043d400602412890761781c0c80c84603000300140e004540c10703402917003082d010480c194816554600c240d2095809000d068603540c414004510010300240c0f90203440e041490020f90a03001110300412240e58110395921003841400a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 123844757 1250 123843507 123843509
    0xe0a0602060103030906211e0e030310030f0510090f03140313150b10020d0311030c030c071416181a0f0303070b01080102070b0a06050f01080a0f050705090109 70
    0x11074102100410000f5001550700c4107039101e6080c5681226034079441c0c0100955459106007489040c00070f0140e00707807000300031000654901402408101c50110038142d03244001c0e5030b288035020080c841080401d01206005042d28410340907100d035000c0300d50585040c1c400790201503520305a891078280415402441c20500034100504442c00c500c1d080c0140015030400c06030117848084c103041c811600010540c0030301c2003104020408501194900780080d07a44800102d81d80200f441e243e152040e0000001c1a2403003030f4007204a1902e075a840a0400c0c000350401802121740c40341465001901c80014840c01c1d07100c241e072140c4d0b488808c0c0fa040301c0d1600d00c0079841d1080115440e002d10724040f074a0150050308141d405682500070806c551000c03d00e14455114047e10300c400c0d036000414050301c1074004110060083e000f00031039489018452048410034031584e80d0103411080000781d04d50141481d80e42c00741c001100010708601815140003030359021241040000c0c00096030040342d40c0c00c4190030b8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 123846007 1250 123844757 123844769
    0x8061002071208032e180908091917031801050306010e01030506010903020607050303060111160320030d02010f150f0b0c0102040807061806080405030304060b030f0106060e0a 77
    0x7001d450824000440c400c800000342c00d5000c008006200407050060b490005020f0034641c00740d882981e05415021001c1c1d020f181050310401c4140755500300340c0e01840031096006a0345903c0d00001008114281305508622a11145014000540c10254a4540f200c481c4030401840d03039109008401c0d400d0a0f02c01c0c24060500009000340000351343d0147c0c120044c40801e0038000303110380300c0310016908801607500003036021600094003010410040080c1d40985000e0f211402c1c81388031210840d4407074001c480c0300d07405291440c804002181c840c0c00308500c03e81040095110002421001c28140700d07100040d500540c0d1a20201d01c00708081d40706041c50443c040c040a04518140301d4105030800140c0704204584002003031604800300c0a42c103c4000f8003010003152113460b650f00e0050009500c904900110000ba103030001929070240d150a44940e9001018600e150b4481d6210001844107881840e0184a0600f0503a11142c007449039034007410568440401c0041000e0421104c1411a000a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 123847257 1250 123846007 123846013
    0x11030702072103080a1d030705010b0a08071d151e0901090204080a151812020d0c08030105011803150b0405060d080304020603040318030807052406060717040608061002 74
    0x1400201394400e140e03076009003035000042540d0000f40d884001304075054940c0c07400b0340000642d81c000c00c14154441d214071001980c1000c0f0746a500c0c849281c60340038038850a05403035101030340e98079034101809800758400f0350b8000100a03241000045600d1020842454681420b1450400c18606c0e01020090042502580561034942030003074951700c070be40c8620018905510700550403030104403a000711402000048000003645e0030380c01c01400da200d581440b0405030041944c1202050300c00c81d005200c95411046152550340390000448000503500b04586e60742403044401300010728020100003001c08190b5000c50615400820001107500c0503103205e01caa00003052040c00613906000b580d03480340d01142c0264482d9034606080c0c2e440c0c00d804064200001030700d030022040140ca00058038009004004035105070450704011020100b06500744181c0c0061100040c1da1450704500515015200f034000081209405400b40b0442d0096040308003c146000104020b40c100f840110601034103520003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 123848507 1250 123847257 123847319
    0xe01050f0c16050705090a0b090f070903140c03060109060602120c060a0207081207020a03120203060a0e0606220501030b03120307030209180405010b12010908030c0c011103070207 79
    0x8640c80c0d100b92401d03001c1408508049006208003408400300400015141064034580180301100600b0400f002d10310645649001c01e218540580d8614824000c03a101c0c0c0f07914a085466102c1015110100103100e84900e000c8142d07036480504c0070500801074241c022481e1414181c0180c00c11490002c0034480400c140260014a04005403042d00160100b00043e82c42c1081e0812030704502c604080000040242d0083c0190540e0004400d00d9160013662880700c2e4400304c0300c9880980c402070f9840b0340d1281c1012814070200c5680000300750043d00050a41d4038003d030008400d40c00c038616400d41c0c82c0c1c2051403403040001d035070940168200c900c03084028004413201e036007103403619000c0600820105030340851840d003503407510880349146000120128149140510b081e6000e01864031140380220020201207002040c140a49003219512440203402e60380c5903a003900071504440400700d815904c4500040e8070b10f161100450082d515039000e0106141016424020b104104049800303040b5407442d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 123849757 1250 123848507 123848521
    0xc010509090a021e1902060c0309030a120213030b01050a06021c0509031e0109061b0203070b060a2105010c08010b03040602090f0a1d010b0a0f0507140703060e01050f 73
    0x79195902c58540000140c45000361510800d0002c910700b6984d220b0030300001d11a032178060035011056661318950071580c01c4d6a41203461703625070005541085042d0f10a0098043c083d000c0e0008003855009a0401801c21f00300780039800c0c011707641d50301c01d071000354204e001440741c3d0403d4030804002d040d40d400201a55231201d02ca000c0c502d42041e4140c0308100e408140c08101b9501401080f1403a0404d51400c14122000f4024900811804030115402841c010405403c1c41407940d141000002c04d40103142002d4054940840c00740d402001c05a00507020100030071079440d0f0105240e4030b151130740d6414014940c2480d146007103540440c5480280a1448010420a075849040302c1d4450782c44400540c50f03800350350210f00003500942011380d00120240d030105082c010071601c5008900c1c10f001e1074800740d0f41c17084042102c0c0303d41c1a1210000319016207140d0748074003c2c0003c00225205404500c03007040814801401c00036907410445915480b000c0340707520300a0134014141c01c0f2201c1400000382d428411 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 123851007 1250 123849757 123849769
    0x160e060f0403170d0603060204090b01031505130204030803150909011802060d020c01050a021c0515040207020a0b07110901171c090806130519030509040b0a12050d020c010509 77
    0x44001894030710503480303104940d08850161404501044c0c02400659100d00d03002001c0d4201d400340030030041c0b07000c00c80c0119610900441807940c400072940f00201e4284414841c10403440414480c0c6c41e5000c200000008043d880118407851910050a0348270b80c070f04040042c544c4000d0001040baa04042d40c4000c070110b15030000b0300c041d038100c846554840f0302030101c0001c0e0007400314a4240f5481c060030005001c066400a10000a400d960401c440c103044094108907007090f100400408800d1003042180c0c1000ea0081405d00c0c00100824111980c400305064943c4c0411000c40301c3c81d411074803890305800c10b00b015034050441d041c05100c01074148602150740f070101c110300303a4045003482100fa4249005001d540c014000304401d07180b1515050001c40b00640355003030211501c2c0306003003015a6540341981d0301c2c04490b5041d034900340752416050811014184080e40c41d5404042524000342e8002219545820303584580094000c2105010019080008170004241030080401a000460b5903613 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 123852257 1250 123851007 123851009
    0x5030705122b1b0e0f01031104150504030503040b0706110a021504031b05030c25092301090b1306050f190b120f010501030c0c020603130b160e060f04 66
    0x8060118102c881c0314480203000600038a00030b10307402c19000c0b00190313844400000f5009003618244180ca4030701c40110100d450383c54181000300001e110520028104280000c491381052804500389030710323521420304507442780d41b000361403040004160b0100980360198014210600d48007500700403117400d010707460b01c0c8800d88248801c036102d40001c0030180151800c4100504198401540b182c49161981d501e6002c1300882c000c84c450080f118420940b10412004070b403846502104055103004041d1000d01380d0b82216001c05030b00e8210360106094415400ba000b00000b5101003801c007840418003c6641002c2c0c43c0c0c9a6031030070248144015103408000140986042d1002c4d81766114295a6490780c0407680c1069001580000e460458145513000c0c0138002e121095682400342d903250019002c41b40100b20728000f286407041e06e41d001d4039010029503805500041d604c0301c400410f940d01d80c1118011940300c401c0b030741c56802014070701d40e1080c1003501038030094403050b24084212111800718001c0e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 123853507 1250 123852257 123852307
    0x150a08090714010912060f020301060e1504061b05070312050711090402010203031305070308030103110a060806091803130801020c010b01020c130c0203120a020a0807080402130b011b0503070512 85
    0x50281e05410401550b000036107c01940c070045450307503181c0750010001c526501040348a007a4241260706030030700204c115001ca44490b100c000105e038964411b00802000004203507590300801c040040490407924200c0346891055407081c0d41c6400030701e82442c100d0403500d8094083c1100108010050343c00004490b00b04400400b040315031000ca00d000ad2500e500c40e00014420b00d0088000000c03c10420120920780c0001c4032202c04040d2920412200001c0445401c0e0384022400d0103e211007410014180d800c0441105032032078500c07039a400901e228104e42c407a901d203139400070740300c511a1802c4c480c0248051007440039100c08010080028034056403144101d40c426541c90280001d05c2c020022110610556140c00c08507141912006c0003c0d04210801c1c00881d4a01c00010321461080318500c0c41158020004c2403c1d05030100d10000915411030003d05026031001140218040300390038402c0b00f441480110340d01c1d4040c0c600103040ca0300201c61005401d0f02032006190a0751010201d041c0140 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 123854757 1250 123853507 123853529
    0xb010501082a0a11030c06060103020904021b0f06071409040209040615030501050a0905090616030b0a080f0c040501050109061d040509060a1116030e150a080907140109 74
    0x6940d42c00c5420715840000400240c10400001182d108150300a400a08615140c14240005983c4081d40300d214a0103211410b80100e000600950300990180a025801170b0005040402c03c4102c0060741003401e40710045a030151000d140c40d05810481582d0013540352410f4034010451b10b0380c8058900402d0507543c4550b80110ba00b1210b500d40e0b0348080010003001c0408040300200b42c074044c00529007030260314002c0310300300004910141e0b54000c0034059114070b0700608542d520b545031980080c031250b98540404d82c0b1105007061a665448905000e418400c1c094090b4030042c174034541c81d044c0f0300b5a46601840c209030042046a0708001d040c030864500381010801e850118040e90140c1300d0017020319500030715200c03e0051004000840d180703e1061101c5c10002e03104800402162405a100c0580e9003140c50900707403002038407900400e001c0d903070080d0121200d20f2000c1d8000d0b0542c2c00180340c03040020a940c080149002e0704000440090010003500c00c1e46841c5280024010a0a805840c107124 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 123856007 1250 123854757 123854761
    0xd03021e09040e01060f0603060b0f0703033801020c120c01080702012a0e010305010b1b030903010e150c0a08040611090d0302030405150405090103020d031b0317070201090b01050108 80
    0x616503400400804040c10f008003d041c0d203c080001d0320131240d02480002928001020038101c0b0700034106e4a50100b01050300b420440a40d4049010b0309100d520f00600c0c10f420800e50800040022000008070302d0041030848005a0100084c80c0a10320303000c0f94401c9813840c002c000c1206d80030071400c0070390f50280303800901903440a1080c0d000d003004410805820308840ca00d80e008c02d03000b62120f1480e540d19654181c1c0e03030f00140c0c01101030b030700e082c001e4100e00708040003002080d204040d0040402081d8001342c038144030310500028215020041309030240d0b000100c5010f000030344800c50395400512458510700305130150310000c00d40c40300288014102555162003000d64006171040d1202054028040a41e8010702c0c68020340740d810501c40d003405456000700501000201d0001c2ea07080e02c0d400761601c400d80c1e207181c0030450341c0c20070306800b5000c0c403d0142d88441052161107004509030300a8861880300c4404078400c02c12410000c0022046924000445000410444140341100c50910384400e403a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 123857257 1250 123856007 123856009
    0x60917060c030c03270d0801090209150d0f05010b0306040e0609150403031b0216090209241e07021318110303130e090601090606020733030203090d03021e09 69
    0x1038460180603c602800002086020142c0006c1802c1d003081182e4440e14940da0301c2c0c0a030b00503401001c94107580715060207500d29002180030040d00d42c5240c0c03141c003c01c808148c001800125407081c0c1110428490000c10090107003041d015804900348040010102817a0550354039071541080d0103480200e4141d0750100b0245482a00030308900b01c502915240504030968000c1d660b0004100e803115403a01d240d600040200462090302c0320444017404441c200d0202414803250300c0380c049288401c1031028400c64000d007600304049a43d801700300c4c0d411541d480315030040100d060741325401d1041441c01e280c0c919180c184e01080758501d8030340c000020800e403401d4000003419130091810248650078000000100090080d00d05030182100c04207a03125a40c991044509603080d9000c0c0c640964490391080094543d030700c0021555800c0d42e070b082c4507054076044c21310303130b10040c80b081c4400025000b10038410420018402d2405885c1941811440e011282151000710200d454280044440c041680422 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 123858507 1250 123857257 123857281
    0xb011a070c06030203090c010f05090103051e0106090608090a0314091503070309140a05120307030e0102040f0303081e06040b060c03030901140f090c0907050c07060917060c030c03 79
    0x5500036094040e842d2908030080c000d41049441c18418070521f560f00030340c2d500070001c40c00320f102c070f55031018504100ca10056025010181541818004401c1000e00c410040c880190191589075150b662880ca40500286072947c094542e042680105003654006504500f0041003410040e0a26466520000c0091003107103d06810358030080303000003040004c035030661140f988144241c443c242207020070540217903a00b41078007009003241e014510180e20280700300d0195038484880c1c40c02003940e000381c008142c00da03045540a80004401118180209034001d14025445000c115448151a004007444050144003824150007150741c2c080748055900d43c1c20845030352042e03c2045a0352403c05070380b02c80c020180d180d22121400f4030107012902090300408842d001342c3c201c1000341261a1050f0402c045c0d800043d08800c1403100c200b01b030303180300101805420014a099100c03440c0301440c01000c002c1c102e040c070540c0300ca1030700504c04208042060070160f07500680380864807a220380d00d444607042 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 123859757 1250 123858507 123858517
    0x30a140702030a060e01060b040b22030c06020312010b030709030b0703110c07030201020706170103020f0a0509100501020607020706051c0240030f0b04081b03031806040b011a 77
    0x505402044050001c4c0f0055401502c0108200002000720a40d80d010766608c900030360080c59100d03c030412501c0002c22146d240d21200d00181e000a0400a58940d07500b0011803856000c48056000071827002400341c80540d10301e00400708207103041d20714039155a00400ca80c809010003491019144081400d81d031181d44400c00705032040c505641c0c2c50340201e50301c41d55040b0a104c00c0780107102da11004140740c3c2c400c0742c0324076051001c00c5107804c041c2d0840c0d017008142001c81480c1074010b01c01d5207000505549a0400900440381000c160460130300345070009080070001400c010944d130140d002000015840801c90b070b14001401041107024107187c070030001a2240d030350b1000762003d19800e11000c103c40d8094515940026040071355a118038100781c2c81c2030f40740c0740c07102030100304080780711070089510244110fa0051107860410316145184803054042443e8100341c5030140c2c8040108246840d441131040c0a40d41c0001c002c02c1d031441c0664642d00000014001c400080700081882d000011458055030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 123861007 1250 123859757 123859759
    0xf0c031815091a040e04080304030c06020f0a02070f1d151011070905040b0c03091c02161d0c0a0203120c0703032306010302070213060b031b0a02030a140702 69
    0x502038001c420018204200d81c065502c40302c624860b038940f100310000c1110b007180c422560503001d50f5030b507446038142508020310035414010710441c500001100d51000f0144004c4084e111902d50403a44c600902d0050b05400c4060f0b40d061491090120b242c06074850721403500c00a01102e0b00d0b81d5100164041e107034081440ca904141d41803461000d2903000304100f4504103203102202c010654a80c215000c0e1401910301800e109641d001107646907405800840c3d04c442c00000b00d401c6140803903a095103c07560704804000581108059464501210150100038610700c41c2c0b2034803910b1100400192903d000e401c048880800064a0404900074010b84112880780701c61400c0301d10300090b540c011544041c00450000703140c0f50714524840d0554180c205e1802214242944554540006500039440140e00b40c1e800026104c44884030211801028041c14000780c080c1d485e0b041680310b4406041150b18104044141840300118460303000041c0c8030300c11041d00d8200c00e01c520b10f50340e01040b88540c1c1800703 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 123862257 1250 123861007 123861029
    0x2010e0d02031903020f0f070f1505090a0305030309151603180605010e06010e06071223030405011d030a0c020609010c08030f041407081209040b10080a0b010f0c0318 73
    0x10f0003456004031703e4000a4519400b901d01483c3c0c3c0000712606c401481c040c80d0304c0d580d07014034180004d256051090408e823200703040a41c07034402d0040c00101d105d40e241d8001c0722240c0c000000c111a607241031150018868000c1d04c19079081c01c004404000d542c044031a60410155111a80c800038405089030200711034210b07104110a58481c03a6401c0384441c2221131a021811181316500c01d07082040890b10800e812401d040c150340000300d0204c2e440d58400500d00c1c00300b00420b509245004003140114041c0f4410784c00000d01014030303002c50300c02c3d04e200300c00f80405820034041d03000f10b00d42001c00a40f50703590490718241d440c844000107a4141004c58009481c3c10304c00310812602d0300d10901e4003805103004280d12542d5070120140d49980c1d00241c045c2c50169007200400d020900d0844002d08107608004201280900107200403c1c0c4400b0796103035820020301c2c4a4244410701c001032084110945081c68480c3c203644030150054031000b142c0c08001d0810021803035240e8140303040c42244014200d00459 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 123863507 1250 123862257 123862303
    0x305040b0d0b150703090e01060807030b01020f0d0203031501080906040f05120412020306090d02031204061409060403030605040504022101090c170106080c03190c0f170c0a0302010e0d0203 83
    0x81203e01d400903041280440c2401002003001035844850034103c1d05c007607640b04503a64030710380110041c0525003513040c198401d0781c000f00000402401406840741d0258001c58072031902842c1011110b0075442041d0510415030203220202c8004645180c0c030239040846007100c0401071511900d41000f03c00120305180300401d000c100f030300125907001081b6008804940c003d0303c0d4145080c1d290340a040401003d43d0040041d08201c265514110b1341c4140181d00015441080d86a10040740300100c80c42c10b03040d00030700200b0003019010310480001d06820341d010001440c00e60f000c10a10080d1504848079446a0700d48101c50f6402500940d900681c408038072290240d803104016000c00c0041244407803542004001308400790009408030001c11300034010540c2002c08a0304900703405071200c064a032011400000b01d013140850394100001e005179000909944002c00c005424504034480341c61164568010400150307900107010381c61054200c5400011200d5403000924080e02000960340b41460280 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 123864757 1250 123863507 123863539
    0x609020405031005070816020c0409030f080112050312060d050703030806040f0b0f0d1b0e07031d06060402030a0e0f030901020d0807080f070509121c0203070305040b0d0b 75
    0x3610480754142c00301d5412840010710401520307821a008800165800d00141c210529041c002101c03001c24010348603400c81103008982131360a55030094001c110201c03d240f40701603102e20f0090060885030f0301046c540385541d4685440b0711507140e403046091f01f1303040810350030365401986506036540309003150f16080c3e0302e281c060314000b01190850b1090303142908d48190034080d4004c41c0c0904030014200d000d003201c1a02004406065801d09440c82403c00400d40c4035100600364000181c1b18040790b034202c40c902035500805440440d6032001281e91002040d601f04040000c0064100104840158032640c0e007007595001030102034806031a0344914070300442c1c0b50a0200051016813030a9090b100a120200030948017001d080d02c0d0f070f00019000000245d03100a02000194106104e490440e140980b000d0010300c014112801200458004c44648034281c01503140060030003480c0c4c005541002004e8402a002e8015442403141010000820014041055001d01c007007840081c000e0589200000d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 123866007 1250 123864757 123864761
    0x80d0206040605010f08070b0307050f03070c0506130b1b130609090b030d050a03020304020307151e02010509030d02071505040b100902090d11030115080d02060604060302032a040609 80
    0x9901901c24515080000c6845d030510a9008142d46069004002c0309107415600c00079580f008010404124040c002141c0030b2101c58001c501440740760382e800b90f000401c4e06109091900c0a4940d0260b6640441010001188481115031181c002a42188641c414a0b400d00907482955041540c20030a0880800d04a0300000200256501c140c0b080050f80390620515685250600f010f0000c41c1e4184072a001e45da12070b80081d5400b0344042c0030344000d00e5032403a0400300500542d91070b4000c2610801c0c4412088500494180036030140d00c000e01082c1407031744a40c0d0312840303a800340d402034940018040c1300b4400101c0010380860203d0701e0800c600d162a0405100c003c4080c1d40c0c0448446281030005002641c034020b81b080d45000030224104000c480e5aa0026900c0c0e0b909070b540c1554031000c070b142d11074902d0180600240b0b07140e0b000c3c1401c1e00090350b00908002006202c00e201d989054000e20241e1000900a5012641a690050011080098940a4541204020b82c09420a003011814100319 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 123867257 1250 123866007 123866011
    0x18041505010801140c090105070f060f1104030b07090e071b05060f01030212160504020706200c0106080106120803040302030f0a0315120b04170d050a02040806010605040303050703050a09080d0206 86
    0x50b580f5207041751510310440080d4421843c0f2070b8000303841071084401040680c284040010310403540083d40c144000c98800c240c4a0755000b802c010309001c1002c01c24045551445603001c0034901c0c000c80d031a0708140000041710740207442801040700c1c080c08205400063340c1d61500098000302280c0541c603010301b1156828100340400c90140e2811014008402c0c000122408081fa42c0e600300010030742000c003444025004080c0940d50030b80c56250192100103201450903655607000030361a65449503452990958079194018580c583c5041400c010415a40d802444410307400b89400c0e0703503912203007400c0b0320b50301402c5103100c0409000203031464065003560110352005481e16240500947e500e8400344809038008000e00140101d500040000c2d2501105200c0b84209032501414507105000440849104442d8000343c268001010b111020080000310700506651030845c1c5003d0450381c0080c0325000b40b28004042c0400441d0301403265003d0040e20003e00541000c82d24616041640291781d0081 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 123868507 1250 123867257 123867281
    0x1090c2a1209030c0e0403090924050a030b0a02090105121612050601051909120614010905060612040f1a070906022e0603020a18050a0b18041505010801 67
    0x7101e001c0c1000740780924001422a81c1016050109604c0c1c142c081c0700c0c840e0001c00440c00c0110200c2c011411004910a0720003186e03030444c420704948103104c201074043c0303680e0300070a200390005282000082c010010341a8070160388500582c6030841c04005a80c14001e200e250803800c0c491008208007446102c552500364040340c0e581000031642c004c00802201c50580b691400180104582ea803104d58800007880941d40c02c0c903040c02c0031036603000a03455001c0804800c803400c1d522114004118020f80881601400c4405001c219a090a000107400c511880d80c0c241158a111400941800500016440610b070404070380103008203013120641e4540720868001010070000c19020500c1031002030501c59042d516511484804c9003c1684190a4a4407000c50402d03030b140c1d900440141c0342c0000880040004180e038003801070801c0126001d0360001083c2c0030090f0b15041240a0940e2010001e41c1d03003514002c40212543c4545c1401c85506110030070b800c2c01c1500b00400042c0b01841588a2002400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 123869757 1250 123868507 123868523
    0x403031d060414010507031101020a090306060f0602070e0a090203030a0323010605041206060503010903020a0314070b06040203190c050d0b0906031002090607060c120b04090b01090c2a 81
    0x11240c1000071a01a50098045103003400c00d080300d45502031401801c0050107424504001c07042082c00c603099a02c4400c81000050003c5010001c0082a000d180040c01d0202650000b40707090072002035075048117101d400010000c1102050600902d5880019441e80240c1525668245844060041d1500c00b03094490036020501c409070612805c090a81030f03031540d90311107140c90310302200e24514521240c000da8420382c2d28800001c8a42d02449403403120382c400e0300585920402818058070441c2c0b4003c5840720900b0410480c000600560001d5621900864005031241c840c0e0a2000a0301640c2c09a2068145040d00c0c030220305030400d02503c01998004014030901d100c240500500c00000c2e01d8280e0564800d07101c1c29119805074014240c1084051304050902c2901d444500c1550807200c41207000c12003080407005510130f00d0181d00e5544000b500c05000c0d11440d50b442d00c042e1941445855142643c40c03080c0c101141c4910320201e02840d00304143c3c02001d00701ca40c134481d44400740c88203c030599 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 123871007 1250 123869757 123869807
    0xd1407290c070b1b090307030b01050108090f0303071b02090a05040507120807020904060b060d050708060d1203051b070813060201050903220b030f090c040b060904020915040303 78
    0xc03000070860780b5050340701c185907040344c5070907404c1d007820300500302c0f00c01d0441c506106180c2a81c404214190040d03002d92800c3c082549040005080c04002130704040c456000824165500c03c400421070390441090300e8100c405201c2d00880017544240c80c2c6009501079111002c6c0303c484102c64000500440c0100e050b074801c01d9440742000c0c501840920020002c101c1405003c0c05840e10b000e001b0b03800780c007407440800c01600c40000114580d008070701480c1c0060780c07002171080030f0f6400b01000703600c01010740c1c22000315025a00d44180007000101000c041507103580004030003404c2000e4900d044010070700d203191030b624a0310381036400b03400c004500d401c034602c02240000d10720320502400d4000e060f00e101946c90581c61110100c07511600f00341d007500050307441c44001a101090002540b00c0c0d40e021002e184c9a00744400400d040025805803144a0340c1000040e4049036039100441e403145000326030044c0d13508030200100ea11560b032442c89406410012600005154000c0c0f0403a00075012100014016 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 123872257 1250 123871007 123871021
    0xa0303060504150b0903011503080a0e010201150306020d0e03130302270115050f07112107062a0609170f120414101a0301020304050d140729 62
    0x768480c2d95040f0300100c550344104003094010004020b001c1c40600040b500c21031080c464405080700d588210740041e40040d450703001c664400000c803840d010900c000d00c0500300d0390342111225451400003610603903000480380040c01c826403000e04917410a6050740c0d1030304180d03601d26002c2c00c3c01c0e200c21380c0509451308030001c80c0e404001d60400c8001c5040c082d80e2890342409103121051141e04514401d0000400c000720124400c140501062485114040340b00c600b400184402e1101c409100c00c0c005a040440c054941004505c07082a81e96528025001916460300e08050384c40d0740400c0702500403141c1400c0f080c05040e030460010180203074060403451180504045040c45442c40d1881c0405003030211400c0340e041e050415800c540640311481a03841240880f50821030040d842e40c035101c2e03507400e031034590304007508102402c0d5108400850841c03900741c40302c0f80c8981a0700001c10400c0494451107910300c490005641c039154010303007100c1d540f51f0300b4003101e2010000c480e40785600e088100c0c009411 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 123873507 1250 123872257 123872261
    0x60f0516210203090a030305071b0b030103140c03100c020111070501060e0c04031e020432010b0f030630060105090a0204060e010f0519030204170102091c02030319020a0303060504 79
    0x1314030405480325030b01a1a54400311890741040030304031118041800e03081b014111030f500380c502804862480030356951451a1101ca030690744a202e005035040300d5040c1c103141d035004c1100c001003111900c010451344042e20040b801002e628151008601002c260034003440b0056011405a510032000704801d40c42c2c01d51180210f005621000344071646c180035108503e00d141d01c48610300c2d4409040400d2045440ca034102102c81054034850011601070301071703698900c06001440c01010f9079624140781212110303d124981c4130082c215401640908604910380c90319140c0c10b2a00700701c0040300342c504021174040f42d03244c480c2031069a22034403500b008118020207070302c00c1700c0440d46640c8a002e4020740c0c0c40c004dd200d54000d0014001408001c0c4031a07000034001801d000f09500980d5401a41d450403c205005007066044020340c0903841404401c12903141c007c0b94403190042c402c400726894ac0280700091641c400c265942130060808004090000e4000462000c0a446902c3c144403103501c40c814041 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 123874757 1250 123873507 123873517
    0x3040606050d2102031e070203070b0405060906160204020c0d030b010206010e07030c0c080c070f0f1d090109051501030b09011a010f0201020408070f0611030307050301060f0516210203 81
    0x200810080040c0d045032001c00700c04210003c0e0069905007181d95203110341c148121002414207003000681181140307403c0c400e240c094680d00306154145420240454402c0c00303800f0035103008510004014a034060054284005594000d009550324002454002c0d240d41440d90040040b0b030509034014a90b60000c9900c0e03068601c14a6008800da803000c40441c050401045450f0500400e008240040744201c0014000c654140300241480e80c41c20035a41900b1056501c01c0d0748bd400c14640070b00c00e440c285045c0c000c4519415007001d40c151946840f4030f00521440800410905c136a200c04503207004561603060407203004183c0060035984040c40e03d0300ba10000303002c030340d1400c0405155804560181818041552040c4001420a526002620700e84041d68201500540d10020700300806075000b107440010303022003400b42d410341c14200c0e0007410390700040c0181c905114280d845600b903d8481d40544508034000302076114940424100720001c0564622400f5000050b03041904440380000200c4d1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 123876007 1250 123874757 123874763
    0xa020705061501020c0f040b100305070f0e03030a080601020312090d08010801090c1a090d080904050c040303050d02030a0b0315240a0b070c08071403010f0b0102060a0b1306060503040606050d 84
    0x1c0300d01800f500300820000008051a4084c1d80ca00752308080703440340e0f20007045207400d030f032400201d0f420b02e0540500007081c0300003418204580c60201d00031359107000c404e4809901007402d003c4490f40b21100142e00f14003849926501e422264010040c1d80364000481c1c500203c01074031400e1040e41c0300c0716034600b40e584918000d4010940c0300070801410f1031100c500303007200041000890a0030074041c0054089480c03240c003682c0942c404162581980381c54401c06070481940c0c9007003840c162030759030041c2c294025491f810030090f0380400001c450700b8044d003011850f028000c0554990f0070700000c4543e43d0310020f03507041d080181c411071580580c1203c50b01c00084100020074240340d052810300d000d8076030b038010305e811241c14100c900c00013040e070010040800a0841c8425071302c40c40450300245401c68084040c0038220318181200b489080e60040b40c0950443d82120300401c0704884040415540000c400012200728900b100004031154080091800381e4410308091040d03035560400c0101c0b4414007a405 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 123877257 1250 123876007 123876013
    0x9010b0a05090609130204061d010801050601260a060906060c060506040203150405060411040305060f09030414120a150204050109080105010b1218150603151005040c050408060a02070506150102 85
    0x4900201e40685d107400741035200034800f03c1c1040c1c61320790001003c1289094103000b402010700620504000307000301c0b54400c1003807030400b90030a9901480b824400c401c880d816040c130201004165011819044180900a4150706001c000d503945401482c180c031030394043c0e400340c0c0380102241c0f20f480e250007101c2c0294406000c00d1081c0c00c01c603040000034900a03003542d60007030740c44410060610803403010340300440c01200580314034039082c0c141010509000304000c032160000c00050050420110000310101c0c0169942c9805822110603246004a01301d00078140001c0020503208455840d00204140c81003a690100d002d5907030038001d400e8400a0042d80e05117202030001c0c0b60004c01c11454240e002d0301c5200d801800750940305840d4200080c01e02e0300500c40031a44200080741c04e080184428a030056040d2020a140c4101c0d404403a83c0d03a405440e04c9552207845803e4214414003d440c05061580700303a484504202c0000d4000b90300c1020300f21194081c80f0000b0341c4900300040f01d040c0b202c030180c0203 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 123878507 1250 123877257 123877261
    0xe090d0207050609062d09030d0201050403050a0c1505010b03010f06140307080705120a05010e0c0304021f0203070c0806160203040608010302090a02070812240a1206110309010b0a05090609 83
    0x3040102c1d000264552040346600070740038404001d0b64035880c100107907691b90b580d4411054003032505040050150344207680c1060240400a076201d0201c0c0ca1203002441d220000d40390358600200343e5602c40020070b001700e040030008a02c4246c040000c5040360401c5588140b038070b039203840c143c0f08041000c200003046130050000600d0580241c0a66500ca8400d140c968509010340744c0c0c00c0105402138803034240031035580c0b0050040c00c21b900780306a0084c00c1d5400c2d4900f180317020750000308024080d01e1007050a900480c056040c6900800a98080301e81c00710f10b618029454108469698a045941500e40c03001114080a41c0c0d0001c0122025910240d072003051a03803c5409001000d4006082c00501c0c503420088207010401d40c5000d4210034580c4015600c180c01d001103c407900c248800c1c0043c002420402c1000001c3d541e1180f114101c3d4604c41560485200d00e0502400900c0c0c0c03d1901a420b00000040018614065002c1500845c00300e551400c1983c440f414803210b044111200c030b4000b100c1c080 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 123879757 1250 123878507 123878509
    0x60916080a0b0d0f08030103021005042102031f0e0d0306030c09020913060605030f1b09010c05010603020a080307120e0105030406091103032b0c0c030c030201090c0e090d0207050609 80
    0x21003444100054443d40d00030019aa0b03001078200001026150440007100500843c0b07404284015800000e26120341043d042c540291808108103150140031740001607014115202031200907404c85130811070340001803e118040300907110000381d200d0b55003d044414240c0602a103c1c600c25030b07402807036441015003440c04a40c0258884066668090064004980e1524190041001400e01651019107038102501e6042940001500120070054050030004050804400f5188484000d103440e040510550a225006003240d42000e03401554684010070303a42000001060401e00c10b811410b9868080c45040303881c42010041280024802c20216002c41c030180c02002003540500c0c00c22052070042c0000902d5640b10840c2001020040b803411b05480180e2014201d100c100180140070034070400034018104007124000a0030700046c2166001030500c00d610007802c240c2e0008002c1d0450381c54000e004a10300c0c0464072240d0900c80c48070b15070f1540f0b1000c14982d08813040076050904200f40c60f0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 123881007 1250 123879757 123879761
    0xc0c01061208030105010c0312050114040c0207180908090a03030f0f030c0807050705030d140a1d0706140f03070e0405130f03050a0e04050a0e0715120902120d08060916080a 76
    0x1f4240c0409c404a0789040c201c06061107614020b10100103807021180000c0140400d80710741c5003003202903400102d010002200440c1030342c245089a03c3c800615120300c0e10380310301c140c018408201c0c3c00c8042008040105900b120342c030446808980c840500400c14281c086007520300d2248140005004072010030101c0b8002d0000c0e146051041081c1c03800c10300d0020040c011194075011210820000c5824000c880103a4810302e103110340000514900c04a50103001035468001d44110030400c0241840c075804400c40c8015107414a40c2e8800c80ba55038240090010a031500482d64684210700e04004074040315002090091521342c4195002501c400c2520b0688a03038024000840034010f62000b40700882c1c1d90313071165900c10245160009108200041800e14001d01354020124101c007144d0f02c00d041c190011107500502001b034201080200891010031002c102c9900040c00d1803180740ba040c99841d811440051103018151241d042ca40e5038403003d00d50401c01c0d40f807502c0100b003200020441c050810703 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 123882257 1250 123881007 123881027
    0x1b0a0b121e010b340506070f0512060d0201090f0603060311060406021c02010204150206090115051c03030603240b010806010f0509030106080601080303101509090e010f02030c0c0106120803010501 86
    0x4d808a05141d42c182d80501180a0701240c08803010f4003c0e2003000320040c0c1140c0c2122581d126403903e00d0800042c1000d0a07071102018041c0740c4940030710545a02103a21031141c00303010380b0400321000c0140c3d5945201601404030760004941d000058000c9060702d04040b0261400c0303500540c0104440d24410120810400b524000b480855408000119558110b805581140c005683c0103118924001c402c803801c403000b1001c0740241602c40d900801881d43c400320404148182c1111742d521a0010380b40a9009040d2a40000e260306030070081109070700512042ea95038010040700c10f02c4072580078001112201c81c11949103000c00d11006008003003d200744041c1903a2800a4000182d158907000f405140040c00d9001000b158000000c2081d1019205200c4008141c6440058408003100c40007502c0700c41c03d03008070f80c149681d07041c240862075401d4120391403041c0788510441d5a1300301040440c0707180d40f114110700c101c0d6007803036400644407280c03400035209607400100d000d04607420703c0e00465008400d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 123883507 1250 123882257 123882307
    0x15180908090919230f10050603071e0305090c030705130f27030f020d020307062703031505010e0906040e03071203150501111b0a0b121e010b 62
    0x40024942c40c00c034903a2180c404c50a403d2a5501c20780c61031390020203e158801410f180740c1020900621000f45040041c010545a0490b00c40d500c07561400e50480d1440d88000724074103005c0d00307220700c070300c403d174055110600440802060300d00c9100361034249540c8404520455400c0725440840078001c258030b61121682c8910030700089010b0030314501c40908015001c015448400e070354561081015082070010600071094009402062540e00011b91039005034040501029180c0d04558140004000517420604c03140000c40203510341828000d0080468500700301d01c0c4075807081c000c00d01707600542100100500003421000b00342c0d19601480050144c58074422a9440140300541c0011080301c0c8070420180c0c0f42c0ea0010325118001c0110b134680c0c04a1340601c1c10702001d04680c0341c4c2600086542942c2c55415040840320b5100741010070701800d0381c0d610080308241d01043c00d818451042040314082c1c8035590800d0300c199010000d03085506000c0c03007009140078041010722009002c10800c4410202 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 123884757 1250 123883507 123883531
    0x1e090709050c04080102180f0a12020d08070525081912021524040507050d0b0f18040510110403111c0803060a080c010903060b030a0501151809080909 66
    0x40c0c1d81d01813900ba40c1040504410130fa00e0b1100c0c500840c1842d13070009a00d07030000c45070503024900c3d200ea00140e1a11130306029000301b20142010061000c00c504640645510408665081c40080601d0b508254040390f1846d02c2c0d1800b8800084810001400042d540700e0340c80d241c052408035540c0c1c4107054007400f003141d0960040c0182d005041c1d0072007115602c52882e40d18031091f240100b00d8030b11001d80094031407500c40d80c078101c144100c85a201095402030580d0000c00981180004001102e000e140058190300c0081c041a0703c02c00080f031241e0301d02952180c8101d07001002c0c05007450003541d400000d89450181c0c00c1c0010008201c0220f440c4101d00805410031940d0800350300c1c801081d00c5030303403004c4d5903000002003409000d0900d030340c10000802c4018050040440100c0c0000c1c003110586c80003a000c00c0d2030784082d126a95060180c0c2103010341c460300030844a540c00c106918140d64512606449a08070071020a00d28601e005c2c0c40c504945c00480d0340e1500150404003e100440a03003d01c800030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 123886007 1250 123884757 123884759
    0xa02190203100606020708070915031103010b040216020102100605010206040215091507030e0102060c09040c054602030a051602030a0b0109150503030301050120030406081e090709050c04 82
    0x42c01c584a600c024240a502802e0441c0c1864071840c60280140d104540c07040c90101141c2081c0500020141a698400d04203030015400600090240100c01c10595115100048001a4010402d14041d840b4801c0e000d64248050002c01d48084804d0b034810b00d40581c01240c00100145003070b0404420302600c1c1c002c0a400c0510b071402103000300d0f50480c41c85142100006540e000e1542000800c158003038244010315051510a8111096018411a1a001d5500c5007801d50b00c05008034182c4000240e00f15585200c0c0300c1801d01018144584001c41105038454401000c0080c088120010103240c550010f510b012000c100848196120103011851518602d2242d001640c0c18031160380030502410381310403a5410150341100308c41050041c000c2005520f20100601d860110a40341143d80900340894107220308100d408401004e03a120404501000030007007000c540001c900c90181c4d80da44410340461540c841260762800040c2c507194481d0b8402c6100b0040034000d0f41140351f00018003c3d400d4142 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 123887257 1250 123886007 123886033
    0x13050d0203040f1520070801090807121106070c2108040615060207030b040611070602070302060c091e12011a090a06180c031b0503090d050a02190203 66
    0x119152a050006030400070b010090900d80d1065440585020701050042e1608600042c04d0006100c3c3c1c112400c0804480002902c0780a202400080035080000c1c072117951645081d01c456800700c0b0b01181c100403400d1744c051010b03102d0303406104004a8130006200e03503102c1d01000e60b4030741c880d1038048416140d01d061042034440030620340c03c5104266120740c41241820714042c0c0030744800c084440200c00400d030040002590001c0c1c820212500044a580c50307031034506101c07000c3c100c001c01c0c086840718001441010052203078002c04806010307500b03590391904c46400598140c0b280c82c0c98264003405c028540355030190415640c40c00707650300a0071070a50b0708a1a40301c40c2924a401c042e600c0794080f40017295214148051105d911000031281085a9420b0040c01c502004140440c410380720b640d50318849146000c1d0384502084803121041c00681001d80318010505e500850300d070780d0540180c02e14407000358040c1054a440410a402070410084200c102c880a880e0ba264180c0c1d05104d400035440c3c034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 123888507 1250 123887257 123887263
    0xc09010b0c240717060112052e0305070801050105060301090c110d0e030f0303060d0305030709080312010302010f0806090a0b0303071a01061b030e0103091a010e0703060e010f0e1305 80
    0x244180b1500c807541c500041e01605031134100c0414282d8855250800600d0380c0d0200d080314002940200001d0316844001003856020304140d0268047e0b8444105a4410030400c450001224807071003c07580e5058498508d1130a8910078031402c0d800800034001031264030041d8220b42000219031900d81c84602484080c9031812900101180104240c1306000115040c107200c0c815031000c00e200103600c0c42c00c0403004141d800c5058030010b402c000e008808542642c1c421601c0783c004052120499854807084178001c04021000c1c032003280032480c441c4134003191901071201c46d44211002049140c40303039220104040a0075442e00240c0d450b0004104410003c0c0e032000802d501c03c014281c2140c42581030041c00341c500d070b1585d00c2e5480c840b403d103844000069800720b62000e044c0400c1c41c020510001a183c40e0f07000f202010258491041040008075401d440d12841901c41c00040d40c05000d06030340c54101c1640007100b03015605400c4004541848288021076605401204411103080040410340321581 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 123889757 1250 123888507 123888553
    0xf1409030a111801080d03050709030506040b070f0c0302120901090f030f051e0c10110102032406040806130c150503151e09070306270e0c09010b0c 65
    0x2c0c590400403814412424142c80d1040b001220504075222541005c034103da540494440741000c05462354005a01b1612a248070402913034040c0844042d0704052903e01c09001003140c0780c1000860810070605540e2152222000382501038014101030211485404c45540c4214901c2d8140040618001049071829030721b800214040c20181c0e15010b40391811034204002d03c9900d050800341c1d600f0101c076100c0b0105491201031001c8030f15840d05503464030155000801d1140f0034005510100030000c1c4000c400607104502a45000e4010440e00380808201030b80c002d5004016459016030b00140401141d0005c0b000b8a07030250060702d040c2983c0710010105c0d40c0c005003191001070300c041f0520001607030404030b08240403400c80b00c655200c500784c6400300d10301c0c1c01029118841c085a0001c911404d0081e44150041d0601a22051b05014440d400c90a075100219140c01403a03c2d0002d44044020042000a80e110000b04102e409900e02150310002d07411420100440303014880710404130b1b0311b907000850 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 123891007 1250 123889757 123889763
    0x3030d0605040b010822030c0b09010209011806050d02030901150609061b0812070c020405100302090f0903031902040504020a080f34030e0a030519020705010f1409030a 74
    0x410032500780010b0109588041c0845410b03c41c4907801d01940101802c8100c03025049480c0010b044691401c086460700420b1f5000f50001c0110014407808100c1900140f11a620a881d045141c030300d90f182d500e1400c805071140c840011018003005031214a55002150000b0b03130b6000106403069002a040b80007946075000c0400300d0b0810204108058009200c200c903028000e940c2244820542c0307440c1154401c0c0b6070400700012001c800038070254015004c1104c00364002d00100840d28107100ea001c2610180d000580c842c0910200081c4441c0d50300e14013a1061403808040c42c25501c03212443e4840541403914070306c110b602840081074540f1944040c04801d40e40e1350b12040f2a08100c0d51080c0c0740316025020515880300c1e101190010450a214801d900144c08032011040400318000c030010903142d060701d521801811503000034107038402c0180c146907005080c0e0754600b084512007607075a42c10f40d02c65180403070000030340054160f0065501d80030380404900d9803841c00d402c00d8002814507011010807 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 123892257 1250 123891007 123891011
    0x150a050a08060121020d030c02061308010510050301050606090405041a0910050c07050a030f050f030103080705010b0a08060c030601030204031509140109020d0206220303080603160303230903030d 86
    0x4000800907103403941354906680000740c400341c1a54021031401684840040d0a011586178200f046464900481c4c0307043c1092030225202d41c1e00d404815000c2c1ca01940c80000c43d4200b403070049001d15042c46454025940201203a1420322107070140030290200920945201c1042d6078403000000f60b142c1c81c0b0740326103003d0b8041c02c404444a2400c40480b9005407511020213024028400050000120410f125405003001c040007106031504942078441c11942c00f0043c0301c0840000100318250001e0180c081c8550300074046a0010b034180519040e01c1e204003003295203d0f10126085080e200e00450f0801c6042c5400344c500fa03144e8842d19141603103001e40070011aa20741d9440d05200c0c86e280400c00001c4108000e0150000f90f0f00000c110990380c41001e840303850002034046034102002c000300400c2d0714292035031120655904000d000540211242e0340280541e094034251000354500c14000d503585a00d46d240340101c0d880c10009040c2d04c01c1d00020380d19108120000056800b0000b03014a00c10500780 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 123893507 1250 123892257 123892259
    0xe030c01020a170910150f090203040203010f15090902010210020724050709210b072303061f0324060201060e06150a02010f0501030803040203060717150a050a080601 73
    0x4001c2100e0301d181940b410f0808514203000c000720002c21700340c98104003420003041c4c010b683c07503150210f948503038003082d50324465410010b08400c080c1c005e188514000c40080102c1c607499042c105c01d560421050003002c0c28410400e111225031503008083c0c01e801032040311044e16100d4071890490b400310704207854180e01c59916a40c146100e00580a40c00c515000602581c20000e501402c0b80d10140500c451800c02d403e440c0b81c11445410322134905030703004011030710641008038000e0501b032036401d4075080c810364050280000d500a501145d02401b4060521408028410703001400e030010101c0b480b00b00b5881c0d0f2600400c0f41d08118500c405800110840c1100758074000c0c0c041c1c2180c00e203510000d0001c07184000c2203590b81d41c104607410041d0551801c2d07030303440e11485412401081c50500b84a8400e00d008004824030100700040c41c441c1c0d100346d0807128a0303140e041080e00d0031900d01c1211002429900c0000b10030014015020a404c00c000d070030005031030303140c20018404030000d0f00080755039405400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 123894757 1250 123893507 123893527
    0x60f0501031a07020a0203031e090904030302090901140a031101030f0e031c050112110d0602040b090f0105031303140408060109050f06120d030203150603040c050f030c0105030f09010e030c0102 85
    0x22601c0c0c2003c1c0c0e5000424286003168040303a1240a454140c1803c00824888101c40004410480d5600e4000502c0031001d403501e460003030000c3d00300d946118010f501010000c00c01414015084014442c01020b0151580c42c3d6607441422000300c449060426440d02c1c2d4070359054009005042c110254200507540310b40301ea0414442c0c10320110140307110141480010449010203144120f4500e40003d500d4600c04810008146000340e58031005146d03074400140000e11035605030180080724022140c00c003aa40c1c0a10044505000984401040039130600020380064040c648050b0b0a00f08000c81600b0300b07a5800c94141461001d030700c00085940c841003080024210161801da010900301e44101384520303442d003c1d9030b0b103c01140c0110249640080411303c0030391844450507661074000c103006c0e0740c0d00c3c05140c82c094442140c810b81e07004080091160764a8940030031511020501a07440909641d2840c1c0702800102c00503040c007d4555903201d802102c08800d00061031148262000540e0390340d0184 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 123896007 1250 123894757 123894803
    0xd021308061b03060f12030d0603120504081915020d0f050612150601020c150d0609110f0706020708040f18050c030a050a1b031a0609010c030804060f050103 69
    0x60903000c0c0d1800e03058912880581a0083d0780d005007081d148041d001440c10081906412801401c0c411803101042406943c4147c0d04401d0550b0f02c101743c0030203052140704056405c1e00583c05048202e802081c51007451100780440c1e9000b50b400781041d00c0349592100500c03000c07a80641c1110300100d4803510101945821409544e030802070503201047c2e824640300d075075920303040c1000101c10301d8a030750307808102c15a100700320388003013041300038200e60039550010705400c035a5201c120b40160b05c0e810503a0005540e8214404e640c4806521030b015403070407089107100b10440c3e020044c1101d0322a428445200800c140c1d0000e400076001103111500d11038245000034032160f501143c011101030800d0100220100c69609507508121414004030700e83c1c036200c003581e01a14003418891062100c1d24a00086250f240d002400307a0700703d4010306408000c011003440b00602c190410300d80400c0c0c0707040345000064428050704d640306000ea42c00054220068001c13a080d54000c0e4404c0d203002c408c0c1c21210448a10300c1b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 123897257 1250 123896007 123896011
    0x907060e030c0306070503101d010302031903081302030304080d0203270105070204020702060c1b010306120b010303110f07030609030806010e0a0312090302041508010e0304080304090c050d02130806 87
    0x4070000d090000d400c0001a40c0e5040060410040100c0400030a00c444032120b1000003074260040e5030289012060740c0e10482803400d00c030aa10911500c03601c0194844401e1844164607010342d02d2000c903035108112280c0c2215440b000300c2e01803000f00700000d51740038184403014203040154050360751f810307415006030100e4407101408001c5040c849044401d0b41e0f00007013100c803080e50544004da1905da660002440360b000c0c030b02241035540600d6a603045000d11850081c0a40c90b42601c04024813501e8002030154400c450000030009020400148082801020700400d000030f071108440c005000703544000d05100b146c0d44115109a200c2a6030400c25800088260344040207180c4007061440e03490004010500a20014040240181c00d45540900c11104440030715009401481701d04400400e0a040c4801d501c0b03601825442d016074419541004802c0700c080b102c40400440c03c1c5810066214010403081100a062100c10081c14801014900103406650003021400c05218504a03140d81032a0300 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 123898507 1250 123897257 123897259
    0x60b03070602030c1b0a05100e04061a070605090106240206010e0f06012001021605120a051804061203020d020606040608030a0810030204092015071113050907060e 72
    0x14880702e000344400103800003100300d0000c081e6000d80080c6000c19104151b035006903404c45910a880b000c4d542e000071a400c0300580035201040041e0381e03842070348207495010007d910310703007000c116800c0855041c2e0045030b00008040000900c0d696a0300c0c850041c46403000d060034080341c50b0354a0822280d014084240180000c1c8080006440e14040c103a071280401408141401010204140002c80c1c2c0240700f4410080c942c021591500800c1048046181e40c4004a43c030703114802c1d01c003800301108019962440180d4444170f0503d40b506200b841e485008052003608076a5886000802d00900150144170074081d4000e00b02030301c5411802410000018030090146003003a004020a083c000120703105403c051803c030651f0345030708461040b0002182e1029620505150390382c1d0901c07410075941110000081503a5644442d80400d2100d614640d4070301109941d014045500070030b0008424142c0c0480040044c01c0c84041c601c81002100e00c10346d00a403031a44030303800c14401c0c982c0000907030302e0a400c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 123899757 1250 123898507 123898513
    0x6180303080606032a070c090b06090105070f06060e060f0306070905040c03020906030c0c0f0a0f29090c040612080301060e13020c100506010503090a030503180a060b03070602 77
    0x81103440c041c1600501600b050b0180c0000030001e5105100082c0280c040c60011018072000c2120300c0d10007010b0341220109032901c0760141d20005078002c10748102c4d0031507000905001c0c144000c1c030005507030302d82282d8000d0721504c06524140002413210701c40c80015000001c4030305d01c241041c005221100b50180d0302280203a0041050108040d0010104002c4802c103c070080380e4801c0c03020089000e40982c4186e0b9030031060110a00c500b0310703004805403407010401c004448200d00c6c101d406540d14511502c3c050310f004030078503540e0701041090040030050040041000118000b10301000c2c40804225420b0306503411002d48041d45241a024020061000c111a034001c1606030301c1d0800c4510041c854901401262641c0019685400c94513005010540e94115180e198500c1469229103030107092104480c90300300019415801081074078001c03d1350a00030850401c00356030070b07511580081d080030140d8811503102d0264542c1008000f0926206250104480d02001d09040c5040800e03005041550 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 123901007 1250 123899757 123899759
    0xd0b07030c080a09031706060d060b0301060201110a05030a0b0d050a060e06010906140402030702070806010f03060507080108100903090504090c1a090319030e06222108071118010618 80
    0xc0d901080314101b040c1c040942000d5500d0303040c0000d40e035104020b40e00e0707496428000300080b04500c0d0f00c0514100c0b0481d8000307101401c01004220320309e108512111020980030b0000c11062100b07540000301c40c4201900401c030070981a20303940c0c0740134000e01c070407200c0a4407111000c03000d0406105250042c001c010741402583d04010308801c000c1d650340803040c040d42d40840010b0701c0600c20090000101707041c0d800c0c0c44e005e503104c10800030048124001640c049040c4400308840500c1202924121660000a4603d21400541401c043d1105000c20740401546180100f810341d40d070b104091481d407140c0c054001c02d91401652004402d400d01c40c03030364290814080201c140e107020a00c903a810302c0c0400c03a800050441d103816112051900c1080741c01441c040b40e40103100c00b40450502105e400707040b500e030a043d0307103401032a540c000100545004403c0f80340d0003800200c0510103402d030184107002040310450000086a070087c01c0c016802020348143c001080483d820003401d107580d2100d130079004882 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 123902257 1250 123901007 123901013
    0x60106182402070e010602100e121207020607020a030519031e0902030c03070501050f0307050c0a03030621120f020111070803100e041e0f0f1101020c01110712020d0b07030c080a09 79
    0x900c00d041100c8c1840d6071a20752a059100c0103004440031803c000c0307031003922042c01c0001076020314400c9580c100503200d54000309480d54000100c51680030380c1a80c4061500340c082d106280b4205000304010245515103c50840c902034850b4603c00c1440d40070000200400786004251030442600c494a01a4101400c00d1140341d030300008407803c24031441c80030fa6827a00c2d0003104039031511484010007461b005a0342510b04041d407640095084400310000c1c4643c0c034000071010a10b1070f440580003002c086156109000040c0961042d28041700580000034100e055000c0094095000007000c940310b100000801401c020841810000380601c0c1002c40507500d02559010303503541c84600c58651301c10440c030641d01044031407092028056400190300200150f985441001c4c4804009a980540101105100300354812a10107040303000042c01040a18602100d82c1c2c1504204441a6001020b400811000c11402d00000d40203100070707a400144003004030702c014410440544240c841e86d0400b0f001d6004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 123903507 1250 123902257 123902263
    0x10f0b0a141c060506042901030f0b120a05060106021b0105070213181106271203031009110702180705040512030702090a0509060106182402070e010602 67
    0x1910009035103000400040000100d0342807818000b00b44525407200a41c04020b5182c10250181805607800e2000414903407010000e041401414245800c400200c1d560310f40c4a40c00c15160401c81d0b1000191a000d4940441e0148000c0e1050403819402050a481001410820640181061b00c0906003034803515120321200e00007039070140d04200005c0348031010b6640b001004012006c901c4000c0012000460180c2001210100d0a844135200880c04180a013881021514062504070500052400b250198002500e401d2100354104141c1c1c0803001f5041c9040000b18000c09401d00e0318504036250051140580b4040e01c0381d0262000c0500500c401a1542c0711010000800900301d010640d850000484090146600440c1d11004408180000c1c41000c401084150300944001e003c80e40c90100b11380541d00e080d034014520741e200c1001000114410198189403401d000b1409140c26034034402d000c1d04499210111a01e40c5061b00c0c101c815940400c0321400612800c0188010780d0b140a03030283d2 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 123904757 1250 123903507 123903509
    0x20307050f150a2a020c0312031308070614040803010e060f0a0e13050d0e0102190c0501140c01050103060e1e0309010302220303091802030c03010b0a020a0204140603010f0b0a 77
    0x4120340b19407246184c40100d050f1101c1141c202d05030b5842d81d004504000b07595501e603c21090181c092514010f1005080c0c00840c0c0c0f0689154a150100382065502e95501f43d21501094440956620902500300340081146010318051203040352294186901482141c0c00945207030b10480062030002681d803110b080c00c1040743c01004c0c6070310b2190383d56119590303e028030850090450065603032007400705810407180d4101c44403c1c1c0c200c0d2404410840784a01d2030038800e5019002c0f0f41500703000c2100b58483c001007101c4644031020300341002c10b0310b4403242c00d4501c207820031607007540c0383e010400100008004408417080c594146403a0464281100c0303484e8402e41c14800e04160f00040d031021681118140005041580840b000420307941f403c0007080100d16021764503034260154080d44034806140280e0307000d10036000f41d80703207103074645002415546e00c040641c009600a85480e403001d40d49501c21009501214690a3740c1c900e42402010300315030791100d4041e00c4a140c0454072050382c94446041c4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 123906007 1250 123904757 123904771
    0x21206130f03020a15061404022d0f130303030b01020102090109050108150a030605070806030f030405010e04061203020c0301110c0a080c1c0c03030f0c080a150f06020307050f15 78
    0x1800040790030224104008001c000d0824420503000c4040140964802000c40344400c142800014034442000300b03910440e519207503645c4803161828803910301e50ba040d1034030310340301051303280380600b5a28412407941240a1520b202c245002081003403603018003440a003131009100071880c0c035402c3c6c00041c0030b0010a018160401c02500b001440710704000c5680b82140d40000e1110074602c3c0e0320304c6c260014000c215201030018a8075400b14510b03040000f071461000e1030480c041d60a15081c03200441c0c90111035500e1540c49030311003c1c009410501c0c1c1d1319464059000340c0c0540b1400e900d01d42070509440c2000c0901c0c034000020400306030444008642115481e60002d201d55443c0480b00e85a46403a1882524803000c0280030341c81038442d50080398158106102c0c2c1c4040c051b00300440c0d100012200c406680b2408615000e0004240c00215400b040040746803240084c075950b15281007449004041e00702201581c0300003802014000100409901e4a0300400103014000351024050002d40000d803c40c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 123907257 1250 123906007 123906023
    0x30209012705030a110f0a06080103110604050409050a0302010c1404050409080c01020a1d010801031104021605030c03090a0801020f0a11250612050601020d0e060d020706060302120613 81
    0x8440406202907403030000b400c0050495010140e03c0c207050a015542038441442102d80d510400032600f0103982a0b011074945445030704041c4e20f0741d01d450207503904102607954084410000405c0c01c1d030301ca2140300c45080c0164020700702541d4a18002e421207800f801140e0501803201904e09095495000321001c2d01c41c00d485c0440c204210307140440302c1e400383c1c1d6041c038800c0d4004214110560f51101c0b4990740c8002800314218285500c0d001034420007800c3c04044c1041c2d0007801c00e85001d0805400800440310040e2103c0c2e08403036076071210390854002e5003d0719407a42001074021644d1a00300300c0f074400351074564021880d0400c501c0c0001618807c040003a000d0103158944002405da041c010441a03040703040e100100e20182c2001c10000401b540240408030300c090707070b00d2654840140b00380d40c81b4290607001400c080450b100123484809a01a100e0703400780302005070208401d000d0014281d0300d4402e4001160031790461042150f003214002041c4850b40c095010400810140c0204501c000c3c1c0112007 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 123908507 1250 123907257 123907307
    0x50919020f01032706050f011505191b0302010501061404050604050d02060d0f0209010f0e09010509060d0606080c10020d051608070f111309050c060d021b1c03020901 73
    0x200803400d201000c810710b00c40000d81c021080c4843c0d608941d221f6000b09501c242540e0721150300811103085954018001442802404111104000405600d94040c10000496107024640c42d840e4046100b00301c00503510350004116441c2c10481c1d800031900700786002c2d41400c0c00c1102180c00c6010354480d0074485d4054400317441c01c3d5180c03081110348101508200340000c5e080c90103810b003c1d6004005590014000301c0e0603441e901d128a881514a0100800d4591f1907444e0904109107400d0180503140d0041c194003000001a00781e10070b44008182076405400380711104820422403201104141066400001d046034180b64420700b00c13041403010381500c0c904002d090601441c01d003e0004000d04040e0801d082c0c0b0140201b03429891a200411a800b00c2c00204008040054400c1502c005060754408805200c1030719202002e040348944192005061059a07a00d80295101000e545501a0080c08444500c40c0900c0701001098240341415840c08203208002051080310341201c0e1040445119 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 123909757 1250 123908507 123908531
    0xb060111100c03180b0702060601030908070201120b060a0c051e0d03090606050607110f03030c07030209040f2a0b040f0909031710090b0a030302062e0603050919020f0103 75
    0xc461210350140403600003130314920f868a410840f00544540740544034483c00103006601c603004061480d40d100ea00c06080219582c010354080414803030b003841454807000c40c140030b0345841014045030b0f01c041c1d80c0c07000b810381075003407890800101400708044040d02080320440302000040080d191009850001051401400c05000405041d04065402900004c40e0014022541c0440201d078030300310b400d0781004a030b10701003560703d21031010318000e290481d640410140c605030030283d80c45401041c10240c5a03040d5901c81103100700e201c1c0001055407074158000c1041c0d000c2d8101c607014004103446a49010f0521014a0f2140054071482e90000d0729001c814007007612401221250000d500c03a1030640e0705200f54540070780c040500030551403a241180075441440c0100fa400110b0350135402414103500c0f911010864110003042c186000100000f12a002501182088008259613a800034040c1041482d141c1042281e00c81034100708800b504981c0541c3e2507145903910401e00f401c0000d80c01e11105 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 123911007 1250 123909757 123909761
    0x30409020307030f05090d09210b0106050a17070c0b1305070603240311040e0f060108030304020901090902280e010902040303030606020604170a050903190b060111100c03 75
    0x1400249809001005100303106426802086113010014000d01c600c2d42d9100403155a118000354050015140010400c680c4510a403068100604014407c40800b010f4840c1280020300381d000d403000070300025100c40b940764050540ea041d504004000c075003a042c141d40c024001201c0d20006000c030908400420801c001110150f100756600c07000392030055a468501600806900c2440c420411983e40408412120f0107107136410f5a138030002809440341e55006100040c111841c05040301d03c00d411b900f05400310208404e0b4002c0030608001c5550340b909206111b0305590684c0044a86400d0221100040c1d840707803405d1034044000c0207044508942426406c40100c51544848828500d2900108080302c03079400500a60f4000e032424003140e6130b80d42c1c00700d98034441150041c10b0310b082090148040d01d44d450003080011400e01d0300b00d0811a2120000b410001c00009801000814840d000c0c10006c1c4a001568885024209000f20b2424549125125443c3c071040644503030b5649c02105d4114065 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 123912257 1250 123911007 123911009
    0x50a080a0e0d0f020f0d0314070201020313030c290304020d110a08030403050114091902030106030206030f09010501050102010e0d110708071509050d020d1209091817030402030a0308090304 83
    0x406040340e65200c1d0074a0183c0d03035034400e0240d025010a03410310415050402e407a444140d81940e551030768140c800348600d0755400c581d0049045000410040c4881c403120b008500140d8001e46601500500d8028140040c0000070b02000010140c0741c03101c00040d40f620b056903403154042d40c0c3c6401c44542071900742032510001078116400740c544d00001c2a20300c0d00202820569114038001c000c40c40f044040c8594030b42d422680143c5ca6885182c031350b903084014107907071850948041c00110362642c4030741c00200135820481e481d00d010484041000280e82c800d004090042070b081c002040702b103018100194a400c40700400c00140144a05203014581040048200812188040d20352a98440f0140742d60041030200300400900400c0f000b04552410b12076125516070b001b09000d15030001c8c1d035683c13842c3c1243c011246045c440b03520b038006907100e0f0311b0041e54a41004410300d01401c0103503262082140120203050011088240100001030701c001891014503601410414186d507201c06000e031a6100c0c1d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 123913507 1250 123912257 123912259
    0x90c0b0c030c16050a03032111030402040b0f0319050712032c0307031712040309080709021602040e0703060c031401080c18060a05180a050f04050a080a0e 68
    0x4002100c90a18402001801c2000400829101c40f209082c001d8100542c1d14001c1e158442c032990400c000182c000d1610000c0b41d084400c10011710340702d24040e0000c1340c0300e202600000000000030001146868440c7d40d81c025130845840c2c20014040011a590700700d075462008180700c0b050746100500108000100c02000d1448071201c48640e10f18004002142e000d2040c11030f100301d40715032001e0405003941c003120b03400080d00a004080c91600e60000c047d2103406c1d54003aa0608110302c80e0a03d000c4d1a032103105030701070344034020380718a0641001d1604090394019182c0030300c18000b000225440b280e400c41241e0701101c01141c0c1b0540c8440c56410307c1069800101481d01d080d03000e66007141c150300300401d0340107588110021030381d90350810303a1103010502c2450ba03c0b07801d01f500384c004460341c40d87d040d410142c0600018502c40d15800851021400e049449071110740040c1005441c14440c01002d50016014001c6541410700340c3d03a503036442034814402001c0031400706e40d40c81100c2c03103003034000341142d0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 123914757 1250 123913507 123913529
    0x305190504080d200901030c1b1b08030f030c0901030b10180608040305091e0d050109060b0d050304120512031905010602030903030a26010806010e070e0d0303090c 72
    0x7450301e82140550300002d000d056090510030340c2542d20f103840300f80c0007441c54204401464054603000460040c1004803504080c0b003200c4240302c400c4040f206098848910a510106080e200f00030b9040c0002e00c1e0780d00030700d4941d04c20003030030b03005080c4081642d4210340d050350701c1c035214a500d50042c0c0c09041900d100b03540040d80090240645940000000f01080480c00801807440d16220200c0706020125005004154200500e40081c246804009a803090004010041000c2e07200000c4901c00188026680c80c0c4d15000401c00f400380d54452405840e0089450a420107140c1c0c2d145130310781c0030310701c40c3d584034104040e050424085c09200c15424803842c4051540da9207000250818840704403801d2a00301c62503c00045005e50001040b81d0400c80000c00440c00c02c12100011246030040c621102020000c00040601e5480c101c00b0f542d000c0c200c00006004d0560400310f000d265444020588010840e0341c00d035000103521a0040554800e8040c80d01080c00f03802404c1411040206510002d2110 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 123916007 1250 123914757 123914761
    0x70207060c1403190f0509010e1c050d051b07030f080a0e03010207120f0f0813050309120c100203030708040b0a152403020c0309060c12070c05090109090309050103051905 75
    0x11000d600740c44207200c4e5600d0342040003600c140f040300c0d14080e844035580400c01d4800c98202918114031801a4040e420000f041030003520b40e50320b07003068032490072080401c1c00451000c90082100340c0201180c511030004068941c95621203005040346e40ea0060036a0200140700d13100e4a01c40c4507121015840078000759a11820b524011403d018041040e070b001030b030811150703c0314074464150040400a5075551101c2d5498448480e80d502c2c440c020201c0e85488108441803407911010052008080d941c00504044d107808400e1000c10711120700d000b821500100200201c030398001c400c2e55049500b0205100070342d5590342100700180f5103401903441007200840002080c01e1164403100d0080b00882185210702c900c0e035000c3d420782c0107025006a480c1c20038408080907052890140000003c5201150b6120704520a07500c203aa019480681306484501c1081c07100f824400141401001884000c0022000944005003203200c1400307081e04168884010401000b41c2e0a403410661b444010100320034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 123917257 1250 123916007 123916027
    0x90c070f050a060606050a0f0e03010e0610080607080403020d0e12060f01080f030c0c040f02040f03050c040c1115090705060d060e0c0a050a0c0312050a0b0414070207060c1403 77
    0x5041c1e0a40102c41c039030701300440407546600c90015a17009140c0d0741c4440b40420008241030b41c5d401048044181c141d0350f902404403103403804212003806410040c0810054500782010325040c614014040c20900c140f2074103000000c0c0c0d0000e00700f400c025261805190f031001a500250b0804101006d0120f641705e144144080c203166010a103040320070401c1125089071400040300e8a070700032142c1c1c0030a40d810040503a1018206a042400b41d5000a600185082c0d11594884034540054000703650560100c14003c0c2241810311850841c6403031130800a05504003401403666030382500b0320b100355102d07a04010810340041040300300003030000180001d0b1500040507a0200a291902c91440ca401a030b83c045440d070506c0700203c0f440a001a95290310f0000c4a00f0305642ca0612554120100010079842c101c01038158840d69024690007100420342d008c0c03140800040e0b50740718070503d200c007548000f40400c40c0e4000841400700e130034a040503403102855080031000010001d40642c05800002207054038 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 123918507 1250 123917257 123917263
    0x1060b0d1a1509061e0c03130608040f020f0f090a020901140a020607110705030a150b04050c04210503070501050105100203070804050d0f050a150b0904050c090c070f05 74
    0x22074900214440302410380c0802c200008001c0d41c02c40441d03003403c010841c41802c081c0e00030014400c0c05e8142403003030341188400c0c400c55400a005108903400c08140030312554003d041f544000c151600c0c02410307a05254441103e08414400000d210b0403000d4103184003510f0f100300d0345d000c3c1c00c00101459158602030000d1800703507000b42052400035205000402904215606641540c3c000364010480355407141e400f6221009400d403c00c5a51103880700c00a000c0c1c0e01000241e040b07601c22104d949803a004094124261021500f076140f01c0c40c100000c0125649120007641c0071501c40c0491b0803c5000d10080420611036100b030040c049020001c2c80034103009054005178101c0320b090300d08a64502c0c4ac440b049860740111500100340360740c01c00042006203041700100680c40e014900d9a15480342654409180c00c0d40300d80c084501c0c416481d02d40c0501e08031031044040e002d00503034460b1110319127070703907101e0716690b241c02414425441c040101c1c4190940c0820b403000b007544261445405241401c00580e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 123919757 1250 123918507 123918521
    0xc05040b09011b030e15040b160c0b0c030406030b03210919080606280e060a05040e0c0906120606061b06010902070204050604061211030120041401050f070b0901060b0d 74
    0x400382881e00520380191b0341c0c01c0220b03011508407545035824502e1440710101407010124041e2400044c503503003c60f8031070101c801090721800b04401103a4403468044050143d0f0a000302c194401d401c800f01c941e510f4061b03070010000680480c601d01c3c4e0780300d004a0004e000c15035a25040b50046111190206a1031000a0014000c1c0021600605003082600e50700000340c11580e034070791002050420420a400002c5c040c0ca0300404001c00c11001203880c1d4002c201151404c400c2120030341c1c0070038180f110303904141c4100b81d001031040d203003481101ca49480643d41c0b005c02400c294000c07180040c00c010320100140540d007445903040240c40c03480d40e4416000300a900070410a901c5140b078980422200e2801d8400d44088800c042440611460641c545801b40707100d2225841d015501d407400007185500080f1044c07040aa0075121030b442d2410401e0f009000e0390f0528580341809010402843c4d0101e40d00159090390798400c1e80d111051307550741d140a01400c515800301080f05004207500c208284240c201131 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 123920863 1106 123919757 123919759
    0x105040e1302040c0810031506150503150a03150f0b030d0f0e15040b070302190f030e10081617070e0109090c05040b09011b030e 57
    0x4400d4600c1100c048140220100080c811480c042c4504018207081c0e292139040c2e03142c803007031001c04850f10b400b001d40041d001c2851410400603503082440640380b05034450401104ca8400901590001d0f10f55260302120034041070102d0a01030400012a5040b020010301e4444d0007107808010203d51100000c03c50701e4542c0520342e921b007040346540704801641c940030803400d82c200060403410300004603840340d48413840c4080046d04000682e41510087d0420650303800d41481d05a29000c039100a01049400d01920b00c4144843c070302100302150b00a807540c0c80360020308420444221a0100f0380800315010401148023480c114800d401600c0340d5050401003080c096100218451003100e8000001d00c440c4600307880f40d40d11105810041400749028001040d404001520f039003d140240481d00e03001180a4400b41e100b078480c085c00041c0e21401001c0f02145050051000928060306 = true := by decide +kernel

theorem cover : BRFrame.Cov 123741007 123920863 := by
  have h0 := BRFrame.cov_init 123741007
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123741007 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 123741007 ≤ n) (h2 : n < 123920863) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
