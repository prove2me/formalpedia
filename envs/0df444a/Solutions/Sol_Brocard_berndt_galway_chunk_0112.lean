-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0112
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:54:06.864957+00:00
-- url     : https://prove2.me/submissions/a88c0f06-971a-49cc-97f5-a93449ffa648

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 19964035 ≤ n < 20143891 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 19965285 1250 19964035 19964059
    0xe1302011403010b0d0209031f06080d05031003060b03070306060b070611030603070e090c09040501090b010506030108070b07140d02160909030914060403050703050303070201050a0e03180307050a030606090b 91
    0x22a00407503005d01c140344030150f200c0840c0c20106c1d183c030701c098000810600089091480c8500103a0211342150740b810104d07007503040003450131360316440240c807805820003030f000060000c201d054011400009010301200c440940e03c0e21039204443e29908541c5140b02c00080900911185001d4100e501d100c0c926900c0c51400c100000980c0e4188520811590500d4000082c1031684180642c15928a001c0c1c081c444501e4917241950080401c0041164061064800400d16080c0754050f03906960b0310300c0c000c110380c5080101985964000c0c68003241e200020448102c00ea207404d1040c1c603080e1240340c00810490791161402745000030309400c042c00140c0b03403803038102c0441d50104003801144e515400403920118070310041683e41c89143c002604600c5461400010400d0000041d880340065500810040d102c1400180c1683c10207480e001c0c0c22780c0b05110503003404000013060048503c0081c00c0b07502d141d42c0c450205110134825407054030030755907a2008100108130b0b4010b4410145084818420001d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 19966535 1250 19965285 19965299
    0x6050f0705091513080604050f01050402030325080a111b130b0a0902030c1207020309010f11160b0408010b04050609010e181c030f05010503030a0c03090e130201140301 74
    0x3029503100244542c0e00b00c41c0c4085010041d60403100084034440480400075185c0c452070340d0354038050310111403a1054002d1032000b200103200e01307809503500402442c58080103902e03246580d4004140b4403840d90365415900c0000e1819402000310a0217920713001010010b0702842d508041007143c0b4680e200000380e0316500e8954a4008030030203140004c0000401c500d02d13074081540d00240f5004100558030010901030007400d120081e01d41043e1025070130300c9640d80c1e901c0c00c0780c907801a0142d081c0401c0c0f152503005074250007010b10004541101d400c82d809807103d00c07510041200035a1003d081c2950004040c00024420300070b0800004054409101c3c0307080c09804030756241c1c014420410a03018010204803003c44a104101c00303070810740115103446188a0342c507840c00d5414504640441e140c040c41140b001d4003401000e049840003406941440d41c4c3c920181c54030300301540100c00300010040041240080c2d044881d010307d1401c210800301004030f1001504948042c0c0061144007010b000401000d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 19967785 1250 19966535 19966537
    0x1815010f121109040906020301210506062205040c0501020c041407110a0b07020105180d021f020405120330040602090103020c03030703050a05100303020312060a0b030108060406050f0705 82
    0x4040107403000103042c44080c80c0d44409000d503094469020f0300b0103500b102403003410b4003c0d5040e030f0744211070910341103070500100c40003d01c00d0070000c0060f00000c0015150b49040e02005868030444a1801c840006180804007125804c07501101e00b00c0b04d00d0030501c5556810058050a01000c7d00e0400030350648910a4090880003498002004158078101d18507100501028207081e43c4120000440d00b030150303000e0302134042180c10713401010001c200e072800307001c002810542d0480303583c001d0201ca201004c2c00e800f040c51103081078280c8070340802001030326446a08950b011140c803131001e0342d21101401180081c41c0b20446088920300402d40c1640b00d070b1480d1400142d00a9800180113944041c1e40300180e000c2d0180d20114070590001004024170142c15410003445050060010091aa00c611481c07000b4440d6000240042e032042c400c106140d100549065000840140001d401582e14003c05c005980260080c80240d0014824001000440d0007040e82180b5151007460741458204d01c0200340d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 19969035 1250 19967785 19967807
    0x90706020c0d1704080a03030c030b0604150c030905100306090f0b0108011401031509090201140a0e0402090f0907020a0317060d06020304170f0913060b031605091815010f 75
    0xc20340d07280700c8080c3c40c0c2c8146003100d00420b015000c0d00d81d154801d0030081e004064203802140404c1c10910148103c0c6040003c4070700351842180003404e43c0da21544125041c10040500302c1c14041030340030103d21a510f40000300f00c1e600042e40d0114a0b03d007003d04c10301c207950f035051000d0780c1a410f0104450f080e0381c0000d8001e0654002650803820741c0c01c981c2c0100c01800b50201c20011000d62070b40e000c580c2c0c8106030800c144883c004c1e00d85100c00100c819100c0d41d81d2040c0c1b6030803400604031161000b0180f03081d400904882c030340101010142000c0350001383c014035058582d0b00259010300ea0200c1015000344104801b0b070645801c80400e880c01101044003c0680f00000303010f9903000001804021a410488641d60559100903454019402d401245540944c00c0d0074458800c0c1194aa00c04645009400545036444d000300d04649030540348101e4402c0b1640c62000f072080c2030022000c651580100465440c6102c4120790b241d0404000b50303501152001445410003400b00d05c2207405940014141032 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 19970285 1250 19969035 19969043
    0x4180902030a03050a1404030308070e01080712020703090e0c0301210b06060a0216030c171209010e0102150c1804020702030c120120040e010e010f051309020d0605090706020c0d 78
    0x145d41d401000049030281c40b4a04010b48000b0046004030515a01801c0c4500c26031891300d0341820041c2540c01924903d400311080340000d064030103520585d030040c4d00917001d40b074424148640f20940380c2140070700c1240101e0f045111188044010011100d02c650300f80d4030f007060011a1a003e400645401402010041c0b5040c0141e800181e0227410078403c000d05240f071030311200c100d0b0000f0344a1501403000c110b0346c856100e03914032404040b2001c101c0490715440c0704881d42a0f8529001c000c00064485072860780083c0d040d07005d4100d401d0413030081c0107400da22884480521a42c0e03805040303070300070055180c2d1001c50b005a10510444c00181c60018001590010485240c8809000350f29114054039001e00f40140299084440784852200c20f0301500a5070800060000346a8075500008101d0307909105078240000c0e02a0f04011904203200303403030003040c010000440c1281c1c507a00801c44114841108841035540c650800c91020024030482e400740030a88050700719440220001201d078011104058 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 19971535 1250 19970285 19970287
    0x80c1204060503040b10030f03020f060c0c0a02121e0106150302030106021f1b030504020307060e0306161806021c08010501050904020306040204050d140c0904080307120605060c0304180902030a0305 87
    0x301d419442e070ba608801558000800381c0001c108d460000d4072045181168411441028041080c0e00d086000742c0300e01401210060000b81d1440e000c100b6240c0f203468880566020b9180c54200300102072050030820652000040f4415140820340d80e400c0310400c10000c00c0510510051100da075000c103501140b0300c880228060706c2a40c0d10747c110020400b400904c402d41e010645030802e02600741e00503a200380d0084080d03441040d541d0301c041d111540d842d0412541034002c400010342401c200345032600380e90740901c5c0000c0d5000d140c95841d2001c1085800c803c016901c000440081401c0502c944c040038642032501c01041e51604001a1507802101061441f40e5000310005070365803900d45c140c8000b03010040005a4000c0c0c14141140e0708a0311904140391800354160304043c03400c059005c0c034000c032390280d03c4a19580c2d039007a041315075100308600c213000c1640303480c40014195aa14068151800c2c83d001540d6590b1801c40c04801c40c9841d010010340c01d500701120b0700c003d60303400b184140100707425040036 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 19972785 1250 19971535 19971541
    0x106080711010203090703060e0307020d170d0603151d1b0d0c0e0906011d0a0c03141006020d02070807050d0302160803070201300b1c080c1204060503040b 68
    0x1a90070748421034554905600c0401000a840e50000700750703007102c0c0560002c0003821081c4d03c0f06078503449590000ba4020040024010025505502c4030455050f01401c4034140000c0303806010a480a40d44191036948400445001c01501813003070031004042e00019500403030b400003110b5100c80c00451100f5981d220b40c041d20945441741c002c046c401c1a800f68243c13208545492031140c16400582c0c0e140c90341d04c10900042000228264002c0201c4043c0400c00c03056614030094201601140713110108154468070381d004884000d81446005803001c81c2d00c406458100311009140c003050491280455000c0c940401c010200030640d4410303580c003580c81003450101410141d02d810301d00b01600b06501c164404c0000c0c1100c0100141468038400d1340c0d040c0c03200e044080d07210004074072144113801e103102400101001a02651004070400e00103402e200c0220208601244e41101c0c0030000d540d050706c0041c4001c62040300740041c0c400d1405105d0307410304040c2402c000030b01e203000003000108000180804 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 19974035 1250 19972785 19972787
    0x30e0f090f010311180c03100b070b0609040c0302030f010905010e01060b0d0f1103040c051302070209130c120803010807060206070206040602030a020409090503090103060608060f150c0303011205070e04080301060807 95
    0x43e65180780300705c043c0030b41c072410b1030f00c20403040d58411141038924034800d84002c55515241c0c4119034040d50800d42d07860240c0c45d01c00400c03201c0b600281044031041090b000020068905102c0c07880c401840c1000040c1d1950682011400c2d549200d00031300c1b07241d240910034400e980303c19007a2142c0d05449900040d000d06000710300e030300601044202e1003800c80c02204110400482c098024150341c4207903403001418800800c41410381c040c000c0f00039800100700002660a0480b205080c3d211801000450440b5540f1800744c040c0c1e01d10000180c580310fa0000040c403030a14208000c0006003000e100804540c6400c060081d02d84a01810041245400101265210505030140c5001c0c141002c8200000c00c42450401d90b030341d001c5d024042c042400c0807400501c1a0003156801c2c46a100584440324805050040200421202c001061041d00c1880f8803101c4100c20130103540a8000d8a009640150040c100140b0b031007090342c4000c1400e1a8041000000340704041500d0455840c0d041200c1d5644072020 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 19975285 1250 19974035 19974049
    0x150603030d050c13080d0f0c1704090b03121608030702070f0603020406020c0102060408160512030103050a05120f09010e0d1727060405010503060a03050109030e0f090f010311 77
    0x112200c085410403061049100d03c030360007442d040000000041d03041d5a034102d099202c66130900f0500105891095240c4a1070250300c410803154804d08a0702d806075600320340100e194009070010004d09a0f548103088a9080420030b2240003c0780402440c24800141600078008101000041c403404c0d000c000b103003e0324000c000d840060003084840c15615a2102c000a0003500b203445400d00600c6800843d240780d50001c03039428083c1e900410903a240a608110114813144071070011030b05486210300704440001c91401840c0a58403401c0034000000369410030500c2c200e01c0903a62640f0000400c0701080402c4031000322080400c00f030a001d60f0340701c040c030700040700c01f14032007006045850f41f0214030002507081801040007000100000341c94000c9a26002c098004881659030040d00400080c8117560050340034540c000d0b40142000640d6851f40d84290a5482d110303000c80105818003410a00d918001c12b00d0b241810040d80c80d04d407189001803011580c80410700c000390581104c0e80c1c0300150303611a52 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 19976535 1250 19975285 19975297
    0x90604080102030702030a080a090c0608182b1d04090201030e06040c06021b0306180109150c022406010e01030b0d1a01091b050309070e0406090b01050a05010215060303 74
    0xd008544070f18110902940740d501920101000401020014210440b0b80c8070b1002e640c1c0e0010030b0030b0016800c000003901c0540c409410001d00645803c01c02010795020080003039042803039803600c0402c551b40e00582c06a099500d00c47e4040c080b03440b104480214002c150203041440440d0045140ba040c0d000507001064441d40d0100940580c404100030b0000d03d032188011103078154205d03024018200c000c41c18588609008940c50340001000c03940d100a003010450104000500000b6480b03110b60b61455040d142d00301000900d83c8410320303100d083d60103201c12a0740c0c10f03520000008107030b40c0094500001e076005124505000d01c4890042041e4400c1e402500c4000d030242446c00032505900b0a0811609100c00007000304c1110b80000c11101d4883c05070b961005c0f800c940080d8101b0101c5030a581540008045054602c51950001001d96088040d1030143e8000c0d00c00140746003103030408410009050304800e02522a0000800a41c3d80c006980f1602c0710039440b68010f03a03213885c80001c7c2035100301 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 19977785 1250 19976535 19976549
    0x31603090602220f0602030a030e010e0d02060108060c1e030703061a0c010b060a090e070e0301140108010b040605030c012304030809030f01060e070c0201050c0708071a03060904030302090604 84
    0x841c1032004818640840d00f0840028002021001e0740d440298a0403900c902820006810510242e2a41c0380640c101d0346450b01f80800205202c04001000d92134072564009240041e03210030b0040000c80f40503c403058000255148151070715190030030b4513440307106064913511203d0300040040d04043c0300b82c0c0400050100c0480d6400d0986000001140756048110600c0340780d46810f1070f501032441c0080072160303502c04544400301c103e4900107003180e01c908001c20b40400d0110840a850f5640d50a1241103076180580d00c40161a505080026003140d10341022140980d02e044014086540c00080b500c0c5003183c00d18100f00c1000f03d568080c1c2d011440000058541c50000c24080208a0740c42c000c0c1c80340c000c00b0303011504410011440c050a8440b40d1054085c000c00d41e80c00700c0c0016214034550714a540c010b04002c2e00c0c0041c00c101c00e514200069001c0718094201c24410f01a8260a00188070049143c1046508509001c07002030006035003e003004041c1640003a50892507164071041d14020003003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 19979035 1250 19977785 19977787
    0x10b0907050a03060609030209010b030702030c01020307080f01080a2103060308070f02010305061f08072006040b09030403030909020d09020a0f0303030f0204150f02100c0903050d0e010203031603090602 89
    0x1412010307126811080300b80c00030078103207134010504a00c20501203045030f030014103115051f468001424a01c0e0701c0035181c032045000403c074030300d2540c80900065008040d181d0383e00c2400c0c9000c80d080c603110034040e0007001c12500321030300c0f44022501c161118420318810a40041030f001038240141c00808050384010070035500401c2c03103401e01c8032650b0016801c078000e88003070019503910420899580c0309603980503c5811000c80b0552103610440d5180d910041c103080045a0703408006d410a1040c0010380d0700c41a550003041004104010f0221032500040e010700190b081904540d406004e998030784c0a040075699001c20712843d00700840d0403111000344c02a2080004580303da541c0d03c10a00c59000c02da000c0790902c046010700a1142c0f080302c0848200318a01d11048040003421a42151418039000c00c500c01c1a0500ea1100c0b054441d083d1400515104c221b401e07440d519000d4200810442642c081c4400700040110b9646c0110450b0303440140b030f0f5001d80e50f2580c85102680240500348007d06090700c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 19980285 1250 19979035 19979041
    0x30910180305011407080c04060c0507030b09010504060b100e090402030705042a0203070b010b070609021005070201080f070906050c030c07090b030118020a060e060708070305071a090304060809010b09 88
    0x11065003d244d640040345602031250b900c07084140c901c01d200760303281140290100010030295208401c0700e0703161031081c0d05441d0425901d03111420400016035412016954a0061004000d605d1040010186058400111260a82e44003510500c0044e003040d010700d984900050071507030140b01c080013404c0010b1042200e0380c81407640110541140e462101243d4041c402183c50900000603280266413155461542c1ea0800030318503116040303800b00300d13440c1d5143c00344c2c100141e9030300c0440c991244170340d540c06841c1c07100c0c0d000040085002814243c03000c19800c081c403062550200000c1d06031741031802e055540b6948100c41a255101e25903402401c1e005502012901440a422000041004030024080510040303048200480428002503020840c4002000307603500030030380046480c00060110342800c2290711411201d0b03120701c00481c0001c00024421003002400070250302e0038a02103035007002518110000b181e9903c998020311040c407908500141c0100c0d002d40024221100113000756030142 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 19981535 1250 19980285 19980293
    0x60f020d021629161e120509010c060e0f07140306010308030402030a0501060f0f0902120711070810020901091706010306180f0309030c08010225030215040807020907050304050309101803 82
    0x1d6139656044a84040c1c0882c42c50040c805207100e44c2041d6086501c0a0003c68030318003d8030107522601c00c0d54140b00120301034070003045840c89803042c8490910050000007034109041e9091180d103410281d0300c005401039070340441d00c000501906480d0f000038040d540b52902d0000a10301164030030020420345c01c0c4800032600801d00750004007210401150000762545130046801a406140180044c440706170000070002c910414285040100202c02d17074000580b26100d00c0d050211a586844516800065212131541d2001d0a800103100d089640401a546551501d03102c44040c44094112511484080307400810100003207901c0303520000d400c003120310358030f000781c900e00c811710059030300394110100041c4040041c0215105c0e100e18166a54901046032400000000c0320801502184951040060321000121381280542e004030f481c01c4e00d840d41841000316080000300548101709040c018070000850010656666032002c55060f140c0491025086600250214800e81e80240c501c1c0000140 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 19982785 1250 19981535 19981567
    0x405060d0c0b0a020106060809030a080709120501061a040e04080306060f04030605060301050c1303020108131202060103060b040204030c03110f0a060f02150108031e0f04060f020d021629 82
    0x1400a0350001d00103140d480102391481d01044501070881d810801c05550090320840d070050388142c10341010b165a644440d200248101d001400300c3c0e4581d56500300340f00406480700d1794000c0743d0316141c10524003410320700c03200175560020348003c0c44101e010004c606141d42d070106480b0100203003001d1940b0346130b070781c02c020010345419100c0c02d00a51804002c00e07544c1000004403058412243d882c050100c0c80d41c1e004403604503004000e05150100e015142000807640074a4681a10455008102c01e505600f400400c69590424241c801c0b44100b2040000800101c80d0300200c98200d031148000d505418085841d0300c09a05140d54000f10610010401507000a102150680c0e660b0840c1c040c00040f1840ca41c41150a02801c04107034005e0001001c02c6003a14020340b24200501c04030790500c191103125800c207401a404c90300208821368171009040d40c0c10088212580351900c000c0c204401d00ea030250713903840c40c140128103200800d62010340009111490807424284010001d40c3d40f60700c00c2103040c2e01 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 19984035 1250 19982785 19982797
    0x2070b06040f0603050d0f02010207060e0a1703071409010e03010c08010618050303030a051306090c05100201052404110d0b04110301060f03050711100c0905030a110405060d0c0b 78
    0x12491400300c41ca120404284205400d84c0d50000c01010701540d9020b0540d040f804202e101c504541d002c1100e000004c0060003481600460036004000b8a8845c4c81c0203426003107540f1200712890400d100b00110340c1d611801c0300062a06040603a07555920b021700481d280b030752007446183c0640c204480ae900c81541304014a040303c0072982c0b1600005800d0201c16600810741c400c55038141d10600112b04081c0349544426040301c1c01041110304560389581c0c50f020354251b0390054940c103203d00c0f42005035040c421000b00c090209880204128600121035003941c1c2029140c2800c003540d911840740301c035150b9600008010046100c1e690702d500b080003480016001c19a0210f006078100003503081c108500710166410f0300c2e010340fa54100850121422001414000c000b1003c1000c031f0302072a9501e200038080b17810440000740021039030005c03010000c0c1000040e40c0c8500d002e0351150301182c0114103041c004081908040700c01040b20f850b1500001c0010038546000f805822440a001070703000798030002416 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 19985285 1250 19984035 19984039
    0x70819090b0613090804050603061c050706080a090201021b0310020d0203010302030705090105061e0d020a080601020f0c21070503010507021c0203120a05070909020c03070606080c0102120c0304050402070b06 91
    0x29180f0080b12a041c2500c00120000b000d1180511085c460741c41d1000103103a00a40140c1a00c0703040d01c43c2149000c410940107000d5815811054040c8a1217a112083e55448075481e581803010303104560000790f039111540c04403412214460700098031345c1c0d414010100d01e80300c4030000395100e203a04100f440080d0320170b03c02240f09110308030340003a690034143d10f55812514010030305810200309100500d00048890003118481e4804c01824090005030f2000e0049000c0650743d183e043c0c07030040000ba1600c40040d140a501e603010040114144c1d58a52400100320307550b400c003c2c0c402c2d04800b2002c0c5012241e4102c40d606500701010080c0c069400121548a61452503805001845110040e80c07240b094445045101c1201400217034903040c9900000d802610620b0402c0003641d403000c00c80120b0b002000702c0f4599410004920381406028000d50010b8641d031070142c5611000c1d41d001035a1110144100b403134209001c500381000003070a00aa50040001520540d600e040b10f18042080e00e0b01244e56034 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 19986535 1250 19985285 19985299
    0x30e120114090a050c060a090b04030804090506030a0507091d1c080f060108040305070219030b01080714130504050f0304060309060c020105160302090a1205010203060102011103070206070819090b06 87
    0x20b000040c0c005221a001500600900720303180549080c0803040d8452000c00c414442038035000079800c86902e004000850003050010345403406c3c003103071509076030020301264440d034052050140815030200d802c0c421a000030b00002001000101e40c0b8020451200c154400b900504110100411003401c85a40c26002607550391101c0c0c0d07454000341c1030728106896150004c0c02000c00034000038090801405c403039000074000c07194203502562080300c421890300100c81c041c002d07a0041001103c10051000070f4071260029610204110010804040071010a44403041d12040420305011060250301900a501020713a6507a0340c8911014001d0a80101d04031182c40c94002c4004c5000d2061040301c0c00b540c0c0c482d820341c189080d000022000b9400819030f9036440031311088006016480ca40140070014410000580c5a1030281c002a0858003250b403103212500040081141031a400700f4119405805170400d8000b0351240f000540b05c11580c5400480c20524000a807003c0c051014102071140720102c2e840d03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 19987785 1250 19986535 19986541
    0xa150e09040609050c0a0e070f0c050d020c030f01020c0a0b0c04080a0f020a06110c04090303151d010503010b01050409050408090607060914071208031b041d0105010314070507030e120114 82
    0x4000b200c6c10320b1207508065a003d002251040f4402c245245940b006c914290303803187c1e1103031249802d185601c180d000c09688003100113280b0303007402d112140c03a00b01d0010003141013039900003840d903d80422a00040c99030503010005484840340900307176004ac0000504603414420545841060841f00c40c0d01a481508000d400080b054451851201d0fa05d0310302d4040e0408a12030011302c8090004a00214141500d502c401464007900204080007004034080c0c84202c18a24558003c1c00041071300250700990400c4907410301c2d139801004907803c0319140703040040c0e00c0d901c3d41012601c5009141c025607000400040e05814805c0c81e40200441d18000d80d1070b24040105043d030660f03603030b5a0b407140300c4009143c0c841030000300c7c0c01c02001c0c1d035200c0c566150f10061200180311034515a031060b0003d000c6c00c0201c94103403040c0458483c40c0e501400c020b0a00f040a031342d02d6800e005c41001c0080000040100000c2c90204040c80340a100d00828000b4043c60740c040105844240038041040501181807422000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 19989035 1250 19987785 19987789
    0x6030102160206030a270309080304080a080f13060305090c0315070c0203010605030607050310090e030403020607060f110a02190b040b1008151005030c0a150e09040609050c 76
    0x200c84118603001d18040030300465078288846600020050000c42d513803190321030720480c40765a20041100d001121007117120f000c0d2802816501ca55000300b02036030700510081c444403400090741c280440d044010542c40d13401548070501680f145c003222509500b02d1082c0001e4461b019088240510004810f46400e07a0924090650322244d80d801c5805041c5003c020274801c0d4080d50707000c0050341c00a0004280d0b03a8a520200c1c0c074200040c0d4040000600000030440c0e500c40002c41079000d010a40c009000e4001c4080e03000395030b8000c9020181c40b4100010b00d441c10824564808402c00d10841e800b80101080c10000101c141c220030030000150141d031444124200192000802c5250700c103400c0344441d1182c0d11481124035000f000c40703100f520b150b880810461030401008081e00d0b0004004601c03407030300704000000304c00306030302142c000d90240701039104956415062200341c0c1c0080000500180325001c040700d840300340e5148150400c0d0790109000a01000d6040b0202c035600600484200e0003004c02 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 19990285 1250 19989035 19989037
    0x20303060d060e120304050c090912040306110c011b030c0c020a0b030a0e030304080405010306150c061a040c0305040203060c160b060d060204140306070203040602030405040e030d090507090506030102 88
    0x800a62016100404a0000e111a0300034034410030f2003c2159035a211840b0103603140e5200381d9050342e6550105205c0c01e11841e084030342e541c0c0103030070b00c2c084c048820b00d003900708146000d00d02000384442d440e0f00c0002514415507056070801d1244c03400170300038440c0388a12a141a032160024100090030240701081071400b0320403640802d80d01a181c0703030903146480d5001507290400b500c0c52040c0c50315003004048031a801c201950080e80074241c04c0750349518007800501140e00782d40c05100203d220781c5684100715045410b0000458001c007000c94444a41e00e201814065600305c12540985807504107003120354140d0050f4829032080d0116160740d00c1e04020311101e0b024507465241aa1075028181c0006007006440c10f400690203400362240c0c04082d9202403d82e0060340040c101b41d0007080c0f0358115481d08201040c0c00c00700e14005141f42a0808000075124416805010b00650310343c80e501c69034010410407a454044884c504114024091131324540321105403040301078003400d04001c25458513043c8 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 19991535 1250 19990285 19990291
    0x30105010e0d081303150c090302010e100c08040f090509070b09060d02040e010321031103060f13050901020a080a0c05070f02010c020405040302060117030301140105070c0306020c0715020303 84
    0x1848841c1260492410031082001020003114480700500c2134500400c00e4094004c05103100380448811401600301c6c41c011a5084188101008501c0d00d003000541d80100d13145501c000160349201400030602000c1e504c40c100800700074000c1c0c00000c0c0000d030002c50000050141d42c40e140c414416a202c071000d03280d40740014001e03200749040801c2445800d150035401021038100081000d805c241ea64018014000d000b68416079020644a0961420302d440c4c4409241140460400700305110019401c2140303070000506580c010109261425425602d51703150b4405900702140600142c5401000c40b8045d40041030070300042a04200403484075501d5004c2c0e111402e030b01e65075080c1098203d890b510880c070350101086c1d060040862a10001d602d40d809000c0c0f0540c081e400030032903545801e100c5440485207103004011500188010301c018880c40d08003005800342403070541e454041d18240088d0240d0305a200408103031001038801421900854240d04407035200e1002c90030018415000e980f28031040b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 19992785 1250 19991535 19991537
    0x2130902180a08060c1c090c0302090a050403091404020d1104030606060c080a030b01030e0a030c0201080a0b060d0e12040f0e060d1a090106080f060a050112020907210606080601020f0303010501 85
    0x7000010303030301540c42c0050481d00c0700fa0580f06c03003da6880a5071034216440120b060364072040c1c0300b10500540c2404042c254014200d4034003042140744c04c1d00d00402140c1c03d401800c03030800400c0c500c00c0031070f55950183c4543c1d0481550400410030b02d1081c1450303a501a00c000c6440c1d03030338100b000485500a0b107030103003c5604040304904d081e1242d00110028810700c01c1d041c5c1810ba950741e600f030354810100f128107140c0b40720751901c5104510500001d400e41c04000c01d104103e9060000128694507002e0540b42100c9403540d002c1010500311140b0740c00c022440800d1481900017040c00544804a800312a0880d1504811200380e91541070078004400c0c1a250040e12084a80310061814540c03000140d50018415000040107521540342e1410041c03456020004da4ac803060038481545002d1140e540100801003501030201d00c00d501140d1a100300904860a00c00386440b40000744a000b180100b102d01114410132005495080c060840c85058520900502c00c40c1081c0da0316600000489041c2d03481 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 19994035 1250 19992785 19992793
    0xc0105090303070f02011704080c01050114030a03030f021605071403010c09060f0207030209070e0a09022104061103010b03070206060d0209161e052503080a02090402130902180a08 79
    0x407074444001d21404d01d04100d04001d0780d187d41c0c000e503e08040100340568405c0380300e660b071044026416801d651381038010482d1000d80324102c18a030390700041d40f100d07100d42c513041c04254074551800c000001c1c0907a030004650030030400c58a108000000c0b5254054560000400d5824813445080c1406ca80d1b1411800c0080f681d07819081c0309003400b403018901c44061900c1203844890300c075404103031100401c5c0c6000e8007160f540d45c80f0748840e1a150b11240c0250111180c00c40c14070030781041004802441b801041111517800c0085010b020561b003042682c5000c03900c00c550380f96540c03548031050b030b07000322003000046c019034000c9001d130700e03001c0d45c5000c0e007540052803620f090b00c070701021075501d09a0030107406c1408403c500d50811b41c007a140c03001c0580380c055101e4079258070903c1c80031802c0c40c1d2074903078040840808194a41c0000e800042850304440600310058030303131070703242c0c0450700a124811001c05031600400002440e2000e9800826282c05903403429482c2e00180310a2000118460149a4031900 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 19995285 1250 19994035 19994047
    0x902040f0602070308120402032a0a0506070507030b0c040317030402040b0105090a090f0b0301060e0609010e16051c02030a05010501030e0706080612030909090f0106060801060f122304050c0105090303 88
    0xc1c9202c041500240000c050f81c03180c2c03c1ca01d01040d20036035201c03003101d4041c841d03032b1003450140380c06109400100001e8603541d14000036503a4a0340c40d0380c082d020003424258400c011848495042064602450b07028441402c4441401c1d03c85a85402c2110203d2081c4d040480551455100c0c1c07003558190034000c2d015158541c1082c0d42e4030042c00740101e2864400ba80c408000c04c4603502400fa0000504600ba200320141c01d025042c880342d500160802c24a0000d50f90501c181000720003125100701740d0900c0c0c0301e81c89400041c002665035030800b800d5100240040107000f41c0c4003040c1c3c411412150240c8041202004c1c4050b16a100d408610940d0041428a00001c68500b0091122031020303041a0980745030004000c0003039545a41a54004031507808179140101ca148244151000f404940c203140c00e256141c080020f181100c546481000c2000b06c0e40300c0e0350000040d030404107a0000091150a0300c007412030788500384000850f426246446040c03185038240d40610121415920047c010b5440c141c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 19996535 1250 19995285 19995307
    0x10e0c0702060a030e0c0a03060203010504050108030f070605040809091503060a150302040b0d06060f030302010b030304030c050f0301060305011b260711030c031b100e0d030f0b03010203010902040f0602070308 92
    0x300300c1c40d412030046e0261080d0030700c15641780300c04e007009580319900068582d4144010702c81140c0c2c05801c852441d9200f000380039178600d1a00252400103905c10307404143da82d1585804165400f407203c8545d0030000c441d050000380f201d000650406170b00103034101c03901d81d134403842c132901a585085400400030825060034005422320341c21660038601d010f40040c45502060780c1d00c100b104c401d507021914a4015403000d208140d828011800c0c401000c900460a00d4190b8991811050b800d20a080c4250178480300301446860a402c080000c50300701c4000c014040550b07403001d0000010492a600117204d9040000346018034070f0481c0c4019900781003a0200d07554100b8165803045518100c911144014030802da090b010030401800c010103401400e00054000344d81483c5002502030040c0311803420302c3c6144040030000103c20001d044280340101d02c0c60201c1c4100310041941041c07003034040d40004000b08104045400405c1120780c840341101c1c605035a0142280c5a80080c000241001010055520300f2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 19997785 1250 19996535 19996541
    0xc010f050a0e120d0201020405030d08100501030507020f010510060207090e07150903080a0f080c090d020405060109050a030b010e07020303090c04111c0501030b130203060a092306010e0c0702060a03 87
    0x1c030024200d4407411040c1c0403d00d02d4030b2100300c401c0d00180c0d0000f41c00e12107400c09014903d40d1081c1c40c107148200341096171002107802c4041c0a2a410155079100040016100f0415036500b0b801c0c010003040a4102280115000e841c10300800703002d0f100d065400103007a10148a04c44e54000301d0405089034505168180172040c494980550400024450100c00300d00c01000400d0801050780341c0ca10003401100740074000480040c0112640322040c001802d5544806010300d000030342c111000140f030755079600103072810300f069004542c2000d01001c0210402c40c02641581c143c0c0c003401207140140d610001d049a03070380300407100900343d0707040f003030b884034140c00c1540115003c01079440c030650070140e00c102c0d51140d46000d080800c1e5040d890320010010b02541c202404e07004035040a03201d4400980d030b0003080e51034401800da0900c4a5491000c03a00b4001f228062031060350b80101502113841d00320b02e00790350b0740300d00380034001107c1020800b107582e9078043c0c801c4034000c5902912840c10084007190903002 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 19999035 1250 19997785 19997807
    0x607111005181504030b01060e030d090b0909100f0b0705060a050402010c080a050403080309010504060c0305011a07050a05030708251104021803010501330801120f051507020c010f050a 81
    0x100340c20138880813000801403141c3d40d019000503580d0f4155102c2800c03c040c900f0754170b2030803441070007a001000c1c0181c07a200011904600410342c0c8011140c0c48803541802d50440c1a0711900c0c6600d03100d1400b01c2d110340303806c004051060048080342e000741c0740d580041c1c04958003607400034041401c0c1d0000c030340003031010740250500c2411800c1050402e1768946655030164011200d0701c0d405c0e50355404004c02c2041910811b9003050300c9180c10021581400030141ca499000e072000105040c000c181c03002006070420601c000c05500c08107803922006c403450058040d400c210319106000282c0c0000041103000320694908140d00124450100741c900800d010003540710408901d40c04c60808103594441d142401060b0003002200c4c410444900c0320000c031500710000103124502401c00305028460503a02c90022415502c02144640402e100341ca0701189500303140303100912600515080000c09000c10b089680700723494035003e68103499250700045a420301090a0000400c1c1300b880803d003002d1140124000e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 20000285 1250 19999035 19999069
    0x50108040305090d0b041505010303140706020403020607050a02090912090603090f06070e1905101110181101020309090a051008060c0403110306070203070b0402060702060711100518 80
    0xc80c3c43e80e402c001c80c2c4600d030390341820b4401e540800c1c00c0c8000c1244d040104c04a880500380c08100550441e03500a0000310a014400d88011012440030103014a81d4121001103900500032a0340d100c0620740184c80715107840d002d910804440d030010325003180110b56045030300f00b5044094904026081000b089410140011405100b06410000d03980c00402200d8090b5041d612001400143e10003001b911500c00b09901034588200d9400b00043d0303da020485120300707a43c1c1806c8001201940c05949410603880301d0181090426060114250135242906d190074000d504480750044c458005a07a80d04c40c442c403141e00b141150000a1701907403141d109503004041685401c6403a90340700300452402c60260b550f20304542c4001810070400c80034206003609031005401404a030b282c00754002c1d4407401612006803007154010001000c41d030724181100c030441e900420032526403009080010071880d060304014012a540401c5c00d24981c020000c1e2780e60711001c02080c9a804564070706210b035425124020303071 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 20001535 1250 20000285 20000287
    0xc0a171c030f020d1406190e0a11030c04030203070605070b0a05061c0503120105090f01090908040f030303090201080a05060d0f05030702090f09010b0d02010c03030c02100e071406090307050108040305 88
    0x4609a2501c3c002050405480c920100d4840c2848100103070005d806025203101c0d03122403000f0510008114a808100c030103444124480d42d85414102c0050002c8545080380c01d0400003c0046150f03a54004d0810303240250100c880c881c1d01d480d070a4542e803041c040c01a10740d00001c030000d00300e41190b80105038003203070150445a000548196054540c00840c004445540010a21117840c40846c0070302801090203c8401c445428a912004030002040c0500e486458076042000140b01c0410126802403241a540200c410341d6800c00a00818001c036003280040d20720300c0402e4802c20180640c2d40a110000d012115001c00d80d9070381210409610021511800203000034805651203500c141e1055034070b031002c0e26032443c011089908480d0b4500d4524481e440481c0c0100c01750341d01c1803030301501070707807605000441040820f0168640401c0a10034540b44c0d04003a910b04402d00c001c81d04104540303403070040680300c604080811103240220701025415620401d070030810b9600c100c00c16a00b2600a09100d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 20002785 1250 20001535 20001551
    0x5040c0e07090302130603020108060d050c0d080301150f020c0609010e03010c0305041a1e06010e0d050d0f03110a0c03090b040e0117030304050606010e031e0c0a171c03 74
    0x548030901084070084007003211101c0c104150300b800040d0305824189003104010b0f0b6803d541c0040c1c000317580941a940103821078086501084810049125805402894004100240d1a203440141d009010340c1000e080c841c2c4110b080e2900071000125440482c6d00070700721200c0d44e0f509011a41d040282028104130700ca13141403000d62000c1c403441c049000281d50219080ca0a4101800400101020401003200001c2080454440d28150006100716524032400d5501c036000102d03055140d04034400da000f0b130914000010030100044540010304070307484100c0e01e0040140194100d403032150100400c0c8408106030041d080c828186400780a00c0b034100708140380d407103082d00306040d0420340048245201d02c400610112802000000759000755500962031490a6992191510740281c8050b061003940703911000e00d564180030212802000c8030407034504003901101c80c2d85e42c03041d0110706401343c0041d450106040b0801742c01c444037a8085e20007800310301031003140d82200e40460845503080550fa0b0250b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 20004035 1250 20002785 20002799
    0x120609050a050a06060c03020705060904020c06090129090103060203041b060f02070e040812091905071a0a02030a12020d0c0201020306090705090d03050c0a0b010e0907062105040c 79
    0xc0d140180c40c58000080c1502d400e203003d00c1110740e40c4d0001424070100c0b042041c0000e0780060071505942094a0281c4c5a02c0c00c4c00c0418041e0084010041841c090f000c03c11140f02030541c00746804d02c65407030f038100c84c1940400c0311440342c0c00000742860300940000014000310300e598008513002485040b50758004484a08050503081140d0885000155201c1c1c08040c0c141d810042c1a026115a802182507800c2c6a51070300d140b4032840d4100c4441d61800e10018424080030720050003a00507503100c07555a00c605281c1581c0341d8007603021b07100458000000b203c0b83e1420100586141188640082d403820808172000d80313030751003280c01000d1344a40030002d0002e541e40d03500640601075081d40001d0386900f40300040040c0c2c0040282000d0420505005c0d030351996441341c03a880b031b20360303010309081d50f03208a0382070342905081c001403014102300b03941e0300001351030304803022154454409181903548036500c8501c01c8800351995800a10111001003000c0c4191800d94841600715101c0c038007400116503550781e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 20005285 1250 20004035 20004041
    0x40c030605010f0e09030f07020f12032109030901020d08040f051009050105130c090207020a03082a010b090403030c05120a061a0c0a06020912070306020306041a01020d120609 77
    0x81c2090341c141e0000c0001d010110081600b05c00c0a401960401144880034403150140d0603029100343d111100c402e07002c0c1c5841d40c41c034070340c0c10202c405d42c1d9a0714001198a48410740005410220020410004042130307404016240b08240590141420080004085032840e0003d401036440d11004014800021002c01908031040a00d640225012129080090850328010200d0302c0d04030b403110002000603004c0e032072030b8150381003140700684402c0b250020420b030b001c0d00e4000803c3c40c4000200c06941d6441c2c0220070401c0c0100c03003410400c02c50294141c2d42a00c024004964002d5069808280024001d0300102d0126510b403034a5820800480300c0d0f0009200c05481040200c2d50f110814062201890013455a00009480c514500003a142d1041e0399060304850290020f94045104c0305203a80381c0d28a0641ca813042c904640130143c0b44c1c02c0c03540003944140d480510803032610701c15101c3c40244022508650304141c001d13100a080480342601c0092003c08142e02c065940c1d40e0119605203988 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 20006535 1250 20005285 20005289
    0x1009050405010b01091d0103021e04061e120804050f010e0d0b07020d02030c0a0b100f06020607020105060109030816110402040806040c06110718060302040203090c0405010510020c01030203040c03060501 89
    0x3000220703c9010a50000d17100d014150062461001250540501c071010407910504481c0d040d00d81c0a2040074031380003616440070100034030b58481d080c41c134005940414208941c0301841950522050982d1300c10003181d442c058900c008168010a1000304400d1800007130407440b4030018100300502112410000f00e0300481d580044078407210900c01e02070703010f904101d15050a50540019440c05004008203aa900121600203200b1100000003500e03d9034014036000040410341c1c81003400faa142d1401a454007022265440198a0000003820540c49105904111b0740c210b40824030340174070740e2003100450089090684a140044480780640e40b605e1008200074036141019041c58103191400f100c00b090181c1c089010000400c0c2c1030000260085804401c03212400c0b4600b248402200d548406001540c0c0040d600038030100800c040e1420200d8074000804c02210204442e0780c0b20380c10007000d01144002d106c0180c0c40f90b5510985540685e0046170400d000704851444a6503a64902e403d4890903 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 20007785 1250 20006535 20006543
    0x402120a05040c06080112060509151006080601020a0c0b1812010614040504030e01110a0f030504151706040c0c050607020d02120306090403050706021b010203071101090b0a0510090504 81
    0x1c0c0c4204400e000c00340e80300e072002c0c000c01d1400c2c0c01d2175407610300000845a882c1401034801591040480c07805c1da004c10035401c1a584e1b8000160350ba18000d0741000030a03116200d07000124440341c000940a44c40416000c0c8180e0b441111502c0d110704051000e00c42c3e41011441c00162840d5502c080305640e035036010392285150707240001c03580a082503405c0e0304800540c3c0425010300e00b031a0502001a4003c1a00c101070002880c00540c00d4104550803490000300c1980039018005000307001042c160b214008000ba01e441217081c141681d2284011107040d001d02c0b0301c3da515440c0403404a495807520360484441c510082c942581900b003a41c03a0b050400b1800d6441102503401128851701c8141c0522004905a107181c1007242140b4081c80420692100108010300700100003911008105007541a1500401d4031080d03900c0d40000346415034001e6009550708804a10003100900915005000c1c4140081d4450310040064886500740000380401500402c0303039100f0741c1c1e0302245440c024403c080c840c03401 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 20009035 1250 20007785 20007791
    0x5120a021e03090f04140609040201021015060815131a0303040e0702070f030b010312050f211305030409050604060302030a03030204060801090506010f0c0c050a1403011a1309020402120a 82
    0x1400804c0443c80c0400d4aaa000da8144a1030311000d42c0c882003802e501c0b0100380c1c1e5881c00796465200407400c02110110707041c1240d00e440c1020054011101c4c064041c1c400ba0b866052083d01c83c1e000c0405100c2c40d50040f540d0124515080390503440554101c3c0152a40b04c0710700007440d440d02e000090542c1c0082d040b440c1701100041c00c110046504014220084c000d1a03407500009086403a01003509605000180c21800401c1d014002c85114100b100e1407103600058164840c0c08590240c04084508010111782c0b005c0d110205d68004900c48102d00d41e00c1c0e000e03001b14034003450b00010102810340100040d0f40035a54840000258405200c3d80000512a0b9001030b03490b8200140500007040680000032031610388020091140d070806070511a904a90070259168102498280031030801500956046403800d0000207007401494000b0300300010440003403003c04404401038840000503040c440e480b42101d0214402c00406170300001d04240094005891b001804102c1c0761194020742d200c402e031a81d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 20010285 1250 20009035 20009047
    0x6050d05030d0501050a08030406050f0f180102060a0c09060311040503030f0c16031a04060b031209030114070206060d0302010908160302010b0409020303030c091207030f1e05120a021e03 82
    0xb010340b00706405404100c03020300c806406e200281e03569000798021441400310000705400508104030a5611040d80301c000c50f0358a07e50002155024508540704501612924010070710141003402240c21814840d0358485406140c0300e8124058030b0000303d4a04809801c10001c210307610180001c01d84070b240d49400740e0707589400d03090051500030307000c1410b0514407180ca000e0001810b03004200300824200d035014036080d21503042250041074209100c9030305104682d0320441d003a1400000c0e203000b0804500030060209580780495030024100c4111005802c41d00c00100940381c00c0c402c041201d8001c0c800020b088100350303516449588003003040c0c020024411107a008140c3e09000d000700e5800159414058022198046030b9a8000034050160070310000c40e000c02551100390008a9940214044400c0c556a0b0b0410034000c01e5411001ea80b44440900c070700e800300c0d07203260b408101e0b1640000104040e44550840201542200f01207004600540c007403050611420019180c880701c01001440c0d4600c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 20011535 1250 20010285 20010307
    0x30302070b03060306040b091906060f05040501080c2403040507140102030a0f030c031103010906060e030303040812060d0203150a051b3103080d0507050711120106050d0503 76
    0x1034060740700c44100c000070010862540c0303010aa1980041d0f00200000040e02c40d83c100d2400c054042603206011124042c82d80284403840e0040070888070075201203244a80c4410501043d90424081c503105540072600100311401c01003800500001c00355440202c2604004004400350b04c00e40d0203407015400350300140007180c00c4040c038540911090000310b14004000c0c1c4003910006d03280c0d17800c07810b0550350a00b15081d87c2c0660450850509003006c219600e40c0c64010f610002d06ca80d0050700e0006010b40e9011030701e802c1c00001c07a40141c0d08002c52a0400000d070754801c0103544024600ea40003042a0710480041c5c6041181c58400d40000d04088031500d8891445000c0f01e40050403d03400913005000c1d5800015002d044400e0400c01d001e102d45014482c0240c12400741a200380b180c1c008191300030000512210b18040c00b0303000b0302c03642c0070300158444c01070480d6980a1180702034032141001000e00840e141001d1120500e604540003c9285659400020060026000b0984241e00001a541061 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 20012785 1250 20011535 20011543
    0x308070f0807150f0203091c022508070801092013090605040204050c0313080d1506020601091a090112050f0609030a081003240f0606030902040e0c01080a020d06050303070606030302 80
    0x141d00d540504500794500014a1030303072030740440107a003454501c4441440d1030038401e2002a62802b030401d40310410502514a401400d100d5208031000d034020840c0108064106014001c03d02c2e80100070440256400c001000c00c0610301071203d175102140c819019007900e11806504815400782d400015585000e006000039a400201840b82c04c081c100304000246084249440301160000f00050320f44041e04000b000a00c86840c0c50461003000344400504640d0000304030341a255108014007047ca0700c0301c0c424000d40f41800c1d84035800207000006100b08100d0001c1040e03182d008004440798440981c0e002030508100383c500c005a42c01c00541c0c003045641002031582c000142031800d001240c590346620b00c2400c40303405036030081485c5094011940780b064200d2010048940c0c000c10855a5031100600207004501c1d04130b01450806006111804012038841300070320041e101d0008079507401107044001c3d445400c400c000340b90390345400708458a0800140540a01c40d000005a15045080c06890 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 20014035 1250 20012785 20012801
    0x1b0302090f0606030a111605011d0708070605030601020115090204170c0607030509031005090a020907080601020a02010e030106030b010b030108010e071a0306010c08070b1009090c0308070f080715 86
    0x1090784800340605900c400c821039920070307000040043e00e403c420350590030a2142c4014100b00005030710003003040c4481903000300c0048100d068000c0200703520a54007030701c8100603c50030507950005007042040728025001182e100805100005104800920f01c05010215421078031020f980441e080c000400b00c4200700e0705018920008002001c2d845001840c41d225480c0010100030022554120503102000134802d5907030454418080f0f4603080e5401c503541d80400d102a84245092800700d08201c1c09110700600480060b40908400f00041d001510b11ba100c00b40302d01e030190342c1d07600000049500d050300799018200e4001c00c0c564a51511507014291000701c1203900c2d2503000301c01c0812901042c1d9007090b40482104908980741d0b5100401607502c0641c0031000b50151900041d20300800c031591107454451030703120306841c00d42e90310f645484084410062000f84114042001400403600850107803446030300ca4001201840401c0d034414440da000002e044806410405041071209114007550f0a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 20015285 1250 20014035 20014051
    0x301050702150a0c0e030d0206160e0306061203040b0412110108010b0d0902040209040f0e0d0e01170408130308070606080d17060109091a04060506040303020706080907031b030209 79
    0x182e202c01c19800381610b0200600304a20351a0b0711a00c26042e84d0003032100944802000782900c450aa0301017000e502c400c000c580c070000c801614198030f803c180c0240180c0c003140d03001400170151951072605100320071b0408034000803188030502002a03000008402803014090402c03928035401ca05240c070030b562403100480302c0c0c10701041c8070060268686801c03d594506020200104403400c650010030001c0c443c103141c03103401a09010085c01c1c500c0340c0c0d4104d100c4104691381201c8415001c1d400499150200c01c0b42140007941c0384400241d903040480c242500207000c4c4c4003c62400000b104150301361141a0300444140c0400701f460700070311040d440760400070a41e440143c400580b01d070400510315051002c5a104e4141410042155644a07020004c0a003440110810071410565550609055440b042e20320603820250042251708007001035404603035041e002846500e05100003035403404c000400c43c442a02c59043c0c00400300302110b00240c0b030407054103c2c0030a82030650050082d005030040080e9 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 20016535 1250 20015285 20015293
    0x10501080c130b04020403080405010e0f100c060b040e06070f020105091207050c0310021b01020405031b1f0503040b0109020306010c03080910140708060117060108060d0b0403020c0301050702 84
    0x640030020881a200c510100d400b00c119084101004004102c40600c03160468030219003c400c101c40c410082040d0b4100340c80d801d0200900c90704101c00318020000c03482d0000003040120840340c0c0180c0000c0001c13441003c0c0401c079001c461010508454600400114a41c8080e09001c06681c015440c0c41d0700b16041c0c03000303010518142180580c0d40c50a1440300381642d03000101141800380900c490b16500700028241c60f00c0c0c405056031a00030350000f22080c05942c524400c4004c400a05208507412285c002d00a4a45040c1c1c1c0341816421200542d51a5004a00341d191a0302c006111001d80140ba10a13880d01500d9003001d042c101c003102016002000300700d10420600080c2e03a0000088404c0759030514060107a5a10041e183c0d00308010140566030031803e04000300b5401e840300c20207510030b100554800d00d00d41d4401004403400c0801d0100d01e03055428003030100700c0952044262551102d0041d00d454890b2405503105110720100300c0d0141d005821020051760146422b003c0c01d41c100405100030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 20017785 1250 20016535 20016539
    0xb06030d0207051908060f01050102010c0201060e0117070b0a03020a02010605010905061c1b0504031101020105010b0304080d18060b040c08070210020c120403031205070306030f080306010e030609010b0111010501 93
    0x6035952140f405154418010062038005228425070300002134503c2c0703030a0300c13402d0502c044c01102a17030080c003c0c81e02650a011224007124070504c00c1004407030480541304056464410120305846000f9047d0f40c850107004000302d17005200700000c000c088038951f0300503900c1c0f255040003400c640003500098100484203400700320903501c1605882d40c0d40b000c0e91142403000c01101ca81c0000b0004240f07452103503c6100200f084250f00440508102c901806090303000c0d1a9140c0120b080310070074055007244800510100e030214142c0e41c05030035803e02601c3c00152060344003002015903541280c040b40c5850300c2e0b2007500850b09150040030705596040c10301d8100340c1403210300a5240d111041880e000c20b80d002c0340f5850000c208100d040c41c40454412503642e00c2d916070400038280da0064614a007501d081c80b001c81d02c0c6512a21401c8122600500c0d0400081c050356143c203c254030103042241040307054003619015039014058a401403903481c000041c0c42101e08000f40100c15102e0400051364500001 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 20019035 1250 20017785 20017787
    0x1030b0415060503060907080105100806010611030c2a04110f0a0c08120106090b04030f080a031d0c0f061c051806040303050118020a0c03080601050c10090b06030d 72
    0x28454000c0d5110318101d8040c2800a0480014462640001d5040c4118420301c144940d000c984241038541d81e074001e100b1662180124800344030544074400f816400350004126041c810403032003800c070038404144c80ca052201c0115900c2c140c41a002484002c0208000e0b02201d03040700d03040040160152028083c0003860000080203010310700b080340c061400050910b200d81d01c501c250701e001ca070340306612544403160444800c003610b009000da9000300c3c40c000808109800d005040c1c0b8200e03a40312201504200569039224040e070400540002410b844a0740d244515940c3c100401c05241f42800500080a0003010400990358580141c0d00911041224009211a1032655034049142c410003161681f501a01c1124596031107050030940d00800d0300788001c165041e00864129180311400160445942e0455000c07481019030394000325010318510f60000740501d80715544180305050031402d04192454150600b5001e513110f18016a13190210030030001000555034201400b600140f5030744a01d100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 20020285 1250 20019035 20019053
    0xc0206010501051608040e0403031503052104090e0109020a0b0a0909090305120903031005090601080703050601050904020f12180303010303050c1c030e070902030c090409020607020402120a0509060103 88
    0x7806040100c0000d440200300d81620181298590046205d81e88030758814a0384c0c0381c0c103019681200000c2c1052206004440100d01303020503030790010085c000e900c490243c87c45e903010061100e400040024440010b8a00b424425103400303480081c0042001031180c0704105100809411410700940d0038003510010030ba008444400f91070448900050310341107030500b030711140200d48010840f158544104200c5820101c0610b009500001036600b0b09501d8000304000c0c81c0d4110f604c00c1c001120301000400c524825004142c010a060414a16010280b0044ac091781d00c02c18601d842c0c00000115122010000700305903a100800d20500e000e0881c00c2c4001607124071040c407000c6e080150102e91159240d800b130020240203040c01e00350a505100c1f080000c5c0140c03449940e415694000c05400081c641303e54000c4901c900706501885142c2546001040028504140241d0308011b0038480f001c0140c07070701d01c01007010040b4802607418a1038409180e500b034800041c04251030b0f0b00400010400a24452 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 20021535 1250 20020285 20020289
    0x30b09250501050d111308010606090303080703050402011106090a05100603030516060605132703121e060f170f060a020714010606030209040f02030f06010c0302030409111b010c020601 81
    0x100e00165510081c01034800039102404041c6100880000c00e28004045441b1440450301c1030402800103541d140015550081c140c0b00280209101d94001106140300b540055405071050602000b5a440201100d01d405012204040550b020300b82c100b0a210007040b1a4004100185052103443e00b190307070090460154030f010300b04040354000c1c4c48e41049841d4100b0310207400c01030202ca101c0011031505401070910501c540714050303002c1c0e81c0f9a983c07004180c016443d0315010b40319852030319585004100104401481c0044003e003101c0c41944100c0c490041600904d00d0b42001448682041369100b50722010300c2e202000c0d640b00029118035408007140d81a4022003041300103844030f04a0400c0014054048111a070039444c4c0140420881d825038090805c07140103407001c0011001185a49049110603580d241c541240746000440c1d41d0307c03404001031064071a02c162810982d507028224140d03482803180000d1108c1c00301340040c80514201554001d4480c1600a1154072418140a504c8102c18 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 20022785 1250 20021535 20021537
    0x105010312031d0d090617060d08030903090904050d030507050a2a14070f050d020307150507020303040f080d030618110f04030b010306051f090203040609020a030b09250501 76
    0x140000301d414012684442c1451007100042d15550f13000060f00800400c0da9010300300115014480e01c40c07002c5c402101c018443d80b0f002d403044c034441c41c3c503840b6a200c0e80c00c01011880c4510007041140a0794442d0b062040c001c610840041840803045036001d020f80d400180204c00b0040c1c2071040d80e07282540140c1c941b06d401303002c4011001c0c0d0300e9901f0a070400030701c81d0007028001581c80c601100c41c0340800036044040310590103154620a480e541040b0150b16200700207035059000381e07030a000040512081410796010340c1040c1d032401c0703c1c07503012030300f190010b62003014419801c20041005810030300c110b5081c005a85020062a030420b0038010a2060190020f80060b82d40d825003004002990308031a00c18460016003a15142d072480d14621003031f400d00040b15242e003400046030380c00c40110030032440c1d51b00d101c0d03a409107030781813031440c00c02500f00400903200d0b82d440345604005a1600070940300518059050f01d005813502c0881c0314501500c00e0305260011442045000c02e421404515006450003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 20024035 1250 20022785 20022791
    0x601061103220b0318010c0201060f0605090319050303040303050603150103110a03050102030c09031603020603060603040606120f0308060307240c080301091d0102040302010509040f0e0f0105070e03010501031203 93
    0x2d01182400998181c111000d240d500005000c2c400104031884024000400b000780002e0440e0700781242030710075500c11800100c1d00c3d4081404058054806041448005400c461081c98941e441307110f002d20b084000e41e02a04000144410305602d4040c559018406600611a1a0740821004030050052001404031800b070101c00c2c0c07165480380803030340c02150000020354803400e05400d00d100f141d10034002e1611030f01c68420380954003c03034003106c101100d8008184a040d036550780d040c0a82c581c030060080714165a64000407446601908501030030b54013800c10012075410345c0c5400b404949015018500c00d50040004003e206c1031074581c614041c00440070521040400d0340252089584500000e00068001c40041480c00c8ac0f42e0001c0310030792607e184480d01d00120704440d400c1b40f2441c00080e0000b101040400514105508801c0303880301600c0b400240b003641d03451201c3c204403c55180400d6651a481444503040c0d10802e1210fa01404400070409945035a0300d0007640c011000f003007018551 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 20025285 1250 20024035 20024077
    0x130c09020706020c0607080105010314060603011406040902120601030605240c03090306042001180e130b04030305010603060b090d480608062815050304050601061103 73
    0x8255019034600c440850f04883c401c6c00d11002c0070308029424010740380064580b000b046e54844030300d40700c5030142314080c144a146134205418020000003202c00660010385c20000050780c244144000c10302200444614141c40c10141c0c00141079a01c680e100c81d03c25000b900344440d85c40c852800103074150b410041c440c1e03a99000c1c064442e08601408042a515000c2c0d00100003c0c40b2003000040c00d00035144080c7c619034803110b001520305c072281c8101038000340d24030384080c080710708442000d5800068081680304107500c603507034034015000100c40450000341c84000400c140341c2c040c06000040c0001d0341030203090003010f0020840301ca10180e006409540400e403c981c050041d12203461038001c01101c4400446c0f810400780c0460811210940b00c10120030400050f1640315081e02400384134003c2960704003c051f41c81d074401c0c800d050118011000030900001481c5d09a040214140a409440740c90302c0385002e0030064102881640464203001106401c0c007903408000c4101c5500c0c2e65002c20010f5025 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 20026535 1250 20025285 20025293
    0x30201020d03090516090501030606060f050403110307030b0405030d05010b0f0d0506041b020f0c0103060f0308030402030106080f0a05120304030c03050c0a08030c0c010e010b10050703030f090c050306130c090207 93
    0x801481100000c3e1000d0502044000c0d1702e4201f13070b045e40e01800c4117001181c0d50700300854440c0180c510140000310284424000540d0211201083c801e00400701c4142507125100e224501c14165001c44090b400005c5030303c820046809024010600ca52919040110b0600103010328442c0145480802d03541d640019003d641d181c0c022403a12521010100041a0344034000e5900c03018110040024403a030388150800d98424083c10090340d402e0303100c41031264550b96400041e50800b80040741c1c15500c405020682200412100300e035102807600a040082c518100942094110041c1a10480c0c0400801001c260010f4501140c65454900503035281500103c107410030034030b42f000405145000090100c400401d0f13014000400042000304401d0f904141c0407422200e4030507403240c200081503403108425000760041c09600340642804140100c1000c103610840d040010708440d1702c83d60300001d1000303080c01c02845902940c0100360131755405450701c441080071014800c0c00401074000446100304 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 20027785 1250 20026535 20026543
    0x203061906031502030f010b0304020d080a030b040f0c1709030909090a05030406050d0e0102030f010311011701080d09270c0509030303100305010507090e15030c09010e04110406030201020d030905 86
    0x11a00610f0740c03005011449880b101075803003981c040080451030740000c05c10068440072240610303401004403009000315981c0401581101111b00103141d074a1440e038a03191628041c1c0f11070f091403500c002500b03800b40d901c05800c1c400c0301980092698031104c20440410400021102241030869210084d6640c4411461400e29002c4008000340808580040c0e5160024081e107030712a141740e0244a5010a803070160300700d010448051120a00010041001c00d842d040712040586040c0f4110601c1d90380801640d456110a91016529a00400004461079442424603010b09034054201010348501140f4404000a011a00e8102541d92010b103960900480c1101d0100d03001038256916131400c8020040d0701070b094070050745c00b5401d1400141d815489100458195001c070003101c940c9407100e11007404a49910200d40e03405125059a20902d681e079001c0e414003c00e020074440700d4501d40b80c9007003200240a0511240214104242400180e80225401400301a40d02d0000345020841c280b6030b1038 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 20029035 1250 20027785 20027789
    0x30605040503040f0b0307031a0904020904110307120b060402040302010801030305030c040906060c020f0301020415051809011503140601050a12060e011d010b07020a030b070207030b0f040b060109030203061906 92
    0x2844030401d00000e10861505c0035511894440e281000004502c18202d0070092411720345075809182c0f000040c0040c0303001202c00b50414019802c2d812445140c00c0404d1030025542c0081c04201c0604d1100f0040001000740300e86d100d1410384c1d096040c80d1940e070000e031041d08c0601008040c1700380480000c9039a241541650b0042a038050140486039480301c1c0504110312408050f4041c05104000d031805090500071902241d0f5815120014030159040850381c0f50442c0704480c140b05000c2d040340d6070701c0d03a0f41a00313180606a02c0200d003061295451004c1c0464545903c903540c054074003030030004a0303a0000260340043c1820304081c02c1001c2c00c039020f04c00800345034202c0d40c013000b10a0004103c40d00d000c0ca0440c2c040c5c00c03401101800e640c031024040300703501071640020740c04500c481003480040c04d00506190400040d0049400003902da544403030040d502110b0740c03286110f19101304000c2c810f890700394176000032083c03c2c00c40440341580c002c80d4070342c400180a411041c1d16610f914041c00035661041d00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 20030285 1250 20029035 20029049
    0x30e040207060b10020601030302070b0a050904050106020d08090109030e040f0b040c0818120306040e0f030d0b0f090708040b061219030201051609061803061505100507050703060504050304 83
    0x50340791403a1501000800605529034050f5000c2000e41d5031183c00019902d050325007540052113018a05110420154400002c00d001c22206000a030060346550003558040d00668014040c00c1e4030400e0010b1801070700610242690703052141303440c0840d410101000825030246c4001c14400c62014903840034102240c0d80c640c0080c90b105400b500c5584c071503034040c028841d842010b005070290307141c01990381e5808004031740492002c0001c40c2040c0750a50102c0d00300700c610320540d0510101140494256080b070014502c52076210115a00d05180480050400780c000316405045410700c3c0c14024046a4010802020003100c1004140c041c1e0718401e414140782c06c903400700ca84127400c440e078000c00b41ea05034030b04401541c00c003000308030b0041c001545c40c0f48400d42d40e661800d03240d15040080359503000c4220b00000a8448500110100b034150144e101d44440c0105680107851800040c03107010061482001d04102c014040d441c0054004121841100d13000b20010480c0d85807800c1440c1144501d5200d50307 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 20031535 1250 20030285 20030287
    0x30f03020114090106050f0d0606080609010902041d0316020f120115060306150f09171605040b0d0204050c0c010e060103030e010e0612100b040605070510020c0a0807030e0402 77
    0x10109541500701c1031140c0d040752031010031a11180b494500b40d802c0b03030007030340d500c0800d0041c2c5070300504203006200c41144c010f850100301d60b9a80c90800e82400e0080d90124401d9460740120000c0d41803030300444002400d6916540b200d0207104c0c03d540c2e00c900034010f242d0842000c02010170250b694820b400700c09603034020003d032000941d003410503000340141481b1054003400c45000160260092240c0c90407122005042a803a4000400464040c04542c003000140194240085000e0711048170500c0c0f080101c4005240c84000c110400d680b144980d030081d4840c81c2014401c00807511100c101c80607040d81580c020403035072600a120503581c0140e202c452210341c80c15500fa0211400080d13554100c2e0f000e611052a1180c072040116034401c03202c1d000e242c0202003080300450440d02504100d51000000c0c1c401b40302d4503215286aa415441540700000240022580c4400d00c8014850450200d81502e8110b02c0c001441c040c0503160400c010000c0d008102c0400e0034010300d0300030100401d003054020411 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 20032785 1250 20031535 20031563
    0x20a050d1508030403030f02030409060b0a020f06010501020d110c04050406050f130209040206160f0b160504120b0408040f0801090b090102070c050f0d02090405010e0111040b0301051903 82
    0x606a0304030810140030300d0705010307034481d0881c441001e01040d070340c1e0701024600c0c15085803030070f0b03c0c001200700440c0c0c00c51104000000b0680405c0c42840d0141864400d041e40d1060b640714000c0c540000d034004d252851300400300411440c0c0e00011251007001c504c1c2420020b01c2506413605061405943c815030f003013410641000700300314617940b00302e21038401040c680c8210344130402c2d02d040c41c0c085100003e400c1000000410050f180a2003d07259102c8098055030041c039041d80c0d82c3c070340c402d081e200840e500e180e04001d01105003a01005100d0121891030300a0500e482c00b8060700568442032030280503100c00c5030200d014000c440003154082c050342e40da40f07044907659100c420700030400c11809a500c002c0e0385001c60300c0c418040c021500c0e0300350003000c004030142c1000c0c108800d0541060100e40e10050701004880140c842c91405442a40504c0000070200116101701d0b0039944402d9400f03842d0b0800300001d00c142200c201c1941c3c19520252010305100000030058055144290005000c0d54101004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 20034035 1250 20032785 20032787
    0x20f01050f06042708030c0d0f090b06010c030917070e0c0d060501050a051207090909050105040203010501050906030717030d09050a0201090b1606020c0c0a150f0f080106050a090801020a 82
    0x8102c1c094407041d2401c0140c404010380c41035002c0080300d003071440c0c003400d0414603001c540504051508000840800d901d4010f80e070402d1800c0341e0200d004004215118200e03102449030031103d99901100c203007004006e8401b241c0e001441c10b091805032545220751300c03004420b0740c00308203c5680906858041c900700ca0505214182c00d03078002090b1075030b41300c3c00d014011902e5403141054900b40c1e030903a100c190608600b5564200b40e0400184081c00b040080000000c3c0d10000380100303942c17180207100000781410180141400e45078160040d60066080303c00780101034400084180c00c640c40950415542d2908404040c00c41c03240e401480c50250402e545801809800708000c948640301741c83d641c1501b5030b6003d060140340914403807281e08810b00c0801c0000304030f42e07400501052103160181c1c0c5a0a0541d00016000c1d125030300028505000520040280c641204a03840c01400c181444008010107004c01012208140903100821101081c80040c00c1d0003420300d00d002d0180c1c50001d64550a5601c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 20035285 1250 20034035 20034061
    0x3030504031b060905010e03010e03041d0105041103040312060807030305040e0f04020f1302040b0c0d0906080402100c0f02041409120c12070305070b0103030302030402100513060807020f0105 84
    0xc240e070340300810645070b2100605010640100e5905403034418805103420700541c0e000704110f051a4055480b1591030701446000d000400140c4458080e61a10303200d03200b018014440c050300000d0060b86001038200c0300341d6034902a02d500607494601560240c40300000c5401910003580407107610300c1264030110030960007034054400e607400c404001e030480d6668110b84120040c2075a0180d006018264401100d040040f03101c071003000e085802502d060b81d54a81c49440354049280103240d5004507840c0c044072940150054024240f40c60402023508203500040e0582d2990398181d01880810b06c4039204001c04610580b41c3d83d45c00410412034401112006044011700700d80040745401901648040b002c100800e884545020340010718804850080040e102e034040ea40c00c1d030034401c09108020000d000c090409020310300c00da50150301d0f0b00340b510501c104a02103280b48010b000c0140030200e202480b8035503240803031b0091f02d007034001920f9120f070680c10021070b9000c0607090f500b84010060307d5903550b0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 20036535 1250 20035285 20035289
    0x180d080408010f05130b24091302040605030307080906030403030f141008150406050702010b0303040305070e0c0403020603070806121506030c06030705030a020f04090501080a030e04051003060509031303030504 92
    0xf0414030081d55004811034280f1300894004021880c1030010421880c1101403d01900c2d1001c4040440d558503900061503515046132103910101445403041c0460078a801604010082540103509001d840d540e281c00d20b02a40045a00600001c80054280740c420b411094000c086100100021a4012401c3c1c1e155070013240c10602e83c10780c42d40c001034510340004102081c82c00818000242c1d40301d541e01c604c0640f10180c0303801c04543d20340710310080b142c2c1d06200030710003175118800408506203401c1102a100d90024400c41910005000400c0982c036a1400c40761300603950701e0031800a583d42c070b0000d0250005540c1d500d40714840c0c00800d003201040c01015078080c1400b1001c8443c560340700d4007041034900c002c5400c0d20005109001150030a10141c01400000c807000c802907041644032060380307040304c05c04d9001e500b00d90b0180250f1424181c001c00c0c0399003009401d6800f4440752a09000d0307000f500074184001441261394000059010809100703449403800d5076136807402c03065a00c0c10002d00640142c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 20037785 1250 20036535 20036561
    0xf0b150d0b0906010e040e010603170403200d030f09030b0a150b030c0415110303070923010912060207050f03031801090c0e09010f050106110706090506180d08040801 73
    0xc20304040103440c200b600715201d004140c0d914056103100c4c6044c403010b0302040b45074034081d64903200c2c00f00005001304810110b003500c241c44962070304d2031810008d4600410f40004040880349031036110594941483c580c003095058200b40710302c0d17001890100e510503042d80c009030010700440d003801034142c82c0717811208000740300e5400c000c0941d403a40304418583c03006980a40007032004000070030208526000c0100440d0721810300540036450a044541180c2c002c90303e40740003ca0458060105ca440d003003009114a002e1071800300c05c1c41d00400068101d94a0b4015000a10b282c103900c2420880c068040326061030740710054403c91000310011640da42c00030f40d9501085043e000f2140b813600302c14440e2860840d00041c51440302807409c4d2020740e510782c0141c4503500395501c0c0c041600e043d00c903034003501d4020300880d80c1e500402c007448507007581400f030b96800903010404115010040c0ba5285010340c0c0980d1000703e26042610000320020300c00320b40c0408000c10394130001c6030004140c5070650010400b0841 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 20039035 1250 20037785 20037791
    0x2e0305030429030109051b07030e041a03060c0903120d0507090522051905090a0b13030e06030c040302030a03020105100e070c150b0406141206010b0304060f0b150d 72
    0x2c0002403a0000500010103030300000184010444a0001d0300210f13040840c240100c0d01c1200c861400b084558042907064022546e07400607a100390403e4440c00240c0703003800c4001060179040000194a40402400c0106610300201d0401030710b503014000c00101072000f00003030380d0300c05607543c048000c0c010445082002c10a4500000741604203004c2410390303564100c00c801c51044482059000400b805080b0483d0008084030708014224a4406c0e140a070320a603000f000c2c0c0e00301514048200840040048881d8107880c0d01150000350082c41c1ca50b50580126075541d00ca0747c8520b0801850300417a07002a506100c4c0030003000c145601980010300415a44105030703403040d00d07412030300004041900c0c14000036100410003804542000c000710010020280d01003200340500d000182941d11b035802418550301d51491406091810300920441c07581203030081c203c6980b40041c200c1003400000c001609444c3c46030003043c0300040c181d200b101d03402402010042c03260381c4803020b060a60003030400c00f0540341ca = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 20040285 1250 20039035 20039069
    0x50105060f01020a030309030302070b091f02091c050c030a1401060501030908040501050d0e060c0a170105010e0904081309020901020f120405010c02040609020a05070203060f07082e03050304 84
    0x10305104026803070106800505005200761703401c9000340102c0d0301c00d80400d5420f014800002d4038020406004a00a10080c1440c01d0f09042c0075801b0201c00403d450b030144100802c41d0300d9298a248004030203200c1c2c400d4000c070121400c040e030514010b03200003945400341c40350070270030802d40580c86190038040c5030003000070944500042d03044400a00000e08140424481044a0340c07107140104449031189101041415074220242d00d0690151045c46440c10041440c40a50b580441c1d610003a8070101413052041d4901000640303a0380300580036074014140c80b0006000d0082007011601d004100c4030ba80c140003591070a401c2c0c000e40240c0c07071160042c0101d22040041e6a00002d014407281e10900c43d01c1d24262801006454090090f00100d1308162501400225010a4030207803103080400c0d210141c1d207624910400d07062030f03c0106060b0b1144640c005010100303074000c840341d034440100d00c2c4010301b407559029404000b0504840340100c0c51161900441041000b001810484500d21600c44030303e0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 20041535 1250 20040285 20040289
    0x40302120a0203030109020313050a0602040515180d05030c0706021f090b0f0601030e0304030605010f05030601061209020607050616020f010605061812030a03020705070509090a11030f070f0305010506 88
    0x84598203012005074011300050050201c1e03039005540041e01281c14005203017140d40c0340c5082000400043c0c84d0380364049410480382c10041810059038040814461900c1c1800340516200f00a084540d0300a46040040c0010004200207d42c00780444c5411200300544d194070081d03540c049001090075050505584010300c0003180550b42140d9444601d00000351b03140d0b122010945001000c2c01d04043d180d9000c00c6c1151070a000400141d4040e00700481e040d030500400803180d1585901c0319000f9400000104012548034202881c60721100c5d0022900c20040d000082c03450007405c9020782240552814020b081c1e61b0701c45840c0d01160980c081c1e0702d4036010b080b8020708980b00343c4503150308036000300800c42450340c1c0c01d007007a035490b03000400300840c3e0385201d000c0310f2850b0008014040440d40c001180001e00108120040040c04122000030143c40c00b05040d944031a18264001c03c90031070483c01603130540e07043c403080305614031a4040700c6d80301c0e54424171032410303107464441a14203504c0c10011032114 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 20042785 1250 20041535 20041537
    0x30507020a090903120516080402011808100c090308030c03040c03020604080d020c10020d0e060403050106261c050315030102031e060d0506010509090715030204080607090509010b070c080307030804030212 90
    0x244580c07128a1b21f940d0000b41e0a035024040244100d040111a4603100041a0084a070401410081009000c44183e0504010842c0c4291410b8014003900700000c0000420010440307601c050220580707500ca0700c651034929a501d030203400c02503000e40d0104003c100b1541c00105c4480030804c0d5030807106900007010501074a26604580e8000507080f00d98001f25007401404559080340c0701409051609640c1e40310282114220341011400700c0d40161011180701085880b8030445124601400c005110782842c140d200d228082c042041c40320200000341c80c00795012203020040e00140083d03589113005200c80d0b4140318a50381010710782ca080400300342d840c00c0501140c00390550045c02850070380d00342320401644220081c5140758522075498042200b003280342c0300c0780d00c04810307032005601d0b81d0900384007a0038940000d1030340080004481c0d0402007a980c0300480f0741110045030403241d130341e5400d09000702040d1003604010f00f02d00c000140c0c02c0415030b014600a02c20ba000c0c0e070a40304000700d100216401e03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 20044035 1250 20042785 20042791
    0x20a120c031109150f07051501060201020c03030a050402010507020d0b1909020a0e062d0108090c01021e01020d15050306010602060f0a05220303050103170403150207030507020a0909031205 83
    0x76440512885030f0504009107122509151915614200300f10740003d40e130550301040e130441d00303078006a07040382d080c07440d5455203801340140d40002d50800c0b0a42030320b142d680c003004010309589070b25100801c00b5640200704592050380c01500390310b80800f9a04182c0c074440001d40b80c0c0403a01001c00401400c1603420300c07880b10060741c010101c04c1550310705420701a504a0280a140d4445074a0400d0000d074111040440c4107201c003c08000001c0c0d812000240040304000e2050715140c1140c0d441d042035a81c041039805520355801c06c1e9510340568001400e009024001210740554030b4000c8144002c2200b80320700048400071001c68413241c0e00e44104985075503050300e804000c4012311001c21443e00309504645e5101ca0184001141307040c210942d800046a108d40640104e646c4100620a00680d500c0c21402c0e2007850048030f16091031603880ca01c00841130010759910300da001c030b0310108240c80340c02180c000d641c005040d0302030161142046e000418084400310080307403413031002d202c0c0300030140a4244 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 20045285 1250 20044035 20044061
    0x3090308010b070314120f07080402010c170f04060207050a0503030c1009050102070c0b0c010b010906050a05130b130905011202061902070504020310081e03191101020a120c03 77
    0x481e403901d0340301e6600f5004254214180640c13401c200c041d9242c400c0180910b8608480c200c421411304070541c094a0002806c05000c00906c0303001c20000d030760000210142998401401e10700e0310f0600d11202c41d18024016011034100000a000402c503900240710000d40328100d1300a281705a40b2310404d0b50f00c0c450601480115007000000040d071041a0b4018500140610005441d180b030580e40d0602e0104150050854000d012807071201c0010240b0500c201d240302800c10304038041c2042c0c00030300715005440480b010424001030000160004a086c00020003070003d00503104c0201001041d840b41c51801403614207858040001001c5d4802c1e030090300d1090b0003400c000c0c034200544049110f0038241215007421b6208001c0005001c3c1c6a602c021031140800c8280c102070316003041c10540c02c0c07100c080228038460007128220386040c10080200c0e4070200c540000c0c07101d0b031502c0800580c3d9281211072071122551020400780c40403a00007210004400001c00104030700c1d14480000d40c100e58006600354 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 20046535 1250 20045285 20045297
    0xf09151207030611030103060e0d1d010203070f050a1205031303030b0301091506090c02010605151308031201061e0f030f0b04020c01090507060807050a030506010e040c081006030903 80
    0x1019091204041a8024061058a00320740d02c039158071041d03c0c9100c2c0c10300500ca030000010400d109440c40f0314498124030401405d4594540503009140c1019043c210204104810094056a00030001c60300300541c40f02c02c0b00e8800ea4a03041c940d840700307a114026254400022030000d00c0a22590449200d1201103400220103100c0e82c03030440040900a4902e40c01d07668480701040070806440c204010141c601300c0220b900303410001001c0c25070305408000c07015a81492401d1046580e039207800c403d032503001212103480c0d00c0c00011441e000450303a40824000d000016102032580d030032114a6060310302d01e8541160f0040382c02c8410314030341c84400300000054280d095814413103100e9000701c124208a0f07000410350100d00400182203070305c440c00340a4640e5461040c401080400e100c94001400c141c1400c4429213400070b0050704900c140203181c020599038100085550b8004c540d200e0120f500900b04101c14500c9000242000100303803031144404041d84800102070344031b80900086554590703107103 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 20047785 1250 20046535 20046571
    0x501090513210903060e010507020705030c0d020909030403020a03141506060703031113080703061406060d09020102012a0905190b0c2401030c060816050a02010f06140f09 75
    0x2900282e60300300000d808218156038000045107007070082c01d8480f0304040001038170307003003000000e460213005901c000e00035003040048903000c0e40d41d0060300380c034150195405074080d69059503060841c811500000d6000c00040d50220a1180180382000c504400340211445205903100a00d0350103030840750313035a003c401000750000281c8030b41c1040307207540c10100b80e044c18040202400c0b4054800368008501a900c15041007003480036a000d0020507d0200030b182c4e2007401c2440128036288602070b00700206c192551081340031039100354080465605030b603400742d1020121440c808001d8140700c583d140041c003043d002049d03900d0000481c1c0444880c81c03944000251401c001c0144540000c1c5c40c6075a240924501c405034101000e0622800182d030203c450769035030443c9841d41c0c20405a130070550421090700b04001302001080740e00c810419807420031540750a92078030124050441c450200c03514038100100054840a01103506480030812102012a62000750074030100420890300b4a40c902150190 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 20049035 1250 20047785 20047823
    0x90f05010308090d1506080c01021506031c09050907030b0405060307051f090e0405010203010305070801060303050901031a18160c050a030f0c05030301080309010311070b010b13030b01090501090513 87
    0xc200b0150b445650f801d0003814945d4262001c884203540308450782e811200c407810456030f041c00200b01c40c0c0c95141c80c0c024981010000302e0f40e121910480d2206002c910248840f401340a880000002c000040180c0f0081c41c0100000b4040c2c04110802d50240c1c0c2814040740740ca10380850b8000a48002400220001d948407008135241c0da2088205030070701004140104111240f40002d81c4540d020300000b40e40d0b0751441c588280340009943c000d01240c1d160081c1840002c0d4060211803001c41c09280118a00600c014050840c1c941c3d10901580180c02d80d0100c8210180034034520b1003641c400c50010310380000e200d0f05640600c1603402c020700326042a81c098000a00541c0d4285080c15985011980b10f100d070350354145194001e811840f010790000c201284c141d80d1500410440285c07a06020781001041d81c1c8441e030446060007000800c40000c1012115840300000c644025038014209108035651103906000a01c828040c4074125030a200c0010078085030200f1426580c0e50181d0040c02854020341 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 20050285 1250 20049035 20049049
    0x3040b070818010e03030906100605040303080c090301020705070302010201110a0e041802100804050610051e15070b0619080a080c0a1406060a0504110a0503040206040b03070801090f0501030809 85
    0xd49419100d016402e40070800d000d204420700118540001e41e92424201c2e826481c1c8500201112075480d4a85814001280d115094904a90741810289015100d2030100300c0d450180050498041d8070104100301841030004980b0201c038002e80082007803030448031a0b40341c03510a0720007110118801c1040080f140c102a4408040880c80c0407032041c80d98100d60014881d4500503070200001007110b0140400d105040c8021a003042020100c205040d1600c40410750b895036100f0034a00e03182c0e0180c0313940380c04c2d2610031001c1c10751110190003075032711200d40c0b45c2031500140c2600c1c030034003d44010241152001c404602d004c00d0305d0f0a08010301c42c8210381c1e40c0c0c40301d0682c8111070300100d90090304011380c0002d80c904040c40e0750300c001c1c1020304078902e0001c00b03000b1100101c0d4800ba109505045282c00202464401c48152100526100307640ea5201d0001c50907511032a84010f480700c10000820020550040e1400e050300c04040090000c22001425403082c0c0b60700380006010000d04000f10122072900712 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 20051535 1250 20050285 20050291
    0x204060518060c030a0503040b0a021602040b0a03050f0307030305150a05090703020d05040821060603070c110604030507050307060e0907081801050a0b03010e061308070c090612060c020303040b0708 87
    0x142210300d00303402c5480383da041d82c001082d1a00805d00100501c020000741c0320b10240d01542c200350440c00c111845140a4540c9245400031303014556540e41d1540301c1c0ca5840314107018503000011281801a41d008641d40c81d40241400e034002841e02c80450032032a001d10200c00c41341c0000b441140070a0820003000f00088011300301809040c6d08201c4842c69400b20b004503440345010320603045e25100008040403110340c0030907025100e00803510070001f250b035551059982003180c1c1d25119014480034604a10120201c03801658007503c0230030001704001d2f00141c81000d40f44181d051314083e56544000b81c5008804200043c0e00a401c600002c150303a109084055222070b225040d0040f00c02c000c480b290840ea004d0702d10404441d2502500315060409016590308565503034020f011501c2c01c014001142104000c005040c2440041c143c014844944c442001610003c1c60804c641c540e2040480c03a020b03218181200c0701030a120311805090b0010050302c2c8110381000d0248410341e2070345400c42d10740c1402 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 20052785 1250 20051535 20051539
    0xb06061306050c0c0a1805090312100906060302070f12020c090a1508030a08010303051c02160203011d06010e070315090507090b07050c010809010f0e060609010906031713090e03070209010602010204060518 90
    0x52001001a00007400104c1c021060034007105490344c2407081e46424dc50642e0030020a050040040c00c001840210301c0341882c94200883c40139043c0c0c002812401c0c2803d14009940c85851003091122200b5582e0041012000440b04130350002d94502c0800d0b100d016002c02e800201c0c0808004101080c09031004060f403090320b8040c2c040c0c200e00740c80d500f01281c1159201100f902c0044290700e086060034441d0040084681d071502d150710100304a102d96640050264040341c05007031000c14503060094024201982030814401c200c903460b41100002003a080390904001090300000043d180100c900f101d054030f8002c000740039011040d200651700c0c0c1c2c0010700358416070340d650070003074524000034406c00d03c001c0014030240c690b038101001041050801070300300043c1140703490760410000e200d001d0145480300c00d41c04041d465401c030405203400303001d440d407080c52141e007452540721883c540407000307241040c070848060703145988441040f8201c2c0114003464010070020003494040784500304181c51601d00c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 20054035 1250 20052785 20052787
    0x9020d0515040902030a2603040614070516060f1404050a17090d11010c05010e010e010e0f0d0c0f02030d030207060507080106090b0d1d03090a09180b06061306050c0c0a18050903 78
    0xb1100c4884c4140d82301b1181580d03603942e1000300c5c4d00c800c0703035000046030400c10902e406401c1c417010280031440f803010040c00400050351060858240305e025000b00b07030f1a4010904140302c518050503d26111385210000b22044041d0090b00780c84600c4001c00d40c0c0084c00e001d01201d00070700741e81e643c81c090344107650040d5050019560343d060010b2001d0060441c180e05050021460410010646e42076131036040c0514403581060414142c608800608c95400e80328900d05071509424505182c4003039600d10320f010b501805001d8801c0b107040d41603001044020311450702007140360380d110300c00c5440c0c1a00b03001e4038000070940a001c2291510079406801880130000300040c604021551807903141c550299440340940001c107500e605446c02d4624000205a0030b6000e010740819029100304920f10180b0040035501d1040100d00c01d51188800c0c0c5250004107990840342e02d44814002c5c0c8107802440b558682481624070f4045c2ca03042800c802c10864111010040c405a510301e00c18003d420010015055448 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 20055285 1250 20054035 20054093
    0x607200c0301090804060e060301030f0303110721080c070b04030f030b0607050106080f0303090c04050403030609020a0c0204051006080f060612070804020a0b0a051602010909020d0515040902030a 86
    0x2500780703e200c1159101c2c00c55955510f240c43c60140c182c4041e10f1070544546c03814801000450200981110744075814030700002c0c80b4282040302c0d81c1e070b0700130000040e2501d03000c1c1c9207410585484045480744d0101135103548550766a03d400403261880b1717604000b003003046004013040009008541210490040b802c000c00ca4a44d0b040c0440d81316040f043c4140c401d80c1d16a03208101d05030701445200c1002d103c8038055032462601b442c41c2036481126420441c084c9548000050a243c8030340d100e48040d010400056640b119945001801d00e000103505034455450600030543c800d1908142100702c4900c2e4071405844d03030311502440d103880c10050029070401030070002d00d0076015400308454401d004030b45405400f4106401400340d621065042688003607020006a03c4054000099680742a00c0d41d000c00407060241c0700484951100b540b1403007241c2e001040c0650b0520840d00074601c02d20311000004070000400c0104801d5884281010b501a0000c040300808103014084107442c60920742e000410940c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 20056535 1250 20055285 20055289
    0x106051f08060a1206060e06030a03020a141509030310060f020a080f0c0607051e03040b13020d0501051302010e030109030503060904060b180601020c0406030c0b1c02040303020f0d020607200c 84
    0x291864074101e440340d40e00d16040c4003015070b0b41c07c03840d00200180c00609003025517943c042d60390304100401500c0b4042d44106c800c1002e408224002090035014044030081c180130030380c1c50743d941003552280c491240749080811201d12681000c4d0f902c0c90035a0041020055a481c2c01c401c1e44d01160705042c11980421905072a15020000b00340165019074800342d840c10ba4051401c41c042180110107200c2108105000c00b042e056230745682c00c048008800d8150060500c001b52aa540d9400001e2440d42050100061070000c004101c4006000381c99441d03809800303804044c204d8180d120020046401407010610f05d0038440c2c407260f03100d40304d10800100f082185001071484852010307100311f4100c40707004000c4c15590511180c0c1c0121400c3d981840700350700b0b50703840c0c2015a035140104c0078a188040340c0c01041d00c003135a000030700361180039108655541e202d00b0000c2d12040329406005043c0b048801410802c0d02c0055100d1052402e9070710803c861100100d00c3e408071102410400040c450854041c800d0307 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 20057785 1250 20056535 20056559
    0x141b010b0406060c0507061107050f01030209040c08010503070501020312010b031801050406021c05060a03021504090e03030403020f070b0306041503061d06060d0312020702040621050106051f08060a 87
    0x54005a04e07a003040301010b10b0414034201454014004108241c2407603601e84100080b03103815290f00711150301c010340304400101d00038050200310310350050800b07280b4201c0039081701c1c041e810f07a2416019114020b0b11807005a07980d100b05074100f00c0342d1200a00400c280c0c280d240c040e42d0405030043c64045450200805142520015241516060340c0020060078484203079640c4d01d01e100010105101c80e02e0a180043c490341c03c00c0c4800f03401610010214034402e201501280e01408504500700074030900c00f400c80d6502e410440d8214007611070303940d40c40b41c0c40078005000700c100c50080341031038a180d45510500024040d2490018140c41d00010040300080c40b90007043d1068501180d4440541a0068a04c0c40c042001e400240103a0108103000c0200f6406100a0f4011140e0710000daa90f25851010a00400d100e601011640c0d17401120381d02e140808032500c18915000b00000e0044584800801240c2c2c0c5013003002d1880c2c40808004844464001d089241d446034000708124480c554502c00003503c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 20059035 1250 20057785 20057789
    0x3080a0e1614010f030605060d050403050408070b070b090c0a0b091302030a0e0c1f03090c030204020f030405010c0314070c031103031e010806060607080c0f0d030504050607141b010b0406 82
    0x2140c2c41031490b0640f564040354601c1410b105180a005a5240c200400c3c11071252180116101740c49800003130615024008613402082d14034212103035980d880c1f94107a41c42c0c0058004440c030b04441c1020030000400000c4c000c000800050000c10b095244c048000259400401200d820000c0351040e15803007140f40c80550701c54002c840010500c090021501c5041c1440200040c3c8a50050f800304e400034424884601500c018130700b000105104a4203000d0402e0400b0f070f00c002e60040c0000740c1c00d064061040042c60080d403040c0c00070702080c8041c80044d000c1d12341813a501d11003e642c9100040119109080b401c9005010b03050840c0c12101c1403810a0a60303004a502c9000e144032207100c40c24003080ca00380c1500500303110000e80b03e1410580f0029a0358840c041d40a4001e00c07011035404422401884120803140020040701c42c1e030040603101070060801200c00b9540c90090f400000c490b036000b01d501441c922000b041c0189003031000925500350484400407003100790350350601403507280c40c1c511803c00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 20060285 1250 20059035 20059049
    0x50711040c030504050c0d08031611030a2703020f0d0201050c0114061005120106030c05040e010311040c020a11010807140304080310170703080315060304150c0c03080a0e16 76
    0xf0145854244240b5140020740460701860411402d4008202080180d0303400030800b009a03084203c0c184001c031208031f81416040d586000010f41080460740000c1090f00f06c14100100304d65105540c16a82c1c8003805900c0080e40011100404510625020303054084c2c1c54814181141030a0350741c003085003180c0c1c84460008940b03002d503091082230710344401c80220b01041458024509840c00c100d03946100d5041c401e20342403540300e451504107540140f05440203090503603000452503030340f0b050803d100b100e402800f9014500c1c248503812554804a20403070076039000394615040481c41401107400060007002c10f02040f01c859540000c00720303d0401103000780e0080096a4481c00d0981c441441e1035a540e00c00d6049091550342d89481c1f0102080711421281c100f10403680300d03a100e10000710104071141d0405e9010350004100030412918040090004402c1c0c0020025001c2c120b40a03591140c01004c0540461202800104112407c0c0c0103c0c00940d00001a81d42007650003480903500b40c540e4000c46 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 20061535 1250 20060285 20060291
    0xf060e0f07080c03011505060903121206040f0501230301020d0c020a050705010e150d0b0d0311010e1b06070c0302060a200303040b010905061f0509010305060f060a050711040c03 78
    0x1010b040050b5640e1100450080104440000c4011503081c0f45120b400e00500d000b040e0181c00d654140400811202090b0403503035610076804850714581000c0b14460300c141d10b480e1138081e540364140f04150590341b1110300c480f82d50400e072602c0c5070003123103100c13400368559000c0102c0350043e034042c0143c2c0110071b516001481a900c0c0340c0341450414940d501b09904112030858068666901c42412008092030600255500e8414420000140c01049000c503001103880040c03004140e88a83c091000403080c0000b0050601e580030b0483e1240652218240000f03440741d1901c140780b03080d8004006841c818480c583c100d5a580d4042035094000d00300c1c150205200104220b801070800503000f40310084a405035107946441e40e0f5408070040d040c01210741d410b5446002500c15200d4244144010702c0000c5449401a40030000410380e500200811303000034140004a94203080039500d08100000c01030019082500b103035021109600188016555200c068241c1101900c13a84240d1000303004541e804 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 20062785 1250 20061535 20061539
    0x8030403140309030c0112021e210c0d0b01020102040306051005120303090d0f0c0b010906090c030203010503030702040b0a120b010302040c080906070305070e03060a0c2006040f060e0f07 82
    0x700080d4241c01c0301802503400401c201c190550380400e119400030307001d0030300d00c411030710550301900240202c0d50300c03014495403000000c01703402003039001d40407001ca0912180c0224210007a6401e030300d203050301ca0003640c040501c4100051101904410130350700c0c0c18800103040907902e07182c48060b05c01c00d50340c026024400480c240468184082c0740201450a00300540c607509100c0c02c016a2544103100d5501000485071100220510404100c2052501b11691840307550716200060010b190a11a05003100d20701400d1500d501e00078001d90f8101c80c1d0003000b86040c0261a003d2102424454841d9a80280300b14400b04003454081b9113014450700441c0e17014070640c10340c4144011a040900c500c13040c0030f08801041a0607000040c919405609442d0100d415200d00005507208010b4040c01b540c180600c0b401c1002000841c0e0010140745900d50740e481e00000401c80380d01060124034101071060f000100014085008003050012051041600180e0300320b04001460512040085528140d0025641 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 20064035 1250 20062785 20062793
    0x1e02040c080103031202070c052d03120405040e010204081905060a05010b1b030d020c0a0209100f0b090a050402071104050705040506181504080607090b030c160609020a08030403 78
    0x40886510490074031009075415070301c0180190340355009410301d5580000d48402003042e9000c03d60300a040180c080d040c07000203400030007c8002e41c4d2000c1c854220310303800382c011180380001d4108050180c50412529080c10101440007401c4003005040c1d4940d003c1100003480d071802c00400403920729400c601030035140c2c10300c3d146041100c0079010390542c0d8103084c010b00c40aa06502200d41045110040005400b00700000c60b085008028850540d00d01c0441c0892207000c0104070448000c0c402c4404a00e00d030748070386180502112900641001514094040c00307141d00c690000e2503891801000100150380c0c3d200003a0599015100485032605900380076003036030409020340c60304100c1e40c1c00d00c981410b0130000821301c0c50140c00d203080c0c1900c920900440041c1c80e01d150141401141c070b010255125200d10701140e490805803a10360000741041c0c00001c1000e403400a4a0281400c40c1080f840c0109800240e1025076130180180c80c503a50340d1014078016a5201c000c0c800400121000c0d503121450360078 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 20065285 1250 20064035 20064041
    0x30303110405010503010b0903010912090f0504050405120a0c0c0303050d0f09050d0c020a0506030a020a090b0313030c1401060602060105040609090b01030201031e0f020d050606070c03020f0105071e0204 89
    0x34984011800500050245a80050a4905582d0030030307a502c1d1a40e001d00000303800b41c20441b001903e0130350b11802c0400815030001c003800985550301046144544d07600c0c180405c03200f08403400342094120700f4a5003002000400100303a584141d250500f500101c41d183d02c540c40250398400c40103e580000c4129401c1058011501004000c02c0100102c0c0000d40f0b8194031000030000000410880c40803103c00c654820403100b0140001810f016124030b06585444002d500011450010801c9444002001c00c800b034101d80c428501d203081c07a10369100079507003a110710301840d208035101344800f16007540c820000d1148400400c026802442c0651400b003e00080720820b03045060300c039082c20980c0000c5103100d2000ca0440f50b081c070340010024403040016102c01d9404290404282c180200c42d2010002d940142c202c514900030100720b10b03190441000010310400314001c280340040a401c0001d85040011480140b8047c144149400d5866485451410038565641c80440884845900f5030134184 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 20066535 1250 20065285 20065301
    0x6040b030a050a0204020307090e010f090608030a090b071703040b010302040501080309010c080307020703080c010902040b1e010c05010f0216261206010516030302031504150605090315040309030303 87
    0x540074010080c03058507055155151508041c1c0201d400001150802d8819821207006055103404c519145d40c44090155a080301c40c4643c100d124201003012842d40c2c00401111251380258680c0002c1514102004100350015103003507611580d20b20010004024480055100f00d210b0f5041c01c0b0950f05601c1000216401a0890516580240641d06060741c00001c0e1428a54119040940f60780e95803030b04070310b061039540001b8445003001c56050148403054005041e601c1c400c0701c0900c4050410000c0c041c03a0600301d170000546103c0b00181d0350f0301e0350060340346226150040002050100c12050310b982070ba80b110780511300d258100700120701400540100b0000c1c1c00c80c00c5101900c003034484030002c5601d01032541814020702001004c0b3b0f8030740c6c0c0100c0c1214194108080441072103640d604000d002504202e802c0e00e41013020b0009920181303001d2141031307034003e200d85c002203e036030a1510480e902e82201c0d08841d003520520903802002031140b400c2501c924071965403440302d1421032400a041d61462 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 20067785 1250 20066535 20066539
    0x608030a09120303091e0b09070815060f030d020d02060703150306150e090d0e030318010819050103200a0e0114010302090603010e061503040b0105090903120108030a02011401030206040501180305060c0306040b 92
    0x641021b00850fa402f150001d24140020a43c50680c1c480100080104240341c4081d40d043c4943d4000030840707a00815080c009a209030291001d0f0b907510309054054501c00d5061f504400c40740030090000401c5580131240d220849070164494580b10f039500415018255007101490384421044c0072400c0c3d10400109a40d5000d5001d1802c12142409850ba04850a10402d050110060000303072140c0c0540c00650303400b0700d0080144400d59482c10000d1009694510468203110b040001e00c0640c20800001d204507040002c01e40026840c042022124080b040304040c10141c0030480c3c0c44096030aca8010350702800c1c045401d581a030030050300304443c1245181c103075401039900740200700104005e015203d04503903003a07904030040c6e90703100f104508500c40c01c20b090211071300d000000b003400e031000030140141580f1500200103182d01085801000c4a003440000d40c080c0080006000a522034855150b0101e00850711902141d103980d1440d040c25000c03220400f40c0e81012042020518003402000c05034201 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 20069035 1250 20067785 20067793
    0x20c0a080c1b0609040209030f0d030f0b190b030601030b0a090605210307111201140103030216180b060c0708010209010e120a0b0c0c0a050703060608030a09120303091e0b09 76
    0x42e400410141e00900800c00d200c0c56002c90080c0e0586c0303040c02411115041c41050351845d400c080006001000101c0c040030080b4640b855909560606803540c200740000281c8858420b4030784140402180c0c00203114904050b15480500d00546400e841900a40560f44000c1386290500c024040414044100c6c0f8055460000c559110b502010041f10302c281d0300486848001003140b070202d001c402448001e0701d510341c40e00c445c07506000d15003054141030300c0c071990030b881c46074141351242007140c0c006001d030110800c443d520160034180c0740c0e03021954064000e030640b4200076103590103a00b401c000354800da8071079400041020056a01410710300084030200c4001c1e19000c0034010413580c4e102d08600003000c0b0540c00010802d6020083d003910841404c1c82c8c00c45540d02c0145c60019150200d42c40704481003810b0090204100d000030060747c030401b100c1ea9034a00307903e181c28007a020001c0314040583c24144c0d600300c020045001c2c10305d061422040c0307c2440d0341d110310b80c0c60207806004004140c0016904 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 20070285 1250 20069035 20069083
    0x40305010e12190e190909021002011a0910150801080c01050a05040909030e0909030403030e100c02010f090e0a0203040311010e030a0e030c03060901091a01030c0513020c0a080c 78
    0x1d007000003082083c183e140540c9094042c1d0045a407030085030306a2080100b00100000320041190000307030b09580700342d50350620a01c18020a034262007054a0890781e250807019049254105801d01c1c03644070b0301100c41078101542c0e5070342e40140045c020b600c000c0040d42a0005100c022010000341d0b40003602840c10307d00e0580c184800612902030b9000b1142920f0711800528241031242280f00d804075802000483c2d581010144d29550794007074030007200815015050340c0c000b03150044040d07a0360446c0e41c80b010841502e035801143e0040142130510b040c001c00c002c0100c0e00028443e0110b108400c41800140c2c0da0525050250a00303c001c21080c1c410380c101248441000004025502c1c92502c03420710182d4071400f000005c2c105441d0172007e6805104440401c180120150052182d041c016040c200781d85040070301c80c0000780350034003026108400c80d035000c01181c14281400105503910f501e0050405298035200350900b045e44074140c92800011034103100c0c03200d040c09009100c00c03d0030718048140e0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 20071535 1250 20070285 20070307
    0x903020f07030c061101200415030e030a050c031902010605010e060310061d060f03060405090a030203030106051b0a0b010303020607090e2d010b0304050c0a1202040c0212040305010e12 81
    0x410f0341c0113070f500b089951001c0e0704d1890000d403c120348822010007c0030f140105004c484070345410a02c1100700328038580d1821840a03011b4410707414010800300145140030100e9400350f81960060b20040707542c0c07204200942c80c40d003511151568500507030780081034140c640400107001d400020100c5105903001c009100300902c1e2000d01c0c0c0c01300d0300c0038148001500d04888901d0200046c80c1e5429421000c0025103001b01c20741d90740110700c44c0318110f85c20411a103c012405580e1600c040004015a000700018001140070310060301404d4900b9607c0740b600d20600c880a0700f0151002d000302e601c44e9840d4014010942c060083d00d90140306440d00105031841d01c4c8480c22111000341010f078400c441c8082649641c41400315140340c01d41c5050494a013540e44694040240c2c2c01120156013601806103a8610341c50701b00d042900f280c1c961507020394200019000c0000a0461400200661240f000180824107842010740011409400000786600d20a103416040c01c140488103202030004000107041c0c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 20072785 1250 20071535 20071553
    0x302090d0303050402010909020d0f0c03021c090c0302060403080a200712080f0a1d010206040201080a0506180109020901120e1507030e16050102010e070302010e040b030102120403030903020f0703 86
    0x180e601407401048940315800143c520000a81115100500020701e020303807a410364001011003519400c0400c00c400808004400300e00804a948d1010141c04001410244864010f17100d40d0340140306190741d41d66250b0016105900503441192000c0011440f2400d207034110207a81a90440b01c03000110403581d41c20041d860311600c1c003e96483c41c00c08406442800344017400d80d03040300340c4ca4000b03698500504401415010454100342003580e10491183c3c81548041400d41c001c99041e1242103c4c0d0b116104403501400005142d00d07000740074000e110b42d00800c00641c06009013610000142e6920040000401b43c8801c0c403010920142803003124111414002005020680585000101030315115011000f4103503494603c1918481c1188065200350201280c0003180c009070020810b50340ca44035001d0300c8150300e100290106e42400c00719501414070340c2118a00c0310006000515040c1c510811800c001c2c0d041e602503001131f85d00d00d0795100f019010040c0c83c0b04441da4500500d900391960740c8801034 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 20074035 1250 20072785 20072809
    0x501290409020a050c030307080612030a020312150a03060c0e0303030c07020405040206070b04080417060601090b0c0a02031603020306010b1206060702040908030f07030f09020607021005040308190e01030209 91
    0x1c195000646018080c030036025108650762030400daa40e6400c0c450341c0280000700035604144076094440c071300f80100300000308440300090950059820110150b040d000307101c1d0000c1080300300289554000c00305640c1e0181c428061881498009208a182e5030000c05504248071584d0080e4001c20500030407400d40c1040e50380e0703154111800b145c0d954542c4040380080c016600004c1c05000c442c000e21080000310303c064415200c40e110102281e00c40110015503c130425600346011402440c0c060140361101c0c001499412084412100b82400c036a001c02d107081c0020900002c10003e400c0d0900840c6001d10850740144004045c0504240c2c404002d000585009050305114003400a0500c0464480360094580660045052074803403409c0d8841200344801200d080340002d2030a4401400240c045c030507441140c2d0041c140d6401c040d990b5003844004902d4030881d40c03d0100521001000590b00070090101001ca6130301840054040d100c003800d600d080c0c40240d07060500601c05604252030741006450 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 20075285 1250 20074035 20074049
    0xa0303020703151107030c11041a010807031d03072120150403020606100305150105070c0f0b040303030c0201110306060a1e020102040e01080a0302070317090301060905012904 77
    0xc80c460fa0500050040c408807040c03c0c0112008503698060541141903070130068000c00c07140d02d003856900d0400044525044505034055640d10000805505c21020194801d00c0c0d03080002d403108088034010189c04504c24020120b0f40b0002e500c034200310302e16812070115180604400b4031011114800741c07070442400c0002e001d41103200c2003140c8030502003000c2c2010180b44003442c9102c4c1494207009449050407aa6507000b600c4111081544030710034850180b14a030000030a484c40c600c0316004545c954040d80007650b810000302e40c045002c0302e1409406008021200801380ea80d4035520f030240540d060b0f90320840c25649051400e00418108400300e039444102245c0c0c80395500c040c84000d6070b260908002c403007a40c0c03412201c0c00c1010342c0c055004000b9605008070000081c1c7e82c40c0001c0b80e817030b44201401030040e004000b080002403034030751403040c1010b00c5410b00b40c1040036008c0464215039440d80208002c2b030f110070040029095024080b000c0d9048032124141e180c05403c103680c0346104a21501d4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 20076535 1250 20075285 20075303
    0x280c050406110709060f0e090d0503011a0409050702030702030601080622020d060606030e07090506030a06050601140d05070f050918070203091305040203010c02030304030905040c0e03010c021b0a0303020703 91
    0x1030b8001c4024410000608515041006001c2d12100c010880c214a4050480407010300c0010410200c00001c00d20121901665164616802c0103945140030303402d0400c035034605105101c0480c0004c0c8030301480e40700c2c0e03055600079a104d03002401054544813043c1d000d250a0b810a000340b000d02100040e403c1105602d10054180c818001d20200c0c01d08070084001400081c0740c10008034109070b040e000708080c0c400e030b68100e851280d202c41c013201c2242d000399035043d45580142d52070400188036410807075107d00c0506008168614401654400713511078030074442d00303581c0d41d0100302c2c0803030b0048007104100c0d00c00e14000703080807500c07808212544021255925280140d600040940e8404c20440e098002c0c00762144100180a083c820054041078600302d01c00d50800900c1c14000d8070000c1564072407034041c0c2c0c80c0d095043c81c10b03003440010312403410308408200300c00011180b5901c0c00d0103145131101240e4002c103a50a1401c4112000031819075001c4c0c820211000e080001c40ea001a1201c1600d400c071245d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 20077785 1250 20076535 20076557
    0x5040516031205130918051b01020312040204020c03030a0b19060203030414010b030307030e040c0f170406020706090b071103090a0b0d02090a15120902090411030a0506280c050406 79
    0x507030641e141c568800c019050501c04e1b80000019401e0245070792034824803c503001019503400c4002000400041940168000c0c0851340c0c0e04415894581c0c2c2140c00a40010300d40450f501c25070b815540203c1340038909a0301c950724010541000d80c0d14003651078503c066a000c1c01d0030040300035100d10019001400a031401c05039030407003c00a61000d40b003034000408480e030321111031401400798a0303544007203807084c1c0c9004a0700074100d001d4903074034001800a544059401340074140d18090b031280680140c1e071850f801d01140000a0840c441c0b021b82c10300030001564280740c416402009090300300d00040e11500701f031206401e241c682005a8081d11303200080e554450000d003e0607002402401c1d210780c0e02c040300745c00000d00400c03400303003081d4040401d5a03a0701c00880b2171001001a21107040c40290000c41140010300880d03501440b121481c00010b00780c503280c1e103150b01d1b918034012040d2102d6041d800c200c041d468880003035558602d000c00c2440b030144022200020040c00902036440b9803005c0c400c40541c2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 20079035 1250 20077785 20077807
    0x20a0e0702150709050108160f0c0f0f03030b04180803060607050a05070e0906071b02040b010c0b0c0301140d0804120c030807030203030f09010b030c01030b0109030501090605040516031205 83
    0x4511201000b88501451450480001000b0015130312070079000c2a00300b40842c00e04c0c8420b440341c07080e5021980700d080101001c81412260200807910695a0042c0c030030700d82001602d03141c50300680742c0c060350300030034050070704000c000481d44182c4d040404260072003c103200050301e1a081c1d030b60141003150116200d4020382086424040015001080390050307840108505000080d45d6001d01c02d00f50459090790388070081507404452080b054820060043c98034401460f05411194030701c1030605d07120000d040d10b95078000c44803405449107034804401000511425264180100000e40b048070325282400c284d4640b070231903108a000e01c00b2001b0703d486440c400e100080d05940300441d841035002c0c0c1e4442460400a480fa0001d8681c0c1c0c0000f40110089166010b05002c2d03100f00900060141051110207001074000301404e003c41c03414412001e0001020400a114400741a0301038800441d075841c1c9840d080e03062440402d03d50108011042051000c5030250300741401c15082030421556a01c243c0c41 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 20080285 1250 20079035 20079043
    0x909110415120506040606060809030906070809130e06091501030b04030908060a02040806010605070b0a0c021905011a0402120a090303020f0c0d020f010203091b0406031e03090506030103020a0e0702 87
    0xa60b040301145042d4604000c40010594440c5004882c20032a00d138032400c0403102c11500340c1c0e81031b885500500c240011480c01800400d542ca1290300003031700c0c00d540391010503001e0f80b4144c08110f06035625821410302c2c1c0c10a01c5003607840407410000c0d0100c260814644500440180809011200110001400c1501410b0403501403c218011503915141140d6001c004c0d51189c09400b000d07008400c00041c44500440980300b56541c0240c0c00022540ea90030200010100d0074141d400318411401e10715103200741d018094401e0381c01030001080558030035411001041d0b840d024503010341d10401082d5446032030250389a4100c00b0001d4041220031190074100c0c0640501c2d0603802040400103403032118214009500010f480c000e400b540c1460b44104026800c13030004550210107a04400d104100741c06c40074010040c0350b8401040014203030b0b280c1c1c036003400c04a03503158000320703140e42d0555060a05410401400003003104641c854036560440d4003103001124188a643e00c070980382c0c00800e00301d5000348 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 20081535 1250 20080285 20080289
    0x30403080d0f0612110109050d080703020a080a02010e12030702031204170f0a02010507020a03020c0d05071d0612010e0a0b040201120507032408120304050f030c0c0a0909110415 78
    0x56802c0c0a81c0b42c5512138140c510120b284101c441a0444c4034030003595010340041011200000c20062050009031a001243d902c500411403c502403002c0b148001800742010f0940c07030110f0341c0006005a000410a442c1c440d0b4044920103480041c0104030702290b00208964034004400000c5074152618030f810005c0110040342040f41c9a800f103044060402440045c1a140a003035000780103c0e00d0300d01b0180d0710769402034409070042e001146000f100d402e00010000c0854030540442c0c40c401e80e54030451040da4254444000500300070001c0c00407601d44410550310303640104008100c01d20300604a03a50310b00e604080203000c40c2c3c0320702c002400d5a000344540c9444500c003020610141c5000304005000b0034a948818240c13000f1014070344100c1c007040068205840d4080300030300f03081420b10031210958000610480351403050f00700080f00300100f40040c18110082000078036541e00c6500c10010421070a41000a0382443e00e45503601140048072454044a001e031800504108401d0000601c22566 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 20082785 1250 20081535 20081561
    0x30611040b0a050a0e0603040c14150d0501090b1c030e01050d02120103020103060902070b0f06040e07140907050a021c090f0e01050f03070b030c09131e051503030403080d 75
    0x700340a00803d030400020700802020750340708840b0f03181d450b0800c00301e0702058402900020081d4000e021100d1150070640c0e40f860010710480b101d0240c881d14114a078815440c0b90b840540b03c2004000c0881240280281c0010072601c1c1c502c6c48107001c84260091071002c0000c4d00300400188803010740c2c1d0140c02111001c0600e6542995030f22550320940c0d103010406c2c070080b800070789400030019007522648240d94860364000b18606894480d1140344204600c00740842d42d0180d500c1546100781e14040210700002c0004200c0040d1aa80e030004025010000600300c0c82482020030103e0103807079012960040c0c03680420211800180c54030001c5a0102450300510540d1040b4040441c0760040040000d04881c4125070541c4000000024140c40b2040b80c410041c03014020700202d04024041070243c606a6000750207030b41e201014203854015102c100d072080e0281540044401080e00e06c9000b0158041c213055500301500c01d548000caa603a208520019100d640b01003120806508075403ca80310401c50 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 20084035 1250 20082785 20082787
    0x1020d03051b040605030f0a02040614180603090d080106030902060a0f02070f06031a0f0105030103031b060207060b01020c01020c0a06110a06020409020405130507020303010317070506040b19090c030611040b 91
    0x40e0480175005a1041c1da40c2c801d4649510002004600d0a0080300c00307650080d907030306801c0100c500b100002500026200100800c00c1c3c5006101a112800614420f0690b40000d001d01d510942c00900700c100103800080c02c1504100350600540c44610803200d0505580c46d01e4202c03d0403803401241403008682103001203511926001075031545c0b503000020140e0174110444142540f440820000c29214580c650110350180010004680504900340705d0100f01045000025020307901e40049900000080307030803c4c0c1d20000300e5a01c0d681000310070325580c001e0008000303802410300018004010741c03260008004000f12030806840043c03200f0f03800c0f42d90264055480b81e444401d41d0703002e5007040c060140554845d480c00640c04829018007802140d240e00030703500d180d0075516100d4840f113013260960001c0d42c08010000000740c00b0000c83d4440c5000307080b101018101611104212010440c1d0440d80da03003020240e030b000c1400400b1001c1107075408000062820011101207d650095921034401c80c98 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 20085285 1250 20084035 20084039
    0x60623070f0f02120313050a050d06020307020a08040b031005010e03060a0209010e04090b220b0c030717040c0f0906030309120c050907050306040501090c0c020f1309030c0203010e01020901020d03051b04 89
    0x20004c090003540e0f400d0100d51b052203440d0414014440243d2007200c1d80070f10600010400f050ba07650080da00601280b05880f840441c988418ad401c2d84143d100c0448050004204041b03120b520b88008082c00b07091900503072003050b08c80040d558050241c8814490350380082c0d2503203168020101624043c601500034820341d01c481c01c4c01c00070a0003c0711503070348444c8800c1306a100725049a80c0c030f01c4800c0c3c0c0503540100c0c81d02c0b41008200b040c3c000800c52011b200c500c503155060001c0300c00d0110700c1103210b11000d01c50b0600b080d400c001540416440b04040908041082c4002504081c0c0750095400114101400210302d08021545020307a80c8060b400004202c00d114515a1180085204150544062207681d0740d17109404100c2da4513421039000500440b5400005241805a112000600030412285c0c4003103d2010401c541c82140107e000ca10401f450104600b820b024103a01042640b00840c20441d4030300010792207140c107a00c0c1a08055039080003a1102c1c4420342078840c4a240d100455484039 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 20086535 1250 20085285 20085319
    0xf05150a03380f0907020d0309052a120115030201080a0b120604050111030103120e030a050304090605040e010204060504061101060305030706021b06010311060705100e01060623070f0f02 82
    0x350b9202c100c035000340701004074521a070808024045c05941d142c0e00034404051b50940031801032541180488860107203428900a143c50010f5603e04074182c620841e038801c8179841080000c2010108403400303641415007406400189510300c0c01280d80a0074502829a661a214030003081c1054109900008079218081c0400d8001038031845a48200002c000c0c10107103038090b800602003484014540102410300a038814400c0000040040c0d0250032201c841e445913a6241c02d40e001074200c0801c1c80d5486108010519203030044072001c0038408000c51810f42171000083c070602c554010314052002c010100281c0c90002d41c0305600035131300102900c0e200d1b0902d04d0810041d60103000c0d40d0010000c008111608140c01281d42c43c1282d5002c081016001c109005200c40d517000340310141c0c0c590041424014091400d4040c0280f42105400002900c40c104000038250501114840c0c040d11a03800c0b4040f08000c101017152812604a01c1803c0b07184000c2c82d085c0800d14400380000c0d001516081002001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 20087785 1250 20086535 20086631
    0xa0308030601021006030b180316050c030c010305010308090603060303040807090b01080f0609061309230105180c130f14060906030a0809090a140106090f05150a03 72
    0x5030000341c1c2601d641072104044d65040d205680000b808040e61a0046041d080c4075101018a106401c81a80d06169041c1c01c2001440d11289040c0d0b0300d500b1281011500b880d05010b0032801070002d0a00304415410340d21544002d004400081e80600d0707001002c990b0540d410400c2d1001401c2c2d0ba405c50304216100c1143c030010303140440e00c01d40840d0000000c04c14540c1004086440307444007407c604840d03540d450803c450742c1864103a90481650b5030107040c001c54034128440c2503c0b000c0e004180100030112030b409084a500820f001ca001c0b40001303140848040c081010120003408544d205016002c0d040c001004040f03030500240028900035002d286101030614040c81100200c480070710329074420f0245600e44000c0c48000742122420003031202c0e2450980040764000100f02c400045040901800f2140780c802170f00030301d01065001404000703500200403000050700e819900030b4003d0515000850640c0110100001415241c01c0200040d50803d1890002c1c82d0700c000044150000054a0f0304e86 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 20089035 1250 20087785 20087791
    0x304030b04050f010c0c11040906230108160302030d050a12060e070215060a03080313020a03030203120a0c081311030d0306170102090604180902060a030b1207061d040207020a030803 80
    0x40c0e9400e05005c118028040c202540340503400443e03130184080346608000c000d01309008100d0315503595100c140103105840f90b80440d8450103000d9105a541807555140c508204c0070895a51306055400920068402113060300011915040698658012480a64003160003e0b012181c60385400800146142040c0f03080340106041c1d0252a0b1440846d880150207440c11510b81da0003024688041000030258001503a00052600340c0b07c014400c10750000303a07640c8550703009900591020420020700004401019001402c0c00d10800c00b0118149001e81300d103000078000c40301004050015014400c0350f00035102180401003c1e03c0321805000d034050000d042c28010200030300c84007a503040d03061905100722401114001d0000c0e007040d00e001c0220100810800c644075000303840d5092900140c0303400c0c01511124a00c2c0e14049682400507046c0301c5000445890581d8543c09080100007481d0041428040c40c005500b403510078100314008a4041d10038004001d4100001c00c1e000001c0c0101040a180 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 20090285 1250 20089035 20089063
    0x4030903020f09010b04060c050f070f030b090d170601020c0910090e060903041202010512010603020d051302090c030a0e030f0d110a0509010e010e040207120801050103020705060a0e0304030b0405 86
    0x40e01c1140b003082c0101801c0c24002c00b0320703403a01048240016802010312944081c807680440c0d01c0500806009030800c2030a500200c942041070300240100140d06042d203902c105010000c0c003680841442c0148099042c2e0381a0340103604001c0419926407080c8800800380c107028203c80c81904140c410b03a0b02c0c1614500c507030040d041c0741c014100e08100300410164000d02d00107000314109410701214075608141004200d0510800f046038102e03070602001004d000f031003d5200161030b2004001d05030240c5400800e5206241400184400180d68040c09a50010800c3c640c4644a40e100e02c03d0784000d001a1044103028800400e089450260390f100400000d480444284110054600911924081d000482c40452028002c4c5181e951207040180c0302c0c000d0501d4280d09480e4040301044c00c07079000200c162120f0740258007904100b9001013010340105020300e4114034103405a118107898800c050035402c0c420b52923864541c1c1c687d104106440240d40c225000492504184c540240d988101d955001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 20091535 1250 20090285 20090299
    0x30d0e0405090c0d08030a02070b01060e011206051003091b030516080111070f170301090c090803040609030206070606080d020703060b060306060a0806130c05120a110f03040602070602030403090302 87
    0x1c200303210214400301c1c43c480c050038043e040c03502566801807603040200409100d55082c05800c02244034420568024042512900300d0481a00001041180c40038565a1a0350405008103d29100c3c1c00440040420303618000603e85c0c0c0d070b0314103482041c43c40c1494041c5c40707041140c08020300402040c911441c206130a500b400c020307a80c401c1a400d0b51000c8034440368009003440310b03034081410a0a00c6200600c500740c080304a401c0a481062282c100b03800203039000b03075258a80d100941c0c0240c411809001d00390001d504052400c08002c001c5002030000074004d520200d00102005040d070011400790640d41305641301142c081100943d1140d1ba0305c0242c451608105c504540c40c1800805c8900030000030f0000f034508483c10304152040d450252000350445001318800d4100f0310540700e80300342c820940c0e0380c00307a88909405a10b0100c0350040d1164049619250b145d010038502281140c07007404609441540703e59036824000000e01600c10040d0003513000104001c10158424440020b89100321088 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 20092785 1250 20091535 20091541
    0x902090111070e1b072003010c02060609010b0708040f060e0a0b09450702211206010504030b01090609050703050405100e0316060204050a06021203060105090f030d0e0405 75
    0x860b50302c10481c4148401c0281ca14003007151031199500c0c1c8080340c0c292506144c030340b49965a4401c5141a5044455030900c0303044003803502c3d032400b0700030181078400c684003c00301401c000c400142411018071600c85605000130b1064104409041a50001e10302420744000290f6603141c0a004808246070380c81c0302d20138400b00420340c5002036050364103241c80a401140c08410030300032200d2008000c88460f000b030505200c904151889a510304402014240000020f401c0c25480680350001325400c0c840040100141074016902c41c00039580c0034085054001201d445150041c0d07600e10031134001801c44443d80340041640d00d0035800400880d030030303a9000c03c096a6082012401c45000f074a0041c5240c001e803464030324401484e0070403107981184801b902d20b808480303982c032019803c445a04445168000c20100300d181340800b41400103116074000350100c00d002c510354200364440184078030305102e40483d4014203074455512050f2070501c0a82114800006003030050603207603019018500c924184400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 20094035 1250 20092785 20092817
    0xc01060312140a03110906030a090201260412140c010603030e0d0f06050402040b0d030306050a0608060a06050a09090c03050a060605090d020904020d0602040f030506060a0b0f0702040b0a09020901 86
    0x80c034842c240150409400c154041e08220080c080790400588910424440314140f591740000441c010700f0280ca0003d004030081c40050050740d081b000e01000c02c02413507030142e030943c5842200c90340541e10078040500103503604800e42e0003c200c1070718000c00c1000800e010420941c15403001c01924080d8030303035501d045035040410464030000a0020a1040e01e400c92000103000c1d600290b0b00140700900101d504030700e86020a80303035000c21001798000394944000300710a041218007000501030714500815149407080105540a000e072103000100480024245000e620902141000d803082140501401a600b140103000d030405542c9503044516081000038504d000301c003299882040034000c102d145c0019000c0022454008105030f80205504c2811000602c5900c0200b020308100103c403080706066080030303032400d0710081c0320b40d0180400c02810312508000c0b01c00c2e9817080560021540c0e90712210701c0850040c000040d0b400d5049111103402107403981254001d000600e200382d80f804c0d007048441034 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 20095285 1250 20094035 20094047
    0x1409030c1b0604030201050d09020913060509070501020c0904061808210403020706050c030412050a050601080102090d0605090307050f0309010f03090f0201031503080406030f0f02033105030c01060312 88
    0x21207154401c400b004104010f5000328080c000c1d000d4005000035100032150003140d10400101d48602d205552103007110304007c9503209890300402079400800015040c04000307035030744a0000c07200384106119400202000803e421500c80c00c10700f01c44400e46142c56107420070040e000300c0f00e043c2a03e032008447c010481d5450070460f2003203405070b0082030000c1c43c0401c00d460b1980310000000103800100302c00b080c140e2070380c8803044080348210b00400c42c0c1340c21070500c28242501030b0000c203400d03401000381001d140c0e90076901111498011030005401d4a031103441d507185110300f0708001c159001e80701004482da039012010302055031003a21503d6025050900031021100b803c80d008220502c2624580d015512030360004e0700070a00030004503451601e0b5107400ca40743e00140d0100c0006a100c00c032400c140d003480d00503914010062402982941413940c44222a00800c44400f03000c24800c128500c045444c2c03100c0503001c2d45e040000c3d241e41d2549070b810b0714003904481c08140c810541d40c5166506040c401c0b1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 20096535 1250 20095285 20095333
    0x50603060402130c020724080c030708010311130c030e06070c150b04061a030402041d03030402040506041512020f0a03030512040507031406040218010515030405011409030c 76
    0x1011202c2c10550070316914000d0140305004d03011403203540c00201e0a200c401074022054000d04941100c4800c1c078610003010640010034003044a03005000f4014502d070449602c4d070550b540325034451f800340f000381c001c1030f1226100c4822200550401e01309000158040e4880082c402c120801e9541c10f030b40e145401d4030004d0f0441c0380200440c840040c481003107581d640c404041013000410204040ea0344a541501552942014400710340c000000d100452405100d0100003410340d60303030307000420b0300c00f0141c94490000810290080c1e480b500003e034a540e80390701209041e100001d2a4100780c1d200c1c6801d10410002c200120700038000f0341e01c101d01d6071420140040899a241d600c0514015600b1417152040001070000c0354140300300031010001030703083c00869901701c278500010410b900c1c003801002003000c80421000342640380003005005940710004084060199040e40350381c0d035111494001c0c010716240450340348000a00b000c8c84078051f07022000f05800b00340762044500c40c005022a00b4101c510320 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 20097785 1250 20096535 20096539
    0x32707080307020108090c09040311070609050604031b050405010b0702030106050f06190207030f0b09010c030b0603070c0201140711030d05160f0203030c0f010501060201060b03130b04020d0512070303050603060402 94
    0x10b0100d107006601c41c400e40b580c0000010140c034407031307901603001c140c0060051b10300b240400d0700c5030711103001c072201049035000811003490b01c151020305d00008100349101d9800301603c2180c84140310a4030741038410040c801414060310401156950310040000740e04084c000324803a5003002c1340002c0074545950809030f488401041a481c006014148808094240c000c05055026000001001c61140c0000706180c074010061a2441e240c40d05425003140c1808106600b41442c00704030b551a03440c6c080c1981d03402030b0142865a8009220700059034040b0b0010700c2e040d0164000640e180800c10a4650168002c20540880b50541081c020507140c0b030080500001d80340020304044400301c0c518002c0990b0050020301500d1a00701a2912141040c8211350300e281680c0d11040100207965091140c0e4005101003c3d500e0301310700304142115407a00348058007504c0c18030044046425507840c0c211a2501551120854501802e038031054030321178010785400e4002c00c2c03401001642904020410607c01c80d80 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 20099035 1250 20097785 20097787
    0x1d0604060e0c06040b040909050a05030f09010801060c030f20030d020c06071b06020307050c010c09051201060b03060405040c05060403030f09050604122003011104090608010b010507030f12020327070803 89
    0x2c10300058010261048161020300c4ad01c0d0500011540134401011042540c0300c005035075224020025101da1b0060780110701300300b0360583d64000700fa0321560f01c501d40c0c0d809240510501000c01d2000d10200365601c08141c0c1800005842c6030080482d900500501403220b007918480c0e03442000a46400703013180e081c0c090a603600909440012060381c000c5a0080c8107040041c00e029140031018210b5242c0040d09000c281c00d4035042c40302d450074622041840c0c4c1048003e0040508244005500b0700019040d02c1c002c035140c0000c5010008801d81e0000130305000703809181c03640c1d40c07801d0062025040c10281c07400700301c1c8510041032506001040300d0640755a82e5080d06840079695401402d00c0280c0c2c603007030026446860603d00c5603000e001ea030f841c071964003060076100c4d82440c001e0000c68a583d031246144e03033b24084414040d660014160b886454060402d02840c8200050580b50000c1c01100312209520000800c40f6131128600c0c2c6405607150010300b041d00001400180c0e03502c1602e4003030101e140d80 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 20100285 1250 20099035 20099039
    0x30406090909030201110706050708011a07020d0f14031201121205090a091d0c0f1c05031905032202011409120607080f1501121d0604060e0c06040b04 66
    0x740368001e1441284a44000940101c00381a94016600300c00c0f400c07681075445505000c0c00035840300700c4c1d5016000302041030b401400d01c840081c0e045e10510900074000c1655410034014445c07041901c4020907041a00e0200e8070342e10031840c40d240d9011000d0f402d031a00400c3c0003c150505007200c0e0540d0a64084111044140300003019511078103e00c204a40c4001c59280c0070843e10b5080c00380204600350041d004042e84643c103905401d0201c1400c2c81401035810220a4596503181c0c4d0707045c2c5c82080505400070316901281491801c0d4403450521140f210550b55030741100f5a4080d0007140300350058051044000002da4041d4600410150041d00103003a0004403000030008000512540c0401494644141c0004030590306280e812038414000c6019502044008003100c0107507541301e86a151000e5200c0814030000e002005110304100340c4039a11001183c800c414803500f001e4036081141240c040780381514000b0050510b0800c20b11860044513000d00c0281400d4094806031440d03011002e05082c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 20101535 1250 20100285 20100299
    0x709050108010b090607051c030b06090901090b0d0b07090509010617060f01020106031e0204051803030a020702060c1501260601030212160905010f0501080105010f080403020c030708010203011703040609 89
    0x2070007400e0413076072100d000c008490014604120703000d41c00b01c1c88070700d00aa03100b100748080c00b1a52501c0c009409003108000149103a40c41c01c6040381034a2600c100000d980720600e0102e4070b40144000300030b009550007000c0c01000d9401a9030501110b5007296022103607a00c642080b5044d90088007400c502c0e00c92000480c03481c1c138085401c00141c03401840001051030356615403c8007000c0580d9680c01d00c9804103d0101982094050643d0013a00c000d2440000c04007044901e81d00c1c80010031341c20060741e003ca0f41100715a0381000701d075254520b16040700e0b00c6402203440300d24582400c1c428807404c0c0c205640c1e03010152904904c0e110b0300da2101000340c01140c0c41c1d0303002c0c00f08900e0003100449503402507844150800190a08140140078551400506507042c00c00201031741d1034540000d81440088001002140e921070200e200c45552861322a5107602d46290076031402e81134030003d541c1800f6280012444840540c0035504954142d119500e074030000c60440741e1203200d039005102c0002c4184000344181 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 20102785 1250 20101535 20101537
    0x130c080601200d030203060906061309090201140c030309060a05090c220501080a03020c030304031e0c050406061d0a030302070e090316030f0f1719061205010c080709050108010b 78
    0x90312040c50310019050710503070128103000ca00f242c4040400c5d40481407142d241440107281e036004000f55a940d1030722a810380f527140320010610a44030201e4458104404592080304080031020402045d1510f60039041c1081e40c40b070304201e0b030404003440760304001611201c003401924055544500031340703000c03103001080c41501e412068440c2414071091540304501155403040398020724006018001080031858000c2c00c0c000f40701c01481c401d920a0209201043d110f4115100380b5804181427910000c9030324003607114140303a5028580c010314000c0300180c02500504000e40c0c2c01e5030b211541c06065074032001c20480c41e4082c00041c005a005040a00a0441d010711080d0010800c9040f40d092401d8400d54042014150804600044218000ca00181d030803004440f00c61102c0c1c10092100d82d10140c20f409403800061114040622000035000300380c0e0264040710203003105400c04e0f461000a420254081d019282d560000208a400024040340c810b40c060004d540c0b050b55403a2003a46844810f00d41 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 20104035 1250 20102785 20102807
    0x6061f0c060e0d031b17061309050604050105060112020f040605090303041703070b010803160816050105010306060503060606040e1302041107030c030201050a020a20120706020702130c080601 84
    0x3a40c0c2c5100c0402c9001e010004102044100e980204420340b00c803044500d903e281d0007002041c482c400001d841a224000c07031450f800b40c4150794032607081d000e01d18004081d00100901820702c0c080d81c82448244070041d04402c0c4540b03c03c2e241c601e011041c903c0031108a01c1120340c03a28500d0001e200912825100340010048020000c003100d0503d44c50301c503a900c00d400c4044104040b581f000032039000b00850000040c1c01014010041c42c100010710047c3c100756800610020304406001031401c00b030401d86800100c0310b80d0002c0c020866903860b8500b1200410442c015a8841c0c4648000034400340707400011207041d980c0c0700c071040b0240d45525141e0300304d00302d4182c0e049030b00949401241d81401c4004000d454058040d0342e41c0c40a03810319003006070031544080d0400d000c550041211f080f40603003000a00c410410340c603581c03501548400301d003981081850107900c100d04c00002481c100380000c035006815083c3c0200c4002ca04911454110401c03110700d4110780300454889400600e541d0b008151141c5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 20105285 1250 20104035 20104043
    0x3040602070f08030c030a05160806010e0111070f080c0f030307061116060c090503010501050d0314090a0f06030605060310031e02030d0207060305090a0321060b0403030305060306061f0c 82
    0x70b00302915550044103402c1228a03035400c9001108101e409140b134000d207508200020090006c40b6090203000f004000010800c6052026000142c11143d02c1542c01441948103407042d10685912407007821580c042503c0f9504041c41942c5031a50503180140c00f000760440010001e51518401e5030f9118042c1041010800d460041440290040b1038000100041644a010005100500e10030301070080007094101c680203030b1502c00180050b80b03c48984a840c40c3d05410b081400d1300b40074480c428644510f4082541080c16050000303640c1c895a04124240d80840c1c4040c48080c4d2104188001c0c2d00045401c08070442240c00e00f00040740417074406012034507203906c14241f01101b40c0c01081c540181a842400103074001c0e20100107096051080640050143c0d020b01000d10341500c0051000309140c0601c0c4000302d940c2c070203a05281c110760048d001402204a00c9442d41e41c0c900700600280800ca540038028081d590015400c0c0c9000fa421007a02e244030b0b00040d42c5100030800450341c0c400040360440d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 20106535 1250 20105285 20105303
    0x203060105030111030622060b03040218060102030a031109040903020f0d050f07030507020105090405010e0a0e030301150509011b05011b0503060102070306050a0906020409020a0e010c0b010e070c0210020c04060602070503030304060207 103
    0x200038401c00703010700b0000e0800301c09c0742544c90406105004500702c1034022014500b48003018484180c0c1e010003110008540c510b00803513842c0e01070407504510b101d40036240b0b40c01850042d40c4420160007281803601004d0b0f110589407111070084040e80c00e44505c0710607a2522900300407001c00a401400980340007801807408a080481000c081012102d01381c010a103c030000c2d20401c040b0302c0c90783c000c403261142401c016500355403610b9014a0000c440d4104441400703004101c02c2d04a91082e05043c0d940e00c1c03c010484080c02d11410304600900341241580305400c4c0304809100000d005008881c0035080c1a40140803041c5140c079881c1c01014050020300d070030740d107800130701e0701081c0180041c0014100701080103a660029000141003495409070b005d060040d443e076042c000c0b901002100d41100d102244801103903a5204040f28818000b03180254031aa24100c180d0038580e0004600d4a070b004165803c000705600c444ac1a43e072540207104156060780200002030000c1ea0f541c0140c50070303d1181c0000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 20107785 1250 20106535 20106589
    0xa0c0305070602120a050103021201060f050909030c0a0609021c03080610020f01020406170121080c0307060914010c08010f06110c100507170313140a08031302030601050301110306 79
    0x10300281007058903030b05d0080d501e400044c010341c03038240f00160030303800002c000b000320f9842c000720040c0415191045038444c00381030340010f01d08034091040380d1100054109642008080b858804010251503509034040c180311b00d0351000c900c41a0034081002c42d01901c8260b03499885000700840c24952002e498214005c40041c2101040c003400900094829500e818080e80b04c000000100840c1c16032042015090400448900403450b06840007101c2c0c0069076640c0c1c0d00b40c00015280703503101d0404010143c9162084090900201501c0038040f400e223400207021360418000216446d900c280609140c01241c260100300d860700902d007414a034200d0030306940b5000510000195900142003d40300803520010307580c0c0c10000c0541c2040c1014134401903607425818108c540c1081c03202a40c81c020038010800c0040074442030300700005440e0a6102c500c455491030b200d070301e0b138622901d0304a04030302034071803200041180d140602411945003248043d05080d42d0b02e000c10889400d2903044c851104400e51000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 20109035 1250 20107785 20107807
    0x512010608010c0509040f05010b16030507020d0c0e07080124030e07060314070201050c04030b09030904110a030b090603031e0d0c02010204050a090e0604060b010302041d0a110a0c0305070602 84
    0x10b0180c001c3e10707580b20961502d400300d0074003040d500300b80482d09586140070018040e1060000a9425003500744080303100c088400c0c9001c0e2400d00c03803d503020758064001404001000030f03809262080e140744030020216500c1d0524141c8250b0001e009044c00c0c80300c0c0c140c00341c405403070030070300c0c83e00540c00d40c50007040c268080314002c2d041c4030302600f001c400203894000d0302102c00b200955150304592241b000300310503d0b006040c08014001ca0100030702644070080801d20702c1c1c0c1e0800030b1b0313266003c00a00810030b295054200b8407181c1d01219403c130100f42000d450b081140703442c031603040c4034803800740145261600f0550342c85a202c1040e07a410190110900c500402507900f807040c4002c141c815000145da80d4100820044401072a600404400b030600090b840304401c04641503401036400200803a20900d80e400513406400f0703d030030205420303806600304005c0c0800c402746d6900030ac00e00f1900700030020a980c5c00c07202070320420700000e020a10b030800a10019100d80000c08c5020b0080200506004007140 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 20110285 1250 20109035 20109041
    0x209130e0f0105010611070e100b161b060c15090503030406050105090c04030807110114070305040e0c0c070b070501140a091101110c0d0f0f030807030f0b0109051201060801 76
    0x80031802a0702001d04122280400d1081e14054550390800810744410700342a25550b1342640110003480082e0300109041c5803030509207401030101e203100c041d01c8416205540103142c44246042c1d903106c3e55140c9110f40c000503d10304000703407800340d42e404071000750ac3d4441c22050440310710040752070b076903c0441e200410303c180080c500072403051801091039490281046240e0740007802422012808020400c0002c0c0c20b07a0843e600b40703070b2101d0b0100c03a50f0051001610340c20300d92488001010000900001090717030080043c410340c0c850340e5060645484d0400d40c0d40041c000c40800711020b50041f030003030000d40c3d100e0006d0903402d44254004100001810045c0a00100a41e5030080301a241c00c7d048013007220440e00c6194400d028a400c180e00c0080e001c503156a441c08003c40d90160b24145480814841c004216814640d00074001541410309441c008288580c1203030b9140010b458060710322404030140c0a40551104165251a051424038081003110f25100303401000c9596503050000d02503c00780 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 20111535 1250 20110285 20110301
    0x70c05031f0501151209111507051002070f0f06020f1603020105090d020607030b01050f1809010902070206030f0a020714031c0603050601030b04030c05010e011a0906010210020913 79
    0x30340001c0780c1c41e025001c40d40a4a1042e00030031010003102c11078040156100b441c121500040e8030002c41c403c051401c207002c2500c800359400b5008500007201e21602821000108283d47c4128200c443c2c030158010988100c1c000c001d0020030810280522901040025028601c000d008003001840e00320640700046e240d82c40740d50b6203003000c41071580d044c0038550207218943d03100d80104058420311601c0701000751156801004202030541c0c822031441c4c140d1081c02640e00078107007003124598070701e5100504012181d441a503d84510710820011601400c01e0082d40c2036140e001c0c114600b91340703c08882e403e960100600c0c0c440400c2d401c5c80880c001c0381b0078414481072101b111028584c0c0c0d04092840c100d00d004114094800d0500349081000010000141e050440380c0004024215131241d150469511200c1c09010b0f000e582000002c000c04041035012070226074004500c2030100d0703c1d1109000c5c00880c1110a640960030102c06160301d0300311354004003000701000340300e136511008075029841159800 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 20112785 1250 20111535 20111563
    0x70909020d06060e06031e0a02040902031e0903070f110d020301140f0105150409090201020102090a0e09070611060f040804091103041a01050a03030e03010603240c031e02070c0503 79
    0x142d2800c00615411081312121884142ea03150300d9417410750000c008440e000244403100c000c4030000900d885520f0f6054801519406c4001e541d641456085108055000240710040011003004138460901c000102d452003940078000d142201c42584075003400081c0301150b0364114403e00f00300710040e80c0c01e02c1080c1000340c0c41a040e0302d8501b084500450498016044031b4015500008401d2451007854250344c211b55019001240c41015840100d019024218405070003204041e0003045030f54902c1c10803481080710604540f6225540d07002103e80019101140c91903800c801c020640044c03290300810b900a01802c6000d01c0c1a56801664049600c41f54458a0715103000c0240010042c1103144505040c01c1c0c1a500240f95042c0400a10814000d11004040c0324100301803074030f9501c0a401c407400940e0846103c100509600b00e00d49240800c082880319510300e04185140c126001313108411000760b420070f0320307402c00d04180001e01c0294048842a522848903100014080d94100180072500c111 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 20114035 1250 20112785 20112791
    0x30f080d0b030f070b160b01080d020d02120d180b0108031305030d050f0d0e0a060207060c0f091701090b07020c01090f06020c01050304020d060603080c070602070b04050603070909020d 81
    0x503448a090403140c00c1c1d410240310303421107041801c2d41d5030300050584c03c0d910f88182c81d954a04a01401034140200c84000074002c0e44004000940300303502081e0148001d080e50281c50800c0e94180c1c00320b8849200500c1d0340c41080b400c3c403c2c500304515962002d1044026440e0400070204e072903c680116400036840b80300582e20015810201a1030080c2840040c5416001415881050000a407480c0901c8a070380805e51008142d418201f0007642000d00f03101344540c00d8595415190901c04003035409030105852080c1800c1d15140300c40d110b51440e0303065030801e0b0780b140a16030401445c2c001ca07060b41c0310721100c6907490302000030106072243c400d540902855001440c0209070400050311301035030b07540246100d02c0c10a4023040700036004105424281c40c246071681d07517640c9610018a000105003c0034108a240007408005c10491030014140c1869113412a56280e03030b01d800807a078601150040004000c2c003480300300000d040c00800f464100d1028201b0358881a100c1026004a82220f6112068651 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 20115285 1250 20114035 20114047
    0x2070b04080a0e0303120703200706090b0609040f140f030310030c05010503090705210303070804020427080d02120907061805100e04020405061314010c0302060f040c030f08 76
    0x504045000f10075a002d8000e542021440c2401321200c050043c00c0c28103040d1202e0000080d0a00e8940d60f548420380303207030a50f4880e1442d05145c4020500700320116030018500000c0384903031502c001002c0c45254490202203040d843d96464000c1500b00903505485803042c2419080b550900380040c1d03108031801080403d180d0314506010814032103d6120f941070000030401d0141e42c1c203000c610202a80c1042e21310f030058080b00c0c0014402880b0340590007001f40400b0061000340c5511441d4075008900884003031000030030f118404046403c06a610005650926050100007844030015041071a200d00005003003172000c42140034010030850301d11009030044030303041c000c0c030350400090500358520548501448d82088081780e190304d0f10f029a5002d0007a0b00c440d9003042d43c3c454040f034014060180041d1388130134440d5207102518500d8089e10101c0030400805003099445106200256034040d4010141c83e00c40f49174002c0046000361081d0b803140b001d008080003189a4184c2c44c54001d1090440c81ea0301d078 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 20116535 1250 20115285 20115287
    0x190f0926061602030d0506061201060807021006050f1311070f03110307030e090a0603061b09080f07030206070f1703041b031110020f0d0201090506070801050d080d02070b04080a 78
    0x1c0c00500032451507030401816000103030300000352448030300c40d04400991511382e000016500e000c3e9000c200c1028988500115480358418442c500540e2a5000c0303d00381203040104105441c8640501500700c0381c42c0903414003a2400c0350940040f021414400203445207041d015921a0b40700d0785c2c041e80c1c0d500c06203045008240e0702c4180c020014030703144c0285040c041190780042c541d1804458182c0304840f0130021507100c0031190700200040d903102c1810420501c0102c0b4210300d502c5410305c64008102d9240c0001b07980200803a410201f090030300042c11040782580c0c00c204003034021001c2600d03014042581200004d415542c0603210442c00791660b0740300d141a113040b180c45803000c0b01c80d060340074160f14200005a01641c150380d035910206c4400e10444c4884004031710303048600c0e032000524802e4056040800b034066100064260141c803d0320b82c01c3d82d07044000d9030151001c0c07081c1c41e045102d4a070302c0c00200d81c6400181022000101015203000150f0321401d4103200c00f6142518041400100c6860603 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 20117785 1250 20116535 20116543
    0xf0d0b030a0b16090b03040201030203042108160203040b040b0c1002030a0515040e070302060d09061a03061b04050f120a0309090b0a03020102060a09020102010e0f01020307030501060302190f0926 86
    0x201d003c6107030000c203080c103010b55801030f030002810080c1850b8001c07011504200c0136162003c81e2540c0d844a03d90721502e841d000a262000503624160000104d03618080b01c944044200c1d400c0e030b00001005880c00d07140091071040c95001c10b5074130f251409849594a5441e04600040d03000c3d0600500116480c24542424240014812070581c459450600c91103800c98000ca05242101d80441e09a030b00c030701034402910050300b180900109400d107490f9400700c00940c4150380350303000d010503421640030f99030700c1140c011030203601010100702c08030070b00c82080030745003003551180c4e03020020345643c2d40181c90241a41c9402c07500034080f0041003552806000d41704183c85242101c05081350442103451440e00080c0d1601c00251a003505540c64200305c0d010f69000350000307080c2ca4a4001102e8041c140303281194000d400c10b98131440003a0605000180c014401d009448001500000381403502c140720b0340c2502c08400c041c042c1e40c00e02030400c4000503600d00e030300c0303402c00c500040801c1d4860300c06d040e0b004c00e414 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 20119035 1250 20117785 20117821
    0x507030210031401060c050a0210050c010f02040e0f01051804051c0804050d2105040501020403020603070f020601090605130f06170c030f072402030c01020d020408011404080f0d0b030a0b 82
    0x6c10945208072000310b030002071881d00c2035406803010b45e61941c507990700b11814172500304102995824080380282c3c2030407941c024402c803240205072038030584034850f0403216444203105107688070400c00840441a0310540790650010320900c1203691500c2c240f00c030304421940403040c8401080d800030030041403201c10b00100104003058035107501c440c0caa042c4544292420320341d903803041c00d6941c1c000034200f0400b541260080c50300105169203902e0580001401001940d803810014040c1100005181a19010382001d588000b01012413090a0747e411000600244028210721a207034480041c910030608240e0050180312006020394120301d00030701d803400701c21000c21265640401d01c20401218030500c0d00e100158404000f006039002c5903412444c41c00303808080d4806510010b03011403440c41a034000d004485e9600000c1c0151142c0c0f44170f803c81c04500b01c03005490031384100000000100004010f0038216403450740051a40000e01c040b03031034000103910031251046100c5c01d010795080c0c01005850 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 20120285 1250 20119035 20119037
    0x1415090303070c0302070e04051f05040809130209120304080d020312060d030909020f04030b0a0b01020606060a0c0507080a030e0901030314090a05040e06010e1509060d050703021003140106 83
    0x142418540081656403000501d00820811110044400c2602c2070054000501c49a120f280e00c3c1c1c2400c7c1811501e95900740c0c9990719801a85444514200090090500c1180c001d00c1085c24499580c0a00c00001d042c81c5002d403010b5400c01c00200b840c1c0c1d441e0a10801e4502c003000440c1c680c1e00b4541c07590701d441010b038110400d540c0288000140360010038035499001100b52142d40ca100c0c0c40745002e40c1d202d00b058008021140c004286807820501e20340207441107a000703c0100d540e50f100d4002c881c0484060008150041c1c00c000d0005400d801c1060007400050300e1484e01c16604c50a5803900da0030404107400600b142d801038030ba0441415400001408000d0741100c628082c0d5140d0790300034011041c3da001a80100f82c0c007081410042ea5034100100c020a40900240140580c00003010b45561003401614545c40c3ca4001103106034014140e2440301c540054446441900c6106c100801c040d00c04030115294450148040016100e0400310400303082c894802107040000000421318a49058005174 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 20121535 1250 20120285 20120323
    0x8070f150b0a032111030d051501050f0a0305270109021008070203030f09160311010906020c0612060303040909050708070501021c03050603280203010b04050c040303050f0c0a14 78
    0x3c00851604255140c0c0540b44030002e0800c00f01054050360541441d44507620503010108030500710001581001d48a0003454a82c1880f51500c6401502c0c3c9000b101040c5601d807906010b0541c1190207076000a1300420811080d00310084c00607400103081441942c0650180d464444080842c01d000240f000205800d080c4500b00b464000c0740251b032404010310555900c240030000c915101014880c4641440004040c40c010304d40f0303414540305020700141440d0008000802c0020f140740b0101e00981d10741c0c40200620701e8510044e500600c100c801900c420781c140410400021400500c3c440e0f10060351040000d00241c0c1c0c0b410b00c0d910300701003023a40083e042d0340090500702c15400070038080c1401a02e40d41400181c5465580c0401d1030005c0c80c070746180d6940400d404101104007801419030f4228402c90090003515145e50600c0265442a0303048900e524040c041031000a00810151102d6032000c0c02603824a058041d18614105902905035107041d0303400766801c0580f0007407000d601d02030800d6882c5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 20122785 1250 20121535 20121539
    0x70b0105060a0c030c030c02030a0b0106080a05010f090b04060b0414100e0d330e0717030714030d0501091508030a0c0209100e01080606040b010216030b0408070f150b0a 74
    0x1800034000f15600070200100340c0007000c00c0601540c407860031681c0241c21121244041d1800082c065000c0c01854017284407180000c003541c070507008203410384041070344440c452407400b801400508803020090ba03006440310b101040c611143c201400041c006095000300b40005081409502800020030b0410440000711004c1980c50700305000c90300c00d85c00350f1088090070030761085124100780804500c0120f200824203c44101080d005080020b0407101a110001daa5550a01180940c041c070700985410600046011401e1032031468001300c0f4040580e07141158282104d012101d090700242485070380e5180d141001d84d1000700700406002d005008501d000820b01e0041e0110401c0e9000038840c5400b200080c0c4181c0618020000411028a60f0340b070301d58441045030f445030300440b4860b010714505612884258070000d11002070321080d004980303c49003191144405000028015506500304120b80e00029031001161302d5094018000800c654032035010407820b9410795010710748900920402 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 20124035 1250 20122785 20122787
    0x702040b1804081810020c04050a090f020d06060b0c030a020c0d0305030f040c050d030c0212030307080703020f04170307050c01031a01030b03010b0a1203090504020a0926010e0102070b0105060a 85
    0x15042c0c1154100001c29120080c4402994441000310351007600000103c454044075600003d5070420307a001260706102994035545020102e03440700f08050001e078580d40c401c9000d418542003040405020305400700e1a5519036400e0981a8840320304440c0a5100081a6180c20b80c188420301c4103074400c541e003101280b090b4800030042d0002509100d0403c004101140c00c2044a28100c0000c4c24040c140d01010b0400b0305015264950b00ad0007a0300a500b0000084010071020040f2803050180d42c03210403031510750103800c50007034002d01d01c91012400300b0040401c0021b030302c8640494001c4114000c41da602801d14095090092901c54981450300708182104913070300403410000303800c80c286400100001007500103809809100c0655400c15001c7c1d802255014401c408035040764000d03260324401caa40d55050000b03d1003188012400a80d1120040c00440c501820030004051401c1d0545264100d491255007141d000301e03a075900307513980052428200000c0b0540a801000101c03802401c115003410 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 20125285 1250 20124035 20124079
    0x21507090b090301200c12040302060708030702010621051009031209050a020d05030c240402010804020d0606090b0310060b0a0e01050408010501030b01031a07020a02060a0201061a0702040b 83
    0x11190700340008038201c4031a44096004842c07649926600061584001c0c040101a41c055489056280105c6095105050040c1d0031641100da028040901e48181521a012147c1001c6c0000045540380d10300010600500260f02c086840454209141d0070a10315100d0f2425901c5040f081d592400d0120f401c020a80211a4100d40b07103054001194098113841c0c01e40c144503c4000003580664000c9000007031000020140074403400401c2200d40c69050840b080b00500741003030b1000c0c64000c00c0000207005500c01c0030020b40092001d03141210000303d40d079422007540c039150041d84600303568050380c0e4400c3c90100f00202038460390750410040c140c10700601020340d02c141d40e002410f100c100b1019801303d0344240c04507401418501c008000558591a01c105642003c1c4000d81d000c5104a00c1c0107030406e410036025000340084c1c0c00420703601d00301c0d900380001038000060113015950313203100014140e07400c840b40c011070f4110300c400303540e40d41020305c100300850b05880d080902503c152540d44030b203041100 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 20126535 1250 20125285 20125289
    0x9090a0b04210e03120a0203040506040b0a0207051c02040c03021207030506010306050109030803010e0c04080a080403050106240e04020c070f18020c0d180902070303091403090102150901060e0705030702150709 92
    0x2040746640e03400c0a50168618816a441150484c0e800140000d0540c0c4dd5009014051010703401c1d912455926010040140703a085588414129040c0b44c2c0c1c40180b038258040050756109007000742c00d05014030140c0c01c0031841200d22901094803201001019a450b100c2c000281509007020186203003103848030301e0344e804140030742182c0c08140c00c04120008002c00c2602e0051400004644a04159180080458016203c102c50545c280b200c082405020a0b005404a182180d44007500040c945002c540c1a0800c004a03900035508100c10230f02002d00740001e1001d84541000400320038904101080d506003030707500244150f0700c1030000340d000310000b080c4401604641e14007501c804c500004507030320034500c44d484694102d100141040406030950031a0141c80e0203031104044a06451034800c1d03e0344150241540182c10050500204840048100750800c514900015110340c594282c100035450035544140411400700c00c00004035410084c0b11201e2044203007901d001e007080340340601404918 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 20127785 1250 20126535 20126563
    0x801060803070803150303070f0b07030209060d0513060501080d080a020a1704050f06070e010219030206060d0c0302210d0e031905100615030b04140609090a0b04210e03 74
    0x8120707051201d00300d0051042001b0300340d0303544018034501000402d5825104403600c80c400d50005a00d2402442a5038a50001412280ca401d594590301c07001040000c14101c0e00c1001c600110020444611805000e0002800201004108528040c0c0352540041200c81000e00400449000a1340040d0f10300c641c0d080107040c82d4481d1210320b400f03410800e00380c8070714842d485480104581e140d80700c3e1401055900c01c2c0c0903a01c042c40c3c001c80030055800300ca02c025001da800b4001284140c00c18506041010f03004025903039505443c4d600054540d0b1500e818180a00c2e8200c49035011040180030359240c102c480d040204040e0200300100391540403403c14100d07072400840602c81804020301c011840240070240800010740c8500b800080700c014400900d0010389000151881800d0900c1060700c507020054400d16155140800c205030f042e4001d2112025008429042d000a16601c5d46680680d0fc50588000c0034040440300ba210031544002003400c20502410000840e02e000c91107104075200 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 20129035 1250 20127785 20127787
    0x106091a060c07120305070311030702090c1602030109060203010f050901180c0c050a0b01080607020304080304090506060910050d0b1c0204090c12051c02010e120a030908040603020304050708010608030708 90
    0x1040203800d05001480e484520b44070a04e1204608255204009081261003500e0325200d03101c0c0000c8480e946d01404c00001d412041c000042003401c42c0400140010900741161419010a6035021900307440080108850b19500800180038a581e03c3c525003010301021b0310f40a9480d85080c21414031090030790030003900d9694480700749100d50f00c00c0d488603001613001411103d0811440c900380f0950039007449204841d0081c0b00c04583c410f840881100e080352008001181403238245007404000f801e02400c01031f4030181c1002044241d807110400400100714a4032040c0d11001c40071006800d41f03111441c6d04d1705c41d0010501001110825011418401d50107a400082d80c000514001c0f40c9411140c012101d600b41c54208c0a0400030001744908445480d2115030201110300441a400e80d10240b00000580c2c221512a00810100002400703804a003441d0110340018580c540000a501c16040a40040c0d000001c00051133420007500d401031082200810869150000d0103860f8007560744001e0032250 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 20130285 1250 20129035 20129047
    0xa0b031902040f09050a03090501022a12070e01090c02010b0109060e040e160302030c030f0d0804050106150504170f030d150b0408010504050706080c090105032a04080106091a06 78
    0x44650011042c2190608108115009400c100f0386c0c5031403040003103000910521001c100da500c04916401d01d1850503840300101c61a20000c00c07003c00000f40440e0300410744400c21465a20104034207001031000300304060155041071910000d44002c40241c40540e81000015245a40d1041404044580e41d02c1c2020464010b000080d000d0324880081139120b03c03406440d1000001c9151420084074800c900700d66000c040b000a02d6220729010354480c48941003103882c1406a801000603e50052080d800042c480d511800808004071a0340c284500003840410b0034040140e0340c3d04c4030407241842c040145a2009201c02250ba07074802d12a00e5050b8540742c220140307060441c0201e41c8054141024408c0d19a5280c401050003800d0465041d2040c1c0700e9808005950b030301501c1860b008014000c00342d4a0f2001d101e0064500b0ba02c040c0c100074910740e04c0032514010201400f41c4603101c0c200c207a025a510346ca04400a4251540c03604481c1e0507030326080004020010303e0000c1e09030035030150f5080e51a10 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 20131535 1250 20130285 20130289
    0x506010201090507061e0e06030103110d050303070201060f0603021e0906040305010501090f06120b0609191404021003060501050702100c0f03180902040b0306010309060b06041205060a0b031902 85
    0x4102d2000040c0385100780d500226001d500310b02d40f0000d15020014424004c3c000c44d80c11100c41c00304e0507580d81c00440400040c00494170200399143e094001401900000a0a41d03e10346183c0c0122403200c0180d40da1041030001c0106540760800070a09845e0a600308581000c00d048146041d4003401022040046c0040c49516010261070040d1f4104000300074a69480e5910310142c010b003004484030601e071401c08100b140d410082da005d59500811a84c09540e280ca040c02001c0801504900c16444107247c0d540000c0000d00403d650941e40d82003400d00b90134188140280240540003030014507051140c1409966405800d4902ca59012160f1150a4000f101c0a5801c0203100c40d001c1d000c41c4400310b02405042d0001d0900b4043c80f50780340900015540c6500c3c00c0200d004a024030700508200300041141980300f5081030401034020b0340001040ba044400041140d4403640c0040440d40f503000e5401c0504c1000d00c540eaa0100340c4150900c03076415994000780e00d80c81030b1030210950030000c402030400c0d5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 20132785 1250 20131535 20131541
    0xf09060f04052d060702160b03040804051c020306061212030615030f040317040c090b030c0a06120e1501050603150406060c02041a010813020312120402011d01020d030506010201 78
    0x2c91107054100f1105882ea081c60040100070305585202d4480d038004109500d2000a88880da5417044405002007402e00420384410750000d8429103104d00244404611a41c41e04d100c0c039154410003403007501118030391041c141041c400410700e41c4602c20301104200030400202d4001410042000e00698a5a4001c0003881c0d150300803440c5404410040200950208501c01041c02540251a102105441c82a400c1c08a5800b20360091544203961341c1007101c84510f401001c0141c200a0668070320062060116010640c941d009000081d078010020210040c1c0d031103030548842c041c00160148041c50300a5545295044c803409001d090000000344140312100e1122980a400a0090185c595680d200400083d00c0d86000e0f4860b5141044140d039039440c80084117803404060f1500200c0c5e96481e1803600d51484001c0042e0303058010081c035000840e407038800a0801c0340c90320031131400d28203060000421851844202010040d440301c0c6000d51680c000440208080380e07840c006c1010b5950100403405 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 20134035 1250 20132785 20132803
    0x91603050613050a1407030b01080318040203090109050604050601050f0402070c05010e0a03051903030c050a09180906021c060e0c0d0218031606030c09060c06090c0b0301030506010305060f09060f0405 88
    0x11480001c2c5545c1c091076000310345c08044a0050003604a5a602c03581420340f02e10035a41c14507088550702c078258845061a0300503690081c07101c4000100300450f5180c89040070400c0701c3c00c40302c54100c00010700c80ca1a04100c0e07648030703c40c26a402c5041c0903035560740d60000400740c02594148015101060380300da0f503c07140e80e00a907901c00d050f03c4d091480e004ac0d410b00d1110310401103000c44d0411001c420058819401d0350400c40c45580c4074110185805951002941c4800c210034403242c80e5192036000c0341c001e000401c4004882c4009910340035080d15210704941c4075411010740002c281c400d0050048080050701d000d401041001a914000c5440d0309484101e501e0196405000e004500105848840c404400304c46283d101400b0105030240c00322015001d41c0541c20114003481803c8000c120203902010313009205200c9181d100d0b40711516107070f07a50400d0744110380039800f0f5001072003000018085550000170b00d01698545e414680e85154558100a00c4104040c0e0703000c00080500c031041207201c1c2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 20135285 1250 20134035 20134043
    0x1b0904020304061b02010209090705071211070f0b040f050103050103080406030506060714030d05010f050105070b0411030a050304080f0a0c14030a14030d06050d050a0b190f05091603050613050a 85
    0x481600804c1020f03011350442d0541703610030382064000520040c080c00031100c01c1d0f0760002460708180503150301503c0725540e06d04005542e1240d01c1c40469000700e00082c843c007400f80700d242191114a020319040700d5094070f0300100d04040c1494010000a1850300649040c0c03015030170040f5066a80001081c5c1900400102602080f4484405c1c200c3c0003000c80103101e209a030304030500c1240e807106a482d4244009105076030000300c003003003850702080321341c0c1c4159000741c40341010034003041d4000c0020740742c603103000e03825950340d00700040070401840200580e03001c03800344002401100e0000d0316200030140d603c0c458007007407542c03041c00841255030078842e9803441a8084040c540c03800e840061159290051440c4080103403401c1c0000c207280c9040c0000804031503211b0b0080c4115441d0b6510281c1d40c800290560a1001e25000380d00401e00880c090340018110241000450f4070b00040303820b04e81013a0000f030200002242c102031000c50000b14046900001055a2000009451520030316051000d103001d8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 20136535 1250 20135285 20135321
    0xc0a0e010e0414060f04020108090a02030601060c0305120f1e07050a050703180f0504060605031303030b12070803070314031003080306061b0106090506030d0518010c02041b081b090402030406 84
    0x400c80304901a617907409a4000c5c0d0710942c1d156a804840c981c1ea00390000d020758180d110b10010081c032885440c802e0300d01c502c20300e0000d042070009031000100340d4040c0e035048000c400386810000305030b00801c014500e0810070300c010721841c00c0c21580601a88100c41e8020104200062440181401004c0d40c4000c2d11192000e4040c0540c3c0d003111400d05400d6008240c0706a090510005035180f140e0150b9001d04a4651001a2800039a6080e4000c121084542d500020074007102000503900303000420040580002841d0344a0113403500420104c1010208581c2c540203100384000d41030104071500540b54011070841e900e85030400001c135079018505808651040071030765503848103010b4016104036241c0d143c0501180c0c4541040649030707500c03203014400050040c0184907401d40380c03250710541c241341814242d0301c0403025000f10b4155441c19007031284002c0100380c0781804c180c3c050791560b4024200d01a605c00c040c4c1c0c0000c8400140b040b20540361189802001240a004103503028645001c1482501 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 20137785 1250 20136535 20136541
    0x110a0312020705030c030d080a05100f15031b0203120408040503120d0b01030612060c090306020c150606030c0714010204080102071401060e0c030f040f14010b030c0a0e010e041406 79
    0x20b503580c4040c01598000d00540f00041c00900b800104111003640d562140c481c80da40c0e1058141c001c00b0010940d4450b0340d81c0e0b010000b42c00c030b00700c041d0310b01812009406000e54841c03510040e00340c9807205068441d00640d88000800325a0200c00d44204035034840b004003440e00c50b410000440c0c0140c3e005580c0c14000d20f14041a15480c800041400030700042c41400501000d10056003225420b200c6c1908021098400d0400900d407548165401c5009061400b550780d100d407210b804a80001c030900046a001d0140309842500c5440e450f03501040483d00d003495845e0200882c2c40500400701c0c014508072956000000c007807002c0d01960040e003001c2000310b440d4080303410304001d5030400c0f40c60300f00a940f900300041494010000402d229061040f50b540c91921094024207690350000e0090b83c00380c01071052000050450840d61204401d030741c00200c0c4910b03a020030107042c0080400c032a44600c41440c01003080d1203503400d0b02811542c030350328103102c1c43d42c8504240d140c00070151040c2545000da0410 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 20139035 1250 20137785 20137787
    0x3062d03010f02090109121a040804091d12130e040c1511030a1b0209090309130b09040f020d0b010b030a06230913060e0f010513030c110a0312 63
    0x4a4a10480110020301080c09002c1c50301040b407090052240c00244048414015002c4120034110000e203d5213080c2d0610310382c0c41a050802c442a45d003181c1c001c500090030000040c4a004040c1c140b042c0785c0d1000105618202c07003d41d00e030510f002804c62501c01182010042c00e0038002400100301000801c611490031307181411502078140105c1c14094585100342c04202e100d07041240c3c0400001e0002c500d826544a002e9440c04110329601808000607a070b80300042c0ca600d070f20103002d030044000660b00c82c0030500801c8007901c075a110740c6808a261803d09002270b550800e40a400c180c011001d4000800c0358004580140e03441c000180c03001440c2030001034a05501c00c015480f40f25003030010030080740c0b55500001c5825072246e0980342c80a0b0f010100100d403400c2d2180c03942195120ba08420604081d42d1040140c4800d071919030f0700d40c0c00141d4403995841080c040c1c1da5101e450030a446504c0c00190381d015084510440024100c03081844502d0000d031145c480c0d5101460700019004e010341040c0e80 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 20140285 1250 20139035 20139109
    0x306020c010b03010e0f0613061b0306050112020f030406110405030a03080106031d0a121b0506090c0a05030d0e0103020702090112111e0906060f040605040623030406020306 76
    0x480c18004d41c6000083d102c1298049498084030b801d070780140c04d103030b02c070202d902c444034059403000d851942d0b858088d6040d018903d0310400c0104013940303020403400d1a180000d001c400f44040c5120105004124022404036008200c1c0c0d4415440708000407480044d5009103070340c0c000c5410040d0148151448030040c580c00c05500fa0403245550350503c010a048001582060952b0344081d040c0e51024140800081006155840e002040d10301407903250345400016082c0c81d08130109032003e400c61011301039003050034400411408000d54901c004d591034007010907030304c41e1b00f00c40036410080d15020122290f0300c00c1d01154051500200800c0c02035844528042d869101064215603000c03441203616564104901400140c0d2407030902230b044805a801400000d080050140b9407041e41088840034046614001d040901429560b8039104e6017010740151420030741444001000000c48450341030340d03031860b048a602c207500c0480980c89840c1c042c0405d20291107a02d42d41c0d0000c08044130f400050f45142 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 20141535 1250 20140285 20140301
    0x311100c0c1101050f03060409030e03031c061403070e0702010f05041505060409080d090201180305030901110a0203060103080a0c0606240507020a030212030421021002010b030618070306020c01 85
    0x2c100406004003140041d030b418404c807124100c5148003840001d000b883c1a50200c03039450300030b0400081992907440060b065501140540030001d440c3c1046040108662007900c0252600d0010001d154140301c0c0001c2d520704192050503d20f00c003001c0002e045500c01e42010714a003610742400d0086080606d010000c4c1d9603184182c45070246820006401c51a05002d032420598100c041e452804080b0a4030802405065005038180321000c071309003908450b0440d12900550248000e1500c49180c00c00040c9030315411009440b2a9000f408020003507600030600c03a0440ba07101141c0340d51188440020b807080c2c210307c0d4010b80020b01e440e01c0001c403001000c04c088100310720310104540054441380140d0b4140103074000030b0341080c60320340d0034401030520b2050304a02107902400c40781041c0c0d031441e440c200130012011203003902403005402001c60520440f06903080b04680001c0c843e1084441c0440e980e220000d20700d0804401c0e81e45603042e00d0a052100d40080c42c2c00c000c095580c2d03046080164040e010304 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 20142785 1250 20141535 20141543
    0x705010902010e040203070801090e1e0604050f030f03010e1b0d06060905010c050303060f0102010213060e031014060d02010e0303220506090307060806040b0a24020102160311100c0c 80
    0x1c0c2e0f500703054624042c42181d104200d65294407807140d003010000002054819504402031284035441c1c0d00006840002072849442140200700501c1d062501e40d051121036060740360141d106100d600c040482030015241992090b1414000d80d503504590062011413442d52003021400001c2e0003804100c1540000040c0d80c140c1c0c844940242d40c0b1001181d06100102e03000d40705820600c007085692808130305001e20341205200150078240f003d06800401071482d8061000b00d594200c000405081c203028400c4072400c001c900f00a4019800096800ca0300000c0110b07100305407030000c450440e805601803819500c00901100e440700000d003640110885840f0b842319a0003020711000a4618045089803054403019000d0400c0b80d142c00d006560316400030300060b61098850a41500702d440309000d070740c001c180e40e9144c4070740c8000d543d08a21800070540b0303a03e0b00316401080b110300541d0170307900c3c0c42001940c1890241d006580c2d41d05618108101c5401d1101c2e803e00b0251815042a8010343c1492513a0103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 20143891 1106 20142785 20142797
    0x603090f060203010b0408070603020306011b0201090f080705030105011a040e04030e13050703050a050115050d020d0e010504021807020c0f1309030201020a180f05101202070501090201 81
    0xf00b41c0000c140004045002c01c442c1800304403010080c00c083c1421813850030000002032001c115491421508015081c2c19011079205007507aa00070626800c400a503941c8131264033b40c8402043c89a58801c1d82400f00200d14030700503045040b80006154030f460b20341854001c0070441c480000f001034040c05064a4500c982d5110700041c1c602d03500007403800080714902200090704440015040945079440d090040c03140220002034408440c0041c06e00548030301d200402400a4800d500c40800c4207420100d000240807815000320b801380e4801c48030201d510800305c4507d1411a4110382103001648600001070203420030080e51080220043c2c0080f4401c1c0c04401070a040c0c40c4000000c1300140e50004d0302c0c25001c0d61002ca031410b081c80207648001c186180110000400c1c0c0702c2c0c0a207600c039142c51200315585038000c9640c3c600422406e0f038190f40b580c0041c00c05a0082c084024181e010402c = true := by decide +kernel

theorem cover : BRFrame.Cov 19964035 20143891 := by
  have h0 := BRFrame.cov_init 19964035
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19964035 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 19964035 ≤ n) (h2 : n < 20143891) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
