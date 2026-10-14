-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3803
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:43:15.987474+00:00
-- url     : https://prove2.me/submissions/6d4f431f-87c0-4fe0-8f37-57b3657a80e2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 683812949 ≤ n < 683992805 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 683814199 1250 683812949 683812957
    0x8104b0b1203070b01050307030b070503040510020a030f060b0306011209050c031905011802130b0a1a070c2c1f09060e0f010e01050f060903121e040e16050c01060b 72
    0x4e1305000c0c8400040b84038100003400c507040b2a041000c140075529400004d6034240c0c0701501c1038815004d02e02e14201001c85500040c024400c56942c0002d05140d00c81804007180c032940c22210003100200203101a680e805010340d003030701c40c1103000065260302e02e14010341f406800040a54060140b0106002d081c5204000c00030030500580003407001888003a4255401f4007000c0c4000e502c9403110300c4050701154079502c80e441c4d450028121003405a11010601c110380b2110a108480c02c000203401c0041000500b08040205412040400324060802c503503000003503002d240407403250740c1800080c82d035003624a0440240080f0075080640580b1035480310040d00701401103008035003808005c5111001c40e100345604a81540340e984180d42d00f00340801071403102540c0501d900c03074014081806180c0d420300032224415551182150788414030300202001c4801b45000520711802813100b0040e07484072420003548032151030340f03149218500b14003d45e9540a00311010116629002000c2a0310b81100010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 683815449 1250 683814199 683814203
    0x1802031506090703090f080318060115120e0c0405190f050601030c020d020c3f06090a050c0910171b0a1a0f0408104b0b120307 56
    0xd0b0440340d40b49401a4150341c00034000814044031040e008003c075418102650308401c9003500c2000280184042c07a281860a800c0443d10303100500c11030305a40d40013284103091a104050034000769045901041c0c0fa2448011458003440c2c44400207100a104103d925400041000c000c02824080011060003400111105801b080c508108014820f000007040c0b03001290540c001c040d071010500600c206820041001c0d00780c020030703c84500c00b08444110801d01d007010300341030384085010341907151310780f03140501803000321340000d000803000c500041401d211509003660740b0f40d181c1d100d5a8040c11940c085520a12905101c014079900884020801c0c00d400c0100c10714041501d40d0040800810340014810800100380d414514240c100c030312405400c1030460886800c0c1003640c3c4000e01800e042d1182c03c68543c4079641c00c0c1c941031070306076480800087e1500f0440800c070101c039032100d00840400d40f028220a19020009600000c6980d0041d24400758090501170245a92500c0035640b60810001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 683816699 1250 683815449 683815459
    0x7050c0901050d0f110616060b1807020a03140403140607020c0105090f1c061d2e18080c0a030806030a0308071805150c060a0c0509041802031506 64
    0x10546008016050310304e42010940c01d01550595a180c01100058001900040e05006e0242c80428020610b021940102e0001c5000a0010200007620a0415007245c07018039110074030541c11703070001e1030220b07803503060a041c66540c4d20b0940308400c0b80110391000b08846402c08103560b1040021400c54000c00050b000c454000c458580151030a00030703000b0180d0000a40e20b5a5034039490403141c0c0201d0040340600311441c0d01e016445150540e044140c0c0144241d10344410640074110401c00040c80c02d4601803035011030000708480c0d9084a4422003c0d035030264840480d070940d100c2c01c13206820682d5220546541d1b4130205c441c2c058540c441d0040c16030100e80c1400000d40681000329601291582c15640c44c0300c2a42c07045010b9070340c450b1001300928038150b8043d002c1090b80301c2080c1180122406045152145850001c2e240342030b0700280000881c41c1442d0400302ca0350313006805e45140303010031600801c0e050503012403c07010007014103010b94940311b2071621400e1880c03625a607900810302a24 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 683817949 1250 683816699 683816701
    0x3030a020723031903060b130f09020c0c010c021207080c0a050604121707080406021b0d03020703080a030f0f09060b010c05031204080409090302151f12060b030307050c09 75
    0x4500402d0141490380030190000c2020301540100520144010412401d00080107911151001c525400c440e2800d11140010301d4280f1807001c0040310320b0f0007840000b000f5403903d4030780c100e45a00c07030003601d440c2c0b414042c00605201c00c550702c4051100b80c4651900480d0440b070f698418207a500c0c40140c01a1b405114664008220b50030034804503800c0d921100d10014061a0551b2906000f1040c2000240424014000c2000003900b80004000500072540100f03021103020b1980700d00e440c1103023039035403180d0074801e0904002134004c140c6030304581d00320811070707143c5400c1082075000d4207100c10510007291400542c002d0a00d22540540401c0303004400401c03440e43d01d00c00564103020305800280107a4401c0c446044407007a00d032030550b40107104442c2d2074100ba664820540549891100840160300801c0c90305504c0a607102c0b42c550300004115103144a030031180c01c81c3d0100002402403449100e881840c3c5828842c0c0d60700129480c04001c4c00301d1b80e03100c070300b4103040d41c40d0030002c51001d101d4250700c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 683819199 1250 683817949 683817983
    0x9060b010c021e1909020405090a0b0f01080910090308150d08120c16050a170a090b030a0e0703030807020f0d0807030e01060b13031b1202012003030a0207 68
    0x1290711081c0c0e6a001d85418441d0000e07004048103800f80c115842c0e0311a4001000e00d122403540d1201000400030014050303112810601041720104000300440c860314503260455115586a0b0f51f64040d500080c07c0200080d140e1012150800b40c1c00390f00b408080d03040a0040c010164032402c400d00c03030124420403c000a00320800c000e0b0320498060003404095041c009440c00690078107419030002d1519048078500360000c404e004014070400401e68503a0030086850b824007582d40d961401c6130b15000800ca1a01c0c3c001c84014162505c5c078061001581408000940f05e0320311640011803003082942200e103d01c3c0d0300d24001b461002c0403540000180102c2000754081d60000a110091400f10385070080b807652440c00443c0102207540454075990b48030f55000441201e40d200038912003c101c003000c00c1e06070960070700c5114502000c2800d11000926002040455412900030812070740c24079044000001000c2c500001c021a1050110907010000c1401180f0207643d004042c4603101d040f07018400003040c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 683820449 1250 683819199 683819207
    0x1508101a030c0108090c04090602040918021315030f0f121b02150715020a02280305030402060d05092b020726010501080d23070b0c120a09060b01 64
    0xc800d1150164040b26142c9015030050044c580d10202c590300711140d0464000000c0e0907242100c01c261389281d030005081c0040041e601070350100300c080190549000e5940e07400300d40060044000030b00c80c035070ba800801864821000860000350b0f0000343c02190b120750380c02c04140c2c1c0070116004803008100c102c000c500040c014811040d40a5142c511090900c01e507400b401a8601141890000b8440811000d40054840514164018072124005885040c0510040d1400601040d125401c1850241820030500b030040c948414552624109860361103503c0820203501071681e403910300c0c2d4107042c20041c4100c000104010070006001e6201c026120810182c402540000e40603001a00030f4070003809001811414180401140d0b07070717140c15120010080b1802c441080e00000c88641062100f001407035031205402c0d41c403c880750300c8500b52a004940f80301d030703c0c882c41400800d0a480c0b140000d441c0e80484e4240e40326007040c166030546c0c6207058481c102c0180460300044900e04d141400704146135120b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 683821699 1250 683820449 683820491
    0x70c060b1c050d031d030a140706020a0906020d0921030e0d030f03050a020306091f080106120209150306010303300e060901020c0c04021308030a0c030801060c110f04150810 76
    0x1715006180740c41c0038000c0c06c64200800304c990302d00401003080f10100003009440203180c000c0041c0d40700b00d50305080442c020300f402003201585040100c04207080c00306402184811441c04504043e500d002d074624a8181c4440c40c5c2c0140c030581c0040c42c100e58000303054004003860300d200c040b80d600300b2181c5c0d2400c02c04c3c4100d00082ea40070782c00c0713540440010440100c0c00510b200255454035608800340e82c4c0d403400c030f0030f64440343c00c10980b02c5e40f8880610118181000070320b030042c0c0000000700078801490b0100342c1e40d4505101c00740030862058012800740b425040d209500080078915017101c0c248031071003500a00340542c8456054400d6000040c12400103109540042032000c01610725164140300700b2011b500100400d49009114200010b03041600f00010602c0001d29160840b90f6a0320b0708010f018038005034810382c140f10610f0204c100060f40d40d0040d26901a0858a1000c0c22043c10301190007082c04268504400e0003175000400e1503000012032200408985000348469203c1c2d0003034901c8030403 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 683822949 1250 683821699 683821751
    0x803040e1608040803070306050a0803120a02032e03062d090c0b0c010e01020406021c030608120f1b0708120906090d031205040c030c0e070c060b1c050d03 68
    0x102e8008a40001e10350710055030408030301d15020071140d40b10300000702080304a52221001e0750000440407821aa5100010343c052640c01045040d441d01c0f0b405031180882070310b41c800148100402c50700d00c204c003800c0300030061600f1840070840302c0c4400850400007615500841041003107600c41e0313003002c406401035280c410390080030210b001c2d280c02c2440e1403d800c102031210705952503140901400703900744068070080075154002e100d076504a9245500c02503040000204060800005112981001074148000000c40e003200c0e0360740d03070004001c10300341c00b58030b18108810003100a91801c0d010002100320a58000c0d80c1601c1d0700700140078020307920344240007980707030400c6091140304d5030742c90050014800310b40607081c444907a1407220507980c1211400c035006c450b03403103482c0c500384140010a0f0303046024000c20360102ca514140309002514003a440000100815216205250603440d581c0c0d07020481d44040003400b1902141c0d1031301c5500d0303082402c007140009140c8a80811600307051082c00744105 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 683824199 1250 683822949 683822957
    0x1505121b0f01032315030a0b190b0301090f0525050d0606050303040f080c060a050d09140a08070b06030a030f0302220306020d050a3b0303010803040e16 67
    0x81859050010009100c001e0605243c0c3c0c403d1200d440f1000c0740c4911500081c8081c0160f030602c1d00900303428100d074448802074069409100c1e1500062a41b0036055042003002c000107209003070107051070001d0032007440555055400c2c100b16404001d5100c0c5520781091003581034036070105183c8511034409409210151014114600c100442c0c00d04519100d50300d40180404100a51240046803941d4031507441400b4000700014100007034030081c0103000a98404070360651401d8503404c0018101c0c015007080c08801e5903a454a80e081180340d581490b51020800240c0c0d13004006820001d00c3c03504000010758079254a82c3c0081c0c010329001c250200540d030305444119104008650460082d00902840e2502ca0002c540044d2540786618000300118880e410150303860140240c40026035a025049140090070b0101031030350b00030042d006c40e9101701c0008a0684504031085d06510050301e005e844100d0b8000000046038100e004801002079070633204001c0c42c1502c0b0315001c1d50045c240c0c2d503080e200003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 683825449 1250 683824199 683824243
    0x3020a050c01020c031216060204150306090612080d0f06090e0705040c0903120203090319050c030a022101020d0509010e0f1609020a0e030d02010618050907120201050d150512 77
    0x41c4c03610040d11080c0647c3c5540305143c980e42d51401c080340c0c0503800035608603071615201c503c2c0692500501001e42042c80c01401a00d00e03040c1101c008003410307030b40100110000301e11240300000e80d03030218407011107242c403e104071030b07a810f4110020f000d6540200d1841c01650800310740d50a107801181440d40c0c15644d61140546180c0b540400c102206a185045000802c8204100e5808220b17071402c2c0841e5035a01d19008172103140c0540b0b84400030200c079010b60810004800035a507812888102506807400c14006807080c1801c2d40e00a12611001c0341c2c00768680028400200c00540c044c0f1f42003e190300450740443d080c150040c1e59a1012600a01d0780d03030407140207000c592015000741480c00300d542042929001c00d000082c0c00d00d1a59508480182e54400d010170101e051100c0b0005200c24080c070422040c14154401d9441c1c0c00c1d28012403210101040d400780031640b150080354140c0c0d80c5840b082010400d04500c2c03100840c420f10407248035040c2e900c8040600d14001c181084c214000c042c40340c0034 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 683826699 1250 683825449 683825473
    0x3082205150601020f240106020d0207060302161e02151c020714241b0f130b0f09010306060e330a120c1707140d060303020a050c01020c03 61
    0x900c2400520301c074111701420181d00f6160790100582541c01107100c06481c090341202013102c0c03055005038400000c540c403506d5402c0c80d082d00407500c0b5050390100c1c5005a41d43c0072090400da103214207004024075139040440b4040c850389002d0a0103160311f108848000e180c460445020003180580782c0e0301d00d2110b05901c80034072040150ba0042c41e4141c0305803510509049207900c0e0328181024041041d8402c40902180503100340080441940002c60300301490507a6006082c3c26024028401444208000005e00d5003110407905010030040105240007595844800c80829440c1c208101050200381051400b01e0928040d407000c24285102130260031050412a05c1768003221f80e041c00054020b00140007050040e4401001810041c02c0d83d2600105505000088011110041039030410404038035005d000c810010440e0581005662504040782c022840700120f103841071540100c1c00b145829400402c040d00032610200c5940590103440c9280c5040b801a41c40340480342b0940e6054010342c917080d503 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 683827949 1250 683826699 683826733
    0x100c0c060c29060307051c2a0b0409140103110915090c04210201080103080d1b110c01031a04020a0c060e0604021002070303120203090114010303082205 67
    0x419103008103503000b00310700590088002032450200042e0108540000c11485044c00c202601c001e11058404030044800d030a00b4803141d5008000c000c02000c41c107100750035100704182100b241202c11030040070080c2e130750f65000149580944100741007907040405820b4065192848503049075008007544080000c0320f02013007000d9030000c1c01c6210040c4140200040c81c0c03030340300500c0d00c00c51028094560751810000102101d081d060318080344030015280381c10041c0d80c40100d150449621003a000c7d101d00180c684100503100c801810f0a00700d000740c40031201d00d54841400c06600d1040800d0f0b540d56025200110180c60030008c030301081c04e0308040094030609043d0300501d549146071400617000395890f80d8950954560b2010f481c0ca40c1e03c4003007844150303e403520010b002c0c03010724002042c03c540f540e0b030054055201d1002410035a58007000098a2203002c1d0400c1d18143c40784808981745685034580a04501000d651010310380103450360b4182c814500d04210480241c001c03000344090f050800b0071407 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 683829199 1250 683827949 683827967
    0x30c04091a1503100204030f030c021203121806070e0609030102041802030403020706170417210f01060203040b03010b0306040b130c02060709051f05040f0602010b100c0c06 76
    0x1a50081c64012400325030020005603805100e00d8080d5450008008042500c0c201c405020105520710401c0200005101802c042050321b6040c01d249881c481d542c00040d4005000082074110303400f0016050f0040c0200c90b020520898900d0054031240c0a07054055507030b88800c4071600007041c0342c8200c40643c0c0c9050b00180440c0000280050320b41515040143c0814082c10502c1140395000f100b440101074041c440200500120715090700780c1110170392900d100c81005080038001030795110700c102d80030710f010f01203070048440ca129005c8094911000b000c90390400300c0e06103004440d01c0d8004101140301004643c1112244400302e811a42000c189000d07540c8044c22040e8010360380c0041da00b1948414404400c0075450000009002440c03003406802c0c045d004008908000300070409001e907507250f0300c44070181620060101c03042448511b09a8080c4070f25000015600f401880000e64075a05402540d0040001c1e80c0f4007103140340d510016141d00300509801401c0c003203068001d0000310f120b24054 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 683830449 1250 683829199 683829203
    0xf04080a12020405060d060302040f180b060d060c02150907150302030c0c0d020f0d03050f04080702030a020618130905060129031914150402070804050a060f1d030c0409 74
    0x5190940c0c44000035070550006c60b428040741c0e10f4850410540c0b07024401d0101c9051003003420300070145000c0d00602030101d1903400900220101c00800d03030304c0c2c0b2041510700010380d104c0d000f0015400d0000f4080e5031922020302c00e00c42d10182d000040c041080200d2148102c0301030b80c44070703288030b8541c10f0150007035003006000c88030640c002e02c001c088010302004840102456034014060250124804909040744400d030344060504000c14003601c151010f680340d921a40050409850b4009440083d05040f101c0c2400b035401075000c510015000c40301c201c0341001d1102114401c08803503204225a0503594905000341103a0046401004881c4900c1c84610a0100d610404400c20103501b004028503001601c481c01e1302803c110261041010034071440303d40d4270040c03501c20068074240380601c40b01c07644c080c0518043c980201c0c414081115007419100901801010b480526440c5c00380106800d80318103288000964031002040308090310b5510712603011000e80034200c200007043c20300001e0000380c1c0c81 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 683831699 1250 683830449 683830451
    0x300c0f0503030703060f15210f0f02031012150905160b27102001020408032115010c08071b05010207080f0312040218010801020c060f04080a12 63
    0x50002101880110310840264800040c180d051040006c0d800400703400c0716140d581404c688140064206084903d4001e18045e408600503a6982d651b01030804c9202c0c440802d401c1002c080c40001c01c50700954032881c1d002c8166120b05545003140c1d40c00745c0d150032004c0d08a1802c400c145440c4e208035004116054001c80072a2101d42000e525040c01031800d0703101c2c00340c691010030501e0460b9203090140c0050015680c1800040040200140d41c4148001e48402809000c1048024440245124944400d0782000031511150344d000480c0e01c0c0d50010380400c51450344500030401031140345403c5401001444981608036140400645181500220540e00304501340013840016840c0c0a02207401000380a042030442d2501001a2520000f5001003040350805102e402007984000195401502101c040010f43d45440c008070b981400440c1c4590070340b850200000c00c1c0b1340c03415002003400695074402c42d60325907143c0741e114540799403e8a004091810810421350340621800504d0410302072110 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 683832949 1250 683831699 683831723
    0x42d0302090711070509010b0d0f0b0a0e06240d1e05090a0c0906082d150411100f030e070522050108061003021912080403300c 56
    0x1910750404a600500207151004101c003499400e01400340204030a0706d0f031403181d50405044440c24080c00078803650040da030302c154140a040d10f03003100340c01e464098042e0b804141c40300700e2520148411a500e6014082150503500b00711140b00803402110340060304c2d24201060345c1000005401c2d0b0340404948194900d611507020750a9200c2e060181c64000014107082e140b920f404c0000018039881a11282e19000d010000301c0700106a18050200351060041207104102d942e000d00d01c0401c40090f079a100c2d4005d0303003039010030140039540514000c3d80b1024168484c24108400c0d1181608134000140381c040381c005840380242c00003144a1165019214035903110303070100f801c0c041d440f400c2c40c81d03e04500c2c0081940201074856180901007400c0130b4681858041e811000350303c11403100900070800600c03040f01c2d8125000b003c102030070780c0c003007440803046240c10142c243d504103010076070301e810030b0300100074403c80c910006500803c0c0141598170740d0343e04507409449189a0307410917203088010003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 683834199 1250 683832949 683832953
    0x801150b0f07052e0b090709050f0a030804140a091b030506120d031a011826060f0406060902070213020c03040f170d02160b2526042d03 60
    0x151511102c1040702c040c82810100c4da1192007a1444004240d0145206130241301c3e180e40e10032440804e0b01c40075690a84c150303940c2000308440c40002c1e4000350010b2004540450740d110800049142c150046407000181c0d43c4422240b401c654000b24680318100c2d001256003030b1a8080c0d004203074003200081c00f4480010706015803c0c104103c0c4104ea0780041e0340d40c50000c4241c0c11984400c03c10400030310b40101c1e040b04150100440a006005900000c1c82c10507481c0081c50b0044440b40100104ac00ae90380a8100a26030003400542034508450b100d04002011410329024070070b8408880e00100480c28410300c8140503002540701c040c00050f103000c1000003140302d0000b50391034801041c40c44414100c11918807502800d041101614a00319086204580103440000340200240c4103802c3c011030781c1c0d002071300c6003901a906a5039042c83c40c2d8403940c00401032000e1100ca07e12010150708820002c07000400707803030b8200d1103140600c90164502c100910911a0360000d0224404194120a80510b0710790f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 683835449 1250 683834199 683834233
    0x30b06010507060f060302040c09050312030a02070206040f1a0c0624061813060303020312091005070c1a090703080d020c011e14010b0702060a0c0c06090801150b0f0705 74
    0x300c1c400501340791164001c10840c2842d00c54902c842c400c0b0320744200405c0c10680000c0c0c50745011104d00ca40b440d0003001052000d01e0756411540440ea00800300e85da11a078904a2a90b100310500c90301a24038182100c102c400d0b61540304032030300ba452640107460a0340d100c402000d0001c03c06c40f8968003d42c1c014185606a480c0d0780001d01599443c8100112107000701c0702080418503800c01c3e94422141040010400247c0000648039001d180716019080783e642d1801d1240351040e4901401e65950921061100490300325900d103105d03501480e1240b4810002403c140f07500e880944001000d607110720420004a95030a002e000d0640c480340c805450100002c0d6214250342444030355140c88400c01441030b103135120391300c1801d1550300c640c24494607a40c5040d03d5032503203020740b0001078001d4800041c461503a521a40e000c0790b00c96401100950141d460b4180108910401c0c008e15010750b1034005c2d5624465030030b01416003211125080d491078010300b41c106058680090104403010702c65099032090080c44 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 683836699 1250 683835449 683835461
    0x8070f0908100b130903020303010b0d090203100204090c0305060307060c0c030c0807171f09150609021c0501030c05041d0706050711010305070c060e030c01021812070807030b0601050706 82
    0x40b101c00411400c0800041001940000c1c2072211024034040416000903008001d59045500501d50b55455141011044028180741c000096040c000c0500280c0e00c0d0a075540900192000780000300301b0700c48800419411a80700747da41030340c90303802080100199445090100d154601c203580c01c0e076003a43e4a81c0c0c0d0902a400711f8201140341e40016800b806084540c0752402185400b001c000d102c0b140029005800070700d03020242145440e00d45265205100f0720032100d90019035121b038100207843e0b0344d510b420001d400c899203040041c0c000340c4401074001c88500031a0f050b80d82004c400c2e49413903d030004000060120381c000c0384100b6140c40354084010400d1042c0c40040c5500c5d180c4540e14141c42c41c088a503c0212104241498034180601c4013160340001c4844040b540210b000640c10201c038202480e500a41c18044503960000a506850070040e201da928280c10903960019009518108151500040e0084c050b4a80c00030000b0000302d03081c1c0c0b15241d001101810b05504d40000c1c2d44450040d224 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 683837949 1250 683836699 683836723
    0x904060e0702120307080601030504020d0b092b120506031606050a0207150e100201020408032205040506090f0601031103070c1704060c24050405240708070f0908 71
    0x1055420010480e4041c0b04100008141c0c0c2c4810b1318600c0d12000c054495140500a1810540c2d02d200040440d107034034004004051300209441c0d242c0c5040c1d501c0c15074907039078441070b4a00808004042000d004444012120f00d0072207444d42001030100103813001c0100380080c0343c943c0c14401e800c08007400e01d21032520a4040d00c4c0c1962503540d658080f00300a440c100e141d601114001e81c1505030f00b0f01c030560000c041d03501840d04584142c2c0c0122034040403400f900a07600302c803d96000000d180216074907a00b1302d85910187c48070310f0220090340d4804000407648110303035098000060313000051559101103070194ac060b00505000408000340e0200542c9034104540c14804141c9a026140034010407030310540c10102e081c0c81c258549410080002d1007141003400003005034107426801a0340c840520041034040035224010440e900e000c2c148290b55403000e0101d0304500030802130030b2507c940e8a141c5103105001c243c03a03403103503522443e200311444600c28940d02e042209540c004580b4010500c94055030319 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 683839199 1250 683837949 683837969
    0x6111b030304050f07031110030f0c020102090f15030f100308040303170f10050120061e340e040e06010602010b01020a12030b060d0905060703230105060a05090406 72
    0x4601031400d14501001e103445940d103030384604400c01c001001450b00300841081541c2c0d0a003100032300c031000d902401044544056403410001d410456950540c00f80c20084030888280c0103024100085c411080c007180e0402001c80d07020000190300f2100081855001642040005031840c1e4a4448000e65009600118001041e0101e80d5000c00b80c02669160002c0a2400304140e03824021800b095030043e603c06c96040c000b4506041c126151100d051400c0070011078250340b5246880701e01115104c09180082c25440014070201e0004402400d0381100e40c80f40080a2400d10102d00b0400f944503a2200130f0000c001000020001644482c05114000b5006030024107855042c500c001e03003580c0107402190304550048424a0100c0c0c2c08a038000724600e01c0b070900056820390382c00422818882c3d0005044500d04008400040020000f2441e21030012a03800f00100d004860741e41402c200b0007040c6074607040f44403006000c1454164001c064042c028107240340b500f13031648041400e03030349298403034030405d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 683840449 1250 683839199 683839201
    0x30f03020102030a0608010b090402091305060f0406063f060c1d04020a0e09220506040c06081512070f1404050606030f0115200d090603020408030706111b0303 70
    0x9000725015000160106e40007d00c040c0e0070050229030703c1a4000d01c080e120f10111000303c0c4c002442c00c00c5500c5010303040030a403186446d01c081c04250191040d00c0440e1024900b441c00645100480c0b00c46080d082e40c07101e4103001d50070305044c82403401c003104030f580600c0c04500302850008035244185a111111500da945405440b800f5550300c01c202111203a024500410070024950360128420603184011503200e411354842e0790014900380c0d0a03c1c2c021b108403414850043c14003200040e0280710b1440303602c4110071191920411544034009842d907a0888010004d098043e00d04001d8030b034940d0811000b21385006941300b00c907031100d0405501c503205410f91419180040e00345030040b01d91200003501d50724a5400c0130000401000e00501c210840090303c40302006145100d800303510307070004d958451400c207581c180744210384600c090048000032407504000040d03401c0c040c1c001d40d401c4506a402071820030340140c40d480098424040c00460b011010040c6240300e140e246a0f0301c0309690790750300554503 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 683841699 1250 683840449 683840461
    0x31c0f0306140a0b0d15060c060605011704122706030b06030709170118030504051215180307060c0203043807110406031b05060c1504020604030f0302010203 69
    0x2111034942040c0780701210b904454010352a946184011901840040c1da52000903003501001410780642c074180c1d458034942c00265207944407403c0c03900180203943c204506030b5540700550b40c4d028150001c84030918002c0000c6c021524801c1060650301e85400d201d80703503a070051036122580f041082140d82030703030701c40780140315442e814030030684547d0f003d9075460301c0c5007080304001c1c100c0d0b28103114000420100911090051074207405c00c00c0d2071104024940c900d40d4880c070f0b018203c1d41250140b07074007606030314102c2d448515000070412415000400d038084151140304000b805c44a9800307003194148400c011180028140b40b20b400390190b015070181d51107505040326056041c0c0d03408003d800c110040a01400c644040c5000c0600011007113403000d40e50910f900e41000c5052000700e206510916000000042c0010b00003070b2400c0114034850100032549032000c11003507000d00d1281600c01d5010f05420750241900104072600640001d000504040d902e40d04d040d0071544030b232800c50050b5004001d01c01 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 683842949 1250 683841699 683841701
    0x20d09021f112b1b1a1e070e01020a0804030c090b090907090b0103110c06090c030316060b0f0306041a06100c06050a020c07060903110315070e031c0f03 67
    0xd40710b107644002d4030024049219280309001440740040c020611503141103002e60090404c41c0803041d9900d80d04078103c01c58208140d41e8160405060074044502c4c0003e0000304045001c0041101c2084036041540c60385501100d4884503142024190f1003400c8404012485002c090001180b00e008029000d500f804511800d9400e00134072030780140074907000d1103c40381c000703e17120b020344280e81e00008841210000480152081601c0d40c00700300d10000c1c05c407a2000011900304d10810010003183c2860580c0001e06680784280d001000c9440c08455505000506981003446000c200404a07000d50320400b00007401c10009907412100c4480c0300c0c100c402c20200a520003035101c241100c03448509049941c0c058021801e1690082850f55200001540404181d050300c20182c0c402d0101c446c015240d0310080c051160502082e10445480c000d0041c03d40f0740003c00d45056049442c1c1c07480d00791600e0000783d6032203510155407030341401054891482d40c5200861001c0490895840124281420070050 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 683844199 1250 683842949 683842967
    0x32703050109050c040c020d0c1b06121b210f05090303090d08100e19020a020102040503371a04030c020f0111030910020109080d060608090303060d0204020d09021f 72
    0x1501441c02c280506d07083c0c07500030952020050f101e00302101d0500480c81d001c200030410291004503401d00b4000818400d80c040e400801e98861003500b040b90152a00b01081810480720305030b40011203810104c101c5505002c10b50040c00754920004c03480b80d2384030b010b2038141c40d01100d9034000360348040208841041c04109010000009040203401c608103082c0c0002440d03a01c4c003603820604038207404200342254135100c2d0480362464017811900d5860081e0000d02075401842918031a12404019080744a0b410740907100409202d54120300d008082113215240c40c8440c8401c0d03d4074014176007000c2160140b51400b9104138807960f1083d001c1c458500c1003018044000c07107214100070000700c40f05409800002211004c0d041211400e20310011a0030880c0900042c000c024590f41c00420350301003800c0a07810410039100343e5115544259070b84690030340d403400100c800c0c03a40500f40c480300001506080d401002d050030400004900b128803500800c0c203c6c0c80d1008201c00d41e0200501481e020341c0d010b0002 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 683845449 1250 683844199 683844223
    0xa08030412020916020a080304020f0d03030c030b04020301050d0201080702101113080a2303040f180e030a0e0609150a0207030303230f060d120503010302030709051303270305010905 80
    0x42034413445540009503030711001c803401450b00b02d000022030b041d90b5450f06014640c41000309000c1d80300c405480d00501a00c3c2442c0100042814030240c640345103803d00075641aa00050441d01c001c04003a001110f0a0342c01801000c1075024074545811602d03460300a09560380c0100701d01c5999001c451007203045050b416440050f55030409400c40300022500a28107150044251100492040610006040d88135962018039505082a0000b80440c080050700350400c4140001b003005140c0c00c2034190712845030f00001c10000340b08442000107031522001900c20710401820b460320074403103a1358071030f529481325110710056480071b01c0410400d6070500031001461051408003000d0812044a1528074001500c501e2800c00c2010000360541c4801001d10f11442e00b11440d000804101403010301194000c0c0810f0b4041d01403803074082a500c100340611809882d2000341760304a0031064030111100150a028400c803a0109845818580c08403201c541c05180100e00000d04081c00d8a000c6240c07540c05241 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 683846699 1250 683845449 683845471
    0x90901120b01060f1d030705040e100612050706181d0f06040e0c090a02070204181101020d090618030507271a0d0515040803241e0a080304120209 64
    0xa021a819440280d81c1100c1745030001a8000440400c00030b41000420b801c5550098540b401e034424003140051a000064403490041180c01c0c3c45909122a00c156041c01815580c0170031410049240301e80d04d40e00f44100b00422000b0000e880e040c0500c0c50406140c04c0e54913090810007400301d2a40c03584080c07500030310112001c1010b1880030303d1440d2140380b20b60704140700d40040000641c0c210040e80490300c0050340244104400c1948450502141048a40686900728002c0c045140c0354000583c50b8954261901c507400d22070f1601004440301d010120130300707035556640b01001000440812028020303040d5034144840d0340d07100540d4034885055174110300e8425402d0040484d5071400403210384900920644816292040f1400c0c11403070680c090115070721500500040106100071f00000d0740c003a10b428903180700106185010348203050360000e99a07910405d00000ba5a1200e44c0d0314501d01c2410001d8060480355540d60b45240c1150025441004009134030101202145040c00b100356002c00c1043e4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 683847949 1250 683846699 683846717
    0x120a140a0c0f020d0906030c14040807030506070e1e03031c0c0f0201060b2a0f01020a0e030303060102120a03060b190201180804091802030618300708090901120b0106 73
    0x40091543d01c1a06c90a81810340c1c8408030b201d4144104859108150308078910740d40c84c0d503120019075580b6000d00c010341d0140101e8000c00c0e08035100303c0402c6600380d0002e26000701d4500c0f801c0410548030018001d075915200801c8034117200205009024401d01000b540003d00c40c4464901502e076003c04001101164501001030081c0c480384001c0ea40440e0715004210306111b210750625503185034400081204c0e204002c2c001c010240150000c00010000c0c3d52050001e41000040c580d881c0003c5c3d0303565002d83c11015548a080050304080c01c0002e4240c41c005c64195030b11645403005034014020181e61401da104480307802e47e0240203110b003890501003002c0b0200260b0300c40310a0f6000d140030340d242da5502e07000c00000500e6180800030035150010151002c9040501c02e1102130580180600300c680034818104040722600403d030220200d50b6500203070102004010040c0c40c4e440906d0403074450b038051003218015100c0414490203071200040f110200d8600c4e05001c40c0340c0905030b021004011443c6 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 683849199 1250 683847949 683847973
    0x1e01111f0509240108011104180903200c030601120c06030b03012018030d020d0804020d050d08010801110301120204021305150d05090f03120a140a0c0f02 68
    0x5040c0000316000d10390001440d8440e03001c1a42032021402d0318203041e0b4402008003198101040000d412508202c0080040c2080424840c41078001c0307120746004038801d0050310341008256000032207210301c28500204159002c0c02c1081c43c00d10300110959055022502604183c20308011103809400aa89810104202d9940d90049486640101410540c83d480c80d81d6054400350481c1d4103000d034003800c1034214080d240da002403070f801803404035140c40702000701640241004140c22990940303079070240c0300220000380c040c4ea90f000040c1080307811044903418a00824001c1c0550f03a803c01a507626a00fa03549444143c03429620845004115481c1c1000100080d0350342d084103078100e9605840150711000c07850000301648481d030380030640240000010422000880c1d00802041c1d42c5003404018a4562200030383e551901e40f0291500c507030040107090300c18080400c11941c0650070384004240c603489001e4034080203170103603080c00456465851000420341c02400081e000703a038502c0184800e4a0341 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 683850449 1250 683849199 683849233
    0x915060d121b02030a0b0f06010309020108060103020f0c031b1216020d0609060f0e0d03060e150d140a0606060f0210020f0f130e070804030c061a1e0111 67
    0x10020741002c1c03180381412010070100400b20602d285400600740c4052a80909099403900f6048520405045881e000694250f0291058416aa8069444e9011603803810b0054009503c1070103c151500e10900540281140c100024109100744114004415a558500b02d00d096403003000b218401d1010b0110000303201070415013100c8241c044442001d00d2080742040c2d4000d000c0b006000c5d003641d092030b014080362000d076001030401810803003c9660304940307000c6c114205e81084c00340400e041021008580c4441d2481d070079030b41800c40240881a40c451540d20060885c049417680282074000c04200818808548121030003001b65042c10303011343d052820000d403120b10120711000303a1035021402e40e444890040903104040101d21b16156140043d4181c080b45090510907a54601124000900164400c501890050307905450300840381100381e5803c4013809180002c8101881000c1a0039030076540c4800c042030300c010003c4401d02e840c64100c00105444804083d170b0b120782c2e1143e02c401c0403040b0300e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 683851699 1250 683850449 683850473
    0xf03020109122d06050403020703020a1e0e0604021209061e04030c121107060215070306050619030b0a0b031906050609090a2307021515190e0915060d 66
    0xb0f920045100101d40c501804650801c854024103481c0c030f4a42000209074001640704103132802111589601a0341e00c0303220f210a151001501000392065000704103013455200c0107034104000074000360518180350351030f1100701c008694044a0b9070115091082c201c40c2240310b5001e015040e80e80445c0e40c40c11340c5002d000003000e40001070001040c19001903000e445011004000340b11a002d59500c5541d4100095541c220411000c0b000d10203e4003240a040c02407250b1802c4900140c0064141800e8a0140e158200402569010b240d210340152540c0e0382c41c0c3d10300c00e000d090b4414659441e17040546426091680e89541c00c0c00d040d140090902040c0d9888080c1c5462003070445c0c0c078015560b10b445808028080754001000c02c030840206d0040345000d806241ca2081001794200c07180910990540c001c6040c043c1c84032824149030010f43c24460400034030303103401c0c0c00d0746d002050035150341c0e2581c01003c2c060440307280f02c2d00e4100c0044081c140c03000480840d0030407000c444504003c00580c80320880d25031 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 683852949 1250 683851699 683851733
    0xb121c111c0806011404090c080a05041106070c0e0117010b09040b0112060213030303090302060a09080a030c051b1b0a030c170a06052703070b0406020f07020402040f0302010912 78
    0x400d03400003d01581c801c048002c50451841d8216803101e558170380c040040d03c2c04107481004107102000080c00000c00e4494140300c0d9410460b003140f80c07120f8009014aa50003402c0c1038030703c0380e20014041144481c039104c082c02066081e001000d203100540380c9170300f10f60031a0f46491083d0021428440030403286100141560350300f00030b14100c0f50312860300500920a00341402c99602d41c81c00000705068050b803064007001d0080e02900d5a9075204a01041241c00455000788034010030312030075982c0c91190f8040d400039200340c1481460030b0001014600d4064803000c5680e001d6001c00c40782a0303603454002145040c81400d540da49801800d40d6200a55803001d4098201c845402c2c403482e12555004010810100b50441c10030080f904060510b81c00066002c0e80414110000824030855280c00004582e02c07250003400060940c1c596559920180d884000ca4629204003885404096501d6200600c01030031400c1802420520354030000d049180c6942c401c803081c0c80c1114000003c00c41000006203000c03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 683854199 1250 683852949 683852957
    0x12060c030709050a0b1b03040305060a022a0706120b0604030f2405011d0c070308040c2607121e02030a080705010f050612100b121c111c 60
    0xe5140001211540c5030b9900059001c07138220400654510828001e0401d20400c00154014030201c0420a60701d200d90300c0010030a0340058001000036520364081c0071410103609400807803801c0384c03100d80092000030784040d02c50782107031400700310381500b040c0b080ca003280c0050030500850f02070b03a00083c0103000d41d110182003130080140b500100085407211614498020042e00118400b6a00c218010700007400f5894142d02d2407580c0f124000580010140724440e501d10141ca4101150b50850f110807000e0002c0701d108180c1000410800b28201d4411032504500201a140c4035030702c01e02c245080342c180d03c10382a21704080580c1000c280b00c0242080c0690022a030040180d00c107101203850031b210100c0140c070148000c14190200305040d0000c0d0140008400240601d443d05020081040c5010b601d40c24107034000e03043d00301e40301800c1c0c001c5400da0034010240f811040b8485081400c040204842400c00d404505280c004641c2009039140c00510640c001c0411035002c2c5142d0034488075281e2420144 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 683855449 1250 683854199 683854201
    0xc1b03080c0d02190f0c0209010620060112150605180411130f1a0108150406180c02060c0a0801171c030f200405090717091b12060c03 59
    0x400101c0e0441e9140d909549086548031a4019001038040110302480c0c00075000c19880d4805910611018041720f0b002408049a81d00e404c0342a103401e40c8100b030003459000807410300402d024062046e03170b008101c17580611240c1c0d1210300d040e03507440103010115200d07540f40c544244004d440b000301a4000001c085640c1d03006854904048074005222280b2a80c4400c0803404421101115084420128260102030195080180304003246608048200340081c01280014040848c504640200440d020340002000d5803640e1040e88070f800ba41c03007542041034903408584030b1203a04212065001c14121f0100d401d1410b00308001300b14200610030000c41101f420900000942c080c40081d002c1250341e4000c01541c0c40c0d028024006d001900c00a901c541d10785004920910f0081e42040350385003801c54000d1908e0705207000c2140b4410043c0c420820000251200f02c2028144800fa070b01424524000700581c44080f0245030109180840c854010b400d207210308099040000780b099001401c20340c0340341d00c03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 683856699 1250 683855449 683855461
    0x30409020705070e090706110303161b050a08191e0806120604051b190504090503070c030f05060c09090604050c090d030e1918050c0d09030e040c1b0308 67
    0xa081c481380c00143c1c02d03621243c00d1280440000038150229243c1d9128050b20800c00c108183d12400216040d54a003444403141d408003904c240201c0c18a40c04420041c1d414280c59103540380f62102003207085484003c00034040c03a0003081d8020240c00c0100c0380c40c242290940e41c41143e03c20090312031181c8244407001c400719240fa43d17040041d00081c9544011a0301500d418104540e95855250b21181c207141a40b44041d81410202014066499240342c5500c0c0d507440c0100780030003045a503600750f48a000501102d4002285807440c01b0040d4068200d045810b410307400d1603410910050710712414588100070130b914984540061540c0050100da00281964030180c0204092088052140c0d20000e90400b460402d90040304062152800391030704089000c4448030540250410300400c101056114100d4214001035007085501442c803c560605020345200e480c010b49004400072804142000c1c80c814150901d84618010b64500f072802610040303246100309102644101e010342044400c00c00554 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 683857949 1250 683856699 683856703
    0x50409150e0403200f1e071a1e0405180402010903050f030a030b120322030204060b03150108041110020109152310091802040e0726030409020705 64
    0x2464107048208003840d20745802000060004404020250f00c044101c410010001d071204079046290002d00d8820404040c02d0250030750008809618032500070042005020079520741400100204055180c4c038941c051002d4000788035040740190700060004000e42e5441c000680c440b950404c3c3c2c0565662654001200c002c41e0030f80014060344a41c40d203070030751030a0000041890700d0301c0e03940800030281000308010150300c2a0a1004d995801400090600c406e0110f40c21078656201103c0340b46207550354081000d80d403ca5003d0001b8201c0803041210520095180513500310342440c0044840c81c06569940e4200c0c0d205aa8074001c1c0720a084c02003400e8001d62101440d181c00420120420110650807400341c00300c2c450312210a02240550401000e1102d45c66004900085801c00c0e15405c16500900400b0a600c03a52405410000080056215446040072009440014007122802c1007005030201c02000798040c01c0341c007060320407204c0a41c04400d480560b001e8000150b980c881a0500e14 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 683859199 1250 683857949 683857991
    0x603051603020f070b0c1b0303040503180a0f1211120a03140f03160e031513031e080108070f030203030708030a020c060106022104030308060d0c0803160c15050409 72
    0x3060300e01794200f40a00004800301a00c003070b9031240484411034501038001d9449000070b49005003154401d100c2e810400901c9044100e10110140140f0a00341ea10aa4414032411a0780042d074042075401121060002000703c401005034180c424008480c0c005032100c0c1d88150384400901001585c8140200c44081e6004603550345540300c020130703220f0600e03168001010070b2454032100810a101c40c40421410042400440c0742c02102540e03c880e81c03007900100414041683c00c03030800403820401c600210310030030039421a6034103507038080403907040404141c0740004c25080420881071304502040180c0c0d000040714030080e800107070145c40380c660490280c06030140140c8102e0a01034a00003003a00350340065810b10704000c0441070b460700703002080320054500c9140030150000300c2040015a0604115550b24240c0c1e1140d90080c0c450b0765184602411900003401c0151700c202e40654450074440340040c0e038000341010312801d41c000c14074070318007034003601c00c910030051180e4440f0f8a074814460310540d01 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 683860449 1250 683859199 683859203
    0x42307080c0c070906080d080126030403140f2506120207170703080f0103020f01030203092505030606060c060609180709090618030801060318140d08010603051603020f07 75
    0xc0f8202a11140341d40c01500d03203070244051078800d0108205e01c40f4840c2011360b0481d80440c01c0c0004d210481407002c2101071040d116510310307200c1084008009403034440300504205c08100a4020310b4240441281000070020380316201d2000c030360000000c400b5401c100c40480c0e00906222032000c800f5000c00019029032940a0080700c00d580c500300b030b203501d100010181117210750780d2a80c41e039540484c007961450080c0006500040f40c0c5460b002e155029600071a00030310b441048804c00c820f0410709094030140403810101d442c039003100400150608200040d0444c000301c4426080100345890b01d581c9450040c4814850740071400403c08002c040c2070418114402407050343e0303610b5220249100a08100c0740121112032400d8501d0000d50701900f60955180c0d03059031243c02e9a460240128050b01d8801c10120031414910030581c00500072040901000d9000c04c00307000700c00020388006d899001c0588c07041081c54140410011440c00d000d0010365100342c1802c00685881451455404a010700500 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 683861699 1250 683860449 683860453
    0x3050a050c03044212061a0a02060705070c05280311030c030102030f1f0b130e01150e04050703020904060f050906011e050a090305010c020105010311031207230d050306042307080c0c 80
    0x30042e160301f00d140061068240300d408a408540350503008072018410000042c205107480c0c041409140780004401060103580f406a01c142604000f4001c0120f5043d40304640c6200300f1610f024850070184911044442c00314005c50562800150207003001900800014411030040b031940505c1c401c41110101900c41b01643c952103000e17007406034004018038050030301b110388810b0000070130304c88241041c00c642d01295100079503614a181480082c15000c1e240340c0515809208980c80d40d01c45214140003400103120070003000789005c0c01e001031036401512103410490011085074000c9980c20215101c02c25510b051030b620115540211590701d887d410040165003042131501030580d054000d18140c07030040e941010302c0189a0101941c840c200c261b580181003091044002051040100319140c0c500c254903040c903da000080d0034185260486002c01081e0040240000340c2414858000694220101040034000060700e240d641400103000030300b041084400128a0f03280701c0c081e541102c1c2c003041 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 683862949 1250 683861699 683861729
    0x1407080f010203060301201209100e0604020906061e18120a020a090c0905010809010f230604050f010510020a050f070e0f070c03050a050c0304421206 66
    0x38040d000c1d500c140c072520311030b41c00c15007040080480382c0c644001d2007030103070301c0c1c9440d1141c000401c4802c0000107024440754000c2c2020f045808219000b210b8170118214050903c51400344100402483c0103070003240204010700043e8000302c1c00701c00701d04001c0e1001e00d055031a0240351701d0b02c02e4034100100d5502d801c031540f0414018204c1000800700701c100e1084410850303850322604204100ca2044034403400080040f0020040765000b101c111390000b61040c00406d140d0841c0c4000d01c1940d5441340542c82009d100804c0000d1041c0c001e4082d0f8001400710f8040c005410f08942140c102c08060040351302c10181d02c844008900d0003045603840b419480320039180d4540310101c8040e103e50562280c059640d0180d000902e800300000c2402e032040080c0d403502d0059505a0300c0495564022120714424004104404c0c0110541000030300000c01c0d00744142e04500450100061001d903103562100080580504131017100e0320030754005118001c052804000c82c20407254507a02800c255880014580714443c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 683864199 1250 683862949 683862973
    0x1112070b12070206061206060d08040305010504080a12060608011a12160224010e06120106090207110118031419110a06020a2103110a0905010801080106030f140708 72
    0xc0d50152088500f0f400740c0d0083e541e49028070180c402c4412500032140c1080b0001440ca1501d00b20440d01c19001d2201641081d8a1350b8481e0b0841c0c10640f81030b1010180810103a440c21b034851014103a00c94250b50034440b440c5412009000100103001d191441c2003200c1100404900305016144621108812401d003170170001070300c1c002500840380c0c00006001d42501c00c040ca54854640d089403245841440d4801c0e860807a00c24083c070409400d543e40146103079900c4941382024080d503406418030104c016a90700c03c92805200c6026000501418400184141d00c90410b419402804580d0448848052007131180300c00c5080c8002050354048121402c61560244254603507580e10801c410b4540c04101901c6403811b82e0b4518081c2c400030101050320f040045241381c0c1d44d0440129540034100403480030762420701c105007908041a00800039009420400c0b0765039000110500410001c3d00800c0310508640b50780e80103202411020b4021584503240904460040080d00004c0018800b5a1141e100d10 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 683865449 1250 683864199 683864227
    0x7080f0c1c0201151409131202010c1b110f0109090204180e0a0209010b070f060c050a180b091504050324070206070e011d2112071112070b 61
    0x1070200c00c40158681940c1c2045800d2001400c400e88040b030850000b10620f2100f0400c280100600036024401109424400221451034008034042d0640000c204070282941c01440710034030f00031541c11440b031004001c1c00700301c140d400b0800700442074900080442440c00181d40b00c0a10344d00400f000c0303100050006844100d5403c1600340c0c0704100c000d00803102e8403812107a4400710701c8006903020038904010009a82e180b4010000584204524412016151a03c02c00c648203804414003040c0d00185c283c0d95164462105002c500f607004201e001a420310983c243c0b44d000c2d4080b043d0142d1f602c110705401800300e6800352801440f00804840f044041880c880c104030a50112200700f9003a14400310350f107540042a407600c111855550344d007005220100444108555802c0c6002e0402c510007040800d8aa9400c03010407200005500e2080a850b0f82243e071421828046081403c1414000c40300003070101c0c5082c1c690040201c1380328081e0000b000c2c0b17031400c1503142e83c00201c0002000420310885190 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 683866699 1250 683865449 683865493
    0x10e090f04030e15040603152103030b060f0403110406060e01200105250504080a1121011a0f0f100908060103060614010e0f0405180114040203010b060f07080f0c 71
    0xb1b50b079401d1202c89020000c0026151040c000c2400c000b11007148a11103000d404009284c5038060700d0042203c6400d4004942c0c25806203010400349100003d041c014001c860074544030882d0b05680401c8541c0c601480203110b10501040203040000340800c40c0041c0242509402614100d04020070640c24007000090781c02d1020b80c00c504d598860300207410724040c00741c41990304860154014040800e120341d1400e00c103030b00e88184507038420318400130000f00c25041d01c14444a0f081748000020b003815201c8040100d0555074500301e201e103030b1440314038145844480c19201c0000094546407414100c8800a031020030041c0c03c54070386481480c00010034040c40d604030364121074245001425041d010f01c01146e9003000005116000504e0404100040c00c050344096400b981d50000403010240841055003501c4240e5415112424088180700641c6028440c039030f982d0500b21401d501c4c4c500038100c940000e0180c040301629005020a01034407000007002250455045503054130448100401d40003270b0000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 683867949 1250 683866699 683866709
    0x120f090a08060f0f0103031e050408060405010b01090801060b0d0e0102040e090c010807030605010f0e0f031b091303081915030b07030b0105091302091519030b010e090f04030e1504 79
    0x7980f44041002d0003401c00344607040e40e0309540d032056050340c403100718002180481c0c17807403003000700030440003560300d2040c0305490059100d440040b42c1c1c500310302d000510b420415084100e4a0f45060010007600c01002c08444010b849001d0200b40c00d610107111318021b001ea07a00541c0030002c0d00d0100b00078206c0115003011030100036280c1007501d4035111400c030b04840c080d00646000c9124010b8690f042c0380104c14003298603000a0440c4034501440b4046401c207042e8005003000c6445024420300285080610a0740c800941d00c8000d1000c00c1944008100000c06406c010381034480c0324090446030700f250003810008100da0300f5890381998038681130308804021a00c4400080c94512000c42175881001125400f030320062942214840c2891b150740250712a10001e603100161301200c00e811710b0010003500d00c5160302031248000b61000e01d070140590304020344c0036040000106000c456503075440805a04a010340d80c43c0b200740c2c1c1c0c80d40380945d566074510b5078071079200d0039484090851410440c0100141c807 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 683869199 1250 683867949 683867971
    0x40b03070303050d180b010b030603010e070b0a091d0106051b0a0b070e030f07090221180f0102030415091a1f0f44070f0b070203120f090a0806 63
    0x94880442800c040d00d045c3c0b002840042903900410120000c4000f175508510b00600006442d2101c0590520341b020b10340c0b0016404801044107241c2c150058080c00060000b92004c0903000706001841d030b0700301c60500694040c03000104c1d1041c8520b032070b066801110308440003101c0250401e828807204089040350f0400002e041c0050010003801e0100e0341c840305c102a0320007032100d80e0038420710102942214845000452040b2883c80308140d4203224903018541c41042d002c4022861001c1d241482c0e688010700074580c4c01003060100040f006208840c4122030040006030301d010754a8454050307070704c400341d0446c440711207030a0080391074540895050180e200790101021558443c51490040a280b00d0380d0700130700c00300d806075104640400c0d42622a00d00790290300c0c10000c102e00b040d004085200c1e410180e981c8a24000d0200c02d010300c0307030000503000c5142d1045c20b040059000a07941d101000c4210f820b8100812001d50340100c9009545102c10000e04100c5000d4450b44c51565410088802603210 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 683870449 1250 683869199 683869211
    0x90b0307020a0204051501020c040209031005180f03040b030606070309080102120901060f060507140f0d050a1716030902220902130e031b0a061109030c10021b040b03070303050d 78
    0x909450070700d12039214812380192441c405500201300080d082012090381501510415600000c00d610959200b091504c02c03508001044648583c03030020510086131040d801040184903c0c00241c0030360354000c04c116059540d8ac0b4640c40c2c1101d40c03201c45c0e400282ca03980045803040a01502d516424411713401c0100801099540b00768404980d0702510075500031407020040880842c0c8614014541c0c03c03260400c840003c1c5000c109140b80c80f45030059080028004214217400e01c0c1e12155102120007420252030b060704200728038000450700b15040c0070a155403807200c1011912602524a0600d0b850041d0243c070308038491840d40030b8001520200e1103600316120680c0e690106106400f60515003600950800800003418810400700082c480d10754407800521100282080c040c1c1d44041c1042044103887e40c5400d018940360903400000e01d80707e20707074030b074641064541c4c00034070395103c005024502d1003580e070504082002070444440958050003400c0c4044103058012008003041689202c04001c2c03 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 683871699 1250 683870449 683870461
    0x5090d120203061c020a0506030106111908040e15040e101404080403020d05030f03041109090708120d021b011b03091203020c032101150503010b0405060a090b0307020a020405 77
    0x2248812540f050340000d00125034510034480c0c01a1618040c805003190b038901d611080051140d400c04d9000900190074000030800d009802d02184030604912100b100f0402402c0d91100c40c18060383c040d02c09511142d500280701d0041500314280c40c108090810001c07003401070007031501e40b242210340b094210b0a2071560800240c2511107148500e801144141c01d0505550030081c14040b1000140d520b4841030140b03079440c0d203010004601451180210650031310881c002c1c000f04031070040c6000d102c2c0c0c00c40001040000000310b0351015a0f941c400000e0303078400008503004024050440c0800c070000f400054142c001c041540101203844802032908020031682808a0543d0391030342d0010b1a94886d400c21210f4280690007810010b100328061303a007094058031111a000d20003140c0b2070303554004880100201c841240c90090b03898a20301d8a5482c540c100311100426100e00e108041c09500c0024240201134401e400c03100c007170040127000c281c0c0d80c1080c2c0402903039007000040581c400d91130725020801d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 683872949 1250 683871699 683871701
    0x20f06090604080901090b030c03010e060f100e0102160807081207110105070201030b09131218210b0103080a02011a0919021608030f0a05070c1104060905090d12 71
    0x110a10310000101415a1150b032420b5954010610250510000c480003003041c1d14603901540c401c075603c482550f120340c5000d2005504440107843e03640500b42c0480c5840480c2c850600c00c04220865084c01e81e00180308100413481c000354142c50010184048802003034051000c28034004440f61101110341d2620550100b1002c2d10400780000c00c04101001c2d4040d155000780058003070070340141000102213540364041224600102da600300c6000e214880e00e410881c803e041401e101d88a031030180c0404070030034603c400ca07420f036014460074036052114001500041942072424a0b92100c410314942d692454591681d070002c200c0c200140d400c003500141c0200c1d026481013a0b50800610342c800c103844a2241003007500c0b54519482e04250200309800b0301a2424400c146c86d544030301a240e1340d0b0316007003141081403000603011092240c141003c0c410b0165100f090000719a0300084103081c9880c010002500518103031303011001140c144810005840340200340a00e2080300d40c3ca98901101c02d03d0035441c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 683874199 1250 683872949 683872951
    0xe0609070605041e0b1c06291e0c0a050f031c050a0e0f07050f06070b06120322181e0f0204050a030507441903090501020f06 55
    0xc001420502041280402015518802070031350070003208000d84071480141d09612030800d120034080803190843e50268540700b0303030000300f000021350141c400e145043e41420720042e01210316080c1d00030403082011405c0c2d0495020002c85401829501c8600c019a9511040c402a042d40c4030700808410052010000c821503201c995000e0035a070f00b0000304100303040103210145c00c14200c0c590703513140007405200803c14030780c08116585c000d000c1d661405c820424620015685640900010301c50b000015000c280c505402410407603006118421003460756140d07004142820854000d030303101d00034504500103010029a02c145030000720340e09a441001c0143d800b02d04c400b0701c944c90041380400115807203034007420300a0b00000015282c070b40e0f12000603106000c1a001510f452b0068a01003020480c00280301c40d000c0400100c5002c00c880304030072400d501a90000aa680b0200c00c030300d05244980610400240c0321a00000c0307001264103050091040c00c1c6409003502501c00c030035050051280c0046d4071 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 683875449 1250 683874199 683874209
    0x30d0c030804150905060c1909050a03020103020705030f13090c02031c1d010e031213080d0c0309021207030501050604021611041512020406120201020d2d030e060907 73
    0x141d4a41d1640d507102080054018981030322241e41c1c08610002503800e0001a01482d24401d44645845050802c03541c00304520700380b10306200c0b03a408200001e44590040004407030302401d005851740344a0412a041d4030950b91441e030450780010700360740c2204950400d401542c030110300401c0284649070041c0e0780e0748180740c0c805816130400c81000d292040d0070780060900d240519401d0707204008172941c0b20b00795401085140002d070404590111603004030304949911041040590328001032a4881000a20610030301d0441203484118148c8140d003e90095010207501a05620b24801591030480c0c5500b05c60000b12090350030070010813440d10303180c002c0c1c1d40705040c02404e074000c10585941e502e060020102255801a4440403100c018412a610040041c2b05c01c80d800003031000c203881000211004c98000d800c0c4040112410000b60342c0c00100540404102d00b0072a4a03004c6082e0706101c03805032030049802c2c403080c11600c5145154103401004407002c00508441031900c4448485403503645500803 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 683876699 1250 683875449 683875457
    0x301030305041410120e01060b070b061f050d0b010c02060a032301050310050402030c0d0b07090906060e09040f05060a0f1b05030f0a0b0307060e1905060a031a0402031302030d0c03 79
    0x145a0004c17041c1d40444040c0000c140001035043d0b82d80b40e05a80e0b41c0003c1415501801154104030075070406168102d100307001e001102c20720828400d40a0468021382031440040780d41c2e160024003990043c03050403600c0b03400400c0b580d1195040d580040c054203205e00c80ca0341d5100c0c0e00c030036a080360030321406081c143c80c1c0080280407558244080540203160041060383d0500c6048041516500e07060100d908190203000900b035035244c50a000380c5581480e5002c6c25086240c44000c210640e441620a1401441140c6044281d01ca81c02d04c0e4902a1918201401034001c1d81309001c0d400b2004c0c0e00c0701c0c80c0080d0209052109501d8400004200c0c181c0c18421404107004200003032189034000007060b0320800c1c07000000355118165001c40d1806800743c0100b40407803900e004002e032929210141104400b503148111070703e04d041c50085a058003d00d0000c000341510750005c0041c403c80f49a000c43d09442c06003046481c1d140c103096411001001050583c02805051042e0800c640315401b2210074a80540f1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 683877949 1250 683876699 683876717
    0x501061d060d0c0905060d02090a0b0310030b09100c0e0a120b01030803040807080c03040311040b0d17041d061206010e0411270a15050a0306020c070b0301030305041410 74
    0x105450243c024103400c01c08000300280003203251781e6600060321104814403c0103844101040a202c2c0d141500d8221140494060003006828031441800e0b00c190ba51002d01c4050741d444040710b1a02d000c04070301e038561200b82402148191707150f01c41012030009200b00c8112100580d100207441c600010329502400a90b080b04c0148007280004006507003061140102a181c03101c1520385250304d07040080111020b030000541041844849000140076070000c807010044280b0403000031741c0c1031800f00700051519422520207140356440340180c0b4003c01c0a69920341d039a124010611440420440f05103100d1215090001c2826600040c014180c40260050b140329440361388500340554400100301e6449101d50000815880000e4800038203044102d4110100c3d0078032407071101c19191041c091109a41d10b0740300c03c106075a03c2c08011404c40e42c0283c00103a58111255589080c1005078020503800c020001c00042055403000003041100e901654040030b003520300b01084140260300305c0d1200000e1100e1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 683879199 1250 683877949 683877967
    0x6050a0501090905090a02060f0c060612031912151706010e07031e230c191209050d0c0c08120406030b040f05130501050f06010c1e05060a0501061d06 66
    0x1a001d05e07081484542100c3d02c3e0a1243c1c00142c0030b41c04105441556040855444900c034010080e068000030221043d0f151640605021980c0e03000b6030f05a490103413101c81100340c40c940244590503c10172542c03001d0007018912051204420300c40d1003024624511050300506103000403920707905950404003812501d03114240c00710701800d0b0310002035038145048400d142008000d4850100c140b820f44200b40d02c403001071480964000001011806c42d800104840d00a00d140101022103448090810701d00b05c002c2e401c8150024145481c0040017441411003080c01203400031148055a407141c41c003041d516071181b0115458039100b00740070740c58481c107000900506000381c00020442030098000949812102d030204242e840c240c13580215111480703006004e101003800380c254003214000c0041c00e0307400c00500081c8441e041c0140900724000310300704403100c1ca968002c01c20350542c00204903102400d0449080004000038494240414051502c201d440d15031051420700350400144100d00f050028 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 683880449 1250 683879199 683879201
    0x30906040f080d0603030f0f0c0206030c13030c080a14011a150c070e06030706031104050409050708070b0316020604021011010b091f1e05040c14030403030c0306050a05010909 77
    0x40706080711245000d00a40c54400814450030000b140203688440400314a52000b800c201c0342c5550160800c441d81c2503080c05600c4640c11a5007190b244105169a800d400316a1950b01d40c00390002005204140c0e80002d40900000d04914554001c502e40c2c0ca400103803003501030032584240c00d005407070307070322004500b4162a10400e94920700030f6103802c0500e81081698100e062440d00d400c4405841c0001041c007829040c03c02000c130182c90203007400c21031560300d1580d440c1d242c040c82c41454820f0351106180820040c09007c808002d1100c182103800c240c0d10f0300c0486200b50811216407501d482400078412426200188150040360090060804094500400c60340b40c0d56a103c07495956403074440c4183c80d0b45400c5007071407150b16810004100450f9210151004030000d03803100c5888281c02080560108020130b0361401c031791301120000350101000b081030701d50f01900c00c1010300804010041006040c3c2540107040d05007030340d0b6000c11403240c41c0e9003001a14186406903500240d81d6120520906000e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 683881699 1250 683880449 683880473
    0xc0106120302011104180906090b04030206150111150c04030b101a030705120603192619030209131a04050f070c03031802030a080a03110403030c061505040515130203090604 76
    0x14079009c03620303c095490b001e0b030b400070507542100140d201c4000c2102620b103401180c1c41180302460081e400600c855442603603a0341802021f03052a09a00c082a9580c60540c00c03500156404150854140361945800d810342000f4889c0052802c0710309107194841c85031800b140e10908a5031030716814401240703407800000704010300f455090b201d509a180d001814481d0103600941c444e0440302101c0d01c6c149010004150011060444c8031001c1c891201c0700c0200c0d80000200341003c2c0340058a07654070707038009103a400c2105200d40c12a4500502c004404106400f0100e058400759410701840e1100d1965840310103044407038200041d13900302e000000910940180203c03511743d031044210084181c00290502204143c2121074100c00100d04030f03419014016807030420600c01013103007040c0c915103010706102100500205520b54880f052041c07074940c00c20242c00b401010300300300000d00e8542041218200c0003c0380602c0b485403288060f1660425008480c46488a81c000c2c2119071074a5481d003912280c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 683882949 1250 683881699 683881703
    0x705121f2105030d0207030e0306042310050708060118030302120c010204031505040b0a0b0105040b2215020f0c0604051903080c0109030e091612020c01061203020111041809 76
    0x710051a10000c140104003420010b4400344005a4506692501415050250385101e0180d00b0000070000400d400390204541c29072022400c0304400902a24581000302142001400310700e800d0a000285501003440341c8550000e803585118076008003070f4040322042d01d120040c0182c0c48201540e50074426a0090b10b81c0c0010400054105600d0f030752180c5000103100c0d80c0641700d903030710310802c0305104034117000356001207040004210443d43d54000920621540c0a902c001820018208403140002d0542d905a0040c02218801d10b40c0c641088401140e0f400741d13000014401c00c0100542008046a1010700b020010141450a4544014016522040102040103000090000000c01d202800030f241d504c42c844000184601c1505d00a803480c4200b00a00340142032032403c1100410700d001c01d0601034412420018035a403080d0102c00c020b0700c00d8102131402542841c00c0058068070328904815958402d40080c85400301e006106c081034015403250307031500310f0b82041c99450640c40c0c4d80400500e80c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 683884199 1250 683882949 683882999
    0x50f160203090306090102090913050d0503060a051804021e0915040219080105100809060f060a05030a0302031c0b0607140c1f0f03360b0705121f 64
    0x1040b0500041d00302030381181c1801c0d141c2d400103001c031028604440038561004200f946ca0072900304585409a80b0b0280e07100320410303c4000004070f03000e40c1c6c80852890050100510910044451200300c0020705c070107032003c9000e503d800480b1209a4100300300850311402c080e004c01c2159a606000304074911013040c0f640d42180d820040075401c0349001d8007410300e007580c0d6202c0f90300552505082c00300310510b0900c0d0408202c20b0350140840d500c0082039450f004040340450042d9907c2d1304000407241000d035032100340d2500c10080031a04168010011b090f6200d449000e5401605541d40207406a5001e0056990700000c20001400080c040700d03800000e0744e0014013101c0400c40700c040071981f101d400000c044107000c7d032101c582d0b0445034826410350600764240340c140310718107100e0303055805c0d81026a00fa004c42c100c80400c5030340498101380c1d540c50107504150310080501b00030201070915172045481d449041b0500000030350200080500100134112003804c100c29900c1c098090622041030f0b90500e0310f00c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 683885449 1250 683884199 683884207
    0x50c0d0503061315140103020f0d0f0b03031801080f0f011205010f05040309031103120f07050f0d0302070c080303040506010303030c120c030e010b09130305160609060b0a09050f160203 81
    0x1450b9032050940132602c04580801c4a4200000258100c1d031900d400c604140c010070904804001d224180c0703d0b001c03119036011035510f01011078040a00b440300d110b10b4040c44045081545402c038100c1e0032110075000c4e00c48010640324011229064803048551900b412400401003105640d60524103906600550001030041c1903070416406840054800b940040c442d0381c028401d000c0030307072000d4882070800c40003000c196130703512214030b0720b03014002e2421805a0080f07043c1d01072000502c20801104031720829154040503040c40030b40250000c21040d694940d15020224400b0340000442c0d0107150010001c00c0c050703180daa002c0f8082c042c8440040108200c20001001d10003ca024031041d840c00c549020481c2d0481100340c500315a074544104d0321403d241c100344000c8050080c81c00c0ca0036a018a0b0041d40c0f03481c001c0321130a04400040b40103100a181aa2605c03e0113136591040c0001c0f14116045004d0310307074400903041036681c20390f000041c14540c2808150681072400440c642e145550040d6424 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 683886699 1250 683885449 683885479
    0xf150e04030e01021e030306130c08191509050a0605030d020309060a09050d050d11030406170702011e0501061707020c0d1b2403060605030a0915020304060c030507050c0d050306 78
    0x1d0400910401103606c040144800c0d0f19125950b8401c3e1b0807030000800c04486900c4c0b0040c40341102404000c0c021490b106880403110264204000e10800c0002d400c1615a40e69000380041004640200b800c1d403418001082d1850049022007003401190f000b54101050700b003c00013198000070306c84c014001241d5002a0584031441081c00f90f81c000c6010300000b500d500c01c05400580b2070600c1100642040000703100480d0064021000c20b11080021070b0705540d03d101c10b0b4010501044070590050b50468124a0302c0d000c1e070001c6040e1489555107464095400c0d189814168040e40c0503005a04000341146041c14601c0c0c0c420b290900411400c150351000c50f9030300007a03003a107800a090b0410741400705101d041c4034400f10710003017210346802c0100d503180644c010a140006004154020303240c0c0c00110600c01080075440c01107140700400c41d0f684c00c0c0392400b180101070703264003600443d080000103020140141d05a0b1506c440f4134000d4507010245d80c10441d4250b10080845038040b0740c880785084 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 683887949 1250 683886699 683886733
    0x408102310052709060709030303050c1e180a060504090504061d070302090108070501051b010905030a03240302061605030f03130b0c071502160204050a0f150e04030e0102 75
    0x10280412840c081010303c03038651401840020080e90556100d501840718542c2d00541407000c40f90180b400144a46551030a002903101e161080441414000444007144140500919020f0740410258221510100500511010764403441740801da042c0020420b4034550703040350b64054828000060102000c055100d103440100140c82105e9102500c14011403c6c081c440c04c0c0501040300003803940c907261900003000f03482001460300700100c00c01d0001180c5002500244441c80d403040903651922407004006000b0000110b006a0340c06c054550030308161010390b00182501c0d00a40f00602d0100c0c00e10307000034a03243e1800200c40f10f1108000105040300380401a40c0290f144000c50040d0300d20f103007802c8804160113081c0c007003219020800c8000254815919042e0030001c07800240c2c03100b22850402800740550100690054188400c0007012920356001c88030030b50500c2400c1025200c1300c041c4100384805402518001038400000c1004240180d1000c60000414030454240390392200c4001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 683889199 1250 683887949 683887969
    0x70249051e03061804122a03050d05010b130e150d0b0612030f090d080405030a03030b010230030402062101030204050c0304110906150c03040810231005 67
    0x1140001002c001e221140c0390002500b8030751a6840302c08055400c1c13644560039106045c09280080c090842420101030000040d564400304d11030105200402003804c1c0a4695440350741000c2c0b02915000020442c0d41c145000d81c2c80f40301542e040f400340c140c01c11107245a03250001d4808442c0c3d044080804090346d544a4442d183d45106100381181070400d48140001d514000d00f1103450b5801c00e0206408040b2504244c0b184010203c48440046c0c61034100201544219006075030180503000012085c0b5405400842d01b140083e400c658801c2c0340708600d610700c1d48041140d502c400e03290381481005849032002441c3c12a000401c03041c40c00c8c99101c05409000640700407200c100d9500c10042040d0302d0203126140d40050ba007410350345940360030350f81c001d420000ea0310110b01c22042c0e03074013240040d11540341c0d090003048214042a925020034034565a250402c2c42220304511807626040110322490060f014030601c507611400040c100516408400c1c0c030000d0002d20454032045c00051140c1c1e41c40381d10 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 683890449 1250 683889199 683889247
    0x9010c1103071715070c0b13060e01051b0301060c060b0a27240608041104022a010204060f08071101050c090f040905060718090507024905 61
    0x72500510701d0340f0322401c0c81e0215001400c000131003810011059000174036010f06070750244118101b5654202c10460109142001a019502d4200301c0503150b44150b00080c041d81ca200c4070000c004040d40e10340d11407844240550400a21540707040b90028070140c004480184005021603d042e03240c014008819003000c060700800071759405241c10750b0000d40718001e80c00118004940c0800c400c00140541d94940744503500400143c10002811711401650302c01629000500c113551320805d420300e06000e4030250000c0e800012406401102c111014401c603400c6485544a5291003051200144d803401c0000b0990b1003401041c07840d145206200703105091003490b0842100b501c4844141c03c1c015002050480c541c0203526003c0c0002c0450800584940c3c440c28600e8294840d140018200f42a07000c544c2c050300c103003402c0c0380501c03400e00d4000c140c6c020303155141407104100c4016010410b071800582c01ca12001c403e0080310400c801c0c41300b0800d02e00000864141149031a4041c0c0d04000d14154191003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 683891699 1250 683890449 683890469
    0x1090221240f091303090b03010302060912010b150c070509040b010e060d0507060f1d0a0b0d06030b270a0c0e0a02040e0f1603060b0904090203070b040902090310090809010c110307 79
    0x501302056003080018028181c002c0d440740c05c56040d54041083c03031150311503043c0703e0b041180c0c0c402e0b000c5400b50895001c0500c09051200040710b003180903030b480d4102038140c0e081401011004501e5040800e41d0500c038540040302003c840c1d181034030b9120b4943d4007a1115820070071103010003010907010420301c4000c064a0380c1d0302e00e114030310181c010f00f5111074511001041c5001254640240e840007280310556403140384060f40c488051185000a10499100400500048042001c520301e0441c04e88500c0d00c01699101280c1c4132010b0864607004070010013001e1298806084c010000c0d0344581d903511007138000005107450b03103480d118660f0000481c2c041d070f80c0c140440208845070b0300d40c20403442204c190b0f0030306010150800700c80c0d81c89800f801048500442e83c418801c0c003035507020000301c0000c00741c83d82c03083c1e40c8a4071208400d000c0c1d8440401e940c001c1c8100074070070300c45c098144500c10b603064100d032500d410324004600456240c4c040c008141d40300300141103003580e41e686c20302854000b0a01c03950 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 683892949 1250 683891699 683891731
    0x51f120c1e090f0e07020a03030c020c0d050c09061c080a0203090a0915090c090920040806040b1303050901050309010b190303020106090b03030a0c08040e01090221240f09 75
    0x100e00400c1c00d81c43c1d04103400c454442d03c03d01a070646c00041342c2550325454100421001c6400b0b000302d1078840c1554850764802911100c01c0140a0041180c1075050b0b03080d5000000e41d03444005001c4110a402c120200ca1143c0096071804500c05502600810b4003503c141c80c60881e40900260000702d107904a07024141d0b03510101040030500c408144001e003408442442000700300305020340550070b03d21800300c5880c0c0310541c5c9442c0388104030200074021070505890781c82c0e0352601100c55840504450450b40812a175020410aa03011808121080c2d410ba40d118a0702d05400c0044407190030280c030040c029034865258001c2c9a4444031446c0b2421240c40d59039a000780303942030090035180c256104840d201d140038003041d010b8601004039088d046c0300d800c0c8454820802d01d0304c0c44080c820369101000d07003020000045901d0301c5980080c0100100c04001041aa48940a1b028840360a54000545119071440b9060030b04656290f60340600000b000b852000900c80041450726070221925060f101740382c4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 683894199 1250 683892949 683892959
    0xf030b06030c010305090d0e011115180a050703021e040906020a031a0f0d0c030b1f0603020a09061b050318100c111e1306051f120c1e09 60
    0x107030b010096030900e418019810000d66454580303d40c02e00c04001c11401400718540c5901400074600804981001c407032072400080b04c0c11040304d20584040304034003801c00203024440000601c031420703540c01401030211946540c1c00c02c9441420450310b072400c1510440119a60341e2148580501d0a004000c0503a40e1842d03408024100c88080c02201e000c1c80003902040b0654444a0004088141c2600d81030305408a0f400e240141c1e45c600d030700090085071010200b000484030348900040c40c5a0a19060b02c80700c0d2605401da0a9005030a5403000040c0480001c001c010322900c10415820052408059584125203600c0d055078080d884110049208081080c0d040c100b0b00c041c034000c0d101d5440d01003a009074590780c0c0090480c9c0901da0341d00c5092000b44000030422045540c01c942070009002c00b810303040310003021014203403a01c40d02d4401c2245526000307000c80d03c142031808200f0140d40d6001c140c482004500000c00700d00035004100311802005002900b007540002c0e41d1990640c40b03030320602d4540 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 683895449 1250 683894199 683894203
    0x5070f1a090424060e120c090405150901060509060a27061505040513020304080708030702030d0c120e07080307080d02070615080d090b4816060c1401060f030b0603 72
    0x1170100c1405081603d061803c105000300d50000c100c2000c846142e895200e0782419403600794014040744a4461500074005906c0055012030115442a101c80b40c2581d038241c1000a128480e128819041e041401040408800008450076a4900c400006003440d01c600703a4501c001d4408a03d0300106000203024005443c0c00c4801c4110048280c4040d460343c0380941d00d040d098095514020030302c600110204c2da910b8000c0c410303605203900781c50f030801c40580205002440c03014101003c503515447c00310b62485292006c684441030b250b04078000c3d40340003941e9076100c21036800362402c0118681c0c01e010700800160140280a05050041032a4152034203085804e070038007188004d0b10040c0482d012040103030310b2510b81610b04800409154850b070814074036103a0b00d0b0000001c0c2c0f00e80b4076580b038882c02c012941c2d402c004a0740940d4a41c21174110400c0085418030390204c07030141b8400b284002e10b88000040c4801c0461010907100e10010850580d0358003c01d0100000340c004544010000e02001498141 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 683896699 1250 683895449 683895467
    0x50403121e0605030c03071203050c010c0f080a0b010933050901020712020d0213140a0c02100b0901120302070e240405190203060102070509100305070f1a09042406 72
    0x7240549403d00a0a0002ea51f0360b0281c4101030b07411080c0e2079000c0a0500580540f031882c44194024800e0018481c8000c0030881d448403c080071941050200340e0346040c51007540c00d15013040e1074072000700d41402021036680b10104640c101c1d11b03c1e14a00325078541c812032400c184072489501c0342926040f02070b00190504a0343c1d0412603031140d42030045405030361000c5101c940103405440113981100440700010192001d000640601000031781400420b5100340e00c401140c006507070031340b4240c0092014200503030310f50415151341304c09440014071140e10503940c05100d00788240101d44a0306d03500c0985c81c0c03d034042207a010203060402044030144400c00c15038401072540880701040145040c01207100c03114220608900807a9002c400103810340d0080000d0700180000806080c4146491800400ea941c4e0b2808111910b003e01d40c000a20710f50020042000c0d00d040074000040c015140080c820a0b0308404400707a400f5489040111201c41090080403032241a203041d10b9546050460103818112 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 683897949 1250 683896699 683896709
    0x4231b040e010608241006050702011103121f06020a062a02030316110d0f141c0e01050105010c0803041704030602030709080601140409110a120c050301050712050403121e06 76
    0x403a45d000c01c81020f01d01c00900c016078501d803c140362551802c0c00100d900764004000000d4911001484840310100104442d100300009001300f00d1184007041030307029100c2580300e280d0250740800440000601c07a03030002d004080000518422500801100720030201452842c4005031b040007060044050141c09a071800d0700340760800d1091f40544040d603d40c0d900041031070301c0070400502c0031080388074840c2c0a80c00e07039031140c29045030f05ca010801d82c550746901010116190686408445d041501041c090107040320016100c1050111440e2641d030002d5200900441d048683d248805030040f648e4800351014500540005840c1d1408580141010b44e40790840c500c00c1c1c1c4000c0040140e1450740e040b81c1c405005c195000716807402146400801030031b1103179216501c41400300001c40c12050550f4204020350044620442ca07940e500d061500302c503000d5901c0400540414450303001c214090f0419600315219240590702120721014a100f195900f80b0901c0380341ca80340100340400b402078001d401c0500 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 683899199 1250 683897949 683898013
    0x20d0f030311130510090b0301060207170609072102031506010206100302060f0a12060b0c06010b04062010090501051e062103070c090504231b040e010608 68
    0x10300b1080d40d040480c0d0051243d00d10429580303c4105d01103100300f070000010030342145410740701d585030400a500e4102900500400103046d90028104240001d003480c090a0780b00701030b0070350310300b40700c040d916142c400b10f002c412090342100801c005071010044000103040301e5141c0745850821100090910b2000380181e0140101c401d070510142ea1084116001c618044500d60f40c3c6005400c0d081c2c4030302002030381445d50640750420002c0c803030502078020600850f10104ac0e8040341c4e01d44010b41c09502a60250a000400d00803941c09125500c1e03c610720000c62003801c9a2a0101101a001c1070b1a030140e0300301c416075160030502c070034200c00d05090204c10740c0020000b0624600310021600c0c0080c1c2c01400d20000322203038840c00219406004464049800c84542224544c55961890140c1000e640403281c040014000c030f0000f11210144201c80510480034007108442d4465900c0390b06030100c84584d0040c0d0b1103c065142c5402442031000400c0c83c1c0014040c4a101b01d1248840110300078090301c448 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 683900449 1250 683899199 683899207
    0x1e0812150f04020d06030f05160803041a07020103020c1006090e03040315090c08100510050406050609010e06160609021002030a050a081314010f050c09100c0807020d0f030311 77
    0x256285540740ca20160140c50060300d0742c1600c0103150242815900141a04038858a00c03800e1100100c0d803031440c03c200e010b0000010f9541e10416690344a10321410f201421303580310f1000c076403103c00000c181c0907005140c098207206503008e000e402c180b00100303848030095072094200510041030083c0c4003a81880405103060501d1511034030302161808180d00301ca40c4c0d541d1403400c204880010340a000e44201c070100c0390605540c1365000000c10041d5508044c450040304001218a010701610007a14000392195082c0540c07903006562400729100102e034003034401d00108002e19100b00c1c2c80701010b8000e10021500302c2141c010f001c00e007002c0500000031504100306904d01c03c0c0d00b18003180c0c40d8220381d1900c40c090742d07665000700f49450002e120050000007021031380b00b0190015000103240c401c103404100410703103410041c1103030f41c4514148c00b500011201078100c440c40c002e484070801603008a02e442e20302805036000550325504001d080b5800380b04107180505140e0b251058107034a03001010350382d02d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 683901699 1250 683900449 683900491
    0x406020c010e0409120216150509120124050a050406030b130f240c0810060e13091b120803040b04020d0c08011a0904080d091e0812 58
    0x44410100025041c40811002c26006885035030022440e20340001e5800b40748040c0000094807402c9072103110000e035511300030104885154564180e031610b1903440d6946484810340500018030351410040603c1e558039003648110900c0592105c003100c41c06035200c0c0009040404012030b0f480c3e03580110f03024500c3c2150900000d82600030f01c0d40c00c61003840000c0c0d10744505250034200c10740210401041c9415142c02808400c880348220303070380052040d201380a4415030302021100f00074102c482d01c0346041b0200c07080002500620324490450030190480013044070468280b001d460001000b1144864a595450035800c1e0f0b00450001902c41518003041103066a02c0701d43c035900021700050201e400b1b49012400315541d04200041299201d0040440b0b141e403080014000c002c0c800c0001125440b0303101221051910440c0139100d150b0200c5040d0910ac103c018035401080c4290302150310303100340b00421123041484044500c21500c584900383c3d4a0000000c81014148083c260f82c804900012607046 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 683902949 1250 683901699 683901703
    0x4210207080111250f0615150f0e040507030b1513050a0f061b140a06050603030a0914010509060d0c0e0a150309020f0d0602030f0c070308041b0b030901020d0b06040602 74
    0x50131030000d9040361505015040c500a050401000181590320300300c89413000c0102c0500b46002c0312500300c1c98251600d004001070b100c1c070f5042040308002580d10084408289001d0f4041070300041c5a150009908134484082006000b042080d01d80001020070000244503032401e01c0405003905650401403680703402954400c1110a01600c414800702181291311900f10440b210040b9820400154000341e40030920b90b102d001c680340a450321401e000000c1c540741030010071610b04404550f642880d19244c40b1050606980c0322001d64104003042041c640c0d1942d5140c080c00320469800070004501c0342c07060024002c1440e41a91600800c1c00c401e04000300005042c07801e11852440c207011950381c000307100294100010107405940591a00110b00c00e21044e85d019511843c00008011110740b1081e1552241e4003403039000500140f8228005800511900d0b51114002060000c4211094840182c42a80d400448044580303130740c0803a00440d000e106018107603800d1000d0318080c0c501400d1400080d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 683904199 1250 683902949 683902987
    0xb220e0d1704110402160c05060915070507030515070f020a0b04060209010908120408100504020a05131b2a050d03180b100e0903030108030d0504210207080111 70
    0x10003001071500040d05010618040514061008100b1580c588403c0346901c45080c881000b03175808058000086000c1c1440c2c8101e0b86142c0b4001c00c0e444d03840c0c0d030514140030320760300c136940849141c000d100000000903c100a280c02074000400015078610342000c000308650415641841150301c00c000040100f00d1000c0e402d030b00240c01043c05a44c458025006a5100c2119401291948184582c0752800f620340005001660902010b48680800c0c10011200f07035441664003070340c031052169080109150507001181900090030000c103030386444034400ea0049816901520100b258511000c944000150152f009526600403024082809072581d0341c2c2c940180d544e1030285540c58220088070750407129480c04c0540d0286150320030b80390450100d81009140e218a128000b0795401050010a0200641c0c2c141e511800042d81811a407540c400003401c8050802d9400b840f01d1503400c0b6a045818480c4c100700d00041d00240b99151802c00d11608480c420440d00711180424450301e43d60604041d210 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 683905449 1250 683904199 683904227
    0x70e0907032d1b02030a0f020f101e1a011106090c090709270506060403080304030c08070b0708010e0c09030a141e0a051c051c0b220e0d 60
    0x10280b6080050140d600802500c41d03800071110080103c40900c940c008010700781c54110ba03030f52510115901d201a81d94910140c000400d5400013100054403800f2a44103500e4840d0304401441c15000b00405082240c820420104191075000061344065811215202d820b0104800911705450000503d0b0b4840d80c002030981d1048142101184200b4803078540c0001031b10450340304070403c2c8c1844003400ba2031414490100c40c0141084000303203007131400d001594216a000072006140d603071903550888240c2c3d140c0070104d030120700a0182c400842d0700700d9501c034490301845d04c03003041950400c00e10b052960070050001c1642403080103c0091601c003c1001058941d11240361682c1e203010000c0070342400001e504680c1c60004104620260000014281402d24040d200340c410b600001030002d006114804440402701d00c04002402c0250700300e49880c40152058040064440c002034000b8a006c850490704030b84c0ca850095083d046030305a8420b04203030009280040444006c0058060007100c136030740b14 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 683906699 1250 683905449 683905511
    0x50108150a05100314130b01030b06060f07030c020307051e0f120307050604031407120c030c06020a0302040e1003230a0203150103060f0c050322020306070e090703 72
    0x19a41251070709801c01010b014024100b00d06151403850090040101209450340020240040303108070360a40d202004071a080407528280740e09686034074010100103040140c00260800120000d448004040c0281d94420350750394080b00c00d540105440e1801c00c0e04424428814008403040f07000c0144400c1945440680d5800703d1040c855000401e20000784892100c54040068900104900810b40c00d20840c03298480c038003107419000481c80f650280b00130080400006143c1c00b01c00c1401003101c2020342d0302c030f481c240101c0c2025a07582c000b03a0b046103040130701207034011505100400740c2c80000ba40c44152401602d0b40c0ca480c64a401c0141c043c00c80c0003881d00345003800782d240040424001c0d08031040c3c0180440f8260a4800d4580703406080c2480151052841d02c402031000b06c00a0180d944d420500340c1d145805c544440401041d00301144148c030480240400003c0c00503101801100d2050020b41c85082c1000c640d20140102c0c840003c20349402c140c5080d81c501d40c1103415491030010302e104454 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 683907949 1250 683906699 683906731
    0xb18040b0a120807060e060402240909190903020c0a0504110703051c02070c030b0702010e060103120210050c030a06060807020312040807080c0f0f0a0f151116021009050108 76
    0x1046600c0f4031070058050304046c01c000103101d80d280009000c41c0154400d81e261105c001520a0410503d542d640c000c060480b4100302d054082c0c03908008144d041044240c0c03e2a20401d005c03800011138000f40750440145cbc00102500c0b241d8074220401c0b9000340815a414810044a031a460220303200381c502c0181803220200d41c07200e072044070300699411100300c001d04540d00d40c6941841d50404281d84802c850065003107001910352403045c01071000d5410800001c1055900f196241c40700c84548030141411032103101413105801180d8001c082c003031a14000040c0d034038100208010292921038000000380050b1205020380d40364000110f6030a00110039240700141c80303910700001c0910070418054040000070422000e032600100344840e5101e07a420444c1c0054451030700460300c030f08810002601d0018040c104202081c03102480383d200120120000641015000e82a030007500f1681c42c0c208648150040300007141801892610703050340d00e0401247d50b83c94600001d00481000b4020a40020440d03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 683909199 1250 683907949 683907953
    0x612060a0c26011401110a060e28020307120b010e06010216140f09011203030b03011b020f240103030507030905091e0a0608030703050a180b18040b0a12 67
    0x507840842c0b02903007502d003401404840051407a221000e02407000c00c02c8003102d5003040c030b600031041228642260000740241c008542c451000500d8035400e551680d0044904000c4000c8101da00c42081001d840444610300042d4010b062801081e0b404c01c40c83c0300c10300078000e000304a44486190460300382d40440503480d9500c1d03004034105016409010f00b440ca40e10404101c000c4000040710107a10195a0140041195001c110540d00300b8844c1c0c1611402513504140460b21070703000000030701c0b0040c00124085510b03140100072181d0352807030080160007507101107a403840c0a020403418906c410304201d4111842c64a0804980070605c03000301401340000c0c0355820035001d00a200c00800c0c0040c49030050385408480c141103041014500c40b00c0c0710451000403440d400d144103140580320f04400035804c180c0581d0b0309035115880740c6c7c00340e004c0c00100203181d41c90456910711a0080c01c030300040d09440d40c000407445204030100d401c0c0c061185050450b00d0032980c5070701d207140c0c00304d0305034219011030403a882c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 683910449 1250 683909199 683909207
    0x11e02070b0f0c0c100b03010b03010c231c050105010f03050709050f0d0c181805100b1906020c2b02060d0e19170f090d021c0302060108060612060a0c 66
    0x80d0030a000074040c45d500444024240c0e4021003030355409400038004a010f01d8201800c8818003222400440d103030722403915551410304210071500241c01407039454003014810300c4500100c0c40b4a504007940d150b00c018406542c0c800e1010201804a0505100c54100510090b00f0301d5007034001c0c42d0007690b415002d02074580d038840c24030708120740000b00c10b61b107151104840c028604118440d03482141c00c00c417640c43d071508140c01c80030394660000058030241d403401c4044400b4140c54800d059010541ca402c4503201200f01b45541c0081110f03070014240c440c000760500035200003480c04604001d0826034403101184070824609a1994100c405907901c8a40d02000c800a00c1010301d110082c1c890f1075400c6082203100c0c2e01c08808103001d2044480c40d01c40080a0b00b00314072a00d8203401c10840140150300c40346c00c1c00a1100000c2e803004151a400080300b40d060354091701c0904081c1c0040e40000e0042101c000f0500c0015003011065828140766220a0327a1141e552002504024045ea0b03260b100507030061107 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 683911699 1250 683910449 683910457
    0x60304060f0f090b060105071106031005030d0f0e04020304050606130e012f030105010f3212010b2a0109080309030304030e010206070f1b02040509011e02070b0f0c 72
    0x540310700308054500010b12000803d003c14086541030b9100c00460125800340c03041d64496640405480f01c0510500b0511505800280501c0c2e02441c0003031000c01c10b40d405110303440200485554281154100550003443c45880105580c01288104240408900c1c040b40715940400240c502d10420304c241c3c49640c000f003000c1c10070901c0651a0030900246240390070708240d07482000e400080c0034801c1c0c002d2060a58842807203481e020410740c1074036007450790282101c4002504200400c02c1c81411013030001c1e40c0c0c0314900f11440701c020740c00504010b011400d007820030301400728043c10b242030406510445400840446504503040d0b81c0c0d0080032400d803800d4004c0700c06243c0c003800b490340f01d0070040c120660ba90002d8a049000c92400c4490015652001589610030522039039007200401001d41e0030369004130390b04090402d07421306c225400056280c90080a000e041031800010b0034404604402c44081c0c15070101c011424010028080810300350340d09950046d000d81120b01311512910101095845 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 683912949 1250 683911699 683911721
    0x110a030c06090302010e0a0806040b07050c3304050601050d020301110a05120a1e0f020d0e0304050310060b0912032502040501050d17160213151d040206030406 70
    0x42045021640c2030b4000d41002c1124400c1e26804100d406501c10016040d078140038010729a0711090014000c14074800d00c030740e00300b500307420000d2a200c00c403a441c90501e04281400b541204035800c0d07441420745802c0111465500e00d9000ca4141d061a03960143c0b294418030850b031051411042c403406650303080d84440c2c0301e40d00d00b00050b55181060000508650042000140310030b840400013030211405014240a501300303203403080c02195100f607080300107000f9155440080d5509000f0120030802e2840390300d03c50b8000030001e54556240c90101403602050240d58a0294209082003020201d40300584032040300031200e0080c0403000341034245c0b41d4015206003403004140342c40e0116074244601d80d01c1c48100e0007614244110ba0726074081c00011030301850000c05801c100090501c1030408100603241001203d40119000030729900090384418003400c0254a09aa4203003410351400016980c6c801080303861241c00740810140564201d007040188003030b00a000000018041220f640c0c0601034101d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 683914199 1250 683912949 683912963
    0x1020c0102071109100b0f070309030b070903050706020c01050304120c020d140c06031510031e06081608030a0f090e091501080c030a0f02060c0d021f0216110a03 71
    0x80c00c2c14900301110b4030000d0b403030080c030300407005c41c80030320301d189280c0d05075600420f0319403810301c10051b0140e240d44188810740800a5140000c000644406400360054140342d544900040c01d40c00c1880c05c100e0720364020000d40d4400c0000f910b0350b98002055139840364010000103000071908005803151071030a80000d41c0901518500c03002c1001340c0c000d20840b1003409003102c6151070040309011407803101359000c3c0030105407043d021605181c00303446d80c100c020b2585008601c80c1d1481201004101e0f01c0d0080149241d112441800441010030400d980f40346c0ca9010819001d08c0d0095140c0c8a01c41d1095040800002ea147c0003009401041010010402c802101220349809500551665490314403407260155010000600320b0000070b03049044c40c40180034140b40903280d81c4940a007441014120b8202e1000e0000280445007031062000c00c6405401420f407129024440d49803000c1c101030781c000c5640c4140902000143c2c07130b6160015140e4004000c1070029092000582d0020140d4070081c40c1d0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 683915449 1250 683914199 683914207
    0x9050f150c370b04061413150504030804020603041106040b0a0f08010b0f0711090c1306022103060301021b010b0a061403071b080a0206042315070201020c0102 70
    0x4480006103806000740ca1019818501c603810503000c18030400384401c500c42c1140c603010360002c03480a545035a00140308000c0010380c84450301303c44214000880386103000030040f43c91441802460941d00031900c25894003004103140542d0081c00902c0b0282000e1f0069201100280070070200c44424900c1c0380009051540755130390781907102124ac1c0024100c4000a0b408014401214040e200b55810303207144081c0c3c107080139030802860440390030070041515180c5d0100c625070800d4841d00002d030301469910040c250f0f00d420449114030305044941c4507200310741c00302d048014200400e8020803d80c0d01803a5050703030303213403900700c00280640075950b0401c040265400e01c403da184c04c15440f80c6408102036400200c074903a2180c06a815007200710b03400449003810000640300e07501c030704100031840784020020003052495071101101d0b908000002c0c030142e03002105010070700100d1208810035101d4000326000321400301c1c2815450b40d00c2c94401c3c0e08030303000050100355858000c0d0190348421188800864803 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 683916699 1250 683915449 683915467
    0xb010806041a06101d19090b01020303040b0a0903090e13030807050a0c14070b07080d0f020703200304090c08060a141005181203070512040609050f15 66
    0x842505031402c6a011254901124207446a50300d183e200b030304000c014018a118101080e45c000780d8494107540181d404401451403a600d00100c6104c2c0419403508299070b40c01c00071000103c803400124107065500c2842084002215441e5280e4800803001021681410342d16042e14a04000c0d08207030f07011448402084190014148040c040310301a40c1c0340c440980b0341c07000a40300c5105080d6400c000900d2140c0b54004540802c140758000f0300800101c41f00160784030241e056a4200920845000d44009620003580103540201801540c91840441c603100c1603a4029216000703031501e0000324000b01e5004a50310200740181c070001c1400b0031040c0316052880034001c0c400102116a06d10030300d003210000c5011a49543c829520140141a0f15010380d040207060b20707030340c010a10707003800001c004040d10281e450350f0b61124000b250900085803201c0c010324206003442d01086200d40741c0d500510003004800e81c0701203c42c0072510142d50b115000241d0074081109104040b690b10503001c40004d98200c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 683917949 1250 683916699 683916703
    0x2070b01090203161103070615050301050c041406031e0a1e0c023c0a0f0f0b1f17011b0e0102060115021b01170c0a09240f05070b0108 59
    0x2100b5a90000d0705800b5004209003951145182c01d0100c91131b80c02400585c00081081d4030481244280078896a440e543e00ca0020b03003510000c6910060500c0046400c00410801070454140f1060031202c803819451700c0145400d01c0c410425048d14000ca1817000300c1c61402040d405004601406040030900c08505090314000d42901304c110001440b82001d100007010300922500701615005224807912000184a02c01c0944810074055641c02a000c0c900c0c0001e4040f1000d0295078400c0010b800e41052074282060404002040041c80762440c801c4110701b01c0c2c84005c0d0344252074012a1601180d03549403502d81c0100103c03110306010407001501d0509030b913080002490048026803c41c1d0780c076a243c0041c0c8820303818800150015901c255400719000b45040e035212028a410b00d4500003000c0406140c24400798150b454040c04200080c08000e0300e0f9018003690050841e41302840000003407a80520364540d070110481c030400c15500310001e000d501c520200c501640c0c00c44143c0e10750396120b0386071035 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 683919199 1250 683917949 683917951
    0x302090d06021806070f0201050a17010801050a0c0203161b0302040501090207020a080a0b0f0717040312110a08160e060a08160309020f0907110f060117070e0a02070602070b01090203 80
    0x407903031000e83c0f02c0e550034607043e81110f9074030b940102c0764180c99241e54015501da4210390102801e001031034442c0c111035600340446500804140c800482c1508250b00c1c044201c40795080c0180854008014107944900940c402240d50f541c44401e400c404100010811104410782c0c000947c807604040001030410800d802400c0106c0c000c4510001d403d0f6508a055980c4250b104003c00b01c0760350300c0001e2070904e41e00562a9102205003041840400011401c403038801d002c4038200c01043e101e41c0441c41c0c440040c4a6582516100c0e081c051030145004005083c0c035000511b0701c0d540d03580140c2540c0106100305d441100984000d04443d4480e01e08020141c107103501194000ba02039505600c820419200380604110142c002c0e01e140c00b86003086041c004443c0008084905101001c11064013102041181003800a40b41c4060b00c02541044403002c0040d003890000303855a80500414805000117510960704030225140040e44d590440c508400a40074003807014290807142c10002070140300a070021 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 683920449 1250 683919199 683919217
    0x715020c0f1005090a0f0f020d080f0c0111040506040e09100e060405160f05041d0613050f0303010f23060301530327030714010815010302090d0602 65
    0x10f000302ea503140c810b540d50b00d0104201910088090200300080744034456441142400030380040100000b51b1203109a5602c1041500d003401000640200d00382000c3c07040148041210404629081c84c100c00150720f0300507401021029030480000ca103000308200800e100c914422041032002d40c0241c4c0034580c88000884090316540610100c0400d005100103a000544401a00c0b0082141c10b0009110040a00b0204014012449850170402500400140d441150040d00d4030500a0300d601c3c1036030808954020f00100b541c014001403001062070f0590405446000f4281104851070188140c0d0202c1c91858054210380c0000005c0340081d904c143c0c00009148031000441034600000088100e075041c040e46100403210312800c0341c0f5001030311003080c1b0b040300b910301120706003c0b100d0000366421100c440304416443c80902c03c00014101030200100608000c0e406c000c0745031040c80083c1003618010880300220b0822140700c0050381c080d0f41511401c000140c10341542d954540740100c02548030f9114 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 683921699 1250 683920449 683920451
    0x2130f030620040b070332030901180203030a0809030714030301090506060c060406050601031d0c03060702030a0c030807170a06050a050d02030325170d14010602030715020c0f10 78
    0x102c84040101c610440301161500d8845070310f0a040754508481d640140c10300070a8041c10643c19028011079001c8a12060340380519a40d924107040c4d0543d400c482d00828202460458200305001503036021058415415580c200900c0558511a0180c114412400010803004110300c1c500c100500000147d410781d046190704201c1c41c1c441800304400c078010501030300344551088001a00080980e00043e8002006040201c0c1c0c80110448203400894034180d9240ca903441a11841075514007003001c3c580024440c00a545070030041030004241005e0502c004d814041c0034070101318018411790038180802000e28104c4400c2c00c00c401c0f080058241807203058403482c011500822140fa2a400710a03c450340280114646100907a010b003440703180304c20382c0c48060803240c40c401c00300b246000300300c0c0602501800c460f0740d107220383c480100300c6000903442d00100c401c010040c881160000300725242c42c0c0d000760342c8000f0240012400e10203442600380c030603098051444541410980028401c400c4040584 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 683922949 1250 683921699 683921741
    0x10807090e010b0c250602150402130c020f030a03020d15080604111c05010e1531060204030302160b070f020415051c0311010c080106050f040905040c03140a02060d02130f0306 77
    0x200020320070323081e00c000e548a100580e104031200e503558424440c03e1140d00594100c01041b065080c01d40c0c01c03207080e000100303400107100e00b01c41d221442070f0004040346142c551450350034002140e03600e41c80240000c0140c06030200c140c07030039500c3e102060f5992003641084c442908030781c07a01e13901914003000f210520788254107600c4120b8104084052040c210703226004203c03600304180c01000c040b14006580b22503100340e212401b14486000801c00755019400804003042952010b050b0000182d214417100c00e028400c4070000703050b90706849125501103e0204061031701030070742e1075406280d42c4015070000f164041d8401001141c14402c82840c002d8542c0305000d009024031071b00707903035800c426500041c80a40c010b002090040018004840e142610b10781025142d4221008895054030181c3e4225030100b010401c2004c00342d920446d11001c0c8014006804035540465414003540403140b6207141c0100b440304400d9000b0001d10020300505841701c0314280c1c1c174200440105000d085450701c88003129 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 683924199 1250 683922949 683922973
    0x204050a0f0e0606032a12060601180302010e0114120f090c04090b13170c0109020a090c0801140f0d1202060603061603112205010807090e010b0c250602 67
    0x224025100d14005406001004d40e20420f0300300e001c0001c00301340c4506c03100d009003174a00d07160098040f4000108000800c1c141c1040b5002400c00202c60400340c0111118800601c010703684000070561503507080c00d00d0003401201d13410011301402014081d0603006055010040640340f00d02d605030180403028155260500b1920900050f40c04186018007203200342000303d1000889170404422443c0a9072408a00340300c50400d910003580119401d50507070703441d14481e4055141c0030400074002d080f21a4204041030000c103010b410440148100300d8000c0c10604001e181d9210950b04006100d0001d0980380840083e00c0c0ad030355901c16003126072005102d80000944075040006003540a0540f054000b54080b1455604038003500503d00000718400341407205406100705243d40c540d4460107111088035084c00c00d8001480c04000406400030401e0200b02000425400c45040d0705540d607402a9035511000b03490072510b0074415000080714481e6040182c1b80740c014a6030b0800544050741d0a45a070a0211 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 683925449 1250 683924199 683924203
    0x6070906050c06040807061104080c0f0a031e051e100e060907031b0909080306191206022104150509010b090c0a031e060806130807021c0204050a0f0e 66
    0x20311032849560f210501060209070100e01030140345225040104003154541c03c401815085030b8002d9415900980e249002460540c1c006601101c060312202c604500e1a2220302d150000c7d008450394043c1401c1249040c01002c2c801c3d46102030010150b00418803200035196030f511800601c0c4641c1d039240480c50304130400089581c90041d210b45000340030050654a0750040144030003c100010805103800243d508568090841054001c080c5107450740303401824409004d003000c00e61032030f20300404000d00030305640c41400110542c020200680311000e10395a5482c2900c800304c03003900026800c0810040112055014a00c041401c60500c45612009405402d0742c40d400b0a03640c1c00860708001031030081d0707900007420004549250100b904440341801c445c0f504201410000340e0b42d01c608060014240030043d80d07801c080d40c00010b86a0740c281d500c1e00c040601413400007e101e051692140340c490380151442d0f81c07950350014003c11890501da40382d603000303003e20240c1e40c481604011810413038ad140 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 683926699 1250 683925449 683925457
    0x6060807062c011407320a0302060c0a020102040305060c0418020c0307080904091208060103151d0403110316120e011d0406030615050f19061d0607050607090605 71
    0x441e24074010b04041210041d54983c0c00c2c8040100d1200c0144044004919000c0c9000d50890380001c030520007001e11071103c02d80a584451801251f40841c81d4500003e5000406541c0003544840030b40c0c032024a4142280a4070407540003400361f00c00c83c0103004002e4035400040c011141202440c1c925807205c0c00c0322400b44d00400702028219001403060102184042001b0b10305294001d06c000f41300f815036514409881c003411881000151381204005031941c05200c0c8000d0308003800d02c4116854a40a26503280d00704034a1112020b8519002140c10035000fa00c1c00c0e054a5180002e51f03490b403c1c001082c0790341a07503040d0180d8620031020810f030a00d6000d203a91041e003c130306954200707481c140c80011003518a030010307500d60455614440000410702c544191000d411038000c2c00b00e900d41c81c000400c01c4008002541a11440001c0031409042109140042c11103099050069000c00601d03250501c4802da401000d8100c500020407904202c0040740c81c2d482440183ca0303070218503454040407030303960003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 683927949 1250 683926699 683926757
    0x161a06010f05040b16150b041107080d020702011e170106050a020c0f0303090a06050d061508070f0c080a0512180a060908220603110702090f060a030606080706 70
    0x2000f080240500a401001000e1144241c0070020358070f2050b6a400020004404886410554516098503245094020210000c03102c4244a003800c903241c40700c0c8802d202d004e02c181c1d1901d0f0b0000b501002c690188150200c1c00180110004510350352180181c1442903415618085031801d50000c90141d0065007070310008a10382c1d0040c18800b03244814000202101c4514640c50300c003d0080101c195180a101c0025000c1a81e8003a158130001c41e0243c26100705400c00b8469000740d8061000d016481103680d41d2009007490000c416030800700c0207682c07526200c1e101610740072000907800d1500e50494000d020340301d070b5400003c89640d605a08201c04000100c80601960044a100e00c0440c400380c101d094203c0c0140c0b58603283c5038003600150580700c1d0401d41c415003000c0c0c1400400030700ba00351287d00701e030215a04500f490400b1960025003003010003420130004078107140102e22180c482e5000d1401840e0300c0401000016100d0740c0352503456100f8801c0100091140900314408400301540d040641 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 683929199 1250 683927949 683927957
    0x60d18141203011a0a02070b040b040f0e060d080f091c030e010201050108060a090507050306090a0c080a0809040f0e010c09080c030309060307030507050c011b090e0f0a0e0102161a06010f 82
    0x4c00c01100300b0005512111040c0c0440c03040a0000c214031035820300410003400a00322143d83c9624100b040310161000d81d001c001c0d198500020845940c070b503181548030155005802036901c00e0014aa030a0b02d010700180540c00c0720215120340a40001c070000300220902030b4982e150548038442c012826074009000d0b070549038004d0b6000c0707014090706801a80200384501c0590300c240342c6440104e40780000803610800c60364411400e92083c042a05641d030f0142641c01d0150074482c005455032100b078410b0f248110f01603940c600c0030140300d0340307079920540300102d41000a009007600000020000e29603801080d949000c2c0da41c2032041480c0001c2101e800070070140102e81561745592065000704030003080758003800820080d010701c2c06020300c40c1070003144400c5561030051026400080921095400c11680000880103010540c9000d1415681c096042800410101540c02405019029500c4002e110001c0d045006041203c2d004080e521049090140a05641c03501d004481c0b0200640c900741c041 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 683930449 1250 683929199 683929229
    0x506040903020a0b130b0f04140d0e060a170a060e0901090f0b06030a020603070302280e040509030d0204090609270311070e0702031305010f0e060d1814120301 70
    0x101c112808942c000054203824505c034526440d040c1c04400304807400340004020034200410021b10b11120b1141c805841e0003070410715440304e0040d00400220754403510a140208108102c1e9100d1001c0c441c10b090004041d001c2818605c03403440241116000b102c1c0c0c0343c0b481a00144100105200e4080c20542008004054515580320100b516002a0003503405002e20740c400c00140c1c031800000c44c00780c02e003981c006035038404403110905400c0400f0f007018086240f00200e154030301d90004514105260031200043d076508c1e0f001c0c003546140b18112248041900104002440710a00da2110040307480c0b41d282405040d00e0030100e003000e241010003103050030448400c0e040219128509441d60402040c0c112400b0239210031516841413012541c10300160b1000490008081146c107268004000a082011a49280580150100c40c400840600842c0c012441d4001c20303555810480d00e0320a02c02409018103001d0510340b00c84400b40c051026144660b4044103c48244c60046078100c034100e980d080c40b1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 683931699 1250 683930449 683930453
    0x91b180b0304050307081b06090a032c04062303010902010c0b1504110d0b01110d110c0a030b100b04050a05060a0203071203060521060601080702150a050a0506040903020a 75
    0x10079000603006654501c810700036400050340210003412910072000400b807500101011042c90694000c2c080395240e002481d4140000350000c001c081c4800714021000c220340302c5030055002c0b0500801c9c42c0380c1c2c058140800041d514a4030b01d000c4900381000c1d00c0d2030320041d007450281401d0344c00e842002070010308145a402d0204009800c01070700480c01420911404000340c0000c6c00f03444002d10000c640d19400608080c400900b48111401e0740c00a003090003120043c109031548600f0ba04202c1024001c00c4200ba00229000380020884104003c20441c0c64a48909000300741c1c010440b00031040f072030380c040046003641102c030513039080f25002002018180d041805004850f080031101c00294401131203038070006400120700b030108203040e40d00007802a1902080004101c40540c07540540f040d4040c0c4503168070404070310380d5031080003828826410340f581c2908902e801024544402111810340c240310b40c40e8095000580075448c0e0450901ca191030308020801220340c038113402805070b0706c60702203940 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 683932949 1250 683931699 683931719
    0x1101050108060c0a0504080604080417010c080a15031a01030303061a0d0c050f120609130209040609300f110a020409060e030d141806070507050115091b18 68
    0x140c213a03842c0780640c20030b80d5802180746048030070f40381100c3c10a408101400041c500a80c0c0041c1b4200507002403100011280020300b40c02c40182143d281562a1042a2401c44021040c18000d651244000101d507080a040140c400b03420700003100082d042810005049882c90704600070b150400c034240d4a4004240300b00e800400c00e030b808050502c002071103500429800b8202503d00d240d5940940105440c140301041804034000742080e520440c0c481c0d0170400358543e030284a40c4694400000240e4005604140040350110025000180f44503180b9460080c500c88041904178596200c070611425405002c0d208075000c030401075455403080981c103000d0701d090b8201c1c0220394054030b40040c850a02d034001c241107500c001c05480881d61a43c1c0141003072810024003c0e03201110342c022004c0030307402e06115034840c44090020410072002103904018440c003903000c0003860100d8031220340c505580c1c0c14928090000302c429544490701c5103107050206400b910f40d1200603800b100c048401c5a041407400070b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 683934199 1250 683932949 683932957
    0x70b04151704050a17030c0405090a02160305070308010b0403030503070e040603083108070608190903091d0106120c020109062c0127060f09080a1101050108060c 71
    0x401005000e50168030510700d41a410380c0218010806003004c60030605054072690002604900c86030300410401503072001c41803ea4040c0d070b000f184c1c1c041d20303601d034800d05070003074010000c0804120710100001d40425400030000d042c103030700c6910f42c00e820360b9a82c00c0c0e90005008034400540419400c000040300c942c441c0281014000300104002507a94072a180c0e005240c02c5405102142c41009604207a003040300030703046403008500c00c09101d4a50500a4942d120091842404103100c01c030b030042842c074404104c220104000d130402c20400000e4a0070000c02c0c20480c0e108007550004003032402902204610100c0c0e0585110342c81d94204424050155001000e00142000c00c6560350384141000403202d0284070700c00b044960301164803600018204001051a48040c60300340e01d0701d000d00000c00c65a040c803c1d100003c0002d00319a0032000d040c8807029202440d280c2140a160100030800c22000001402c10340c10281e0b10101c00e03080c3c410340c807400c0304e00c04e00448000390301060029003003100b810010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 683935449 1250 683934199 683934239
    0xb010b040312032408070f0b040b0d0b010212030f0103030f0c2102070503061015210507090503030309070e06011106060f0622060e040507080601122003060909070b04 73
    0x881c400450b44c0035020704c94080368120348a990440041000304840d2101404080d14417a04050301d002d241c400d405050384180180c04440703a48071001c0c0100b0360f00034010384259810604d80760b682c0c0e203404114148001c600340422408071750714119070040c0728410340e242c0d5400c82d442008d00c407880004440308044800c0500b000411886008000700d141d880900c8175078068410480e1200c48103092200545c00c6010088000b0200040740c04800502a801015080002c10090000a51b0744036040100c0e44041035070021509484000240301c44050001041c40850300055000c05c1c541c2c9841c0011100b210703140d1481c825944c4800c0101b0200d290465965002c08001050032707107042e602e15401c90358411074282c05900941c4190301000700d1134010700210303e03080381140d040100385440200606000780240030b050401c450a15200092940c6034030038003002925007d070a012810200302c500b4181d00458078140151001c40c08605c4c00c0100007401001c0d03451070660303a400c2c241082808209507107940c0790 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 683936699 1250 683935449 683935481
    0x3111e0612090c100503090c09071e121805010b01030b0f091302030607170702060408031302040e062e0620031e07050d021204060e03010221040b010b04031203 70
    0x1054820b5544c0f070004100204103070b1200340c2c5a240154144d030510103072040642c001c002c110108000140d00c80c002c4030b0140e0071816100242d070403500c400c4800900542e0300907406890700c085091311482c0a0904100b03284140d009210350300c5070300011010b5409080710303075802c900c0c03413207901c480d03842d290815a40c40aa00c1002d4241004250000707460b21009441c3c2501207018a244000119800012180d00c2511800140582d0801d940d892180d88402085460362180d40310341d40d030031035545070445d220f418580c0c8111100e0b8200601d40044641c0348000301c8582e50444400720150b0b19642d840c04080b150030b43c40e4042c02c0700041003e09010004031601d135080340000c102c41207001210111103042c000f0400020340d100c200502c0d0140c40c0421a401a2080d5409408074001014602c01103400b550801d182c040042ca01c1280840e019014168002c011803e821034401140e14441500da485a4000c2d4484052640e070f61221903150300c2140005490502108041d060060098112034a41c50429007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 683937949 1250 683936699 683936713
    0x20d0303062d0515130306150b0c0d080c0c12030a0c0e0f012a0305030a05130f03050c030c1e0c01080c070204021b0109060e012d09140703111e061209 66
    0x184182c06080580048905555074400c0821001c1410611805000c8420409140120b00c020ad25a6050707081d00290400c0040300014840c002c1e660165010300d06c1640442e414001c0d0301c05c401307413913800490b4802c034680d1900e880d030780742d46110b03c922000c1c00704003401c0c04d06410449001125080321543e04070750002004592200b100f65400c55000c40180a91340e51510ba0030818201029100c015080054964400b9600004100d03103091204000b1f515040c5240c0c1d5070a02e0301c8107401c600032140c03103a0b80381c00303500d480c0382c0407980d4280c880c00e100a021003a2070301e8813032250041d40d0f000000c1c2d450441c116820300044005080c5135004040584009102c0000310701c500c514242911103d44088400b00d03194403841e502c042090150030181c06954000c800b1422002001f4440040d0758030015001b103171075518420a000c41d1000760b154180c18003040c1c031003c6480e4144411840d0034122468012581201c0c0c2c4d4240380104040010b0214000701805d29003003000d88216081c8101a1a241e07160080310 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 683939199 1250 683937949 683937967
    0x1050723030720150a030e0115061107050301020c0303070815060d0b090f1b030c0d1401180c0c020d05010b0303030a06090608070302010c0b090a020d0303062d0515 72
    0x5842c40d1032151100240d000c00441c100c24140051a0b481401180440e10305144104003c00f44e600581a600d00018280d005400803800b4005045201400402c1400d0106402c0c1d8403250501c0500c00000840f80136030703a40c906144c02c030702c82c012418405800901c040f80030315116411894010211001010400c00c80e0310011390580c0c0000000303c98140e9030200a8040d0924050700c95004036204100d01e8107282444040207500500b20b8503901c2c1c043c0020001301700e00c14201c250381111610f540e0170170801c4210424091840002e0045910031000102c204591103514015003c80390503955600018000c5e9500b0312a210010b15030445455480d1a25004182c804001843c492400d2000100b54140741881040031918950840301c11500310300c1041c00542d801071000c0d030610790702000c0303604159684000c2d9030400e03a4403c4001d511403540c99004041c1a0b01d600306200359148024001c2c6a02540802406507480d0104181444400d011080026180640c0451030380d100043c0701ca85480d400c9 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 683940449 1250 683939199 683939203
    0x603070c0503120c19030905030412060f0e0604150507020c060a111203070306050a0b1210030b150406051e220e160b040b0904110f1617070201050723 66
    0x11a01c84d0004d110114044090001500108801080505040086496079142c9075100d100e18000c0341c0490108480030400c100c61a40841140303e2010800c2220590140001c1c1c0c40741020360302990440b00d20b00d0300e01000301903849010b0041030700d03070003d01c80c104410050000701d030405090607081c4130300c001d09240300e87d07014442d1120354a00003104590382e1420800c00340450789203400c0f2a015080200b014441400088201c5000f440000c00d000956a1075001c10b464502c03440e0001000c441c106020300c0040900b07114551803200303007250b05201050301c0e8400d009039504000e03560702c044405d420550416041407a24440c582d400150800c0c00440701400f1401038562a101c4600142c1c4250045d100e000c081a0044024102c02003940340740c00e10b00900d154060107000c080303921881d558440741c2200f040c0c807422685940d00b403c554030f8070340c001c070082061a403039902c1d01a159160006071601402c1c0c401400c8844580e816120f0390f00300010307a1600414010784d1408050824100041d1010700042 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 683941699 1250 683940449 683940451
    0x1103060a0504210e04090507080a050703030e061228111905040f090b0a030c030308090705010306080d08222108041203090201170109290603070c050312 67
    0x510000481c0e64186482c08019400f031484044101d01d03800c50600d40100ea0008160103080400c42c0e000c599203072541030803401d00e200c65002200500c20700002d07030100480481c1105c2201c3c0681c603080c040c040b010003072200138400d460800344007689600025004094080020148103184940384642c1201641e410048864421a14420300804150b400050440c0020310b06501c0384c62624505151501d5412034110030b0b14010711401603112036100c05207450784c1b5484401150050280e0f41e0065aa0401074004c40d41920214550b000707840e40850305501078040c4030201d41d442001406403142c400800c4400300405043c0c0a03618544c0504061007070196290301c2482c50080884089920382024089040c030704d01c000840c14042c0d00303c10003000c103590039a040f44110a505003c1540740c09880106d0b0f40d5132550a400d04d182d010000040760300a4151f02152441c10004401003078002c0c0030702e143c0c0c48224183d40700c1d94040420000104024480d070038178034800348180220b80c100301c10398881807403000c4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 683942949 1250 683941699 683941711
    0x220b0a03061a1201030320100603031106041e0614070302130801050c0a0f022e110306060d0e1002031306050f0702071a0f04080f0c091012110306 64
    0x5210601071008101c50050441e034600e2640c2070510b01440f09007a6842031070140700103001d002c039080380801e241c05150900c1c0c00f034010820a0382e08901400803402d0003001640030603070000d1150240f000d994600019001d009942084a2084c1c80c1080c021005205d45404070440e03501c0d8403004426860f4000d80e40c06400703840e09031800358a0300c00c00e0101801502ca294400c2e000c80c1e04040600c00d0071001d0b41d0460300030940d189418511501840300981c540000d400040c02201307071480c0509075410585121801040c08148240102041010400c05a0009503440380c0d01c260100245d800c18801540602e020949484c1520007800104071132604a80040750a1015030740c21115500811201e8442c1643c07098461020740e0082c28000742c000d54640b070314018407140602d07460640c0341c00c400700410380750540700341c445035a9610b0701d89401c03640340e84000c00104410b11403907032141c0c3c0c103140c03040070b4a2140f0320000003900540d1512a040d6448202c202c401c0d640c40a480d03a02c11100e450521074a88100703 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 683944199 1250 683942949 683942951
    0x60112061107120c06090f050d1214060d0f02091806060603010e04121125090e030f0d09060911010807030b0609010c110a0e0109150b220b0a03 63
    0x804905041080d604030214110380d40c1c81c10000100002e0030310303201098840703031480d0600d00c4650515004000300f10140c80a89500c4120b82d80404010340000c03804040303503c9a0302d0f010a801d000013280b090782d42105540e50348803400800180d41c4c0c20008440412070b801140e02a03902c0645401142c000343c425130f502c800200c200c1c1c5441c4142482000007a07080301081c0e07552882d45d89085a400d82403400540000c0c42c2103181240e220110744260820b5008e0312800041d0380140d010051007a180c48242c25414070059600c11000403c45610701c2286000304464025510f072451138058500c85610180b141c240040c1d84034540400700b4280e1180c20a0540b0402c50110b039501c0090000d0040a4001c000c60200b6050000071289500c4000585420754028202280c1050013840d01b241440b42d00b82e00e06401c400c500b280000c03800c00c07986000c1d04a902c841c50030070100ea00c2c40b1b0300849401241c05110600582000030300010000c04818240314030740c014500703440c6501c400c0c403455140d00c1500200002 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 683945449 1250 683944199 683944229
    0x60c020307090e07031b05100806031c021e070308040b07140703080408011803140a05071514130206180d1208060118050306010b0a021207210f0e090c07050601 70
    0x212400070341820186d5402c140c12040c50600080c3c030a280c140c40100420040202280140e2410400901419000003d00d0702d040c03015500203503643c054000c940d181c200501700a0b034920310007107000d00580b5044503280d4031385800c094001055a03c95482102c69000000202403030380c0c2c040c000c0c01c0c055031246072041da480b4540594a402e6820644151036040d070f4a034000800a60410000e4188454440b036541d19405424000d4415008003080036001d20042c2030500c0c842180381d44001c1052450601c54005512220004061485044c078002d4000d10208441d00382c2d813041c0c0140000e142001009808480d0700e07031b5501401030001080f52400302e008002880110b680003112754103031040c00c0e5540c0d6240762a20001a950385018032400c1c018103800120541414424041c800c0350340286c250b00e6540f0303422450301071444003034408541034080604141184003449101d40010030112941c0340312452406404101c0d80800181c51401c00710020000e450001e58248001030080c441007400280ca = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 683946699 1250 683945449 683945453
    0x160321050c0418180201030c0e090f0108061e0708180f060108011a1516021c060b0103020903030d0c020705030a150c0e0303030109020702060405090c031915060c020307090e0703 78
    0x5101da04152642c294106180c00d540c3d00701c00310a003440c44c1c0c0c091802050800c210b0a05489000c049545e05401401c481c0c20000f08410464506040b15032120881c1c132030350f491a4040b0f81400821080e20090444200495121807041410076000440003a54800c1d01c400500b005182015100c1808183d0304880010403907040b081c4280014240300e41d010001d240c0700b2030001030300b0000c0e040000030805800b08419a0f18284904c500118950151803a0785000320f90500c00d80c1103603c0b0000719040b60525814141a5200707001361515020040c00035810801960f84050143c11500191400c502c5030240004103550104880d4200d180980e10f1002280d1414420000342c5480b80200d90030310030b90410403403960b100042101d0455241f88001a2141110702c0002c400b071107103a008640c403014074024840041030000003103010303071442c0710707200d044100b104c50b44016200c050b070017006c04400c02402044014003808031220040c1c0700805403001d083d202c8201e08100c5070030070076090055210031801d00c1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 683947949 1250 683946699 683946719
    0x40b030420040b0609041a03010e100c03021c020c010e030a090618030201090b031909030518040e07050f010309150b01141206010c0f0203070b0d060b160321050c04 72
    0x1180780162414402c2d00360ba0000304903288218a0f0007801580d0341e5074144290541112440c0304040020001d01010f185215a81c2e618040c0880c5c0c1c813011454081001066400f0703100303c5000030b44c031215601f0354841c1c080402d0f0003504003003239203050b035529060003401d40b4009000604c6030090907142c1940e0395007442c1d8000c1010340c01441d11703950382605080900150380c101d9412800c4030000b08525a680e0b8030b10601400c15540154541c4085040c103030300c0800c040c0c004000d007110840305807010104403071100401099407000c40012030203411181d8140900d0421644200f6940010304010802401c01e544940c1d03044902d032041320b45103075100910b1841f90f0340240300f40210710010440c1400c203100d02880201007070003d07042c50b040c001a044d0f408200501c0400344072003650010b042c1e91003156120703d0400b056110403240c02000740f038070070040b03641183c1e0000d640128402d285000c00f02181550156940900203210105230030020301032410920850298921940c07600814588407407030952581 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 683949199 1250 683947949 683948003
    0x3071209150c02060906130b0408060703111617090901090902030c2205061309031706030d0813020a0509040309180e060609041502121006030603081e040b0304 70
    0x6820040e100d50004090f80c4c45a059035500017044541c0d581d9004480f10a60600b031180d031020550110219000401e0440840d40910800007500d05008240c408040502e040c411441030309126400d0805000108000036000420441d20000e241e1a000c001c0000402c8080c0981c0500740749503ca491100071402c0c2808080b40b246002e85949044660000300030f0100e00d0601080c2c81c8150b541e4000550690b286100c107102a505141c040181d0b4459090061010350b420300302d40c00d0380500c0000300b03005040000382003041e4100d0b940c9510312510380740b1040d03912400d8a44203aa0007a815280070401da80e0b02e86070035008911a4551000407450301001410313540181150000d02c5d40f400801c0d80c0380b0400400c8140c0d00040445d034440c15540c0d285005012100741c2c000e001c51061021510440c18449004001d008884449a0103044c070b41c0c55104500703882d960301004040d00c4003409469080b0f10020221404007100300080e0b41031079200c1d041500300d80c204541c161240c200101030051000c41d400c2d02c0d0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 683950449 1250 683949199 683949239
    0xf0d060602060f0c0702010507080d0b09010b03060a06050903071502070306050c090d02010305040501090602160314040f0b13050907210e060705130e040b010501080f060109050d030203071209 84
    0xd40158a4070039503c0b0b01002000303128500c20703640011040216881203003222a01c2d0f501c001e60940b241c0745500440024022080c0c10750040007020300100d1441c0c40c03801a203200e1440102180350342418160200c074242c0100c200d080d05445503403000701c2c205203c0c0f00800c00da44c3d00d07940100141803031400c110055a1019003600c1500d14104179042c80c680390b16560381040c640a007170101d02e60f00c0305c1c0b4040e401030500b11005402d41c0d2000c201c010342217292004044086009a50b141c0c1d1034008c0d0f084004107441284214142207416a6003000105c421201400c2040d0311074052001c155034480c0499018001110000001401234400c0e01c03050b250130310241c205484d500d80410000191409255171002c0c0546002e051084c0483d002d1b603316001c00d64000942041007689070142070078a003184070036400f0b00506022503025000251b21075010f001091280701c05a490001c02850441800780300329450700e069045010030040701d4041405684001d0b4550141d41d15424410718003410401410014150 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 683951699 1250 683950449 683950453
    0xb12150a09080409050c13080303070909140403030e120c010f0501061b1502161101110a0b0c1b0d0c050f0307080315040204170d030b0a21060b060f0d060602 69
    0xd0080072641902c00e54003902c80384c0400042c180c9a4824a03151400790103404055203254500c04142000c0100185001d10b483d9124246260b4030b46c4542c4003900c6910a6403d4101105800a00824865000000040d800070285c45008a90035000d500301e52060002d0413040e0344442d50a074609559104542c0105a40d240490003450b071075486040341d524a07640030307118541c55207a5103104801c1d0740c1112040d060309100d01a82400c1ca15000305501007144466020a0307100445141081c1c02007880304c4019071089802c0520b9440d0030840085412000301c3c802d1414900c12080c5404100f0030008110194030344900c0a401070505e0020b00c1c03e2240f00c0740301c005c1e030020f001410000e401c1c14103036500514000c5a1050103800f41d00400d0003409103901c407400c2da1010302000543c11401203000030580c000f42d60309101059440307003807280030181885064654001012400940340d101c5c0405000c41c1d00c20b410101c0d980007040005495904400c094401e5a131000514500310319080c46045c1c001e04171400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 683952949 1250 683951699 683951711
    0x51216050f01020616050f0703090f060305010312111005040f05120c0d0509120102030f01091803052703070602030909160509011809060e15030f030f0903010b12150a 73
    0x4d440300c801806000b80f40048400201341d15004900790361584106002d115100c541e01d04000385100c150b03114604200b6101c0e2408141c06110740503003416207800101c4186508000e00b812542400b46d50107501090160040955804100780944ca02a5000b02c40d41c6001090034105281041d500303c81c0d5240c405810050340408440c041803407014a078503402c0c00c0751201044000301e00341641c55003c0740419407000040101d00d000c1c0b40d0156068540e0904200100d07001c020702c4c1c501c580100b000c00780c0842e1080c800e054007030103402e904911859141a400c00780e00d2040006c28900801500702802603000885d96215030305144400e598080b08110561460541110019140f4803581c81c1490401508400203900b42050119110003030120714001c2004036911818400d14110030f0356a07804e000803000001da114900001d0303c420070340540c030142d8030b445000340e440310040d8030004085802d95254520010690f039078180d11020400b100024040d001c00c0c03031a058800c507000030803e0548515044c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 683954199 1250 683952949 683952979
    0x4140c09070f1805040510060f050a02030f0f0702130203071404030b2a0a1d01030c0206061309050303040f03020d170601030c030e010c022a060d0c050405121605 71
    0x10700c100b0510511424291002d540ca01040d0307140200b2030700659005801e043c00c1c01035455401c01c0f010111400c540d110342544912500403900b41c82082080001603005016210340550500e00822900d85000b1555103030862680c045141d41c01901d880006050340841080500f681050200320400c1040c200c032442c0c40c0c110b5407050b0504c45d010b8075060000d85150040d03036646442400740c070302d00b21001e92000d44984e6207000007056a40d500510965000721070070304a407994060700a480042740e0f15005420782d07585040901246c034041d2b04501900a48416080c00892028001140074034014031040362055420f041c041e181a13058a03000c0100a802a04c801c808003681d00327070a410101c01d280201d9412102c20f0102c0c0901000c03802d0044035464111f03004945500021040e0f01e40c90a03030501d516401040d02c030481c080c840e0500a50304140e08200144000c2423584c0045402c600070305002d030816840320086611005409180703116a40b061541c850300d9060b0503070b5400200f1080300d0030406040d4039 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 683955449 1250 683954199 683954207
    0x1707080d02160c091e06080319030f0f090b10080304090908120906091b03190c0b310302100e010306030209091005010909050c2704140c0907 62
    0x8000420a0541e0100d403612500e440c9003416400365401c0201e480a254554107828014010401c0200405040c40407143e8241024041c15049841da10051401c0c1590300c041101010b070a00c00e88801c16541da42020f4000709680304400c0b24045001d400078000000b86030004010b50701070b121910050035400101301a807000401c840c103440c2c0c02e500200d030004162825001c1405501c820b0340e8800943c1040044030308000a1003849030303040304201c840701580c0d400a586950902c07048203801d43c00107544400010310700c000030618240310350001c00314655102c081400941090310380500034007001c500e0080030f6240d25000d03d07140000001d0008054516400201140c0700b548001091014041507807107280e02a80c400801150082c02c118003501d00711580382e456200c42d8041800c154a07080000c1090071b0b41e032082c8030b51954444010059800c56404010804540c0580701d5007905910721030900c1194000b0382c1501491240c6080513650040310803407401d002c0906581406042d07030004000100e540 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 683956699 1250 683955449 683955457
    0x70b0a140f0a1812060f0f0c0206010b09060c03031302030d03050606090f041407020309010f2102032206140105030d08180a021503070324060f0e180103170708 70
    0x341c2403809100c3d1040c00c00c42c0301500d00b540140a69502e0b00c0303031102800080d400501391a400c064040002205118500d001c40703043c41d502030016404500107200d0144614018500084c0c02444141031051040c035003451030f40f0440c0c4802e4840712412032481141020064a80001c0490805000d44d14100300401c03094050b480000744240b02002c0ca103007640d19994001031141e80000e02d0b5184910749000c02969030780c070002140380000d00220b1101c88841c45040c003100961007140480d141d031b401800000c40a9000a018a06444050800f0b2120ba02c02440740484e51407081c40042484d6116200900718804140e1000f8080d070440c0351480740c9180d00c03000803a0b0200005002ca11000030405031a490000141c500035000f140c8440210307401d030191000355103c2c51440d40c2c14030294008640304d50012005501032041d54100301e100f0b102c040d0042c515400c4030019880e103011803540c6140012110028106040200182c420044c400c0c050703c42d0380c2d1100e42d01480000b500d00440d0f50f8034002d0503c1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 683957949 1250 683956699 683956717
    0x52d010e0c07030302070204050f1005060c1911100e03070902032811130f060c05030f22060c170405030309040b061605070810090f030e0d05070b0a140f 67
    0x240000b014000c05000e903056510b15900900200709a1401ca0340c58009038000384c48030700340350404000000b00c1d0703c0c0000c200d03035034420154098400340e41140007900601030040811188800c41c1c403410502c84c0c56900343e01102e0300f11355403811349050901d000d050519070700c0c0e008400f220b4010810400d1052001070340b104818101e0380441c00010385812120f000300505092013100b503000041c075014013001c0b81b000409446c2054a200e0304559102c0055540621185004060780c00c140006c410410b5900c019200700d08034105612000d01140c441100c0890045c1c02c07c0300801c0c03000204000b070083e40c0c5964079a450f034001c40c807440c00b8200030001c1e07982c1c0035164880b849140c4a1940300c00d151108070588a1070b202c4514007143c9100140b420303640342d6050780503019551060344203001c042002c41c00303202a1a03402104189002400307850482c0c82c028010101c6d50480c1c40c0410a00015904003c540d008101d4010391a8075103031140001401039241e0301754044004418010214240d0b005800c85070100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 683959199 1250 683957949 683957971
    0xa030c030f26040f0506010621020301030f021c0c030f032601090c051c020a17010302060313060b090702100c051216021c030506040c0813080a030e01052d010e 70
    0xd62030f440c01011100013000300412a0165000000311590400e6441c00b50120b140c40c09150a01084d204008a000903c0003900343d0004100800160800130500795003030800610381c0d1000651502c5424486c103441d40704580400c025044001890b5000350002c09040e125138149012031014502501103c0043c01441902a541c44051084900030412520007401c00700001012003042e00c82d50b80290040003602d804101c4000c00318550800003d03005044e03e60041170142142c0703801c4401c074002020130004443c810703901c0414102c0383e50351004543c4654150f074018410780d03201004000c107075080c6410800611000340019400c85e8030001c2c00942c0103030291003100c01c4120580d012032400c1d00320481058140841080410881d50680200784102001d032000e00c484010004219821001154100040008920484000b804d1000104006200741c43c0120b03981e9000715070542107401c1580c45480c0c0d031031312002c00359a124a030110740303902d20710900e448209503144c10900048070000519841ca09 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 683960449 1250 683959199 683959201
    0xe01030f050f01171e1507050307021b06090613030c120f0602131a0d05070903050d0305060103021e030a0506091006080402010c0b010e15040216020103110c0a030c030f26 75
    0x55108100464801104c16209100c5d1140d0f48803003511002c501c0040004181c110f800528268010000c1b01c1c007461a0340d00805010300e45011818001454410351688108200004801651244050540e8000000140320305901d1490090000c4100d5402500380100384040c503404101d26080c03610540d81c00541c05a0b948046151801502c2c185400030701c4d400c10004500314140c40428040c107400300d07440504100039204c40380d0070347d00e0380a5031100902c00d601603440c10a4051183e00141e0300544181409030400c1c0c50b6404a50f400032081c002c5802c001400300400c041c094003405101d81240c030556401c030b5182048d05202400c12514024070b0103121010b0081411648520300c00195642c02c032413500590350b115464014080c106030303138041c0c1280c1045101481c603e801e100b1604c2e141c0c0714a2044030000300703681c0190050b268020120112800c10301840808641c203100046401c3c0c82aa00d400c041030552601510715074481d580d210400448944407992075010b08c2410b80c00c222005072090b06 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 683961699 1250 683960449 683960489
    0x8030a0806040f02041e090b1c0c05060d09020f06030c090910030b040b0601030510061e030204090f05071b020d150b030d110f0f070608090a0807030e01030f050f01 72
    0x260150b0500b0000c09480010001106c1e003490381900081180c15206240b19581d0780041010384280d40c283c1c6601807440b00142c00202481c400420f20349100b00c03851001d40d99190000341c0c0300c0d0060f011400c141501d9000e800d08601c0c01070061302c501c3d60102c8031a402c504105d074002c000341c0249180c00d030141c01c0c190007041c2d2951040d4a250029a0300c0b06400b8050302d01450003929140e0182c0d0514042420701d0085603062044030509820345200350796101d606010f01d030301468608006413405041c16801c01000c54000f580b4001c04040c84015003002c505404d1424005145e0081c01001240c80d846030b00c0010010f03a0780f552084000781e000610f04980201c0d07035641e0340080220300741155046c4a0400c00c02d0760705401044190341904030707406907581c0001001e00c590b1600046c0b10820380d5504080d0303003072040c0c83c040e030a8a9003009212003161403031065580c608203a50b0150b1000e1b0041207203041c010f441582e05008100c2141c40c4501c00b0300031420441810000200d040c010038a0202203d094088 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 683962949 1250 683961699 683961701
    0x90305041220040203090a0204020a09170a11011110022a0c090c0f04032907090806071b02040f020c01060e09011104120b06040f0e030c0d0908030a080604 68
    0x8040c2603051030840c84540d103850702d004801a180103400e9a260390805800440c60140700b80e034400d03a9500080d200204440e803c00c8000e40c0a0300b9020144420405c01140d11142c8841841c07000e443c0c40c0c0103121618160501d86100b02d00f000da4941001104078889101d51f1001c0380c15441c0302840e403405600d4048010004140d28421050b10841a003c5240c0e5444110b0001d00042e16110a4440d26410f03150101c0000140c0300700c1304611313081e0504000070030000b01014203036165000541c02284030204819001c1e0030300c010540d140b40008821a1042c00080c0060040c0303900b00740c25082248a0800496035000138180900c00a4480d41e9a81c848910b1031440c0c1c1c0441d0003a01c4000e000b0401d49440d550a240540c1c01a5984401d40d8030f04030820901c1e01046084506481c10b01240e00082c4e1403a907281106c0000c000d12050300607031500484550000300f405089540340704e000c095074507100403c07160392400c070307403e11100e00b00040f0890401480c1ea0200031140c0030b040310728103054036079a240c020070 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 683964199 1250 683962949 683962957
    0x50d020d0b0a140a1b05040f14040209030f10050709060f0503060d140a170f0412060905010216050c0103150512010b0a030f02010908030a02070e070e031501050111120409090305 78
    0x1951103000c3c00104608404164400d0300407180c0700c0a03d10900000100403141c1c0e000b540902c040d00c0c2146131050010022410044c034a40b500140003501c0c012078003022908140102c0c014a2095008014500c070b00c030b84c14007030340d0390005145c0342240310700746001e200600210000390b50200340b06001020404a44031107c800b000c1c183c1040c0050b040032603200c0c0503076913400b2440007901c0c0e046040d0601d007036042c1c107201100c40828094528038180f03401d0100b200c0b03200c241601c04903081c41e40ca601c8140016002e00107018003c52044440c1500320040c144181400e01c290042410540f034481c9100b254034503c101c1c2c00540360b003038030325041d421200040940100080d04070f40c0d512420980d0000200582005100c1d00705100384d84004100d41d4070740107141d0b2409801c40c4140960001d0009110320120b041500354000c8041c03510040107040c1c940421b00f81904501341c2c3c0321406680c001441156082110240388001100040001c440805c42c9103050703010381d004826140f6120348005040c14401c1d0192 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 683965449 1250 683964199 683964221
    0x6040c020a050a0b1b03010b09060a02070314160b030709150c0c030b060f10090519120c0303031803170402031f020409110403080a03240b030f01050d020d0b0a 70
    0xb2901003e20303043c0001c3c00c490403140103c0314156192030701d5003e40320b4000d0b28102d401c83c410321800c2c0540c0c070007000220340042c6a1502188680c0a0020200b46190384071041d0400c003c0140c120000c8a10340e0144a207010f0300048650513080051280e65075004421100700d0310302104421004405400446c0c02c05030300c09018003003500c80a03010040c424522181c40c09503000300c54142c0d8281000c0140285100e40308000340214201c10410080b80c288812301d0b102446112401c20512900d400c3c00007220003c1c841c0a46602603189018010990144203d888020409001c0c0310b000c81540c2c0c0040154080482d0000007100c10741c003107001c649082115104020940d9443c420031401072034102c000b03401038031408050340d0802d120b801d140c03000c10003118141c07034018100d43c1c5040f202c01c2041c1c0c0178059506400c2c040750700c56944a408080051590b41c054510440070315580d0906000c20b00d111030040e0072245c4a0810f81b01c114005070385968000c0c05a65000c000c50025035500040c0400500c846516 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 683966699 1250 683965449 683965453
    0x1b0c020d02090c0c0d03020d0b090402090a0f1d0c0310020f0a05070206190206220305180f040c0c020108060609010e120703050604030504033c02030307020d06021c0b0906040c020a05 80
    0x403005c1c80c0e60990040e0600c0d00d40048100700700c0201c14100045020240c5020f5040810140801d141c0001c2d074100302082642c051010503060081d00c80d41003103440c212584c0000350840e8500414900e800c1c80101a01420001c041d41410300e8148130f100b03d4071401c8813040601000003000002c40d01e0700360030707101c0145a441c140c482103403e4550181d241c5c401100d0640d001044e41021580d00c201007055001c0c22505642d506e810414283c95145400806009596000500070340d4a022a507850141c050b60700c8240c0d640402400302480054058071001d08003902c40e080a10412201c0d0341d0203100c0d4035840d54100c640c544032144102e103603401c10101d41c0000c0c0c00d078000c8000300030034190800e005104885c8180008421680c00349400c0c00001991b01c0c1080812001d14010b04210f2241c60183d1f621034001029286030100300e03400501612020030707003120318a4004c01c0300c0641c02c000074000383d40015103510034480741c55100001400300f0f4004081602c11030b034a58803140300610812519101c00d0303014003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 683967949 1250 683966699 683966713
    0x6090f0c08070f120b01170406021902030711041d060709060e03010203060915120f070305010605090c040513090203010c031a04060303021f0209030d031b0c020d02090c0c 75
    0x610100500280d41105010699000126042c20f11544030b50304491500d648003900c0001d010f070034030040e0441e084a58100b00964400340d04002a4103105070199108001c010382e41d50080c42102540000302c1800070540d041070001c40b010a180001d4110fa100c0d040701c000960512134040809900b030310121914180c0f15000c200404260803141e180c055590549034070f0b13002d078001e1003050300340d100446a043d0451104c0e0040748002e541442d40b903601200c024004070f198422500f0f110301e03065100c401085203900500c000c2003444030a204410140000343d80d44442450100040549445240f01c3e281c090070311504528a9000182d0041032100d50007030080c04102e002e503100a001e0a20803004001c2c145e03481d0445400da190602c102030440394580c0141a031190000c0001c03401403400c15204688030307000c00c0000ea00f41e0b024010240d190300c490b240000c0514255030801800715003c0c02c2e500a0060115034070004d0ba83d1205003415680d411107900c01c41c0e95440c50107400ca030065080e40925849135007 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 683969199 1250 683967949 683967971
    0x31208090106140319150c0e1c030807050c07031502090103140702071a040f080601031a250e062a011a011d0303040b0d140610030b03010609 62
    0x298a250048000d8002808810b0300c5210720b01d42030b00300726030165140e44403c045500350360041c801c55507001d000c1c0c02071500014400c3e40c0042621b515081d082e0002c1c43c141749100e424030349040b1003820980203c0208007440250b0f034010b811020702403c604144500030a00c2070000004000001c040d607408040740a04010b402d9543c000703074103e102d8890129040100f00400c4c1000321241c54400d1256a005003a00c0b454500700402212070a507032081082d03420400452203510680b0600010007100f001488030b58554100786801603c0c40e0380d8031003d10b02d03079000d01c000d0003199a142d00040c0940c03004562400d0b154002501c0107824842102d0300034001280c00e540e00c45840400324048054a000920204080b420003400c880b40c080c40e9000b0080c00e1105003c240d449102031860020080007a90014140c1200107440e6400941c494028804001540303000c03a0002d004880108080074044100d50900c28000341c1d910316130704c1c048010540d84541c100d00c0c0c0e580c250020002081d140c0c2d020410711142c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 683970449 1250 683969199 683969207
    0x117090c0a0e01090e0a17090f0a1205120a090605090118090f0c02150703020c0f011b0e030f0606040e01140103080904110f04050423090129060304080901090312 71
    0x1d20601d00d00d580b400c218255086000b260a52040303a00c11000f500f00b100405404147c0d820810702190480b01140359a90213803107059010007d0b0084a010f4034000c1c1007441d0061621642d030564459a44061180c01340540d0441c101c5410303900141070094070354010b800102e80c00b02a81d40d5900010400d0072002614056907070040040f0350100b02e0503c601d125801d0140d90358014100702409070800f0700c00085c6018440c0c0d015190001d07c1100b40c3c0d03400980b0311145c900f50f8000b1400d25001c0b00e48007042d80301d840e411101c3d480310702c0c02c294054481c03048040c141c0703a00c480c802018a402584c61f80c41603002507d007944410320820120a01d01420751b1a03040441158004e510658042d40c584040820242c28240589030091016080e25103000c3c20901403201400110300036035585003140100800000b000400c5910801d8810f0000071103c0d10b01d1000030f841a011000c00250b51880341141050351078800032294401c1e008182c0659507100d100040b01d0180469201a0036403000d41c0b402a4010f40c4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 683971699 1250 683970449 683970451
    0x9020310150f030c05061810210606051b01020903010e030702031005101203120203041b06050a0f08040f1a010906091a0f01181d01140117090c0a0e 65
    0x1410714020111901c07880da002d00c0ca40c81d40401381c441090413608010600d083d0b0000c160f0840240d15401120720f41201050ba02403044c0c24007008030700010032900041038135071450300c00f1040c4101c00303008280c0342000282041c420b02c410341d445034010052201d800c1100350100c0c0c0310706402070001c1240500031507107039440f900705d44000c0380b082c01260100c000345900350060f10300800d0910388031440d1071724003000c012031145901421401d0142c05402840d00012900c0618810303405004414074200780701c009070790500010342054091050600094074000c0d40401d032000f8600705410306542170340711410042e62404a006000300011046c48101e070038100086050b60407035000303060500100751951682c8040e501d040b0007400120859640d460024034002501c8100b089040c18040d007481c008400441d140f901e40d8008807080741198ac00741200001c01c0c140d917030040c03a0f9440c5a103100700c0c07200e000802c4000400701d400e041900d450007040030310f141031046001c1404000e01c0955103e41e54091000b004030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 683972949 1250 683971699 683971721
    0x12050a0e16080f150106050a020f0304060503041b0b03010603021b030703020f06010906141315061d012a1401140105010908060910020309010209061c0507090e0c03060409020310 78
    0xd8010555480c10000030b08502c0004d4501c01050036a0034414202da940e040310205800314460701e211050310b03c80620040000d41103658401342d0360300d05410b16034041300d40000c46030003143c07064004006003d0f81109403419510703a4600542c0c1c607039981e459103c000e0302820101416000001702c04040540000b010141c0c285902c0c00c0e01c1050b039031000340c0c03411903445114512400c8103848aa01041c0742074401e6019000e070303050000620943d0a002d6044c0c03000c1980002000c6000c020780d83c008002c2156000490306401d183c410070f40ca541858000410488461180350318108070342000400144c041c040c02030700419802005040700300c1150060700e107420b1040d5804500403070008581d46401140d0103110b00b401b2070003080a00c550b40c1b0301c00029800104641c119540c00e00003644550f98810040c48805410a00318000c0211f50360841d0440f035004c0d000c5001e12006000420800805540c0164403600070030405490b50707201ea0120340500203c1070003e5040c0541100042800c580380d00840e2003039 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 683974199 1250 683972949 683972953
    0x16031e050f0906040c03080d020d0c0e030f03090109030f03051603030f0b100c030e19090f0606032013090908031501180509060d120f030507020a0312050a0e1608 71
    0xd2180b481550f1181c20540b000307030054560010074004034407000001c2c8500094428010718002d01e030168282110703516800000020701c0e005060415240402004144040901c003852900700c0c0c00c00042c4c600c0895220061071128031800520078140201c080d180019441a030220080780744d490020700900e0f100c100344190526041064180e0b017421150030a220300c254403100c1c00d48131a504c040c0c941483c0410702d250b1040c10103040c003910000d002c1c0e004e0020320b100302d4041407034403507a03442c00c00b82c0f500c0b03810003130030146411140b002e90740b1103540514030744607020038495803011036840044070a2080c1d00300d01c080c075003884c1015003000007880040d0300c04c680011510840303604030001158550300c00152054106000d003014080d070300e4034407005500090020602103805038299101100c0444a411410104501000e401c0503550180141c0307074401400c0c0f0282c00b50b4a82d40e035020740500c80400c8105999642d41e00003d1507420503a001c2e18a000c10001162512000b03581e80c941034803841c0c010705803e4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 683975449 1250 683974199 683974201
    0x12070c03090b0703080a09140f0109020f040c02031b120406050409230a1503050d080402180907060509211f0b06070809150304111203070b16031e050f 66
    0x1140b05425100c1813a8541d0310015a92503081d0004083d00c515841903070006603845441a030203004000351442104003800200d00c151803030040003194044100d00c9030060b41481140b4109543c04021a03000c06104444200751540e1a04002c4c506103042c9000010000005004204503422034081c10855107119014418000340a070b504241080708010081301840300804140d0103a030680000ca2150121030010141699a0321968501441040c500c2d01044c1032009100560820502d110100121300001c2c13403282c18041112995002c1912a410030484085007246643e503c81e0941000c0380d601d04201c080010402d0622a15400c00101510400010354011705140e140c9014190b90b40c04010000750070303e1801d880d4203805500960289602a0000001105036a0800051030196014000300c000c444050303010711103488812a41501d043e8070511030100080c0400404a038491907051104280c0d001c8503000380e000c1c01003180c2480114429800a22112500341d00c42d51149001c2d80040d591 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 683976699 1250 683975449 683975459
    0xe010b2808061e030d030e0a0602040e0f1e040602181908010c0e0303040504020f040e010f051305042f041e0b01030b0112091b060201020a0e0a051809010212070c0309 73
    0xf03503030000302202d41c258210208500c40d0500950004901c50071307410a40741030340c000c3c1d600c500c101d901c1a0020a10042b00100b0b02103551640181c19511240000207426404091250f034101802e0003000208840c0d00001d1440d22000345160005421401518445d038400010890f0041720786603028840c071070361900401281300c80c810300310514011405009145454102000c1c00003a42c09011003210251080000040005030014401d000b0071115113006c0000c0d007803004105000d0107144c0190721050500c018440822014000c2040e0346030203400c02002007101e081d400307503002c00120600e98441d01d4101d120401e0141610704d080c0001010784108103035260240154200c40c026070659000610325440400c0603c0c145e844465114002e1070342c0303006080b8081382d140b944407241c0c001d000140d4021030780b805203e4101c0c20881c000c440c100e0300d041e10301e410301c004280083c0e007020000c81d800319040c020078a0200c08ed030407643c6c1d100704148000d0684c980a000500150080d080440c0002c0300c801c00064 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 683977949 1250 683976699 683976739
    0x30e0315060607060e0c220b030c0a0b03090f010f0608010e0d0c140a061d060f010302060d09020103020c1b0112020307080a0507050d092a0e010b280806 67
    0x403084000915081c201043d54482030010f000f9112060b000c0c1c400e480c1c81485039a681240c101c40250001000007503410312054203001e40b22100b00c014000c2d070210010031000c1d503d0785a6882621080c03580c40e0b071a03070b8400c00d6040c03408006010050031940303002d0414041340046d03080141034070720550090050074080c01c60641d80b2103194214100040b91a003d500005803d10602c0c141001d041d0304460846509480700c004650840629044141840c40c1e94001103400703010303060340800c40b02c681f041d1030344c5550045013042c4103041a8010442d5200581011a802039050b43c05100e01a4111100041c0000300191401e84034038229000c20a807400c8209000b116001301c0b4410f21060380d03002c54940360881c4400c00382c100a0221030074414103104032001700259116000c5401d001d8501102510b052448083c00841c4e042c41020032031308035540c02c2c0402c0030301004050450f4052403420399501d901f50304240003034401c40f0000807241032400c00e5200302c03580109064050f07241203a410000d8007414030030036 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 683979199 1250 683977949 683977951
    0x309080f030f0d091a100303032702040c0212030406060518040c094101050a03020105120c04030209040503070210170628060309140106050d0605130807030e0315 71
    0x40640208001d80070081005400162070035210b0401003030100c5c901100c60160100444e88030051a0b2120400c000f0b0582c1400741c26215074407940d0044c200355920070310310700b07016409a0281c09551101c80d82c0c14041c0c03007000035407200590285820303120305062901c00007401052280b24800d8100e10351001100405891550089030f1200e4004031861524585902901c59460710450161041d50104241070b480c00c035591491084c900003c0d0822000100000c014006800090064529030420700042c1d03041800c5886511100d10034090968411781198058071807604001d40000040c0c0c103110030010004080c0101900c200c2e420100b1201854084442c21031160504501544c03802c0840d541e4184090600d0303116040d42d64001441c00603500c0c02050707052961001000944d00da00200c00c0c8500031244102c101d540d00028132107a0f05c2d0000007034a030000500c015100580c3e07003020811f00101d15428020840c2d00000650700c581036030a0140c4017a1141000074028040d1080d141042031210342c4007 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 683980449 1250 683979199 683979217
    0x12060e06150603180709051602250b031009020412120c0f0f11060c0705090610020d081009050a0b09090c061b160e04030f020601080a080706020706090309080f03 71
    0x407506564400950031211325581022000030700038840086404806401203500c6026008100100e80c0741c112070007841c20b10b004401007200d0707030340d0b080391543c2c07200e80c112041c101c4e001c1d180ca468903502c0f429401100e20040394000642d41c1d01c00500000c10010004181322158018001c2142d030710120076043d5500302900e1401000c1041c50f661402c0051031160000007100d000b2000128034075001e101040d07559015021103011a4440742040180d40750405002e07a201100381c401d0103101c450707900060340d40e0f03912070495418082080d00050b880050f10024800410074144140000d0034a015480000c10305800454018168070b40010588100000d003407950200150a07245021404908825034984d01d80046805008411241081000cfc840492000e0b10200c0d00384a0142007034500900789404148582055421507001084644400b28000b10815003000100d5601c490b0351070400024030072135500a02a601d001c0d40f40041c554440c9940050703079260f00888001d01400c2c4280c1e0741d24040c1d40c5034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 683981699 1250 683980449 683980459
    0x60905031507020114100f0506090f0d170a0906030605040b030714040f02070b1503070e15010c060c0206060114040f05120109020a0618050a082512060e0615 69
    0x8141c0054401456070380e01602c80d10000962003002ca0b07010101a006071008500500002428071000c0c0040c6441c40c010304040302c09529200b425408101c90801c00442140f040030040c1881d818004032400020000400030780040c1da0f1038074544050240d0000780144070000b442c0c40008240c0b41400d200d20b01031752100600905003a85004140480452440d002d160856220600c1d0141c02200d80003515050380310380d00304121460b1200c1c03032104469034005c6541c401c0d804000104000070050a0068008481155100700120804010380b60758030005002891b95142002c4601c0b4140e021904034000d42e0241e03500122001140c00010881c081e0f8014004280e940840c10003852800b00800b40588600c00b0011030600c0702d6070000768028145601a2004c50b21040c2041403140c0c00100c02c00140c803003160742c104e0b024108800b040e503032103086148100552441c801003031442c1084103c48014510382031100c0302d00a01d890400003603d0b80d181a5007040c456040820420303a00c0e01c080100036503001e80 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 683982949 1250 683981699 683981713
    0x821010f0e0f0a02160305190903020901092406080603060a0c14031914180601030c0302010c03111f0609050c190306210b1014011d060a090f06090503 66
    0xc0c0000b002c1405860120140d908101c80d00f005c9108648820755280a9150340c0e440700c81d51402d61403064003004039001049180081400180ea0302400c603415500661000514884074480c24034050510790003e158028031036070001151988400254840c2405609856581d1035078058801919010b09503100400d400724507509085040030301950344801e50340c00d07440d590400209403500315202c006c031a0401c0500c4d4010014151410780761000380000c054000c00b403941c519109c0c003d4084442c00028100300c2e00d59141010300d0300c00c4480d03400d00243c0310207981d04550100c41080540d5001c44240c0c0059007001c00c00035035200d040c41600d01c5402c0091455140150004c04105010201c2480300c050555880b40031928410a9401e020b200300185040740442e4940d00300900740820007044c1011740040104107210f0440141108070001c41e0a00780000340e4801c07011400910440305040350b80010011038042400c2c1ea114511204071061080f924070b240313890720811603482c80107020f200c0d0568400c0b0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 683984199 1250 683982949 683982961
    0x11070b01150f0207060318020d03110d1b1e06060b0301150e0a0b0903030705060f062d060c120d02030f0105011403041b080f0106050109080a030801150c0821010f0e 72
    0x600a54007040c2c1100914001f1900c0e50f0000c2d4030881e011300c1c15000510340134803401c1410401c001c3e8412000d401c0c01c0c0b41c0710200710002c5000120950040081290230f20010f004000c3d0254601d000e01c559110b0005d202594640080300080d03003003403180070741c202c4041e071002080d1400350789207000c64034000e80743c026440e091140040d1076501580000e034142c4010044070000c078800b444411b0107442400400ca05034100340c420001144402000c00b400f1011588000a0480100d880220905001d450150310f4944003400c0134180a10a0a50446c00344000b5403100e2500359a0f005602c203081115601030680d817104011140c4180115296095100c01c1020401041d10b81d8901d40300c14602c11114803200d41c45d0b9002504040340080c00200f560744640b002e1006680000d1b048015010b000014001c12901d0748000304181c0341032041102e505c0e20440d541e506207100b06000200e00b03800c5408241d842c00c01e9451344c00c0034039a65940048600ca190004550800d500e602881100c09414a41d890b54540b8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 683985449 1250 683984199 683984201
    0x9040609030c050a05010b01020606040e100f020f04030302060103021807080c09030319080a0e01050601020c040b04020c0a0c15212a02070612090305040b0a0311070b01150f02070603 80
    0x200016418044031120340ba00180701002820449442000049400c0d560500064580140034141e00c1c1320b54242203519180b030344001f07401c11440d40c1c0307480003140c9015075292401c003e10940c0795148900074002000320030b0580004626040303d209030380360300d074a1004009058070f020082d150400005c1c2c0c40b80214060401e444c010b80114040281981d140030b9035100b111040c0a10200181c1c0402c14020030442d10309010300c00e01c410b03252620000c0c00b061034402c0c0001e40f604800c0040d20303c50340c1d60b55800d00311612a6410790724000300c01c10890706110a6405c1c00c408a054a100d4070034105807040107050603d10a4403012010611206e220b540642030100150180c1903184504604001301c8944100300248103a40d20107007061074015015890034480028040c4000e001c5a80718503082021a23000244c0c0a0b04640c101d0789e40010050711a10540400c6000e8540f90003818003018000c51031070702f440340c4c0c0441c0d0380c100c5201030459071030810a180144c8a082241c0d5102015030000c9004110190103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 683986699 1250 683985449 683985461
    0x2309070e1b090904171c0b0d1e0f081b0d020f07050105030903090d030e0a061b02091b0301081c08040c1502032a060121150204080a140d0e090406 64
    0xc5030f4016514010b017600d240046801c591081031705a4000c1c00401e1180340c8034403c00c140050107403903100001034980c0b16480898070716075800d50103061032081181031200000c1d5043c0c040c2c3c4d201c0e000945c2d070142c544806990714940c2c280d5980300c0c052407101001c010700001c2e001d031000304000302420685240000540e8650070052154015000400400b1201d40e0340d503240c006030600c2601c0c1c20041039000d400780842e015144c0c101c00c09101c1002540b0124203842200d8041060b412568058031303175540076454010085140d4415034000f03010001003064040401c0310313021405158030000c19512054012180c445003914094440b0103101d10500010056510311507c00c0c0e050300480f80303424010724000c00d202e00140010740f15890103c0c008480d01406009203401020b032000852800d8030718080c0e40386440c0700340d8002020b140c0d41d58111480d0405c036070142d4006201d050f041d68010081d508003600c0c1c00f40d4a90f500740da43d001d61700c8182d0030307113001d40b0a1540540d80a06900080c0d952075440c0401450 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 683987949 1250 683986699 683986703
    0x408071a07121b0204090c06030605040c05090405060d0212030d050a0b10140f0708040f0b070b0f0a140c130801111605100510091803080a2309070e1b090904 69
    0x30082c0f0078000903840702e00400103101d104041a076012440e02c5001004c841d11b1750841441281405403231125140d004040e90010350007100d0000711174a0340c2d00011481c140b000c034003c0d007001e12206413409910021005d0b0468200b03c000c140015543d40300035500301c2e40c4e40c154072584803a498000f00026071051080314024001100b9003490266900900d010580202408480e00440007500744000d045082c071314401001d0700c1d034031070b820100f00c0d81e42c1402c80b030002040031400340c01e07500c00600700c41016080300016210481c883c01c42c504249103610007030f80c0000840c030b0051080c4c0f440010303010014404e03280340500d05262a07092030340009591b0b400314550381058800e44102c0e68030444141c51485154000c41c003164031315001a2815901c0d0081d1140b80040078000c030040090080403c1c1c0081d055030780315028000005010210a032074140081c039100044402c00e8800d01049012100010b42c07070240c818914208440b907441c4803050701c120b5000091080420380a00c606c800da81003114416402078 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 683989199 1250 683987949 683987987
    0x8190f0b040201020a0b090a020111031e1c061d0f07140c03090a0603090201110c010530042f060f090619020114060d05060411060f0408071a0712 64
    0x10317641c1c660307400d1044241d41c0f02100d82c00c424900400c40d87c101c0681084122200007a504080390300032064040051440d1611710386400150111446440000007010900145002c0101a480b1420400380d21416449400440418008100c07100800c0d0003da105407541c0d6280e104c07180c0d07004552074054001582504c80c52006010400903640c9014500d405403046990020b000000c2e400014040340c8504e01e51407003134028481002141e41e02008a50000c80b462203d452400c50404000b400d0072280c8052035800b240d070206010401c0540040c1c0c942c2400c3c001104030001d6001c4002107108403011a40c50343c0403500300a8143c5082914000c0c4c44541c0000300389a050031303002c503a41c00d800c1340420308060060f5520140310686c10120102540c1280b41652002000030341541d94036078030800607202600d040203039403008407140d4902d0100c03080c2038000416540c440b5500d031074240da150034600580141e0740401c2c501039803142038841902c003c1904084503016030384102e8015600104c903004902100 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 683990449 1250 683989199 683989213
    0x60c0a090f0308120c04060e010e011b210905030c040c0c050d032f12090c0a170601060203090315060d0602040b0a0f0504050d02011803120908190f0b04020102 70
    0x803215804100d009500070041269120721070201300c499901c005004004c400c80900043c410154044000c0c20074800a00b841e03000c503001480141c403554078030100d00d0415180c0544c0f080030050351504140c0d01c4044007100c01e124071000f400541301c440c80c5d40242e030b801d0752140640784c2244c5096040516000424200300109044540302c00382881d440d81c107000f0119860b04241c0c804002c2171051504520000207030284a1019003030140080d1140e0040d4075441d0780240302203400741701c003030285000010005180d1001c003070359241c044c0400b07240900903148174004e44000003449400801140c00070071004003d03000c0055005028a41c109000d001f09801550800310700d000514544010406000700885440e2104d07800361008050140b00d1440c10108641070100300b003203844042503c02003960908041c400d090b0034500d0309001c00850340c006445c02c120700000c0801c003078000ea103070416204640280d801c080d50036840d40340c0507590000f000301107403814294400468241c0c2600c640080c070500c195001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 683991699 1250 683990449 683990459
    0x4050618010b1206030607050d02030712020a09241709070801050a020d0506010f020706120b0d0b010509010b07020a03023001061712090609010507050106180605040e060c0a09 77
    0x4141401d81000310080300000c3e941c4044401c0d0750206a102030110014207040ca0203110090050041c1c48054502940100201d080c01c4c0c000c90002c510b0483d0780404540710151a0001400c1040c01e00c180300821021401500b92140d4030502d82010300030a03101d40036546030100c080d0b102060010905101c5028041303010480c000f00780115802160880c2d00540c8403000d6084803401c41d0b50181800f070502800709203540b80103401040400440c0c0383c5040088110f48402da28002030200104c00301e50141240441804201c807540c0100d06031b4006032480905680c844001c3c00b194401c040020f54026200c1d14208014500040c140b5031840c110041621103500740c84815020b201403840100140e51116414040021000a034400508005008003e041c0c2540b00c0c0d10007612840e070845001e114001146201e60340290200c8110f00c0d0310000810180341d44032070b000d84080d11404400300603401c3c08000903451a00b40100054010309402421483d00c60000000c82035011020502c2404405070b00014 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 683992805 1106 683991699 683991739
    0xb040b030c09090a170a0e0121020a050f07110312090607060c1b1410090213050a0605030102070f050d03050709031202030f040b090102070f080c040506 67
    0x80707441d05008541480341c04200500010b00d002c03210505c0d40000e41c01004410304542c4c0d4504110600c00c0115004022040380e40b101043e0b586c40c40841c0c2c2032581c002d0a140c912800d0551409801089242d4150412201540d00101c10038084105080600024800680c0d0b0740c2503c0c9080886400105140a07170b00c0007400107a516041020080d004040c0350071840441101c1111086d46454550501c0f8a190030110250162043c0d0310000305403806022011540280744a014600440d0003000030a001054505810b0721200e000403a601c003840200292401840c103410281464104145000c9000340e40d0002c06186c401002400b13548070301c480080c0c03507203c49468410b0580c003000b2480c50260742c890b80c2a07a540010b0004803002c140c4001c1c44081020780030768090540d10b400c00b0801c00d43c0d500c103255083c0c000306140101d500e015486940e000b00003d18011120540c1141a6 = true := by decide +kernel

theorem cover : BRFrame.Cov 683812949 683992805 := by
  have h0 := BRFrame.cov_init 683812949
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683812949 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 683812949 ≤ n) (h2 : n < 683992805) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
