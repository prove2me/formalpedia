-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1030
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:54:51.221557+00:00
-- url     : https://prove2.me/submissions/2796e5a0-9dc7-4526-b69f-e045147d374e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 185071942 ≤ n < 185251798 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 185073192 1250 185071942 185071969
    0x30706021501050109032a0f151d01050319060b070f050d0c170901020307120201060e101406030a1503051f02040b0a0807091a0a080c070b070e04090b15 67
    0x4424080c08001041441c12200d8803409182507085409a01d10140d07450080c0030f0704040440358403004001030708160340740048030900e89d968a4070010001c440314030706115090b02100e40000d00a00100b030000c409140c180c0c0805282c482d00150700350390ac0c44401d0240d0002c2c6820380b5490b400b286004140641400420030050b0315142402e215001950350483c06d5240c204000d41c2101c010603555031f941d008001301c0e00c00756040140c00c0c000d0451300c103009000c1d0009006003105542d0640c0451403030354007000004c0a4852001070743c0c1660200c20203010070303504002c0080708610f8403524545602c1c1c0c4c41c05140c07006903000741d010306001d0710031603441d814003808210b0b00c50711244108400c00c0f42214840641720700702c0840c6000e9003140c0f40d14404480d1b00865810009072012002c118200341c1030f0090040c0401a49030301d0b00c210759070312068620414055040302809000854002a00007480b4041003080b5401c01040004c0c903604036190a429030804985201c2440c034400b000007843d2500514442e0304 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 185074442 1250 185073192 185073197
    0x702030c0a0305030703060509090a030e060c12070c031406041e0b01030605070905090f0f06040920040609020c1e16120201051b0a060b090705040308180307060215010501 75
    0x80c00c0190504558540030054060308200e80440071440700f0340700790898801050010400701031802c1c0141501c0d2655003008040700450110341501080381802d909440c250307178a10010b06406011a10b00078401e51001804071180d2518841c04030029100c60701000b0b08054420007041185420700c3e2417030900e00784108a003804502c80003234400240c4c900c1d0f000c0e415240d210f403000c40e280e21000c1058690111603040a80e004480d9000c003c003810100c40841d115075402c400044040c0c46100070301007220792412020700b8910501c2e01203200040c00c090814900a4003420000d940c0e0798800e080c40880c0c1110610300c10740e410090b4106000214400b5040310440440c001e000d4010000101811182d410702ca1020040c3c0145103000940e801502652043e02e050003401403043d448985c8541c0306d04500500316400d9140c151110500c1c148441101d01c00e0059484151916040da12090856001031f2000ca4144022030740302c00050720188242d000500560300100444000d450341c4041d56101600315904 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 185075692 1250 185074442 185074447
    0xa0809151e0901060e041b0f0b0714120c06040506060a05090a021b01020a05041406090307150c0203060f0610090b0d090804030501020d05040b01090b010806010e010e04050708100603110322050105070302030f070203 94
    0xf042c0e40000450703950682c858a05840203e020340c03032600300389110cd006241c00c0c0002c40c440c50465401308900d4801c91094083e0341150740c404007005041400ca0007000d03006100707000082d03801d0385181d000b031803001e41d03145d1403501003082003c4050999121450f0304000442c040713410030820000065240d0885421601c1d503090244000101b135803418144140401c0f02c0c0c004442c500c016010303900701c0081540141c1a09d03024905a405c40c40000026111940624803100180c0e200e68420b030302101c1583d099041d5146040a0388800402500900300d05440c82c41d010000000010801d00c014021640400004501da16040c1030200495505901012000c2d040400d081d207542c0c0d21810340b82d44035500f400c11140071146500100c1d4220140b884003504a0300d44402c2c440b08070f8000c07040c0c0d480785804082d850f4000d40c07101400c600340c03512000d054502a1f0b051010078018900341c0e40c1c90b4030303402c01c0ba600c3e88407848650b2500ca003074410a4500d5030110754004280503050f003042c54a2036111406000a61 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 185076942 1250 185075692 185075699
    0x90302010b09190b0d1128030c06090501110606100e030601080c0f100c081602040504050a05060a0b0a170111192c01140d020a0809151e0901060e041b0f 67
    0x440c520045a040c0c1d00c100282a800d40e040e1f441c884041130509020555480d8090310303407401c400141030031701610000c80d02441000403251311400000340c29072401c0c4040c3c03101e030b202d03841030000f020030a1010758113003d00c080b04000540c400f00004c80c024610480200b030f00900030b9090008501010880324085c80b6103840d030740425600301090090860744105a103540d20360000d04079448040c07159000b0360090510050100303000c40010810b03480f602400546841e52603412000049900c0302901680000036564100800d0044010103042c140b03005001052410361502c40c144c07540d10035154048a0040c0241300044a41d0206e5030120b00350500070944d600740b4021441a140300d60444802e070400000c04081164000c1c1c03503041d40c000005400081d510f4500900000c0c1c6441030844040e02c092060f0072a907111800b011489a0142840003402400e421520341204030000009000f0b8850390b481d0750000500550100301c040c0301d14007680d1104052110300150001702032995101c0300443c3e03d03076041071 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 185078192 1250 185076942 185076953
    0xf030d1b140a1103041a0310060318080309010b1009060e060a080f060f030304060e0906090f13111c021206150103020a0e0628090e040303090302010b09190b0d 70
    0x1588a442c8a050405a04120b05540e62844c45280c1084105444641c20041129410809580100075a4081015494803204110211406a200c071020392140f6588c841c04101c0c144c00031908800028000b08c0c0d01550000410140d200c800b162b80c000842c4500104240356003c0380912240d0305c11100b0501c0c045100c90001c150f00c501810204a400454002c2856030751100f802c00700f803940c0030741030300e44450342e600001d4032081c903020111b409a01003100007816480c0030701826200702c908922203116520b50001e00c40c1d0940b01307118210b915500030b60560705181c0d5241503d894410100041001010303041c41409401c02800701c041c01d15500c01e02c2440401c44030300300a83d280b80070070302c1e0050b1982d1029004517040d000c030014480d00920000703012582d00c0040210307801549c00c030001b85540340d07036000c504079820209849400e600181d00008600024031a8100c4000d440c0a0303c000b003042440280001c803030640555000c0d01c044041008007003003a0a40c020300c00c400e001100c0c004405595900d84 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 185079442 1250 185078192 185078197
    0x51b0607060b01180602030903070b13060813061802040b0f0a0e07052a010b0a030803240405090c040501051c0204050403110613061802010e10020f030d1b14 69
    0x108042d84074201c0c1c00c0c080c3d20420688041d04182103028800d9a95140065129444980f03201e00902660402240b030601500c1128009144958030b0038810f807a0041c00c0f01c1d000e5002c6c010501c2054440910b80100b5524083e895881000c080054040c04440c8104821554030203542c1e03010f01a8624526080d955135000b0404603115142400b189540383c1d4800c490034810804c0062803124040c0b00545000c3d0342d4000500b1801d0000000c01000403d50108407000351107100090043c1c0382000082c0b20b41c0051074404401c1030b0100721640c400c001d100700250680d1022208120f00b5071105030340528929141c02030030b00615064400e841c0708030f01804000030300c80360040064021519680803808042c0314010f1841610040c8081e14000d0a02007600340c0c80c2407030340304162a2141001005e4009031030010840f000d03182c3c16100e040d0800310010600100d00303031080404d029409a100901194102400103280001e409900000c80b40142c444009015180412140030002d807902401c4481c060030f401c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 185080692 1250 185079442 185079457
    0xa0e040b0702030f04060e13052e050406060c03200c01050903100e0d1707050703110c060d060920030c0309120d020715050601050a0c050a060905030403051b06 70
    0x1401a80d400c04180e1840c1300c0d49107207103014a400100000c0c07882d0300001489007881e04948403004105c22034052420344005907254100700c1d18042c50100d07020044011050040b52a8040440d43d681c0e4038005422140d99502050106100b0324080041582c032560941103d040e0810464095408035009582c5001da508510b0502c040065840401c0d5800c04c00e00c21a000c0c4039800740320b0301c1d990103030854950a0742142403010035800790000c0c00061045108034442e41d060307620300c0d0600509440071a400511059410034070301903008070414030703183c1100404603100c00c0c1401041c52403410503400308845200d04455084421950303450110b21b04603007141e03001a95166056100c0d1500c107101c03400c04003440d240400300c0100081e00900c42c0c40b280c000d000d03032501881181002442c0c591740801658811a00c04c1e00140c003c0101e882014010301031882141d0040b070480e01700855560f40c0c0021114203500030740340380d400805e08004020042000e00d40302e50180344042409800b04011030f00e14055100f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 185081942 1250 185080692 185080703
    0x6030633030703150303050301150e060a0306030308092a060d0e01060807050108040b010504050c0c010509240f0403050a02030c0703050a020a081f1e020307030c03051005010203071b05130f0b0a0e04 87
    0x800b105452070bc00d2082340d0003008020040c5644080880f4081e00802152100301c01080c840b00004600141c046071030041513401e101d503580d29208114505103016a426245036009000f80500e810a40d030b5031243c6101100c2c44000003a0160525810a2130064035031b10440c1040700e0b0380104800074651981d8103044520039940031580d6100c04024031024004c0000c41c0d2803662900c002c00030811ba0020342a10314000d241c0c801e00300003580140c02589030320219460410200c107440480c0010348103000404e4480c150f481a2070420750700c02c280364202140e0798403d0780c00340d002034150700c1545442101134000b00003000c0200008020074202d42403282d08481d041560390742e511a0245060301080240d410500c50340f20840d520700c1c0c50303100680200120616203000914100001d0758102401e11010282d4005070025400e107007003640e40080e24541c4901040d18201d400b0310014041d00d400e174002c1c6442041000c00700750101d05e40c0c409001c0b00c9a000c0e445108130010b80c0e081148079036801c54150081d4215 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 185083192 1250 185081942 185081969
    0x17100f0e0601090803030703090204060b25030e0d05030d1a100c03090e01031401050c0f090d060605030303010314160510110c1f09080a0206030633030703150303050301 74
    0x700d0041c0d603042e00582c0500c03558003001080113030484d4145d10110003944226000c200054441c0740b01f10890041103990300c54441c94107404524000948401409203100e45800d281404441022646414107043c045034140d00100e80300e4002604c90180d11800811b505140c0c10b24180743c0c0024010265200301d079814032048144142c14035105000200203002c5020380c445180d41e43e480c20641c2d4084414000c0c0d0a94178042c0400c84003070210381240c280c111032074050303810181200c04000001054842c11101c2d00da480b00001020f4400f800514025402420b81d24804403106e55001c1c03c240650b80000010803204600340129541c261050040a81501d0040f0441e40d641044524003181c0b08002a446083c0c1448581c03444001d80031103420010955841c5203442d51a400160b0700c500a000096100c6000d1000403168181041819080500a1603034840409980059218402c0000058980000000411240d90341500030383c2020051000784440c1d07280765403402001400103000f04a008103d9 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 185084442 1250 185083192 185083201
    0xd0210020f03040f051018051201020c0105040b07020f0a0f0b0a020c100e0d14030a02070213090302030a082a220b0909010501170609131217100f0e 65
    0x2040640200d912110840c0d43d1140c5a03d401c03c102c0c140c83c450a4429946aa10500c0700d034400c80880c02190240b16513101201e04000810a80c0010040ca00c0c0207590b085c40840b404a1090046502032802202c2142082c101200d0003800c1080d00c21003107103d54402c0b40c1d1103001603130f040c201503400c0c0c0c1c01c0048404907440c0c01c0000c070042d00c5044001141803040307a0085500030703500e074004c1c007103151080c08450400e2800182500c0100113541010220701d4240700040e0005030700d03001011900e100801d40c8000d010701200e00800c4540007101600107a0010a050f01c0483d040080d007a000044109600024040ea60b151200701040c0e00144d181032001040d852036401c1c0c0300003009203a80304520b80040035600d44400202d2604a15441c1d8810300c619000000c00e540904410881343e80211202c1000703640c1c003424000d4a00f400382803c01c091100361101c4e000300d801e11142007075180107951455460700116600d07008040014103008560a02c03039004101844801e001300045551280001d600d50750b6 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 185085692 1250 185084442 185084447
    0x110616050f04080610061d0303070f020414010905040605070302030411130e03070f1214120403050f0f0c010b030607050a0806030c0a06020f101b230409020c100b0d0210 74
    0x1071036010510b1445211305111041c8811340c10b60f001d8544650701d200c2d481c1101d103200d49007210855001605034000308103000c0841c0c900e504440340d89001074000310310300900f800c0c41a0b03031180903070020302616518400c0c881004061f000ba50740200045c601942142066100d001c5007512903a142ca1080043da82c40c225404120b40045a030040391a081d00d0312506982080048508001c074112078036684c4401004c4190302603255118201c1d081ea51150a14610042101c2100380c05041503082c440248641c052801c82d1400038840000c3ea081000d865609401400e803c5d5034241da500e51103904104100007055030320409030344024034549030580707107515820082400c00c81c5012002da0040c11400000c11500d8000030308880c0200003604890008103803041c8041250207503000a60323142d4000142c2c01c1b031188244041002100c000a00c8800c00400180082c0e195129a10413490507401152005031041c0c18419822000c1104c0c100740218808140081e24801d004a00284500b24605101d0301861 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 185086942 1250 185085692 185085697
    0x1707090204120302060109090b0402120f010c09090c0f0813020a0510050c0d05030403020a03110f100f0b040603020a21140604151b050f0c060c0901110616050f 70
    0x145010440d03845480b544507184401e1401020340c00361003010000100d0f10914420310680e540c12604a40c0c09032100d50030003811a80c1408030540621901500900c01003083c810b180c520002034403014402c91421660070180c0e112103031088240f0884552156006070403946a030f40c032100d4070300c01584000041c03000400c0d42c000c60b046150403142100800e880b803034001c0020618a0001400c4808460010b03004650078031007194010010b803c945030403c00a40980308607024566000180c03005084500140c40c545a02813001400300c1d500c0c1c815504810720144250368901b00203031000e000d05411a000318101d144288107003480038030085800c0c820710b103d0411070002c00d503012201c0ca1140c0201d9001550b40c0c8400c2e41e06840e92030444404116411043c403490150307918400c245c0000e2082c0c04030668181e0405004a40d07220001c102540100c0014011a41302c0c000c01e41402d601d45d0b01d0350b000140140000742c09040f240e0712074018080540b40718070000054a01d14941f1941d40c040480080301c250 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 185088192 1250 185086942 185086949
    0x21e0102070b040602070c0f0303050a0302130e040312060f05030705091308030906060112020304021324080f0f010204080712021f0201020a02010e0715080a090c0f0609080114011707 80
    0x40b121032007032104000b400d03002841d8050043c50145061034031260341d240c580c00340c0d100003808528108800000f05010b90090044500580c406d50403860355158440c0803200c2c225411400501483d4106005003200c0c4a01d2001e00103111540c00f119043c00d0110341d50f18807a001b80d602c100c0000000402c80a80108005411544003030081d0b182e0909034525540c904042c2e03010b5000c202c000300c61500009040c820740744070355001007903020344145200c2c4c450024640401c504003a075589058401407280200b00d84401030429500500440303818003091410b01c1800c101808169004002c01c00c400d210004101d41610201c05200c0e106a21600c009120088480c1c842108520f100d401b01000c10307010b6000d014904d4040d00248012600742d8140780d10351425010711100001010030303c8280e94860007c0b9070340030b0f05003400055045226222411034064950141103140c401f00c5081c02081c3d03000b46242d005000c1c2c10001e0245510f40c1844002a2805008003c0c0300340070210700400c03641c800c0007245d006 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 185089442 1250 185088192 185088203
    0xc11060a05120912030c131707030b092d010e010606050c0c09160e18040501151a032811090a050603250203040314100e03030601021e010207 62
    0x4411500304060003076048000c40841e00c00c004000a80d000101081e07022000c850101078034516036852000458a400900351408585840b0201240c003001c001a17a82d102007650300288134891031441c02c0360305890010442c8030242c0100b581c410604104450340324090080f00c58003600b4140741d0415600501003005404110b40c24201c00062241d04000101078070265082550403605c0703080c06100c2c07030400694501441c2001202400c1c5501d101e00c401000f00f00c0f006001401c0080c030300d0711703c0307901e9401900e003500d090b50f40b080c40810740c441070f111640081c01201401440c55000900108082c00001c0016031a54403110100003510326244d031a50041203c00410003a4480d024080c2080381c00082a55000d8020000080780c1481e20320140c1e449925881c2e03028a0810400044000c20411982035600f94070083c0004400500c103022012902503440c001004100b00004070041902c00c60b1040c04069001007040c0041e41e41c1c0460011420102242c00d2031181020341d01d510700920422402404 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 185090692 1250 185089442 185089447
    0xc0103020903150412080705161704090905010b10020d0f030507090302120c0307140604120813030605061005032202010917030304050d02010c021b04060f060c1b0602030a0c1106 78
    0x41090b882c41410f0307526415030346c4425560300d5800549280c41200c50810600c46c01164640c00107810982a0200c01c001c010540d044c181d031119403009682009008441036510b8840540d02800c020908000b84012880100541c41110782c005d89004071028013441050713102da000401c2d060081d038107600103540c0548440d4815550720807154503500134140b000c2c402e0140290006032040c07000c0c2c03003001248000b00795a00d003030f290510055144c2c4100d2000c88540400740880700c0405180304d01ea0009502a400118051a04104204030b464009807a401480411f00074040c0050314088900790a02c04115180c00042d2035000503580185182c0c0044200d17089103550000440b004070146014511030821031300d0b400b0000c1001c1c0d083e2a5021882c01c0103a04c0041c40b11851a20003c00b20380548020b040000d18a0301e8a00b4424091156001034000c11071800754403003040707040260305012040541b00c0301400348c05c0c210001e4680c400d04411408102e43c2080410610006400c010480d01005280c980e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 185091942 1250 185090692 185090701
    0x2060f0a0804050d0216260330040f14010f05070903050606030304080c15090612060f0405100b09010302090d0c06120507050712050c0a08030a0b060702030c010302090315 75
    0x50441c00102c80c11034413400b44002002c02c3c1800081ca015140c00380c03035000e460b00d82c03c0c00200c4102604036055050046444074101d18200c10a100a04901d4501c400c0207500e404400d106100300241d01b56400d83c0a03504804201c04640d056080d210030301d80c0061108407c003070501545016000a000588240b45090280304a0a40010580b01103074469400c0e01c2860b5542010541c9900580c4154000c0c2c2c1c2142c0002201c83c60a680b42c40c030381c84401124141000c4400300403500c50f40000340c994004003181d000313008142c034088050859443e400c035002d2020389003504d440c5403011107520407142d22035408075081c007c0fa80a9015034001580291085020340322906081800701c0309071040324040381d0455680b08240843c0d000d01445a40161a6203240010903034442514110301d048e82d10070003209000780c514000301171100c848441c0c01241040d4603070606c402c019041f2184020400d00c140002c00000c001601c010814188621090030014ac641041401081c20030302c0c034800d0b10a400610b40c0402 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 185093192 1250 185091942 185091947
    0x40f0222060905040213061808010203070905040b031b060d020403080f21070206010303050702130f0e0d0c0c05040506030109080a11010b0103091e080c030c01060e16050409050402060f0a 82
    0x11001c81d801c0e03a40344803285940ba0280f004038400c13030318807040c922140c1d0300c103008082c000d901100c061229088141e6001da91504a2401c91300142ca1440c00194001d808000900c0d150242004810040f00640440d01b01c690310b41c0011004030300400d02801001c039602c0d94416213a4184d41c0219044440107503900070500301c10403030f0f0303104003111550130700311100071244a01c02c105414801e00705c5130010302150342541c42c20740306908000000ca9100985038041001d2200600811106a00703403100400c9981c0e0190b81035003894032803c00ca5042095032180c0c900400e994030380d0f10080b281c0c00d032400119030321000c2c08070780034051420014203e09400504002501e074018007007240b022481d00200300c0b0b0704e1980011070a4030f2000304090304480754460601c208285030468146139034030500b040d52629400700c0c2c103c1e0554010280345025655149002c03c0034446c0b080300b16a2118001100c08842000c581020b01a40036a000b4160705c15500c400041c21510340004807100c045585141c0390711111200c000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 185094442 1250 185093192 185093257
    0x3020c0301051003020901030807110607061a060a0f0809150f041a01060903031b0b090705151303030c1109100503150105030d0e010c0c0e070f02031305040f02 70
    0x900c0c02903280100060400318003060480c10740ea8020884460ba0f442c5031290752264000890039200c480030403160342110fa5400c0000e05800c1d1080f040400c1500700d01ca10040160841e40c003243c081d00f0100017527800150302107419104014107081484250311400e01651405458000c4146040120024412820400e00040d403180d0b100e920845006190024844030743d40c4207100c0d100128602030f000307000090041d10104d25284610480660059054540300d00c0c04000352410040c5400108042c020780c10074058030001c1e040780c854039030314102d1011200800b0940d54440502040411115103081040c65101002244402402000b540c20402414010040c0341c0c07140c00c1c03203403164281000e028141c122129040311001006420780c1010f1000903510300c40d4ac0c509150402011901600002d02c5e01000c403405415a034011455600d44041c0151a61100c13600c000203560041c0990408030601c450100203a960a035030218241c001d042d0f8520107030154000c0d0440303c40501c6141e00045405506 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 185095692 1250 185094442 185094463
    0xc03010e011506110a0f02010c0f030e03010b1912050f1218010806010906080603010f050408070201030b0109211505070c0303050604021201090b150a02010b0102010501051c110a0f030302 82
    0x10118400c2d03948071802e03201191500c80000098000350340701400305120310384d1341000d01d0040c1008401114556205415170083e6941100481c1d034000241c00642824807510100b600e01f03455a50710b8030704805001c80080501d03c41e421040c075243e1130000c1084003e201c1c1b00d101a001c0e4003252101601d0a10008060b0444032000b030000f070101c40302c1182d43d0705c180109402108103854100e02c4500b403203821101440e00401c5c00d42c06640310740074801e0000c030511407030348100d0048001a0f100c010750b10006080d03a18040d00c2d00d041040c071241c10300c40d0302045201680c1e003004000b081890074400d85030114003042e41c0d040c80c4135118075050401100a41140340301038014070a43c0d042202c1e6984804000803402000040038131912108018001ca100d0340c0e10407004242c00030085104640668000c0d02164041150603005035145d01010381903580900a09000d44011a0354031703c0c0c280d007025004070020b104800503113410020911940c03513844100b112400b510640e0308208800d51a802e01a507140c08265 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 185096942 1250 185095692 185095721
    0xa020a150506010f081515090a140a08010203010308030f070c0c0e0f01090501060e0f0f0303070c090c030c08040602070303060812251110090b16030e0103050c030601110c03010e01 79
    0x130740880038103100e407a586100300700d00d118402c2d400380e40d401400074005448410300141d10041040e40d0342555001c0080d402401d06140c201401c54503281070084880b5650310800030b580c01800103100050080c42560b030701158590102c2403941d146c00e01220002c41140300500880b505600c040f501808400d103c61103140c0350031a40c11266071700e0060208840b402d103d004000b130341c6444505014505031800752074440001341241e441c90300d20340c0081d003581d120350720071101d140c014402040003002c0d50060041c02c41d0710f800d080007441040720003d001444010002021030b640000d1a004041c003d600820103081c2850132a80940d051507621400c0703500682c1b40c18a403440d402d1030303602e008503845114200c250780300302d861802818180c05d000d2940c1400d83d001d4140040c200380400d1100c00d00c806004207800040300041c41b00d41ca400c01400d003842c038a0009040609100820502808a074222604903100b860403a64444920400300c2c140103000c400507070f2550908210115190054210b1110803070010f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 185098192 1250 185096942 185096957
    0x32007060510060905220c02010c020d03020301050609040e0307122a08090103020c030f1303121701150e060f03220b0708070915020706020106060c08040b0a020a15050601 75
    0x10411540001c1e02d500c2500b00248a06409022a041074039941340c1c014107121201c041c072400407481c08141c030020841704c00107070356034010b0f5010a0750410600e28040f401741030451540d4102070110b900d40c81460005401f864482c5039140c3c0ca48420000c9640315500a02e14052070308180000a04c1c1d2a80c021614642c503610208010310b0500b011100c0400f00ea01c9100145080303d1580103501132f42010421f031000d40801d1207000b100031207440007019143d5822091420160541c9080800d82c5a4014900200907030340c040031050020812007641034030160000704407404807010003101c80c000071804064010402144c2e100090481070065800340120310041c007103101900112002d0184401c0d0007501c8460480040b41c0f0140c0900d2505402c01980d18108170741c50340b10303003401032010381084020300180d1020b401045242d03420f10680e005002c3c2d40c9012a03109860b510790281600441c0039010480000240ca01c442c64000c000c0c0750b41240e4094a60103040c3c0d41c20888100820007280e105000c06c40d903 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 185099442 1250 185098192 185098201
    0x80c0c010c0c0c0f08060406050a02070f1109070314150a0f06110601050102010902030a120c08030c0a1413030201050d020909090304060806060a2a14010605030f0c1503070320070605 80
    0x100544030180c03080c41740140407503511030301d07941c000c4d020251960301215402c01140011900494144c070215014806491b134071004401401040b0713100400a40130145040c072000151074504050344d421403104e580c14010aa401c3c000100303d242d05603ca640d440d107800500280a6402108610b6244034100c151602d507a030b500016401e880007188020351503048074200350001a41080c024440b11039920700400702e5440d5aa6200d115070054510241a50700072442429255100502011103c42e00c900c3d2414002159100323603490751f89010080c140400415007240c2c80301103174180e0f030f16460000c2010410f41400e40c6e420b0f40720b5029014400001d903846000235400c0c10428100c500000d66a0382c0d6100610160403038405542c01810036270500c91882500d4401724a40340c001c048c00c0103c0c00c0000030010b140100b0589400008412084141c118030b0640c6080c1d641e5844400c441c005207034559903a90344409044006001300c00c11650700c42d40604000c20f00c5010203000d05121841124100065140c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 185100692 1250 185099442 185099459
    0x609020c0604080309010b06030c1b0c01140a0e1e1906050906030a090f03020f070e0c0f03090703080d0204050a0902090d12020f03030f0f070c080901080c0c010c0c0c 73
    0x1145038840e1103600c581e001c100054510002182c3c445641070001400080200c0010031940c01550f84100340c443c045401410606100c0786a4021441076000b8001160b0010001e0030800500c010102008000718894120310700511000c04606002014811b00b0028403280004910900c0192801502200d0811032481041030390b950645034540c80c3c00d401d04c4003140c00c03c081507200502e042520748d11442c52200140d150403801d14528440d0b000b0300841c0c1403c9290f1840e1400981c0f10035104c4840d5410b00004403804070480d10104500309000380d4a075120011145041c1c1143d02c000c00683c00081c88035100411680a4025620200e807055503613950341441c58240c0c044c902e016503100b8441c000150004614191000c845182070050714a081a2000c0b05030440c3c004540c010010051141000300402d415070501c2d03404900380c1441c0312814200d440303656082c024034030002d040c4a0064041000ba403501021341c2c44400b000c0c0020b201900002000606070b8600200840300d41c45144004520b802 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 185101942 1250 185100692 185100697
    0x70e120111030711070b04121401090308090c0607030509040506030a0c0801091b08030a030506031608011407050a0207092304200a050d0305030c07020a06170a0b010c08090a0b1c060902 81
    0x1b6980d451503402c290a05144a1824803508011501c07240201c170005902c4100b8060144c00a00944812941d45041c0609604244048240754800c0c1e10130058400000d030458152041888261000266540c030003020030702d0104039a102906003c81803a002440384015041050308510a8131820081140c80c05440540001806121042e41090145101c0340b071081e80190342c004002400ca441e9440030320200c405404003600152920f94654030800303003540c1c4000b007003608003402d407604511384440b03131100035100e08280c0500c19038071b82c490000c4000074045540141206140242c1d40c3c0f4030781030603e81510341c00088069103141040129080c0d00d54941000c0c00d0080b6000a4540200c1c81c4860350300b1105503000810b0741f00289000e0114201680b07514016502034030322516260090192114024486200203214007140f5080412f03402060741c1c0203890307a0001e81c0c49000b4a450782407040c006070180d189500081d00c80c0c84013280d0010420f031400d20450000da801c1504001d00340d03c42840c0000da1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 185103192 1250 185101942 185101949
    0xb030601030b04061a040f020403201507050a12030b0f090106020d0e01020f0f06090615060403030305040201030e06150a12050c010513080f060f060d0b070e12011103071107 76
    0x825094005808641540c200540f00204180c03951861902c40c000241101c0380e4141f10300c41d069000c50f060040003d540321012000810b0890309504550701c0c070004050000340b0011621060000c12110100a420012040b4899014007481000040600018028501c403203040c0e103d562540450400c9080c030322040c80c140c5840b58054100340c0300580043e207648200b856030a045201d00002040c0e112024030082002d100391202502042c00c0c0000143d1418001400140750300541c1c02c0f9500c45550b821084404403503040c180811203540b01e00068000f018001e5100180340903d8007045110410704a50418101d0100c030200c021907100d6800109080c8034407002017040d4001103005141d58041c0c00500040c4166121080001d038031794051a050940c1440341c0c00180d03100e1002e0010901070181c215601c83c2c0705442640b02c2c1100d5865044814102528000500002c4442070300c054850103c160014601c0744000e01c00194440300503034031039000b2500440000c1c600030360f00e01c86000100780c12045 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 185104442 1250 185103192 185103203
    0x106110a021c050a150c0206011419030b04050d02010c0e0a05090c04030507080709061a09010f0905040213090506100807080c040306060b0a0e060306030a1b08030c030d0b03060103 79
    0x11030490360034400d04240ea80080d00031020761503160b5002403020000300300c00030b1080003000440c007004031180c0142d4080c20100415034220710010b002e02d0040300008882c1600440e8610700700811010b50114102c402e40001d4001e141c0c060800091100004000d028484207a000304411051590104ca01c1ca6402c400b00782d00c107140150802c0a4078010380f106070041c0c00c1442c07551a060303503540c41905d02001c2da400305074a60400003040100302d0b40307031080a006202e900300960620200440000403485252209414890b541814080d4180328581c841702910000c2c20465440028651903100c61074107101c1c00c686a0b060100044460401b4401c00d900c1c006c1a40719002c00b80c6804800351003d00340140380048500d401c0c4400408215107018100c0107100311407000f50786440d10301c4000e008490440929004070000c01c240084c1d070301d001940140090b00b141e01e0704d08511000d0640c600a00082d44032412521001c260720303000f5100400240028101c2030010051520300030280364450700701b440007611 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 185105692 1250 185104442 185104453
    0xc0f0a0b0706270302060603070303210b060d3201060822030906020609060108060105060702061905030f09010c0e040203060105070c26070b04140a0f09090605010611 73
    0x10040480000d0940a44200c9021500004490109000d818160101c034190300a2242c40c0b000d064040c46007d03045081500a480328500356100074122290b800e00342c003d001081c040124404185601400b10312400070304540d41e40301110764940c090640c4090101b4460011417441c100e2450410f0b040380d07001407c003c40700440e0302e04142595490802408102210100107041722000020704949695920030384070b414035a410302d48001e05d070423401400c40003560300450040c8a07038500001c6e0181142c00c00c032001c0b5501c110350310104810780100030342c2101c2c01a816101c00d450356000342c0036502c00c24000c41c0784203803a600d03102028241c1390041c01c4000401c0b8005c4400465007016002154400412705005180455594414040e11100c0c0d000508034612140c810a08040c2c26282c9040c450264004140c13031420300d16807a480340326500c0f0382c68841041c040c0c000281d4a0785040c0c0c50092013072099952217999200e164801078448100c1c101e0f0058600000803030100c0c010f2110140c071104c078100814 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 185106942 1250 185105692 185105699
    0x31824020601050d0303110d050a090308010e040302100c020c060309070e0601140711010c0803130210020f0615030111030f04020a172116080702040506030a1e061404030201020a020c0f0a 82
    0x14001d104005007110311f19010010911201d0540c06824022400305500242c0c690650400908054042e00b16000070b0b0000c0f010300000ca68002404803860790528000192a07004a40c00c0c0d01e0002c1400070700e40c12880100c108003c190b03021401e0b40c22115103603c8003419640341001150300001c81034070f80102d600d06001401c00b0a1001203041104401030401981c1c140b40381d03c5199a41e081100d0401a035110b00220900718103004503000d6a280f51400140b5103c0c22050303010303880d034200402a80c19510500703003c500366502504111305480300f070201d941d6641044042298410402c9905a016140500c030008001c6d109114074072b101c140702809001c1d00303d2044c9002c10f402034400d203250f01007071042c4501c04514480221241240f4844e00849a48249602c10702055840003050603109400144401c40803500010240001d101902c84c2c64404200c2881c0640040c0342921f04a4801c1c01c07010304020815805500815840030103400b16540346c1d20440810100031015520386400c00c03052030080 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 185108192 1250 185106942 185106947
    0xb09210c0c1804060c0801080d0c020d080408060106020f030a0f0c0201140c010b0f0607031413030b0c0301030312060b0405150708070c1a0c0a020607031824020601050d03 75
    0x10012109140d003501c120500050004550009180240200711422424802000407912500f64940d1340c070b060484066150003013507910f9062003059402030140e40c420003400c6650340341803078500d1540443c0c2191242e8840400c1a81e4640c04d002da4005882410100d01ca1488000240c3c0d1072080a940c803452101e0025000f00d9484510f1081241400010041d90b010051807001401212040c3c500006203485c0c0c0c14204407060030f140c0c5116000b59020000500465480103c82c5d1001a814080b95541d0a00541d0800042156032028000290100611004e9501c5100450480e4001e613034010500036010303108811103d451260b0341800e90208000c2110b82402468090007000004016003031a4181d1a54000c81d03000285c1182c8031800d8a00c00e01c40718180c040802c2e0001d100c5500c1608145c0741c1010203030b903100340c620043c0c400ca001090140405124114858000d0b10b4018000701c0950345405039060b0203c0f040700071040060810aa102213440083c203136048400042c0940f540800d02d407002d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 185109442 1250 185108192 185108197
    0x207020d02040b19090f060b0403020d0305212a09090601120f060f03060e0d0e01080c091008071112160606050904150c050405060d0b0604150207030b0921 68
    0x44d8022140e02507000b5040103002c100001040000d401040b6102603030300701c00032039840c3d41040d001c0501c184403d0015880710016081c80e15410f0515a82d9213080f08a54030010324180d08081d0481142c80c200800440c01500c9107400161350048400c2000d4050003c445c1401901e00f90303a0000c2080c0000f030620341c401c0f00c80c000400e5805000207003800400b82c05d0310995419400150030140310395000c0040201511032400c035000c1c290040c2160059500c0002c2c021600003455504002042c0c01048000c98803008441e01144000c2048156040d4044041d2466808482c404e001c24610f034400d91700c03420042285080001900b0343c051410380760590240d002d0b0402e60080c1c0340c95950701c10100e659142d80070300902441c0580b00300104402a9012403042c0c40c0c001d09400c04010003404108800e0319980300355190f80e40501030110b070400404012800074000c0b139000301805207440c0c4000300c0880d008102403050b0790240c1c0c8260140c0c0e50b903600e0f0a944220101d021800c01c030000d2241614040c010b8003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 185110692 1250 185109442 185109461
    0x60d03031d1014011e0b071b0909150b010203040501030f02040305150a050a06050f0402090102010e010606050d110906031f030812090f0115120807080414130207020d0204 75
    0x107805044091111440b454550600d081910300390f40c0703c0d400110401628807030b07401841d20750380c0345402031402c85010901510600c41c3d442c8440e8045015402c0180c80c01c81014403c050203c080c1000750b8075034901000c3c2408420548010501c081d080340081e403a805580f003000340603001941392620306030046006000c00508007810f541c0c00c1c800440019020300c248044241600e40c00700d40d03030500e07018001c11500c02400900201d40340841c108040d842390f210421142800b2100103032244074443c0180d024202c584032051071540380903000314103107800c44007509108000c42c83c1040b080c400b185c1074000c01d00c544041d60340d2001c1d05100003503141c00100001703a40540c0038590340c0c1c0c11990703e40c1c1c2c0da8815008024005910540321b410001d02110030005010f141310408001c0c00082581800c2c0074900c003990181d650302401030414038040c000380d142102c0d0515030211096039582eaa0300c8050082c0181184a0f52150f1450b4000c4107002c542d82c0251003000390000d000460440710340d4200802812000d8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 185111942 1250 185110692 185110721
    0x7031706010c02152d040510030c0804020d02130509010e071a0912030d0614100305060a0302061308030708180102031215011202120105121f201b1005060d0303 70
    0x100911140c9981058508002001205407190304100c00c000c4080740300f0140d031042600cac1414214155611201464019806403401844a0312034004901d5003000032500564540c1010305103d01e000741588902c070424192401c0e03c6896440301107c14140c160034445140703c020620000c2e11900d0138511039012180c00301c045918090745002c2800035540103034400d0101d610b040d00004d803a0306090440700c80c0000f0744e02d401c014030301c0c0880014248840324000a8054040070074080304680c281d86c40e01e406017003143e049a888829a160200c49a840843c140000c08034152007400709500020a4030242e4116104040d410758403030805001042c0341c61101810010225007500b0158018402441050048040b0594542c102014016035516900300c4902070fa00c06c4005c3c035a608821034900307c6081c034541c1c0c00f24a4042d6910042030a00201804182c01070f8009103516542c0d082d80c03510104407200c94103460011a0015414044420031a0342a411100300c2641c480001c0c807d83c40000202800c4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 185113192 1250 185111942 185111977
    0x50a090c0f0311040501080316030909060f050a0f08060c09010c02060a1206050303030714030603280c0f120206160b0109060302130c0c03110a060207031706010c0215 73
    0xd4a500e805119140d100888440c007004040c014003409070300d0862005803e4806000d00c2d40340000360341d03680c410208818654903010922408240c412280c8100829a10300b091004d183c81c0c40094070043c0003403240c5842402100e0001400803c500f030706104594012000d07080568800c0401d80c095400414040d04100c4021207420040c0d482401404030300e040390340c0720018140200000300c01c0710155004503200703074400c0c0100032625500135248403201c006019000e4903600c9620209107400381d80034509261014415404404124070120008103900402d00c01b14010344e00e0007000d02103074190141210480d01c814580000d401c0c50002864001c04006041c0d81100761502c0d0000384c1182078100d0910252210030410562400454030112400010020012007a081002400c40c0c00f0f210320003428031060802c0c0380414501031058031101a0440019540c0352820b150003014810740c0c118484c1d980c908040403d01c0c55110f000b03100e610303540c080c0c5140240b1804803980140740d00328103410030308114035 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 185114442 1250 185113192 185113211
    0x405060c031e010605091009180213031514011203121a03100c02150105060301050d03020f0f1c021906020306040e121306140a0309030507020306090a14030c060a050a 73
    0x8550442e40201995075881c1d48890800080042c5000b040111004004a1260a11401c4c0910038401410010310301c006a07a0728080c6086103151410fa40003818104c0050755141040c0680e4101201c0c07071103003040d10300070360b80c84d49001d6003281c0f0300c05e0014000540091403c20580040d90103000541c44c0c1c030f13040e0442042804006032900e241d0b0104180116140c211801100340c04000d18500b4180510315040198145004510140414440c991282003100c4070300f0103060091240071440303180300040e41d00d600c007212041552501d00d11b40d0084041102115041840d01c045803400a418031004245000340d46500c4030701c0603400c00b8012960181d0b07200c1501507010030400402100c0c600302c80c1555260302d20f4030342008103035540341d002200340250b199908030007401040c219007101d0007a050000d0301c030150341001c990a0241190080d0148140b00c148104968001044100c0c680300344a40d40c012201c0c0c0c3c4a0507220b0286945a2903070341d02000126503000c5203500010350000c5144030001d2803641 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 185115692 1250 185114442 185114491
    0x31203072d03090c0e040f06060f0501140904091209081c080f06010201180606090501170d110102070606500d05060403050a0206010b0a210e100e150405060c03 70
    0x4040da0103c441c0c601806180023040240d0040d000103107018041003070311610f482c0000c0c141e0141c00002580322000010148010341d9103500c009a596045201d0711030105220401078151f111038010050b0a21900b0944400d4140b040c0b0070410052407550350b050ba50320f51112407901d140015200d00d040d0b5482d140310701c09292001c06045036040c000c1a02254291400b602c8008464040c0c200114a218940c17141c840500c000940c400c0604451401b80d00d001e9640001d54020f028201c00148504e00b851400101c40b0340c228104d01c00c0c1003070180001540c0311043d0b144480750140200031140c808441e0054403520501404610304058080d0122801c20301d942d503107034200b00044608602017100030591240c00d0740c0c100190b038050092542000e2801d01240b0019041e07044600743d4495040d00c0e5284048040d800b034100201c0390a1503011640703583e10941d4000054590406040344600ca1412901d102c0c2004800246c05281c204020700034603203034224255541c0c1d03c0104074142c0d61400b088403407188c0d41d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 185116942 1250 185115692 185115719
    0x10e0d020c0405090d0c02090405010605130903020c030d091205190c0e151302030c0904060602010c0e0a03080301060507080c0a0c06080106080f07030b010e031203072d03090c 77
    0x2119034050903910303025100300300c211503002d45000d0140c1c0c01108007142030b540201001d803080740c044a0768040c5590307524049001d007034150042c54100301010030144c4034050315040f003509540329800303a500d42103500c0f01381982c800c00c07080725000040002404001840402c142e440840d406002034885d00720a002e00c2050966400f2412125030f43c01c00400c200d500c0149044581103452110f1813460700341910300082c841d40304030040c00616a030001c080f4101060000880c1c141d98400391040c0021039451340003900030140e06081d500851726000d101c007614500050040b05980e44104c199007581d00b0903070115801d07004600300b00c6840b1410400c200d0914000c212082643e072150040180550401800800540040c0e0018040c0119071003440010f441d84c06280e94426243d107000103110100c000100d8031032400c0a207054150060034101250490828020f5102d01819140c0302d031010744070000080380322661456101220480c00c0d10070210b0f48260031603a07603580074991101406446412160500 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 185118192 1250 185116942 185116963
    0x8030c120a0c0614010807080312270f160501030204060507080d0908030408070c1d071d060408030c010b03030703050706050408091804060b010201180b090703080406050c01063203010e 81
    0x60b46138500401000604000f0f001c090840d48019500701180c0c0e4022504145000d0005404843c0651380605a60144642044040c122004407503012004019544d2900940d440040d4800001c00380030445501038001c60701114034590b101c030300e020f00a40f519401034014040a6400c81e40710008100441c0100d006980520302412441d0f0b43d030b0480b4600b1101040c101c0d0b014001480e180c7c2c07801c14880c12401d500c0c5a000d0b2890901c4c4c1c400100d01e0180b020424000800303e58840c50114010511000c00000b070141c2e0720703100c00200011150f0303608141da41e0041040080c0007031003c014002c00140c407a004990001d10030300210f0b003810610302c00541d10318600c0c5401003249903a6070030481842501e00403c8101c042c00e0008004c045040369881c1a880c20540c030150040071250003113000307440100306072001980c00c02d00c0c8544460721220000c2c0036501a4228031070960034050089420324981c20140014901b00b07903203180c0e2490114144a9481c86c5841c10b90381341d541c0340c405000110003030001e840103 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 185119442 1250 185118192 185118221
    0x1821022e05040503040801050708070e040e070302120309010e033d0c050702010e0a030c090b0d020603040605060a0e01060816120c120f050405030403020118030c03031808030c120a0c06 81
    0xb203a0800d9540ba023141d90081c03084007000902e20502880359000500d240003000103841c0400c902c00c5041c00c01e4500120760f4002500041007840e01100d4000c0030002e002040026a1140700c05540b800804d940c896182e084584074900a002416500d040000c0340c01d5481c030312a0b0390070700c2e22450f04440340c04c030748840c175442c030102d040012030358115a840341c070b189400c01301100e0303605441e400c54450100800450181c410b42c00c1e6540c1e44450566030b06503e5100c4954002c0c013191fa41d14040c074140016000650751540181c0448001089951500c1c013968141c403826031340c1c6010b503504c4580c101000595200030a0910500201010003080d0728064403035452880c1d180e8400300b0007002000811200d00001c2440e89078542414000007440100854045a80900e000d101c445145100d04001000c2940014103c2c4400d990010825801521321510840866098204169200b41040e268402e28152403201d0300081c4500e424180c0400161075407007098a0090030300c5200c1d990740b40c21a0b4040258052 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 185120692 1250 185119442 185119447
    0x5011a03101205031e1e03100506031005040605030d0c1e050a030e10050405060715140405010501090b010801050d03270b0702040e031611030a061821022e05040503 72
    0x1985c07540c00009500c2881405941c624000740340d0542080310000030202c426010000001c03550703004055035914051301d8018922a40c03804c2c42c010001050340c080c030800380662704001000880b0314002c52401401c14140c0c881082e41c00ca19074480d07034100d50701c05040d810030350f10a40c4000411010400120240c0c0f0a8980c0c8250804100810000d2048000040304000c0108428002c2da1141410355103081c0d400180c2c0703040b280d4003425a50140810181c12811740a010041005101c01500201d04984680030200b0110a0301c4c001141d100c00240036698028200c0d0400c80002407040400c13070742c0805000105035800c6689002902c400720b950744140311000303003c5240000d5140610801e001d0072242d1004615216151009d183c5a14103801d005c0c03c40d03402c1700710341503468809010030920b0f180e102c3c500300308003802c504840340344040c556801d5400400041080e080204840c00228030f094081d0020003002602c0402c1455403056410b101441d500801400244052240070386070156108101554 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 185121942 1250 185120692 185120707
    0x30601020c062b0608011503120905100809010b030d1710060e1201090204060e0114090105010503180312090303070f020106050607060c0c0b0c180405011a0310120503 73
    0x28545407164074001c0c0708040400071504200c030880802c1d0104000b002e003c0856040414803c0300400e080d0380704085a5080c009400b6820056010f51016039104001c01d4203c517900c01c004031b821050314054030b5008018018010b50391401149415032142ea080008122200a003010905113243d040c1d40101056051081440812200a40716070214000c1c0403810301524161004040c2001503100c140a4401400f09908502c003c0d00803d155540260090180e90341c0d13181d00900221091040c5e034a0050b401200c04e0f5a450005080b50403580169602400d60700e50302c0c2005640710840c0e54200e00f1384000c20512200c00c00a0382c03840d01c0794078a1005140c4034a40100302511844007400000116413605d00d051100d592000161110303180c120b007000600d49545c02d0f0a44910742d205401400f082003950402200c9030102c401401d10342d20744000c05030320a140c9001c1c001540c00a00804140901d41420403041c00070b05005154007049120031000c0340d0703903210f8651203054035080043c7c0d140d41001a016 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 185123192 1250 185121942 185121947
    0x3050105010501091e090b0a090c0906120213092d1d0d090323030c0105070e01170103080d0b0603010801140f060117070207081b0405090a020915030106030611030601 73
    0x40f004007900e1070300d000c3ca95106007288155480b94090940c50390350300c04c4c918020b03072640d807508c00140142c000104212a030001014082003005c2c030440c0001f030380c0350981c1c0c10f0020a60084e910182c00c1c01032091441400d1584e03420240003907041c0007030800440c00180c0420f10040b80c492541420361040000c0001d4080e814080d840300c103004d40340d61070b4403884500c0c04440d40480f9243c122500944c11171030404003800c0e03109035245030740c50704855407102207002e03a840301065000300d0188141c0d44640000c0b0004000649459106401152080809034010800300f10884000d1442c44a200000220b4950035800074100350000e80140e5003907950360480e0304106100e00309060b00044030b209815154689400000c00800401d40307044a40d14104008c240640e0080182d040980200400c0e40c07144801c0d64103c47e00c034099222600e12450500010a0000401048a452458002e014225141d86c0c0c0310109901e0500791420540641d49c40100001003582841004002111852090740c1ca0501d203000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 185124442 1250 185123192 185123207
    0x50105060609150f0706060320030111040e09190309030606050d02061b010b03190507090606020c1002070509040308010905181902011b0b01031704030201050f0706020d0603050105010501 82
    0x201d0050701c0030050916180c0e2640c2403441e1095240f0126583c2d02d64200c110039050003421401030155003440b0001c0b007007000c034103900c0482502180c09070103088003810405007650700303006c000203085504000c00e000c2030300c54010701a44100c1d454215028480810401f0401504200c1d0980c00905441c41c14010031a9070b0080b44000c04040f0380700300034000541c0015070944510810b40040d074001c200345484040c401e40009603481030080540780794401c5c80d00c094903d902c409404560a005854010414049501c1060140e9103503078002c003a415412402e200c1c1e034003a90409d0b0801d512500000203415a25000c50500c5248a83c0d500c20342d55260011001c1a104040e0000d40004105e805100d42c2d510700003402880700c0d4504084d44800011303400113030744dc040b18120941e5244100918131060100206840d41203d100d0101c4607081e00c05070108100751b006074000240000c500304043c99049800d0000383c0704550290000600c0d08000384450001c90b40b0715807085540b0394440c0300410141da0800c80 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 185125692 1250 185124442 185124451
    0xf020102090a230301050426131202190b0a090510021f0902090408070209090f03072603090c130b09040f050a0b09030712111b011416050105 62
    0xa5060825040c0015000c6945000d104901c0040b00c0c40e07003400f0440512414400c0002a000700710b242458102440401180c142100002524100603041e400c40e0b07030b007280c0300454800c840800780c03400c021020f040c3c00850b900a9170b01011401480d0203146140c45150024004110040c0c0d950074055000fa00d4003081d984014801e004140c18032040702c0d00030802d0002184148090045a0b4406014500400032000081d40140c6040100420416900000c000942c02181c0f210242e40d00d1a5030076039280c01c4400500e003141c1007400060b0004144040340e01c1b841c524030541c4100d11ba80d080f60320b03440740c0048a04648541c132000c5500000c0c1896072a51313056400844040c083c0d84803c10104880b460080d0000b01065480081c2e101800310901110700341b00e07402101e18056041c4130409582c1c03604038801c01e4034141c004412400c002c2d0b0244100364030141180025100d241503a26109262404040043c2d0600641d1041d000c1c030244000700a01100035817082c06035213a91139007406805c44000030f0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 185126942 1250 185125692 185125697
    0x10c081204050c2706060d060e0105150403030f0507020a05101709032b110f040807120f15110f0c061006050f0a1b080c010531020102070b0d06060f 65
    0x207805005580440c2c90f03034800885011400062600c9000210f0850300c190740c41d47c01403503d00140410b040e624018414105d92003190384c1c211000342d10300c000005114074030004001c01c07800f50240c034019002d10094807160b03000400c40d1246660720f1012442d049510200074000803000c0c6600c407583d06201018070780043d56003000b0360802603c41d9031001400782c8507444280b012401840701c0d0042c1c05a07001061440c0b00a882c1036190544400d0b02a031542041c0608540d030300500c000441c4501080114100054020f10601c194070304d56220038480900c0007810072403032520b505119042080f0180100000f41410212035910a100f044090034068050001803400b2080da41c1081803a0b07104050354030588211070f85c0385d83e64000500c1581c6160f40410100705406140840c40180036021000d81012a2017400a1000b944c0300328403410741d684024100e100d18200c03a1004048500d0080f049411a4418011540015229031151a80e034200c000d00100158840c00c080c4207035640084251044030450 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 185128192 1250 185126942 185126959
    0x31e04090624021c140c01150f1403060a09060914030a0905010905030304062f100b09060d080d061d010807050102030a12050703060b07050105060901060507021806010c081204050c 79
    0x10240812603080003540313020000202c0e100341e480d0b032100b0104d0f086095034800801c120207c07402030805080c020b200d42e50a80c0d1110a000601503c40161440301c41c80040150030b096940d001c0e00d6000303000d00c6105689650355004000c0001e00d03c1c00012465580c0100115210708180c2e100070010007440d00140e0400c8102c45c410007590302c0001c1594140d0711941003001c0c20b54003040e640e6034a070306055031184040c4885018084c200780301141d11440708550705424080380e4042004d01603411030030780e80340350032041d01c14005000c9011240500292012400041400340e83c50450701080c11110303691002c6940002c0040200020812052004000c2030000c0d40c01d0450418010b012130341840c01c5500c13010349a40008403c40d00c83da0000300940344e40c051190300e031302d00c03814564001c200440b950b9004180140002c9101402072090740d08940c0c0c01000e50002c0405404c8bd200d040348007a00403414400e0031703122440052240d60142c4550440444450401d20702030409c00e2400c0d000030070550090001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 185129442 1250 185128192 185128213
    0x70503070620040f0306050903070b01141f08070c03141206040c0305040206070809010c0b01060309030215010812070507030b0c07060b01050708180a08030408012903031e0409062402 80
    0x20600c03004c11a84c01841c006840d42e074901c0010f00310711518000400c0300e1940e200104501001040c141ea07496000d9800700752084490095026401c94800c100c2c0100e224000080c030030750b00c15100c148500c0e1003407416646078a0010040034030364012441c3e00c40003110720410016141071034803560136001d40c107150922070360400b9000300300d03188076040d0050208200060118403d901a04961081a520800c0c0780080c3d0303524000100144600c400c1100180034880d401304c107620f20005441c1c1a12900005841703c0741c61100100d809510888040340d15000301c0b00d0001c04200c3c440e5040d8071506444143c00e642d0101480e12900320386030500003606000d03062082d00c011681c101c0c21340c0c03400c1d0f0302080c8401c0b00c0704101c4002101c2101c281c1c008901d0b48800140030487c07a00641003454802ca07484415402c240c2c1c034041d440700010010040c2034044c1e0050240d4560300e0000031603e140d59980102082c501619103001c0e01c203a8103036811001c40318080760b0410fa04043d041c510048820041d10142000c08c00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 185130692 1250 185129442 185129459
    0x304032f150906180f09040c0621020d020403020306070503100b0f090d050d0f020a020315130c03030201020a0909021314030f0102130303090e0705160807050307062004 74
    0x8800c04040c050510015640d010020440c00c07220604030061280340c866881060702c9040d2640001c00d903014088604100d034807800e00c80030316802203520400820360319043c81812254107003050000300c00810103114903004840e403403000f000300d401003c0016035900d0560061501e0650702814980030028200b08101000303907003049410503101450700c2242d0302c80704407412001c140500c074a21b03903115041c1072440e410404005407101010009480e020500201d410007603840724012040a90190021440034000308a0410040e60019171039040091500c003503110300050159982007140581e60001d031030944145c0200001006280b00c1c10706501c0c1580351603481400341807a02c140041c01604205d06100350f60144802d100300c100c284021034640d0200d10701c4d07000c240715910064011030014038000c41c5075025441307802c0c07007040c0300c0d2a0140f404ea86000a201c80201c00002039481c91030a10042d000100c080c0f00920810b4010726001c80c1e0080d0242071502c0ca806407203420200c04404000400500a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 185131942 1250 185130692 185130773
    0xf030703050706020903030a030609110f0304140a050307150f020304020616020616051b090c040e10050a06020d09080d091802070b07090812030403090e04031e02030403 74
    0x580c145001612002e881c0b81c030001a00620400651501020514580b16a411361086c401c4031300e030b060705015120340075078511070038070a44113204d1640c0d03000c10000d00401c8123058220624000302d0100c074080381440c1c94940c21604501002c0700c03201d40b2020a4041c14000c3d0143e0180e00801150442c80c5090690000b24280709142c508a200c911403002682076549160946401d48204440d07206461f455140060719800e25400405880380350910f007040c4d40c10b01901d2144544000d200c8a40341c50f0400341249514070000b00411040c103111000810188c80e00d00020b802003045800404242e518184003508011ba542c004401c0f035445a918001503a46c004001c108a8074801b00e14a0401a41d901902c080e1080035805002031106005110b0f146038029019012100c055060f24407280c3d4103210011644815600035000030980321003402041c2c1c14480058100348a402c0a104041c50740c0c2844110f0900002240c003d41c01c0814208140034680038408072880380b4960411114415403a00107102 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 185133192 1250 185131942 185131957
    0x1902011112040303151403060109060b0f07060e160905090a0314090a0f1403120412021c0c081b01090321090e040b0711030703120507030605190f080f03 67
    0x1a00786030045014180030768440110501a030030040b00103900ca2201c03140c0030603c800403d019118030b0000081d8880c0ca4800c80007605d4818000c41e00d07109400030789401d140c0102c00140e035030f10354640f050380d45400200308000300e454031091403540e281e280c41011001c60f5401801003030590407509d18403000991000d0486048050a20340c00c1d2608050b20103d05102c1c5c00da003000845d88010707000890f0f0596000000d0110350070031000c0b44c01021a40f4540300440c0107a21070100c540020001e4880113260010400c150350307003640b070304140b0b024003525625041941e5a01007142c5800506490b043c0b10060900055158420308188030300e64990380d00c0c1500c10a00c00c041034801c01400b41b140314024030840c001d000401d00421091220700b401d040901d080c01d401e662510105500f03104d0010329007008426100301d6605625800e0080f036040c042c4001070030004103100c0c10541c1c1e0b010081820380d90f500c068046407941c3c4002d8004241010792590311800c254100580e5648050700b05108400c0010403100b82 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 185134442 1250 185133192 185133217
    0x61017070905090a092d02060702010c060519110901170c1308030d1808070605040c09060b1b01020301030b011403120a0c0213060b07060e030d0207050319020111 71
    0x155488000403999081e654014039840002030040c001066556045800a00c1c021307408200341d0440d0008a901004070956058951194407034031401601e400c1c070151644500605102c1100c4a280d911041241e804542c190b0000c4c0000901ca510b103a698403401c030990329a1503559181065a10010744134500c81d04001d010001d0200000c2c060201000076100040d0260000760991611800b195840360000780716180898506031b040020412100c000c0440f59801824507450804c00e0b880d10780c05404c00034010b5400260711040082c001d000b501c19100103254011000e0b84440e0741f0690800946812045050b6a81c01480140042564050410304488000d1186099659481c010908000b071070711010b40c40020104601001c5078104c2100421180308540d8101169401b84040040300c54070b02075590401414441507000a4199119540303100781102107906001035110b4441c2640d21800c0c3c2120190004194030f840ca00007008545000c450380c0c0002d021105024501180c00d00969800c10f04 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 185135692 1250 185134442 185134487
    0x40501060c0b13050a0b0109110a080c16080f040905011d18010b030d080106020c0a0f1403070b030112021f08070e1906081e09061807080312040b0610 66
    0x801c0c060034003c0507030f90020545441002504042e00a41024829001d41303074200790145001c40445030841c0c0d06214152107500240c1c954080e403408a4000b211101040c0007800300e80800b2800d80c05c06030005c00031444040d43e4444c00e10903490305413441039109599900c03280105401050702c40d0081035012504403005802d1241c0c020140d40908040840071f5014003c180392201c181e50300822840c140c402d2a000c42d40203040240520081760402c1c81100d12011464105101415a00c0d881d1149901d004040355881511002d04441c55403003a4171414030801030800c01d00450600c580303c9689102c020752000480c000105000d0080f6000801a204215a50344644403613504c0c81d03a6070301c1c000590303048000304540300c072005400d020068070402d00e07584584468545d00313064009d0392441420801c001d40141d480c1d01511400e464030b0b46420548600440ca0b02007400a42080a00712129159103045218102403c1090b800103010f400e0a002d1102e600c140312a841d0000d50344103440c0841c4044c40c5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 185136942 1250 185135692 185135701
    0xa03020901021e010b0a080f0604060e030906030a05061c0803160c12030605130905070312020f1902041401050102030913020c03041211010c0512031b03090f010b040501060c0b 77
    0xd0604084956003c0140c008003510a10114158009a0850300a0315811103660b100d03000c0540e0b405402040c0301460340803200040c00180550843c41a000507801142e00b01002200020301503001102e110145c2c80e0345400300540361601c03490200c3c980d00a1a031605050485450f02e40861000a0942d40b40d500000035000e072640c460005510560f401141411101245040003005802030303111306449600710009000801186114000300750790310800074040145581c1d15040f111348103014100a5010f0000c9041800038140071004c06e046600c0c440f480e505200c0e20411045480030001d1716400e166041c014009d80e60000121940e50408540041401c039181440070003030322030103101017618040070800045039106049400405481000e07102c914440840044031001140c050152503980003e10f24900300709040001d64102d05881d004c1c079002c5107001c80c80c603001d90003900c4003a06580314441d402c0441c08203100c1c0144c003410072a414051540742c000014200803d0b000080d00d07012003000482d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 185138192 1250 185136942 185136947
    0x40c0b031e06010504051509030706030204081b03010b04181202060708010509090a151a030a0b0103080706020c0a0f0b0a05010e01091d070e040b09010c02061801091a011502030f0a03020901 83
    0x1c0d40248030040c80e8051f03151400490050541240340164000d200b59035011421a0182c007d40701500c0c0c0301c000402d00e101554143c10000c2036010303855a05175503030340e44a041c183c8950003044400401003003d00c10100079458119211300269200c1c00440d0001c00c14002490343c0188060304603102240e404841b51501001c0f079003000d41400c4010700c40c0c8a1000790030940c440c0b46d00244000b8464001c06000643ca1406040d143e080c941c00003050350f100000144005000341018003501400751100500303110105022624001e50340c0070a5460250740000c2c4000c002c06030300d040b5400000610184010751601c0b030a2030100d0018002c4292681d210404140310301388605202604d4010707203040300c501c0c980d80c0c1403e03001120141c0b0b00b60f5120044100043d0740c1c41050050000345060380d03004290541d640d0100c034140c4800062110180d548681002c004644080000c80c20540264210720310303549015549010078410200410035508184000c0c50105041d8094590000d018180581d40b40f4866004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 185139442 1250 185138192 185138197
    0xc0f0a050603041b06080903090d1509051608030913050705040b0c0105010e060402190e011101060e1f061d0f1e01020106091404080a0516050703030e011407110a0b0d05040c0b031e060105 82
    0x100015433401c54024288400090120000f000401cac40d4031180f900c444000b80c0302c0c800c444072541c1105482c1d11a24146400b41e0005a01000c186841400c0a8803032085809aa02a0004800e1170b9150001404549020601c45420040c112403c5103420700081c00701c0704071085038900c1c50512040c040001d1859009402d00703901c248101c0000c01c9440d403078003081c03010b00700b0a90f1100c0c441c0c40808140031444802c102c0300d01c01da07442600d6040b2000300d400c0342c400040442c481c6440d000384245540781c082d51200850b0f11400c021000c40c0c5401402007a000a003103542e01d6100c3c0903540c4c10407110308842000c207145c1079042034014410580c0d81c21404e4059038248603040c00c4007156445c0c0e100702e1007403003004910541940d1003681c54800007c4102c00450318000f036029406900d2200304141000544041003244100304080e03c000c0500d60ba540900c5000d4003c51a08043d07181c0342d10400c0100400001010041c0a03101841411400c203000c038803000d00541113402c0c48040d840c03800315075030740c1c096000e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 185140692 1250 185139442 185139473
    0x20904021f0216050301060303080c0a02010207060f0203040b06040c0504210b09150a140109090507090c181203020606010503040c030b0a0e010b10020c0f0a050603041b06080903090d 80
    0x1844141d850704070400039a502103465902080b200c003040040346034074041c0218401c49400d60b0301d0128135112032080101d41ea100c41307030711001d542d820011603000400c90b0080203d00c0884204c01601e0345824100400d2205000382014825860145c6110050383c20100341c509940d43c0010345400400564280c41181d06072901c042c03e082c1c1130074204001941e00080d00000301e11207131040b844986031030303111009881c0401401c80d1200300410042c020154a5400403140c01d000324120f51501d13940300a80801c94000110280008805641001008040c5e5000f00700400141841807194003003500d00a4407010042d220a04000002011400384903a01c40c0d508060341e0043d0340c0c89454280032110308010108038010080707950810102202525181c2c92520031034000340c010340056900101002109020b40d05407a038800001840428161a0b0602451066109101d21061680c14406c40d201c091144e42c07003403003000880d4007000b00d21034001c03060b941d46d11001d03540100074a201d8544001c1c90510820b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 185141942 1250 185140692 185140729
    0x307030f15030605071407110904082106010f09050d14030408060a0b040c020c130e1006081b06040b0d09060b030312010e060102120f030606091002031c0501030f02090402 75
    0x40003100b03100750b070f80c480f07070042805c1e48503050807800644c01da00707a034055400042d14a07409800c0b9210302d4185844a035a0042c803507000c0313071f2800e060980d50348039007a00041d9207910607825004010076560484d402c41610103143c140002d165107001c0025140c160f90220003031107001c481c8000350040700f04206990280106100b0356140b0324006561000400340068090700c900c1c1405018074085001013160840c2c0c00340541884c03c3e0303034041d0360454040c044500c403452a5126100900d100c8690511504018100c11000344c00092035502241c661074408000c0340d8030841003000100316060300300b012207000e00002100403903031401c00c1c10a14020806500c0c1c0d540c140c080050201214010500200d05031740b8900b10044480d204c0100490f5100309035451403044042c100030010021034070902959100800070009403400309403a006c40c69445129501402603440130421440c0d0b2009242200602c8010700c00070000c82d071541e21480110000403101a00078040c1d03070081070554803031075400c10507442c806 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 185143192 1250 185141942 185141981
    0x202e0207080c060601090b0702010e191208030402040e010c02031905090409240605010f0e04060b0c1c0201050c04031b0306020f0405030118050303041b030b0406020a020c030c060307030f 82
    0x71910b41d5200d0380304654443c0051188907000ca0301049030820b480e05140c042e903810305811588170a0104044124652030084000d1503000514254201041c2260030f1080080d25128141071040c0000d6940b00c51ba8611582d040071142e906240d030000035260b94209001c070b90440f18104940544281c42204409034100d81480300da0801c2c0805943c03c40032401c1030004402040d52400c5651048800780d000e00c9000035198000e14407806d11800200d10011002440000c40c01e03541c240e100b0b0254800140480b13160400380405109a14107804044042d20600080c4030701d161038641038500c1e20940c08001d0800c0c001d03021000100a20307181900213142d0181c01155600126140d42d5445d400c2403103500d11030b40c00d254001444030a007150740e43c01140c0c49401141140c480c1e031740329280210411071500d210900c04100102049580c00c03034600880c00356000580d07c27840d0040c028100345085003118001d52110b100700321141c8603141100d500500c50b1800140c030306480c028802c0940700300080c42c403841100 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 185144442 1250 185143192 185143207
    0x60913060c03061401080907170309040906091b08030f030702100c020f190f0609171309060501050a27030f0c081608070302131b202e020708 62
    0x69008500741e5000c1303031010041415580c01100c081d407040b01d15540720f8001b11820000c84106c4e800a20b00441034000350f0307080240000202d400c41d17105010682d1441d0711022840e0601c402130204195442120185580d401d0904005540e20f1203241c0996120210002c0043c900910910150345d01d00c28450301400101501c850003541c4aa2000100105015a441d05855a400072141911003588000580c1c2046c1d4592038810080002001c1070380c00b46c14010a4180ca20521401001c13034444904071103c802d402c2080580031500c0e16000b684c14804100602d03002c49030000c40c41224007040c9410220b035900e81d840048910031103580020440f041d1031a80702e041042d107404241c25950910112008603401c103852505c00c00350780c442c4480c0e40c1c000e29418005400e015000c20103103018442e01081a0002d5107104039024070409440c4005003030600b8202071009804680105410703000d0081c0a1071840c072204041d41007081c4409c1a514010700b04030140680070740c0580703400c1c41d040380102d5100c400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 185145692 1250 185144442 185144447
    0xb1c090c030201021606021002090a05030d0c0605150609040b011b1a090d090b0a021608010507020609030c07060804260307020c1c0f1b140301050a0e06060913060c 72
    0x2590700089000d80611115801e01070440f0f99140f08581d40d0303500030702880c4690f186880096100031109900540040d4010406803010400700d1100180c907502c2c42100f5000b4142901110006000154443c10f00f40e148040c43d0b49190549014250031100050b0401d64140140c40d600040100e10a54803101c0a903a414480c040e1598981844226000c255951322403140c191520b0217a241030303020920700e071814059950050042c021145d00ea00440d074845d4401446000c03418003540c03050459a4545c010054030300c1c1d0501074103800261540040d424000080d0000b51600a203006d8041000554000282071002904c0e220020700e900e02c200508e110f22b09104003507580c0c01280e00301d025102c1ca051940e15030809039051440b800d010701c0d80841c0c90001b036440c100042c08640058400d0714403115880101e0201c45c80400003401c2900001a22009035001d05007910f02c01041d81c50b48514017a00307409140300101d81c03a41d010b40c08a9244bc0b5540e90b44124800d450708011018107050b140c0381070076480c540c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 185146942 1250 185145692 185145713
    0xa050901090c08060a0302010203042607030c031b06050f070302030409050408030f011403120a030e07140a060c020d230102040f030c170c0f01030e060405010c08010803070c0b1c09 79
    0x1d09943d41d60242d81e42d110300740640300b03059110090059004010400100e2074404112401d003c0d0102c5005461100110091030034066400540d4002424801041040202e010316025407100c1e042f990000d900e0311001402500914070461801e84000800204051081c01240c002e081d4214003003001c2d04007414294140e420441d0b24900c091141030001c03a04651030741c1320941c1214010000d0800b441161017542060b0801a032004c181a2110380c0304401642c180016000f0700a5520110304101d25102007201c0d1014640c012411701020750350313803009a02c03100da204c2076060300300409004003060ba41118001c00031010f03156240d5440441d0102d00300034508800c1c400c6a0107006000e00c0180c80d016646000c0440002c0c00c00d0991021007442d0301d6060810300300415840506001400f4030400c0340040c107150088604550596469808103201da0700040d946000d045103034015800c00c074295884040503803113800395090101011507850070468034021481c0c3c20b00c0c060002071201110764a4000d200701d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 185148192 1250 185146942 185146961
    0x515090d090e070e121c020d050a05040e04020a030804031202281101021c08090d0f020a030c0f0f0809040c18120206070501060e18010603020108010e060a05090109 72
    0x5014290845100500c650781c0801600d208080529098952a9054812004e0402c04036000101500880c2410f07806001242500e0b1400d00c1500e0644c220035002818944480c2c0c4031001d1007010300050001990101c16202512640b000a11441c4c03035900028100c0748081d4002400c16a00103008400c0003d0800780580400d8990200ca0441100a8801140707011490050004090b60038a00c00821081c1c40069241d000c180141c401a07030110b0240004400c03030880e600082203180c0d0511070300c8a410401c0d030441414503d012403484a070118000d4450400e01c41c0a0104144600c50340309100c8480f80c582c81e4150b10544031141e002207803518211941050661504c958503203c043c03003501d8000c01440209148005071841030078100000c2201c1c14a0200099030802824401c50740040d00c2481040098410040030b5541440c06aa01c040c00720345003021645a80d0601b841080140d1b049001030b030549011034002c616a540d1040425506003899121541c04203d0200003c0c2c0000f1540c825083c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 185149442 1250 185148192 185148211
    0x90324010803040b03040618060203090d08011403030301030b0c0c0d1e0806060405010c0f0605011e090608030a05030403051c020904140f040201080c13080303060414100902090d0515 80
    0x380c0c1d80320074441e00d80c040c51007820b1211808100080010f101648400000708141101c0d1044500646440080340c004498104c4542c0c086c011400b003054014080300d00404403000810000301000b80070030307201d0006100042c1030003a41404250302c17034120019518650740810484050710403c0b070000744003a41c4003510f242c250358900f41e483c04003880f41c084d003071050201803e020328051a22004480c0841d00440c20340709521140fa0030320002d680c0e030044170700071710130034105030305042500805000003540c80e4000d0300344915128017044a0300c0080140d902088250030700d141c4030b54072800c059409224055408450007075641004c11905201c1c0e0151800351000d0320b00f0403941d00c4c3c92003040c496503003e80d00840101d5090001400540c0f081c8140c980c0080300401160401e000321800002612840e008218943c00220420500f070800384a10900443d40c0e209403a500d00f0040300383c0c1d0313a801d0780b13000340b4400301d80006410902c0c0e161440303419200e5a000f0100c450a11201d014010104d1054a45825 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 185150692 1250 185149442 185149513
    0x21e0303071d0114090103060f030f05011103040302210412210f0806091305070e0103030806040911010806061309021c0209130f0f050a020a020601090e030412080903 73
    0x20408200e0081c9015a1042e1241040010020f25000c550340061000c18109903c4110201d14800c5110410707009600c0bd09420b050101c191805a09450000444220040043c410030003c03990004100b112400350034481c008030080502c0007200c61107107170051502002500c034081c0801035909503003444640d01c80403000506262180c125441c0984a00748000203403d9000f10740d143ca00003d40316000f42d0800a009031074241684c2e55820f042c1c0703a5010001c1120740f40010030505400c0103a055110703000721b90800803962aa0b4501c481e100324000000d0403ca00e03880000da040d00c1e03640c204d407171128005c5c3c40d9601040c1d951240601039840451980032010184480a215407014000d4488203e80180030f00a030365400044100245004903108072803036214500f00400109900c601c90007071407011005640c860344244042e02c1c0000c103a202101c0c480c58408424000d4034080155001e54140d0401540410304c0c90604a895006107007206038180901224a200480b540b02060b00740552103d0364075 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 185151942 1250 185150692 185150717
    0xf062007050d020f06010501091e17030309070506040e04060e100e0706020c04050c03060114072915090606090a0911031008060108070303200a110f090603030a080601021e030307 78
    0x241c42d540f087c41032501003011080c06001ca11001d140070561400d2000d00428841ea541418501100450f40703101076a410000500c0300f19442400000d010702000da85491800340340c02c83c3c0c174110020050025208030b0342c07003241c4000c000040c0715568010002240030b10081084003c0140ca9600324032507100076102d04603403810113003824001c030742c8135110004070941150b481100560b107034402040010b07240314040110342e0019002501070441508110440c442820a01e0700d844c03550003000d0680d282400556407800d0843d52001e46042d0320503400d41d01c03a0344819119010500c0b00c4401c0d04154001d40c20100f07609848886200518840c11406201594682c4c0d6045983c1c4c0b140001c2c0107a5407140c020b41c4046c00807a0050f01030a0302d2541070143c050148122556003420103004a5041707812030b8161100c1c00142c0b5000d87c070410303011000c841c008018107007080002c5c0d60b84104040002401504400548141c0c020301801d01e451a0b2a079201051901280c469910381d40704541240200d50000f0894 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 185153192 1250 185151942 185151973
    0x12011e05010201090c03020108041a040503030a0b030a0507030201030b0f09150103141b0f0f0310050a050102010213140411030c0c1009240b120a0b0606070f062007050d02 75
    0x24001150403810b0003c081b070554004560b4030310b001704141c4a120412108400c1c840040030081c0c40740e401100596140d040100d4440c090303900b07084901d8800c1c0e00180c540c10120740086600c0044a50909001503101d401c0e40c0858419901040c805910070340c0e20701040b04048c50b038034495609030f900366401c010744400d08020112424003681e10304034100100078aa5881d040345401000c628004480223800d003003281071200d031594000c961095200ea4150340c104280c1c200640090301400c804d000950903c0d81450355079803241054420302e090030100b040c1c0400143c80c1c0ea4030000c0f0342d5041003681a680d2421048604440c0e2003c480030b00c05208030361720700c1d0a00e219440f41d4694103500c15050304e0404084040d040c0081c81b907032001d0044990396907410240d82d480010640186004201800c030816082c18401030032200104412f00583d0300704944000a8030094440c3d001c0b50b441100014070401614441044011140010781c52060004c1c00c2c00078090300249020030a02d59a084a4400420700c800 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 185154442 1250 185153192 185153201
    0x180f0601140307050a1806020d0206010603020408030f03130503030f0403110307020a271a03010e15010b070305070503030f060306070f0e0402071b09020a1b02030d0c05010212011e05010201 83
    0x31901031001c280042501c541c031031401481619110318145401c1d82000c40c01d006552080d912040140c1d0101068031141c54051201a0040141d800c003103050a1604d40d040da100d00c600c4560ac1500e442c00070018410018000c0e0041d00726800204598481c9403000500c4c03c0d0040c10b40b002d80118050a0050a548000204a4a80d40c0d400b070010343c1014a800d1880a101e11030981000e02007400000c885a40390062041c01c01040004910d404414100ba00741402c41d00281e9104241d40c0040902034a0703400000074107411940030350b1095544e4041410121510b009451004089000000c14812207003568141140a410200c095845684502000740c407240800606880400c01008005080f440c0603805455224000c80400d40e4007404007104802246c610b4021510056006c909107040c01d0740304120400350449520419284409600040e61b03810043d505881000442e10302c09003000000c2d0151041c00c18000744503e81d03941c603a00d110707580c1b030301e410750f1a0b081d260202c1000946601c14003d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 185155692 1250 185154442 185154467
    0x506011d0d02061b0d0201020301140d0209010e060604030614150103090309030615050301111909030506010b0d0b0d0c0306050901061a0f040e09030301060e0a0503030324180f0601 79
    0x81a000a050740e400c0c4220b5800c000115103980c041540100b0400d04140151000042c0c15800103a603981007240c4007140c0c11803200e509001d40b500c62250b50060300c803050080c1c1561070000c65440140d442d44001400e40c4555040100004d0410000b0303c002244000c2d1580500341c1d140c9289403200029004404541c44284082d0000305c5030030341040031600d0303580b0200142c0140350308040700c01c5e25540402d09442203100c5000c450000015044141e9060300301035081408285001c1106c9440d6444550391010180a54034440d80c0004000b041c45000354010214800060107505446031682401c0540a071075102c10340d405401d01000842c0004180708400545068103074041e0300b5111002d0090080c1c00c44200c42044220810010545903032480b190341c42900094011981d0750305180c4010111488000c02900402d912002440b03180c1d008010340b03900901ba544001030740c58050061442051050303442c0c40e0081c002d442595402217100c0c1d0458410700100c000309045407204001116402c44000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 185156942 1250 185155692 185155699
    0xc010501320d0611040609030b010806091507020a020d0f0201020d0206010b270607140d020601060f0f03060b0a0c05120c03041802130b120702060c090d1b090506011d 73
    0x81e40300c149440385440120714000c410011300107a8021600c1e01ca640560040004100d000d141041001692981c0380d0140030000040c0c04035007840010550307220440c20340403001c0440c803030018042a00c00c204114025400070002c0444108508010030741040c100030590041c01680c0514040f00e00008038030381211184004146400f800060040302d16414415070403401c101a80ca4142d1560369034042d02e000d500400c101e800e001c0307040c40e0b150300d40080480380905540010004100d40d50300701c03096141030015400e02008031210030318110000d1083e50003003003149034042900510b00398004840110307a4800c40480340c0001c2018105d450314062005c40c02d071182d10070081407107c031003a010342404003141d165015080c440549114080100c06820030703102c1c00d001042c00a429048504010f41091450000c0c1002e4101300740a00742038420150310340e0055040b040c400c002c008040d28000050142c1020010899803640d8030310000e81800e030743c1c0e01d0000711605032629002c1903103c0344550281008 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 185158192 1250 185156942 185157029
    0x50f070b0f0f010311060c0708030c030301080d0f120b0303070203010501090f06060c020603040311070b0301030303090c090209130b0d02030a111503070906080a02070203150a050106140d051b0c010501 88
    0x1102003006c2c030350045000c98014012402e0000380c143e01000038040c1c040038040035585070340c1000a90340ca403d400e43e12080030030800b042001e0b1000d0300010145107010314010041032452003480464518812040001e40541c038000000814404650000261003e441070600005940301022148210700c2000a5400501000442c000a000d18400780b100885941961060743c1e441e00000310580003684290301003a11441c0300c80401541400c06005404141c01c21403e041c00280030031408201504400c0c00e00c0d035a4503604442d692000c0c0c0f08200c0c190b00030b08441018906103411114400340070652400344210404510002d040101904d2181060390741d6840b120b803034401e0440b10708a02402d150143d950030410200961001d00c500315114071039500110305814035000705405c49030305900200801a0709020040a0380005c02101c102d4044464003203404d45440c8500826400000c020a125030f00000e0020001c07070064020134101d400d0030b0a601001128000c00c10500a03100542d1403058008 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 185159442 1250 185158192 185158223
    0xf040b0105221505030610091206090203030f0703030f060504020913020304020a050a09140a020a0210050606090406291206120c0a060306090b061810050f070b0f0f0103 74
    0x40b500403141c560314010300d141ca016920911404807507401d40b43c031800160f0010070042c40d8106125034400e091040c2c130704940034901e0030b03c440200c2d1992940c018010340d1601000029940c08205880856210070701c0305030b541940c2c0c41c02400900c0e545070345500441c00c100c9d00090711b160038801d0f110220800741c4139020600b4807034100b00095100500c200c2c2e000b680014049800d0315230684500c068222140d0000386054401e10038000b504004003d0b180c0c0714010490320300d4080c0d011815046001c520f6401250603100c0390b000070030702c2c060b1151a917000782c40c00a0002d44c501c41e09840041901d50300040418803003061746062103620a021142038aa406240400c9480c10000e182d04090300c0800240c1c1e00c00c441c0d890008032081d40c03c0d882080041d0b282c038428011540c0c03034490752400c01c00c11179155242020800e586d41b01d054441c0d48a600c26048122401c65203406901229800790b0310414040c0d503902a443d1103803085009507400c00c0b01c15041c500240c4c01004142040c0d06903604094144580b258 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 185160692 1250 185159442 185159467
    0x306040327120308090d02031606060824010603150e0604090b0703050a23011e03080429160620030a1d03191d030a0c03020f040b0105 59
    0x41d141c00d0312144580e0491210500c0180c02258406055103020000403644181001440d62070003420884458022000940c00c1580020448011100c8100c0900e40d40d0003a05004004003519404640107000d14401c050385408440c1ca1380c16071401610518400b030740c0f6924210203e91104000450281249005018282c401e0b10199070000d0700900220340200302d035a4040c05140140c6a00000c240c44605000d0602424080d02c8601e03800403483c07804080002c1e1041c0c040000621174206c203a04210103045a10000310340c0140a5a00800c80da84e4450303446882841c0e40c050020340f0010b194180f240344600d02d0104c8210f503050841074405045030030f83d03034842c40010300b442408582030601707004018010301440c0000e5031080c2059940006d42d035902d0007440058840100c543c60041e0020000da261005410074400d03d041c840346003190081038160505180d9950040c0d08175418480c10030840b0811420150120a41e8801e0703078143e150035000300a11050303602440d80d460200d44103001d140007052 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 185161942 1250 185160692 185160707
    0x608010b0d0e0d0e0a3c080a05070e010506030c0706150f0902091203090d030c03170a0209040b0f01050d090606030c12030e030a17030403170c0d06080105040203060403 74
    0x1500e040000030002c031801d00b01c42c6046000c1ca0000040b60045069042a00d00000c102004045d540900d83c0400031841100d003d9149140d000c25510407000000520401000380403006030060404456240d0b20780d05207030340d8401091103041c401030900b0f0008600c600b4448107480c014490301040d9030514401d550b82401808003801c00c680e041110b2000016503d40f000142c0b8000c000c030300700051343d400c041c805001d4846415890946540c0c810080d50f241a00d075602d103420040e400d17103130400c01c51241c0d240c110f6002d0300200c2456200c420705000d00111660342e9005103a5020111401c00c1104d42d40800d00200f1b00c040c0c4200b902166041c44015203070712203904441e211a10034540098129120b95541c0d04600c03041e00018062080c841c0a4001c140c0c0104d1000140c00d0110010540d02019682c0c82c2c043c0006484020580c91011010408060156400f02c0d080c18800c40b01c480c0c103190080358a0001d411041e203021415080c4140040c1c2054180308860141750054040c1c01d45540341e40f4285e0360308 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 185163192 1250 185161942 185161957
    0x809100e060a090501080108010b010e060d02190f02010e0a15020a18030308010f0e010f120303020d0f1b03090803010608040201121a090f0601020c010806041d0c01020105100608010b 80
    0x8801a40d0000c140d880c80d004201000302c607180c0720f070100e0900b400100300e10016040f03804642c1c54840b50504caaa0802540d02111808542059594a034441e680d000f07405220b4242c0035071140042c1d400b603600c1e003140b1052001002c50f80200840b480d8004896a2240040720180c02c05440700d00e88407044060350000d010005660801c4a2030140a60784003a5000e115401a4005000d084c01440081942c030116070040c595204520034035410940c03201000002440380d041c4000c00c1d00f442808250080e01540c4d801e04e81e41208010742803031306003114082d1070710040c40c0c1d0000351010142c41a55000b0320504140940009446085a08010013905d81c1c840290041c0e06000943c14084100140c40c01481206c1030300b0007846000010b01000c0c0203001c0c0024020780510140303402000240d9038006040c607000b0034241703070244143d15010040f80003040c140c0e4460000e40d443d91010034103030b00c0005407500060020380c000c00c0704c0d0b030750421013040309441c0e4091303403000829500041000c07018240191020 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 185164442 1250 185163192 185163197
    0xa03080c160c0314160b19120203040501050406050a020f180f15040905010b0a02060a0b0109080d02010207020f0301060e010e04021813050c010816051303050712060507020a080910 79
    0x4141c06484540410340d8aa1040f505500c0e10f9843c02e001c0e1005110b1844008005188074034140c0c1094003c01c01c600031005814015510706040d5056a880352403002c02d0395012000031950303403c00c0e080c9030340130f48001c5400b40d900c641000d020030180415442256256119800311a08045d1111800c40c07281c03600102c040c1d0b105450a039046026525803004440140408520660311032620100405680c2d05074480d40508030140120b881d03554020651036404002100001217441c807a0f80140c0b601c483c2a00040610f02c9500450034980790158003c281e51802140d1f540201600001010f007640c2003409080403010701036004100b450414006150050710060041e01c4a5422203210440030408564403490030702c0300010340b000c3c04818080d001181c5002e1a1802003854800081a2044920440c001c100320000980010100f8800d507800e014503403000503a00204c0c0d864404070050f0400d2441510f68a1074030002c00c9115000203078034840c1561080305107082103000380402104d048813900587c00d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 185165692 1250 185164442 185164477
    0x120a06030605101a090604030809030f03040801020909100f061b1a040b16050405060c0a08041401080a09050616030b22060806090303060d08040b03070309060c020a03080c 75
    0x41d4140200e0340304007800002c0c01030075481d240c9a411490f08003d0100d406150400649a03252514822201078942000d041a5107103600300202e4a020018800f442150101240c045a1501c064000b04451070f0111468150358440740c404648403a00e5115101710102e600328108003503402000f007544d54451070b5920f5440d01c0000d48440620901c405a518a03480d042c104100410050725070341600306e00610351440003c46031840c0906244140d000f4a8480d6201042124415408102d110407503503219035034ad0744480d911040e040154031000c89083c0420314010010703c1080c1c503842504140e0340c00400414a0342c44480c1910000481c01d50800c0070552902c100500685410820184940c840c880741074000c00340b80d0500080320079a8001404941021090194000b4004190703500301c9030407550421700c0b030840e1a00513030a00c210307805444824804020008031a8055100005050061005001d403156007001241c07036404884009010420040105201302c1c02100682a41440a200f286 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 185166942 1250 185165692 185165699
    0x50408070329011e080606030601091d070308030601020613050307020d020a0503010212040b070c0f0b0604021c0f060902030601080f09070801060905041209030305030109090c170c01020d080c120a06 87
    0x7040c2c480300b604484203800000d031000301c007411051000402421a000640420708260300004d80f600010700c20305400a03160010401141803c9105c45000d1119404890849540e80b800b455260412110507015015550001d044604160629400141d0081c047d5107000750f150300304021245100e405a80081c07100001044c917443c00d03c010507000c0c401c91400e0050380740602d400c4404c0540100300a01b00081140514001030050607070110300e0340c0c8202200c00c83e40e1600b02141c0240681070301381015940d01240c502d2019003c0d0f200400e031403110042404802d84a0b14040180d210507600f050010700441c0c0051032188040e000141c0145010007a203120955405809094406c69045515000d43d03941c00e0108104052481d0038032110541031099086185490280513400b0502c60f8021441d01c07902a03400f042074070800d410140c4200000d02d902d800c060034606549401005400b4058420318401c00423160069400d544248494950603160170070a030440caa00d4100a4803a500c001e40304c10010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 185168192 1250 185166942 185167013
    0x305030f0a0e04060305100b0a0f050103180507030b100e01210303060b040b04061805060412060f4b153809061918030606090605010504080703 63
    0x13100860140000b4151402c1c07240c01041200c030030380f100a00c1407052003420000e8050001e0341c0811282c09080000e0300d0300d95a070400000340307a03440b030003803490203400c1c004420840a00c084034080c01203000086a03403920303050042d00a0780280a000209200c59101e54582e0180000c0085510310074540441d000d590350304131201a03000794100300c20304000800e0600003158460349040c03292509503030421a561810000c98641e224034000d101d101001c4060a40c10b22120b5001031291030441e0000300801180120740c0080c1380a03082c401c504238414a0313402101d50494110400030030600100b01ca508080d1080c00b00e00808040c0e02c00c010790103400c180000d007001c62101404100c40c01100ca401e0740414207480d1100c80025100801300f29101744881422500c6103000c0d03a20910800101010044000c03100b41d681e42c3d001007000c10500f9000c840407080100c141c2203c0c0c110f52131000280292501e40c4d00541e1680158080d00c0100c2e4064101080403958070070200841418982d4414101109041c44 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 185169442 1250 185168192 185168201
    0x405040b030f1e0d0203070c03112b0311030c07180e03040b041d011401030b0f061b0624040504030e10021507050304030c0210020709020c0105061206010305030f0a0e04 74
    0x400e110012010500400e0301404d02c100b000a0b000b0384051441c0903c1c0e651441c400d01c1160101410310392410071202440d0301d030000181c0f128906020013a0040403140c141440d001c1400c58218000303072001c403c0142c01c00c0b00209807110070308000083c000c3d4908020f1b41c105207900c3e010508a0340381c0c98a500c000241e80600080010f0400f00201c0c0c0d9441e400c0c01954034101d0050010039640e80120001000700b03c01900b12007240f41c9003440c1c04140850004002039201405460407940030070001740c41d40d101a09a500300c0102e18940301a25400d544c0c0010707102c010144062040446580d19002040500d8075078082640b191182c108442c41501c80000300c1c800180c03071081503002da0700008940300fa081c1c85c8010140d011006251043c030310325156500404010540c10000d001e18000001e01c22a9402031100401502c15400704548941941d0354aa010f000700f6503001340948800044003413031040100b40c5070b050f00c3e00100158070381002202c01345180d9000120b128104003410003002e4981e40c440c0103 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 185170692 1250 185169442 185169463
    0x270314040603060f1d010b0a1419032702010302030c070605040c03030809010605130c020709051f12050c010c11030601150314040c090906060b0c010507140703050405040b030f 77
    0x400043d184d040c0307840046481a150850800710464000030550b000400c0c20107415504440540d03619030f011298180e940c80e5600300c00701c8007110007140a051141c1d441c2540707540f00c005603500f40302002c0f100907443c1d43c00c810315440348610540300d100ea0016500a40045400402d003200031f920b0422035841706011103c06a400725001e8a143d03d0030001d166000e80c03041e800c002c03200000c0001da880c00c00084c00d12580625884a5640c954034030038003460003800240300800401c94148032920389511003942c0200c9201800c1c8410f030082401184160b510121054484e03405001040107148200056a14107010042224031851490106656840a1100030700811008801c0707544001500307000350684241c00e96907000e65041408100115024003920000c507030f80302000145c00032185c100000a02166082002d0315400024035050503101580000e202c0d10f070550300d040100c440d240000d1a288507071080500003c405100a201500c1c10741d01c001c24926000303040300c40d501b0360481321740e09007040c448 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 185171942 1250 185170692 185170697
    0xd15020d020a170f010e07180806091501050609060313050102070503030a0c0e010e10091211010f140306060f04091401080c01090326090d06020405030705042703140406 74
    0x240705941c143c0200d0145845a10302c108280146009180140380d014148164002c2c402c044011480c05406180710b1407552904188645101d071322902c070f01d43d44050564107015188202807000781d5044040040605881e00113159518001c0c580003005040c1d040034010820200c0c800c80309000281e02440107000007440380c805142c807803912000003000c83e880c01c45c00f07c7c02d001691440682c5a0703032042d03060903880000c549006500054400c112041500c82d004910100302c4480b00c02c0038400150a0154401e509989480300c0300c9404104558002c61080450700c402e5013440412610b00c1c0c00009411880380410a950401f40c1d1a54060300382d03000302020300c0303a201c02e0300010f000340a400c2c000280445401c1c20715402071072443c3ea42c505980f510810710240b0403902e040100090078044103c90132048000c0c02002a8007890408000a51061264030301c244120b040c0061141041d01030a6214000c04032060048d00c0132150401805216001c00c50070002003495440714050900041d00152170f055 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 185173192 1250 185171942 185171947
    0x60d0813060e040f050106051207180f0305010e0f030a0507050a02090c0c0d09060f050c15091f110405010f030b060c0102070507120f0210050403050304031101030f0b030c0d15020d02 80
    0x803000d1101311140504850655400c000040c000150000e0031a8900001b6121440c50781c0d40782c51003200c12155240054040141421000070040300203824102500c8c002c41c000c000e04448034800030703940c803404841c2d8842904140b00c44640c8c20f003c0c001500015004105442040910f94002a80c10070204c8606143e000701041009404c1010032207020040220300300a0b0f50607080040142c4075040d02c1c081c080c10820b0008680b1920b1000b84041d2100481844041e196800e2242c03c05841e03c59480d08544030b1014001c902c00c4c070420314012a1403c41540c90014502420103004642c0120803400031801c2c581c0b102e034101495100c51004100c0c40e11400e00058495145103010341c1410002e910111030034101c81c070041c0c040b6028404448090380c2c1212509020400941e090b500382c0500c1c0e0001d4460300002c5000020b1011302052a0000e0030246d0707003040403039030f826035607811610b0a18016070198401c0b11007504a00341001d0744c502841c003c0c0d0f071411480c2508030b0002e0a0303a01c41070b016940107801 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 185174442 1250 185173192 185173217
    0xf0324060f020a11040b04020c01050108030901080702070506030a0207050c0307080115141f1b0303092a0303140c0a080a020c0a080c130b0d0f0201140a08060d081306 73
    0x1001c0c012202011910242041069503201d29918180100d0018465a03503078160040658455048400e0345010000a000645c0e40d462000e0722038000c0c0c0030790ba011840310b0000400c0e00d4804240c1c0d10588000601c0b0906645880701d400c0c000f07401020080715140308010501c0c41981c3d04120080007071038200008282c01c00414107030401610701d94808180c0000120080d581a600c02032847c405004101c00030000307280c981c404540c8401131500780c054060360b00002c0400e140c0d0540025081d07d020f100034003d24600b0440300600354a10441209150061120910010b480350b01030284135010042940d007400511070340c00d42000c40c0c02d1000c51700300d0b10028007a0110768051040704440b20b0111281842980381c502001c1c0c5603046243c03110700c80c0056038000030b001d00303050344940e02c006d0003e04200d202d80103520305910003004c1c424069001c41c1c200c9840203540502d0b1001c607240350f031643c0e9403042c00d901c4102c2030020207444d20b82d04950f800c07002d0002080304070b503136000c840051025a60700c03601c8241 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 185175692 1250 185174442 185174447
    0xb0907080d030204060c110a0509040b10060807050d0b0427050d03060f090c0329120105160e0d020405041203061505040b070f0b010f03110901060f0f032406 69
    0x115140220706040c0140700030030903c0c0d0080700c0c413010700c0e412108500c08021000009410080c0f00e80006500c2000e540c02c0c1701c00c2c00207010030b841c45140d0880303c80c2c00003034450406488040d0201c902c0310000c0c5040201da1041c090a8101480860000c0d001240c0f88028941010501d000149140c040101c00d680240078440d041040c0500384586013410807425013085c101400d400d004d400ba01c51180d827140403e0a41a00c607502031180c0008804149071042144202d800648295000891003042d81c0b1940350368450042c482c02e400781c0c1c0c18168005080c0304040041d1800480030140d030398051050b1030003401580781c9009440c4103070302c46c80301c01e010012000c201504640c142e03001070f20001c04034004146142d400408176800d5440d18922151901801c0c074048100f8100c00c440103018918680002070103c04944100058a1040240e454114019414082580405d00c9618001103402c8280c14285004081c131a598034a03a2801103144600c500401e850180c820041c03514041c3c0d0450200212035 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 185176942 1250 185175692 185175703
    0x31609091a0703153003020c03030f071202070608130305190e2818020d0903050d0b120d2003030405070e07020105041502030a15120b0105060c03070303050703090b090708 75
    0x96241103540c4e03242910700c0404080c14017096141018104c40c002810f00070018001c0441004040300d640c0e280042905400da0000001210081400c1c218040450300200b04501070364480c3c4c3d6104c0281e0b03101c428109424050789030a80c28424108224012305011036020794480080d41c98000c1501241d07010b201944c0c40300905081000c80345555140c0c407a0303007460542d080711601b10313074042c1031405161480000e100700300180e070701c541c60022804201501700c07000c0c1205490000702013100c01728040621a0240d42c03039111941c160411742049a54501400704408a401241030032217802403012181885d43d4420760781078505501c000e90800a07118225450782c4e20030041c0c80280603600340343d0b842c0005005004000392030190084000740c400c9240380d100c0d802c00700b140c00031852a540e50703881c0140308410814050f102d08031240004151418500104c2d420325602800862a01c0301a4030114002c00c4094103540c03c243c0c4922503d4040750342c3d10243d47c000c0d000034026165062415201e40c0c42c01 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 185178192 1250 185176942 185176949
    0x231b07080304030f0210090b030a0e060a0e0c2704110312160b07020f0a030305101502190f0803010b0a030c1107172415031609091a070315 61
    0x140c0c400c00043c000507100d600000605541580c81040514080c60f040d05d0300401500110001040442005032600054104080b40400c103070940e50f854075a500194243e80098421207510750001440e40540d080a56444030740281c0340e131003070000c403400050742c03110074800391000c0d80c080c4000700c0d43c2030203464203210b00100520100c5c01c481c5411a0305480d5000503010980140880c2043c10006031a903000703008603a1030103155010394901250a00c3e02030018074050360032401d101440c2c0d01c0415250000764030100325901075002002c0c4401455408030400c91450011250b0452180404000407400000fa5002e0070003d20143d0312400300040040c201c45403a0080802c102c002c00540040c1440071541c182500c020b40303c482980a40c0c401024600500c298074180c0115009071b140d254001000c1c4480d0240b0704010b0400710300c8569908242c1d0b1503200c0f80c9509042581c00d2002c01420506501020400d44160117a80744108407140c074a0600e041260014046519400709040103e801003545014 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 185179442 1250 185178192 185178209
    0x12060b03190f200306011106070f02060c0a0c14071503020a020c0f09010902071b060818030703050d05090a02040c050d0b120303060d1505010803120f0f07231b07 71
    0x1044080600c004680c1e0002c1c108240240000005c00c103c1d900c24402d2040040103e402c0303580a007003420700100b6900b4240c076410014000c80c00410322090b01a0f007107802000c015901d4400000403911480410801301c2034001040c89030800001d020750040e21041c0420403c0e450040c8c50b200c050502a082c0310007060320511038400ea805404581d6101150b69054540d10000142c5400e854075010b181024004031410341c140350040000b075500d41c400c0505128803c40c05038034000e0500d0b031030165a680244030004000c50000e000340c0c4004281644a40d03403180105088800700741c41500441d040b2031500e030026000500002d44078806e80003501501003607540075205407813041d02d0003c42944070301018019512402076400202c00707000380c0469446c002c036040d080401c02560349612581c0d070303075010900680c801c2f00c20800060100c0b010b130042c2440307801005415407803581d600000b2200b0302e4031030000d64504d40103026805034040700e04020300861450020b81d106003402c10300c0314614105643d8003800c075 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 185180692 1250 185179442 185179451
    0x1060c031211070206031003020406050d08030114010e060c070e09030403050307121e090e10030302060f04080d110d0b060702010f050d0609020f0a09050108090a0312060b03190f 78
    0x81e61003480c12000074031141001a40140600b000750152081c0b14020b548100040280501a0f030300b140c4010880f442100d04001c185d07610414003e50410309440134104000600041103a00500305580c00801014502944090542d000141850b008a14440ca0550040000b400010030b01a0061707080410700c00110700709451959440d42d60312840d00d0041040d80400841a5458001c05000d84041c04900d0507001141d4400801840703510680702d440403ca818801042c480a2005074050070303a42c142d405403145684400c00d0242c1040068401c41707003500c6c00c000d00c0103103180c2442180191803450741c2a60307603103001141500582d8105940e441c8500810010000180e0704582042c40d100050304010782c494585c500e005008181030b81c820030400b80006a4a0781c8806480300400e00e410b4140c660402c5c050310351004541c0c0c00001c441c900307201d50041c400d62000c00d0040003120300714002102c01203000340d00ca9044001c260401d4a0a11a810030011607800f0f054540c082c071040342452a40411 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 185181942 1250 185180692 185180717
    0x50108070b0a030b030703020a08060910050f04020906032b110303010e072109240b101103270109060302160f0524090d0c020d02010e180a0906050106 66
    0x981c0c0c0b240368500d400345030b511001c2c00c410752000e0003200c0003590024015042c040c0e036001050b4441d50210b0740380c0c040b800341028100e600c0895224550141810141c4616150b8441e403c4c00094207000c4c0c2500d5141c07140c0301d813040301c11040851900b0404000e00d5403401080085402910f003210001d19036481d5001400144054050340d00c1140d0701190600e46200c0c910986041e0550034000801151259803c188819040c01030328a0844840c1d144000d00440c000c08408038a01207402445500754403940445800012520a08100d441100f240381a28a410400705150141002129441d600c0d5034a80c0c030603000c10b60704040703294010015403c0c150303c0c1c04040c0154210722204254001c11819000c60244140310080042907941c100100985a04460304d070f143c3d55001c001100d88200c00e114041e10b80340350901c6001c04029a0398090704100c4a04143d5005684001111039210340044070354025070b6596102c090694041c0f01e8035031303001400450501b4940143c45050b0440d0092000da044d0300c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 185183192 1250 185181942 185181959
    0x200901020d02060405060a0903050f0408030316110a030e0a05030a1406090303220c0305030c0a15020901141b0607030f0f0b0f09070e030313170d05070b040305070b040f0605010807 79
    0x11f03600400d081c10000e0118103518080d10603008500072030070511404035011600500000003035000d21500741000b02900d01409086034003007003281c20822150401d40100000030301817100182510001009003500070b032203a0100c0d01d01206681d0070b44141c0c800c0d80c6a604013a0041c001c90350411420070145103189803001e5441c8081e1060700b0300c03071045074a0001c00070620520038028805540d001c41500d0396180303200c6605550f6154217105840c3c07a001d50b0181c0d01151030a2085664040c01030719002401c41c80c02421040507003102c03803007009001e058403041a100302d090107051700c03624003a1000200602c00001210844003100301121140740f900c0340c00070090b540c0704880100000b040712480c1e200d60b11001c0448510305600201e40d0144404901007032240307056603082003912140d00940340000d64101030b0340c3d600c904540688010a504001000c0881e49984900b83d1150103801c00b24940b6115544503400701c94202c40c20b40b03000399075066180c1003000d1350248a004004460090403100d0411840 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 185184442 1250 185183192 185183203
    0xb030103080f0c030f07060b0307050a14040b030123040b100b041206060305010e03070b0c03011a070f0b07080610030608060604020d0902090a02041809030c06050a200901020d02060405 81
    0x82ea4001404912440380c1034040084480880c07440d8240b503100d61052405401401d044030b85684240164a4007243c54103100c4804011104280e040d98030901c005020720004104141c49030350035548800094120b081c3c00840c1d01d40d03048018055a003185040d04202100c2c40001d810041c0019590100b000308604074015282170b50712282481c0f050001e01d00d490402440660b100507d59420480b220018200100240a02c18054110036086989030441c1890b04d1009014804000c500c1010341150f040b201000361041038440d16210b4005082d940710000e808901f06c40d2540000e9101080041e14103101c0c020503007410080c102400f03900d0030400e129031944002003009009039404914145140000c1d04246c07103140c1c01800400050030841415800303980107015200108402901c0c03d0800c1d0020320880300403c0d01a0307201100a000d55542c01e01528000c1c5c00b114980d078494480940308040d00d40d11000c00d0360341030003c0baa01d8542e600064144a009081c9105541001d01080b0115901045 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 185185692 1250 185184442 185184457
    0x207021008180f0601060e010c020904030e0a08010e070f09020306010c02012f01050f010f0807030312020405060307110111040e0408090402070b1807050f012c180a05010b03010308 79
    0x40c807054030b5031540c03240d00e0b80d264001c0b028205031185080b40084040041220782c10b80e1615564400c804c903c640054404c40c4088100942007249100003502281c40380720030614456009003070201c036a680b840310500359405203908076034640001004100d051a5500100014104203c1c1513080d8640309001070041c620381070020381841881d5280301c411b4001092401150303d80b8403080f4400c6030400030ba4500900d0101c41e102840310341140046001c20400b05010100c42d80d070001410058150f42d400c8070007020b000c1100c20080d400f400301040a0751203001540c4100041c2d0345840c5003058114109003546d6041c604051140401c00040c0407106192800a52082d0040c000d42d40d260880381c0454024480c406014001848810900143c0e204210758404c040304c3c1a400c84849076103e00030410200c4c0c82d1000799000c980300311031b0791140c070702018600084401a8503840d000e494041010912080c400c10102e00514815410810010300303d01c10a4050004c0310b01031401c40d0304540c2c0d811000d110703c00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 185186942 1250 185185692 185185697
    0xb060906121509010f060605031029160b070c02030114010803040501050f121e0c03070c0209070c051905070b040807050915060d091e0302211207110d020102070210 72
    0x9000030303c404000d4100740c1c03251001c0f0300108071a80d07441e54001c2158005a0358240820301000002850102d54252000b24010235000c582c0c201d01d0701d00d442c008990000581c880c0291a40c01d400010508030400790384203c0c11522000c0204400d4410035084554a83c2c4040746807074414010303c4035110000956007078500030700303105907030b0f040b0110010802e01804901c0444244d942c010065a00012030596400d201084107507085034a0b21540005580021160340b80043d01004500c4098506640780542140460a096111490644540341001d9400d10f5800c40c00031490540c40801400f00040001450f188034520308250500305141c0c0c49200500c9194881e5581002154680c0150103812240000c014905641c40c210903400714090108440d05540c0c4a60301c01d100552018150b0080d403d1542c198040c182101d40072405400b000445006141c1c0c0030010b100a442d800000000c07030340240201d4445603981882404c1d050302c0c00001c0308048007164010b1080800588075403142550078140390 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 185188192 1250 185186942 185186983
    0x1050604051b0a0504030602040609051c08120c1207082d0a050702100501082407080105060307091208281416060903081605160605040615030b06090612 67
    0x5202c04ca425000e96003002c6e151300c0c80003030009541900032500e4400c030350040d290401034902449401440c100d06540240200808001030100036076001070640d031000c818040780c0c0c104407180703d080e10010401c40d00400400e88500134402d0403007540d48480c042a0482e14581586500c1c001d04e00f407a10800b0300302a110940340c0020841e001d000303100781d200c8004002800c00081d031f980d140c0b00b659000460340118a0b281c400611403800032804046511601054550325500c0c2d10300024090642d00007800312081141c4d22101045088001e0244c4031040d0040307202d00d03111a8641c0c200d48400c3d0281c1451840144c0b1000b44822030b6070040c2ca03031381030288980201915901c60781354001312600303614801884070740780c40b40c1a01055080912107000d013810780707054410303a46c0101c400c0c0d41500c80c0c03c22071150044541c40c20800908580c203e80e034828461000403075010000d05a0f4000b08080d50000c0390b031410a02d0803c4124201001c000e07500170403c80d403420165110881c02501d40201c51040600703940c60 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 185189442 1250 185188192 185188207
    0x8031309090609050f0703030f080601081302010311040b090907030912050d140c18030303150f03070306020c0f2e0504030e0a0b1308010c09061b0b070305040501050604051b 76
    0xc6511550345180c008081e0343c05500c00700450786d180c22550000314042000c50004041992080c8201d511849068485039403d40312a003020200c51400d6108031b04054a91441da542401d401001e08018402c034421244c9442070b4108208509200520702001c1625002803900030070014070382c0c0c2e0030b40040c4c1c0c200140c1c1d802c41180ca88000c8c10b070006004000b24010001e02c60802d4034540205001c50142d41d0280d6080381e4001015228481a1140c402c2d20342042200e400c41d140c0140d101002400c0141240c88142d504d54602d01644c00100d00c140d416040402c181c0c00d01c24041c0460410000c4503001480305500f5101d07a540403102040c24444a6603641001a0400d8050001c50402c030000800201e545039503801016110f50022055140c0d0445e60440003c4401e03050090796822080c940355180401c0c1006400c030b407070f070103400e2910b054500a2043c11000c10804040640150300a50300803540b072806051950a690001d44401d004510344810031011a148810003540c800c81c7c0521565189030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 185190692 1250 185189442 185189453
    0xe040516030b0402040b0a08030406052503090303021005060d0b0a090b0415060605030108070603021606110d0c0518130905191e0803130c0806040b040c0803130909 72
    0x39004086015011000e0100c01d10412440300c511680c0708a03802d10030009114140813400e40c581c400d0b0b000a6205000c14003180e03000d0400380c000c00c0d0741074031000e010310421100c1451440442c2010760124003102da007802856814020300c8020311000b601032200741045004204c2d0b500814401800800b20040030466408598001c2446682c10a85581d180c1c10a8100001e201082c0904008c60342d103440000180103004200392412640340401510507a4985501500694840303001c5008500103045c1800021b40184a2045d2441400203129110900e4030303140000ca03610b0703c154005010050081400c0d0000002500c40e00d003506841d030800d4030811420341c00181500c01344c0204140035814041800102c1d001110300f201740078585001d0201c22a6440034115140140090f140c001c0c00c10004078144c8000c881e121245101d001c110250340e59500c401800c0545c01d0f42c0484611000304140070602040d03c000c4005080e194002d149000180c00228120078454820105025100c0c1105020b220 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 185191942 1250 185190692 185190703
    0x20601090c210e0c121209010306031506030302010b010809100e10180b01120203070e0601140f0309060a06050f0405041401022803050106090302010c020a03170901030b1005040e0405 80
    0xb200940792114141c0481c401d4090001c0064040840c4180310142d141490302e8441c0c11890f40c91040940016000c0c0c5102d12111b40c46039000c10305143c0c9800380080003440d10401c640728450407a400203102400d500e002400d444003034000c2c904000d1300106002c030010011400c8a03d10314419800902d80b00303c62005421700001c481c0b0749076640e15100426034100c0c50040105070300741c403d02040701304da038a802c42104c04001c00b800194050780821000d202441c102c10f22135401150504201c01400c00043c00003803150300403410001c0d0004007009100321a8010086140c001d08014800c0c802941004013080000c40715150051055807504040341c00d2000341c25400034400601b1000f556100c803160500501c0d400602c504442d10180160703100003203840303403083d14103889841d40c0e143c00c86072968004507030140100c2816039202c60f01d24000000586001c502c0820400c141000c030703898601e004c0024003140d4200c1503460081c000c00300a60b1103550f000d000c803829120481801e82407603d880c1090361511 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 185193192 1250 185191942 185191967
    0x5121308073c091505090103080f0a020a02030a0f0203160e150a08190201260402060705030d050907150c0b01120302031b010204050906041503061805061503010e0d020601090c 77
    0x81da2158800f01e0200c00507041420002200030075016481d503120248000c09109101c06846040180280309464480c4001406a0259031040f1800280b040e00028100300180c1c6044403004e81100c070b0300045080501c0146212400c8005029859241001985038064020808002c003802809250f2065443e220b506000c2d001c03a408032014441c0d0407841c407010218181c01170b40899601071400288200024000f03006840284098489486907801c0c40420740180c1d1341210280000c0c00307401e018030200d11400784507881d10310080012a26100d561002d00703402522000c2001804084074021880181c00141102c000e0310840054410034107049045005e0207110b000c2182547c0076500c20810150060401d07201c08580201e125100ca404000450380190200e005542000e40100045000f90303210349002d01c0003605000c0c10740c1c002d0361410b040c040122031000b507010030384450008a06091041b5400401410001d0840801c03c92019556540500c030703a0f51400c0e03d8100603e0301d2403055815504c3d6 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 185194442 1250 185193192 185193299
    0x1a010314010c021015081507021c050f0f042301110a0812180f01061404090b0601030504060608120c0d05160f06060905010902031602070b090607020406030512130807 73
    0x11f4203d40602034401000340c0c0c0d428010700c182c410403c0102d881e00e0b03031030600c4031701625040d1604e20450781c00951500203528010b0050018040042c0800060288035090344004a01c4a01004250000b41140c0000520152150302042c140c80001d003626007241c074054503502800d11990389400032030340d03c3d985030703442c00d022801080f00d0b100a200c01508a2800d40320038410b000d40516020091000320741c0f40c1c0c60302508140c40e46000c03c51700c0d406944881d410500078040418481c1d11071004610340b040e00c240c2070004110004041d40d11a42c28403040c618140e9500d48285014103140c0e9035110200220406001034012204a104001c00b5074002e000070305506205004960303440740035900a40085500444200841c900700c010ba910105016094441300c0c10024101200241030040300e070040c62040b03800640d5000044041107007040030141e03000450381c565944000c2c40084569401c01ea51004a084d844000d0603c114480051515241280c2070b410424480c2200c1d010a0880541a041c050 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 185195692 1250 185194442 185194453
    0x503070203160f05012f010e0313080723060d0e0d0c14010504031d0301060902070813120308011a07060603031211040b03070c02030a1a010314010c02101508 69
    0x1c01d202c0d0358803500445842c00c8004492aa48000643d6046400c0000a101241012031404145100c5540c40300b50b103003130780c000651820040780991444c2d01c00303084e0640801d0020400c0018002c20000880a0034200e0f0481041e0500582141504c000050400b8416040440c1081d6003c80d07aa2103114503980c4d410031038010410401003c0d0a0381080c0c4030039a00030043d0000201245014060703140510b41c595a800c8104801840210044003201451540f55403107540c002400e4072140050001d1a0042c1840d5a54109210103102e0310840e950100520680c8914080b0110ba005495541144c00d880041810940c070960100c00c94441c0020007041c640c946000803050560180c51344280d10b0304204100201030164031031283c0c5029911601d15007540070000075099501c09c80305030302024070250072075940c8400ba03525411b40c010090b40e85000c100407400100148044490070445000034500200700d0381c540c2c2100203444034a0194000e10040d110a80940300c01001c540d008000c0112400781c85 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 185196942 1250 185195692 185195713
    0x81b1f0507080618160c0204020408060604180312050705040905040f05062a1b060a0902040605060415030b131409010c030b010507150219170f1504090503070203 71
    0x10041805032244000074007801d0004829044c41540000203503c8036040001e590741c0e014211449001c004507650801a0b5060140f00503115400500301500044c7c000d0300c01c070301c1d0032814001120140552044141000040c0c5c80220b6044400c50f4031a14809801040d07540d02c4075030a079400e2146500c20b5420740d00d04030401c410b0141c540c03c6082d94921480643d5116152035050307166110700c0130014140d482400346014840c100700320007070401d50170100411600c5600411983e040c4141201d002c2244d94460b00240d0851901d481000c0242000b2500310b424a424850011032038001c1c074105006043c1e0350500c0c100300c5da03181801b005a1006421044c46420100403900300c03000350030f5548100543c00d12034035407011fa00a00441c1c5803c28103a44640c2000030940390504054134111042140c80d03801c103c0c7d54605609510390039090581e03522503130340214082c442c010b000326000b00080801d480e80d4041c000e2020b0b01d60048828602c04a90100b00d071420750504500b0b52040b01d0000358107104020081 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 185198192 1250 185196942 185197003
    0x30210020303091608070603051503010501030b150415091a0907020a020a050f06030c0d061d071214060112020f07030915030501050603040605040317070302031909081b 74
    0x452154031808144c4003078000200402c1c1c5809040d00460b804c0b07801203101030004034480d80c007950780070320403046034440055001c0c00719003101d00c282c0050340d0039075030a0104044c01041080003041d6500c00d603400c01c0b81100241c2041d1601b0101d000c0c4d46215034841c9441d034072160071a1050b809064004242507050b0418180c040c1d9100201c140c12400740c0e80c4180000b480b450b00c17501e02ca01c0000301420341d40c503603a02d035a58503034543d20600d0110600f035681c2d03c02188119040500d01858a0f8403052201107042001d0043c0c02d40c10304510401c0d0b000d003043c810703030580041d0000698201070203082c10340703080c000e00c0c1c003000180c000e5502c0e00390410350114640e011726a0046001048403807a651041084142d008214103407002400351640091040012400150341580107590040c024030340040c03845603040c045100740c2010740707030400001d03008810300500240012040c4501420480d0400205c02c40340d864003000e0155080000100e014004000c000c070700244001c800d25002402100c1b200028503c11 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 185199442 1250 185198192 185198197
    0x2100f0506031209030d2102030412080c0a1e091805100e100e04060209041a090907120f08190504061b02010c020f030309030a0302060103051903080708060103060302100203 76
    0x500ca031240c07016010f4603580d0641110000c0102030040c04114580e0201900c62444070260120741c251320aa07075150045540c0f02640c040c502c581030f0001003400c0b40c0402081d43d04054166a062107041040e01e0540f5045103507001030203000186a1030b030240348030701a0342107001c0381d114401d4800da0001080d02c5207025404035102e5106880090380090702d442d86561a004111100500c2c8002000144411800104181d85c40751161102504e0f11103c1c0c0f010038159400540990306d9003518558601c1e452604515803035015141c840108105840c0140c102032140e01e80b04041c115281704c51444050141d03880458002403106180d000d520030f40132074018402d80c054464140000c0c98100c24045a014000100e07450300d40513503821407080d07c0c64081020404420415541c540300411001010361418031194084501940151104e9855410310609040740001e2244090006968000000c0d07003104101c1d401150628200d8a03c0d6038901c01a00102103e03000a580300713002c503075a00b102d07d900000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 185200692 1250 185199442 185199451
    0x2030c1e070909080a08060d02150307031b0e130b150408070602010c0906030e0106091514060405010f08090f0307230604200402040504050f01060914010c030f02100f05 74
    0xc850490741d58003621802c803003c1081c010610300040000d141c00307905c40ca001ca604501c000f0b145022104042d4005000100080f000548122003c010803040315010322800300041e2031041400290281284001c24140c001c0f0040d40c801c0c43c03001209052036000d0350207030082c401d000c0d0841c10f04d90080402504bd603006881150301030f205003080850018810b00400d45c0040311a02da6113112418250158050240307510f00826966a1f2400040d4607440ca000340c8030021410082443c1007820118010f41d400203141127a03005d82c20400c0100300343d0340e00030f404410307024940c9004101134440b10a22818014070302d81d04001444041103c44c10b0040214050b00e004022689001d00c10310384203041500c1d1001140d0180132a68020240a60f242007015201034038080180010301e010f4880b400201191420303207070003600c00c1010006111035600031416401400c0e00c0c3c03024641c00c00081000070903140c02c0180003000c005030042c80c030703450600030421920422070f01c103424030400e84d804404000500d0100c6 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 185201942 1250 185200692 185200753
    0x5011107021e1806011e0e011205041703060607050105070201140603010912050d021204060b0103060816140111030712083603040f061d060405061902030c 68
    0x1c0032540c5206924a032102c2101c080c0003681ea00c1d010080388850040000d0606040c089030810340341c0b41c10002ca00f41100602d00d80c90ba611001c1000700010311100d5407079010040e03a03180205100100d5414054445204440e04825550799a602c01040340c6020740e0340014003a40c00d18017404007086d010742000c1c1c0709045400d0101103641c2d9101c10107083e10003000001c0e0403013007040700c1b445056102e6001407420701d07450394003d40782c6440741d01c00707404001d002c43e010b03a042a07a44098086030b6a16008180081801800030051401808050408280180700f404541003981482010f940d0252a400800740300107020380340c0340c4a082c18250781d007100c00c02c1c494000918510026481300d0141442c0040c4d06072072000c0200c0154030405a800d5095034048051a07844188000118050b12540c204098006c0d07666070814010960f140d0f0341650786041146104910606c0180604c2d110328094a07000710103012250020003007000d0603800c502c6102d100641b5802154045c0c15460911258104c000103482d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 185203192 1250 185201942 185201959
    0x4030e06040302090406271a010b1e0c0709020406030209030d03060605160c0b04171002030c0f0d0f051302030601152f06040605014205070501110702 66
    0x10041203080d208a01000754015001c202240128280740c0c17100fa002c4c1c0d420011902c118001907050211106868021522003900c8900102d991000c06a018014010500766a042a034555109505148901c00090900c040810030b001c00b078004014480042414100840d521038440704001c0c003075404150311900a110342e0b4952440c0134468030814007220456a141b500b0800c164490b2543c44041500c165041d014030440414191743c4400103000500701150303440c215078200018241404464160081e5a40c414402c01c05003517000c004070387c1c2030101803038040d07030340c0341a0325605001b090140c421700c0d4003901d4502081240980010660030b854003c504441042c1e9071a03031402552440d020b0818001001c061500d11b025a1081c8a00001d1a0740c450620054080c0101da03450000b04035400d03508262107000401008032a07032464040c86606000300c111001c0000301e600c000861075045510400303010b0503004800f51042040d524950383c454001d210311401c99180c10840c1d040101c0691042205 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 185204442 1250 185203192 185203217
    0x10f050705030a1b020c011407060c020312010e011508091e100b040b062208030c030403060e0d080f0a0e01020c06010503010b06160209340e04020f0405120a080c03030403 75
    0x70071112034000c2c0c00690003800e046c60074000445000344440403038441842c0c00d1100b040080c246008141000006034001c50720b48918503070103080c03c4010b82c8214003c01d80c01c0c005003c00461407040d41c000c4a21070070206d1240e00d411420b20b2800001c041c07907081c048082001000003440100c3d100c1d03d6010350040c1840383c003440c60100000c0380c0008252583c003100400c09450034408103d41e00b407165041990030034050742c0c3d032000c071402e6520055004105030800681801040800e1150100b5200002e005040542908002400c070440103007208014122200000d00a408541c001a104252100003503450300000c0b640503954070303028001c4600c00e50810008001d58100b4000380c0d0f04062580d0483c00701c200d815020b1005c10603015090620200e00395020b40120106e064440045c2c8803400c1c0c1d20007220050b13920060110284408940c80355004100410b000c04501d07098405564084901d014030300100c1c24842d20309007040400070040314020a541b01c48002c08005984568001c2d1242000b6211 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 185205692 1250 185204442 185204471
    0x1501080309010e1003020c0d050301080601090b060a0809010b0a09150506031306090503090a12021f05071407050901060f090b09090a0506011106010f170105130311010f050705030a 79
    0xe44101c050004400b914443c043e80381c01c83c05581d146010b800d005207840006100242001e81c141d00e1200800c40c00001000340d4481000340900426603043e04100110100c800940c2d81d1203a07100001c20045c080d004200141d90a621050080c00000c0900d110b060b56442c4480162042000c45020050309440002d8981450b10840740701d580055101071140d4001d43d2182d000303020074002540c01c1d1005005113046900d40b10001c1d170140c0040313014802107444620400c2a00ea0b5080d40c1d40c0303000054014000701050300031042e54070040e0300044804c803004564001c10714015180c0e012990002e072a000005125070080000400903045580c0c00c0a003c2d254440c034102480b8211800c4d41114100c1d000690400c503940c000c40d00410b0507d080042c2411040c0d54500c1c001080e0081100442507440400c489000c044420320040c80200c000c0c0035034034007843c803100700a034114405010301401403000c0001180a5109061915030340008100c2410b200700020825002154020081450800f00d883c5100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 185206942 1250 185205692 185205697
    0x81003030807050a02010e0706030e061f090c141201030201080903070b15030102090d0602043f020d08180901120c051203071709090112030504060f0509030d0215010803 74
    0x94141d00e45090355102c540c030440e02640032114910465503610080564080240084001403480d917802080c0c2240c0880fa00d0304100028241c0003442c4645262120381800e0107100d82c00300c4400c20740008420000e003000f0785907000c400c181002c2d0700c000010b040070186042060a41664002c1e03035003000550350700582c0d81d03580c880c11030040d141201c46000500941c100903607070103219a020780058207051103040400c1584240e510200d40081d0041400c0c8103260811040c040c08940e1a21071104640004200001403203c80e40c124025801000c0d0f9035017951242c01c0301c0304800b64882841659001110601d4811103103281659110b004207000000711100d405201c01680c9403c1340d40c1041491602d810019005c51641074421240000e000d100c002c00c0d48a00c100318501c0980c1c040c41c2d540c2c0345580c02c2082201058000301803a0681d0080400400d902106440545a031424000382112000380141c07030324004c050806d94103100b0145103000c0d417903010900d904080f078407402c0b0300314a9803200c040a0700e90 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 185208192 1250 185206942 185206949
    0x30c12050f0a030c02042a020a0615060e13110705071a090906010822080d0c0201020f030c0a03060506071101021203060114210c03010602070603020403030c0b0916150810 75
    0x18103c50051405446e05078404000364442c40c009400b400101c800c04041400203405090150700064250000e000b91409103403c001040029051036074100000645900c5c0c00b400c40c130f0300034030507003188500460303859001c0c1c8810340500d1007041c0c840000d03181c91595484140140f8414103004407000c3c88800310740f01070300d103103034001880c0d11350580c2c41d83d0044824880007000d2240b040d12544020301c40d1034414007450740e001d001d03210b03641d680c054001046099441c1114030400f103a20400c00301c080b1382c082109030f9412041084c205030741e918455104401400141e00300350703072201001031500704006482d00310203820502a0280c03141c04100b9201ea102c0e500046a10a0108036510b80c603c1e1250006802084ca40004200321003d0b5648101012442c5c2422a1480d0b01001c00000501060340c040109030001c080c2441c00358682400c650f0000c051b40407140300104801c4248021851b0f4030400c1c40201d8045460610031449550b858845a010208000fa0324004c03c0c1d4130008600310103182d072a40c0054 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 185209442 1250 185208192 185208197
    0xf031103030f120a0605040507020f010506030d0801061b0501060b0306040b040605060409091b030b07180b040e060303090405070e011205090a0206071e0f03030501080d1d030304030c12050f0a03 85
    0x62000e0301c3d035108a45540142041d03205036032403601081940d51441014040c0c141e03940106141d4102d10142d500715440906424403d0b07001080103015158044546070541e4024a444400190140c5a80c6281a40120001d150354280100411410704440c05036114200c01c03101400440382c00d40c14041190315038050260029020441403001c800c658001c542568802c0d90048424110011480c2220245810407103951840e1400d01c142c45900100901130a134400c40d9841d44d0914142170600c9a00c00c078030841e44200041c1d00000c45a44c1c2c140240c1d010042c018100b404189040003005000a08407040c9501082c03074003240f880d40c1c014520559100b007140000615820140360200800380d0001d080840c0c009a03420704c40c194190400158000d024822001c00c807003004e151074046c060f01d00c142c2058044ea80004090305405500024039130302c0303130f10005031701040351222008a41180314503040900758007242c030000140c40422510f50500a40542c0686401d45e9401c1c01c200d46409108001600 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 185210692 1250 185209442 185209447
    0x10305041709010c0204050a0504020a08030f090d020a081f050a020901050409050c0c0a120f110c13020417072603041a0405220e01151806050402040f031103030f 71
    0xc145507981c00a2904002c141454401090103030b00103015030b10202c40c000342454a42050000318109101c451000d045420051400d200401c01c00140a0050981d00c0d44030f1140841c0000035501d482078188068254442958034041c140d609401c5001c480703410704008c0e185030000081c170903112442565491746050703444074a064607201121010f410007034201c90800a040000c003120000811951003503d10404030302051205950000d40001c0500341c2c094207000c00c8110180c1c1201c000304848444003401c0f50240101610031000200900a03604220704022800504449000d0000f840d0300032200310701c0c040012103030201510410724040d0030b8004040e0f4020704c0144100d660040b085e894030014030b00040e003000d50b20000030f40810414000148289201545a601c45031180030750041240040000d0000485004225092000910036a06010104404408914400d401c02001450000c1c029074a5940300c10300c40d04c401c801c0380300c01c603410036518080d200c05050204c2994031420360452404d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 185211942 1250 185210692 185210723
    0xc09010f081f030b04050613020d020105160501020a020a21020303070c03030b0301050a240311010e030709050c03060a08070b07020d020103090606060513050a080d0c0f0b07051801030504 82
    0x850705280a80315400808102800b8401982e140c00702000440c003802e40001e090900741056810140d01900115400706001000400758950b2130700404001c0d420b20b4925075902c2c05003945400301c2e03003455004009500000f00101910b500084003166280200c810301400080c0d0602400810b0081e10154091380050000130f009502418034400064001d0602094018003640084e00311541200c1e01c1c505182d54950242d28550882079600306061078596040501d03046845010416041c8401a4100865080703082d42503142401388800900000006102508041418000f582c008403041409009101390005036039200043d039208072091004030a181010540901140124010082e41403603140e03005900011642e21540005180f00c0d640c00340c840b4036103607655941107955030286200d0015010140322480001c500c406c0c1490885c14010141d0902d444e010152400102c00900307402003400400c150701d6003200061043d03108030050303001458018030054044480030307030740503060954000009c0c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 185213192 1250 185211942 185211947
    0x1a070203060a1107050703081305060703020c10050c03190311031e0a090b07090503161409061c051513030f08190f02071205030606071709060c01140c09010f 69
    0x1110140f10550034524200311921040c0c944400c680c4102c03402c11001542006002ca0b2103a40b60183c90100d46041c07400301983c40c0207681d24600c0b2209442000d4013426411031034095021030b60040b111000381d80d200d110f0890b080707507591480700035100800d0078000582c102503101c0c1c01f01c0e0720808820f5400d40c1c802003001030200c4a050000c7c86104110396541c440d901003a054610607100307603586c5d9100c2861030309020505040c41990640360003e160200c0b0148259004081040c0000c0029100b403d01c41d17072500d00003400c0c030040340070507401158009044428040041345958600603100c070700040c140c0700c0c0580100000380c01c100160003d1112212000024850700f12a5001459250310142850490700460100d5402c00e403601e0640b90b002440004000108502504441c11418264110328007040820302e18401e000004044c0340014a52080740c0c0f003008180e9440e4070015000782c2e01c62110360000b42c001c040e000c01004a074403014000400704050101104d09008040e52030305400e41c40000103 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 185214442 1250 185213192 185213201
    0x30406050d0b060301150f1d09060f04090b01030b10030c0303030906090c0803270109120c08100207020405101802070f0f030201060e0108010e0a110303070c0306061a070203060a 78
    0x1807500540c4400415040d41d80c1d00c8007035800303071002410304a117892601a015229040702d40201082c4800e500840042d5808145816400d05084c1c4510f25240d55403400901e030140700c00005507002d031034007482a003442200e064841c1a85d03c1564038120688a4810533817070304203607100003040410700070300030700009129420185c031403841941c0201d4582030343d40d2a00030050068210014642c408110501100080760710000d8004080c0f1040c03a00d54500c1000a01044150103032855070750011150000304192200b241e0028031080040d03403944500c4003810740282d4010b84042c1c6c465420040495042c0861130040c60407110211000c2d510605c00d20140c8003c0d42046405031058042c004035840440c00c07200b11944050700c6a4000503005041c070b9416500d205040c2c0000600b60b241c00708501c03c80000203511900c49820032140e0b040c070007a21001902e14810303414014150031120400004100c010340014080e00c0790f5241e5445c1011003440501c0c100d00564a0180d81988102e000c590100d4507a0700 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 185215692 1250 185214442 185214457
    0x60206180c2701060809010f02280c050303070206061021050a060308071a0106090311060f090301091412120103080c0a0203030f090103050708013f0c0504150803040605 74
    0x5214440d000e4a10040280b10703426801600400d1a20f010040802c0707082c07280b05a00c040940d0214280101407000110b00507148003400c54851030700c42c40090385c600400d090781040da1701200b101d41c0c0303282244000352205000c2d520b180c026522010007900381c40c0a4401c039070105040591005880010703080700805824043d100c03141c0291703580b0010021544500013018034034054662140ca080003ca14124542c20513481031041244041050000030410106640c0c1c508085030501d8481042c940b22140501c80c0000007a4590b10708102d82c0100620381d1940400c11812200351001c000c0c082602448a203d0140540804030b124070060001036960005400c01203200404c07110080f4503035000c245140e200c0805206010004240400b03950703458091261b01071854542040b09501d4101e021711a04c02400000c2011480301402440081d801c6c141c00301c26004000e400d10245009040c41c0d0780041d01805168051804c0261820048010060203400c4614540c001c40c5032601e8540f00300c0fa01e410000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 185216942 1250 185215692 185215729
    0x90303020906070609201e0f09010e09010c080c0901121808130b1204140c061b06090714060c0304091505030c03010507090603090c0503010c0801060206180c 69
    0x100210071600d40c440a0000c2d1882030310001a04038403420700034a104d81204e4000144090841032121585400c814168a5406014404118030364200007904035214030440c190002701c010000604160796552050140e0301d01c4000708941c200c4150704030b44103802100c95601c10321082100c02019403207000308510100d50b040001900e030f8903a850f918614034401c0c00544100501055840344007035600150300c010104090f400f4502606100b0340030404a0042c4058160754070b5100d0f00d648183d09001d00001110020212030381c4940d82d580c01058401032603803501480c032900c80003e070312440006180040d0354050899103402c025150801c00c1c00c0e440942000554042800002484d903c14080c0f22501c0a071503031a400090b041c2030900d45030018803100c0a211344c2c140030500070b0441c0c00081100944d0070a103400300b4002004c2c2001d0250404c0c541c02030303401d0361030b0001c1c00c1034050b03216030614181c60756582a9003143e1100101880c00c6104a068131000743c01407005d1050b64580b01107003500170071468 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 185218192 1250 185216942 185216947
    0x1180b07020d150b131a04020c0f0a320c060a11010905010c03050702150604020c011e090c080604080301060e040605130614040e0304050f04090b09071503020a1209030302 75
    0xa590781ca000c048100c0104802c25110045184035240001000381005c0d0030400400900f1010025a0042420382010328052070340050740b40300300c801c1440881a6507580e5030886920a0152904000c448032106041949006a40c0c0010b62001540300c035110820103540200a4070321124100906036004102c0042401290755120309119800e0003402c8500d4010313800003c1c400c0359150060261030000700440c0c00c5400820040a8011003081099049201a1070068691208100c1140181100c0a000c40e201100b00380102008540c0d8201148062285100c000880e030303100c0700c099559005450080c8581030600c018032007030788201c1512130545401080441c4280c0c2c1c0f030010031108001030b1040c0aa072500c40100b81702000c1160000404d6040a0324200300391081105042e03140d000e5800782c588200c141c0d480e40044c5607216045045003941200a41e200c50030840d084907640c8003140b06403200024118502002c1c2e0b406882a00ca8514240e2505040041644984070040004e203600700d050590a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 185219442 1250 185218192 185218219
    0x51009171507050c0d0503160c17180411121503070f090203070f0e0a0902030a06090203010b19030203071704031101021c11090604151b08071101180b0702 68
    0xa5a907003405980107031905981c40e20440022410140c40c07002d20000c1c02800c20a1014115107032031004150080e174501390f0000303903191502e50794204030303020b904404e4400030a00c40948000c0c00400c60000740100c8040200d18500714051101c1d01503220301c240f90020a1000458140480c130300140503520060640f50025202c80120340e00e0f14107030700b02c0380c5000c1d4084100561660407400d03e5401c1401e82c107011803c104844005446d02e442405100310300354000c0081b850b4080c03036802a03070140010746000c2d074a0f5078582e140750089070051403140390820402c41e4600d000307a01a1080b01d01071100f43d03494412070720103010b8504101c2c0e0040e000703c0c200074110210401c03990f000e1002d03010400d03144410b0207007580380580c40d40079589882030f0042100020401c0740303655a201d800f22012114049080d114010840c8002e55050390700301d00460020b4104880b503c20021060000c0903030500c504001000881d6007801103030380d0314003080584100b01d4415402d202507184140a040c43c40d00c0100b03d0510b0912 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 185220692 1250 185219442 185219473
    0x30705072c0105061b0118050c100302070c0509090c0d0615060e0d0b100b0a0801030204270206090607080403050a05210306060304020f180103020a05100917 69
    0x30203a000141c82140080032040c1d205031040c0c50340800c0704903500744080c1e504010000e9454031801c00020b4404c240c0d5130b041131000070203400004040d14086400c0e80740c0c151904001c0e03203485a001c916440340742640d043c0311074540207109448420740c00940504405080c8814000840e0016000820078440c41c103c40e00e050b030390000042c081500c58080854103060442d4102e0610002d41c00800500401c640c81846136101c241c0802800d5400403213101e80c644401303031072011030071040d0052111840c0000e091039910303030000e840d28103e070f00c20b4a04010f180034201c841a10742003200007100d0074801c0384c004c150151600340060111030200906081ca1301402d0360741e0114940c4240e1044440d0b80008400700c0c28400244400000c22400ca6400d418404010b400610749100c0108114440c1c0130110104003551545e401040000c2c0c0080c2201c42c00c1101800312860780d000c00d20089206080089011505040141d40981c1c90040354840d4890281820050f0911421800b141c004902c00c1900b100c0c0e0010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 185221942 1250 185220692 185220703
    0x1e0310030809040626010b0315190b0a0308070c050a1401111612020f04050702030d050c0f04080c04050702010606050d0b040207021005041a030403090e070c120e0414040209040b09030705 82
    0x514860501800c1d4032041029030942c7d00c003104151094015100030100e400714900c00707684c040c6150f20203610480b01180e00d9002410295241600406050004010465020028010107028400c54131032141c0da4001c00400176090302450343c0000055002d024954020510099025504019100d01d103841013450214181240d0240520908048800c8203500b86520a11501e050a440c140081e180525000c0d549100f80c00360b45122a030b44200082400ca03840d000d1310b112560101e022542c4503503e040c00d0b41c0e41d11040603058860b03490000850300b401c1c014071400084031641d4030b41906118a0301d46040003400f00e11007454001e40c0800403000103946014074103901031401c1d1121901c5c3d83c1096105007000c0408140f04080540c104203101c0407a03000f0503920304075006006c41e005903580d200e00841b50380784d0181000b450442410740700000c0d0b6400c2120124081c2c1e00b540d00304024464407250b000171006c10b0350042c5d04a03202d6000b01740440c48002605908c180500212881c0103050740d00c003131805 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 185223192 1250 185221942 185221979
    0x405090a061a090414040305040506030408090409060b0f0d02010f050904240e10080304032307080d020c0904080a0509120304061718071404060e0405031e03100308090406 75
    0x81c07000140c0b01042e2806106120606145c02c0c42000240303415640034203144941e01a0611070100880020308019240080311140c00016005000300255131601d18007620b074445806100351303c0001507018606061400340c0c0756540594030640d18116541c81540c99900404650b5081511100c100e0322017000300340d1140b09021500c9180700014500085031041d807101800000314900c010804000e049800400d503820313aa007010035440d54040e003e0b0358500d41d58846c2c05105c41800b965400041051010072601c40800545e001e03280d821441d80f0400c502d4503c201c4006109080c14090b03141c04d0307482640a00004103020f441d401040b81510303141e600d0741d04150300c000d000401140e42c00801072034492440e0780240c01854134190709080c1c0c0c60202d803510b60b103000f189410250030b4142c50050b601c6802800c002c0a00d82e504803494202418103c1d203d5000d04094085041c074103481c0081c402905007140c0c420a0002d0381d841d0300f141540d413004220760140800c0b9511948454010603888900e218640d882c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 185224442 1250 185223192 185223239
    0x230f01020c0612011e12080f09040914060a0b01050414010203040b1209100b0315060f0a0905040b16091503060e0126160303030905010f020a0c0606090504080405090a06 74
    0x40b5850710813809601d17030201d022030440c2070840f04204400c4185d80400c100103030340b00d0071850700d0b408805541002805000d03c1a584a42804490028088011100c0c0300120100b0255065640c2c2c1480c008180d0395042c0301e15001980c1048100112111542a41c1100d40148103a0349020703501c3c0c9000c8000d4024600e4132406840c40418030100f10001c11041a035440714140c00e0104143c100002500e649003c0d00607420300c80d07140c1c002880d80c0d4820100401410008184c1c404c03a545030401000103010071102241c9a40c82c0b000400e80810704646441c0180495598108007141400c1d6105124094002e54500b031580714040130400268110055000e0200d083c100c50a09050583c1d0020941e8203600d444c2483c1c00080702c01c07640c4090145a041603a0301810301242c0c0900c03502d481380c01424a85011580c181c80070030081e2000d9480b983d40000c4a009280a02940e901c07000c082088a606a80c000d000c81c100304003c104c0c0b424140001e0350b00811411002601c1c941c0c40174060840d954103100c00d8103 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 185225692 1250 185224442 185224477
    0xb030c2101060806070f0f0306090e01090209100e04021302070816050d031104050d03050d2c07051f05090307030b010f060219060216060606030203040606230f01020c06 74
    0x80380000348a000001c2c101c1000400703203810407407030140401041781164410041c0c50044403010a0203500000d00910416004200450b10348040303a000b080d034200204c0c410b120041c0401e0360314000090840a6030899a5074170706a0310385e0f41c2000400340c80102d52461940d000c0c400310020411613406030414010106c130180c90238060340b600d2824441c642860318281842d10290302c401540e442c094a05646059960500c5151281402d984901600c08140109814100740c11030248801032020581501641c2c10862591a0303030003a030301c0740150301507242c2050b0480c4c4080305641e125000420f140c0c426041c014548a1654046070a001c03054005440752454000104a28090700035440000e00300391010303101e03001140481d45402e0000440141201d9000701c0c100d031501d02070011105000b03600003010001199614405000381d0002c40307040d90180c0ca0706d2000522000365106040c2c8a0003030031400e0042c10301c43c104106e505080007014034110f11582558044030f17124600181006948084842c8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 185226942 1250 185225692 185225749
    0x30a050603030a08040b1306020d060509010b0f0304030f1e0806090901020702030a080d1b02010b1c12080c04120501020306091302090109090812010306020d0b041a040b030c 76
    0x42920406418035009074020014503280550008806401a506c0001c0b00400e880310300004064403400d0101a040900c0010446444540e42d4041001c588040d00e01078811ba81e2496144010300901607a501941410000100024440c0400804040880c145114000300c4003a40030860242000003001050072581444942d1910008203588880c09400070351030f20550354003280d2101c5010301c0c000c1103500081034501c032890003500070035841d000206044484c1039400310002e01a002ea0000341e80103880740c00c40869001c000075459015103801841050003250b40c0d00e0100e5034440c00a001340180740d0180300118a1600a404035072402d401080096102d040c40300030040c000c00041c0142420048144002c4016160040c201e0b045030503003600010f54401c035082c04102c07445808141900c0000c00000801000440e07405000a001400c804106543d0190305010407901c09102c182c0c629030915548421916060700100c2e009034000e0b058440c3d12101070041040b840030714172030500005143c40c020 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 185228192 1250 185226942 185226961
    0xf0c0105040c140d03030b0619020a030806011403060603060a0f060f140c1e0304030209011511010b06091309122309010e012a050f0f0303010819032303 67
    0x40d005807061a90f41a190250000024440c02a0000007170a064448405080c0d0307a55110a80708294082400340b1605500018029260360704c0384412004558408042042d0b54850f42c0b8400d25041d10070203c82c07954441e0b41c00c210b1039400081006a108515207130200340070300e00044880c01000c550320f80c031b00c0e8070305884d5020f02034005c0d102c142d40c0700200510000d490707440d000500f0b50061400c11400700011484902e07460a510a030f40010350800e40c4400001074071072120190307401d4030140343e540030074002d0803921140c240c038614910f495002c1014002106030b8584043e500c9620340d030750035001480790865a107482030364100c0681c8601103809510b5900305001c03440066000c80d150301400f0b03490680c0b5640081c0268048000c4581040621a1601e0840601403554810403d59152006400e1a01d10b411543c1d4101c0c1c840800c95130145c3ca0940781c03403000010983e8160f840c1e8801600002c3c100c401001c4004501750012790420040d101c5444400d4503851080c0c840c0c0713540e203525594903e441c0520 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 185229442 1250 185228192 185228213
    0x60305040f02040e0f2506081905090715081e07122910050d0f06050d050109020a1406030a051015020723010c060b04020904021206040b0312040314030f0c010504 71
    0x904201041e08104955408581d040407000c1e64001d088c00311980d00c4e00c107a9500c44507034901c020708601d0703e0142440139a040008101003190b64000c11005580941e50701260f501505a0b010300e0f0520741d030240c100c0d4003520f0392000eaa01c60031034641403540240280c04081551495103144451400f00c440b1403110400460324803d00090903a00504e40052640c0020203501c42c400d41005405d6917484a0150f20019800942c01000000c2c4144040d14250811a009240c4034404a10032120040b00040320204038114405590b4014107850031544e4406401e40138040060000f80301040042c8046001000e10140031110550799000b0043d040c1020840d192003c016070f04503418a007003100c201c030141e902c100009000d40c0d01c0b0388080760803d0a040883d01902071740000b16405800460744014011079685002e20400040794203020180b0362000341901c4481700c0c1100100180c040000b4408070360640c24042464004c0d1044a1034200725100f00c400c02e40000918076441c3c0d4562041c80144405c0704c80 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 185230692 1250 185229442 185229463
    0xd02011d060a03050627131a1608010503060105010c081309150825030602090f0a09020d1b02030f16150501080d0e0307170709050108011d060f01060305040f02040e0f 73
    0x446e00300d08074040c07000c028180f03004043c1d500e0741c4c0b001ea10a400704100b0851100030000d0a12040480b4103005d4981429070105020070760001d600030000088618000422034100c0310181c5031315100e50142d4540740c4103940b00284580c455440040000b49080941c803c201c498442c2d11010030300e8030306140c40141044108040d410b807004d0f150601d41130000e1008801000c80758030400040c1c2e50b5603c4404114038160401d10550310020014000454403016001004e0208102108020007240e00b0703209004240390714440030040c0d10501010703200c000c418008240c0940711f0f80321800307030b60300e241c0e1103040d4041100c100080e01c58461004005e01042040080503411590500d00994000103001c03d540d09a103200c0e450000245080440c0c2c480018080440a441900c03010300541d0f13150141c0901805c441c040c8001c5411a101000401c000e01180540c050345145100c07010903441c002084000e0203000d0401d03030701c3c070703550f000d0100040c2cce43e80c4102410480c0060180c07040740a492156030070407180b0003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 185231942 1250 185230692 185230729
    0x516031203090302070506090103090506010e070905031501120c08060702010b040f1b050a0e040e0c01020c01090f0b0721200a0512030709050d03030e1b0d02011d060a030506 76
    0xb000002e0300401e100b429540d0070380f02543c881303203400012070140200e000058014001c51001003039a40180700355500c1030328141c8888a40603910340a140e90345a2915128036200c500c0001032010045865100d0189030144900303100e01521099000e007416403e0b07a441001d03079940d140c0072999082070301078440c084101076420400882080f0141c01503d58242c5140304000b400140c0d41c6001d802030b0000c1c0454103003c0c008200750080800419a104080745031180544203214a04009621818404040d508502c04850580d0f291000d0040a50042242100c001c0d541f80b8981172124211803a410450355079030340709401403404645035203804a98990911032908120908804201c0000b40300368020388088000c0c3d41c03030b5a0000100d8045145400c055400130b0301f00c06200c14117500d0b4100355070320702102040e0794170040e07a444051545106414640e41100d000100311001d036004944449400b442c1d050030b10120aa00000102103070300c116412004650b0707950900045041148405c6203560700007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 185233192 1250 185231942 185231951
    0xf060e0f0d02040b030f0d08010906090203061c03091503021c0b0d02010c02040b0307060c030f0305011a07060908030a090606090e03031b040b03010f2102060a0e04090516031203 78
    0x64020403520780801c1d601900654680042d1406a1401c100742045030040d00183e598034050740340b008007034420038400c5081342d606088000c520f1850600c00c4034003621004003216000084d0042c0c169007140c220f6800d6040c4002e45a002440000340828982c050b0465138006a5510b881c41c81c1c440740c200002c4010010900d04100d0b12135903215941c4100441c0c0e02400c00619801e40c030320014016041c124001500360052020018085d6005011800d0a40c4039031200e410400003408100c0841d40244111141c02d4445182e00740c02c2900300300207200450160002040669035030b03c904c00d82e44d00c241e800103070955403225198248103071403240d0780244ca00a4018032101c1d82c02001c4580c4c0f4000900484401d88110641150f25290300381140d005181c0350304103d80300d6a40350080f80011105104242e01f001400c011010107041580103196a00e078014160f500f04a0745110403581d804400e400035421a5032120300c070f404101d08000c6100a0a40c2c8041140b1080c2180790038400c2e070f1242132019040c0341c01c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 185234442 1250 185233192 185233219
    0x1c0501051e030c060c030f0a0509031c080402040c050c0a1113020f09120307060905060a0b011e14041205030d2a0507020402071401050f060102030a080f0a020408070f060e 75
    0x85103c4000010881c0c210b42c4880901d1103580c00c522803084180e004d1a00020707182c1d1802c0e0444060000110210183c44400e1909001c02002c11338210425001481e450001801403410b80c0c041442c0304843d10700681445c903c0c80c00700d403801c41245006e80d5814001901c101e451b00d002e803020020007100712029801e019101a569400780a401c0b51148162101030110091200c00c1041d00c4e04941c00c01c50a010000702400c01503181c3d50280c59a483c06803c05404107442d50003044c40384010840034100c02c4800b4100c4c841100c11200082d05484190b0341088006103031038401d085c1c1e0110720702400142d03540302c461092290407a548010f00000b06204aa104c40403403d40d100610130000044c14410399400702403001500030720880d43c004115442d072400f05800d400056000c503108011800781d001251700c41e200160fa40b0f0055030b5440d00003400b0400001d1120055104031b503000548081c0143c2013035214042a0f0500c8855041070364031402c0340400b040250b6012200c0510352400b9242e043d5005031 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 185235692 1250 185234442 185234449
    0x180103060c0f0c060209010c0507030c24020a110f150c060a0501030f0308070c0b13020f1203090d1b0611160608070804110307090606030509010203060a03171c0501051e 74
    0x10203440113811240d0100d070b40500350740141c0c001c1044942c40310a4808ca1502c03880c1c0707440c1c4042e1134003c06403030300303009041010f40d8000c824244404451603002008001c0c0240c1d01c2e0070b25103a440100c69040503030204074260944031010101c00c03091542c082d030760702d40500000709031411500404c042e803103e00b010010004150603842ca1184250545044d507495910510300380c0769451004c10040980d0140c8040122081d4469103a00c6640c0c03086840c420002c4042d0100308080b1141d02da00da9894000304103819252504c203c0e400c8001703119a2070440a00c20307007041d0303030800007076540303ca0080762201043e41d41454040c8110341080215800c014280c9003420f20040203110002d0404040c000c0351000b103014024010709034201508014100c420203500c56021b000035007900d00c1100042802c1c03070b021946280d0f060003900e202d06405854070310300900d1070b10343c0e00d60248152001481014100a2003030680c940c0d041241c4840441d40022034107503d4034003448645051071000f404890903450310200c2654 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 185236942 1250 185235692 185235707
    0x30b0a1212021204150e010801051309060b12060103020306010f06140a030f1505130504081602210610090e1203060402040803040f03170304051207060b180103060c0f 73
    0xd4002030000c0416084040030303403a02090107a0041d069101040016140c10100800d044004c155502e041d020480c0da00123550240080c041c043e07010001140c0c00075003d1581d48520040744c09480042203407010000400e01c1080a40410021504268010b00c00e50804101440c0101070700300d0b45654061500100034010603010380c40482d60040004d036038090324440e0700200300a00101200f004440b0980310181e4250006100307a6001e40100515040c2c028007911505215a8100390401d242441e020110070f01a101d921049a011240d590303414000004d14100401c10400b00307008260394101042040460f000d19400031545134204001039000c00e1001c1500d4103203520b12210544c0782c7d159a00010040c0c000c58000c5202c0e40300100f40028a02c00f2070003a481102d0150405082d0140032124160a602c001c03540903015600016541007242140001030101900482d00000c50050090001e0b25180d003000504034401e00e024014030034003c0610401e0710006081c204844c0c050b01e150005002034 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 185238192 1250 185236942 185236979
    0xb09010b0a050702040f060e0a05010306060b0c12070302120f0301140d030f1110090b060f0a030b0118060b070506040201140301150809100e0a060b030102030f0402041802090a020a030b0a 82
    0x5c40d21240d20b0410682c80d071b0016009041c0203540c0a103603140008890000305424842690041d0900b0360000303075404c000080340c46105003200a002602d506078881c903840d501c55081181144076042c503044007017460a01510429180e254245d949525082002c102035000140032880303080c424144400090700034590301d101d4419407c0c40b044800004075194204025245044141c0381400e190000f04002040340390b105071000c03907000c6203400300001400011100c0340001800013011100500c030000d000c5480d00c0100560020100e00030b5114140e54005400c450801c944079400403060200b1582c202d80700075442900024040c0c00c66140c101711989100300311881c003007804080404504446c206101d044e818104110051254141601c0398650300d04035000c5c10781d03030b19280c51b03040440703454113008036400345150b05d91310f8030103440e16000c000c024030300304101014082c078091900c3c0041e01e60644151003494603010050302c4111000026050b941d00321030302c0d0b10035a00b11005024881010000b400c60 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 185239442 1250 185238192 185238199
    0x40513050a0f02030727080607210204030c030210030911040c03020f0a0f080f0f0708090c13021e0915030606042411010c020d050c070b0d0b09010b0a050702 69
    0xa54440c0003503403004204480400c050b03180008100300909410240d404141300c0441d80403140022000e0304002409500d000e0087d03590014000b154000384901c2c0e20b1040b2224038902003c8040c0030082c604100d0740968821580c0e489080800c00961510503458842100c9509080c0480e0180e41d4541400c0e501c4803960a11035075442082c070300154420b6054a845604160130a65035151407640600070150a001e5070002480c100002418800103400c07150041d01c00880642540c2c46015040e80c0301e100c01403401c6940e100f8110b452071107a580111a00070004031140059603223603030700030055a102680c6003980c00d400d003c21000704c1e01d85a41480c0d0344c0c1e4602652a203900d81d110078000a60724811a40100303988901c0c02c200500e901e00c0c8038410181e9040076220304007442507900701d05003030b5050306256402507007100c030281113414041d40080101039400b6044e9001507840700b000c60b0710b580046410001c025660f01d0310741c0305401d000a06901400c00c1c1b0381c1e0b032814071003141c10040c014030928a00900 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 185240692 1250 185239442 185239451
    0x3060630060e100f02120105182a0d05071206080601050d03030204121119031112100e010608010c02010905030a111207051005070801060504030227040807030e06040513 74
    0x40e02d2000c0c000b0103102c02d50140140206a06009500041d401500c40c0100100e2941c000081a1130582d041c1259107400d25224241d654800c03181031a4041105050500d507500c2d1920003144403240002403880c11404e400c006010b0514400062014400720383d2009910701c1d060042c46000c50014004d030455a04840b444000501441c0890181c05140d0280120070840d41940c3d00300469281ca0648007003040c3e548142086031344840303001442c442d00c000380c600c0c00f00fa50516074600304000c14051125800080300e000f0300010160000321000d80b8440301459540d81c1e028400c803030080c02451001c2425100038040040d40b0b40b00d690716442168030350014003c02e0300c420912280709000706480703074030101e00ca40e07180d510a06119031103581c40e25090007002d2820300000d80c024061115075040e50100c0d56200d041c54190703402c1c801003500c1c008680b01116440e05200d04906400311041e03100300d00c42d29100352036090703030716010b0480f400505813180300b22011701060000d81c079449848110300401400104 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 185241942 1250 185240692 185240711
    0x60307030b100503030c0f1b100c050a121809020301060f0f090806010b03041b0312030e1513020a0e160c02010507050d0e120a150c180306063006 64
    0x4900c0b40c81c80c0c2c0000c0c0c02d400045005034501c0000b0440404e405100c006903030100d4140e08003080700d800c109130705617441144110072440b124840c0480000340f6204d0011a90780c089280c590030702c0c0820481c0c40030005142c0005400b00032050841500c02012001015804d41d41022009000030850307103080f00400108419101c0c03148c1c8140410001402d41030107852155071900c090301c045900446040e02c0500056001c03080d981c2c0400010b5044940000701b91121420111048020b8225010004402e02c181403440400e94144550540644424174040101c508107205106004001b6441340b09443e804100300405d04c4400aa03039941c1ca0001d20780042020303158401603406002c2c500c405849481000380404009402104800c452001100d5082c41d031021014496074484c8009801042c4003201418030800341d5040e04101c00034502d604009400004c40c0030003035510f401c90751090b141c1b962101000c00152407044402002c903072070035001c088016030325040703990001e000c1e100003010b80b6a1080901d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 185243192 1250 185241942 185241961
    0x4050f04020f150a091a0a080a18170309060f0103030e0d020411030a06030c08010204030c031721071b03020a02010c05030c0f01020403020f03190b06010509120d0201050708060307030b 81
    0x1000100c0c200e0f5001130715082c0c1c2d030400070011400c900820300082458280c5181c040d44d010240ea00c1100e0541d5044116a070b52a103000160569640b0500030030350925603400003031444000303940c00000501c5132580b6450303c400c0c0240340050240003407000c44400d00060010a520442c80c1c2d001840540781c803c0c03000302e144045001054007e0b10701d4104403000c0144124404a80c10403800c0700d000f031092140c03aa4aa01d181801c034402e03488000c14030340b00307042c0410000d655003900f03850712031b44c000906003480416100c15050f01d058501c50958100b0715400c1000041e005441050134074220f05a020034243c142e0303030296440c000c0c8030010f8103000322007102d0810001c08000325900c41070407000340c0d00c0e260303041e401d07103400b0350444e02040780711f4036421019840340c0c200092400380315003250b02040941c080319296011401400f50090b410004100801a00b60311403001200124410130700034045404000300090031502c1c094142c000300952142804040e0b078001624000b42c07508040301000340e44955000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 185244442 1250 185243192 185243209
    0x703030b0d15091505010b0a0c02030c060304030504030b1b0a1b12020708100c0e0d06020909040c030506151f0207030f0305041d100605030601031e0e0c04050f04020f 73
    0x2021070100c01c80810301d030005908a005018072601460040136541c85100302502c009024201384101c05100f10205144200708884042d4000317800c0e00c000803d800049060703540111001d6012640004007001000100802d980d4803003104501c02c40800400039010b980c900c901c4040b0701c10406500ea11100c00b02c9030300c0302c0323b10341584241e840c80d41400380400a0749410f124890400207008180502001c58013078090b1102e4a000e6980300c00040c860041000769418000d1400d85001e5401e0040755200d4440c165010300071802041514862807540c0350a51525400600503410244031b4940310000e034a543c001c83c22403010303004254100d010f000a08904d048038590000d030407400001c140c0d10a040d00440104141da10b000c0103003454017500c1d5850180d0420584a4680b20382d604041003141030301c00d8001c0c41d04440c05140100e03084508007110800382c0c1016034860422070342c9181c1510b0300c2c00100f10980380510280c0e802e10040c603201d00440e1000e000204068007480c3d44c9a452002c0741d07561140c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 185245692 1250 185244442 185244469
    0x4120311010504060c0201150e0c0307020a08041e14090f09030d050103080a0206070207030503070f03030e0109050d18050d0b0a0902090702060403020613150c02010204050402221a0703030b 83
    0x200618541030030f105000d0117a1609040c055482d045510300b41d2500040702d00181c911140400c00c540d1a01c0d000380340700740e100411003402c500a4030a500000307004000100001c2009a02d001d84110701c841035400f442c111039001804061007400c1c04600c6803130701d0460a51000340801c001000740c0d80c800b4101c0c11845500d0032803c1c568a0a000403082007154405868841250f608582c80791f070b180d4034141da82d510f0600010b4410b80c0184060b038001410300604041d01442490003150300704070b501d5600d00f1744000d803008440a801545280c000103074003a4030440008803042151203c2403800c1d01185038035950f800302034803031002140000c0700d0f0007540c3c00c4020081c0d170103000c86590b803602040094907800265412001030003000d000c81d4400300c1c0d92441c0c2c107020780c00c00e01c0003540e9000700345480018006038030443d0a40d5024080011b41c0d40d120310140802101c0c04030722a407a5030004103c20360158141d001030301a50310b0002c0b9800142540b034107a80041d545800c00140c842c031102d0014035013209030503 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 185246942 1250 185245692 185245727
    0x60b0d03021b0405010608151c11030f0606010909110f1c0b03061b0d060509090d03061208090105180a0f080114040b0a0c0e03030d05010f09020f041203 67
    0x25809010035074005034600c105100800e8400d4120038040800081c1c51083c4200e10001d5207260200360024904896030f0702c0400010000c0006001c2103500070b0000300040e100740c07080d1580b4200c04805080c01d02461040264080c05040c0c0344c54810006001003040d4096851069907ca90409001d26440111006030b04644000e5440e2460480400f0804040e5111000803d0820b01e441d210f5041c001041030182e8102030044154280b140d0060a1a41000740c2c2803900c1c607112000003420780c139200804c07400b50510501419851070a07401c00740664203181e002c403840051201ca98000304081d0030070b6851114003403034815a1070756600143d405408120303180c20b501044114000410854500d901d00440300948006e010111485540383d0b0469011500139081190050002d1503880d450750100340281824100031410300044000f2902c0c0d6000307541d502c40000d58940051200c00000b4240e00000d110040701903203444444807000a45010b40d1141e50008a40410540101030040d880c1085880019 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 185248192 1250 185246942 185246959
    0x5070902070c0812070602031e012c0f06040509150a02040905090a0c05090612030f030402030c0a15031d0f0a0c0b04050f0607050114010815160e0d060b 67
    0x48105400075403040000b100d50001d403250018030400003003004e20b03280001300111800e025040d01d82e1800380d0b00003040d256464842c41c0d0081010300096030701034068140c0000d900a6448003242620b14800c43c40341c02007032640505c0800c41d940c01032007881035020200b503a0105081d1a004c03540c514048415520364201c4400c002000540f51560303001c0c00440300e02c00404d0003203444000c45507444281c28080585821440c1b10f040c0803d040c184c4800341c101300007400d103044040b4030070b448a04580005011102288000090109514042044400c0f0007001c488186a03240b80401e8204100d404401c40b00500d601c031044c0e104644040121902c415082001f62034001c0044407001d41c0b40c001919003106c0e0303288083c0011941900c08401d860a03034030050002c1e0546600f1404000f03164100e480200d580f9903c2c0e1041031020315a1440e894000c051031802020303039040030003038182c1c2d110700105800b4040c0218440c0d40d003940d078094841e0b056003070b041c1e0b8003d0310051035040c80700262041440305a08039404 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 185249442 1250 185248192 185248199
    0x16020a0519050d030501050303072a031506050a080a11031501060c0b16020a030c0611040b0307080f0c0d05090c0301150608090d0c02060a031404031d040501030c0b0c0a0507 76
    0x4407400c0c09038151003041620100d1000140c103800b128003e0140360340683c010b200040019094040c981e901c00302085400c403440080543c1515042140c3d0000c6421281545070103003043c0d2503025000141c0320032600000b00b24103004601da901c980284020703001c0443d00841b0307800380e18140802c100400b00d500c116030b125a1910070140008910000c2141c11240c2440000e651034000c00c1c441216814542c00341052104a8400300c40d00c1c40d043c04142c50305941c503080031140001c1080140010001e181c49640c40b407814242c003401210004100c0c00000d01d000c0f04101413000540c0441d40c2c001202000006d41384c40e0b03510010724012510041c59055803070700d85903140e00b60043d80c0440484900e95140010750341c0f0918802d441d00d40e40900200400c5206c40b0007801403500b07801500221040b441d001420320442c001041c841c2c0c10030758003a800b00d185010b0301d1108100301a002068003505a030188400d500d15174072580840d140d44585450b92001142200300c42e0b20521102051300e070804e0889008944 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 185250692 1250 185249442 185249473
    0x140910030e06160203040b0a02070f1e08030708030c18030d030501091a0a0e0705130b0a120504110411070c14100207080d1d09070f030b041416020a05 66
    0xc0080c410076244140800a002d0480c4800508146100b0b035000d1401e051401e4580318058028400903020748c010301d14042140807101090100401002c452294030120b820495524170325190044400c6400401040000c1040d046c22170340c00c104001c001e25501d095030285032605500c011030003a4540541c0c800d82c142254140c110905032803004104000401c1c0314030b901d6a0002c3c07032a80075034109151500400404544002d060380c080d48a08016181c804814500c03000f0120315000052000c0b0081804414103a1004211107000303001d4004203c1e506144e114036070b640000c055000e210341d44070340440c1044860003040c0e80810741e0241c03526968a448211100c8090140d01049004a6041031000040c920000340741d011107902c00d02611600d040c40d034003294814540a10001d9468400301d01c0701c80b5843d6030002c544103031096502c0d0180c60807031007001000d071580e00c090b8602c550f0500940301400c00c8100d100b6a040450034180701c10000c048075050741041d5050101420354011110130303c1a482 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 185251798 1106 185250692 185250701
    0x60203060d080a03050702011d031206010e0a0306050402031c0c0308060d02090f0f160509060310031407150201060e010311013f1a0114091003 63
    0x20310b038842d040c09900514400e0000303175039042040601c2d40d0a103d844149131010740d680303c09010348000140d886c000c2c030181103024102035020485c180c1c01040100c8014030b0183c511500c85e44e89040240080c40100e405a009005007a08040c110030032030580030200c0415258480c0b085003d03102215042d000030f0040360802c803003140020140c2d0755940c040d0312402c24040604405d160081c01c0741200f64000d000c1c0c0313082c003a00c00c00412072a5000003c1c1c1f89804000c0e00e0003500c0f40e0b11041c907881e5580d0242d2000d0011020002e0020158a0216402040d070f40c80b0788041855100400c0101d088840c18422000401d000d440144005841c01086880441e4149001c44002d40d610061100d40030907408421240420400000c150b01d400f0fa2605411201034001005818030030304404800e1045a105103040001c1c0701d4800b40888494015a030451101800006040490910207002403 = true := by decide +kernel

theorem cover : BRFrame.Cov 185071942 185251798 := by
  have h0 := BRFrame.cov_init 185071942
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185071942 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 185071942 ≤ n) (h2 : n < 185251798) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
