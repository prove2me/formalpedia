-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1891
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:03:17.106625+00:00
-- url     : https://prove2.me/submissions/7f1f0319-f102-430a-95e4-1100b6d33507

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 339928057 ≤ n < 340107913 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 339929307 1250 339928057 339928067
    0x204050c09030d05041d040f06050703020412150f0203091b01051225030606300c090e100605040b0c01090618051606140a05040e04110906041109100309080c010507 72
    0x5900c206da004090345040c155220041041d51045c0105603544540015001903c2a410f8500404001003664012283c50411800b0a00e0983c088404a4280a1103035208070060003124040c3c610700000780368204001062b0304580b02c80841c0c6c58100002049105034030080c00d66003e0145800418181104242d141d080c1c04c0403030b00c0d603d0f820600d824450200403198115000f0400b1140c19080d005800b01c440f641e0915803184254448031103490201413a6071541d01010050544071446101c00c050389420a2401c03003520715210710300000e80108001d0108a900f00042c20580c182c2100101d075584c01036890310700b51911880080c030528400303544001400320800c0100c442030402c90704050443d080680050288001c40c00c0504800d2000079085005803040c0c040724002e01c84102c403480c40e820949489002c0290442940b0300c50b032548004a0071500e8144507458680d00c09412003031070003010000380402d8040b00104003060550302c501d5030002c159500000c048061141c00009880c0c601a880940303 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 339930557 1250 339929307 339929339
    0xf0f040f0e0702011103070c0c0e0906060112090807021c020a0306020901021b0a06050c0703141b03031602040f0b0405010e070831080d09050a051213030204050c09030d0504 76
    0x441e0704011078035005c1c44108044036000780760792600343c41810540c00c2c0a1020300d140c4c0c0c4041509200d000030401200e001249840c042e100c2640c0d40b41c2034103d07c002c0c55043d5041403030301038981c9000704498401440d0501c2c0d8083e0600c4400205664082103400080014069600030354183e50005180d0540d0745c0e0603c14070079a016002c0340b4200c981c82803c041411805540140024407800080c9688200700c03c02c01580250b5110035480c8005403150071407a140c051222002c0c51300b110f003026005103440e000c4151488a00030f41124171402e407042e000c00018000854409620f1642c1e40c4a1188a4503a40202806842030180a00e80350611342c0d0010b0103030000404084c401010a110200800018410300414450142e24200000050b007800700b141c0c402d0341d13124442e080c50103120300d0811501103654080c99010308150741c10310300c0a1641032900d2244d418200f9242003c070030207100502d0550b02550304003110741d14031410700368000f010038604000f01c0712031004920041001c1240c04802c0c10100 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 339931807 1250 339930557 339930571
    0x61d0319060f1a0d050a02030f0c010207170d080726061801080a06020711280e01060221040806130605010b0a1704050a02060d06090b0a1a0f0f040f0e 66
    0xf001018851481c1034640000000c1c510486014102c242404002c10110024980003010b03940c007030406a04643d5940c40d0110b219016001c0d1100000364084402001c1f441d03e49400050524050340c5881101e203510300801110502107101350301c4803850385070f0100352083d520324028246282441c004100c1e9a900c48803415000440010051003c404042180c11140b40c0c410350150301e8a11a141410034810803016898022050085040072a0b000101520300c03854040c0781341627100c0c2c85609440b803c400902655015a112100d030390400340c0785414103400000c407403400500701070b29500c03e68200402900c8810690f0300020480301400014880d00d40180341c1d2a40480c40c10740c0000d030103025543c0c0403180e40c01c0ca80e08500080d0a200092100c01141c980c010315a50fa1180c1c0c070002e9034000c12650089901c103d15050700c8c40741d1400c0036402c0c00c0c1540c0750104030075001081114090f150790f11803071045411040034008070658009400181001e0200d040e0000041030a2640054140d81c0003400c84e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 339933057 1250 339931807 339931811
    0x18030305240103151502070f0b090a26030f071a0103021c020102031b1c0c03090608130501140a1505030709020f16030e12011406100306030f050f070e010807061d0319060f 75
    0x102c0000d0390342c18410400c40742070f402d0b20241c0c000350220280d051283d850410740c050100042d00b240c0c0015003001405014840c9506c81d0030109008001484c9030000d0200a4101c02c52540680001e414e2914540880e8814412a03103056148081004020030321942c00c01198001c1c4040055404258030315a50f180c810b2801c00400c00c603d85004050120724820001030140034000f00d000780300d000819000f0700e07400c100240101c44d00d22031005142e100803a140c4500070301c2c120701c0b03525400303038400e0000494400400500240b804e20a0301c00080d030028070049200c640030801850f800306043e1141000500035180c40e68040da800c0d0601c1251013128108041592408500b081600720707044402e50894402ea8034401c0c48010400140e00801c0540c2000d801e1a101c212031004000b400240300607003015160070780d240542d8070f004510f00200203005841c000e410002d81400301c1841541d2907580c800e642a03035500c11890a001090804940002c4258260000a4201c0601c069406030510a017150182 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 339934307 1250 339933057 339933067
    0x110d1b051201060309080d0e0a0b0a0b010504090507032007020a0e1303030e010b03160302030f060903070305130302060309010f050606031501080a0f18030305240103151502070f0b 79
    0x160461a80c0140140b505159445c09208240064802070302c001401541e82084031008000300c040d600c07074401904079240716842c0e00240313048100e030091100c900e0040e1286800d040c10007203a080580001400c4800b0507a90381d5020600c4d01c0b600a02211440d084075405a0b121558018070003500c1a43e0000052a0001800d21111816914140d601e69030036280000d0100362620345640504080c80c4855803512030421190070440240c011601100d108808503110f031861b0142071791303c032603003142e030318802e070300300340200008a80140020315a0380701461049407100d07101e90001d240d54006480340c0000e80e66814120504900910903541c028204a400c01c0c214500170458040761121444240c0c10450301d98042443c20f074003600174522442c03080c90144158806a100d0210520f44c1410541c0020304040100d4401c41400c020b090f415400d000400407904c54500056015002c1d020300c00150700d090580000341100d000c1e88000443d4000c0c0c3c040e00e022440c0c130038203500000150f00040c0d084602003003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 339935557 1250 339934307 339934327
    0x4081c090309030f030306030822050a03051e070801020a050912210703120c1e03090812130501050a051e390c0a020a060c1101030f110d1b05 62
    0x1000044907032102040301c00d030380c0340c0c5006c5020380020740c0018043c0348042000c82d900031407603a101e01c2c1c40c2110542120003560b10f004104a030b8000d0312001c0e10580040202c05c1c02e14004245440310001e200c811250795a990b000c0440c02c9070301018400c0006000810311003100d03e0b000780c18030f041511101c003e1548401100741d445840403105121095503030b0010740441014041c3c1c000b0480011075100412201118060240c82c0f0903c001003489440d4400343c6042d4058000d01c605010150061b050320308050300040c22828015020b0304003c2035041c4640314100080c000d0040b6803042503d15804074071410840e8150742402c80500c021030a06411408100800f40054440315503845809030b054442e22400122901a1200304c68511407038070b000aa072401201c0c00a01701c10081c0c400d403100c041d066a0303103108480d00440200e0007090285aa04601d016611a4001c60408508040006201c072465607225217160700c802c91003030032a40c6900b9041041c8102c0c002154480c003490805500c2c0000d00c20b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 339936807 1250 339935557 339935567
    0x9050a1404031d190b0a0201051f051302070f0f0c050d080f030a150303020601180207110906030304050a03150506010212030112050a0210110f0f0d081e04081c0903 72
    0x1e0006800f22050406020346960f01161000400d0f9202c5444001d82d454001042d85a07104034070040140d801d00380403480b011a80c5440704001c0703241105006902d401d20003004940920301800e06106a002d0018401241900b08005000c81c4290a90000c000152030704030204d845a6005a101d40c61088038a008212444110b0381d528007000c812640c1c0780c2e1741d88803950003132a04510310841840e03008008000c0640020340c0d00d05130340401c0300c84040d410000c42c6e0842a0b11a1900041280700315600645513410035826443c2c201c42e00a0580e414151900041802400c0344d078001e8070700d1400e0031030b4807686600c2446103a40144080c4007805640d29082c6001060303200621681001e402c4011005060120501000c100142d00038020101c0e40c490280051074082d0021280220303000d401502080480c0c000380304220b2600d01400780000c500c0001d42510007001c0107003103446980416490002c2101d0120f6414440e030721801103680c4407a802c00600d038481c00d400807200261440c00c0c49142c0413035005 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 339938057 1250 339936807 339936827
    0x151404050609130603061103070305130305220e091f0603030801050904110310060e09070806011401050d06030f03170108190311070602011a0102010519021303050709050a140403 78
    0x20f0307440c030b01156144560380700240f49503803010b03200e1481c00c501c812005c00d0050080d07004d0f02c800e980a1069888d5203403600301040a8020060219604001d44003010340460001a07050f80000c10f01d255080e6114040c900c524022107424a8076000042e180030301300310100c170054041c091990200030550035550003401f6194103004080c826240c0d00c00080800c456140000c0319420003506407005040040840c40c00380c401c40c058030301e00301205400151003507070016140d000c541c0640000c048076460705102101c0d45400503c2e240c1000340400001c1500c1101e80141d0005520446028032054054240180f4501d02c00b00f20704522002c0300010802002c0002e0400300c081c02c4201c002c0c40503000752805442299001c0350000850240c81d43c000742180e019403125040c20703510000b5484081080b40120b0072580700f00d94400e0250110070f8a140c8680d0302e5406448481c68081f80200842d07181e407102460b06015174031443d000c43d228020051004400d004241038645500c01c081220700741070341c019100c9030003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 339939307 1250 339938057 339938059
    0x90b160909111b0304030f03030218040b010c1e02030a0804140901080a3206010f080309012f03071203061406030402090712020a020105160525061104151404050609 72
    0x90305201c280c5800213108440c02140d218062003400122882e02402940200281d4004040c07020911a51402d081c001d48000020503541e680790404280d4401550201c0d201c40c81c94070b20420207140d40161030801036420b0703050180040640b92850800a00e26129980784010302818411004201036200041c0b0076a44690100070110603401401400084866a4a041d1602c00130303200715035200c40c00410094160740d0040c101800ca540c443c4402c40c0d81e84a844119400665804880011510041c5c140c0301ca104082c54540c01407507500001c01d00d19001741c0026110a01c807101220703000c507054070500000780040600c1c08204c404480009100e404001c20207401950a1400a440c403803240d103111240c519031020454541e640d80750024000c0ca0200d03100c00008006072b400141c05409001922001c208010f103400004900c4450130050940d48a011101c0c9511070000d1889021403002030009080000749851280660b820b00401d549900d220369640c40c0700070001401a81c4a0360f00302ea240006c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 339940557 1250 339939307 339939337
    0x18190c080403050a020118060e060c041409090709020a0914030a030c0303180204110c06010506160201050a030b0604060c110103140a020711040507020c01080a0c050a1101090b16090911 81
    0x40710005e074058008602484403072001e40d0110810004641d00403164081300b1001c03640151f503811414941e92045004142010003c03406000c25498a00340d0154004100001d8070000d1365902450426a0410381e4041c0c08107140e880306102c0702d510034151101841c8124024030542c1001d03100a00780c02006d05003e03082544451800d410317075080c0034003c0d40f025030140c0100000f40d000708565a150b00420040a0700e402420300018881c070f0148152000c0c0d81e440c0200002d5030343c950340151103a03800070225900381502c1e20f07040f80c2142e803000c010340001c200a0704c659584542030b01e8074424040034000024103040c074011318a406406a5000c56900c42c0e1240d1005030703512554101500340840c4d852901d64042d09080030859416408100ca0341c0c3c5520a0304c607003280352154070b8a2000e481500e00e180001503801e001d9051140c0c4100c40c00c004c0d480c1d40c0000016a43c10780d0321107042c2d854044030100c0c03c0310b000c0d40307000d55031640c030a0a45008041d00f0703a08110088250b143c0500901c1602942d00c1644 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 339941807 1250 339940557 339940567
    0x15020711120f0601060203040f06050304120324120303050105030a0c1401050f030901060f080f06041514040321020408061504021201080a050d0f0f110c18190c08040305 74
    0x20303400c02042c0301c1d0801c00700855000e07607564030009541e60b11601403070880604c480d0300044c0840c001c034140ca010726131141d04094070a0300c1d03000840052482070109210710b01401d0504044550810300d00015280c2285000c4103003c032800e0180c1a01c0060340090701942c031282c418404036000c4800801906d49085a45029181080048403d40103104040340a00300000600c0348544056028a0480364410307042c499641e6241c1d00c0c02c3d11041c40c1410003420741c200301c00040010302e44441b030781c10408190700001031024443c10200d55404085400701d010405040c54800010780219424000c005451415454a82030503022611000050b002001d429980941107040382e881c7d070145c960302194809404060369594440d07035900d046012064980740150907130b442c0000d1042d0200d071000c1406844d00001100d0780803088403000040600d941a5000d082c01e007007002c0c0d070752280100002062180f80d56050070001c500018142340d0350b21039520145482d0041d0040c0d600300c0e04c09070340b10360582040b40d168 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 339943057 1250 339941807 339941839
    0x708040204051b0d020301050306060d030c08090d0c03050321090c06070602211506070804051c1b05040e070e070c1a01030b04061a06030610050403050a030c15020711 73
    0x1100e4800d080c40b18038034040780140c844c2070b4035400f82d81211401c404680c1c65403669002d10441103004c3d10041c002540e154031080108100e5401807520341c10241140c8810040c0707850301c10380a6038a0f00101c5854000052003170300a196941034112084906c840c9000e24186126a2650b54250341c0d1914041c40e070118145091105950689800c40502200100c0a219200002640940403100c92030400865152103256003454002c0c6c0394659405000340389481e080c402000382c5038a6208403941d09219820070340000900c4101401628501e1042e442841c609200810050301d1044201c0001075101800403c40050001c8241d070f00f244071814900d4584800b03040c600a022803a00ca0b0b40c02c60400300c000082000600031445209900500c001c00c1064140440c03c010f121158502550100b000c7c03020540d03078071b00a00c000c1125800f03410708a15069680d644e42d800c1549802c000c2d0042a00d00556600303229404a00e035150805407803086103400001c0c3d4034030003194030074004240901c1d0003205005a03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 339944307 1250 339943057 339943081
    0x60e06070e011e030b06031510031b11031603030e010e0307050304060309080d0216021f091710050a02090325090203040c0308120a0605012d051303030e04050c03070804020405 77
    0x4031707440941150b43c2c070701d80400c014003461070a00310240280c2c0d514500ca41d841d84a4400c0c0060320641c01d0a26650510b007403000c8846400445c944207880c081000900c868502000e07664a001d4442c0d02d01144060106006908440440d80d8226498004019001c0014408021503041e030300f5608000401007828142603030300c1d00841c104500103070300c0011909004155044c1480354184200c0c0d5034507162402010180b02d90454124900128040d50001e00c92541049115006000711004561160440c000d0349410750390103842c1c18606503030001c0c1d40e40480c00c0910411300d100600d00c0c2c1c24000243c0c0015181212401403040b09010f0b980230001c02d08000c0c110003d2002160860364654031a14912104903881d43c0c02c0d1155440680f804070009400c0d4083c00b0726480902070f20201807440b0300021403480c0c01401c00c030003e5003080f80800500c2011790020344241c0207503000382e9500f50244072400070f100465102070302c81c0a072280284200014160700c00d110f15401031741a11f010503141c41d100c0000e40 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 339945557 1250 339944307 339944321
    0x4080f070206040b04030203010c05040b090d141501050f01080108100f1d0d030506150406110f010c0801090f11091309150b040b0a08030702210a060e06070e011e03 72
    0x1d84010b000800044000c044400f4100b624001c0380204400d9400c0ca000f03482a00c1688100200c2a0040c40b1003889494407044100e0341501906900740456006080e050424a40e81208442c6005540051045060200004404802c2803e00058035410318450a555004052102403410f4545007494145011900014401264095151016071000c40da2a031601c013140c10085c00039180900050300340c98000c444198589041c903080d841c25040000403140591550000000d034400c17851400a0000309124030484540c030740c1d4403000329504081405d41034a486908030b40e059810700450001c400d00843c03c075142000c04a510750240d054540011001e400c0e010f42c003420f020000d00c50480f200c80c2d6500006504201118100204062101000445c040e035009000c21584188603120060500c00b2446540e00034070b8031400c9001d0704800d0a0b6140100148003111107a480c3e20750750480c04010000d258004000d400c01c80220100380000038098403082802d0080680074640d000d40d698002c3d40506 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 339946807 1250 339945557 339945559
    0x4030519020f0709050a050a0c0f0507060b0d050307120f09050f01030e0f07080d090b09061312050114070c030807080a02040e25080f04022e020c0f0d0b04080f0702 72
    0x503041c9603100d90b44e4008140c12500f520340141028001034440712140700b04101620292603070451445004801c40302c580088030110384141da100204d20032a034405000180c007a00c0798005580c0d9181c2031604005a503e0886204140000c030381c0503448040d081010340041d2101a6000010185440c004034042c1035409003401c5d041c000d03245c818903204c102003224070981d0005400c852580d2090230040720f0500705441518814042840350000e0361801400504041c031251004c1d5800a459103038020112a1451089405039914150f0051418450010301d9008115080400b01d580440e14003400e1540c00a040b0340800c0005000a1640388259054070050204404007070041e15050002d60303540341441c1e680c44400c84401c420100c03018030440300c3c20700c21f1030303094522000f6407070780e41c00e100008032041050f031824061001030b4503070803034003104c900c40b60040e5038020720182910700140062640c6003214a0b01648900d260540400c0e010100b80e500a503019a040b56580c0e05100500e05e81d02500360b0003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 339948057 1250 339946807 339946813
    0xe0c1903111c03180b1e0708040506130f090519051008011104080715140c01021603050918091902032b02060609070c0201030902131104080606040504030519020f 71
    0xc042850750002075002d10b144e84038100400786440e0b6940d40c07214003500403088000e00300c640441c07505140f45400b810240c8d224103555403c1c10f45480c001101900084d0344954022070070101000305e402d407000d11400805509008025508054200824041182d102c0281042d1620049002c48060700d004000a164010080022100a10008206a0062040f40140d11864002046d20b1001c0f4442018402058079031400c0840a1920000e83e030b0040501903030655401d10400342c0c1c482d807100c040200c071482940c0301c96443c01c0181c00c0104150000082c0c041600c0098104490b10710001400e1002c01c1d0240030502079070180341b0000303103443c44000d00710080104c45854007006801c00c208030600300710f0a0702500c0555a42c90284290000222003510026050f0420340015500950040180b00e00150072800d0700080c1c00d40890558140344e8801c121060000ba081051600a00c1107030313001181110248150306241d01c0090003030107101103009055005080715800a4001c101442601d141d000c1a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 339949307 1250 339948057 339948109
    0x12070902071401050f0f0a02040e101502060907180f1407090812070206030c0909012702030c0301210515041202030901090e0a060302040e010e0c190311 67
    0x40006504020012650745401002d01d00350500180a403d1003000080114034031070380d80001804181d00c0250640c0c1e0916802c120204401108001062150900000042040303140c51120004035000300c5118003103402900500880000c08140c0e801156402e014034640d0300321030030400f00280051030442c2d06051425034005001080c902c01244901c07013984491100c260398091098a50000002100c1c00640803c8801c00500d00140a52b8000c5130203110340e0b007007078010004100d85a0007a000030301e0f20854000c00f101ca200e1031160713040e111404081c0550940c2081510750307640d0b000c10b014036900310580d0280030420b03030709140089410582090407158102c040e000706000e1800107540664580321610b000805040c00001150348210040e0340310f6040c1482c064441c09038000107090080f2581d00c4131800405603030b560160480a60400c4000259070042e000e0b011728145141c01042d0051b90030103030316000300003500608005c4030b40001001c4c0401d070138200002c0e45004c0b415100d4044000d1900 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 339950557 1250 339949307 339949319
    0x70b12040201080c0c0601030314190c050d03020c06010902070f080f04050306010b0721200105091603080d050a060e0405010b031b1c0804090c0f03060b040302010503060f1207 77
    0x84014003481c001e885402158846440d81801882004000002a4007650042000070f20404130000d0204c801414181040c41c42c00c0c0700c00608080107090400100481100024044280320980515841781811441c090084000300c0d20303040144541d0150a80c0801c0a00510030a030b10000810782c1e1000c41583d6815443c1450322843c1c1041c01418024172078800042414600c44044507280342c0c20800b030603e51080c2d416070a240c1c0c045403801d0002c0044058214001c2058913000b041e00c684044000b003841d241c4100310a00e80107038481c0e20710408020310001c00c0801e070103800302c03403c42820083c081180d60752002e101d4081c000c0c0f0743c40083c2c003000e410204801d010703066100b44041902201651001403404507420148150084099403140061402c03400804402e030b610307440340c6e00c91602c250810f44e5a8108004841d0300c0c0c41c02e500828896008552040e915200d018003901c0700301c0c00c02d0304050a5800007045800018186401608440e152a40395a2950203a42e089040c02e022134007101e8440c4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 339951807 1250 339950557 339950587
    0x8060d1e06060f0b0d020313050f0309010e0f0901170118150b2209020f041407090803070c03170903011104050a060c02090417122d04110f03070b 64
    0xc030054504a19041001c40d001050b030185100315550a1240c90504800b0201d400003940003620780c0202c10300342c0ca61040081d00a028035200900d80c00091601c0d49a040000b4182011a510b2144110040c0b50180301a5542646650654040010250403a0003500390a401098491f0502d045411000a050200b140210039540c2003206550184000184101840240c02c0541002d0040c03100b08150302c1c000c448560300118103140000c180c051b40d040040d003c41c1c01c55031554440001034004500708035190340c11400340d07002850b076070f0300461511000c4c0c2c443d40b4141c146c50000801030700205005010b244200001d5505000005000f08440100c2d40c1141d0a554043d205542c050701060700c0000740980195404802c0039005890711b426070b65290b03504c405082e5802440c0301c1901c42803003011002c1d0f40460380a031017560002085202c201003054049002a2420100024885a5170402c8005240e04a44002c1404180d500d01b00380d5105030f0000b03040004a40140c10443c10209885050705090 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 339953057 1250 339951807 339951863
    0x5070b0f06010f180312030b0901170601080d17041a070206150d11090718030f0203010f09020f0f01020712050c090c161502070209011206051f050108060d 68
    0x243c80d80d001d060144441980c40404030040c0044c841c501031020008900d013500c14500028807460001000c19841c400600c241c030003030700814004210f403540403100364020410305000d0428003000341105441d080009083d50304408140c013990484002090802664240c426110342d4040c003040007a24010b20020350f5160212030010124182c0c8081d03100d075060030030740d200d030707403a041a04404070b07607500c40502c6010302015000c5d03003c10030030030316041f044022400b5003405103205001c8103400c03003d540101400d4600055011500a2518030702c0d600695581000505201c0107a8201c040d51420b10010703407c0002075441308524010326010442003040102e00241c8134003040300c9101e201c0e155480c2443c000d0103018a90381e595803412642c50041880880c0341aa4100d00c01c0c409490700c22150702281c0e80910a0f800030381e00d075200c0c513401e408020890081d55030000d150145d42100400c546a40c6034a03061070710a241c140302c00030010401a442d82e861014401d90401b44590300301c00e059028061100e12 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 339954307 1250 339953057 339953059
    0xf0909090105250c03030e0f030c070f08011e0903020c03010c0509191a03130602040b1c09020f010e0301020d0c02070e010801050106020303070f030f0c020325150c05070b0f06 77
    0x42c0030041015481d18031001c6110f180305641d552095895550154014801100100140d1041d1600104900c0040005065081c0c0880140070717040e150031100e505052194200003040c2c0d0500941c40802c2c07202800315854500290000308500c1c00508060b03040500308a02c0030b8255007002c1007140000d400100030442c03c003040e100001d101d0070307203c01c894a540b924040d111807080e54505810101c90100003840e001307545200140b410749260f41e0b03583e0403644140d000000710b040c045041e0580070005401800c510000d0320b01448140030743e50004d408162511102414040300320700d07036801600c00b5416525841d038503200403c001d02e07285602030b644007001c1c42440c0340746100c040089100e0f281030194074100e94545d0011803c60b00d451000365401030702c9914540c01c0655400d1240f0300e0f04000c0c0111220005150041c55661180c403e021031107005805002800f800c2d40c0049400044200d029018011580c900000706034101000865031031050440161200c007100c41481404843c940b160341c06004 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 339955557 1250 339954307 339954331
    0xf0c29090f31020304110906011412150102031303080c0106180209090702030a1704030e030a0b0f0106021203010b09010905060a03060905060409021c05010f02130305010c0e0907050f0909090105 85
    0x80c1c1c840201c00d0784805c440003403011a003501000c0c0c090411441203500031005041c141001c0c031b030086100d601504224400300d14940380c40d050095403030491458041891080c07029510308180707030300c00b0303480c0740041e02c401000e00c0380005005400041c2940140090301e040c121000011000d9030402c0080d4002c2b1403050710454007180440d40d02c0f0300000485640d0f12140e10740428441c252142410ba84500034416400c1c05643c24003000785507424064141c4045c8621100781c65400d02c2000940c041c40144c11039070541d07000300e10f480700c403810b0031065a0444854508540d0307201c0507400100c809030b207940e01c1030341c2000000c41d0f0101c0e0355070550007000650306090020005541c9440420043d02c10410020750400c00442281990f00301036008020194020390000c918543c1088003042280e00107560a903030a201d030703801401004028020840407104518000e211008002c00141207014041d2505050040000b580c84040c8400b2094581500c1d005004540c07601e0405450350107040c0c1281e074a1f980c50 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 339956807 1250 339955557 339955639
    0x3041e08010c080415050714071a07112503021507050111040b0f0d0b13060302010e0910050108090114071718030d0c110a0f0c29090f 59
    0xd40308000044c80349400241c180202041034054a004040203031424003046407480c01c01105052240c0104411840f07240d01e14070781186150040c21390341000e4030407000c0104480b56050130075800188035080007400000d4003003054002c0c94481c440f480070b0740025041252803403881c0a541c00320b80078040e041e02402c000e102508010541c2131162240380688140f2540c2800f1f8003d4088031003003d00b0b070310704005900044000042c0001214440b52802d000c1c03102d0340380c11302481196403081101008250036200c10a09040049070300405002e2401a0741c10131950100140100700c01f5002680c409400c20110600740c10300e0417005103802e84030a0350035181754200740440c8520007141d100125504408001e94140304414000740050007a081c82d1a04012419151000030001841000d078407a110f1640009440e900b49041c084501440e800045038030401c08100c0366105100c681012002030b020074050351034909030002000d40c0020b9003c0c0e9005901d0425180200c44a14110101c8102e07003401c0000c22 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 339958057 1250 339956807 339956831
    0x40b010f06021c020c090901020903010b091003030e031603051c0c11090c1c020a081807030b0402151909050d051e0a0b16081b070f0503041e0801 64
    0x540101d100301401640441e02429460a0040803600f11076440c0c070583d0316451755440011500c0a084e03c1c3c03203501da5400268904946405d10a1001502003500c0341542e9150628408444030050310024041c003900e001c1d5003c0d04e9501344200d0b5401140008000ca056499042c29070b91010308080c265061448101a52400350054611100b40e0754040303400034101c0e80040900c4038416000d840348414110910004400620080d181140c3c2d841d030395801600c952000714010400702d0003800501410400b5209030f0702e420300109890302a05e0304104480c055403901d00c04907282034086550458910800f04020a01ca000008103c01c540d486070342d0400030310388031000c001280c0d1450030000c00369804400b6080303500744500e4001074910041d509980c0d000171291103085d07003840c007292070341c058104100004d0200e80d0405a00382d0403548100407410140c03812401c4482e584150003024240e01040d10500d410040c04104131000303070050b100c808094001079911040c0d8100319004501455090134052286 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 339959307 1250 339958057 339958079
    0xe09030403060b0a0e19021b01150f2412050a0c021204180b1203030907030b090309060a030902211f020c03030103032102040605040e0906091213050a030803040b01 72
    0x340c032091030900c10b240d140c2000030908201c0e1a642c200c046c60f020b1041c04c0b40f07825000361018404d403035000040380b0079480c001c0300041a07506410981c101d00c2002e00500903110b0840d031040f0044406000c0c4005040c030b440c02a511641da035188243e491382031500b00640030300c0a800c80000d4001e290201c80c0c011060f1001d45c50b581c05940641000329691030b101408290940c0c01041c1d2070300000e020601c4446102d40106d003035603c102c603094000e80c000720041080080b0300c0c030706503270250200d400355082040e9400040c0d080e101c0d0381544000c050700ca058480542d40e0700303800000714060b0b408408403010400001d20340c659200a0310008002050084405a54914003c035991102000003540c0340d682103a40c2503a03801a00c403c6100600008411580d1100041c4010000f4fc140e80e20f510b030b2540c1c6050441c61204900500c0e01a1507007000301132150030340c0c00040300c60000e40c00c201304c20b441c7d210072820040c10103c82c2d03001030752042032300304008141320305080154021070040e00d9a03440ca0f82c858040f141 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 339960557 1250 339959307 339959309
    0x5010f0305042d020d030e0a0b090d02040c050d0501060e2704020603040c0b04060203190e01020601050906120a061a010206090c041508010510090605010905060d0c090e09030403060b0a 81
    0x11009559040b01c4881404a0708a038240383c0a4045006100d00c9640101d11000c220b107800301c004c1049145580024680440202c0040c1180540d0500d445404c83c0030495103200414000e01071034980780303a1083c03640203005480351803a89460402556a5802005103a03c518a4815002d5078401000c215442e034540001750b28651451007140391915240d0901c0200c0c0d00041090311002203000c00840d031501f900d402080101810f50055846d41074414031107840315900300301c91040c800000700d0100580d03004601941102c800700c071011a070b0b5a800c03020512000c07010103900c0c910300561300302c1800c221069100204c811000b403040403105440c980103aa940c02c040e0307011400755104400e013283d2440c103900400c07d07500400e91400c0c1c40c203641d10005400e4503c00e83e0854102c544490090003814210b2141c0001402c003468086441843c15001c68560300c0344400c0d09480c1c544a41120718603038000d0107035000910fa1800403104c20724115801c1ca440340c02c0743c081111514209081b448035880d240e80b00300 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 339961807 1250 339960557 339960563
    0x121b150c182301020c130504030801050a0602061302030102130b1b16030b0406020702150a120c09090e0703121106070201061404050402032b0809010c020c15120109020405010f030504 80
    0x91040302d2412040180c052004072907070442c8200b10f4805020346500d080c800400481c02404680780c146407070042c11180c0160002c40c014022160100440e03580090b459030014218040d41c40301e00075600200e4060702c1001c40b00018005940e00004840944600411ba04204000080040006001e1160b280c1390039a8200340059242c007414800702d030900b0b0690303402c540700da030005181031140d6000c20442d0303207152160b02c190760005c141d014801e608800480848031003040200240ba002c5031010342480084d0084100265035905007040c004010098100a90380000302044c1c1031683d00d0000708442c4000702c0c450036500030303000459145401401001d064840800d0a411090040814000101402441039900d40705500d20030740369402d04501d1048402c0e284002c00807401035054060000e4030007611010701e5a00d03140b5020011135000c01c0307000c003c510440390010a850318011180e190300458148000c0d0202040000131074450b40da004008441080e00d0f44020210080410380454000304c0d006 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 339963057 1250 339961807 339961829
    0x13050c030d0f12090f080d0e100c1106010e070e0a030803100617010302010207030f020f040f020a0201290409140105010803070b07080618070203042105010b0d121b150c18 75
    0x40c000981c80c0c0001c1d00d5007107036001001810000614149107032110071415a1000c41e91450018012b950202d240d0b07181400f4900200001d51500075444140c0700011718040400003440760160f11955040411401103400128181e01ca040c80342c140d20601106200d0342c00404d01190004908045600d11a4100c1e41c0580182000ba03146884480c100700c5804801c0f40d00c05802d202a10340c030384e03403807064564614801d800161602d12004000e0300311402079006a0300d12805002906034038456444607a21080e068602050340784a6203051002c5510406101c80c2070750030400007160715100000607103100f030300030416a101600c9241d01030756054010313a80d981d00f040b4407080402c4802000c0306d05d1030304909244100c900e03040ea6210100700c658681c0c089114a01483d01001007440424043d801d2214411901840c1040d81940d40c1c0c0c8514407d0b40e450f009012000c004044015200b03807182d1110303600702d841390f410144490880c2005154001280020528580c03000c207a0b1403107080ea0005880c450000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 339964307 1250 339963057 339963083
    0x1050a0b040506030a0e0f0a0b06040e25030b0c03040506100b072301090804090f020901020a0f0c1203021c03061a03131e03120c0813050c030d0f1209 66
    0x1400740991004100346000c0746ca0b0b665440891800b08140049031401c500900b003554880d10f4100012880501181c0c412410030210000340d600c0071844500c540c42989510342c000781c920010b100d039414240c0c009007078000018100800c280c441001548954403131425580d40369140004100420010b0080d0383c02d940c0c00703000d0580020305d00340a003074100410341d40e08050840c2c0c2c0e640140c20340d119040c044420280110b030401441c0414021682d016104801c02c0d8201204080001c1d610105950003919440c032542e4030005004003c0d162001400e0a80d6407550b90380414100a55124140c8261540d01c200421b010150107110344602c0040d44c03a0b41c444075030800c0c038484100c2c107035400207843c1e2000c01d00c2285103400025500308410240303140b0600710400d030340328504002d070100c0f00101410b0801d03800d01544c00f00c416401001d459204d41c0414a1b1251502242003152500103800001030301442000d079030b5988079810140b24001d10300740355940300d00d40d91495540c600780c0e03060100003010518140c803 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 339965557 1250 339964307 339964309
    0xa02072c060d0203010f0218120c01051615050114010e0d0201120903021603060608060c04030b040204110d0c030e010b030f030706020a2a0605130b2802030a060e01050a0b0405 77
    0xd0b822500380001c002050081c6400d840a0480e40410a10084c000481c0101c18460420103440005840b003100500448507510300041e1540c4900300d0307412200c00041c1d6180041000303896068032120001c0300200000d685039000c00900700010041180844d8602c40b0324003951401c070f02080841541a9a030f0074451a4074000d48018040d0204d00310158000c41c941d111450004150042c0214041c004c04110307146480100d42c24944047c01019540e0303420401800400c519240c1160055810780f000502202d00c81c143c0030342e134052860900382050a02c2d503203103081036050300254040046d0000800c00e030000d03c800c05560f40582c00e00815240c00030b115101c049402503014141d60361490410100c941503841200446002a400c0c9050003481040d042c1c00340615441425800601158402280e900c2600e9080c4030440c01001c290441d507031024041c08a602c1c21410a202d9a01d44100b5505c81c2031100c40b51015100c41d0080c10612400d02c400082e0358034260090781c2c2159140d1039040e1409007450 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 339966807 1250 339965557 339965569
    0x180b0d050a0b01031401051605130801140105091605030c07081204061a220b010e03100906051003200a050d08040510140a030c180602030c06070302191b02060a02072c06 74
    0x2064000c1c0703000c01440091822020300030708500c4400b02007032021640c10b040810c01089005404d040c0c080104d411a03582042c1c0280869801c80401448a6111151450308001c03621039480f041822610a1092004025940d002000348800460411040000706030902c07142c003071800b41c1c0d200d034220140703009a880c40e1141e021684194062411380c550104840200f890b00c01600e100380a12692070301030406110b003034800d080c3c000e1002081401214038640300c50120740210042070300c07010764880180105503200c901c1360008080180410b295070f440c500b0550340740c1d0070a12446008810070100c0d4145c0b20703ca00071954440c005070340c0c460709002c440c90302240200440021202405016100d03168080042080580248201e9000b95510788500060b542800300141101d010306005210034080207000410350b410f100d034103140651007072807076603040e081e40624400080e4109000041d410741895000c10359405a8402c01e00902a46114610780080c0120142ca004401100000030410b0783c03600c4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 339968057 1250 339966807 339966817
    0x61b2d120603020d0b04050c10201f06051201050c0301030b220c030203010b09070503011413060b04050102061b2506240e01180b0d050a0b01031401051605 68
    0x1800007015030300e0340d0108003004011441620440c0104040008204041148140c2040140c480344026000c0c40c0f0083d100c80042034007a0860084081c85001c00712003000007210f4409605554002035642e04d0801000f82514001c0038020140c00d1402c1d015050140a160b0003204c5c90740c44903145a01e07588034454540c0300500f40c0c9003000c0c820002d682c072114960445001485c01605003003178840c40e61041508450307088801d140100240c10802118542210a42e0304413004910008050041c020000783c00040641c0b50726030f601d03d0040c01041e82c8210781e01134030580d4002c3e000c888650b210b040850800803081c00b0481c42c00303642000300c1886845140e03032040c0d40441d40140c40c01fa0064031741c2e481d000e4603164003590308041ca840801601c1e2035040d031040d074000d1010350100310342d40d41880140c0307003041c2d0285445003240e07407104081c2e212500c0381c107007107000142c208040d42c0c0e1095103450030418111080c481511441c1d0405035041c9030f24010701c9024043c440c0c940c120f141c03000100c0001e0f02c090f000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 339969307 1250 339968057 339968087
    0x3021b070f0f0e060a0303111c03050f07020604020d02062b050403030e070b0403260c010b0109320d08030702070f0506040b09010807050d0c0302030a1b0c0b090307061b2d 75
    0x6900d4070342d01204244440c5d0034000c0c0341074502080c1c92820705330000c0d02c8400282844115882320007400050b84403451b44200540d01907030361698034803045402b900e56818050300900e60a04c103600125074900e06c1c1c1d00c0705000303610a035010700910b140c0100d00ba50b41c601e54098107100c4075080100704006a059001c2110f454032048601d841401109441407003508446000b001a0351561131040c0b2075a0b0081101006d004004139804011421810003110600c1d103850001095028050012199a651040c0c00036141e1009455640f031811441c0252240070522800810455110010030603180010a44013528600c80c0c000d41071440b004011103644001404c41802d016080050600c0203040c0d00558400e4000f5440240e680d007441c8000c0703411074aa11840d0101020f05000c0b18002d65840002005c006400408401580d201d00b01d1a070700390b100d071480007040f80f40f40031075900c00c41c0c1d0b45486840c40e4050540b24600111041005240140000b2040c200071031241780c084443c213400340304010700d0742e92 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 339970557 1250 339969307 339969313
    0xf0d08040b181309060c0206150402070809090702030417071203030c14041e12022d0a0611101103180f010504030216090204030f020103021b070f0f0e060a030311 71
    0x71102c0045104040380b1501504041e8031070b6400740910241d40505d0b281e205251008110601e001a9640c0b4030441c2658524400d82e000103506051103e5002502e20800000f441d4860509150f5006956944584034221100d43c2c0d207201c2010000002c28243c0488901e01504880c103110b6a4085005000c4801058140111200701000c1c8405007030150001c2c1121344110380103501240c400c01c1d045d07400340e4000340c1c0510764180400d0050726500d406491040300709404034200d08002e240c5909a101620860303401030501b032070000f022544884980040350541080c0c800084003516040c09980c18030f2404401c0070000c002295201c680c030031955011107020015690122042c000c880e00f56101558141c0060744801240c2090542d004c020100406408000f1850289142e64105464030003580c080d060580c00b0071002d0f5083c0710100321400700b1090030140d030b50080d1590b581400001c200e00a00502060640001c03800c140b0380e0000303d0241000800c1c0c501c603503141d03079421901c2184644007001140 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 339971807 1250 339970557 339970597
    0xd02160f05030d1a060f130308030405030703090510020c0108070207080102040e1f12060902060702060c0f010513051c0512100501030c030203040201171503100207020f0d08040b 78
    0x64600c291040c451403081001d5641d801414100c403080d81e03401403041010201c0300e0020407050390ba150464185806c81c02c40c46464051150125000e800b50f507002031b2403820000100010003c01000510031031340b280d00c500581d01e4947d0240803240c5054074041c0c000d40c3c0280204901580030f02d0190303600c9403051040380c0c80c658039058640e00360b0304294450000781c40c480c014845145642d0107005034090500191038142c1c2d140c20000305884076010701c003078012690346030b10006640700c1108407225150054030071135490740802141581c42182e02448003180d482c2c0004194201200090160100e03040341c01000d0b1036101c03140500258030043c1c0d003802446010484020205505408a445440b0b5205005080361408001405513a41403030941c1c2094410001c2000503a0400768500220050000c00c1816554002201070b5202c0e00c440d1050f0303d840381d0b11214508000603001040741e20720036101035880c2e40c070820511480e8102200010300c5141c5c1444244810403811000d0504000040c8060000e2 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 339973057 1250 339971807 339971813
    0x6130219020c09060303030c040308090a050618010e1509040f24060206010501080c04060e01021608010f06120c0536090615060a140c12120f010b0d0216 67
    0x10031000000c0050780000341035079400d00d05841500e034040b100ba00610700d54505045514902d214a010060050602052018482d107419820001401c8081c000699800a04003914003a0600c1440c281c00144051484415030600421089a07407000750904c40c1410701d000104009005104210031445940d44641c005000486400c8010030002944c41011503080c45002820840d0517088503041c85880c0c014458844900d000702c1d02103802910341102c2c619802d10040707003001201c042c0c4900c0491007071000302e041030b410341c880325021144410800106954201e6018000001400540f42451708070040256042a111800c50610111410100d803141c040e6408035494010341e03d003042e45600c108022183c2d900b0070001e0b400820031410032008001030340014000303100300412001000304484612510450307440a64510500800c1591610321801c00b0249480d0420289a580500d40b40003146540320501e800c103060340c4590014a1030b000c0060300207400781d032100a01d5010148005642404 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 339974307 1250 339973057 339973087
    0x503160303090206160b0a020f03151809060114041b050a0c060c120f1a190306020d02070c0e01080d030b0d061e0e07060e040e031b0a0209100509061302 67
    0x1014028000300c81080c402401c2245076070346e00905088001d441000483c0700d2544010549a01050400030846004c84100200c0c0c4403918803541d158040700c4aa0600503420800b1402c10705031180c2c002e009181641d10f00421094581048210414a466000780c0c09154820b10062a55583c241400b04101000d951103200300c50b01e43e0b800c2c4001580b18140031154190a002d1490080400403060182c00c01c440c4038079610034000a0200e204850521107000c507901c900981c1001941c10403002c54950314004904406940811021644a00c80800200d2903440401241e8181c3d002d41c0700801c10120b2240d401d900410059024a82c0107078000004000071f9001d020301564040343c40020704071032050350034440a4400000599601d41c10a01c418002180e000385000d034811022940414074034a507a52850a5200740a12060103a404104140b403111000501d806514420f490181141d1780c0c51841da241000e643c0a002e078041c1d0041c0109005250881440540e004c044000500e0040c4982d40054 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 339975557 1250 339974307 339974317
    0x23030706020d05101d06130c080f060d08030c1612120b030f0a06050c280f02070e1503280b01050607021c110a030b090d0201090503160303090206 64
    0x15900d90002224142100c441c0502c0341c001e4006008140f010341054480c900001508440344020b0343c0d01000030346d4a0769400c1383d5421503840c4c0c03081000b2200160b0b900402d91401150b0450300000304101182080c140280e0100046800ca80928150385403020300150030b52000d03840001c0707111102c00e88008900760210342d4103c0c08040c2c07a5000c2c03580050035448161018190203510981100a4079070880c03e010400c0c0c51001c1c0e00c0080001c0d40e9407413442c4480d070782c0a41c50350070b0400d03107403042428151103c543c181050f901c0c99448403a082e0040100882e59140c05010703404d170111480c1c000c1813000361104085421084010180d1b0380c0700401d0200c80040c0c4400b41e21001e4a00d500e101c042d030501000c03580aa01411007a03071000e06c0c1134086d4001c565a1a0300c07030084400701100444a209100380100009520399008014128590350380c20f082060120540314041d16010300e420007002c00e401485411718140c1e00001071424803000c0c444c8075a5600c48aa810f4040c16120400840140d86501c0100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 339976807 1250 339975557 339975563
    0x3140315090408071505011412060601051303080c0706021c020706110f0f010501050f0402030903040303112a041b020d050c010212040606090606020a150b0f09040302071a0a0804230307 81
    0x6d0198504150620503ea24202040c090f801410f54403042100200f500c0360702020a09000e80e40e40b8509140c1c1c900120251310141500e2404100317988101404100d420403510303203500f183c2c243d104e800e50030900f004181c51102d015034482034007008802d000f0f84990081c10900350654107015114965503051001e40d0ba08581c0603503440006001628001e022400004415101103045203000c851441c1da1344624080603050003840d010003090140d0400021300d68800c001045911424542200d51071501040c040078802c504000b0806071880300c80d42d0070081c960441d80107101201c0e0030300c1300b6074442d4403030842410255020403085c00d440c0b0b082c020482c0038174490440010b00901e480e424800701c84080c0c1043c4115040340107640c010403c0880c200e540f0b03002a81c4001142081c003000580c1e2003002c003483c96001501e0004200515801180302c0c0c3c100c40304d0f03241480c182c410650305c4100c80d115485808001c14880404140802d070540e00700340d441514164912600c81000d20700c1c602e9504100c1e421 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 339978057 1250 339976807 339976811
    0x110a0b010e0a0614060903010e0a1a0604020319110d090b060310020301060807110a060c1d011e1d0306041b0801020f0901050c07051309031403150904080715 69
    0x4100c1c0c012070000c1e9692010007480704108041c142040000481d503011000740c468080800d40c2c5110303950030b43c410110b01198004455003a9880d203406031084000c04c1c051041114250002001c600b060b0007103030302c030341c80e03004100c5080c803540e18090f00140312091094400c5102070040d40080403c074414410260700603000c0c990a0b01d0b1007420145131104900100c1002401130004005558001c1103054020320b0506002601038003030618207180a03182d041c00b0385504d0519412907012a003110000c920308070705508442c0701107100d4005403011084100610368803841c044400d00150321a5824920030403103a603820103a04406400280362000035902554001c698007088189410748001f80b40003809440001d40c18130746400f10304c1c451801081040d905010f40001c2300d0803001010720150020300f500078054110b412180745a080240708040f0200d02083c0810000d1035030f1140700703055078858612041d41c440c0e01170b1a1414062441c40c0908202da03c00000d0251100161011a0680001c90b0500340 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 339979307 1250 339978057 339978059
    0x70c0e042d060f1503020d03021f06090b041a0d0812070503092b050c1f0605040609150b0a02031603180e04031d0a030507080a06140c07020907110a0b01 67
    0x126480343c80d06001544c5040340d001411343c120729401080300e40481d4180000c2d941414140e0424040c601d0505000c00c0d070307541058002c02a68042c4007907a40002003085502c210070140400c40d6101c048007a601410120401c030107150645124401c28801c0892504142c0100c00d0b00030010302c181c802a010680100801820070000c00c244410700141d461304240700f008444515498555803800c17801000360000b8903000e42d010821228441080d00c0781030501d00741441041070001d00b034600030306108a007050000a40300b50310b805980f00303d0380600700110500e460404022700a600c0217840d40306500041c0708904184089000010310240651540c0d04010201c22001d080121075401c801d500d8510302c802c2c000403030790001e0320604215803540e400c0d034000011400a80201c84580c03004089126288020901081c0400e251400510a05051001040705140c0c801513000484030900c2a010070b0241c900545400500c641d0800c00300e0034041d074180350740c4440c54180f0036030080540310074000b040 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 339980557 1250 339979307 339979313
    0x40513020d051003081602120604150c030e07091a0604032103060e0a0902013005160203180604030609081c0b0f01080603070b030f0702060705070c0e042d 68
    0xc035a4448002c0c89007880f25811996003d031103000c2c81075401220b60001400b00c0864644850034402c66005500f2034441d850245400c0c07800b00741024041070101c2c2040d4a412800703000340078448542c04132001a05200d030900c104040180808110303803004401000803213500ea214000180040c1d8020300d114803040210f103d01e10340c1b403507140350343c5003c052800340104000026401c4040d00b1904011010078203020900040311001a0500700560800e03c541645003c10044101162003010701e41050005594070102045034403403d00100e000358004000500400314825a1b003481020001d011504042d141e4444208980100e84116002ea10000b0300d484881c586242900c10583c1c13240050000340d01c81408140c4091459107000d051010842c0811060b90b0188003d40140142401c06a100d1900c0020304404a0069601c0000750094a0216020701d1042d0100d54420360042c0c041c40c80e080c505103101300700c00002042a50020440d4105040c01d03541003c0d54a0803404045181400e0001ea003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 339981807 1250 339980557 339980561
    0x1c02010615182d0b0f03060f0a0312020f060a0b0d0308180102040603020a020105090604150b0f0904030804021207080706050a03090c06020610050603040506040b07022b0e041e020c03040513020d 85
    0x600034405139041803182540d1015110200c07607003c401610f401d2645966071020030303038444580c0c100811001c81500f40054180c0e0001e4050b240300240c0d412035030a61906040c2808035403400324400e40042445000401090042d10000d800c04031130150784042405007405642240c000f600044002a00040c03101c8020b40c1c24020180c020bc28400988102d00b46940e805440040c90748800a07d56100c10825a142c0e450742c2080030030b040003038240d80440c980341c1b90042040d28115812445405e41c1c1d40e00685190f40001c42e074056800082c000d021490030010107803441d421041c03d4104042d02d0340413840005403800e105000030f21071038005000d503007441c1d00c116040380102d400060198800740100004078000052954000750440c8190b20a03894450080703040910209042e800d19030b402c021402d5030002c0c894062042850303981c071100465407010402007901c0c0074102040c01104107402113120712007154003e001000411048074546995000406c0d03480c09030640c081e420541c042200e4038890498 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 339983057 1250 339981807 339981809
    0x50c011e0e150610030b0301060e0901110f07060513080703091a0a123803010f020c030904110417010f050c1207080606070b091c02010615182d 63
    0x5001500a000c0b1800040300408802854188604d18400811460030301a42c0300e828103800141c020300406440b01c0c0041c0d84484180c2d5900031030741c42c0421030300c0001d0f4050266190080d1500c0d01c80c5c0352a04544440340541801b07041410010158a0076000144d041c40062005501c01d0f2075000c0801c0c600000e15000d80c0340406c0e00c03445c542d001c001107080142d10075464072003c500410300140604a81807061055600c07408a400040c0b1210348004010340c59106110003644110024480b58820082e464142d00400a10b802d203680148280f8010b0b2078980c00510384030320503540305420641e4403c4a8440201c2e50298402c0716591608a05030401c81030003038581c4071311601615864491242c41100c6086402082c45003044040c1c0c1c081000d0756982d05c121140c49802090030451800c103051030a0300e030f10347c029115510b1440d01200c002d880d401801110101c0321b440640303901c80004102c0c181d60114942101c00001d20003040c002c02ca17030f11407603030402485036859698030078619256940307a110403403 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 339984307 1250 339983057 339983081
    0x50103050c071b0503010501060903051c0c24021c05010b07020619021015050118080607110a050a030c2f06090103020705071829060a050c011e 63
    0x8003000c00c5a034400303600c100d030074030381e0310070100d08500700c0d0416400b103444002c0d04416415400c101c0000b80d660360003400c200503a40190141c0d88680d40701d46a40040c00391002111010901c10051030022500d125054105c0903030401da0204100000f1300c1c004102c0c0c0c880d10300c04014070709500d0f440200c502148076484c050004034160130710700000da400203070712800342098101c84080b0030154002c0f614420b2200b41d1519201d100c007032024480b201d9a60503000c0d01e07070040e640010f54541c91021008100d00b0294111003042024022030741b0b8111007161b288641541022151180c000e0100003da8100804a1800c3c000d40d500308071b503100da14201524481b0800c4240384000084595038881070381c5081299072290071580c1d166604242d5005a002e4065148060f026010f030040c000b8504103800b100c1d00390030048000c20040c1004014485000e01100407081845d03444906101c062030600c0001040d012500e030404a00340495045820709480c044155030f0010b1049494804003444180030710005d81e0742c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 339985557 1250 339984307 339984311
    0x30212040821060d0b100e090114070f0903031d09011d0f070207291902070801060b031303030605090a0f0b0405150d03121d1006060206040803040c090501031b050103 73
    0x42550000700c04c0429144090030419810000c100c041e40034241050060882e041400f49914041282d18000c0284035088440c4151280008110a11501204804007600c0c0c441404560950310226481c0031008030311240c60780c0352506c0501e41d584018040d8000c101c1200300c00454038040100f09001e031b4029001500d0400c10383e003406105500415803005450250320951042204042c0e000c04008a075115025824000610600050300075410b4542c5c00c44580c080360a455680c980041c01c90b406403107091403210091003c02c0c00301d0090000ca0010a00901d40800c132551a0000541b40f4030084c2d0369056403d03a50588040c1003a682d0182d0110714204542c100101d2400f074002c40380a4104c005140e100740c004107100b408160180b20301b10000c521481d410041810203020607052100701411141140c82210491540340419014100c1039074099806000c658544d9904d0460940019004030343c104c50820b404250b480b65031003038038000d50240a8105030034010b0303100120000c0c03042c0c000c0c0381094 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 339986807 1250 339985557 339985561
    0x405030f070513051902030f04020f10021b2e032304030c031806090305070905090304060503090a150207020f0406050105030c090d060c050702090702071503020a030212040821 77
    0x6030324020303d500544480500032800795250300c2000b007030081d403210800c0c402d8404400c0c8843d19184040031032040e40301b950a22012440c0d03100b04500100c1c040702d10070050f40650020107039500422150107414401512001e440e0304000800340c402c00d013407aa462800c0b5069500036000039454010b000f007462403c007205c80a40c40f0088007230184c2d4001080602840340080f2503038105442040c107440140c7c010f41c004005103840e8032000380400c84d1031005503018440e003540880c0c1001c10340700d41400342c50468000e600e03052520350150b499810042c04240c49018070462040810742100304c1c2d0050400105006a85034407030710400118070f40142009000302c2c9003a406114590b00401129081040300040d00c1c0c841e0744003030014858004032400205024102840008000d4100f800303046445e20072600c0c4601c684c0d40d07201c03c80c0d54196902c9480440c40d0b4560804401500075401041c41c2c009a1601528280e182100205c0c8c0d203009440440b0400c00020b20480c0c00052600b41800101d440c4881618078 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 339988057 1250 339986807 339986809
    0x70503090d05070206070213200309030301030204150e07080a0e03090109030605061210020307020c2407020402040b0a1d040e1b041506111b010f0804050c04020f0405030f0705 77
    0x81404240c900c00b4010300241410039992a05c0170f507000c141e801403144154080310010200a400002940e4840a400d8283c20b0701c800000c40540e0720610111004504680c0307180c007000301403c802036541c0284600d4074000300381d0058403e1100d1149425031200d00d0b0703a0901400103070860f559070704a80d043d5003060041c02844d0781c0c404580030880750000004542d64440d840000d1940e4141e603100034062142c0220b5a60490203038019500c202e03010380a031070040c1554024085030150000e60030300041034640c800444c4030746500c050542c881c000b4200500301a100e0a60080c241c1c8000500e1000c9844101c2094415030701305a040c04104082e02e00b03001000c92048120303904c000a865150b441c44030000118226112503009910318001c02076443c01d403603616540039204241c1180c449031140203002c01c4410b4200c828500706a6004180c0d80c4030600e184241d411244510041c0044589000700340c1d0f0248aa40c882c0060030643c00090740d0155914035020801d8074140740e41034100d4081d04104010442 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 339989307 1250 339988057 339988063
    0x2003061006050a0f110a03081e0402060a03020307050f040905090601061d01050309210a2a020d060f0c110708010612080a030f1d0f0708120d091e0b07050309 69
    0x40030443c00c00740c9294800380b00a46251949500da000786119070000f038007e142d070011415001c1d000d4561396160ba50f20405281c3c2401200f02c801035000f2004200000e035042c860713801140e204250340b411604018451020a80940c0551700c8183c11645850612003180b0f41404814014042800e110a44142907102e130103000f000c007051a414488048005064040c040c0200d0b0161840c4402c0b8411584280300400400c2d00000c1d04400002c001210101e0204618030402025010300156000c82900d191300b004070594041408850050316040c83d80d040358403038007402150120940705d46070b0082e5184081441c181c0c082d4804d8078140c4c10040304005a0a00042c0c4c20511741e00300b90907035900c00e2610f4064010b440741011401c00f0a2402c80ca0000403480b4a104440e0354030200245c4040e415506886550ba55181c0260303c2690070401c6109483c1880713200a00303d0150105001c2180449034071108042010121000380f40705584a415041111503e1210780c0040141031540c1136003010964155 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 339990557 1250 339989307 339989317
    0x601110c0307051513030c0e16090b07020103020d090c080d0503040f11060f0309060601260a0b040f06030b060f0312040504230a0902010e0406060819020403200306100605 75
    0x30080381c3e1010210f03005501001181c4411721a040a902d01580e80d15000d0708180461180b82004038150002c82d11410502d0402841d12006a9450070b68a080c0320340c0301d1107030f440844100d05055003003003040b500000c2402541751680c0154001d0f007a607031038901d01c0c90030b1090901a00082001c10410000055a102c503920030340c03034104802c03045030142200480c000d0b03c00c2c0d40303100c014040040108440344a0010302144241020399408504140c1540c4000582800c0b0b03072900c17031600705000050030850792680241c14045000740003080d00d41d005131400d401c480c41508140ea00060341010400c040c204280500c4417042c0c20350003808020302c00800c09641d4003c500a95126070b85404428050031240303a10301c07999001005048407241080c2c0c140000134130901004034007180c1c1095030103c0618044c4140f03404c50308262110010b036a5582c0b90902085607060560781c0d26030b424003010000c030303403015421440c3c0f15890b90051451a035950806180c034000404451010700200d00911907540d120059031 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 339991807 1250 339990557 339990559
    0xf070b1c0e0307050609070317180906130f051014060712021c0c0606090510090b0a0b07151103160302031b27040c050a2601030b0601110c030705 64
    0x5880c28441042600b18072030000041c0c0709220b0b607420300289240210f440002c603442491202c0010300365001810311806503020300d06d41185440d0051016082c01c001d0507074031035001007403004008170711180d030421a607030a00c4d0410318035542c80800c4136010b205848000588215030055007a421000005141d40c459094020301c210300303440078100040d000b0015101d24200c40550a6401250004020711841400350161859400c00000062401d4140715075401001c51a501d024014240000b10014010314510740347c100400c61130001e000010355016002c03403481588406628403920301d181d400e84611003a200d621510810074445003420035060340010340c00504006d40c4079501c4070320114152440d040100c3c1c04403400500460414000c0503589121554101c0612a064210342448115091101c1d141c02213001000441540f078003a4015021207000340007886d01c030036540c00303034904129400c0c1d1080780c94040010030301c04207680051400700c551165000801542551800081c0d540714648501 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 339993057 1250 339991807 339991811
    0x112d03070806060d0f080d0c0e011701061b1a01081608060f060d020405070305061c0f030c050f010f0b1c020a1401020f1902010f05040e0a021b0a050f070b1c 69
    0x60040040317070909144001d03000300380c0030740b40c452071507183c0040c200c071000b070340c00184401070484610b60140c4001950f0340a10700f9825841c1c1c2c00e185003a9000752290603c4c1500c240c905400800042c404465012210000114091a9450b0007011840c1c0324852519500b81920000144001100010815440140e46524000946850010030320001c00714038040d40040c204410850003a4058001318050801a104501754422049008025405a01e070040c45040001c02d40e1020034410b400c0843c00602810540706041d03103031022182113078409900300100d0f0707848120005551818601c82c2406081c014401070341250b45500241609610b40180c6060075084108820181d00c01c2101c40300032500082100c201d0b6840201440f11040030350300483c0000c0840018910141c4110b00303550407a0b091300d2200070240c81e41607544000e07410460003000050364200785100413120410195000a0040014005070140d142c040f504100064020019840003005240100604c8c070f403404c0324407003d200e00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 339994307 1250 339993057 339993079
    0x1203070c11030f0115080d08060405092a010207241206180504020415030218040204110723010203010b0703030207020604121209080d050306010309112d0307080606 72
    0x50070a841c0c4554016014401ca000031540c80c1c0781540a04031403031045145514040d0b54034405a55460f40907601d10005407040041034880c01c003600683d800000b00800c0e03504d44034118001141488000211011b8600b6803484200c0365601480000080c02c00300d0906555205d9055000500b2050390842c50b042140c51000c13070030306401a92290300540722103c07540c501c10801c0c100d0342c0b01825060300c007684624030b0121052100a403205000c0222a030103010180c85041420b5101001500284145d8005803074910000f00c40000c1d2001b05a214450740c1064011001d023074003048140900c1e000184507030f00c100014080f4038800e809070b81c01540d040c0307005030b81d803412407001c254a40210741c023080f0080c0f40d18440c6003c2044410040001c54040d548003000140e44003112643c85900c14860004207804101190a40d44290000d1108501a00155201d5001000451030650059441d01a450a0b80111151082801e0760a1046160440c001d0908509120000303484080c00b40a0512a00341041 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 339995557 1250 339994307 339994313
    0xb0a150309060213180203010510110712030f02010b030a02010e120c030703080a120603020901260607050c15040c0e09070b390a020f040b0415050906031203070c 71
    0x9680901d500500544d11820b00c1650301e0910450f501492407402541c50321449218224401c1d03074100c0e00001c002d194412003107441030324804040381404026015080c03001c03505100900d0000100761080c1c1c0c0d18845140304880003401c584a80d5500d034465007094041001503a0702403907030800c40c04211200071000904a4101780790820031401180c0500a4500020900010300040d04500c8076a40b500700312582c8100401084901e5800000e43c000c09000040c031080c1d2180b00c982a032003a0040803001d150140c040c40906d081b000300c9001c4006000040d144188020902480110780001f010516241c1090ba41e000402d42c2c16010711000100d188000900d024810001c100c0201110f0158607910ba64118244100f600b40c82c0407141084000815600302c1e00c01041256022030351300c0081c10140e00300760308110140c1c4004820940c05a152103a18400b0380e03407440380c2800d0020b0810070101da90f162405201d81307940c008007031501c242c0040741c42c01c00c02100c000440f0b6218840b440c1c02c1c000303820585 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 339996807 1250 339995557 339995561
    0x120917100c0e04050c0306030f070e192304051606020606060c190302061512031c0b04020c070e060f010f0c1506030b1b0906090f040b0402030403210b0a1503 69
    0x302e240c07588541800c0034488243c507040b00440c040d4805405554009801c000819900ca4007803103030b000303107984c40f05c001076141181896403100b25016400124486940300c0c01250900740c2c11101c1c0422030601c90500c020800c00b040403042c00e400902514035100d1030b0100103134403100c004002c0d601070100040d800654050502040342c00b082120b02503001140d95080003507442c403085031751060201034410018254900b2070180c0e024009840d00843c90304c0c01d00c04102c2d240480b80a5007607034041d02c402e42c0c40b8150fa940d0000e4007013841100b005082d0585002d481c07a40c0e41201901e030340d000303000040c0441e540c1e076848045980041018203200d02080e10b503140c148035203501651113030240303461302001000304560300c12424011b0f41c811480e41002c08107843d288119105d41d4051907445002040b41603441c0c10310302c079070490041d001800000c41c10440800f203010b0380e0007241c00310f000500c07403a0719220100d210241c03041c0d03101d0005010401d04c10020003040000b030709802140e4540c5c06000e060380c0c01038130903 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 339998057 1250 339996807 339996827
    0xc07290d090501050112030206010911040b0703020f0607260403050417031c092a090e03130605070b220b151207060909050f0105100504080a120917100c 67
    0x30b402003241d0340c0d407070702220500b0302c200b40100c0042c01194000200311030940a0700030f884442e000050701d03113481c00c80e00c90b2042d440540c0442c01d6000f1111a40741518007070020720311850041c0c6404106071084000700801c0c0e0a103605440a031403620b41400040396014041d00c080c0c821100d900850008454065443c601444412030790040810040c03405030740d55038024140c194424801c1c1c0151030b680d12850214030b454084075240d0154400c00400007041d4640101740601d181d5415680340190001c4030420351100d070340004e800b14000041d10801c000680b0348942c3d00016140f48201a20340803049144002c14030071010300001c3c5203201040c04141c00349480850034200902c0d04810044001c0c41e242c17504828810740000c10300300b001c0020041094002c95220754801c00c2c18a116030b007003004010100c0e081c15000b4040000600020451030307000c0004583c5540607000c0141c0d0004801030052000403180c008101d40b03c1300200a0303c00a0000542036484144a4004070340503440800032180c441c4c00c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 339999307 1250 339998057 339998063
    0x605070203100c0c1a06010e0613030f050d14070c230414040203060a02120417070b040506060427061e0617010b1815060403060c03020c07290d09 64
    0xd000100f01d6280d8124080e4144a44646145203c40c2e128000e43c1808030811181c15000c104600f640d40b8031460408018041c036008201605400c40c0c61b07403924150001103210896440d0f103c48602c4843d01e410010b07006001072103140f001d00e4038146580d80200c0d11001d03c640403c2801042169120400d508001c001348103018000f04940300d044003607010000400d4609a02070f009801c081040c0d000680200c5070344081c81b1803020700948807950740f41c0440200c500d03181100c500601c03080700002c10810b0000d0048d40030f0350081065051000c100000c98008524031040c103483d44080794080b09074401d2100189400030700000d20650848801e00b4004c503541008000b192403e840883c40c442c516400003451000640200841005a000d01452852800e180c4004001e80e200080a242d01c00c0850000e64001030030507030501b6a2a83d6803426180d0303480d812008690003051074000c0d540300300a00001050100c044c40f0902031002c4038540c42060003406d00b12070b10030018201049501e60b40010000e02d034 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 340000557 1250 339999307 339999311
    0x30703020405040e0d0806040c0e060702060d230c040312030b0a0f06170a0b06040b0f0c010c09030b09150a090204292d01050a0e0d050d020124060507020310 69
    0xc00f02c4c4060707445403d100d0080e00850b01d06000724000d0b00f4248902e100540003900d45d50001d1000000f080020b401128040b684403504000d0055682c000d400b03400b090441410380042ca42c40d90343c20140d04124000c10505104000740000c10108804a42002c1c00c004107040004a21111202040007001141c00c10450380f03514000c00540140d109000f10b200b4050080d00c1000c0d5141c1d004007106541d000f4480c0d80d4884814403080c05105001c000904401440c01c02c0e141c0f520301e02e6003030242511841d550420200e40100300c10014407278450701da42e520600e00300c0640840f100360400230440000103080607490035540e120f458115100d03580440e00d02d410514540c1220603c03000c0c8401c0300082c200c040303402880603040f80030b6014114406906203007420003010540442c200011034154024620203801c11a81c00d0f01000d40b500c540c00032101113401080501183e01c22464040c0c291601c00e00f400c409207100f00461002510031400e00310556045141c81c0703584030003900000b46800041b203110752031a8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 340001807 1250 340000557 340000571
    0xf02070c120b131448090c1204060902120309030d1103090603090c03010c021c120908070f0303050606180d14250605030906062107140301050f04120503070302040504 73
    0x207041e60344622545c1c03281904421000542c51501001c104002c540a80205601c403681c015516014851650144040c1d09880c1407140701e00710301072401001d9406481207556103417054103600341050341d42c1e07410f03038158000d6240008210202e955102e0368030100082082e140c10300624400c0910460b00b404000500079a00c1f402d014400b641c84020402e0b5442c465843c000402c2006400424555486245011007404c0a20b0441c000d6400e900080401c8814580d40c2100800155502d030183c800e841c01105d0001e807000991402504840780501082c0c8501028000f4102170b005504803c9040403050b100780e0880c003100d01d410504a0b500840300b0700d01d0700409040e0400600501d50f080d20040c4a080e050703181542e0b5010070780d124401035501d4a50340e01300400003405410a4000f44035450f014244280f103044902ca0001c2c20304101d0381150000300d203801c500800c00c0c6800d01485401c043e201072031019904040e5180b000040e5114085410b110020002a02a5000358161002072501810901c000307 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 340003057 1250 340001807 340001833
    0x5130c050f132102011d01031815060b04122a2309040b06121606020d030e1207020918070e01051002121606020c010f02070c120b1314 59
    0xe0b000340103001074400030f08064040c01c0c082c000e48042864042e120201c0c80c2441c140c106070010b1034688128141031700d80001020300c24040100203440d45c0181e1810328004042c812090548495074480d065041d0b06010a21030480300c541c00c4003015501c600050312042c00901c641d1000c42d08078100440300c95001c01e000030800c124482c1050a01e003140100e4500d04040c2c001c00103403841c2a1000303465041c40e10002509800c084000324014000320302203500c0700c00080300148000c42035402403030050304101c00525080b5094040c5898102c3c2d04000780c4021510115200114054200042d124032004004112464030401c0d405c241c084c503c0c0190343c282a21000b11a010300c0d8280b0541d40a102d03045601607559201150058103140c410501c14501081174035014185c080109050710859801c004c80b20420509204000703054007410700143c0c40f4891420228042051030380400a841001100600051420502c0c15400752100640348080400e6041400c1c0741c2640220546047c46014481209 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 340004307 1250 340003057 340003087
    0x7060c0512181315050907020a0609030e03100608030304020402070f050105070503011406070f0201050d1415011116030308181b190f050405041b0f08060604020405130c050f 76
    0x3810003560350100d003c540d0743d100004c07154440c20785001d182c258641403240303151120415402c49045d104840802c001915618100c900c404421004166a580401540d0406000c800050300b8802c808000191070a1040e5880e440f00810091003a036001902e4010040381a4920800036000802080303e8903002d00701600944c4203000d040c5000b28070503201d001901d480b001f00c410250344801e043c0341c0d4202c20780c015074660300000705120340561224101f08902d00d8284016124080300e1401c2d00c0144402400509a004244980700142d00030b0400c14a00100c04412001125410318022031180d40702801c1e400c1e5443e082c040345640d0301410020b0381c9280000d2480c016010f8049032911b04140d400c59031007010602e140304900620f400801c0400c13040c07425a210561003030040302580701c861113608603944d2686054100b06c1801940320010300807060100306440d800b020599085280a00307080000d0340316040545c0031507400b611082110441351251081d00c0c8202c2c94842c1081c1c42d0450301e030700c01c44 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 340005557 1250 340004307 340004347
    0x603070513200c0303150f131a040f06050f0102030301030c2102150702010e030610063507030e060c07020d020d060513050c0d030509060307091203030f0b0904030207060c0512 77
    0x182c0d80f421103000300340d01d00118550344014004008c50300d13400843c1c5040015041401e40c00d4882065603000b4289034a40f8080c0141c03d034400c1c04005100d41c10a800c1140c0e041c5d000312250304560042c401440001d000005030400e4800100c0303a07a4050a00d03074659079a503082200e0003034100d40c0c804800381d0b02c00800d8001d4050203200741c071040300800105084c5961079608541001903224042c00401206002c1c0700d03a209480207000c0742c5032070f0310040301d20f0098500c0b29604044101305164100440e059041c8100950140000c000c0c0000307080c000101d60550242102c041d12402c0d1105070350f01150f440307800d101041c9507c07090911280c0380094070680d42c407040c1081610a40604000a40e2070b160000c0801603803949a203035141807604003002d00160350002001d00d820720200020204e8101e5030203a500103030318403d903004100e12640c000c01a00380d41d588a0414051030f000018080065004074a038801d44100340f61000717641d10b0601f022484c00c021000b00d40701d00040081c40c01441040c50700c03130309 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 340006807 1250 340005557 340005571
    0x10c050c151903090c090b0609040203070e0306090102070b041410110c010c030506150f0d050405060a0606080403080606030717010308070203070f180f090b0a0b0103050603070513200c0303 83
    0x2040d0b29034104080d03007540d44611004200700c55491040c442e90746c080c0e1116403a600060001800c040200c00401c0c02ca07401954140b0224000c40d42c42119407a04006080d17104414000039801c01005d075446402c10880a0002082804c200d2101728400a0030041500c40c110400020b1210100c601d82c00c00742a40008411a1154246907802900c18006e006450185001400d50f5040f40e4417102c03104000d412510101c2d184000811030a00d81d170a803400b495001d54000c801034211801d10710021030403070700303036034400003d01c8641c10030000840d81000450b988101e099071025945e603218481111401002c10140d100c0c0340042001105010380103003e003516600c00c1c0c0454a4440c0c440d42c0e41e206416030361085600145000d01e40042c42881c91f040011100c003003040200303070f54140d039403485070029040311441001642d85a41607003540e03141c058540c129406501502d06107007007002265603046030950b680545030321050503102c01c807070b240d01c285d225100790881980ca03848001c6c406500e0703a00640ea03030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 340008057 1250 340006807 340006837
    0x140711090907030c12050a020a06020312100605030a0c020115030506010305010606050301080a03050a0905100e040c1d011b0c0305031e09061803100608030a111506010c050c15 77
    0xa8180040010200b041e00d410105840e6050702e0300d1061440d00e070348450200c0701d9016101e40c0d0001a01c070060702d00c000c0c18403074000e1600d81d28545174807100180014030208162a00c014108032042d00041185d400441c102da010856580b030501c164050502d100c50340b5100a100400003091001c0400d40d541601c1c807800c028407106039210f9003110140428080c07801c503900b1807599003000900074401000c00341703414249203c525658100041c0c0441f0360401e1840071480041e030900b140d00c0c192141c948409900d04051800c120030182440280c1d070700b03288503414004100c0440c00c00308170038004281e9055102c0380c0046050340781e15005890b80c1110702003072550300c4168a60f1351a081160161403402c1720260129080040484005207402d0030307200c0c2c09425024031854001210303518080d400207008560011907440620740340007400c162240c01907a0150700020003101d800b04503581c0107904400e0034a01054883d84030b04000b8100402c555041d98808246070004c0c0840c00703400e0190481c42100d00300 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 340009307 1250 340008057 340008061
    0x8031e10051314061c0b0f16020d0509010309060209030f0a1527080d0e0f0d08010b0f071e0c0f0501110a14160902090306010609032114071109 63
    0x5600560700007580d020f51a402c05000155607051035007040e280031030015079074003c1001c25240d0000d8142c040c0e411983c4c030450202040744414003056001c6030400903100414081c900c000c8010014003d034055141050b49403518003007030210030f8056506094004042d130f561a02c1200300c0755070325101e02c4021618025402d0601280c07104030f00c40c220101607000e01030300303003110764841c24000141803140071940c44a050190043e521118819620210b2034000204000005000481d240c1401c0740d00503000c00921100601400c0000700548411190020040f51070715100e16291940b00e400c8645541c00c0b02405c00c4080c20301c41d804983c441100c0080380b50a0340c0716260001120f034552032403409816640701c00d80c04c10024000e0380642c0003021003031050b5901003850b0018240d040c141031307004545440c0c0200c0d00310640e00d0b052110500400207400e25103211031544d5100f05903106a1200310b10740f85a0b80f5102c128180c082e5045034050344660120940c1e0760040d00c1c11422000d13880303202c02d00512500b40 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 340010557 1250 340009307 340009339
    0x702011b03020a02100504091e1d0709090602040b07030e09150d03080405011503060504060506010302041a0702240703090801051e0c120709150c030c08031e1005 71
    0x10380d028940350164080c0c0710041250302030043c2c61014040701010413204102c00110b6001030b01c940032100e0001e002108260b48540781c8a0705807400b40306099141d282c581007803032007154005950000c951b411030004c00c1d00401400c05800902441e44070490203070001641c03101300b42d03200c0d2041c140004101c13000c04c0c1a888001100b40b58284611800360004101d00014000c02d010713403a696402841400080381c510041d24080d45c0901081d8011248a9121001d1008001c080c0c0a4154031a8082c0707400c5040a00d4458649018200607040441c0088002409000d41d2692120540e40d1900340c0c24540c034100c003210941c40c85134440a42a03002501c00b000c041040c41381806003d0046080202c1d00000d070004140040c07003540d02500a8510013020846902c45899110741140700340c0d0251644070076940b4001e0021400e4601c940408100800800200c00007070700155101d40464020131801e44996031600762803107107210800b54100561700b135404c0100042c9004012015580c0a6950056600e5141 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 340011807 1250 340010557 340010597
    0x10608030a120e0f0f010b0414100312030e0307120201051b03010b0c01020706110a080709080307083001060e041406010309080d0204061706030d0f030b030f03030a02070201 76
    0x80700000040d41803105128081e01a41100705000c01081c16913030588690300c40c0300e02e0012020717100340c030f10394444044a170b451600d4420040c1500d510416400c0c1480e03d280341042c411014080140310309514400341f422144241d01c4209403501c0001161717514030450900d01010f01d20500202c00540c203003000100c0980307943e203110030407050120075581541d08020341c00314541c100114181e003641d0f00744034000100302e01e4010300e0301d28a10383d2021595020703040801854010010300c40814004040d900b041003240020031079008540013194503880301020680b80c01540c035400d406c07405e41c4041032144040c0098030203c96040351300c5a155081828005802c0c40140d903022902d500b41c14000324000313402540240c00c424840f52284075094a004079581c0c41c50301300e82050704000005040742c10650a00d4148581c0f203900020120b0081c03001110452000705412484a0030b10201619004403000c503481c1004619030b02548803090300d03182c3c90081d2118000703400c01d0206900244030104c0b0f90710101048 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 340013057 1250 340011807 340011817
    0x15060605040f151211070209010905040c120506150f0316060306060e01120c14030a0e211e04081e06060a0b07031b151a03010e0703110a080d0503070201060803 70
    0x19491348481d5042c9924814020308120303103032201a842c100010030059664881090182c03040704c900191038181030038070760b000d110b181d00562400c0da420300018000c5000000e0030355101c5200b0400002d01d032182804681000c1c248651980c0600c2066219101100e1300c80080f025240c1e9035400308041c03076407540126203001c059041c80c0d01041062a00303070b8503440c0c160071112105025003401006034003a584010450380c41140c0c07118125550f0b0217800ca410704144248800d9400402a03010b60709a091043c28680c484e2824000e070b40d101400d03107072900310016000e681c02815010103503040752000f140d004100440070000d011150013500c0004d4158a0b0070704140301650305008585080c0595130382d0988100c4240c00a0b004000c51107000c040018041d0400c0c08841407601c0c101041c1100c0301c8091301c0b10b2400c442031441c880d0f4100408140e42e00b01c005400800c0b43c0d0048100c40c2d00301401c00c041f445640c8607070011841805000c01364042203030808021130040c44968002c1141c0ba036240b030b2064403802a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 340014307 1250 340013057 340013099
    0xd09030c0b0930160f030207090908180103090204050a0e0c0d0309170703050a140d030501150f030e06090d170108070506030a0e0f0d0909050603030a03050415060605040f 75
    0x3040b1003a4420403000400b0403604060f500003e46400182d9103180c810030400d110441c0d0001651041408240d07040c03082800402d6102014411a0750319624032040f4000c172144142421040c0100024582c4240c200418464002e032081086041c16040702d00a081c0c9058054054032801031840842c1c100030080828aa42540c1e450b28218104902000040303045041100240719120b00840801e00c24000c22034050b100c1d0b41d0080d00b9402c0b880505091100b01d0000c042171514103801000352545540f0100c800c00710a1602c51603031031213401c045c0c0050109540d00c6031544100c9040003001d00002a880e04442419258840014141c00e018503104d00c0c00d000e5010a50800c40c4204868103000000c1e5400686610000c20540c0800d01e51340c2c07804086055030511a88018140c0b5001c0790440700807005480c0000050050b8903080d4013184d56445035088100805a44000080034040214041114844200000d1100694482e070082a036041409100d020402500c000140c20f01e50600d10b50034222 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 340015557 1250 340014307 340014343
    0x10906081b011b05030a0309060b010302031009020903010f1a0306061e0d11030f01050a0b040b0906060703030b06210f0702060f07020708010f0504051605240d09030c0b09 75
    0x2001400441d10f8a281102c0c4810b03e07050750b4002c0c4000b907800d002805035421943e5000801c400705040180c01e545040500718107143c4100244901c0114410180060740c0d6261005070b5a03030316403c0481d004181d10101850744a1a0803040742414038110030152101500714111000c40c0c845204000805001c0303605c3e414010f00015000d511410b21400502d03025001d5607510385c070003040713102080c1001c0c030030f00c0060b11a9548004100f107514103032281117003410041d94100003111010010402010000e402c181c0700c1c81d00843d124007014840e0308901e00c1e59002904094403800660f9444a0307110b81c21901a5071032a28800143c40103191545642c410840c44d4001e00d40c5444544600022002c0038100000314080c6650125800c1d5090207041c42070342e039032400081d4038034040c1440e6040041400e00103003041c0110404200541d50485a100701c4a01f94240800f40b43e00c003840903040348582c888103900719040401c1e0206040d00302049098070380c0552950310043c1d840c1c031045510741071030380b051020f240 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 340016807 1250 340015557 340015603
    0x130b040f09110904021218060115030e030405150a12090f0f053f03012706080d080612010603150b01090302192301080a09020f0a090501090608 63
    0x4005030810701007010102c2c8190b2030044038102250680e485440c6151150340600d05108480150003000e041d4041d00d640503000550600070340583c44a900c8448008042c1c5442d0150445d01c0e0a00c00c0b60300400000f000c0541c141400004a0040d070040340c201800315402d28041d2505c60080c0c00744800d115440000c51640314841d640e1540002c1e081c2030151003602c601c09500040c40c842081c0e02039202401d82840103c480c04504401d0440190207144d8034208042c00100a070350300e400b181030079a00c03020b003030380510060340901000201043d600c010f1161040c08075003142c982e00024414020402500e2004d802c2000500c203a09071021480001c200c40d5420502c200722000d940d002201c0e01c1c00514192010300d40e25000603403403003042c41060703110310301c20401001620305051810b0f888030315071407080d81c20b030004d0300011701407a6006024000c80b40d00c601c0327548115038403d448040d800000a1405103102d0715606800c00500b000d0103083d0317070350b1302c1c101d03000c40c5180c0002801c0c0e1006030a6110141d0748 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 340018057 1250 340016807 340016819
    0x61f060f080a020d240602010212180a0b040b19090308041106120f01050f0a0305071e0905070306090f0b03030301050d14060406020315010f02100c090b0703020102130b040f 76
    0x3801c801001141155824015005008094050315080144510300e160b4020010800084542e0305a8845000d41e80b0403c01d2000e0072503010141584941400f01203604807030011022424189400e074020f01d104900003c01081041c090902405036244142c840d00c815100300601c811a00001d40c0134010034800c43c0002c001a101203002d8034495405011503080c40940742c0b980016160581d04898112100e000510507410405c4000d4801503084031104100c500c0c40e101c0315190301c410b000d901c034a1805902480081c410118140008100c818020131452510b984000d0040c001c0d80508403070300742001c4090072100380d180549680c102001300035514691904007001036110240008440200700740b840b00682040900c44a4400c501405001da92480c1c114513040c24007040c112411f05204040003241a0154002882da2518200a800007000f403c2c00310103441d5860664022420a032000604004155064018240b22014066903c003000c0d1030300040c07a43c6001e11301480c1e17410341400b6810000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 340019307 1250 340018057 340018067
    0x80307060c02070803070309150509061905270306090303011a0711030102030c041a03010f0e090c04061203090906060519090f0609080c01020f0c010c020111060702061f060f 76
    0x441c000c41c0c011034104599071244141103400024007a0f000c6003542030104a515801c0740141c0903801c80f483c0261901d012280090018080d42040f0070008520481c03a000351805141110640c003202000b0f9548032605260915512802c0c06916000c2e00481d40810401c1400000342e80c141c80100c01c480d286050480d0fa4407103940c00c0400c0603282140e50030901d0000341c80030700c001d501500c000920317681d596040441e8004650720384003260300f0340ea0041004104c0c1c1000403036004150b4040018044e084e4403161100b0385000001e40344643c1c4245030090000301030030240c1585102501c01c0d141c6c401e0080d5212041c20031501c0c81d100b00c0b80070500410054161070f0952112007646070131070412411550b1560484007805034203810180110391071400500030700d4001c009030071a4100074401450300710211100b05844034003c40580d4103100012a030501168000c40306902030354251390031a007140c540f1170300080d40c4030410f450045d840c000c98690440202040c0320301c0c07010740701c40341c844586a011000e02151 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 340020557 1250 340019307 340019321
    0x804020f040b011e050901110f060606070f0203010c121505030c0918060123030c130f1d010f061e0626041202010c0207050a0b0a0207170a0302150108030706 69
    0x10410608680d2019080059040c1c0680005945c0d01c0e245c0b134040000c0094661154481c02e0340640d40040c04802540308009600c95205000380d60043d15100d807840c1c404421060901d001b5815400d0154680446900850010500460000a000c1d014407240d0a80100f005401425090340000ca03811203941800620035401000300424000b01c441224407450070510283c11800310211448050119015880c000c10b074020800c401524051008800042907080070b42c803100070594642c00c1030008103007103034400000da9580d40c00c1c2c8000d01c0342803198a8024200c10340c04580c01c40ca0320002040d401c0b07210b062a901d58084e6807007070354210f040c4903084d038040c01d042195200b800c1907140304034010103441c0319841c0203034443d001034405075460500190079108c40000c0c000c1150300c8413008100701e5035242c05000843d819000316070303641c82c03500e1001ca04102031504050058140d4421910f020003001904900b00c0f070181d4203135000344030132264039003741d1028411003201e90302c144264004a0409e0380108 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 340021807 1250 340020557 340020559
    0x10b12060c0307020c0306071e03020307050d090c0f0e040b1608010e091e0f0f010e071703070803010605040312050403021003051503070f0602070b03010510080403020c150a0f0804020f040b 83
    0x48062200000007850000c080b05d080300021000c68a031038000455449c12540300300c150400b94158078005900600030701036002940743c000d031200181814090010036103000750000002c0d0902d0523454581d030009400065030100c0f101c0c0003030341c0010a070060301e0300301003261207607552900c0e13503079103041c07100c00d800080540082030750300400d100c803126602c500c0601007100303038900d0103040e007007a03500707151401d10250f0741c0e141c841c036414010444040e10000c07411805541291000e400c0e0080b0805280d407550003039200c010301d100c00010001c80c040381c00001520032a0702c20155203443ca80418021102e034089c900c00290040c400000c0a44854040c0d0803503580700e44103031100f01101281100003468950568084128410382da2401c1c407803142d0510003803000d01080300829246500d0721011469582408169904009050002c981014828800d5080224005001d0f24059602070f10704030705030344817807002408912851241409680900409031040e0380041021082080060501015110003c569 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 340023057 1250 340021807 340021813
    0x312010816181b030e010e1615030905030a081603140403030b030307050604030513080a08071b09020c01020d0b011704020f01050c060a0c032703050d1d0f010b12060c030702 76
    0x18080c140183c040b1844805103da40204070085442d0409007100d00e09038401c1e0050300300c0468001d030f020306070701000b08441b0f82c0e94027821600c1075100102c0c010251000001c01c180000100c0e0302d2044c0e44801e4007401000e03150030030550480d454100758101c0d1004131005600400c50000500824080d5201943c4c605002c0d05492070880150746031800e01100312411004502c000c180c1068040407141440041e0400c00010164012607403030303030305681c00b44030b82c01002c1e60320b02c46915540341d044682e0400106451034095496031884010700b0b000c0e4000114415005140074802159580705c5c1c10b050744030111040780d6040c41e0705c60350240400c03a0800c03d411414040c0c2001040d03211041000018425821180002400d003d007600041c00c1d122118081104811401a640404c826041181030300c20703414104541e072039006408000150200b4684000d110281007950b03518441c1c0440d090061380b9031140200410410f00707042041070351700421040f036140d0240c0009004102654010340c4c01640134011 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 340024307 1250 340023057 340023071
    0x1103071a042d0605010f0f0e070e03060906010510030614040903020c1504080f062e05120607030e0706020a02121e0a0606120206161401020c031201081618 68
    0x21640c052060780d0103142c0c10b4052085014040c41e44141e40c00341c02c1d01c030041036580303240c100d05c00991203440c0a66207850038020045000c0d03a00401c100042200041d041e640c481c500001c03004c3d00ca8000344902c0340100d101010300c1031007602c80e00c82c62007992400c481c080c18000303000c0d00707000040822000880c194402c007401d1086c0e682d10800c1d802c212070300481006548034100180c0394102451002081155400201401181041601c00154150320000300880303000c0d100e401e40500d40c0c1640e00141c0c11025414105032a54400702e8142d02c01c4865850512826401c1c100082d40c82200e4440d590058100c0350248006207031166004007070340364000031180e4014002c2d4075881c140c1d040d41002c0c0102e900c00010641041058040c0400415410481c0d820b199041e40105201748501c0d0850614405007130b80d220104074a088030f05480c68480b400071522164141000c6a696004901d45c4110861220001400b1140011084a03680580d1404a031003854a1840c050741d0551100700b00c9815200c7e05 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 340025557 1250 340024307 340024343
    0x140c0f09040b0a060906090b130c0801060c0f15020a030b09092e06060203090901060203040b12091e010b030f070503030703030b12030f251101050d022101061103071a04 74
    0x5c6030080c000302d04c40050123043c902d0411415100c03031140811103030304098000b5101a00302c1030013811650241400c8042e41d00a1030200d41365440035078001c1450718030760342c002281d61031a0b000d015102c019460800400c200b1000700710080300100d500c035606038428849801c102070300c21744d621040c02c40104004030010582410b00f09850311600074000680c00822030511030716004442c1401410280090352600303040200740c80d0703580310300381c540c105c0c8044d4000821010541004050b50118116120201d48139003040500d01a0104410940c4244542d0070303030501c41040412284125200100214980b803026a030035009840a2290303194056410a0054451007050004050100c80100745907550b03120303012174151080070f006001c02402c807545807000004194894842001d4000d080250300e892130244c40001901c261103070340b9580503403006038603500740611822034162040c5845140c411388810503ca41c0d01d001d0f5801c090f01c0090307040416a03960078400383e00e81c0c1050049985040e0419951 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 340026807 1250 340025557 340025561
    0x50606010f1b14060c04080307080a090b071410060b070f020f030607020d020d0503090318040b06070b0f01080105041e020f09041a100f0509060f040504140c0f09040b0a0609 76
    0x2034054807000000d60445002c40002d000da00e45c001c043d00c800310f0400b03081c032051540c0c9005800740108240c0d000921240707818000c1c40c21400504008041540ea440240740140320301c14001d284810f141300b204840001c10390b090059400f1790381d61604a6040181c580c0300c8007801c00822505a8002d62031b0011094a40c8082c489103100301001d030002c150100952100034a08020940030104004040c41031140180001c0121181448228640003040d800c4000040c014256242d030140c1c03104001800104014824845a1140d00250017100707040e0f0780c500722142694404c49000b041c46001d10b0000b9955400714108440282c000340c8549070348941c94012400c1028196402d80e100c1000b001c0a4001859650a0590044e1000300711036a00d1316005102c8001c14150007114820240e03040002c0b50758690341210120410001c1003030105080608180804e180441c112810381d008002001c02c880c01c01c14036806180e400a808071405a84a4035007103607000c1e0140c01030048540340e40d80000c1c0b2410358 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 340028057 1250 340026807 340026857
    0x20603090f06090d0504060807020c1324030201090b0d021608031501021c050a020a020d0305040602100902060d110706050f2e05040b0114041508060904050606010f 72
    0x490001e01d40810301c8070940c0e1030312070018440042075214041d842c0d20540d00200b07890440350b09007800200754407154826410300154444254100d0000041c01e05d102001d40c200d0003010f02c0d81110040f80c54804422254401c10340d0001074003044403120700300480042c400060518461040e001820312a034680c0384e070314582c20b40009a0300c5d4600802442101d80f0910300441c0d4100090008020b9010002600b049041c0249003041c2444004200c011b1040d00030300c0f0038000741c0c0d401406601a030382c0354540580a900b080c01044014810301c030000854813414810314180c50f400800040c180b01200e44100045d0004454070303072140409002c110b0002c3e600d8040c40c0e00920244000141514000c1103a1041070f00b4405a03c004101d12003020008030071143d1140300340c45050760301140003002000181c0f45103a0701003c00c145502c0005000800d6460b0096a056404141c0c2d00e1804648400f01000041a020b41e00600b0f0b580003040402c2036980601505176800b0b0440c1028503100c024684401d1000c121 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 340029307 1250 340028057 340028071
    0x14090d0f1e0c0f080606010807031802031f05090304030804050418020d06141524040308040f090b0109031113110c010204030b0a150b1c0c020c10050301080a031803020603 75
    0x40c0d18030512607074021960f180003801c881e9006020601e4004002080d002c0301410791400c1c980da07441003030490314540f00754001c803030703005011119440d041841d0300c251803801c1d4011660309403800e404034240e1040030080b07404898005111a040030b05110400008114550200c0e070f1000c1001d50310401038980720180c00c81c80b40101030004090103604024888800c00030081d000e1600820304c01c40f4250b0b40c1c1c0e40c6201c0302101c1c105100854034085c40a041d101c1c1318607000544004008140040e044801076451070955031000000e021a00040c0019649400c485c0401030100240359460000342c1042038500c4042c048010f00410040b01c46c06001c40e855000a070034203905d9400003010310a014030b1200c1690051010b010410600100103200300d60320b011801140b2803003400103600b0f032482c040301c00303140c02040515008000e00010354101a42d03c0340d4034102180030310000b21000704454021402d4034100c0d0074903000b91100e01801c0d41c08503400e00c41c1180c00e0001c0d0f0014034001c80580c4071a0081c500c2540 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 340030557 1250 340029307 340029323
    0x151707150f09140a090b0f040203090304090e03031306020306041508010f060f0e010e0903120a0b10140a0f0309051903080a050610080618070f14090d0f1e 68
    0xd24001d04400c070b59000407144058108000d07980b511350160000c1150080800018000c42da039000603400c0b00e10780c0079941c2c0580080144618410040014400c0792001041041100303880b0208585a0000b00e5a1359070070040e0303445200209180d50000d40c0d004400420000b5014102107100b03000b030900342c01498541e9503803082c050b1041c207544103244c080c080b81181207a002d803500c00200e01c42ea00500a140c0c4405416022440c1d094080042d10302842545c2c402420515020703c4450040c614070a46c10300c9070001c0d40140c0682802080b50344d640002040041c2d113130941c000d0064441f000582d060740201941c8004100104134188004128490170400c1c003007010303285041c01488910080c0021031480e1400052285640d540340320401c03051168108500303540c0d07070307040000c151480d0944191803180900c820408550740c0980782a403002c0290f00c1da03440d80303007405040941c180105003985800000c1c1081c0c001c0401c5030704603170030704c5548903110050f07500d00000e000d80f100420821049400c00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 340031807 1250 340030557 340030577
    0x1a070f0c02041d0d1d0f0f0103020a0507151e05090c12070e0408090405060117011208040308070b040512130b0c03041e06090b030f041716150b0415170715 68
    0x10305d02d080032038202c01d42107030031481450b840c100140e12081e107140701606041d40094603441850107841600d21150b0030000c6411400300c010043c0c0c014048100c10b001a8440c8448100c10b1092603110322802104540020b1050100310303400d001010489022008091050000000ba11070600c004148541e00c1421116180e4409800380801c0d1200902039605100380d203000d041921684d11091411603190000c0c0c80c4411036a0705280c0c8445c03090b6040981745060000d651002d01200c12100c9004910800895104001e0b61003048201d001c6e034a0207d011454000f0200651446070001d8810f9089080540340b400c1d640320b00007091042a1a080a0301076085d0f031040040ca030300300c01d0940040c19040410781c0395260140c8035600e070080c010300041030b840c00d11030340d60545041c2038240e40602081c0c01d904070100c0c9607802d041c01111114080c1d031084500380f099100c014109406190480c00c440300d000e04032341d030414100e0040d4071500c0c07580481d6441150390004403150798001040c4460a651102007040d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 340033057 1250 340031807 340031837
    0x30507110105070201170c19020d080c03010506041815060f09121502181504090e0115050d052418010c0e0103020a0c0c031a070f0c02041d0d 62
    0x80d280d840020341030240c24005180582d0300f00d1a1000601030021141032540d581180085150050f44008000c041c0c60980798149070350002500100075480e80c0300c60052303a8603500d92203241d1009001e61038010b0800d0000b00f100041400c0b044d03412114140e40030074890b00c04030b082d8912917141d92002d80001e13002e03c50000c05a40001910015040303141d03c00039419565103a000360071603100103031410217a0016003203030a02c8450003040c0d4000001841f5000700c1120030ba80101542142c041d0700b50044c80c0000e901c4034148144030307000010b032041500109040c501010010490b03c800300591b007500a044d60520815442c903000c4561101d6480602e165080c984003000c020400b00c0440c0e036141e0f2400241400709038008030001c0139500b00740380240c1e42d078210385001c40f03107045580f03401081229030340f40200400804c2d5030101c0d11680e1140704d19500365030303c0030220b4103078503080080c0020644051045015040030740108104650440c41404206c0c0c40c0c01080d407500720601e0350a0700040038082a0031079 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 340034307 1250 340033057 340033073
    0x303010e16021c11070f060908010b0f0f01051c06060305062403090a05010617011103010e011e03020d030305040b01080c03060112060b030d0c0308060108190509030c0307030507 78
    0x140c2840c140d1010611404010f076891200750140b00b901c00c2048007028034548034075254048400c0b00d60a8460783e0b5035070003080f0012169401100d010602c1c1c45004102c06070f0500c21810340040051400c5684141201400380c038007410705c01141006401c005c1071110b401030052107103079000314030000204285060301c024120341d00039013503034440c14140f81c01a40c1040506ca035280711164007551140d0766150038408038680303044644000c006500300303080010440d1220340703401c50728020000240700d080150000300103284424020031411740302180041c403060030043e0000203203c8403038808101c2030381c1300d070001107900701a020304900180d250010041001100d00e81c2600402081c001080c8030702d0b2940005c1d4960005020760100840d81c3c41540c001d01503590004030714000d020341070f511407100c4858000e0200b0a01e603025030128010801240c501c5d407040090034800c401032418500038110002c405006000c01405102d01880244104848088181300401001b031180e1038565541110f0326056503 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 340035557 1250 340034307 340034311
    0xa091205061603110d0e190f0b130308010603020a050d0603150f02040b0405090901060504060303050a02060f060d0813030b07110c03010c08180f03190806030606150a1b050303010e 79
    0xb08041c2032140313440c441d40c100c10071781e81d4a0500f1034000c1401c4c800380b0b8000707140204070340c001c615020a0195000c1400040d4001e0f114190103484801da080da00d00306124080c4148000003400550507900402c40c05200b03502400382515103242092900c1b204912580c01d6500c690400d4801411f440c000c0340710480188030f10380b05050103150550801d407502900c0c0c03501d80a02e100d2280109c110300b0010b24030403820b500140c06010007c100b0050240c407070030020819000030700c1400151103409c01254001101b07032240d9101e014014000d01405056984562444d0031001e4a41c030b880600800210000745c800100c144900c2c0c0030ba17910034881111809288c0340202c0020701300e0003079141c902200c40d800e510072070711039218203031011301c1d4100a0b8201400d0318082c0702c4415260f1500003c40c40306d08111280a2194280000381c0c1c4054168aa034404c0503202e000589101d80e000505d0a1a0392902581e140600244405428400c07240391840702c0440940041c0e400444050704000018807080c461144429 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 340036807 1250 340035557 340035601
    0xd050c310902030706050f04150e01081003050a030c02131a1309080301030b10030501230711070911040e040c0303110607141804091209150203040b0a09120506 70
    0x1c03246070116004240c641d9524000c030f00c10000c00041300c0138100c001000301d4005184c5120704000f00003905200402245101c003941340000e0291010a584440f0301550304162074000c00078145c404100d035800d0380c04401c45003080741c110811212068a880389807042d4001c0c01d14890950034040040c0040000100900780015490b51500c20150041251081a01e0549500c8200545103840d04d18201c0010013855100500660070002c08207440404204609192526000790014070746035040c0c20794051414800c18103031584a802e081010703808a07002080c080c54480f0703170646041e4458403150f02ea0001120240c8601d5036221b8100b04042c1d2202102c6141084800680300a081c070040081060329203110140200c0c01c00310360044214400c1044c3d07620705100400410008805150880f10555030610803030100300b0190000800710b035400c08488000007568007862070036080c1481c03c0181d80100342a07000f049075401c004104080c550180070450fa014200a0000d45003107100004d5118240d01a2 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 340038057 1250 340036807 340036811
    0x619140703050f030402040e0a0606090f020a081303050c15341206050d060902090106020712080318030301232704050a08030a1409030906090d050c31 66
    0x30109074000141c4801242800e58195a078846000181c09401950604509400307810f5a0750108001e40d0300510803a10f1401e800e1062a00783d141c1c200480c000c610711100810101e00019028490280c41443c84900c281402c2d401c0c04440c1e85510f1520101d1a140f101c0b943e100b40500c840381a81c0c240880e02d507001400d0000707099042d50320510b103400308944c950080c0882080248002e00540d00684d001d41005040707441e00443c1c9042200181c1004d4501380d0050000d0000030070398610228140303095808140c4801f900a44540d29081c585e88000c1c510382c070803803122046074950a410320055008101300c20315040c20025900e41c03440742c01c0404804901c0350840d00c2c1607543c2004078001c00039411a00c0d1170140b800b6565800e285081c4003449074002d0500d10008100952041c444e071003285151014171001025903200c0e00c60598074403554840983c840390030b00c840407030381c0741141d08959410300c518180c800051922010a1102050140c6640328000c241d040e100f0a108201d0300c81038a04c008001 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 340039307 1250 340038057 340038067
    0x108150a0315020f03070503040201232d0d02120109091104020309190303020a0201181a190c0305040b0f0609011e0f03080703020c061309050a0902061914 68
    0x35101540a100003040c4045802e0104401c0030658150785000460089040c0d803854003d000034016401203508030301140f40b0043c114010203c20419801c50f401500c041441e1580341d0005110206008500c1140700c41c180c0c103078040c03504c044000750a6101c01d1060150f19544204000581400141c0240300114a003401c42d40101e01030040080340303858107440059681c3c95140e00c40303040442e4900c04200d14020700d40000c0c105607060380141925100e03a40204006030088000120500e0082405040721140c20030200401d0150707000c0315040411001c0216982064800d0380c1c2c00c0d654081c00304408a5a00e10400c414803140307444040d800038030307603502070766600d03040c0005241e044060080d42a40d80300c4028001095180f51510743c042d2a1100c03610313096560341d18060805510419084005015405070100031f41842010b80385041051207000d0202ca01303181d1030074000d1500070095500151104030380c0000d620380400400c80c1507880a0400c500c203182e1200501801002d04000d18030080401c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 340040557 1250 340039307 340039309
    0x8150a0b12060a050604090b04111908120a0905030604081809092d100504110303070c0614040321030b03030307020c0118030515070f050a0c0813090509070302010815 73
    0x1071455444580f210700054651030b03400202c0c005007070164000b0580070000381448248050f0036105486102c0440c2d0103103a28420031410501700400b440f4149644c1c0c40040c2d045600b695503005080481070a141003e07003217a8032800686003000503502070b5030000e400a03040825134a68206d00e0040340c0240c58564080c200003000742da80b121505070100c00411100d252403d00c40300d02d00b0483c420a41c80040700d84407102c0ba01d2007002080e00380c40842d00074005802404503410007006842c8950781007034118003102d28080c0c00390f4034001c4006010100c108204000710000d500c5401540340c20044000f0343c080003012500141c12158041d0400784650720500821105a50024001058100a280901d13098103124403180d10043d280c2c1008040740121505022100488441d4510540c1d065850036030381d1040c1c01043e600c62289030f60107000907a0300c600030700100b07207140001c2011074503900c0210140d56135050f0f40790489409640750300042c4c0000314100705541c1d1001083e50421662090b003907080d41030f40 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 340041807 1250 340040557 340040563
    0x10e0a0605030c220902041d0114150d03180b07150506090a090503070b090f060c0405060301030b13060905010b01090509130f0302030c030a180618090506040608150a0b12 75
    0x84c0c0000c0304080800c0c1d00060003800c6811420b461503001c0c2080c0006452812603201c1c052010610000a601c2c1c4000c0c1c00700c5401c523000850240c4000406504103031014824803030304d41c400d460150140004056a0310003009215060002481c6003174246844454610300101c81554100c0d165001e02c1c102400d01c1aa0740e16180300f2504988031340c500149828a074035186045029445001d4000010001007081405000c10506440038010040d540c0340d82e90034505190601460140325007280051005000040800d00c039650091030201807a44404116039401c1d0607580005412101c40e5101c0c03211a01550b044034038a03003d400b00311040d29403450808042240e041500001401048012100805042c02801220482da55900650356a40c0701c46002801d100108960b60543d076010242c001010392040081d100b80c255009031040d91145401e600c200170302000384c8032540c095950b402c0000c41003002c100082ca000f5071101c0941a0380307001c10000d001c440301250030034000d160f1408a604548004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 340043057 1250 340041807 340041829
    0x8070e010e1318060e010501081b01050d090b16020f0a0203031e13030f020307050402160303091401062601140c030a060302180a0e03040f18020c0105010e0a0605030c 73
    0x1610303025041c030440300c0d900c1c01030541040144240141c061500080c440650080720030034017054002e201a907a50400c987d541d48142560310403400750400c219039950b00c15001040500000c2002083d0700900b915101c0c0d4400341541d0909000d608444205179070754050014000000c921781c09440c800c8029004241c0f68844d01000122080c21300030b00c10420454a02511000c004c080c0e03030616010f480345071030b000b207040e0504241d11a2089440000e610710b014000c07914070b46180104117041c40107595081c0c0c090400280d00300c0d10000c44d8080042108000d10030f0314020724000100302400c041100c8072000300111301100020710f905201400c8804492490b107681c1000340b0945c1c2d142d9a030b55220358203008244e19000254807255003201b252009140c0a0410701a1045a50401c200b40c030400c5155942d00c29403080c03010000c6d180604111403001c040410220740d8001c4805840c000c1b0450941b807c450090304402c00b140f00c10810302200011520811015100030740040000006400002e85200380b0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 340044307 1250 340043057 340043059
    0x411040b0d1410171207020f011205190b030303040507030b0907050a06050408010506011e0509010e040513030908070609090e0a12050405040f0908160201020307051603020108070e010e 81
    0x40060008042601035000b25030750003840141028508000c0e1500440340420310a2141c2400084141c0e1018034000c2101c0100008010180d450040c0c55802d200040c42480001818080300105600100216020b464481c0141d0601a25070041d00541502180c4551000d80c3c0650300903c04c00c40050f0300050100190f0740c002c00319251a0780d03034009851508201c6d412203504407001d075000081140d040f60203030003917901d00c500038041655030900445081145642940224444c40074010041e8090b100500c01e00300d06160800c3e00410100120b419900c0a941d226154104050740c1d0b0141540948490080c102d880041c02040e8600305000b03241c0841406147c1c9150740d6000e0200004c04200b0441c04a0f60380001c440454010340c45001d0001e40151084074041c0e81041c0c42c03072041e00300611600c060705a100d568681001c1032500044170081440344124154403040106400bc1401013285d04d06641101c5003480080d4210b20006005101c054882000e212140b0303424490360780c009521484c1c04038 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 340045557 1250 340044307 340044329
    0x207021c0219032108070e010311130f05041d0a1709040504051c050a05030c0a0c0506010e010315050f04030e04021b0703050c011b0b0402041d01020702010e041104 72
    0x100e580002444094a4071828940380d24070303040081001010340c00310805142840701e20b05524000301d002c3d10144c0303040300c190002036110040b1100560007a4494203012209840300b40c00e0102010511043d0a01500102c60f10801c5850030440c51419000e0b404211210711b1000f5503400b07109078031665822100c040100b0706924084410b846032040419554011001001801030381050f00f821500c2c3c07030650090030b03040340c2c00b951140d91040c041e9007204d058508a983c0c07145140d58814048405820140009017004120002400132800400078036000e4416030b9403c4140794514a803d90680d0319910074100d20600707140c1002110a1484005035200d80c0506040740d11069410004c0c00a1084900c0e60100307010100d201ca2000c4800640c54056070720034422a82c580e00c4580041d80e5003d40c1c5003607402651928080c0400040d0500204d80c0c000f8800307800802c0c260400c684c6000b1a461810716101c4a03940459a4010366038800c080c0c9140030300540c4c041100250111850401c0c0c4039600480300544 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 340046807 1250 340045557 340045609
    0x509060d031205040519080c0606030f030703030b06130b04210c03080903010f05010f030203242a2113020108060103090503070b0c0405400b030d03050603010c03020702 74
    0x300041c0440000c40908601b440742507000c511b44645031b0b4004564400d4035104903000120281800a90b01d40700100840c000d506203041540d00302d003e0300e0317080d02d4076400c030109009001103415050009006009000c80f884d845a06000d068154030a4128140080c00e0303908242d003000c03800b59250300f02070380e411960f01c0e82e41d803651a011a000d86448402ea1150701d1415000203100740640c0600410349208a095681e1040808070482550008045903280000a5004144a8400270817865141055420713103540c485c202139441540b9401800a00702141041241c141100300842c0501e540182526180450302c0702580000f4900900180102e06151f40c0d050b81d5402c1c0002002030740c0c107882c3d000d441440586080e04001107103802c240b09260007560201444005800d04100c80b4068840505140064500c4c0d0491020380305800404082800c0d0f490485071181c1e10180120480450b69460104d01c90408400b8182161810000201014418020300b401603540d82400140e001e048080a40c401c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 340048057 1250 340046807 340046813
    0x9080d02030c1605010b040f02030f011202030a210306061107060f030216060209010e090114010e0111150601180602060a02030402040225030909090209130c1a040509060d03120504 79
    0x182c89070304200f01c5004a200240000c000c815003002c000400142d41c10b20441c0350003c0454182e0005660801e03015075610014040b03141c102d120202c001d03000500720f800000d09a207d82d11041050030402002501166840d000c26403d801048018482407614121002600b4000c0f5161002030182200f004000a20800050302ca41c040d2800351650704400021010507180c483c0080d030105210901141095010015515120800074102c0d058002e90820a4107000011982004130b40b440a0600c029601e83c241d0002c01000140041d40c5d40c40796001441c2030000002d045410804c02c00000d00107110824030030755034003264842d008941c8600150f200d44491000402034010855a00744c2c03e640c012202003241108148010910b00030b880f11005151038892400a48503d032a001e500400303400046904411641d811140d0240204c2450030781c1034442c1c81c183c04550105030007900c240e40102d4140214600001d40540000c021156207206561641c0c02400461619208a40e03540d5980001030034 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 340049307 1250 340048057 340048081
    0x170a020f070e01030f030e1906170f090318060706050103060b150a020c01050708120c0d06050603040807110406050301061d0a0501080613030e0a0f090b010215180106030b090a120309080d0203 84
    0x400e01485648c00710640c40d41c50050040902003440c052210b22000400da80507000c08505000303004a502840c503003170325004481c11144003205200d400660030440113010407100d10a44d4083c40c030030324011a209031504100004006030416045d00c1e42070800000c1840e070740014405110344400e003415911101c1c542041046401101915031620158900300044103044400a20354124041020022243c807001401001d010440d00204a00010402d12000c941c66070070f400c1050000400106005442e400800e00f910800d81c0a0075400017007400d0002d641e40d0110320a176102c4243d0b1802c005c0c540c54401c40c151740711809031000740b070071466200070411f241c07040c1d07281110350801600b07100e000c2e55900002c0760042e80707c1c8100c0425038a05001e681e11b0b5803011580280d00c40c118003c9a541d07440e41089280020b09600d0980145d6681d4600040081c4890200720b100d03540500c05068220201e00384401940803003036400c01010300d0612a600000e0385036094a1070403c1c040707030041e100c1c3e80765110416 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 340050557 1250 340049307 340049329
    0x11d06040611070513060e0c0403111e040603080a0f03050610080c13240e090f0c0c190c0602120f0d1e0f060b13050409170a020f070e01030f030e 64
    0x508990751740344140301e12500f900200c0448252501a00d501d6507902c0e60794142d801240801844c01035440e50078070507440e14469143c1c44a03c0658040000c0340d401c00003500700e5400358001c032000000419030035100c40d01f1564030001d5990f03a0034284003d10b05400007410199900312100180940350010401103903043e01640d01c0c034001d040c0c9000711942c440780c000c00700e40440141e90303c5065207076601d1003203188506030384501d0513000307402c1d840b05803600102015415070082c0100b15a5005025040c0000410440030f01084000b56a0460540150801620007041c035002001954481d04003030700789084032012254200c1c0569811520303890100d40340ea014000c204c8410881c406100d01e200f0250800b94000c8504480000c420000306680300701081c4940148100d641d42943e0034201000b25041c50781040d0a524480c0d0a6910710034032102d6006202c0d0005400d039401a8000040c0046902d420040d4402400407880c05860750b614640c1c680c03803c42c0c072085008007001001900c000170742e200c4420b000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 340051807 1250 340050557 340050559
    0xc0509030303180d140307200a030903020f04020c0a0605040f1202151812070204060f1e05010201062607080d050c070506090f01050a020c130203010302011d060406110705 75
    0x60b075241490f00001c0030384101914810307050b01540c4090081240250409040614840d801c00e09581d9030041c15511102d45000743c00c0600307a90071030b1180360101404174107211482516010304050035401440380d003c0d4002000ca000c0c0388104000010048005440201a584a08003081c1d541da1884d00b00010070046400803d1959001c00c4500301d0790700420448006004680c29500d69502d44801025a084404074000d0039048003004050085200c4002c10f0135a00140003c601696221800c1032090095030090640900c0e00e1040c0d6800e828150207034001384004d100070702c011420034100061006000e8409680100e1035031110b10a80d105101c3d8900424500094496008a01d14050032551003d101d040c014040c000c4046054940003098540d540c40241c071490b8a403024000660322507001c41003403015071140b10f60084055490008501c1c090724030f0303480540c89501d944000340030707101996984800341d02c0c0380c210f500701c40d11900c0940e4110b5070a480d01c2c0e0784100c4d08210550500010350012 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 340053057 1250 340051807 340051813
    0xb04080d1509050906010302090c0a09150201020901111f05060d0c080c012c060f0f040602030a030b1023070203030c0304030b07052706090301020a0903030e0103060b0306040c050903 80
    0x10004810708038070058115000c1c01d60030300c400e41d20b045140351160b00074007009601c10401c50100c3c545400c00e00c003500031440310b070601c030080d00d880307420101203201da10b180c0b500181c2d000038003a0210351380100381118190000300141001114020000140000600f0380b10502d82d90b84001a407545e01c13050180c802c99044403a850089446102040e168141085442e0100d05080d41e00c440c00c4400d00d02c580001103c013041000003040130420881c16500170f01c90070746118021300000c210444460000c00003000c00da001582d40b8074a001c1c02500707031003110248610a840703c0000c00507e40e0407102a1b10b100390a40c01920085000742141c2d145402110406500341c80082644034055000100410070303a0700491084002e60355004086680c2e00c82ca0340300c1c0741e15509003003503624400c40001e810171501000800b440e080804000c04a401c81e00130390a1a00040e10188080040c941c003c43c1e0314205000038030b000d020341e908102100c4518800501050301071035655103504150341c4a4026074a08030001015 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 340054307 1250 340053057 340053071
    0x9020d111201090e0d12050a1514030105160804021216030b01030203010e0106080d08150907020d030b010f0c0b0c0f0403050303040c05040c081f05100201140c0708070b04080d 77
    0x60321001e010240500c80c8603610f818074400c225140040c038420300d030045580c0d021a02540781105400b800028100e410001e44031001d01d620300c103544004c41c0160429100d103962040c1c101080500b035070805060076103203000710340c00d0020050348031003510b5000360141e8104004040f882e40d0940b03045048101c81244210b5040040308002d0100107490480e07000b100244298811500f405080b110302d44107681403a07001640c00080d841c05201c01c16031064080d4004200d10002502041c010344c02220310400681041800140e4190140b2030324114400a180c61801c2800c1072601400e07a81c18140080c200c02202e80018061030340c0742d0112841e00d614000900c0c0c40c0da50b0b03440d0699070307900203480c201c0d5401420303c03001c81c20341000d10840140e00701d50f42c2e50b1401612882c001d4118810b140140855807080060085032035110301006404901040e800041e062200181200881e84080c00074900a90100030450104100406079140070340c005068103001d40b034038a003a001034412448852143c42c1082e01c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 340055557 1250 340054307 340054327
    0x8010509150a03061e1407050a080901090b13020319020f2806020c0109060f0503180109050f160803120c030c13060305010302040b0405040c06030203061203070c06170702060109020d11 81
    0x1e4101d40049217284107008054012440074105c04045601100050b014030000c0e0030584508070271074104403a140000b408042e244c440050b0342d0011103c6008150800000308118101080540403182803521700d03078503000141c1e001400c0216082540b9110351052071000701301d5540480c01c4880c0c40e424500041940360f80b4075001e502d40801c042108d000c202034580000f101802100180c00301e000b15603c03203185a49a074904925503008005041c625940d80300800000b03642000341c0714400c000702000706041249402c1e40c0e803017480350b40c1040d5116003080c0f052110080d40500f041303401420402c425501d956458120031180e001c0ca08402e80203000c412000905550142d018074180d900a4070284200b2207200301b031006030380050700d000f00803660103401003003d00d22a50195810540c01020030192007085108a40355421084c019214040c09000800907550806000c0240440c8522040494544035402030344800d014030404060307a03000601058401190740c8000d90303250085502e1500d850b8582 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 340056807 1250 340055557 340055591
    0xb01030b010f0e010302150906120f010914060d02010e0d06020d061205150403050d02070b160c23030f121f181503021203180108010509150a0306 64
    0x211065500080510010074503180c0b02c1002e406503021040791580e1030b46035500b1301480244901107810504410f0211414550b9101d0007000030803000f60a0402d02d01b07011050b45c66540041c1d100c18001c1c1d00d00401c41c2c060002c072018942d40900c040b2148070034802c1c41d000507170311b40c100c401441d58408c04100b0a08104030469001e828401c10105003000071503181c039510315004030003a40250080d44204032103403000c41c60340c042c254420300ca450040d041203900b800301d805036080b04401b1500368140c0740c10130040303200302d45880380c20b02e4980c0b400d6400b00b811600c5291001c42d500e070041c1e610986016404000d25002c0044401c00e40320300701340ca41da81c0721060130846040c1e02aa0780d00750602281e07410078005401001440c080d00c0748019800f50b800b110440e4500106641602103c1d004400c1500001690320052410b8800c0e001c5000395075a0302c070100d10b18020300310b0b1140c00b80c10301c40030000510407070700e8410080303621000511840103103816510008195101c41d500c0200700c1420940341040d000900317 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 340058057 1250 340056807 340056809
    0x606120408131401170411030613050111120c0d060321110a0c06030e0f0109032f0c040209030c0d060c0210020f09101704030f08060d030f081509040b01 67
    0x612805102d500c9582a140f200d4410710803070f0000d91244c10b4021200340c541794250300f0511a103101c45070800082d01007030604804413102d07440e01900c0728440b0280603080c080c0341149200035500310300c0c0101c81c2c0400184003401804148000303c0100d0050100411540b041000d160412600b0038400c500c04400c01a214555007000300040c0c6002c0300458090000400c101e045901c4040b07800840d0610108074000d010304031100a0601c60000780c0d00e500d8100b0300c2500400744c0290b80e2103081d402141491200700004841c0d511440c1c070442034681c2021000b2aa1070b81c6071038115009659a5925000030340b82ca2445c1c010303103a2105030351100008001e4984c0c0078054040880c7c0035100b00d54a0107400301d00701c1c000c3c82450104020100450a81d500d0071142040030782046040429048042e14041c0c03005c001e0448080f17000c5442d1a203128141900501c5596022000b211003076070656099030014202d000903c4204103200c030748004140e00044034615034031100c00180c0368503042e1909003000c204004003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 340059307 1250 340058057 340058077
    0x40f02013c03020306030c040b2b0b010e0705040e040602210f062e0c0c0b041a04060c0f0c05030a050a11090601080103080c0715080402010f050c0a0204050606120408 73
    0x500110901d07000b4000e5030b20901d0010050030310341088800384005000000c550640c04041c030160024034104030034441003850200342d001b4031008078070302d0714032103814040e0418070503a0f416104010946074000d0444090380c144018609050300d461501d803001c1d00601e08549050705071241140180041d541d0298461641d01d03641c0742c0c0f1508c0380310a000101400b0340045001c44c0410010228818044061102e950003602c0c0c43e81496100ba16104d0000031281c00c5480c00200c00101048240303c041000d04212200c000c00c5440c02d071034a1409018041200001131584c142c10007204207010014001c0c100915015058429001e81d601d0016190200210100c0e00b0a00300d03010798043d402d00241c014400c000607112000707941d081d42c03601003082e000140701c440c0910850a01141d00028650000200382c4251903941960401c1e10001d484004012110341c2080020b01400868542c0010070a410540603a40000c00ba10743d4400304071984545655940030340a010180300420241d075000b07081043c5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 340060557 1250 340059307 340059407
    0xf0d05150f0901121103070b0f0309150f150409020a080705090c07050d08091903031409060910110903010608070f0806060f2e0f090b040e040f0201 65
    0x108030400880080a008103e0144c56100d1408001000e0840304c0c0d0094800408880d01e140d901c040e00c4000ea4080106803141c100d010003030060551003041152450792100700c803002180750140040c80f00d01c038000c101c04480a2205d4001c1c149484590000c3c1c1c4ca190040c018003c0c0c1c540301d0210740d64448043c8a4a401000520b00003145140001c0c19908190340c048040c04500310b12000483c1c00e02400341503a0843c0c007480f800780f42e02c108088540c40a03148aa24041206845205084c03094100106241c245410003001c01100c1003000c10301238a2007007094400642d811140031500d400340600c080c0907805620701740e00464944030008000c4111107509807214601e0b5280e408041c0c5500081d1900d5401120407140300402e450240404c5000c0705108202214005044200d440c008003d035039110085140c2d4040c400086901249580141814101da940b0302403811101940141000340b0240c0150018074090045a04c03540c1450341c829801030413850341da10507040760100b0304210740c1c0714007400d1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 340061807 1250 340060557 340060579
    0x240e10050102070b180310060914010806070801150e03012c030f07030e0d060c0306060e01020304060c023001020406030c090b1606021303030302031005030a08070303020f0d0515 78
    0x5840003c0c40010f41d001412141d09096404004400c4000404900c60b0316010f650910741c1002a10703c61032004204030100410449201c0a089281c4001038009403610707003003401040742c1250810b20590455840080300d0014045092080baa9981082700070b03641542860305000c04200c8032940c0c205540f6412102c100a0006030b42d8556032032090821a4241400500080c000709024661500c0c40090281440005007407940d51001164178240551010036513445c1c2c1404000c0e403002d0300522005003800190f05e0242031038006030800748c543c18000c0c030800c0361030f042504c40e60700601150f0b201c0d03c1401e1103070703a003000450710b0038043e4001d40200f0300028035054110282c90310511402080311040404a85029694003007110014030301343d4150f039855020081e4840d203030030b640d507002d00560090b0f40041e224100101a460b501000350f11640c42a4401481381010a500104450303030180e050800595400000403030070201d00a807000d0030000c030300c1c01e0200b04090010415868282030100c074019421 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 340063057 1250 340061807 340061809
    0x60102060402090c0d150305150f220627050d080421140309071d04020307050105070327030212060c0a030c0507020a0f030b0a110a03240e1005 63
    0x4400441e0040c0d8452441000306800e43d48060041401000c0040c01240703501924202c2c0b84894041d030b1040b10551b102410041030341e1068013031540c01103280d076040385035410021904d030b0211004603401060038000c1d030f56580c20462103a0100d400c40240405400455410324019043c4c07522007001928a400b4144035002003a22a4208030301c503540c0082020303081d0804484503900411045401c0c0305002031410a105941444c0f005944100c1e040d50040c1415811302010079800310525483c100f50122102c01c2c440160b402050102c10394000303290058441390b0030308003190032013101d00325184801c0e4441190340707405500304000d02c16a8002c0c1c2d56000e01d21700900ca12561540103e40700040058140221a4550b01c0382d080f800c03d002031b628010b410006960000b0b0041800d907801002e0301001c101040041001216041d54000480d000400c241c00d00c40c5070300f00a52142c894950201a40c4010b02088140c5504040c519500241c0c2e9561149460350b00c0c8103035102c0142c580e80b03a4410740840001c0e02e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 340064307 1250 340063057 340063063
    0x5010506120a0b07080613050f01142409011202040609050405070503061e060c120c1204030c0e180d0c0203010b041a041505090c040f120201080619080a0f0b060102 72
    0xc41940303c288030703011340e0750480c08032a0198003800d903545c802d5132006101820400c5024084c013450b08003520b04021752400c09150f81c0b0681028031107001e000c54190400a140381c0c0440605420001c0c0c02080c1c4d10000c0c40012501c1c9508901000c101ca0310204000c0781c0c50f03030300060310001e40d4030546003003240361501c02c0c0c01c2e942d074001215050362006103c69180da218440c0e07818145d00349400b0306194200301080303140300d082410410340d0324483d22000c01c4d900d100c548e0400c161000703003034040c1d0000c1c42c00c0d0440d119409204090300440441451560224103104811b1110310501d4000100351580702d4881480280114842c0806030701c40d6003810991509485e09100d000c0000c03180c5288110200c88100a110181c0b190703070707000b940eaa07400c84000650707616031182d0244200954041103955a0902d2002010440c030b58120b800d810b2400004d41c001030b6000a02c8541003142151011442c42c400d005501c900c0442d90050402400303200700b407004101e904083e19070141c1c49400b442006035149801241c0e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 340065557 1250 340064307 340064323
    0x307061403150316090e06060d030210090206090a1d0606033105060f040308090c06030105011b050706090503210a0815180106020c040c02030a05090f0901030501050612 74
    0x1034940c00304086008203181c1c0b000300d881070101506407000c0d00c0b40001d064071040100d900960f0507a0b101c00c032030b016204090000551044044500c60401d0102d500c00968508546403100c088503600e807004400c2d07699407400d4800f20b01c0010034400342943c6800e074034540103030b103ca444c0b0403036007985001c03c07094506001603074864000c5819050200e4042210b011091030350740c03c1200603242010001000c07400c00d201c1030344100e00644034450036081c28a8010070014004100f98016000799500350202c1d42c909044034111a024a01161804820f07030301d1000c081428200104580b00741072000540542081c8000100c2d402181625181c80b0381e070440a030f290544070b80300c00321400100825140ca5008004d02508590b95048680aa00c00700d400b1501c0d841d640700b0011110241030004007c626810007009030003660a403810b1002c0528407070042c0da01d001d1540a00144180810207001d5078961103501900c2410040030303c0c0140d44d5070304129000784800c0e124580124000600c0800d80540094002 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 340066807 1250 340065557 340065587
    0x30e070302012703020402070b01170a0b0408030601020f010e0607030605060408030d0915060905041101020114190209090c120f01030c030f1401150807050114030a18020307090b030706 81
    0x30071120f501c40b40e0242c00c0404554005903442000000c00582c80e6480640300180c03144034901150b505280d030305d400d034501805002509034041c0058000081e040c18246400c640c2c8038500c00e841c0d40b50040180d0400e00e07584c4d80c09a440d860164040c401e5540003038068080c00ca40d4a0030081103032102d007880628403840c040c44080303034020001d24a02e50085c0d03000f03412260040c00302d01d42c014410941c800c02d8943c95441f840b4120744410920050022000050101070350034002006004010b880c04455007800900d004942c941110402045891940440d28800d070000d00d00004c519003403a8146058000c09100c010480c0d80c3e0000407882159508a03038144c03a0000743e01c4071450714541d9420071615501e40200c4102400ca00329048000c000d001da843e40c0218003880b0b07048a410700e04541c0c03418026501c01410002601150300300d03100d01000300cac2c1e0045070410001c0703a9054480e2145140d00301d010170081d014418042c001444101503881486480340840a40710000c1d6210700440b1440340400c500 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 340068057 1250 340066807 340066817
    0x10b091323011b020c041a18090115030f0c1e031101030605040c0e030c04180b1302151c020a0f11161206050901051509070509060a050a030e07030201 66
    0x454807052081002500000350008a84541000200685845000341c5540542d024024010082ca000e02800d240c2d03c07848103500000c405030400080503528041030384a221003c2e00701158400500790803500e154050080341c841c80595078500803001d4404600c00340c41507455210041942140201800f542c000411070144a45045864900ca10400c50000c81e050541d00d480c000703030a8495000f2400b00c040c0b20b4562035011000342c400c1c141080304a030b803054071603441c3c40e40e10b01c05d001071010f114030a9904031704030381a81c0d030300c00808051005d14501d010b5804a5040d800449480151009050640050742500f41d21125088070800b80d004409002011810003c0300700c209512510014860003000389c00c0300c081854044031302842c59441d42141c08104440e00d400020300840c0d004041c0c0003120140200200d00c0c145034842d0032005164a5240700c1d4500a02246040d8421400d60b01c24150007400305a54081185001d40244d010b40c014001090401d90005990300000c1102d00c00c4030b8040c1c4070303 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 340069307 1250 340068057 340068083
    0x907062604032615040b01080702030d09060f020304081308010621081b030405010207060507021309020d08030a090b01081f020f0d020d0e010501050904050a032a05010b0913 76
    0xd481c0c4031043d502c081030040608401404010300711050318026504034203035204030ba4104007408255085514841d061003502c3c414420b5040c0d001045800440300d001c400510302c02c60380b030888041d0a03800700d1441800d00100c14041444035040051140c60031810f594000c0e50b5460514034282c80e114410454a1002e02c030300701c0d08101c01200101601072003100d4480c6440d1854100e80103c840700f600581541c2e01c0464140020750301007004d00d001d82034505219082440c507a00180c061640c00030303c2c3d0002e03030300c0d10840011902d9400c40e407844140e01c09a03250f2203150191a203001003085980a82c0c0c242c141c54000a02458049030342c01031684d41949440e0b00d44040b40c660406036000000340c1403408030400c00d03504008424405040d4440e00c024000c141c40300e450229900f9594180c010901c151014030a001c00580c0010301c2420880c1e144c00e180c259580c000984101d0001c2d0b1218014410303068114030340401206602022503508221341040d5203845024200440d080070140081c500056441 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 340070557 1250 340069307 340069313
    0x60903030c090a0e0f01030c17301611040207020603070c020a05061c0f0216060e0a021f030c0e0a0e060a050d120201110f070803040c0b030907062604 66
    0x6040682c405400e11240980e207601e90180e40c0c0044440085410443c4d00510400c555030018200504e00e0443d07842500d82104150b41c0c850342c0491b80c038009206180a000840c0601e11980166000ea003030032075441d00074407004c180d0144099130045400c6d403401c404100781c0d4503183c8281c030480c5401030603032421540c6481d0240d951403150581030b0390200340d040001801d0b40c2c80100030846c1d1104950f0720561000703411608016034056a1404035500d0051020041c0b6810b100114002c503600808003042d40030fa0306200508002c800702c00650010716100c00700c030991100780c05250028001780d504215811000c0c40072112040f0300100b80d41c0c001c403040700400c02d141c80000810340050005100d42940e59540c2c00060002036003c01c101c1d644440100c01c03070358480c0c081c851002c0042449690928200d00b0035503c1180b44281c00700248111008808142402031107601c01c0c0161594881a544c3c0c0d0a2481d82e0b59a06c21881c0316050005034140c2980100d4403000c0440c3c0c401c20b070404c21190160b00e49075 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 340071807 1250 340070557 340070581
    0x609060c05070806010603020a020f0d05030f0411060a030207120e010905060a17040f0302070608013f11030106170601030f03050c01090c171b190b0304060c1106090303 74
    0x2032001d0325a8840c41001140c50202803060fa8001d1485440059403819050000f80c01d20202000f02c52080d005104032059264200b0100c951100384501420800e41e01c034074000b16001188aa07041d000320001c1220003400b03405500900c0e800d80076440141442c0183d032400c451311000500454000b401d5400c0c10411070074648040d01e56070754181003e07003218034014450800480c0071201602d84540c50712443c002e054060260b14007903d200d02d0520000d41c1840d0075468800341e0b10052980454040343e40342c807141c540303115909030044e101042c6c46440b69a07080807040d1071032882d00284a54603045000400c0120b42c0b803031002494101c0098100da0307103035403505040c81042c9041035051003803c2142c001844d5080c405c28891510070b108041c04d5908045144200040d2a00c10200c0b950118801c4c1403035644c4088080b0900b20100c0d081040041d541201d00c10000c0d00d9070080c00a020040b050004119558000d9030301008155a10090804000d038001d56403081611401215002007000ca59441404 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 340073057 1250 340071807 340071827
    0x703060c030f1a0a0e0115050d0908071b05060702030a11030309061204050d0e0609100516050c1513060509150c0336121006080a150204060906 63
    0x607040000da040c1c500d1090704195003000b00d5580e000d00784000c100c100351824024000c0034040460071130350a903041c001c0141d1512a08901c00e82400310205080031011144d80200e070010384d10414694a41d1081d00d800d0030503040c14184000400344594012442d41000070540d4101e80c2c005006050794942a04d070991118062000d45415000810805041c2d0f19654010800008a0321220ba000e14181c2003043c1030010034a540c10401c00c40c10041c44081c0d681c070081e102440001c8801d1648002502c0003940d43d40f14800203902c5004900384403400b4050082003000ca000030641d03602c84840b42e180c422020710721601703c0c81c4010003a9200c0074401248100e024000483c4060700442c4075110428941c4095048007070254416800010b2003040081d00b0f02d00e080c41444219084150f010032006500c0e128075041c034030712340580d1086040c800003200801461011313002c040d00800030311780c444103901c2c0c40e03906130041514000120320300c0c03022403016442190111041d59481c100340c00d042c00c40448103d449 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 340074307 1250 340073057 340073081
    0xb09012103200a031809050609060906010c02040e010204050102010e0f06011a070501060b0306040b220906090b0a15080a03080601030c030e06010902180d0f020d02180702070f0b0903070306 83
    0x24080340c0c014000400c403c001c041c1c001d0f10b4a0840402000091468641c6904242c0c06130b828034060105e2515281880390300400212241a030b140c0e954030040f40c040c841400003a502074100301149803a070b41d0650051003628000ea0080c04422030f00c41440741c0d10000c00100111940c4003074010081c07490100002c0005481441003a80360a40540303074542559059006220b80300000030a1100501d082d00c2030440031807055444221922902c404600c0e4171034002014032115485490100402071190300101d038056200041900c036041c104030000040421309055240b9407540000800c0403200050720058180e41039a50115682e611001140640001008507041c90380b54140842c4501080c070215001c6d044569005807104d07a0030700741900d02034503524618010a010301961022401c01481602d5813901aa100c442e444854030206240004c2d40400c00610950034040c003140c00d41c08506001101c8000010780000340d141c03402c0c42041d2042c00c003810783c103500c040c50820005555411058445407 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 340075557 1250 340074307 340074347
    0x1020a050d02100e19030e0f04110a02010c080f04030e06070b090f0c0f0109031119080d08070801060f0e0103020c0111091305090615031009060b09012103 68
    0x2440d954007860401001d2080015030421242d16010007094801c940c0c80c1d1007120000c2801e01420403240400440e003060240802440103854a17050f10354410000030b50720060020016420083d070500169005044118015401e016080c00c280b442900017078000c1c107000d10050641d44841d5001d0304d10319500c03d03d25030000c0d420322500000c40e1402001d28421488000540092080319000720b0070040e0702200d21344900b11a0345058410b0361f00681c0d610a495200c0108489031004000013076101d61201031742d4040c81c1c0342d0078020070503950204451a421105071100c0d005615040740507988200c090150701d0000741c0e00f0406162480c07040001e4145450117060051810000f2070703981e82581da4516a40010400001e44c4d0541c40c01c04030840020340d6280b81d4104140e043c090305082e161000035058151250700300e8a070326041da4040c880300c00d006543ca00200080031280c60101c2c064003044610611031003c24000003a00c4055503008801103c0c189500e008003045a80c0a6803814203600350b03811000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 340076807 1250 340075557 340075573
    0x70e01051b190501050402010906020f0304090e03040f0807030b100b070b042f011b0809120708030a12050f0903091002151302090c0a080a0b030c04050103030801080712150b0102 78
    0x1c801254040b0b83c0258004516882e20380005000b440c1c5903031100303086502501e514590f600000c401c0d0f6040c0d0320754160120f001d12183d0011840c5020769001903c010054040000314080000389200c110380c030a140000d00d90752000803500071080782d40303e50f0312120030401c21000040d80015406034007034458a4800014070f000c1004040e50600d80c2d85500340840080f03141000b640c0c1054200080c0b1110002c1c0c0d420306286a03403541031900405121a00400b4288a80c0c464000c0c02e00044000e020400f086075102c004800c001840c0b9003050510154031881d001c0403441500c8400c5c4881d12403110013005528005001c2c0a02203a10680f400140031400b07092285e023444200101e600f40107591119008054222500400c1610500544904510b44007004148070080c3c1107210598414920407000807124841d1012904240d080e84129078040d203480c0002c003c168002d036026068506480c100e0740487d40302e0084070301ca0056941c002e0b01361941d1080c64644030f6055003181030103040610543d6805 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 340078057 1250 340076807 340076833
    0xa1a04091e0501021b060c0702100207090911152803061703180105120606032508010602070801020903060411041509140a06060f0f031b17070e01051b 66
    0xc00702000007203446940015540c154840c0e02443d030300e81400b000c3d000e08403a080000c216010b074880d81c100203000d03e40b185c90030320103a4024004000103050344072062017200721910300300181c0310b40455000d21400510010715a04206c80c002e440ba01040d04031080c2039901c6071003104501c804145810b5040648826000c14030740300c40d00d40b00070b00440041c025038941940c40300f4003d60200c807040d8641041024031501d400d410700f407940203400000a0f107403d65241c5402d40c8140b0102042d02c1c0c1d2400f035120710f01c501c00e1200e900c9460241203603105c0c2d0982e041c0c903450301c000358240d1040c42d00b07440d850790199011a003c9a0131420301042c100307000b000000c3c1880307000151500c1c01550381c011040310343c4d28088200b0840031440c1c00d035400145482d0030880ca5040000280100c0301c8100740004100d140402114190b000e584030f4900000d550304540f5000c1007102e4010810f13004130320729004000103000880d03101c0d40140d03440d4512082c161a214117010642c00440e1614004403031500da40e00c1060484090 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 340079307 1250 340078057 340078103
    0x6010f0e0f1201021c14010303030207020d0812090f030307050f090a080111040603050606130608040f0b0c0a030f06050108160c06050a0605120607021b0a050901060203120a1a0409 79
    0xb11040c40000035032601640c076403054134141d8003007108452900b0150302101070500d030540141583d9060500503122103060000c40e0040c042d16030000c0c01c170f050010b0030240c4401c90001c02d500c41c41c100da00300c402c4005038580c403d8503030105a0309840405c00074089003103d880c2c0c10003d0041c00c10050078450102d580c0380c03203103800c0d6600e03150312032008a0700081c14032800d40c0c18010241d00c00300946006240c14200d02e2103001ca09400c0c41b03180d00300f18000001c2010000c10100c0c20501c0b41c1c102d01e125a180c00d200001032469444000b07a2030201e890000080780105007401034104030340058650700c00799507030004451b10740d107a90b0720381c1000c000c03a40d03488100060071071090034044c89143c0400035210341401c083c00038140d40080c902c01e981d030000d42003086003580000c0f2001e4258522020301c42040c40380303010074050269600070580c455405400441c4841e4004040c1c2071100340c18031229841d444e8130301060101c402144028152983d8031000402c181002d82013921258840c945030200300420328852a4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 340080557 1250 340079307 340079329
    0x71416030e0301110c06090c100f03020d11030106030b010c0c051009032f061603121d0c0906010807020a0b100b03100311030d09030f03170403030207030207060806010f0e0f 76
    0x32072004d0114050780e515104014140d40300c030b007520051051150820000b5a91500e417121001005580f440800c0b00b24030035010b0300d2000c04161000d0103406a407072000b0000da003090058200081c078090000c0615071007080880074680e04400900181030a25003800804400b40b01c88000340301c0800c0e40040021a505204005040d4850f5003003841c40309041d100c0441c8007044a810302c81c0c8418030043c9410304044003a034485e0799040c18142885111103d40c0d0010f00040001c6518a548034490041d400c1404600451003030000c552020b00e6945000040d214481c003940c00701e00592101c4400c4000508083c6130070b40011403c10902d0000b80d444c110303611168000c48242e0400d80307641d0700c20030810807100012845280c2c228080c000007843e1100041010b041e41c440070b0704451035400c1316401d050043c048401c81000805656405203000e080160107507021003000c500620891000103802c510601d412400f03844141c1d2501d0120740314110842d203041006a0b0705078030402d40d4a4010030ba58920500c28 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 340081807 1250 340080557 340080581
    0x203060f09180c04061d0403020115080102030f09060705250b070c0b16020c0415030206160c0801020304150515030f07030c0b0a0c12030902090f01030b071416030e0301 74
    0x8001e8040d200b1140c0e050800301c045050107181443c40500011240303240300c2801010811300402e60f981c0d50b090403409410070140308010303003224520120f0101010740042d0b100307200c048102e50083d100c80403031560760142100e201d400944240715400c0c01041c030582d4150154150347c050000c004050321081c080000640ba07d202003a29003a81d00d08005802c10201d070b0056180e58038403654011144042e48900000c1403840c1700342d42c0d41d109954600c403490000c1000d5034000c3d281585841070314160031403201c0c500348265000e00c02280c000a6501d014001c4038481c07640210034860103104001e441000c0c002c06010340e40d41081941e06203641751810003a00164281c40c0c40104421881e43c1407850000c00b040d00700d0484480c00b080f039400c40b07540090f4501c036150f5111003500d1803480b00035421801069002c4000707500403c944c041c407a00ba00034008180c162070203518042c1c00c580b41d5182c113858516048041146a0605018003407100010000705440300b0700074140084460302c2c104c0080d0840c0c460381609 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 340083057 1250 340081807 340081831
    0xc01020a081609030c18020c150910091707050a0f11040e01050405030f280c030e100e15090d06090b060d052e0c020114280203060f09 59
    0x441d404003014082081061107081001c42113084d5191405100018040d002590f5800c0070082c000b6011030b03040b901c480402d44250f078001da400303910144250764155103180040c03007656a4444c4010291041c00c030519030064510380300e80e44103114178121750804c28007a6141c0c021000114007060000d203520480e548922000c11040c0500401c1004840f8409084070b00d80c3e242104000003d600007040703c1000c00e80c001c0441d1a046192000e144400c40c400480b03580b0303140031950742046904880160442c038401e0b2222040d1040c0442444444511400140002007103c8291480fa00303040c1078400c900d01400c3344c0146030581e00d40c0032400c0740520307801c00c4403416a601c1e00e610034841da14880279000041141d10140c3c00381c0c1901c41d0396807a0b00784500120410340d0314400b1301b414050b44600300c2d031003c656402800188400203001c2e00074801041c41ca00c1c0014114005001c200340c00c0314103d02c402c84d40859006d41141003840800030342004001c036400203d80c010a03074441d44c84509882c8109030741955 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 340084307 1250 340083057 340083061
    0x40b07090807080a080d061502060123130e0709090311060a11030a050702072402070f0605070605151804060b01020c0a03061806151e0f1503020c01020a08 68
    0x103100d110309500640c425000300009000c807034000b095000c020381e001405280c540500c104440001c003443d9205900c220440b081d00c42d5041c0d00810080c0c1211400b03804081c0d1582e0307945401284c1a603408400c0d50000b940d85c0c0c02c200002c2c1603882107034407005800495240c19100c044140803203075000e0055010480e40e01821110100800480d035100401d45410720503481c0c1543e0101d400d000141403901000d0f15140020b41040c400c000c0c0300b00800500590080303e0241e10040c02d00081b04021210043c00f0394580480c0c040d40f9100d608003162103603980c062410503907843e010020400070300380c113200c0001900011090703641c01002c01c241c1d0000c08185513090805c4c0c907110003260b8041c400d107810354000380c00b440c105039500c1064104072070300b2a80105070800014502c104107000703250001d20440c50412191740219202c2019010798a0a07080744213880240c0c44400d0b43c10381c0a20071075108c460307001c02c01c0c8803101c3e00386034948014509040260038a1001003603a801d81c1c000c41c07082d00c0000e80102c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 340085557 1250 340084307 340084321
    0xd091205090a050a0e010608040807020301050106050702100819020d0b0d11012316020d060e06060a0b070b040813030f030503192a0c0203030408060402030f06091908040302040203040b 81
    0x100a4003c200c1120381003240d5241481c01d003c845014413400d42070110010010341030114a0080342d8115a00070020402e540e140c04001d0800c0c2c20841c811f038040c1c285061628101c60182641c9402603036800e0f00280c20349854010038002e94800004803c4003925003466407640e444c0c03856050002481408020030301565a8001040f508090308281c0421140c40b0000451040d00f40c1200d50054004070501d0b0403040c540080380c1600e00404d8001d1010f0300d085507a00e102000403501134019801203c18a50041d50341c0544c00c3d29005030040030341202d00690210780001d50650050410000202c2c5640d80c1319901d0315480002c504000054004c15400010030031003000500e20481d01040704a010043c00b50003082c506410031020010300c5045c0c0001d84541401401801c2450f43c00b90300804680ea07554841040d261250300c02d40d8101d010f4802c441c01102641c0009c00d003248600c072000c009060905403010005001607001100761b402200c10400072015843e81d000a5100314020001842e80d410506 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 340086807 1250 340085557 340085569
    0x209040917092806050d0e060a05060906010f08160e060408060406110403030c030c02010e040204031406130305120402010c0c0303020c030d051c0f06170f0f0106030b0106050d09120509 81
    0x1000742c0d464044441c0e03107040c1ca0340124004103a594615109417109001c0b6609002132100343e020a103180f080804010079110727660402c40c03065500380c42c5070a403504d5806c0151000600d00c01d440f0045814600003030141100840880f02e800385c0b528018000d1303660080400e0441e4425049200030750441c00810051100b00e0149003141e911498525103014a142c40081484800c0754000342004074103407141003960302c0b40d01e40b00605038004100f196130399507034644101d080c440c408020b4514010784000401194290751030100e400d070961035461a05100c114811000a80200120b050007401070090b404240f4682c8004061440b03a001060201d03141c20426281240715100c020400c0400c0007031600002c08600c07903072004217a402002c90b40140c41038020340070b002c1c40d8014000d2030500059005440a0015031202c5844145058400002540c04098207803a91400301800700c2d0000780040200c01e200c0c00091265407030103140003038400d00075603a1001c04071401c5a200d00056002c51004810301e480 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 340088057 1250 340086807 340086829
    0x30f0a021605100f03020c0f070f030209060a05060f0c030706020f0705150106120e1f02030601170f0609042f01090f0e070c03050c0708061b0a090306020904091709 72
    0x80340d40303c42c030b0600504010900302820320218100358010814200200041003144e260241c0395080e10040c0e521440303000d410302d00710b10003a4401c40b001ca020605a003850040441034540c041c107901c0c41c1020b038881d1910390380c0c001003450b07010384810030410020a6591000e4030706058401c01c295a100340d10308109141002100e8580d1660040b00d00400c040ba801105001020110700700102d00080340c07038100c0d030500b1280d402904259460112410b0305811590013907100c0c28007601c62081c074204803004a1140b440849402d43c90151035008249107141070803a00340e0041c0700e048070007000c1d1070100201c00e164060060f0340d86140005c2d0032906103581c001d81040d0180109801801c3d82c00c0c5440084504003001030300c14010300c9005501682407520610071100d40c176000c032084800190b0340d04540c0350b81e080c00310f8110b10800b2103448441c2c0242d00c0c410850b0702c0002c00d9601c246001c0e0460b110704000b5403040490561084c5d85601d07000010340ea42c3d0001c2c03000100c203c126926a041c2c041442076024035 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 340089307 1250 340088057 340088059
    0x60c050415110606010806042403140a0c03060b06090d0c030b15060d050705040e0702060109050714030402012d08091507170c040306061403010605091611030f0a021605 74
    0x24002d4007035626080061070310741c441c81c2403030010103a131a60808075000707010749071800041c0d240301c066401b00508400040002c0328410821030380d42d92800700196840386240c4500410f400b0ba5080b042000c81c41c550000d41c1441401040300d4500004070000540f4916002c1e4200d0b08040f03100020018424140040c0340c1c040800d50660742c41042c54000241c1034031a800390182841d0b5910b0100349428400c2060394040d0104180700c2c002c0742402c030000ba40d5400244260055141080000341c0c28a02c40c582c80062020780c0c640700fa0039902c0ea580195030301244120040100d06125498414000a8501d1128507510700c0c1c981d001507040c540b40650030721b946400c010106100150a0061490744040c045c2000300c0e1040001c885a11803034610311441c8070782c1c1e102404c81414400e01088144480340f2a960880084000304200e1759110b0501015134412a00c2c050340e02c04c0000d00c0151309016181c1c01e941b40603440d080d00e103404200200d404003038010f14141001a440b02400c0b01c210003115401d0400390030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 340090557 1250 340089307 340089317
    0x1502010b1512250801090506030304030c03121e0314010509090d121404060e0f1c0e04060306140708010f1406090609030d050d0c050f0403061503060c050415 69
    0x340c01808080d5a216140d2003640200c00c520001d112021081600058042485040c0c14942c3d0000e10041860340d080c010004000d103010301041d194500002210200e90b03001181c440d40c5031840d01c07101c0d160a121400e00c0103001c044c2d0b521030460002c4485010340c4031200c3d20f0024410700204407004003910140c100300e00a480580501443c1140014040e1510703010303160510a0000da40e4226010b4a40c28011490300c00760b8800b032200f00001d070f4100920520b40d51045420146041c55203039510050040b1201e002030a092155206500c01d400302480340c80043c00100d40c0540d030390b4503c01140c52805100d04011030030b005101029030b1000c881d500500c0341130780c1d030500b0701d0801001d407004141c010f05961052030001540c1c1d100d511500152030a003500141517644102ca00c4c02c028213181d00280309489440d180c2891800032a02a40030b03100c4080d05126024102815075607110000c00d034020030528a6110740c82c0c008002401400341100c20616582e61a85880c40e00c418010074001070710050341800 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 340091807 1250 340090557 340090579
    0x60108010e190203072702190e06031501030b010504050a0801050610020d050301060c0609050d090303080c04030f0b07020f0610060f0c020306192912281109011502010b 74
    0x44e0300041d59078151040c10083c8402c0c90f41d03104030021000c1801000c200c04c1400416020743d0415401d5500c1c1030061580c4030000302c0c81000d001c12115100c120f40e10441d40e2011081800294440e901000d014801030504514041d10343d400641c141030698801d91850391941d04215003402c1c42a141961842d0a00091404805005014200f4001401080104440c0001010a12095403c0300c4051500308055608100c1d0741d90005003019028001030b8013042c280743c0414061085c400445c0c003100e8101d0007040021b1130990301d4400c881c17000b1380b00004510641d00b05c0c800310841845010f01590800c005101964601035000d40b0781120009500705220260116001503140070460a500c042c412005034070300f080c5140030303200402805024100c07102d40034030030001900d1003084c00318800108896509a43c8003020700f00340d48602c1888590f410f007405440c0c1c841043c00c03503c42126218880c16407a030700480c40101240e01c40c40240d2124048908040e945020b403502803240b0406103105580c844200 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 340093057 1250 340091807 340091809
    0xc04090e210a0c140c0a03050d180807030b09031b15070201061a0702010c0c060201060e011401051204050a0f0c06030c141602040906060902070506101a030612060108010e1902 77
    0x203c410040d002d041c041d01610030751450750007070201c0031042c0b400401160155869080c500da42d00d4806c25850003183d24590940d98800e0741c02d002d8002c58030284000d00c040390171a43c446400c3c0320041c0100318244800d101100f900382100d200603055400c140c0003003008808000321014503200241c440c40079a450b041c1e052000401105a010455049035082961803403a840103c0c2d40d041c2d03404018103201c01d003503004108203a06420082c221441082d0749003890340ca0303150b440301403086280a00e011400400005044d2920107085070780c405d026100356020034101d030b2100115066130000c229044c0c0f41070030061015680501c0b13409402a614078100e2047d540300c2e28031001c98491f01e580140c082e9195004001155120b402c400802c503030280060141c82c0d550413020f40a50005901241c2c01d0003101c1c00510b1688542c1783d04030403100f43c7c041c00c500a0b011540c140300650310240c10150800c0410200e0300c010740c420070481e07008103100341c00021250890303420541800030085210388000c000b18152409 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 340094307 1250 340093057 340093067
    0x2090114030610110f0a05060a0614090a0504020a03080708030a0c080402030a080318030c01050106110d0e010e13090506060108060f011211090a0303050903100504030c06050c04090e210a 82
    0x261038004d0410b43e411303000030303404280741040c1915212254881e6204150800c003004c6000e40c0100900700e030034000d11380c9a2906011124924401c0c80e00116410006400d100607a044070340c000f40090510720b0b100d84c90741c03101002580a0308081e1160880001408a40278440c0b107120164645498051154241980001e480d00521240980f610701d0100100e0030300186071b8a002c040502880460707a54210100250340a800e00b446400c000c90042c141075a140a00491607241c1a4002da440d1707003014512900540c0c504803144400358000d0040042400f80d20040c1c482c8803a128060341c0280a10719103c0001021000700400150003940c1280c04040103903003207000302c0c5c40d0140040000c60828040e0f811803140d8082d04e019075a01c518410800014035070000000c21b206441a002d803542c0a500012402c00e0351020b940c010b000403140322500003c15040d901c1103800c00001440306250564072100c07101510310480105046402044154418404001000d01035519182a05041440070040942 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 340095557 1250 340094307 340094329
    0x141003020d0222020c0a020f03010e030a030c030f0207050a02041a0f04050613050c040e07030c210603170d06050405060d1412030709080c0405060604060c030c02040609020901140306 80
    0x4010300d00e44058045898140c05809a6403c81140841d103900c40415150780e07803402c20805034080c0c001d5500da0708d006e05041c01a586940f0550000710310b041c4140350120002c0c4810342ca807401b090f80c0d41e6011076401d04d050000b40ba03803074080d000030701c003d02c0c26004100072903500040b100700c2080d82442c1428a03803980e030005104a2000c5500080710740c0c6003004514108842504c4441d03032881c00b400c003c0c1510000c2c4c00741041d0741d4030070784801c90740e03071101000c0c0d040343c488102c10400f00340d60305d0041d80509109840d041000010000216a0990b60341d90a0446448401150344c025808036490202410768828035000b010101c0d000d01041c100000400d4400c080c089003d041034440542c0c40c18220020000120070303003051803410b90399140c00f000050915410b401801c60b14010900008940e25007030007140c0c0250001841145041d2610358150349580400380308600703200c50b000724040965510700c1808002c04c440d03000581e940308070500041442c0300a00744000700d0b18050061008a4440603004a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 340096807 1250 340095557 340095559
    0x111f1e0e1002071109012405070f0f020d0b0108030a030c03090215130b070803060906190e0901140a0e07051005040311310507050406020a081b10141003020d02 70
    0x1641c410381414010000f12182d0040c6802450703c0340001011a1f40701c0580410340d64010702000c42c001d805008980b01d1040e40006031454416018074130225501e00345882d0f140e44000c06080d41008141d032202c040307503000d0388050070070f07000481c03a0444150580141d00030f141c0c0501c0d0030000341125600051489001546000049101244032595441c0e0002e824016000f250440c50312076070030b440c00c003d1980c411a003c4d802140801d021403007130704220508064203c4402c0869887c0c0d414014000008080100809582d640768001c8005607020401241e019440030400031410250102c40240303070200c45c1d80400c0c02200f815070b0803020658801c0c10356040d41d5004140f807101239000800a00300c600007001e075004160040c241c44000f2540d024045044104040c1c0a00c25692030140c1510180264072400c07025810501d010070000b00140020702034000f074889082d28400300ca4001ca40ba1800c1d886000c002542ea481c0034040c1200c0300b1152907400106c2c848141205070969010400c003a50f440002 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 340098057 1250 340096807 340096811
    0x3070c0b09010e130b040f0605100c020103021605151b04090207020112050f040204050114010c060f061a0307090b030402010c14012d0506150a111f1e0e10 68
    0x1c00560710410701c84400c010020007074007a000d0102e500340300078005258010f00c128a01080b03c12120341c4d40c004e03d42140e00c0141002108583c0c2c080a803020707039200c00101c1c1010f50803c20200310b10403440c581420340d07004400521001d80518510240154080c0c000c1030341c5e030610400003850812200440c0c090302c81e21580540c554416100590740d045100d0380c5110ac090400341044802113004043d40c2c03243d402210103000710b981c4c8400301090340c401d0140f0540002d950b1603031800450610707040b04158101900d00052150f40c0c89074041a1001460003031031550301c001060000c16035109403540064101420030505e1410294000703041c40411600003821001101a4075200d10000c3d84a07200085803089603018002d0340c140b4079680424000c2c02c0004140c03412012515a080500101c40ba80c0e08840342c44e8a400042e100c1500c00d40c1c00345020340440e2068100d03400c0d001d14640ac0114101c6038040c000301e0b420800c081000346640c0c0035508013035120301c1c0c4003c1e25a02000040d060110403018000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 340099307 1250 340098057 340098067
    0x81305130b0d0f1410020c19081608070b13150b011e03020c1608010608031c05061c0c030210020303090a140a051c0201140f0402010e180f040c0803070c0b 68
    0x554810400e804c141600c0d40201103840880901ca0340080442d85109070076540101129607403401079445540c0e0182401e070007407012031981c0500740401924a8016510b9509002c0035942e2240c1c11b080444170303500c6040c141d010340010816080c00241140c040c2c09024810b080402000034402004905c50240481c00000d82109090099044804800c0c45000750b071028201140d10b11680c0c0002c1c0b150704030661034001d00160080011054403080b80c00300f09100000400916610f0140901800c0e8030f03400340c040c0b03052200c61640c0c0c480d400d034103500c140c1400001e03500e54010001c0d1400088502000e40d00200100b1680a2020032900710150307001103041d11038080d0001c1c041c603010482500404a1080d90f0301c410850804400c80c0c4072000c5103070300034010048031100410f00600c0c2920604607103a6581d002c00c0066005a803000450716000d4092804445050388040b1186020b03030320114001481d000307000611202c440704401600303041000b1403808104d139030b5584181d40c41b07100340c200d00100401c2c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 340100557 1250 340099307 340099313
    0x20105040321230f22030f170c0d110118050718020901090e0903070606090e0d030b030c09100503010203010b18100c1e081305130b0d0f 60
    0x810396024503000b2000d0400580c050181808203408058900007044400e0500c2d4064550000b07000c0c150002d4503031941c1801d120343c116185940088406a075803040000000c4507a1303110358681c1000754050784030f00c030440c000380c01c181e0420030040d4030645030344e50200000082d51400188401c100c000350329101c40d401c0e01c610b07901c500402e20380310f0031201783d004000210300b4040e00050f01c0d02a100380b83c11b50480030a01c1e103100c5040348140d45010740841c62954080004c0280c0d01100356002040380c1c166850102c2c00d940e80412a041501300901c11075444107064120b907030130861400b0340300490900700010303040e150000c0d5a0b036966281d1070784a994040c00242488000000141c0103001c050300a5450756140c0740114250b80000c0c640041d01400c108401e0400d14104080121107030032912410000c00345500c2d1036240f00300120443e03041e12003d120394400200000000d10103640007020300c03201c040c200340401c0b6020814901c440e02c01c07030408844c00c145a49420165500c20392009081c0c41c042114a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 340101807 1250 340100557 340100567
    0x16020f040222050415050907020313091a09100b0d0204031a04030f0f1205060616030302220f140118060e0f0105120a0513020306090d080903040e0a090201 68
    0x1a09581181c004140207004151140b0202400784071039014220940c1c84800303000031030744244c00c01c1041c0360446400300a18108480c105410041ca072050b41d103490640c6001d80b0701d0204662019081c150b135040f0000e8460b0704082c009240c4c1c4c0d000c41e036030402030400d020030040407003031801a03a803a20b200003840711407102c1d40c1c0c1c1207400659100b4800b41d0340c038480d640660059041154107038080744040a110324201e10603050011080810340301c030654150384852140c01440e0050003035801c03400130030242c4000036424800800181c880c3d5800340e03468800c0703c1c107401a16030b0b02c80c00000d031850303034a002c1c440000707407072030700d1050301e4403140c030000ba20003114012540e890000b9240526860b0034000462100d9001c8821003281c042940c140c81c03617030380c03070001180e29106141003604000881c0c070203c3c851102d5074128540000e82c508407441c41d1905500001e0400d5000d0700c0c10710450303003d4940380c2280c5070440540c035405016000a5400c05240400c810000300d0f005180c1d609050b07a500c61601160301803 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 340103057 1250 340101807 340101829
    0x9070f0903081c0915112502040605030a1b080c0f06070804050a0e010302210303070c050f030c0c041503020603070c0602040e090102070201030b100c2619110a02061602 74
    0x1010078841d4031134030709005221011034043e1719210b5040c2020000030f2800d00085030710290040300c8107001c07000b00082491080c0c481000407079000703072035050020350b9550030030a81e91381a0144031070703400e01d0000341e0ad40060045c0b03c0d40104440d410011408078103270b540b4003d8640042054a4440d80e81d0100d03d0b2040840c811500a00d0340002002c0000c100c1d5000d50075254107991090320000b605480d0745585030040341c00507441c65000c3e8400c0000035881e51050070180e603000c1c0301c3d5040301c61000f02d0300350503403c0d84c10000c00c151807503002400318a401d1a10303000b603601010b445a0b07045603142c159004580c50340b100414000c10701c201954403000304040d65045030000d200d0102d12400078100300c05810302035400030310160300090418190541c1440d0410b00c50650790b146e501e4040c3d4007091950340b00d0800c5032403a400184448000188181e8401800040180c031820200f00c1c01d84502041d030180c12241544550046076104420724030060f11000b0071900e0a2400a500851450403840005c4071220341d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 340104307 1250 340103057 340103107
    0xc0809040504080c0105010b03100510090819020405180d110313120203100e06060d0203100c091e0806010b030c0c100c120b180402030a0b07080609070f090308 70
    0x40d000401c418000c643c009005103500103070003031209990314010f02031b003800f060350085a494080141000075240040001e526044107041000c400741d907504015081c030541001c400b2126207080c0c800b10862a081c40380540c4101d400040701c10b40f20180e40400e544800078021329090001464010340400000c0096505203070381c4520302d9808a0b255034200740c0b107900b88d180490007803051442008580358140104140000030000400079503660101300800329a541e0000d1381c042c00380c3e001410103854640035140c0e90f04202c0d222991014a0b01c43e2901d214081c24440c43c814594195082c0940d240200d0b0b800d046a8440c0c100980300c0c0c4814540c0805803158040c030060b01c1c0314401c0e102c01c2c0c42c0000d402014440c91580c940307196980c0050301030030940b0140a11298046041504a404901d881c2303643e54106002030215140b0310f0742c0c0d0762440c4002209031002008503440404101c600e141c080c0c00203501900328507190301843d00491018200c2c8000340401498031001103100c05178144c0100100e000c00ca0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 340105557 1250 340104307 340104311
    0x20901021f09170910080c040b030c0a091a0d05040c0e0a060f08070e040f0303020c07030303050103020f10020619150e04060f090c0306090c0b0c030901030c021c0c080904 75
    0x540350749001801c0c400d90455400081980d98100e65000c402551080c0e18050405101c20b0600c5404607103410005200859100051102161400300580514464407a440e0350307598950144001a002075056801080d401c0300c400816420b251850041d070b0280450380e039001c1610707251450b1644900b03080d03401040010b000d650400c400d800040e00104100c0700880d030b44511841d00c51680c1c40c1c85004c0360207400315021605010500180340d4a0f03079022141e0281ca001801c104181c2c60090801c85580d00c1034001030385401c014010f510b40042c448942c450225a840402c0f0321040e0042d4640c07034010220103000007402c41003056000c0c42d40121021281103200302010b1074641418040c0e207501605c00390344c250714201a102d0242e51500c10f1081c0240c01c41001c410135485c43d40d800c406420707103c00c21150b0503500030000a0700d034031100140408016140181d91200700c0e4000040c1114501750365501154040c02001000c0d0b42c0e0300e00d610002c0c001900d04090703844500c0c140008140b0409142c56000342c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 340106807 1250 340105557 340105603
    0xf1602041a09010e063d090828030516080a1d06030f011505120c0301230a060c081e0403030206010905060f010509010309060f02090a08070b090402090102 68
    0x481240400341558204880071541c0c0e9803500c1244d203424208603203580e04030400d00d140b08a580c084042e111048044000c050203a00d0368000807220002c2110040d001160031403405000c801d0052082611461071900c610400e0f000d911061401004100c1c0003074103014002910f0b04446c1100301065003810307080140e440d5107170611b6400400d80a4210803042c049503480d1609503291030080110303402224590105002d0341d00b00040b030703011089209140fa090000400118030400c0c03458240038450712580525a86941c500700ca011905800c40c550304282c142108070103d00c55442005980c1959102c5c904607a41c0d1410346000807481c403c01c3e284c1205140100c04034052180c441c002003040d2880382c0d0030b0f40c1260b40c0e18005103040d10740c00d9070616401400113031103540c80d500c290040c3c95242c2051602048440d100d0310b405085400d040790701450541c00084520f29414214001c1e4002d01100d0018240b5038980596100c2e9130182615943c811030300040c4481075a0300c2004802d40320400355402380844 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 340107913 1106 340106807 340106831
    0x30324031507050c06240d0f0b0a0e01020712021e0c010f0c06050901050a0b010f0507020f040908180102070f120b07110304061d040603080f160204 65
    0x100c030074030407080348080c10070005000398441184546c0120800c45000704214055080b0b40c0074070304110302c4a00207410349070030194458000309242c5076600c940141501816108140504d19800480d041c014082c41600000c034000035034084508140307460328064440300722204180c6113030304141c0c01000c181d4012611890380340c1240c50704154031101a035070a01103c00907074060750603039965030401c206007140d481103140800090030081d038480403e600040003840342010080c01904003500511507900c807504046080c9a020301d205880f00c0540c02c010902e029000744040c0148203441d4005400c65107144020152104003400041003801511141100700c00130308414100031001c600c500f0030440600c003400c0900307020fa880030703107070044007241c0d607183d007000b6011910035450b00c042000011415001c0300e020001c10a4142e03201d141400e00b2030001c034140c038006500f050412000b0002 = true := by decide +kernel

theorem cover : BRFrame.Cov 339928057 340107913 := by
  have h0 := BRFrame.cov_init 339928057
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339928057 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 339928057 ≤ n) (h2 : n < 340107913) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
