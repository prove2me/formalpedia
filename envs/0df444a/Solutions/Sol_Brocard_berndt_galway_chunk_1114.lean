-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1114
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:17:58.637811+00:00
-- url     : https://prove2.me/submissions/19b83377-aee7-40e0-8bf6-4414466f18bd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 200179856 ≤ n < 200359712 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 200181106 1250 200179856 200179873
    0x30405040204080102030609060406030f1b12060b12010c1205060a08030c030408120313030f0917010608070f0b0f070f1a0403270510050903030301270501081002030405 74
    0x8030342640c00c640d0001c0e625940c0401085170905001d8242036001504841c1003000070b0035030b0f41d007a0b0520101d640240c0090b951040b00d80038540c6030303008040034040c4280300300e010101c1c600d094400f408a01d885540100c141c0b040d00a0004014051124000b2440d01c03050850400d0003040401004d0007442168040e034000c00010703d03071209100600e1559294405542d4440c14510301d079103041031402820403480303010010810800030122040c100740b98145401040c100c0b0340e890031542100030340c114a02105084007040801c00056200038221941d40c82a1050a5034038401040e84060f07610a031501d03d074081014900c0d08110070003c14049100d01701003002402d1980780c803c0840c03201e0030110b40340007202c810300c024180c1149000c15001040080d1382003005250720781590761000c030b20800d40180555403030040c6090007041620210300c0040e00f16901c83d82e48034508110000c9a1519081e10112596520181c100070301466060f0fa0601c001840d000110f08100402544010003d030780720b01402c0ca1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 200182356 1250 200181106 200181109
    0x501020702060310030b070c080304060203060d1a0a0605010203031009051b1903060b0711040e0a051b010306080a0c0315020f071a16080c09030a150615050a0c060509030405 76
    0x5540134980e0355101019050451405040201010f00b00303c00340601e00c201500059840310441c0d074803580c4110090703107035180d0102242d111444407000810f40001140c0d0180b018850601076441005020f005100035982c0303400581c3c40c3c0c8001e50340e0000402a030b10341404990714680015800145240070501801c040501000e100e820070004d591100f180c6c01945100c03550b15000c2c61014140c00c1c150b40740fa081705a80c4401c1c0140d0281c170b0860145460703151208070004140481c3e43c03415000016a080e00c54962502010740360740550280c0070070710301a0082980903000940c41c0f0810760004030149254150b8032014000c020049144c0c807803e40030484120f4210301080078000b95403099641c07825844429143c2811158000d001059100c01c00d404004925400100700342c01ca04107060517903540140300c0119040540411003d0420312440780c490b5800819588120112040b0004000408030824070840340d034401c100310b50000a03226001200440c400c1d03400107810070000b90440b0718050f5240c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 200183606 1250 200182356 200182369
    0x120f11070e070e0d06020711010302030606091905060f071e23031c090201080106081501030f0b0901060207030317010f0608070207050301050907090501050f2206050a0f0303020d02160603090501020702 88
    0x4c01c100c4031590045511010003265403020b04c240c501c00d007420750440ca8071f0408500356000b00310302d1500c030ba00700c00341c0c040400407000c1d50b4002030b01020380882d940b10083e03daa640d555002c40d000b100d25100c058100e60720b444031007500001140c0d06c4400190358095003006000e501e1a01c04402d4500e000c10400c90007075420050a400f8007100d450000710780a20180005440b44034142e1040c4240700da03d80800061805001c0140d2070050242000030700e900121401500404d10356142a4000110a00105039980c0005004040302c1c4655039043e040940e500405561480078818251500e02003017007401203034054124150300031294030456130b1003030781c41c0d0000f82900c0d019039044126401480f018410080c2500503d40540b2040c0e410138100041c240c041400d218038071103c2c0301c4800210f0700d00f00c503540e40ca401c004000c0200410754205c0585420030014450b0300c0c4c1c03008501601c940980204032500204040795031021075031403509d680d03161010990280517901021a100d5600b009050010795405 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 200184856 1250 200183606 200183629
    0x80a0215040f0311060606040515070204020301030b060306160c020114070606091a01110312041406090606102607051c0507021203010305030301210609120f11070e070e 74
    0xc0701c0a10010b0894280644401005100e02c0c2c0c541d003001c010000c0c50b40740c08044400b1503101303440c005000002008880c481c0e000e0000001d40c45800000004140001004141d0081c0c10441c10b072021622520361004c80045858010b101040b14202800c0242d03000e04d0103000100040d01c600344c60b05009980d0282107030069004a00c44950300e00d082c090b1211211240070a5900a0070401890805150050340d03a025401d074600d2000e0390500041d003084450302007541d40c41c1001e011100d0301d0a003c21082e803a04011030343c003809800b11104005c09035100e511241070042e254a1240b140e00040c0e203040c1c42c6200f008001c801403110820080c6120f1076415a0b22020031081070b1300040b10b051031140281072444400068012100600c01400401c00110440c0d0458502c3c1741d001040c44401d4484541c00d110440014000520b4080020140300c4805021000704006558892280104d400203030f5800e45445094561940105414070000c8450130340940c20215609240041c0c0398010001106c45105 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 200186106 1250 200184856 200184863
    0x4020d0b10030309290a1b0b0106230909060118030f05070f0305070e0901060f060203030a1104060905090a09020d1b140d03030b0a09020a1805030a030c080a021504 72
    0x90300e00b0000d055000502d040640f90311116100410720b1490891640c0503961280f00f44082c0c00211034200c00d0242c0c0041e080c0814058118081e544d0f141840c10200c0801d104031800f14039680c0c010407405201d80600803a10080e0155107040c0100c480170302440a40050550b41808034003960740300c01c05202d2550200452003920328058800c11403501a050025036800313000c0d074400c080d00901c00184007194a10130384031020080030283c0c0d00da1681c24090605580701880d82501c00402041712a0b01100451217070583c000144000c030550b905005240c0315610801c0006a041c007400d2089140810f0140c2d0051200381c4007141d050650307000039100d10b015060845440300200954031600140084030760040450040484140007540003141901104034030017402c15030b4425240d209070341c602c03401c6000f40000003021500c800c100100504143c9003104488890001640700041c50303e400203800b81d201d507069070303444d080800741c0d03541008039046081d6130740a600480507800030200e800da1a585c8078900 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 200187356 1250 200186106 200186131
    0xc0f17030a1d0a02030606150409020a0302040501260c0a050403170406020d0804050c010c050f070803031f150e0a030b0a050a051303020a120201110d06080105010503190b04020d0b 79
    0x41031246240000d454071400030b550000d48100b400350744d0124086502000544003200b030064403c4003001c092086800420b242440454002d65081d0b25a0192003580c8003038032500f45c021044003003800090120255441c80d600c444000485a030f80f0b06018001c48001c07814120705207a10390351084003d62005880326a00c14000c6420000d03d603040024840d00c60301403c0c403801906140d04c1d0161a60038200e401814000b00384000010020100b00e10400500078000303a505141d101d000041e01ca0307000f694600c0707002c000d4040707118201200c14643c400300c403404800190585415482980c480c04400e04072544010380301400800300d007001c00458450880081c0025103460310206c41401c564014121401c01c1d900e002c40f1200198000800001003500561241200e01500200728054080d14450204609000c070350402802d6060300908140c03070135540244441e030380f54024103039608441c2071032600f0f1002e901c4900000c502c2c2e2444081c0c001c0e0010700444441e40d400c3d02c59108451007983d01528004 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 200188606 1250 200187356 200187371
    0x216080c06100609030b070e0111011a090a111b070509090102120a0204060c14030c0d0933030f0204050a180507080603030d0e010e0a03020303070f080105010c0f17030a 74
    0x41d01c41440b080540010b08080d0015815504c40e1140c03880700030b0641c81403250060240c0c01e641e004140c1c2d5001d598107030f4002c3c8007202c1540c1c100b5419580742d4502c0f50081e4407086c04503020000900031001e4120034048014100803008051103001115003458000c5405660300c0454562107480341d8070307c0384034940300240e6181075002d44101c00c0100105042443d5106005c2445125400f905440341c15400980d454502d035110308005065205000c154141485801c2030441c0182d0070041480c01c031442e039000c0800b1110070700850f00c3c1c2c8400c100c0d4206080000502d02d070050781c0c0a64020b0781c40400c406001810542c9480109804e042507400c03441d401aa20310301201580c125010381548000c2e01c1c90400366500301400401da81e030058040e088807203500c92140c541d903100254041c07150782c0f0380302c0201d400200c0d035410040e4983c1d00941d0030200103030300410704051007401404818126001030b5603513271420f1401c2d2244448620350b07039021034000641c0c100462100059901440c0150180e8100081d180d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 200189856 1250 200188606 200188621
    0x303091c2109140603010905040204060e07090501020105310f05070906150309030813110d0615140d030518030708100b24090310050703020a09080313090216080c06 72
    0x541c41984031103c00320540c00c2050301038403181d090f241102c0c5207500104170b035184d0340300040180c903081e0014006c0380002400c02850741e40c060500404c0310020f800802c90380e200c0c482060101443d81050f2816a56065600075900035480944250180291858152441c0c0d95850f241407500e10342c081c1745115140e80d014484503c0a561881441035241030400c070521003076a02074034040006003203e031521301d00e0300d62006010b4590200c0d5060a0000d1110041d80c0ca186060300051a2600342c06400981203680420810280540019840d070010804101103d480da01101c10b0741c090465400a1140c11400c80c103152000c201880151a0460103000e024601c000c00f0000c9680c40c0c60254880c1e0768000251700b0401030034031206680c0d01da00440680d65402080400c0ca4520071000600c030085c900f400b00b01001d075066010f001a012165509844a80e5586c0210381c0d81c042c03504040c102d03103080481003007041c06a90003810390030b400c0d200f01003c00c0d07a01d407210301c1c480e00081070000d0075801800400462 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 200191106 1250 200189856 200189867
    0x5070503042601140f06010c081911030c0a0f03090905040506180313090c0e060a232109120409060f1703070f0c0315020d0e010b0303091c21 62
    0x5803400720001300800303003071102d81d0140c018020700386200031000000801c2c0303542d01c221418581d4030340240c0d0780d65803588031181c0c0c01c0c0c3c4000c0032a1048000b42c00c50f241d03060401c03008800c540e062a022001854800303010344854124607407605084007031211280002800f0708030f9003d0a84128000c3c801782c092440d145001078000d2400803000b480741c0e00200321701000301c45000146020f88101c03401c0020350903100711054a00c007642d50f17407241d40640c0101c2c48020666001c0b6102c45144a46aa01c443e02c40c0d0b540e00c00d410174011035460b14030040104510314282e5102e1500c0c0e0303034482d54420456840303011400d03c03030702c9641c040c3d00010708184d1030791000c1c01051811610701703004003042d1000d0400c1c0030b1340700d0700d180d1a400b85120041481c0c0003800c5880500202c00b50400245412085410b2621040d03e0084001d500c4041007107011810200806d017042410300c13031291000c03005800303186007403591b10405c00102c4414a2410342800c80070041130206d050200c401407a0000015080ca8481d20380001616 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 200192356 1250 200191106 200191169
    0x9140402070c080307110a0f0b1605120a0e010503070c0f0c030605071106060a080d0c061b05070b060a0b0315010c050f07170706091521150509010509010b0a0507050304 74
    0xa049540c2c0c04001e0f15040e0f0300c0d230340101d40010410a40710400900e400407602002400035100348a00c0080d4903503440144024408a010b540300d56501d040d5000c010748081c0000c4035550085141d600300e080124070280c60210265100d40620206152260303103400c03c480d07094641c0800100c0b0040d1709a00303100104030064000c0c50445400e01050b00e080c40c0107a0340c01d0800700c0700042110b1910b80c2d01c104140c517000f8451a03090001003031508407203604000c1c02504485c00c29211880703c100401d001e402c101c14250182c81522030760341c1c0ba640d2045903a002c8609003102c114104200d00700e11101003881880a14200802c450280038180e1410700c055040c42507002181040340c0005404201140e08015904212029104c1410a688100f001076410204040e14104040f40c1905600c0b00c0c54180c2d803258803100c4c5221440b0003a207445205010003080240222608240040c006100b5594050050300041607681ba19030b01e13080f40b966402c5c1c159001980038040e0841c40040a40303104400622050 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 200193606 1250 200192356 200192359
    0xd200303060904020409140a050c10030b0a091505040617070602030301060c06090201090b0703020a030207080115090b03010b06070f060c0f0203090f060408010e03030901061509140402070c08030711 87
    0x1800d50a00c28002203503482d01800080c8190741d04e01207642000383d403404900461043e80140c0748104100c2c00d1041d11401c00790841442054416004001c85000e032150a803928006050b00c10001d040642d080000c0c851601c52190441d4135120000d516a924003031880500600542d0210780d07025861035a103050440d401400641d0018001031080700e40c041c01141c43c0e43c1d00700f040403415104034001a682250190403440b2520310009101c01031540010354403074814031030390071210351070781c2c1b1181d19017240c501300766040a07148806000c0002640640016081c14401800000da0b0074250001a5881c3d0000c1c00440300c4000f0200d500e002d21885100390045005981082c2540d820811030003501e921501195034030500d0400c07880d10094942d03400340e4000c2e0110300c008121a051409a107550380e0012159040c142d801c00d0b5001c40c11007581d0040d410001801c1d11000b010900700310f04420503808829040d82c005078240700001c0884c1040e190040107002540c003a5a54401c0f904160301e50074480c44085c3e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 200194856 1250 200193606 200193613
    0x70311041811130204080124080d081b31030f0818061308070f050102150c0c15070e040e060c0d0b03010906051608041e03030e0d20 58
    0x15034490720316211107203503a1180c00040d01401c5a070024007001c440080300799400c0c0c80420f02152040c81548100f03a01400300b0100c80c0850000c0300000602c02ca240200c480740d402290700011414090320344142c03c540e0703902b025100001240540d45264009821500d400c40c44646005500c80ea11216034520011845509000c0350a5490310085d00c0b68408004189034400140c1d02140e0420148241b6541e400802d01d6aa5550701c0811a05014403030266a2a034001d030580081c1200c0c507405072100310340041e00902581c07480d03030000c1c5000c405d004050003200c1c5d808001a100754071b001d010b40c40350807600c051a0800c505140342d009004142810402e40602d20b07000e0448000306001031200d6000391b000b440e190741c0e00007001040d0003803d03144800c3c03901507003401c0e028000c0080071b030031440c40b40e000c030141a49460062001254500310949020301049098020300300760710044d000f0914124044e00340860481c4030480d059203000c10082803100026059080516422070800b81c41c2001105100203 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 200196106 1250 200194856 200194871
    0x8010c0c021215180a051006050f0f0f0909070812070605090f0a060e030904050907050907020a08030403081005060c07050405010b042312060703140f04120c020402040b0c07031104 79
    0x2c030700b40280044d004504403a0603110309241d6803001c021044849034000b00f52000080c0c001c81410103000e581c000e90348a014043d401c2c01c07407400c080b8480010356038000c240c08010071312502130104030710010701a08801c1c0601ca42c0480c99850800440782541841c81980755a940d25013441002c03a0009802d82c0e046401c240e18a03a030b802d0000030b40b100700c5030f0040000282100290030140c03441c0b03d0400705a410a04000070014005c002003641402c0342d805991000341d40e40d17412412621100e2030040206075000910200d4040f9100703c40340c641c0981101c0e24104401d8440d0006241508543c500c212140c0c04004284058109130042c0ba00405545680506042c20a81e07040d0214090080d5003200c0b240042c2c2588136079641c49a5140c2150300354040d50a282040d800090180545045407000d81d190b070008641e181440071300c814403841c1c100390284914090218100c0354158004000c0e640540c00f484082080c1c454034000b018040600d00c0100002d80c80d41c90482180221000b100c0c0c0f20347e250000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 200197356 1250 200196106 200196133
    0x190806101d0a0618050303040b07110d02090f09070b0328060504060b07050706051e070f15150801090519030201140a0b01030e07080c0103021308010c0c0212 69
    0x1100c0901005504040346500007481241e40030014541d540c5900c2000e00100140242d00700e2002c54400c0030700301030310313200c0358403541416607912452003000f001c0e0a0400c807076400704900242c040c40704200108107003c0e021082d00050480c41041e40c02c55003009614003800301840b800c1080070000c00e481d013200c82c20340c40c0c4034800c4804a100710b0500d5a448055000b4401a1850782d807003080a80002881000031a440d40e41c0d402c80d90304280400c40d0076100300d40380401c1040c02003043d19507800a000d0070b108040e40f0f4102c8402c90303810900e800c070740f0b05e80680c0000000401486401c03800d880a124000381d50581ca0038170035910130441e444103045034500400e110100d50040ba06124040c0e01c0c81d410340341c100892070103d00400c10004a0300380c1d00384c15010b0041e0b100340707130b001030324006d000340c2e018003941d500c00c0040c9881e0100c80c03103658029488000078180030b50284c2c0280030a00404040a00300c1d03642c48119900390784030000114000758920750039604620303105800d1484003031664014400d00b6403000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 200198606 1250 200197356 200197369
    0x603070308090f01020c03072d0302031c0302090a03080c1506060403120207030c151101020c100507110609010e01151a1608130918050a0803040c0b0f190806 69
    0x30030482c083c1c9562004550107034020400040104000340c12030b075841c0e560310b00d601c40072004081c080d000310501072400c000b5035a00e000c14105032034008010303010900454030012481d601d01417030b21081c59000d0100c10103d6032150344e03200055001d49000c039a43c8003032007005803d000d80030803041000d0a005042c80b0043e1241c0c415503050b03a6000340c0d044510224680180e01c0c20b0190f620041c4951a1000c021850301070110805504010a8840d4048881e80d462500c1c20b07409135481042003584590081824180701e9003049402040c2c0781059450305c07004082c5c8504003401100c1c1e01040e69103400b0242a2410b003446084c10324490705851891050502115101036032000150900821001c190b26070544848032094078010b0344446003940d241c000c031030244d1009040340718800c20b0b02d26008041c0e5440040030707444459a640074018200e07002003607482162a0300f000d0401d40729644d583c00081140e0b485c1c01c00030515003c19241040d01d50401308409801c5101120900e0100f144e85814000c841e103518 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 200199856 1250 200198606 200198617
    0xa0f1215090e01021209030903060f0103030f0f110f06010e1509070309031e020a030e010302180915040c052d030c030a09061104030501110c0303040201180305030403060e060603070308 81
    0x1c6011507403842590385140079001e03100300c41c2c0f290600c1c1c0e001c0c0300210b68000003c01014805a05a54243d0703aa405100d0385003034248405030201e04620921301c9610310541034050742c048517092100091141032811460720203800c3c0009080e911410051003107440d094481e0b5030141e6040302d070100a0030901c0c04520140005080c0c4018940c40c5e0303504600f014020794461f414001c882e84840010341440c0d10007545c54568003801d602140803582c80100300c2d4880d00860300071300740e42015007a841c02c0440c140302c595403009000b040c0c07000581d12a01c03010340c1d0f94016000740c2c0da019900c40352a603090704c1c03080030441c80a0071080c0c04103248040c8003140e41107103015030741d205081420a030340300d6407100605806082c1c0404010240c42c030380001649131141e90005402640c0c0900000c00043c0c500e050405154803a00000002590080c000a0015131142220b803100418514580d007030180d0369a030311480c580243e0011030b000c2da200c1120000d0140d0810215500090441c004c04040c1c1c074548410240b803044 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 200201106 1250 200199856 200199869
    0x80f0715050c0f071505152103031501020304080d03050106260609060607020306042103020702030a0b040c03060f0c0e04200d0b0a030f020f030d0e04020d060503030a0f1215 76
    0x413500400740403018041e002d4000582c94180711604e02645242d8490b08000b40d198800c0220091102407419455411011800820000c41c07464407901c03124140404514000f0341144420400840c00c41014031200240c42541d1320041550b50600300042e0003081048140c003a041003420302031143c981c07040100717508010b00ba00d2103616030b02c428010501d01e10404901a40502c02d10040c40f0800140304103a440003043c83c5070ba01e16002035240100d0680c4100f48001c0e6040d442600c2c25400b103000b010a00350000e1003429441c545c1c1c0c3c0d5a40e950070030346000410f00c5942550394600701c01001d4000c1c0c010b15019904803400c100c4041314908024641c1d000d096911001c140208450580e02091b42c80030b585240004c1c08016680c1d600e1034158841d0280913822401120315403c0901541800610800586207903140e10180c5441c0c0301c10b000080d00070a80e0018455241e502c00a541d850600040c400300c47c03281d03a4a07032005030751840540901084286140340380e00d00452000100419200401a10072 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 200202356 1250 200201106 200201137
    0x10e1b07031407061503030912050a140307150b030c12030a0305040606092d0204050a0b0306031618060e01060c0215040f23030105191503080f0715050c 67
    0x11000008081402203000080074285840c2004e20a45c150402c000112442542c580c541591607140310190b0421550009000750b00c6204910300286d0b29003aa0566220140101d9041122740c0d15a40341d05149090003074505a6110b6011805040a001811311000e054419030b18012042134981c0d42d901c80d107200310003011b0b43e8001042c2000000e400c070300001c1c04001e106100d086c5020b100804030440a0f02c15940642c7c26511580c1025542c0c000c0d1811142d00070543c0150610740705400444c3d0f40000d000a5250144991040b44140002160b0f0068a80b0007500d00d03c210760410060101c502c5904186000c40a00700100800b0354410224404141d0641c0c0540610385c0500c0b040d082030080703400c612015500d2041c00315072001d482d40c0c4e2420300740018031071000003110b1006050072941c050722414440d00201d40480c0c9031078542c3c0c00900410b405585900f0b0203991340d407105000e82c0c0194116000e00300d000210003040c0540b002d08400b4100000c80e0820117402c1000d40d43d000e40c424100c0100c2d04c4c0b103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 200203606 1250 200202356 200202377
    0x1030308070c1205040906050301180312140114012d0c03021609230c07030c11040903030c030c0206010b091203040e090a02120a0c0b09030c1206010e1b0703 69
    0x344500d11080b59250300008000c111109500c1c0070305540c00030b00a244c1c0061415100142c0d03031a05005404800d521165400618000c5d80c40440318445406a044203154580050704405030000c80140d00070303c031001007004400309040006003502c0c0001d4016466800d86103509040400f00b2030344c3c40c802c00d1035007000c01c101c848515003641020f2a50b180541940f1240f0ba00041d2010b198105020f030409198a4011503000c210041107400c5090315000c44d08502400f0a20000b809650783c0c0c0d02c080d0152000c60051401200001c041e148114070450000f510380c1591244950140100e140c480700d14005031590b0340c140004d14110340a003174407862003140c4185101410396800d00484019100343c08189070945044081183d9a80d4500000c0b80150801c5004420141004c02c5210704240d11400d46a401498048040c01d02d40104032000d606024044510030141d848094800d030995516000d404a580f6000031010105401040518242c4240011000d03481c40e9104540e591075140c20a0301040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 200204856 1250 200203606 200203621
    0xf06010f142d03060f040b0c120c0901030b091302040f0903080c1b071212051810020705040c120501082103071e02031b01110d05131b09060b1201030308 67
    0x60303a0b846009501401082c003801031034980121518495801241c010b1004d0b01c40e000d00442600c10000880c1c41d00c48070307034042088690240300400b881c0030145408600b840120001031103140c0e0940f10100c400d801c0d1200d4804505041c001c1d140f516081d510204203195040c1c8014003044030041040350a08170005401c5070140f4480c4210940001071070441c0e402a45901c54000d170325810b40800e40700c064028a81410542c400d500300c0d000b241c40c0fa40e9504000d4010300a00841c208644c80780d8095008200003c1100d403241c1c400c20026a07041d80c0c50031580c0d0414080e940c21500180c004c2e10940d00180d10750715064a40002e05000055402000c41d501d507500b180860301b83d640e100d0142c511034a9111120f5600394000098107030000400e40c804210070400c454542210300e111689807004d81c060058450116296101a0b03110311800c0c01c10542c4013260703844803407050801c64001c9014182e40350030302c0300c6002d51041e900500040440d032881d040343c120b203201e4100030500c80103080000c141e0004801 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 200206106 1250 200204856 200204929
    0xd0c030b01030c0801110a0c141f06030c1a0a12020c06010b07061815020a0e060703050a08010801200c0a0203010c050306030c01050708190c050f06010f14 68
    0x21034000305030510a50b100e01d80361056204511916600c0e60802a6500f008500390044405028198894442800c400e45d2204120601034130900814000c0da40607010070544084003203800c04150100140e40c50071071401d6070031031036035810000662641c1422080f002c490b00c0100d0303d4449040c10454810800440550080e1041c500c10703054134052200005840b0003050060401c0034404d00041c014140d02c846680a01040c03404081d003112003001001140c8a92603000701341004d1549010308690340c29401040d00c1d60300c803401c2100060070002d0041d20103a40710a16501501c05c0100a010940300b99405101c007001204401901e03982c001030540b60b0101c2003003124001c6034060001d0244442851001d00780b508115003507800b80c000c0382e408c030240358861410bc9000c10344c41074141d0f082c00d2548801c400f0850050f2400406e100d8250805004214100070301c1d40040b51703080c0100b401e50304101d0304864410710341d40800442888099200466a40c0d507800707080c00f04030150102603c44148101310170 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 200207356 1250 200206106 200206109
    0x4080325050d08010501080a02070203060a0f090b150109150f0f050904090b10050a06080f0703150f140d0f0201030b2205010e06030f0703030f05070b091e0c0f0d0c 72
    0xc2889882d070841d204641000d0072a040f9102621241c0c0c0d250765010000c1e09a2140c1034009500d500040700085601920b50302043c14090f107900300059002c4140e80c1c240d412042a0f820060040840c0b0101449690000b440000361850344a9005120501c0740c01500281c40b40c8080c605000d4038220400066104400340c1d0031002006005010f031419038282000b1002080c0c928585a0102540104a43c00e10041d02812030b2455030310144940e0f00c01d407185c024490058030703030000c041d1180c0210340869124a6000c024080d1b0b10340086265262043c0e4244030441ca845141c0100c080c3c0881c01e000c134260b0905131200741d4080c01c0c0814854034400c00a00e01002c003084000140c52078000c100e1100174940e000506907020038114003920740301c11041642d1074900c1d500090311940541c1c0b040c40000d110f41c0d05480c0c100c0c01400c2c4581810400e566002d011001140c2091441e4003925000402c40c894860034904040741c0d80290000c5080c07100030403031340c4400070b22880c0144450050130040014141c903140 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 200208606 1250 200207356 200207363
    0x2070e13060219020f010c021e16031202010509010903050d020a02070906081e0c0f22140403020c090c04090b1f021f06080312060d050a0501060609090204080325 71
    0x1540e4010910f1403070f01440e50740c039a100041c46a07481507141010144100c081f407185940041c072208190340d100010b070f00b00c1c140ca001c0050095644400c0143c20042c3c200014602c5440f035459400c0c4080e900a0031a0f1008100f01c0b001d07070414260001083c0c20504540400307411950242c2da404140310141e00e0000e4540c0008151481c2020008104402007000740e23994203c40228440c42c0ea44060b0a551003201c582b1190f4092003801c605103c40c50213115040e00b580440c0002209100d0441224003242e900300d000e030010400c202c0c10032003010390500c04403852200440f503003881818202001c1d0141d000701d005480d10b4990b1444a80304541d180c101145050f0385101c405c5207036a40e0054000e4668400c00c1030190410b18a11032a60216098002e00083d80c0c140d400035410844528102c405070b0f01d020340516088071105c05141c001c1501801a548040c0c05500003082c29840c02d40010201d000d540d1080040d24410b000038400722001100300d5651130245203d080c034006c0c608001e0101643e0500c03009 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 200209856 1250 200208606 200208611
    0x903060c0c170901021b0a050607020a0b07030914011112090307170f0705011d010503040614040b040b0711031e090307090b1306080616110109080c010c0203070302070e1306 76
    0x660040c488070040c09400d030f007a0300f0740303514494182c0e5030011412036014031584152240001d21150401c0c102a010160004040b281544d541e9041141603030b02820b410744c00998808030a2102800e1240f0340d818040c1c0070710700340c90f04008201045840780d12420012015040010703000400795020030907140507110125001c1480c00d03a48007040d54035007644407450318a00503074100003980c1d800ba403003140140d0403002581a001c071160700115196803006008868044d520708154003c48050780754940315503c40d01c1d4001190a12307040103504190300411038000c0080064903032004081c044190383c0301d640550a045503842c0b4045e1405024003d108999406100e075035800510001907030003411030b0441c1a9081c640149103018041e0560700d103401200c001d030b071104000c2102107800b03d24100c950401c030f15044010341c0e81d0400d524203440e445241658030540102d540d0341030180a104070031240b200b500003545020728542c0e000c1c0d04d4a80c580f25448651409100049115100c2100c0003a01030f40090308 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 200211106 1250 200209856 200209883
    0x3070b0c0109020316120615170c0405010806130b041106030c03010e160504181506030b0f06070203060c030a0b04050a0501031a1005100306090c0804021503070903060c0c 75
    0x40074000d1400d900140e02c28420a400040140e0800c0441d200703071401840e9484e449440d54640c5405040340c580c4030010400d0000780095146441040d060f00c08450300090490030b0811301c1004188c940603001801ca0740c00a4050100104c11030001c00c0c40c09034804410602a070315402c1c05d40300c8a4210b0469608502c0002c108218002130200039410f8031007200e44c407441900d6040d451076030320a00801040104004100912110001c01340795540c4103c260000b00d40c1081da14400c18009516030321034404292585c480782a189400c91010081c0d40341030f214107040c011103400190351500c01400180211400001058101c01e03950400c20001070040c1050000c0c0c100640445c0041c44240300994440c03181415001c0a0045140748a0250350280907a00569042800f000b0503400a00d0710b280c14141d503450b0025502050380948000b118994030352011919203801070021098208035560f40564003001045001c41d04021107400f620b03004000090812480b01c002d0320514403409018140e211034814 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 200212356 1250 200211106 200211127
    0x71707050d150f06271e140609040203041e0b090c04150512100203010f030b0601080f0619050306040804061b030503071d180106030b0f011e0201110f03040203010b0105040302030a0303090203070b 86
    0x1c0d0034900f00850200740001941c40c5074506001200c0d47c1c06d260b01c820200145061032400f50051034005005440020325010f0040002e02030b442ca0000444440b618001041002d035018000382d8036240090320180545040507284041c01025400b9552050045805821001e4403c0107180c00e07039503020604664a50715013030601040c074100d03c4111441c0300c2400004a103948a03145490140e0540d9045291544030325040225000400907020200302c2c149100250558042140174080e501809011340c0c1c039420302ca801448100015002200500c03207280c00c8000a5014017240d84c03080b060b14090f40ca904c0ea41c03020b14041c40303804004035404171b1640005002620480d4165040f01d219803010090011072500f80300c14017804030101e80c042500f40b410758858003018041003001c80c00c43e10001442e4498410780401769000381c00c907404a00404810002107003024811141441400d00b445070909155070f00107640c0c0d05554400030700705030f160940340701152400c210310800b40c005941500d884803d0b505 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 200213606 1250 200212356 200212379
    0x30b16050f0a1805010c0b0a0b0f04090c140f03150c0405060a0f021b0a091e0204030b0106121406100311030c340803071707050d150f0627 61
    0x4407040201d1128010004156002d481b107031400a601c0f035070040c4a0380d80d502000b801444a440229000727050455080890b07030301d80c8100004a44180f103261943c034140808880d6020410110718043d481010300303c01103030b07000529401c40322140803a4030850350b0b03281180486c0e40160b500654000d01c0100f0f110352842e030021415082d10403e5800c032142c00b84190410f01008981c5c408403071700007103900c03000d204020b0310f90006888084041400c80700d00410501c504120f074050750040da03851840c40e00610515134840401030034287c40c06800c3c0416042841d0300030050401800003403107000d421420500080c0a03030003481b0041c03800340c40c160312458050280503081c0d00651140340341c9460509040140c6c540c2e8158000046c410315102541400140d444840a62000e00b481051003000c500701185074441c030440c50321078400d80d036526441d8142444058196a034820401c0c90501181c4010311066494595800131915946801c81042d00c22600800c0e8038101d50709620500c1c4150003001c6105601305 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 200214856 1250 200213606 200213627
    0x19020127030e0301270611070f0b010b09060a1b0b01030b1504150e18060705070605070e0102120904021b1b03071503050612010f14010f030b16050f0a 66
    0xe0b15028031480152041608990702c1d0420161459030400380c004085010400320314000b44956400560802c03290f0358442a80c2101c40304440d00c2c1210b061050801c07605007441401032641034840e50400e00c1000003d00640950b0440a080281c0080f5030f0b001840d04c001d0000701250403103c20822540c5a00300f098125508481d450b0b11000b00b0600891350781000c1c0700f42403004001c0300344d202170a400c08100504010015205c210560b200e16a000114502840b026005460640340c0650314681441c1c840280c0300f000345450301f488074200c10b0344020b903004207600010312507015150390b5070501000068000c0c083c00708444400700c0b0400b50088160f80008042040c0c0403104103001b0100c0d001410140e0301e00050040f80c1045480d1040403180a001c2e4010f00d030003c00061824031a1220410030500311a204030a02220a0300c401d030080c0e940b00c20300340a40c050800e001d07001e2003140c11074803144000c203000740c1501002c01143c2040c800051055055918018510509690702c0054080c014641c0110 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 200216106 1250 200214856 200214863
    0x40c020606010216030201270305030a020607021005040b15042c070905040c06120b0402070308040b37090f0c03030f031802010c050708010203010611070503010e0319020127 76
    0x4c000780c0340c0040550000e82d000700d941c165188101d814001070000002c0c03074000f80513034040b8250400400096000d001500112001d580104043d15214070024030f068801c04107010082d103071105100c04509580070035a0310062001c5514021314a10001c01e0003000400c05905032801802d1010458911041c01285c0d0740700d50a00315100d09803141c1c0039008aa800380c40c02801d5001e05041005658000c81304000a821942d00c00034042d0700d070801103016640404411000298240c082008000c03043d00c80e103401c01e0080d11184c10a031000654044103400500c0300c05104456055842032400c0c1581192040e59801300d40001050658a0451301a030307440d02007100854060901500360a220b0301c140c1480f60110b800da4200d0b018203800550380845500d009440743d009410380420031000c240001d42c02000c10f66201d401d040d48240c3c07080d091a40c141c024921a9051040d5001e03040d40000942380d0450090311070410b03109508205a0041580c0300380340ca440d00c1c0990080b40e00454480020140c1e41c007 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 200217356 1250 200216106 200216113
    0x60c0c0a05031603140c0d0303020901020d140a0309111c0212010203090d050702041407020d020c010201020903060a0506060d0f0c0915020703080c2128081501090302040c0206060102 80
    0x40720401c250f2030304028140ca41c60b4408600b0200045a055881c44149020365410382d10b50b000d044000c69285400c849081d40480c2d00011481202e59040150f50210070b02c1d071400340101000c082034884207114a120050800d601d8400710710520032402c07816007100e10000c0c0409000348800e0708503400030703070301060070303481189140c05801038104103000701d9200b580c144000d010000900c401c143c501da00054026600195110001381d80001405550380c050461038000340300c0708540880013881c001c00326556604590041c4018540358500160464010000d60008942c0e40d8441d00480d8040c080d07500302c0c2101604206078280302301450f52014035200740304e950f40200035071a004003080d0404070760100801a032240300100041905e4002615205009405441e0441c000c0c0042e0340528034030340a05241c0220014685c1e4084040d140a14140c591303107896080b00100c4960040d0484d034009084145400000307a0500d100e82c421200350000d0340d0f009000b001a8026408000e54135801110854007512 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 200218606 1250 200217356 200217359
    0x115090c0513090c03180501050f0703090812070c0f08180a0605180621090d020105060a15091a0c070f08030d0f0e0706051305091e070c02060c0c0a 65
    0x28401e00803200c0d18044000c040b149245445035100091541c140d92004040d5a41265034911091402410b011402240007042906050385441c80400002d03141400741131800d00030400003425030301a510101c1001c04209070607a500103090701d4155840d48000c00c000d07005400041002000750141070780030b440c035041d001040d034a00c0c01d02c07400002c540103080104000b4445440052111601c0c58010440504800c3c10201050261810f404103c1340340b00741c4488680030421100e000b00884000e00f19a0301c000d2103a8100354000c01c80160080c09030000300b6007a0005421030702d0080c14007a00901160750308500b2024103696041c0d0715040300000480038000c844000a01841030f045001c02d4410030009980b44c8001c2e0710410000b0065103103d0790946480701c50140b61000c090009000404031178a6941da201d1000340b40030702c240d0180d0459032103401400103000c001c5036941d003245a0b4904a00d0305902c40c4c0c42d52241540c03401f41249000b9840754001402034400507002c09c0707052041e041a14800701e020b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 200219856 1250 200218606 200218631
    0x90f07060c0305040b07060b1005040504150e0f0405011e0203060f03070807091a090406020a200709020711120c010905010305131730070512010614040503011509 71
    0x1072400c580050000740041c0014071201c0b050f800200740305441100d000856058480104850696410603074010410125040000e820240119240c140c06030680c050914200254040d0660707020704429448a40c120025040140c03d503c002100d03400344a004403200240c60100000c1c1d03204071034140c045c1c00e25110488585c100042d000c01030310f41150150080034281111000100020021110020354000202c49162a05c900c058002c600410380541e07200a000c2c80603242d180005503d541c0140140415512494007095200540c1c203040005079a402c034609119406844d84250282c0c0000c0800c100800b01c640014000d001c082c01381c03241c1d001e00f9501e200550841c1c204071f521030f01d506440000c5d900000c4081c0342c1c140707004241c032260505001040143c1040540c842d0a581081071500c0e0b039080242e0783d40c5801da5404001481c05905d80310584440700b03200b40040c440c4c40103108419804010650300601500c0103404083d0081222486204540304900351340e10446002f2440c1c00d40c20480e4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 200221106 1250 200219856 200219867
    0x10203190305060607020a0b070303050912030105040b01120e060f09010e030d090305070c060302040302040510050609090604110721052b0906050a020304020111190308090c0405090f0706 82
    0x66114442042031100030103100340c0c05440000d0816600100821032103005956030607400300600186c2c0d040c141c840d625481c0c0035084407009404443d25078451081d940303602080e042140e05460007510040703180c40341500181c9a252800010181c0326003070103454044070000090013445000b124442c1041500d4071400207089a086050b16039031500104150703040f0f804140c000d20f029a2081c07a00524213021a01e800d03482035099005040020b80001e810000d40c03420340102500040203601c201c3e501450000002c102c0c3c855141060f010341c19050000e5050f43d165802500f07e00180320000341e5613481c9144c40a84250f09680803034070845201880668640306000b6030302419000301002039000f03020b46010601144c1c03024050152a1205214070005900d0700995024421421001d070700c17402d05100160060780100711b601402c0e489024621010b005034550780803001d4141c03c0101d600d84800d2000c508004100821580182c10803040c0800500001400c0308a0600c007420350b620161100400c445 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 200222356 1250 200221106 200221117
    0x41101050406020a08130806010e01030c05030303010f12150c0e0112050603060106050c07050d03050c0c0f090109090201020a080a0207030b160c170706090818040b10030e03130f050a05010203 84
    0x160f1001e6030110001c1c5c07803140113080314000c0322104d052081da15a0345900e0041c01360030540101c16220b00420800035000e054802402c4118050b50139036041180d10522040e4a100e1458187c0d04010b500060000c3c14dc4034803800692294144480c1c9051140030301a40300791141c0f03900194034050341c8101960700c4d105550040c4002405040301c4d9180c1310048610ba0009454280785020314000000d103640d8030341c07050600d184680c50f41500c40d0008404281422144181280249000c400c4000c01381d54403010203054424104000076100d101d400100d203448020341d8010001c52002410a1501c2e8000820703e084920400e000080780d6250104c24103030094100204002c2901500c10200041801c0c01c2000003d4462100b5420159503485140c241c80c0c040c0d4007650703445000103059440030054071040040c040b09503400e00c03505203240c002c14101d008054050003091380c5c0360425100c001c0240111406410403004480845813900c3d1825140032040c450740b4483c0c1064040001c10754000f005858 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 200223606 1250 200222356 200222369
    0x61404060f050108040503130303121406010e0415030203100b0a0611030315120d08190e030702090c270a06080c0a08090f1b04050108010b0d03030b01050706050f0411010504 76
    0x21041481c0000651300340720050b108481d140000d02141c1d010701160300c0c02034000c50107507580b030386c0b0388446a16980484561399281c5820310380c064100120741e40c002c0680402c00d6800e880c001019000c0410703032004002c258000a43c90700400901c010914881e401031906614105c80800703078182e445106440d1051140d43c469000e410500024030080d8015580e0310010b00f02030a0150608401480c0a04100440c403c40e004512441c5c1070100d600c82d03c169610303102024040400c0648203000e4096aa07000d040c0b0003d1291000b0800583c1c0c040060f000d8802102c25025001c030b045103400040075401d0312003e190750190403112800104903103d00d5840f80940e080340c442c18500b4020b002d00b04c44042000307180b080d40b885124501d1403103d804204112040c25080707281a203191042c0100403c1d15811b03881415540c0c1010019405a03070388141d400c001b1a03050400003028814032006a6840c0034051010300154030b00410400c920130307110101480f82d845455080003040000006680b540120300589 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 200224856 1250 200223606 200223629
    0x408010b0402042106021c09060605010807020a0206030a0b03010e0304091404020d0206030403030603021f09080a0302060f1305010c0c020102210f09060d050901090b1003150b12060a06140406 84
    0x104e590341e4003e52a210b5950050002501c0c02e900911244801241c0e0840044225030700c1c8042d00c14040315100f8207000e0b01c070034600581d107800d000000942d00e840005020341300c0ca4000001c80e07411051640401d00305030025000f8440d800700448056100d8009109150209050100000d4952151690903108590052901c43c081055800b4800f054100400803000d1664400e800700140e540c5d10440c8480d03075060700700103504002c119002845081c0c0d69200411030742c0890b0712800020340100b489036100110803031108169642c40c86a011004065801070000d5203400d50410710716900401c0d5014880c000e801f107407031a0380541000005000200b814009a240c00d0080501404070070300201031081004210354200503240d04201c08030350041c0c540c07a2a9a41d983c51210030404e49a0800703a10000200403000510301c0e54a645034115590100403c3c220b03070703920710141d03545d44c4d410120034003e0b0a00304032441868a219020010506401491402c400706400303045c072868903000d960265500032000307 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 200226106 1250 200224856 200224889
    0x2070b0a050a0302090d060209131a061e03090106141c0b06030102071a0702010b0d05070909020607060903120608030a020a080a030204031209030b07050327070b040b0408010b040204 80
    0x2201c06400800b480700401d9020007204a15036503614034802a54012840113a982890034100030010780028810490942850b64020b22140900c41c3d01b108414191021503445c000580442003d030414802d00c5d1402402206001d1280415800b29040d5580880c01603124291401000a8024960181c00c000d0703c01034804000a458201010780100001e0000346c2024119036443e44200d00d02d00d06079094045000c200700714160309006990002e0300c1031324403520204807030b1038003a00d514142c05800340958545068900315254681180c2c038554016504000200091900070070145581114180702ca06041001c5034004001c8100c44000070650018141004c080e6200b15060f00100a440b05040d400c0c00000081402c917903280a400c8140d6450100740c03411881d00380d0300c01c000500503000300f007024410003403013122100da48075142550f0290905114031240d1500d180c00072580151a15a00100d00000c000c201a8003500a440d42503000f13201000b104402d0004900641c424100d101048950 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 200227356 1250 200226106 200226127
    0xf080a0e0a050a0e06010f05190203070c06090f0909020d241b0f03050a06030615080607090e010b07020d02030102041d0c0f04150903050303010f05011e02060c0c010b10020d080702070b 81
    0x65441c3c420f4a01e0070101c1c20601c142707801c038111002403055a0007607040092080200b2124141c450f0242070242801800c0c1410728565660315080360181d0720646a88111003425540c0d007a80b021207941d881051281e82c1c20b908020036151140514114081600300202c1100c0190307040c184880ba010135649007071070074041c554118090300c005440c840005680d00d40100110b0041d000d40311502d10940002d543c482d140c0b40269241c204000d03d007404101003038106004400302e101000e81140c4841d452709454051380d00000301c840402d0080254590701c0010005140e01d012100300c107410100c5025907400e5580c0700ca20324954480e10b8810100302d5410082031203956148011101310750110b103007010410744c0702e941f0710346550300030703044089030903402541004030f036a201c00e640380308442250519680c5468207170065a100d0019212010200022450100880c1c1c01d5018243d40315001702001d10415400314040d4684180a0055000441c4c510010302414000507104048500c000e02440c80c0000b10031 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 200228606 1250 200227356 200227367
    0x915050f070507020f180415060b09010e18090115080307050601060c0f05100b0a15090501030c030b06070602030103230a03081e10080c0109030302070509040f080a0e0a050a0e0601 79
    0x801280c0c0305031710807000420b9440700c140704000221a0419215542002c0c00d05060b882d1010150652042c141a400e000300d0912406a510114003800c0044041000800080410300321148000c2d01032410000c00215041c15040007000c03410403050700380c1694903402c00750f07100d200707840010300180e104a00400c80340d8402c0000341c1c2d040e03009200c3e01d603100560380d944a007002c2a00c8031038118540c6405075098589807005566008100714500100d244d40e20000c0a084040d0a00c152814075664820f4a540c6501079041a5000140108419501d246030b28080000703400130f020a0300c81220900854040c03420322010054540d804030002d105a01c1a40d408440c140e45c0105201c10703440b600e96441e5503401e60001c450380039040303040b4401c20301400d02c80c00320b25242c46032a00030304002c0380e0300c4100080394000c01c0040c00d4483c00e5408480542e035500b000b15a640522600512540c40019080c9503658070009100f502a82100c15035562681c0e0005c100b9105054060104010b00d014045240c960059 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 200229856 1250 200228606 200228617
    0x8071d04030212130609050f0d0b0903130b041a0702061c0b060a020d0f021f05130812010314060f07031d060c070507090615140f0301090915050f0705 66
    0x2031044500c03d4203250414802900548a00d410b4150749940610042d03401c000400c0c003a003010f5501c003400d0800000054440c0300003960192018a1100c04031301310900500c100c0348440c9103068540d0215507a1100390680da4000c0c414000c000340301010261840e1000021240b1554000704900e080c541030303035800111f172820710b400040138541d982a500c520391100b0014082481a64000e09007503c03405101078180304030404c1c18002c54010161403010004a003148200325501000e001409584014185004441c4103002800544010521000220f0b9a00806041c1c0f40b18200c0e101141540391300140c2d441005940344d24a6a07040f030001000355100e0b41c01410a11100c1d114040d002980d040483d08000c410b40745120300b003200248450600001b00580d5000344010304040189a241a144085081038440e0715820012601010806132502d0020341d000d83c03031a80c9446543e541e5a103802c000034441642c084810150603820540da2030306902c00c45205490034014090980c1d0341c08806c40b4035030b004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 200231106 1250 200229856 200229863
    0x3090f13060504050c040305011a01120e070306050a1b090e010311010c0c09051e06030d05130b04060206010501030e0102180118030c0b0a08060d0c0e04030306050d0606090608071d04 80
    0x103807080016696924043c46001d000c0b60340381c281c4d0782e50450910303909441c0c2e845600c80d0107001da650074040503640300790b000212a088100005111581f442d9150810100c1e6101a14441c109411701101c0e004681c07092050750403d0071003850354000c4650503070304c00c1007a00c0b80c445075551040040010580710109595034040500d44404c024580360b54481e0b0802d440d8100101841c1c0e50802c00c210003401e0300241c550f154084070191030920746140004d036508888002101000b10100740c02c105101c001e17003000d020345a6010099295521000000d656903000d100d094002800d00105040f0008103208480d4080c001400105949840c05c00569440003507543c548000040b5003030000104045640718009084005034180c2d030761a038040c00901650307010702414400c0008108840000f007550425404a99401441031034075a00c0b400c2c180c000741040e40c08150031903280c52000c81081442da112000b500c400d80c00c1080103646031070b800c41c1d030350ba1a4080c003070001c00759940030f11007400c0020890741d20a11 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 200232356 1250 200231106 200231111
    0x4150c050714300d0c0c0203030c010501091a060f0901020f06070305040308101809030e060c03091e01080103060e0307020a0602100e01022502030f07030b01030c0b03040b061c050613030e0303090f13 87
    0x4080d1f000c44d107194840c0c0c031561250b9541e5801231000346c0f110301681d814219015a40c40c2ca101c0d03003200040705071003100040c0402a00000380000d5a900900c280342251038108180e07142845c02c0e10000c1d0240004680440000b03c800c00096280c004c8044010b00b40c4014210440801c90b41e030421000a0090365029401e1200c1800d05c911160b44184c014180d211038200a561a00007020512108600101586100c1080440d040e080340c1d80c41311200781101e40114011404a100e0001700e4254131172201c001e900b050600b01d01140351354001521220001c8114000c0120400c00d080060803030080110014400c1190003801c0c06a00085086400c0540020283d40a400098050612700091039008549501c03032003004005100080b0045c400421104006a2451038a0364031303a070400f14014a01e92180902203809074280b10011050b00c551644101100e03803500785060205c1140c6520002200003d51100d810415410048241c4806501c0600240d070401c940781c0400c40c0c104401c000c2d00011a5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 200233606 1250 200232356 200232377
    0x30b060d080406020d0201110f1207030f02070b1e0126010e0106090c120c0507080c16062c030705040e030c031306080601030504150c050714300d0c 65
    0x752180020001000e160300245010100d01c50080c2c25264022044696a0303001c0c0890005080e18008441c000011079030840140e1707840c600b0aa005109e013910364000d0300d2003c07a40d0002c010b01044e805010340c0c8030964103010300c401d03140e00d480c07441d00c240241b803e07200356618020000700604800c6036a5190344800800e820300c814141c24210782560740056038042d110501520f8068000700080715004285500b4440c0c4050b00202502c0751041000c002c007500e4002602030348603101801007a620150004202000643d2010000e0a1030040040004c00c0201810107404891088144082856004c0d000e0204140b030901040000d0080038800001e90004208115a01d8003d00c010641c034400e120502d10702d60f00b064001860080d0060545051610b08014040421705103d07460324100f4903c580403800c040950f0046806020300440200008031108141005540c00701e01d02038804070222403290411680814039401050700d0386400c00d050020408841703402d400b5007000041e500386003003414912 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 200234856 1250 200233606 200233613
    0x11704111203120a0603030806060403080405060d0f05271f0b040204080618100605063c030f16050d020a030603080c1c020706050909060a0302040504050f070501050a0504030b060d 79
    0x3d81c11140c1220003a52980e0500c00c154000b40030342d40101040e0389072400e01d400d6540300b801c54410303170003894840c079008504d040400000340c00944400d4081442840710741418000364a1800301c0e4894851441d078100051070800c00000707542c0703c40c82040300e20a420b252407010048000e06090704600d400640801010600c0801005454011554013002c10005264044d0090170103038100d08441d10b143c28030000f0029551190103403043c01550301030b03403070f4560394618419912003425010b000350000707140900c1c030700595850701a51040301c480500700083e03611551840100c00ca00c40071700010440030702903171008a4259014042c0c0c2c200f41d00780081d403140c4035185c2c01d4803a0840c40e90035500e9841800007481b81d807040030481105201d240000e00d5402d060a1014186019210030710380104600000681190b031411f100000846d00540701b040181440d00b8401c3e140d01864140c0200d1f4810858001030951060381101d004042c1036070341c50309003410f5955403e9400405082c8550003c8542d0348540031 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 200236106 1250 200234856 200234887
    0x20f03071701050a140408090a180603030e060a05031f0503010204030f060b0d0203100e010b06070c0303080c070b0c071a0f1b040f030b06060c12030402011704111203 73
    0x19000854050040740c04500190b403e44600074195050b81d800c0940c450b40c09414504804e0300290f011004584070441200411000c0d0410741c0b0080c00c0650101503501881c2c2c840e4080d0781940c2c020b40e51451008411401e20281c1d1240d5044800011001c2000840300e82012624504940c1e40e1640f00400c1c555401c002404d80e000390f001511029040c8170030508000711442058060002500c0520008001c1e0b00084d854224540b603448410307440b038009280c2d8540a5004594441f0000d081a8440e00c40c2d0421410040c82070204802280c030500c0031802c0d448600056a09165200c801410f4a903500c00c02d500c03060708031000454042030407a545012030b010700102c0c54410800c80105e03514918140c0040d880c003a0031068000e128120802003400140b038420340080569400030240344240c1c03150004a20b440c4665200c0404901800c1c10005c00701d00484011401136001760798040b0f0501c44a2800c1e41c1811013550014203103801c24540031351a003007441842c1c5140c8501070a0b2401c1c0040d1074009440c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 200237356 1250 200236106 200236109
    0xf22050a0602030f0a0b030c040203070306051807090609290409020714280206090102070b030c36190906091506020a0b070309020303040b07080a0809210304020f0307 73
    0x800c1c0740c01004100940040d403502c0b550142411000303000d100d1745440440c0e100c1301140f45886c09190000005150300b03000e900b1100050a01a0500d02084840c40343ea650070302e810749040000a10001001a041d445040c6482c1078829902103003030a124100900340c00a1050b036145010b0300c3c81840002100078203480074203425801049001c000d01c8001c0d642c541015221f600ba50307070303071a03c0ca24001c3c0034a00d01445481456070555145584491500050785081410380c800512010f0010810915469600140040b030180d01c2c04c03001c40342c084038404100346110003080e6079048a07200c602c0089182040203082c4a8610401c01e01c030282d1503800e6507007540c6050700b01c03000310390b154140340d2901c008903000795005010900c0030307201c0c0304515900c1051014020f40900d041644031000f0b9019540c09004407001000600e8020707584070741d10f00c0c0040540e00989650b0700401d000d4000201e64020208030b5071030000c10318803c40c2200c103480300150441c0d080503005a80100182207814800d403010441c3c0c20 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 200238606 1250 200237356 200237363
    0x30d1b0f12050c010c020607020705090c04030b3412150b0c07170a0201081f08030723070e0703020c0f010f14010b040b09060309010e0106060905030706080f22050a 72
    0x907543c1d10f2031004282035846030403500301150701a01c100600544c1c080b40440a9030b00441d0301d8a078985410741005e905002d5a00050500d4004405000418240c60181003c03000480080100059507c000d5018080d035062107102051070003002c0602c41c94194080d24410543d000311200782c64440880079200e400a400c07150726030380400c02c28004042a0120b6042910805005043c460140d070700003054414040c20414403620720f071041844801404c0c200101a00c1d00e8401c0300e1f22400f071810f0052414480f005031a1140c0180000032000800115195055038900c003c01c0f201a121800118002e51040102e0070050144200340302d1901d41c01e0007214a400042003000c11101035074503c2072400b10040e1f00c04410344c8810442040001d0500701520902c0008403429920b07556800d002c14094075020061000710752030124040747c21b40d00000140705a5109a0403905455100c0c24240e50724030094600c0701c05d4007080c1c00011103261108040c1d003901216a1030a07040c1c60010399072503140164120080307 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 200239856 1250 200238606 200238617
    0x10c0806031203100b070f1e0b010501030b030d2f0d030b010503041703070e0d120e010302090a1208090a0e01060305070c0f0f1b03060603020f030d1b0f12 68
    0x30a80307190402c2100201540c1e42d14032865401c11900f80c3e040d14002d4800c142c5181c0c1c0c041481024055000c217010040e0b41c114100881d1f072140c0020860060003850021034800030003000100e2107510a106030001704202400910820001d10b85c1900c0d1102402c44110041040500c0c000780351002100d50806c49201c04010300d43d048501d81c0160640c0d00d10041c2904022003030007004081441c8034032428000b1060b9185680e2a243d02004494201a06110036044201e80b03821004214500705c41ca52035145950b9a00462a043c40044040c0d214101025501191b410800d0001c3c140002c1c6d000d0940b03108400c0d40d0b20304468100424880400d55011512116006004110a0707805002d4154000d900e4a440030359130a240d5075925075010f0b992030241407403d45c40b031001e0070800310519a40d50300c90300e03144603241542e5a14200700a0440b40c0400c034012601001c10140f01d06000a01a800340c040382c8965448455121742c0d003011351001042a902c215060266101040302100004109410b0303580c0c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 200241106 1250 200239856 200239861
    0x519120b19111b0109030f080403020c0a0303020f010b0306060a0b280206040c050f01050f0d0f02161704030b0f130602030f07081003150c0309050609031314010c12020f010c08 77
    0x1180c48a0f188010410513641014120000a81d010014640e14407032420640b03170b01e0311682030482c5010100300c5150b0b0404c40c0d4800110925400044020000b640708000344901659803050584410042d10034640112907100280310000c3c0c40e0000e040d000d1880005001102c0d2054000c04886139417203144c1c0b000d0380001041c002070041801994001d0841540c20200d88940713600024a12705c02c40d1100868100d000c510800403603540d82080c00740d0180385c0c0302036450f900341c400302242c400c91040701204d4115996150882007511030003038804503900711410080b10f07581c00b0710850148900401c06046007100340a0f090000d1410f20183d4010030030300d4843c880703902c1c00d094041c1280c403000d0100d009001402408200095040f108500941104103001c078080712407140540142146140041c96800f4100070402c030303404004050044006443c0104d40d0039036459101c0c000940124404600181c4850101d00100740d040d4429100b0240307a10440b200d520003d00714a00b19010303190054000f030384c0c4909 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 200242356 1250 200241106 200241127
    0x30e10050a0603020319211b050f0f06041203150909121409030703021207050607080a031107030c020603100e0f0106020618071203051c0203010519120b1911 69
    0x250761003940c400140840407665103070000101c0c06900440f2041c46961f02070840184960b0708004450080d038040a0391080901d0300984a80d980080c080003803050f011581404040020303580d02491300200941d40080a61404601900b0081d0f2000d02d480c5945200181101e1540300c1c1000c554020000680f0002020360b0045c00000c501c0e160303a241d1030090091000700d0341e0104128003103e030304a0700d98040c40c031001c0c581401d1211540c4040e034450008204039090052000081034006880e903400c12901124000544480c0543c01001d80000c40d1441180c0044c01e15400445e007000c0d09010540f02030340e40d0484500c0807101243c903100010800c10040040d01e0b010001c140e08003800303040c0c41c0c40c0e0314141c1072070b20fa45540d5440307549083c0f855101c03200185401007013207070303400ba10903144041000320200203030001e94820722645001d201d11038040003801d00450141800d50344561a801000d402c50348036080200c1015000340307840c01c0c07041d1841503c601188240a0380d1000c08940b41e4172801c0001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 200243606 1250 200242356 200242363
    0xb2d03060a0f051b2b0e01060906061707030e0703020607031706120a060207170a0c03020f1b040203150402031014060f161406010e0a0e1b01030e10050a06030203 71
    0x1090665003040e2100c4c500341000d408005c1d0b071000d0214021000040380d49810002c480e001200408550900e80100c5200005040d000102690200b2205010496480c4000c880003500107075101ca1200002012520543c440d400a8440102000494515175203a0700040e101e40d00c400c1040740031405001c118040003000402140e40582c0403100301034032180c0b5040d119200e4a0014000340220360000d000c108000e0070401c00029207030307035611840d101c2e440400b0242065110940990252180010001d0959000908070005080005a40b1000c1040310b00b800007940001d05076400e1901883d1918106854920145118540031100d400c091481c051001c143c4601c0c106146004040400520001141d80f4040314400c1070300b8a1f0700401500a810015607ca031540440c107040d011784400020f10a200080050041e242001c041010021a0100c0ca60360044c4070482c6001ca80b401d541c0140c01c0d030095002e0030842c4a15030039145490252020041210003c450203500c0b1550341800380203600b403c2 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 200244856 1250 200243606 200243611
    0x301030b060a061209080f070b010e0f070905010f120509010c030c03020c0307020906060c01050c2503020706050a020f070e0711030708180402040b070609110102010b2d03060a0f05 79
    0x540d03100ca1041e050840041c0314134582c0d5507107041c403a00c90640a003008812400c50b030305410707051a513a072a843e0b0b074580741e62030070028400d030341c200e4000c040070520317001c0c20f6103046002c0d4001c0e407250803059142c03038015502005000500c00a0220640300094012403a01072544100c4001000190100301c0317140c060704407500e41e10054101031060003081030414002084541c40e07034044402240c40c2e510440000c0341445900d100c1c4006500740800d0081806441d00a02203001c4900a81200c0514249102c03003004012540940140d1182008000690041c0c00400511005105562101d40c0c10749907030f40f0700a10703588080d0816240303074200000a030f840b5003c0700640c40500050751a00000391109006030040e92581000b060b4050b2001d00d0340e540343c2c1d044900510a401c0d040789c4a05060400704010010750205580074504070b22003444942c41031103240d030031180c020108040041000e85200304c48503072035000c0c020b032a40160b205400d56402c20000c1d01c103808284001c6a406001500c41c3c0549501 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 200246106 1250 200244856 200244859
    0x2030a0606090609050a090b030f0a030801090b090606030613110a0e031009080301170a060e030306040f0c05040b030a0f060321051303030315030c0902070c050a08150411090c0301030b06 82
    0x2095130a20103581c8000861084400369100851030b94a050700090a08800c0180c440051250008803020541c01084150403038105200400501e4070090a00402110460b2080e600040170000205149446400c2810311440310600180d0040c0286002d5490b42c812485800425203000050850713117410041c050001d07850440a000e1102d181c0d0b1180b146000602910b00c0050031241070042d10032040040e4100603810600c2441380380e090101c0c25440c2d03071080c2c0d4242d000d02e04295440c2030040640c02206800b01d0681e0329186098640505114640c1015007448051911075030000c01244003802800061030180300c00c1c8031690460003c5030174107a8001c800b282400b500b4005004680750007914201100d0705801c001c10000070152800840e609550801040198059404568400c00354050b020103440f41e403412100c95150b0301005101221880303140700c0e41d44401d20100381d050038408625003040c030413001580b00b5007002c400651030050071140306070118030101c01017050294244019420580 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 200247356 1250 200246106 200246117
    0x1a090a0b01271401060f0c05030a120507030b06090d030c0506070203040806090105040f0f050312090709060b1e16080301030b040209010e10090c0516141501140f01110102030a06060906 81
    0x180d400d03440043c800500c21902800300300444c081c1424081e0400d03070180365010041e00c0d0788000689014019001c041d0f4052505031502c4005920309001e8410511100c00060000c2c7c1003001040c2049a0000e2201c004c0b000c2110070781c00c1c080001c0080011a00564882c4c01454841c0d007400105c9260583c000d00c15a8168104402d00010900c803036800d0360706681003440c2580304030300f60038040c1c91482040388640c81c07514600c003044501080440c8075029550800d9061121547d00c01042d51540600a00c0c1c0041c1400400c0c03465680c4c1c01c01000702210400c407040d5000802d2503845062807600264011b640031681c00e0104021441e00031901805802d01c0c4800b1202c0d800c110b5000c40700110079018844c010b80d07a401c03441288902a1040d40c002c210403120451000142d0700c1d1903400f4441d20408038106d803194200903448a90b0202a1506880385850660118699041003001e601d111401d064184000e80329420240e100a000540c400c002000e004564039284c044004c0c5202c010b903100004106 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 200248606 1250 200247356 200247371
    0x6010810090f09050307050c0a1d0f04031b050601050405360705030d020a06050c042102060706020409021b06070203090d060b060705070609060203071a090a0b0127 72
    0x603440e80c0142a034510722000150480100300d504003c02450101030244e1101050385420044005405a007407a4140c502548256841c4011898140300303000c1085604003644c00100c0d9642a00c0c802e0360b00c5400f0389060208224400c882c8100e580040c401a55103401540060101c2d01b0130b0f02466030025036a441d00b00510b16285840100010760200c43d4048000c07007004421800307010025000070704002000c0e1040c60078103c00180d17440751074078001c036103141c20400060150349001b0191003c548619418860244141c3c07802d5001107a02038041368445424001c0c100072410f5407014001134501242c0041e915440150441d84915034541d0180007a40041b0030030040c1035010040e40c46440303090340c084290801070701d061030107014184041c94015a02103a000140040080c14404940090f00d44240942d260081240c0740d105000e4050300302103c00042986c1f01c0c0402c0609a030145541c801d480d228607441d50340c0070400308280e000260382c442112034050840b044009400754010a4601049201c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 200249856 1250 200248606 200248621
    0x509060409020714160302030c1e10030f06140102010e0105061c050f0d0f0f1803120e041b020c03010902090a02030c0d0903020d0801050d200102012004030b060108 72
    0x203104500501484980100e44042003000e0380030a41802d402a0060701c2c1c050310a142003903918091440b0a92086c441c0310710403801d5050110b000000d07551600d031070310746c2c42035003a00340401001100c3c220010951384400134008a1080d200f68000340c0700f8851445840c12140703000a00f510b006400000c1c2c0361f4504400d00c4420307650a058103c031201500000c61030710056050041c100344003c2100ca55174082c9075803510a559100440303105411598503610841760f01ca000803584200090315890340320102c00402d00218001c540c22060307202051912640700f043e060301040a68200010032880e1070102a080a1115014005d4503d0304000361f00030010f001c007540001e56644c1c3c0282810031219400004101c0344146942140c4001c040c108043c06a440e13030340390083d9184c540d01005070008440340004101450004100001c00760003c003110141c001840d9002c1d90184030240b554103641d42c0b0a2001c1d0418016201e2407a900142a101500c0b80c0c40c50407c00b101d000c0081c9003904019001c420441c46 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 200251106 1250 200249856 200249869
    0x6030318010e060408420402060d2d05011e1401052209050f01051806120a0609060b030f0a03080402060f121806060d030e030a020402070803090d0509 66
    0x15103400746050a0214200700200d6103d1003541c001221500456008001d5004440c10102040c0011346001070070361104c5070451000904070396005503851024012401620780b54014000c8a01c4075400000d90420146c0b6010403403a140c0088480b40c40d0149224181c002588542c80c0102040ca403c900341551340c0c444020040d03494007406d10340710036200b00345100d07034803c1d420740d402d580003158407a8a481401c8200c2000c2809803181d000d40d02e05100000c3d14a001015809040f00c4000c0e142c501ca42410310003584820708001c04082d00600030b01540c50b001c031401c0291030001c9000304000240c0b0100d60409100382c44080744070303900070780c020069403150305000551980b0f40c079094507211500341c640d4400184c0030f1291102c1100d190341c01198040b070444483c90030a015200c2c00c00d8401060307038031428040e1185d800b2035416078460249845000031900a87d40380003008002015142e201c0c8443d40040c04982001c0c41c1030743c0e0200080100102d1000821044010f4201c2d410910700308002007000611 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 200252356 1250 200251106 200251147
    0x30a020d0906051602160e100b0f041401090b0901030b030a02100314010e01030b0403121107140607080103020a290c0c0102121611060d06030b100614030c0705030705030301030506040209060303 85
    0x109194400054020002d848e81b11010340300310302d912956847c00d0040c800c02d83c1c209005406e584402010355502e5980107140c0402101c00d801000d42c01c0504820040d0b000f0226200d4068150041e094000011380d00c6220113032802841d80c40001d45501214881c010b010f00581002c0b5540d100d000041c00442d04821303d041d4801c2d8945402005a1034040c8904042c140c07104041d01c00e00d01c0400c40380204030010886082d02c0a141040b0f980d0f0fa070303d584040315200b80c28071001e504107100b55420f1008107001c034019003100d40c04100000490801802c0030880354041d0b00010310340c0c0c10170620b4450940c5d052240c07048588030704403642d040c00c606003441c00407032464140061500301c0c03900321002c1549800d030580380030011140040040e250789080131914440120f5000343c02c00c003083c40100c0d040b80070701c907100e4130b01401e0003403030b800d55440c0d146240d019030000400391041c1c032051000c0000100100000c5010303610801c06000c2c181807a105004110101402c80c502c290400e101489404841c0600c0d541c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 200253606 1250 200252356 200252369
    0x60e0405030f070804030f1112011a122d0c030307030e09041e140c0d0c030605090a021f120203070c020409081903060e0603120d02030a020d090605160216 68
    0x3943c411140c54056460300c200d81c40200f5076481101813001b4040c8000301d04c10030840c00d41d040c1030081d1516000d20b080390461000341c240e5400d01e00140707a060511041e100c1c2c403000c41c04200e0703042c9000da0078a4240c05454107071038039540481c0880c034843d185051000045a00c0107074002c50612555a40c090101160503040c2070085403040001350038020b4000c08070360084180141c500c0320580d41d0911030000e140c01c440c0c150036486480d1000c4100e0500210388a03000d6000030341d0312001410b654400e8058903004e003540d0820f104110240001d60380ba44240c500c107000700ca050f01210351b1680740203004011041d0050020034410f00030000d24607042103000700d103552f0465000a51240c14604400c450042c07540180080340d403099881d13001034042d40008103640017860a50180d54035002016aa80741003060140118001c2c1700c1d0101d05403990b0050f6400c61240300c0090b003031041490001085a01c010019201a81c4500600000a51507801d01000e0a203501c01740195606a4801c0040040d0511501 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 200254856 1250 200253606 200253637
    0x4091401030c0f06051e090901030305030a060e0106230d060803040f0608100b0c0708011b110a02061b010204090c1e0815130207020a090605120304081c0c050607080109060e040503 79
    0xc0c0b1b2a00200300d481c034650007020441e665843c0d04000700541c00c00c40d480c01d0b54620b0001c0100d46504909201d504031011940c0c0e1840d1025080d41c00d540c1d440ba0340b0000554100188000b02ca4281c840c014070000e8400000150340340d62410000c040d207801143d01c24020b0000c4001803061410440003014140e030500101203568140c0107c0d002e1074081123910031b00240d403800101d140741c046651411500d11185560b20074802405484894551042c000c0c0203612107010003070f1803440c0300c0d08490040e50f8136100e000141440c1c0d542c3c41c5042a1800a00440c0000380b09814030760422200118580c150259450a00b045241074941c2e0003001c007080100c0b40c8581c54030043c2074800c00c00c0340c04483c00c2a80c081c02c80b52100340d4998062000d00441e0144520440440380500125003001059400301c80040f40100b20004c0c00151140703040c07503071400b071404020102c105540410000c106080c018905d075510580c4540c5072044034411600c080e0440c201d520448020300012a000005860701205410b00344c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 200256106 1250 200254856 200254897
    0xa090203030909190b010207050f0103050702340e060d0602090301090204020d0e011d070302040902061204051612030503040210180b0703120603052104091401030c0f0605 75
    0x1d107180184030040c3e510015400030801451034810701d900001c0080e440074800180c168005a03183d42c3c40e80150380d00700c42d07484400865580b00790002c3e40c025480b40191440109603180380124401420840d191840d5000a842c1025519007010002001d06121a0b00c880c1440400a000c0100e00c541c0035201580128052409a400b988406030302540200115991881960540040c2000034a511269441d10074444182c03650700c402c51f03002c0b44401c4007420141e4195420403008203091402079812000500421a414801070315250043d4003e1300104005007401841521004580c1c11903003071800b030003841d08000398100f0140c90300541e040717442611709000c110003100c0780b0101b25003298400050000000b40040448010003c06e802a501d810840c800061010151032042c07000615076440440f80300d00c0c3c500c42034050821000d000603214980b90f950044c41301510b042103500a8415041030041080203c4901d00000034500d41440c3e0f05401d1521202506d24000e0411900500714503148 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 200257356 1250 200256106 200256109
    0xd110a1b050310060f050906010c060e0c101701050a05013903120b06090a09020d0b030106060306060e1f080705070804060806040f090b0105060a0c1a0f070f05030a0902 74
    0x1440c1015050203011100da405154142034040d004510038183d40c81103034a004681c5091040c20319114100603111b1901d0381e401c50f5070340c00c010020710000070210300034081000b19540e141052000d030301195548240031510780c000f000071418010391260344504070b018810005030342c0014130355440f1076010620303558038400700701c4011822000b20700d503d182c5441e0b180e000d8101600300503800c0c40e40003502d0f010005c10500000b808a1440390072811170380203003c2c080c100000e50350354000b4031f903610001c2ca0103d005410480420b013900e50750b8102002003601c4000c113001030303640320740c10010010f42121400016240d00240484d2200b11440c143c3c1089000070008920900441c121412154040d44859486681d8080180614004e0f039500d8840d03828181600300ba00f4041c007800d400310381c0240e10b40d002c41e4a4041001015800310010209005030f8500c218041140740290b4295a901151707100d030300d464580254420828001c00440c02e001440c09488502980002a250301c9503c1c18400074201c0502e00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 200258606 1250 200257356 200257403
    0xf0606080c2505070f0605070c0b18210d03050f06040b0102070e010305060109050601180506090d0b0c07060c021603020d0609050f0d090603020c060a05180601080f0d110a 75
    0x88400745000582d074460403c101c00065060304562142c42e00307001c0d590b00c410040b10b05c5d1161000141808101000a000300340d214002042002c1740110840d41480780040818110540002940c040f420910086600280d0502480d105000340d450108240d1611032074281c01d008000e0138041c0a00c3c0e940c00029647d9008200c0c1c400a04032175503a640e0b09680d24a00396946040900868000fa410000032401c00c0d40546c0400d00c1c0700e040608201c2842c0d0424003400002c0d0800850658001110304910000c0780000040600480c0c0714401c4030f690344042d0a200050741d030340e155100111b41c008202c01c0c080c5076103900004240c0b941100d84203105170140c241070010b00002c5d40050900c4c01040d42c0d42007110300c00900e0f040460082d0700c8145216949140c20780407030080b6108080300b60000c10000350444015848982e025000f280711940b12400c40e40601d291141c01d0b00b06400690100c48215644917040043d0501c1d100e651034900102d000d603490385e5480d8450b06030300402d10a0f100800d4a441001e45 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 200259856 1250 200258606 200258647
    0xa06030b180c1302180a060203070b15040f0209040525110114130201090806070e06030903130b0d06050d020d0602070f060510050415050904030c0c0b0a0e040f0606080c 74
    0x402990a04202c04942c3e0000d511503001c4941043c8944031261444c14901891000c5491640181d42416025258802503050040081c030746104455004500d596461180d001036030004a030040c0c448403082c00b404212200a000880d0380920380d640701c1800314000c00302ca00300070101c0c981044011141d5000354050042c00c1241d01006d8004000c00458000072101031026a000f41c8c1d50180140d035415503070751600d0082d99500c000900a4202002e1350402d00c000315000032104003180e191030440b081d400c00e10710541c0c01c0b00300c42c9000020f1020401d00c890254102800c0100d5100320303a8401c9a0004120016111004048030b4022411714148031015000c1d2240e250040f80511051504070783d4a04070a003540202c910603840c111481204554083c074038001e480c0040d01c48541510781c1d8070240d80102c40600d007158241c1c10b505020074508082c3c4040d1417800c03807075101c00d184034a4042c00c0106450f03940411a41341440d0030f030200101584510900c0d0040406034026980c2d16003070007088211034a1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 200261106 1250 200259856 200259859
    0x7050d1b080d02180f1e1507030810090c0804021003020910030b030d0c170f0c010e070501110f060c0c01021201120c1512020318010914060a06030b180c 67
    0x3082407440414140c006001424036a848007013442e02000403c03c0011340d28100c44d41080202401e0480701c4850818295050001060203140c2c02448949550039803009a0440014000006004060403001e100001400201d1424044001144001001030030000c001074400d02a0308140b006e040c1c02941107508111015001c100200420306020740900381d0b0f502017038043c2c803851034110f0031103104e04650790a45070b2004511039214003445045085801142883c900000100101e00c1c400409200700a0820045005000024070b00400504800c68104040426030400702181114240115503d98800c0f018845607803100b41c550300c07940c0207000710070348104070020a078004200080c0d2030306801c42c054803811212041544070030741a4003600800320428045900310307800320041c10464018582c842074002070703144040c034030180075070a5540200d030540301c10694035500003200b002400001d61200b02010107001452441e41d4820720118000e00f49490090908a6a17140303040c240088151101d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 200262356 1250 200261106 200261123
    0x70b1c09021c0213060b0403020402180a090501031a01080d080406020405060408060105150c0d0e01031413030906050418020903070b120a14060f13110c010c09080307050d1b 76
    0x40380d401916a000646200307074490084084015030001390f500a40082d074004107103050429140d68240006500610952080c50342400d036060300d80d84401701a00c005106003000400c0035490b5040640994271030604035020543c805005000245001070a4a0042c043e464040043c0d07803541000d00c024090754021541c400790000d0000780120000074454143d81c2c0444e0441c000042407aa44542c40c802d446801d03207503800c001d00f030043d26806004a8095101e041c1000b1891070680b04545802c0401107a150240f02c6180e0700040c103045d40aa002c80150481e410158a81420107100786c2c00750940105100038103400050031116902c0504c5814010419468000d03114900c82c416444680801c8481031329903450402d60800451842101a005080c00f80aa450460161082c000b401001c900c0e00943ca945488400100000c014001e00002074038200004002c10b031884d0003448004142d01c0302c6e1980d40280440c0001c20000b160701c41c035504150a028050980c1610700c0e480110003128054030f00c0c80c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 200263606 1250 200262356 200262379
    0x8060d06061e0b120402010c210f0e03010507080129040603020a020d020102040b03011802070c060816020705150a0210021303060c030903090b0f09210f070b1c0902 72
    0x4001c4070b40040d080a41840007030340c2c55121110b0394601d0241c04108030720741c07005402041c099401041401e11950060001c40c2e070280810207810882e11400d0a200c2c00600039102213803071150300a140301120071085009014900704144010411103043c010101c0860684081910300f03c0305000729a049900c42c0c1546440e88d59400703000e0b00a40194200002500640300030a0005206108503426030703102818050441c0d00304024040950541c08241881960821050340800e00c07281035100200300c940e680360081d10f45a0240081c0f4150190b040040d5400291b0500007541c5810050b4000a504620f86441d01103084080f440d03c6c40014050303910f86d10000304019000d07100c144210949000c0d5a0910984030003010440840d450014050700080745020b0510110034000e00a10804600c16040307803d25940c4400103504104001c0c1c900d44140420304030411110050082c4204882004041c0c074400f45080c52a040c00c0c8500c6c180100d031600d0f02100312600d02455803122040315005002011441d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 200264856 1250 200263606 200263619
    0x30b0c1c0b03160305030a030906021b0717030a090308030c04120507050102011a0306180111040e150102010b011e0201060e0703090506090303061008130609121e08040308060d0606 79
    0x41007580d284a0003802810400300d0311402e21a141411640c1c0180258a40300c102401100200f00401c021207580ea003c0210a160046222103c40a02111006050000d25000100410100c3c840782141c994209000d0362403101d030841d4082d41100e41240c0c140d41e89a5a00d10901507a2040d904088401450500070100b402030001300f00e4281d130000c1e0000c006840000440d01c08015541c8251545a0b110100045600810980c903054000c0c030280040b944101c6507080d000960055000f40303507a00780a0082042c1c2c0d06a41054200040c02800200004c550a2000070000c160b144192001c2c0c060145044980a2003503000c0300c0140044502c03000c180c01d03d10001009401008003da0f240d102d01e601183c103000f00407080302e00503e0020442c41051540942c1990400c030300904c003100c0304811241c94000f040440c0a2245d41e18401c0403424002c402554001d0645003002810007c40300d5004500204690082c070b00a400c83c0e00342c100300010341d07190360000b449120940d10050990b401c044000031380 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 200266106 1250 200264856 200264861
    0xd20030106060f030507080402090c0a031b0c0215030601080c030411060f09040b09010f180204211202010203060d060e010e1002090f0f03060103060c11012a0507020307030b0c1c 78
    0x403410541d03001d000c1c0b07450741d9004903082c1070223460113540812800e000c0b80070181d1120043c00300c50139500b00400ca41580501c1c84803001203c1c038100f00840c40c00020300c405c501d44031000f4401d41144030b40380d60540c1080d6000074040c10b001484a030380800c0003c00700c0d0900828540d002c80300c0800400759075030707201c0001001806070440003140c2e008504100b150b00700d41c81e003811b40c1c40c1a1084040b8a440f100c1c90101c2803407207144590914a40140c0c02c10010070041c0f01c80c0c04000500001300d280900306581071a0500c043c2c641041031004591062040c050f0075176814003660800c94204402080502c5d102610a0040902c4a0541440d120f41c1a5000d80803046401416a480c0c044400c0b04200d41201c003807100761090041c41c181c0c90380000c0018070000d10036600c00c0710a040b492034031264a9000300c0c1d02d507003100c0b04040e1142c0e0711400505031008000c0c907150b8480c440310f01c91500c00d040c4102c41c2e0104e680c031311841c040140200810400035020070200016070f1418007008071170491a0362a240700000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 200267356 1250 200266106 200266127
    0x6062e090e010801050f0a020a050c0a050c12030f0306100504090c0801140a030b0a0513080301030b1501050427020d09140709050c041a0904061403100b0d2003010606 73
    0x100c40d001d4000050744500610034144280c4140c103c3c694030340d4824010344000e50054000c40c0610809200c0d40318818410040b80108030f00c948018030440d0781d80010406098003940b480a42d0b64000c0040c100841424001d40780c01070416a2540041909807000f039800d4080c90b0006d4840724604540d000b05d43d64072608581c101c8034062001c182040d00c480621840c604280409004147c01c03e01142e40c10425600140c0d000001843d0096052250b640341c08480e030082e0300c160303030600380d20341804280503100b002c1d1b9103900424208646044d241600d1105010f20302100c000148900c040810820b8030a50121410005d10701c0040284644501d45a40301040349400c0d040759100700c0102141e070504505c0394a004501ca901c9040c149407900f016410b07500003800d010800320300c0900c489901c036200da000e080040c3ca00950030f040c2e41e504001c02e1500d0182c404c07281040443c201281201c254450501500a154112440c070300b41c1b50184c5150759580d81001120f64142d0300c0e081c2e001461542c0b080303107001c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 200268606 1250 200267356 200267369
    0x40b0a05030a06091802090a0b1c0c0801090b04020405090c0603190501052b0c030b040b090615100e040b100908071215020304060f0606020706170906062e09 69
    0x201098841312103008442c2968030300100e0512128070b035005860200d0384254400141000480d03a0b4200c00d012808803a0703c01000c000380d0341c280d16a0001c005441e50010040c000a00003040b0307810450b100d1220300a4041d2002c1d001701d50301d90109580407024488041c8003000900304d1560380c200402c0d401a400c1d040c1454140c0c080c80e080000c0703510701d0909507294940303d100007546c2100f0003501c2d903106403000c00c0c4405c40350240c0b101d4000001885264105105e503000310115046403604402c514102080200a01c01c0300046038035800141d41c036100a00d14400300d610b0b18118422185010400401c0c0551000783d01007007810f200354080b035000e4509010b55443e9810b07244420b07500c0030703444152031410800600c80209503040f480d203800180d02171a03206001d0341c408942105100302e50400c40384540c1001e070068000c51401e00480360032068455020980490312682032520f60107080d111000038151603c503904501091000c1c00c040c0c41c2c2e0b01c0681000ca0791000c850002103002901c140f241d4800d51 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 200269856 1250 200268606 200268611
    0x4080c0f031c05010b04033003140a0e0a030e0d3921020a24020106080a0b0115050c06071e0504050d0f08040902040b030f0606030709060e06040b0a05030a 68
    0x2c141141c90254a04a41040c3d0351541018156900c48200d50102d501d904140200e205031103007161603001c1000500203950310001000400b0032080028400024080d1120741d04100014108034000502030125541624295560120010000d02d0821001201404a00440541c200340003100c0c607a81c521780d46e0f0440c0201d203440d00c501c051504c0b0a000d114110200d0b1011280c903045208140c000e56241e84001c100d8000746031a10024450909071508828811a1001d24000300a40910400000d041403c004203003682d11644d40140054050090304845204603041c0e01169020741c05071100c04404c2400c0d5031151501440007444003913582003000242a800c0420320026000e0400c0b1800d650000d420548811444d40781d01d0984100d8090803154001d04000001d02c0c49400d2010740702400c00c0d0052690fa9003003101415400d03d6000d0001c17881030b02c04000307202495801c0480342d4104d49ea00e0030500704548980c80004e045000d20b5200360422079000070881f1110b980540103511a10088004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 200271106 1250 200269856 200269897
    0x30106050f0a030b0406020909130b0a111605030d0e06070305060a062705030d020703061104081509190606153f060308040e090f0c010804080c0f03 65
    0x400c605061079620540d00540d502c201400400c0041c01e0480d80140240c07000351030b14410a0118400c100b0440d9004020a010201c58003000381082055130040f25140b000d0051644201c5800014440c018507207504016a42600c0208441442583c907e081d0304c003030420060340703c2032400381c4481c022034601c07000a10300b00000c4c090746010f00101c019205159258105000052070510848116005d10081507a0b4070f9800075031981d0800025910752030a90241801d6071851401c4030680e00c0d201d503800766040d4140020310910400180000489504050100d07444d11610707075403400c0030b00003540610301c20310900303c0c00c0a1141c580c04c49011560b2b1981d10000c1c1d40c0726094101e550040150746803a403541d5103100712900540c1c44413201c04501303100f100301005040300a1590210f400983c4100c40d03400740854100055405580b0380c1c0d41c403c03e14805001041d203640c29076600d803036244000a0620003060b01040c28010700f6000e07203603000384030011240038210048150381e80c1d800c20110240d107090210701 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 200272356 1250 200271106 200271109
    0x170109051e040b0604020d0e07150905040b10081e1608070503150f0303090d1a0601050c03030106050f040314010e010506010201020703020613030221130501080106210b0a0306020903010605 83
    0xc1d2035100755000018600315884040c100406580710012262165849080005951034140000c0b802442e044018401d100641d0a0180c864001a07000d035200794509851203046032200008c5104480b8607151000842e40c0b88008006031041c80b5502e021302c42c840004100910707541c500e051116689948034170780940d035290760442d80c922085416140ca02030768142d55119061050800700700c3c2e8001070540741840e4803803000c1201920315400c141d42c032000d80303103001c008000706e8034a042e0807110a2030054545600715500c50396900c070620800c0e042001c001940366091880c10240e501969000c0c20700d420003c0c090800c240030b00340071080021603500c0d040101d103466005108588070150f054000e00100d6491480e1700ca0100b0b00c07800d059087d03006000c000c0310003400d9112580300b0041c08015854031225448180d52140c5900c0d04801e06000075500140a02c640102a401e50460400710784020b6103440d062000282c4a52740300f582e0840308840004c0104601e44c1c0181c1403000f01074008102580d600d00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 200273606 1250 200272356 200272411
    0x20307020a120f0b0403030e01020c03030a06050f0105040b0c160902091005030112031b02091f0905071d0a0302040213140306040201090b250f031205070e1017010905 73
    0xc0000b02881200035045000604c840c100030f50007402810005510380407106a642039038000c50742400141c20010410809118522552000d0b01c0b064940e01c0e8401b4680300003030100e20407801100c00c20100482c1100c04501c08126180c12030ba1801b4a0301482540e0340c05280282d0040401c603481003400c5606100554800c00a0b06e04072075121314a1403610791243c03400e031482c0440b030891000310440f07086288056103407503640f81e01480b900160300c80c01950072041000c440322590071000350b030343c00c2c101400203803507010300710240c2e20020078003804803243c050000503002c00c07040c6d00c02504107001162180c000e00b1043d00300c000315060382025102182d400d500f0035032602002c89009000c518004018403d502419010304840034402004149000300041658440201d6803c02c507150100c1c9264507080550014503032202d12103c0b070040c462400e003603c001d4070480500111034007941d5002c900e00c1c0d4041c45000100c0344001c5215500300507503103032080e081c0a810b0481c1c0c00e0301e0506c10811a0141c208981c03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 200274856 1250 200273606 200273639
    0x3e01031a0d02010210090b10170604110d050d08100f0f35100c0518090c0d0f0608010b060c0a0312060509130c0f0e041506080a03020307020a 62
    0x303101810551003000100400c2803004103069046204e0b1055002001e182c030700c902c00704107000c1e11404280d817a00d41c2c101d6400300c2a039006075911020300c848038954080001030755504076a111a03c03c04010394600845c45a000c8038202504511640c00000082e9800c41078035070240941c0c8903510740f169102c04070300c03641124900c25614290101d180820800030401d10000d100c00c07040907005140b210390300c4800104000e441486d81d00c1e070400e031000d0f058640c8030700c10740c2c00c1245142461401d1403140f803400c1c004603086180041c0940700c0440065481e0041d8000c440e06032941d510104501e49a80040c100200020701915100d0341ca010034402c1d0900c0c01d6001d86105003075810007070403078107203030b95048910a08207103003600c0c1140c4841d00030455603505c0c60309a100340085602c1c00b8521f2003d0401340000c1030740d980200200301c14400b06122186002c4000d40e445034004030480d0500e160b016400c402801075a02880041c02119031840401d98084001c140f014002c41e240094540c6800e030750403100d00079 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 200276106 1250 200274856 200274881
    0x100302010f0215160903150c090e0f160e0612161713050a0b04081c1a0d05160303050703030c02030a050714070308160204050109273e0103 61
    0x9000004841136560038041d81081041d1808540040d9241d85805400e28141150300d406c61701d03030301c507560f24941c00501d0400814041000c45c0d000d081208a0940085020f84480040220030341c0c0904414081c4074051030460001c0c022661742c0001c18455a03058005584403140702c0190311040481c50321804099441e07080080350722245848150320381d0030032458464202c2da680901c042c0c0c41d010038240e0b2140da04c110701a000c4c003541d40300245468100351413008a01c5580034680100d100840d5070f8a9298885080140c84d41c0022004604129282c500d1124003648060301202c0701204050344100600000c0784aa241440300c40000202603803a4021140040001384080c0150804585e50068008030080d042d01a5200765840707483d9911035611108a180c400040b111520b01103041c01e100d001c8c014071460008001d140c21004a0041107030030f95901104010800c0c000c1000d03c0300105020401c202d411000d42c010782c24501008080007080c184c03400e01409945c0e48003c9035402801181b01c10400e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 200277356 1250 200276106 200276143
    0x2061302010818070f0f05010f0c05060c0a11030a090317030405060f13050d05090102120c0c0607050f0d1d03010b03060105060d0e010204031103010606091409130209100302010f02 79
    0x150f001002640f0782c400e44000341a44500100051200d50000600000d0103107881c0d9002a2070509002508031003a011203d020842500035880100d4070102c0c1c56038014000e014100e03516002d5503c12100ca04208010b106030340400991006002d401044400407640f00f008031203c4010460a68009408202c402602030b4010100194064400401c3c2d00e40c00084103441c410a0071480d180c280c03401000c50300b210040fa030000350144040d81c0401c072076009030310601e4910345408080b00c01e0a0b10f5040b042c5c1464003a01c0041030920800205000d0451009100c500b00d84141d005800010103202035a280b604d043c1030350300c039608604d00f0103001e441075225019004150b540d180100703021031070344a810303c00c42569591858402e95442800140011406140c2c00e00d400540b0b0010035007124030740d074000024410141c0c010800703420103e800c104919030469030104c081e13031803000c218100010002c0095000300170b0030410403003500705002102541d000381d1741d85220106002c0f06aa844800c80019450103030b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 200278606 1250 200277356 200277361
    0x61d090a1101030e03030411030705040608120c07080a0f1703071d01110706020708070e0637090509010f061d250c061401030c1202150c0706020613020108 68
    0x40740760040d072500c05010300d03001a20429003202c0c2070940c0c109840443d480704002c81c800201d07280c100400b0001c0c1c04100c50801c0a80c1c0b070001340903914a42c031741500ba051000418207001c0d8407800d009035801858440240c1d4815107051030003007186a0180800c4030410440b201c82643c4042d030109582c17090303490f500ca403032120108010a00703540685442302c5042201405413080040340c240305c000d000300b0654000309250347c180f40b02d050504500740c020300c0401c0c0c211002c002003039440d07600340344010046411518a102502041070700480300108040b9898002c40400901d085850703001320321501d5040000c018030075110f4a0241521580e105007814084c0d495050004606109078064102a1004800e80780e03d2030300c07000340000715058003820041a002c0d848081809614040e061240080c080c0c2c202403503045582e0300514596600a15078480e88950402e0304544801c0b001042003425078580507240c006a0f410a40d80c3c82080c0224030040c004d96010448000b81811000b44080e4143c40307900155 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 200279856 1250 200278606 200278613
    0x1b011506031805010c090302150304030f081f15110105060105030615091507030809010b0d06050403020102090904110f01030908221e0302100f080a02030601020c0a0801061d090a 78
    0x1000d01002c0804001e072601100d8000407002d00c2503403440d060940f9000030710343c0755004000490007071100c0d41706640b030700304100800070780e00c048440c0540d14141041c2d0300d10b845281314500e00642c402c208005e00101d4860120f412035040d43c49a1001d241c6550f140c001c0b41c09008140c0c00d87c0e41c1980e40c14003140d41400440c0b014540b03650200300c034001d0201c4282c01c00c141840040d020a90a507440c00701a580003ea1209242d404101075a00c00c2c03204009010131103055002c151800e42524001e02110307510804034003014400e4044a00d4000010300e40070b1181450f041c0000300041103070320144030b0312105010780003d5000740185124550401e00d8142000c0446480084411304608000700c95a0310700c202044130720b0040020404440404142d00c1003a08600c14400c00c4462007550b182070005001a03045440e900c507221075400450500c0c0542c483d1102c0c40183c0c5010700500903282d00039040c44003c07a482e00150300000891ba641400911203041e150754a48000f40151a440b94030380212040c1c1010 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 200281106 1250 200279856 200279861
    0x403240938060f0d0f0602030403030e0d02030d05071b0507060207080106080c0609030106080303040606050405010611030a0e0f030d02150c040501090e060d080d020702122a0604090608031b01150603 87
    0x2070b018046024130031407903032000400d183c0440201c942c203034003000303000607d60715203c0e01c09100f10017002812006407401c00a5643e015001e4007a00140e00c880004900911420705500302c1c0e8141c04120120031090324107103446105034014040103110302c03600011002d90502070402110700860140c001100c070f4a0500005902c203143d41b80e099901c3d4100001e400c0c00800c000c520aa008010001d0660704000400c01a240c1c103900c40c20801c810310981c41c1304100040121841c0f908076051645024040d034010610034810680306550500801400c041c0c0f030b0307401007003c00d83d03008407060348203065503107041c0c0a056000d140500e03400074000e10380034410030325840e410700e4000d04000c05030a001c2e000f036580c5403110f500800c1424522074000c41e40700114188205035240e011721041c007070501d481d00203140301c104500035211011280320002c5d01200c0ba0702c62070b00700d8002d400b0b000c00900c100703911504055a29400140c0f038411031024200406200c4e107040c418028052220032900b15418a0720360101d01 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 200282356 1250 200281106 200281129
    0x13030806030a0803010e240604050d0f0203031b0c1e0111100504030c11180c07060f050405010207020a0e01051005090619090f050103050c040324093806 67
    0xc00d0321422150b9800310750034401540c020009041200c446103440380f44103050307038404c01105003c00e14a06840880350349108c02d0b101616000e44806c401402242001c00440d2101940650540400070315142d48405c8035900b50440c0350311504071000e0018100038068503004800f80450640b00a105548242d071190f181868000c141e50304403000c11354009900d03001c9540659040b00420346425040f01080101c1c3e0f105000f50030110781000900c50001a81505041c004000c005000c00c0040c0c640c1c10031145500c403000c000e00823401000070380740500e82103000354801d8030300382d114904100001401074407084042d4143c40e005440f045120700c3c10303039094074150428030805900c42018004200140c1c220442c00d0a400510354840f1481444d0401c0c4451007421500300604150030b240400c1403401c445001c4800b1281e00c88000c400396400e055078600c0d04070000c0e024101690420201c00180121854003c07411104111483d00301c90400f0140b4190205000401884100d9080003444900d85003a0a41 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 200283606 1250 200282356 200282359
    0x3070c0b0f071b0809090408250c17280b010308070c05120d08151c0309050d020d08090102150108030a0305070338191401110a080a0e04020c10050a0513030806 70
    0x5041c001d02103039503420030020300a030008a280c01620b0006000500ea080802089560a03a0300c40c40701c2f0f0303d9002d86403810b840907085915112540310000c2499030640090107600301c1c1024115586078506a41590302a582c250307050500040080b0b941c0c41e09406032100f044a00300146109480d0607000d580c41c00d002041701040d4a81c565031a85541c5807102410300c501034203280c0003c0e06100786009440c0080c550081e0780125000100f000060301d664440c0ca028a420101250302c40f07420341c0040b86801000c4c0059422011034000019908a000000d0168902640ca003403100343e0310f0300e80483c100c1d20502010a042114003103c08110304808c1e590080b07181d50354a5100620040c0e001094110b00c2040103007500505404040140b1800d04514003d8080d092801d421281950400141e50711780710800036020407400a0300030200d1f400303040d0002040320302800079500c072050b51989a898846059180115500303040c00507041514074420140701c2c552a5880000111003924100c4000c40000c0c0f20300d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 200284856 1250 200283606 200283623
    0x180506030c150304060e010506030c040f0204050607030f03060b070c030b100305010e03040509162109050a0c030219050307120602090a030506061f09050603070c0b0f071b08090904 79
    0x21074154941c180014001014000002e80da82018a440c4003124041214000303ea450481800180d070380226a00070000c0c01103c002c0f84801400910304001e102d80c0c0d203c603510503000140d1908141d04800640001166600e04000c51070b40d03030110aa0038482c1d0900200b00504c089401d00010301c010003a541c2014800c02000e0074941c880d5181802c5502071011203410741d0020408200c5031034400b8185500c8820300400e07035403501c0d0000b0040c0075030b02c1d0000a21703101c580c0715040c2d0002e042168403030137200341c1203000c0740c110aa690070320f14981e04043c0030980c007602c054482550b0319402200d0355000c442002d0700078085c840c0350070306448110010000071541c1c56000c0188008075034031508054051405400a000141030002c104524000b0300000d100410310325100ba8071410340c02c00d800307904440056829580c1c95071140c0045030081c04000c8000c20701c0054600707000307500d8640180301c0e1040d5400d4860700d0001140b4032a007150450855402451460100b25aa44c24149070002c56003141c41010320 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 200286106 1250 200284856 200284873
    0x601141207050d0b120a060905150f010603060905100b1e030f0703051602070302091b0711040501080a21031803050a030506100e0906061908010f06050418050603 71
    0x34000c08030140c540000140e0b02150192801ca5140f0500301e800c08203e0f000e0410200000f03400e520b8102e029800341c40780780d4810644042c8a0b041c02501c6c0500c1680c82140325902e40301d0804481c1510a01441d40080c1c078060012038061144d1040074002d500381c0b88002c2c0101d24265040541360b0003501018003840804545009e984040c001641c020b003204905d00f2130628002e01c0040403120010142c1164201100c40c884140e5001308494003500c0d01910352002903503501c90f43c050305031040100c0c0c5030000000501407042c0f010700702d908040c108040b10240100d0f681c40b81210342c0c0d440d1451015000b00e8030030a101c502e190319000980320b880180c0c18082401d10101140c0002c00142800030740200d1800a8138610207a0300d0b02c0394a80c4400c007143c64602608403244024002c44040b03c00f58055901c40001c07070384558540003a242c552034010781e807030104680250010003c04086c810356074020312505010425900600070784040d03813000540c001c006203400c50b507400030380f10203031070b05401d40502c846 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 200287356 1250 200286106 200286127
    0x4020904140106080a060b010203040e04300804021005040b0a1d0a060206100f12060f0908032701020c0c061315090e0901060605090f01051b0703050d080c03060114 72
    0xf035200070020000a40550215418040d00741d9034001103150454204010500c2004d01100d61a50060780091842080c0f400300c0c1407400701c0e0700302c11303150b12000b1100034104004943d01445c901e100d40c1c4292070001d40e088010310245e59500650258210303000d41402807407030582c1305c0c402e01940000c44d00b0035501c2140c456408200315114030707005200160021800c00c45005500f140c0c400080c03a80703c003042d5115107000c039184403102c960400103106540781c1c9078045010189402a0103000d4015003459507e0910b006051041d2400001410040c100202d408002d40c00600c07e650740308074810080c1502403100c808004260f4003150b4900000e507035520010810001c102c021480c0072201c1d840e01808141007410002241c60000c2800d4902c0e030601d0401c0c0b1610303501030b06a071003010040d136103060640e60f00001600c140c000d840f54120071b00303048050503d2803000003c0301c000b143d01a0054032040500c4000468038140c08985000019608001140b0603500c01c00144654140b0781d03680a007801403401 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 200288606 1250 200287356 200287361
    0x1c0c0506040906080f190305030712050126060903040302010804050312010306020306090c0a020c0405060103140f150a06080103110a0b0c071a0901080a1a03031b10050906040209041401 81
    0x10442d81d9043d0703980c0c03402c0c400300004002c20290090400010140390140043c885140d92808900034100440807001c0380c003460040648616000004409120560b1a4801c8000c0403009480c0380d1155407401800f14840a0003040f03080c00740c0c1541020b14507184c19500155030708100a0400c03078146c481000b11b81448040c032412203010b0340c0b04400c00740e0303642000e00402c050800d0290038155511800c001c6588001e030006080120404191004211a668400141c000f042145c0341910390380c02e89020807450000b012459131081c64110030914554910206000300c00c0c0c40e43c0644004103030100014000301e0b2403180c000c10f4444000b81a12400c940310096040560028044840154400c1c2c4043c070001d03000340b100c7d0031180c508565550400312582c000a01011024002d102020796a03031400580d10607500000202c0180070b0216a510b00c0b0201e46100303001e800000442c3c1901070310180d800d10b4103440c01405d000d401020001d2546448540800664550244c4122046103007000106200542130 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 200289856 1250 200288606 200288609
    0x9060303040b120a110f0d0515040c020102040302040f1e0902031e061005010206090304090504020d0227012405030601020c040c090801110a1e020c0303030f011e03021c0c050604 78
    0x4442000341404c1c40c00285055400c030400c503c0e0030740c00c00e0240005510900c425210494028030010900340c903a11524502d904246030b5658000303003485a0040895015001802140d10039039041240400803140c810403070720000c07089115400c00045c40e504641468200e5540c0c00c0c00241036900013003403014200d0469002c10403030942a0480030800000c1154600c0c0d00c00180401c2c0003900591400010844e26840b60340500c042d260b07030381c0700400c00755200c00340f2500352140d000c4c200c0c0d508a010b4105546040200386c104510100c0124008103410041c0c49e1000300440c00004005662140389100382c410381c10040000341188982241280240d807580601e8002e05d000b51254103e060800c449542035401c0b000b1104041d000400400c00d0750740e0b006055000c3c010000b08032007002100e01c04c0813410000071a01e860340c184404410322640c800c000034003904940102c02c240c0d909911481b8003500300315103440043c1d40000781c0340c07021492212002070750810502c81d108162220703072900d00080064019 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 200291106 1250 200289856 200289877
    0x6010207150207510c03020a050102030109020c0d030c05030f1e0a02090f040501030c0e040f05030c060105120c030d0503090a0803040b06010f091518171b060f070209060303040b 78
    0x45448540c134842d4450362180040303142c90000b1604072007102a40100b40310001c10704020390214540d080c14400e0100144281c1d02900035903507560341d002d80b1806508007000f8042035004000030421403901a1088003428421516810705654950008881809004082003160131806061504068000544c1489000d00200041c3c0780c0c01c001c411710180455101d4510b0113140303401e00500110701d00b0510380c0700722070bc29017088196541c1c51520b16002002d000c0020114800410080034407070022a00074180c070025911380980d09c00c1804000d0b940c4001500480e01500200007580e40c1714403c2c0029a03002042c2400c039401c0c82100d82d1039481d50b9004843c141d40e200501030902c045580e028a81c0581c40241d80351070900302d82001440110380300d80318900800d008403940042480d012806850004103510100a189200c2c800202500c1c0c1007110036005290400d034550000c2480e01c042038584441964844c5400e01c1080c0d824004a00400b505084d03251009200009595412000503c804180b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 200292356 1250 200291106 200291159
    0x80106050310140423072a02040f0b0d1119031214041a031b040e0109090606030605010303050715060602030d0f0f090317060a1202010f0320120f06010207150207 71
    0x5281b07100501c400b802124449000104400903c070310031142039070200050f0119000948200502c1c00d420043c00c40f50078064100700c040ca104004e002c0b40c0d080088a03090162180086400c1182510003010134901000744054090a014040144601111100c5146a0000f10b00c2c2c40c1c0c0310010050b0071855005184180c010010800c050005500744104800460410050800703081451101014805004518240342e841c0c3c10301060058a4000c0750055401c4072081060b96103e0170001c081d544000703426112180a408200511003d601c00c400403545298060750811060441804c0a00b820347c9140000742d4480110760482210342c450b0091103880798556402d10445400d4a10041d00b009140354071034078141c0300030000c000c1c0e21032540540a80c24030b03004c40001b01812081c0c00034405083d81160001100d0040040d0f0b2200c0402050303000030840392030f50a95250480e915000740201c5031180140c02101080109200e4558038407071441840c010303200d2850303c9070081910310b03034031801e0302c0040d0f01e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 200293606 1250 200292356 200292361
    0x32102010f0c09030b040807060c090602010506032a04090c08011d0c0114030a0207050d0f02070801090c0e0403050f031009050f040c14040228080106050310140423 72
    0x19024440e05002a541c05024440a10802c0c000350075280a48800782116040d10001403c0042c41c100b02c81704540c0c4540100071611220703500802501e80707402004059840c3c4000b10b4414500000c25030540103040030490081c101051112000e04e2808031480e4119807140301102c0003907911003005020b0010700000084064460704a51000c0640c110400c9a41c1c0081000349296684146000342c5541154682681c0ba110245010003c0c840c590020701280105505070441583c00803020000034503960843d03564685400083d400c0f03901303518000380140200d2008001444c1c109102079031050007400d00c0c074103148290030f61381d10580c0304540403200b4a0502106200c40d075a144243d80d08112080201409441c00350303a18455520207014120309407208141050648d95507070119110b0304071070010b0264540d100500c0d000c4d42d59100f0314140c04209405c0c00407541d40d12940070b0340e1051181c110f1002e40d05261004000480b0708110386030340c0050302d40c011180b400c002c0e0003202c502040e80c009080d007a40b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 200294856 1250 200293606 200293673
    0x140a0e010209031e0c1005190c0204051608010b04120b040f1a040c0f140424030c03021302090102030307030f111908071d010e040b0d0b150103050705030112050703 72
    0x50b81102440b13106e101c08107682e0142ca07130b0205c02d803040490380c4540401340203c40201030310a807102d482c000354054100410000d2828022500b904124066140c0343d401d644c03148c003e4007242c0268094030113100304112405010407502c0c0d18241e08207009140c0084070110350744549100640d00401c001c0d551840c1e03018001080400c2c2e00c110000c050781d00050104078100840e460300180a42e181510030b80d202e1040d074003c245580d2012400c1204440c82e00710050f9031740391008200440707100503031040040030381102c0c1c480580c0c000c40780740500503400785196641d0a44e080d8000c150030700090604a0b5200c542071684019a001015548a4414891204078840c040140280c00003082641000900e05500c8100c090707400c03c81020f0442420312141d0182100c0c04100281600b105507503100c90360301801c0044c0007920680314081d910340f04a00d194a076410006400b83c0f041582c0010000380c00300010802d1400741c0e440308501511800994003c10703500e4495504400b00c03089240300d0294100b0030140c03803 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 200296106 1250 200294856 200294863
    0x8030703050d061d01140a0e0114220902011112041802091509121c11031c06060810030224190201020405040b030c030d03050907080a060519140a0e010209031e 70
    0xc001003259030300d47c4141408566075003001c043c803440040c1c5114014a12241e915a1460041210780924095080140082000c003801000d0002da000c81d054110b40c200554bc0411101c45600817950041d00d4203140c10350301c0d40610640b03e00800b00036030034405000d941e602c0402a1f40300c3c03903450650340d07240d0304543c04001c070688910810041580c0071840680208007140380c444801c01d92407c2154141b1a808106030844c85550107403201c00e54048040140540d05501c22019074500380c2e02c0e00c02c1640d0b4465040f800a0442c0070107035000c0f400c03481d04108100020034403a642d50340c1d1355502d4100303028007100019600300d0401210140c0d401041c18070142c14540704075180050110700030000c1c4249040425140c11001309203d04049e00e420004251341002c100702e078000d046240c2200c4034078800d8180180201005e83d4103100c14506a044805121031034003e18038511002c6860b50043d844c1c56808074010a54180c0c5164503540030b20545046940520400551020a40f002e2519040a000703a504 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 200297356 1250 200296106 200296139
    0x504030c1203120207050c041104082b0f08150609031501150203210702070b030c070302060105040507050d0e070f030606030c1706040b10090207110301050c0408030703050d061d01 79
    0x1042c1306105080c00b180740003c1d0640140c0c0241e400060000c480343c894803291140344c002c41c04c28400c003136800351041002c024000d00c4540103c0c100303400c00c0134288211024000e48080800240010300414001e44010120000180000300700ea4900101000883d09002840c0c81816100c0400f10040040310400a0740c0483c40045101461502c01c201140f060300001c64080b8943c0340d403a1000040c3c00c54000c0001c400070740703902410345440b0320704400e469589a020f4442200140201800050340307040c2405003500030b03816a1645400d01c001113244500030f00034990b000d02c003481171000019030310304c022405001850042e000403c1d26411405d1604034111241c1c01890520741000070f503188841d0114000f508946e000301c00d917042c0d0711800b908680a0060f5000194168400a02c400030030a0304441000388681c10f40090080303036a0304207024007078099440f5005181d0820051000064861401051310180c40b50700080d0080d15500489107441ca1150340300c0e101ca008500511a05100d100c0801 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 200298606 1250 200297356 200297387
    0x8150307060f1103070206030408130e0c19120501080709050f0105090402101e080a0b010e150904090804060f0210020f09040f09020904051c0503010308190504030c1203 74
    0x30103145000300040602012003160740800083e608000c00e983d50501c202c80d01035800a020f10707181d0509061410650340501028411444403540004130308440d0001c03544180c034258134241c00c05071402120b000c0150284032200800480303103c41084040980b05081c0a0001c08005040fa5400d00c40000b04440e0041e211000101029004208035580c14039a00c3e84107038160f80095644142500a680c00c05064404043d900d0451880145a541c40b5908511900b1080d1040c0310104840b8015602541010405a0005490350201da00c0e051948014450050080c000041c01d804a403601e40d02c0da0801d4007d080082c0e5000f03080d0003225410081c4032003450707100804501d42000c5287d0716081d8401c1881107401075456a0756054180507580c003020310709401514503a02403500d46451601c40f02d0511811122a03a5000740520303084c82070b41540d040e0f0380d0201460380760180c03202103400c2d403241258074001040820031001c000241c1402c5490014410110725601c412014540506580b400e8840031 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 200299856 1250 200298606 200298613
    0x14040b06030f0111040b070206040806070302091804020f061b070902040306150f060c0204020d0207111c1104180c030827061806091002030711010306033906081503 72
    0x4d0301c100900350b0488045450207081c25644209503c00326035540030702e62080340da5005041c104000950150020195100200c2c6e190200a0360504141d00307480040c4c078041d41021100002080741c0c200f41c8010954060504102d0003043e442c003203014a015071380c0c0c00046440e500401d0410030052607010b1200700c1807241112405060600c0c42c1004050744a116800030002d0b413103552425034840340e049400c11401110b00b555201c6c82c43c1003440e0000c2c41d800055000311000105484a021456031038001240e10130318010006074868100b0000d062042c00c0c0f03d016030301099400340000d0641d1180350085101c1e54206880b2100589200480003204040049103030303100e0100026660341600302c40c1c014180018405d40444180003143c81400b89500c0f62703801420308a615186180c000020700001449070f01c1c11104104000011402e96000e4400101a0708004000c1400c441c0c1187c101d0480e410700100120680104000260890b181c40c1e004da00490044400e1001c0c2006031042400e00d040f007079008 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 200301106 1250 200299856 200299871
    0xc0708011b120b09040f0218060a0308091206180105061008011e051302040311150301060c060b0603011401081602030a03090f05030c06060a140a050d050114040b06030f01 75
    0x795004041521010000c105450a00c1100b5880c1a4800341d2412800303000760b8450325103483c000610801c02d035000d0740304002c1d25504100c40030b04102c00a00c188030107001500c0c02c5242d951210540c0e040019070a43c8880d603111102000217040003a603106210304c201c8c04200102040d00182190400342105004004490181445a402130718041c1190303002e00b05421010f590601d082d03a441700d00c5d00718540c814001134098050101c660050f0095078000d01001e0191005442004403180c5401d5001c000d201003072004000c800c2c00784001a280d02c2c000c40010940f07983e918005000c1b42c1c426041440b60504a050303400303c0e56884070415034030003900d0305164407000302490065a20b00a0350030385e9040549551075001040701404c0e007440560b507c8800c8030345a180703130720705581c8480e41116542e018202c080c2c8001584d484a0a072032002e008d028080c000300c80c2c10241403218000040c031041d2120b43d2149000c1d0005060800e103148a24000d451240c0c003400d000b0201810202141c09a04a9030b061004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 200302356 1250 200301106 200301131
    0x3072310110d0e0d1b210f060504020d1b0f0e07090311030c0603090d0f1b0b18060708090c1014071406090304061202030106051209010e0d050c070801 66
    0x750900c002c0141d04160080405078000a55113000040c4000c00740304000d81e42421140a0f00160700a5580c1c084481041802c007041c40c01c1000500c0c40040c0001030490078100102d0f051b94485500300b40084c0901110310090384600601c803140320350000500800704000c20100b800642d0120240c00ca0070002011403c1c5a41d00800c0080d9a00010780300040700e501c094003654003000072014010016110544a00d40036070280d817541461080c0e2000306003080c0b41e407290a40720750440d41c02c020090708030703984840868a07200e0300c801008200c071400f01207445078a8608441000b0142c41244150340e90051807400613003150034040b040a6240c010f070402e0219182041d04100c40300c08410b005001c064640080b8101048001010310745d920305801007100340300c42c4103808802030080d1082c07600c6640501e184e241445049100900c2a40c000407810701c00501c45510072400660803013442c10000c144420500c0059041105198010010600000d82980f100105001c264010003410008010b40a048403 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 200303606 1250 200302356 200302363
    0x6060d0f020906040b131a0109030f03030b0303090d050102031509010f061428080f0f1302010e0a1d060315061203040f0f080f061005010e0307231011 66
    0x2800074851905540003e060752282e61260503445001459041d01c214141c0c02c1030000c0c542402c4250022624107c20a07080d40609aa042220350000e00c0180d12780355610210010010b2100d01641400f0412500b0b055640b002004840306004400050ba682440b500b02c10001c03802140c840d005041e900010005c41d480511100221800c90800d4503102c00480105040342c4195450001d959800f102500e428941c2c600c030165031550b2540f1307504030325100c601c0c03072204801080361012000c40719080081c0342c1c0310810b0000012284103060403540340410800140103001c0036041107031401010142d5180c454070b00e50503030703401040c158003134840d00b824000d19680740c42001705141c0c01415001000300e100703c810800c40d0020941810700c5001c1540b10340c1001c80458203442001c00500c2040d21010403114042042405004003004c182031203480e2100669100b19036268095140c010f00d40009603103aa0340d40200b045003520708421041118803001c0021000340306010004004130f405c2a90401031000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 200304856 1250 200303606 200303633
    0x3140103062f040b070c050a0b07020a090509060a0b0f030105150a06050c0a02060703050c030f04030b090c091b040323010c090e0a15090e0114160503040813080604110306060d 77
    0x107481c4985e513032900341000051603240d41d01c41a0044201480020f180040b240a0300710f551081b242262410798500c01c070004d40c1c0050f41c9601c6075400100208420b002c281d032000310307003200241604000021303500c002800c40f60100c800441c032000103880d1040503e0500303000c2c00501024100981444500324100d580c925428000a014400024851040c140a0000d070f43c5400c13442c104481c4d1b2105000d60b0030809400c00d1000f02e4903029901c004ca03404490200b41240e40c09006002841d071170780c41e40042001400d416070a107032022420003000c0003060f0241b1034019002054124000e0762910002036030300315124214100704004491800b03021003200b03001c3d0b6a4011103130f403002156104600f81e07145902030050b40038550031490150400c0c041030042d0800040d9646110144500341c0d50040c45410b2a00f8003000a000078500300001030010701a5405440a00300401c640c0120a46030321480b031800c40140c8060f82e070301c0048100c0c0c0860b481c00f000280d510900a81b004c1f0b110002d1540d44075a4034290 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 200306106 1250 200304856 200304869
    0x1110705061b0702060408030c011505030c2209030c050d0807050d020a14030f0402040b0a0b09120a050d0203040801050702010c0c0f110a061701082b03140103062f04 73
    0x40c000c0102e41c08028058426240e002800c1c10f60b21030361200c21a81d240d000b00c820220319401c14409011448040281000700c51001d0094000d070150507041100096503290746507603034080c880c10044424014892402050b1103070300c40ca1943c00d40c504003146000e840311551400c21010104102002e5444415206821b403001d501580f50100c0d2001610380702c1004a6007142c050000c01042200d010b44281c480c020341c001d54080200841e164148040070149004120a00f6010400d8030740301d042003100d1070781807202d460a4070381d10f48070ba96a450a0444e021044001648081001d10004a00784191a080840f9000802c40745050000161261103204000f4002c4140c0207844010302914422034134901d007004240c812416115540035081c1e81c500f01040140801031030010840c007400103204500301c079034000940b001c1803151480c00402e22000481c02e04242e210002c403e1115185031489003c0e5125420120381030007103222442d1500e0422140036613035181150329030020a01c0500303c41c2034500 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 200307356 1250 200306106 200306131
    0x510020d110c03160e090111160f1a07020f060103050705010c06020d0c0f030c110a020f03030d020c0d12050411010f02010605190305120403080d05071b03030c020111070506 76
    0x1015000d850402c1c051406194041c011034425060488013141440b0a0710700111040d00c294549082240c221402520000d400071b104008008619100000a00800d40310385c5081c0813420045c1d542060307000e500d01d0101c0c0545415002e01451580502548800c1c050100003000720398919110141c2d500c15600c501414007071180d60f01c0b010300085404a0340001c0c070054050007030b01c3c00d00600400d040072205001e4002898886070321310040c0304903042c10300801048000e02c041001d0360200507200070340340001540b601c801c0000d013071341e8945400a400368050840240121046011001d0015101c00142c400b429103480304010004400c80c80300015800280b0b482d079903400105405134010101038101c294072082d10541010401c40d1148014243c0744240b0586454140081d00d2842500950000400e603920902c4000b04408143e0320140d44000300b0328045d1b07004d00610904503045414280d0940000751140220111542c090003042c1d9140200100c0c0d0340f030302003152192a02d4100c05022500f1070b40 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 200308606 1250 200307356 200307377
    0xd08010e041e020f100c020a0501020a08030109150515130905091c0504170c150a08160c0605130b061e0f120d0512010902160201051303060f020c070510020d 69
    0x1181d0300d07031101e1213500190842840c05000c6902500001800c00100c0c440d1491100104d215480450034425603507104c6489400e590070a01490051314202d1284491890501c034001040d81d40d403510030314482d00300707a1242d41e12202000c1d2211624941d4001021903400c2c81e00344410f0340c178001105007020090000010072131804c04402c441c41c0c420740d032010010500c020100e031950b14000c00c0d240c070b40500445100992411000340e00a0602610080c2c0000c00c04100000d180d88070305000f03807039901456181c4005580c1c0590b8404c0100c3e24252541e40c2e82c0010f0012082c1004200140650032210445850311034641e01044140b0000741441d905000344420031000c046515003217580000b030740403041075940d14448004005e050360081c08407100d01448800001410b0540c40c0700302c030103c030310000d4050506507941d00151004c1d405981c8502c0c0301845d04c03030b000010910921441e003141e0300c241d0000d66076014212103180f4102064111612807203544401b0761400e43c00080305c40c0c401103241007054032031 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 200309856 1250 200308606 200308609
    0xc08160311040b13051602100c0e0d06060b0f030a1505130b0a09020a0503060108011a040b1b0a050f0d0513090905030c030d0b04060e061018090e0d08010e041e02 71
    0x1038040c07a13035040814101818800665140c1e01c6929040704158203d6072450f014944550a4843d600c00c00d1000c140b0f100404441820101c1c0b60f4800140640e1000c26803030b40d9449400c01d5540040500d01c049440807041c040c030b4820714000ca0020b1140704106910b2981020001584141501d810000d03417030b0380e115540368586403000088028643c14100715294522400090081c1d0300c01c41c0c001e40040c05070400401c1180c40b041c0c802040d24030f109030322810103081c0b82003096180d1210101b40c0084c0324503001110b1088081050f0301042d4030030b00107014040d01105c0342c03914010604102c01c05020081c40200c80c1e4900c900d04a000f19807140101240200c46410810304510628955502a002c00600000000c0c110740181490390b1090742d00f04800d5075a10050100c02005079407107035006036040228090a440340c0040d1514030700340004807103001d50300c18840302116420305070114290030030303251840000d404c00c6c4c550b401002154140c001c1890959640c940701c0a40b040b0184508851002200c1503 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 200311106 1250 200309856 200309869
    0x1b04020a0e0607050106090501080f0d0516050d0c05010f0c0e04090602160b010e070f0c121812050d05040302030d0302031b07050c150918061302070c08160311040b 72
    0x1c0c4440a40075076520682400c21a0103010300d40a44142c26040400002d2100800200840c040d0007140241c018414a031404851650002029040500c04040b60380080350381400424280303c4a1344541241205518020382510507a844080c01c00d49400003940c858ae0300b2051000302804100e0300007a2800480c17409000070301429502d8017150035001500c0c410422440c00d01416500e1079104950140e480e0501156504141c5c0d11030b0001400b181751a0000807e060328910f41402c035414a103819141e010002d04820004c0c0d804110302c12940e0b080002440020301940210041c075142c0545421b0450300420b070744207081c1c1d81060406900000268401400c2c046203003240f24039413401552140c5608040f9950f00b130038048a440360545144045540360041d0442d104404083c1a0304044800a0416029200001d1a41d07070040040707094402c1d10031080c4010090f40340f00721455403220703060004891400d210807121844032000c00c1800e1010900c02c2d4628010047e0881c1d0118000038044040b600 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 200312356 1250 200311106 200311127
    0xf190213090b070206090721020f0406050402030c07140106060806010c0804080a030c0303140105151b12120708190e0a050d0201021c020f090f031504030801030b07021b04020a 77
    0x803860300051000303c950218105000c3d88403d0101c960440d00c40207000c8118180b014040e018428135071030f540041c101400c6802c140c0000420009440d9540c40c04503042c2d1780100c91030040c003000040d440c400c100b00040c141a800c030034034000700f040070b0502801600d10180070300028140401a00b1a508100300c04003190081c02000007907420002c400c1c640680401c0c0441c1003140424141103410520008407030019040b540c00400c000c0000300341c0942c800940d4401c0313070103080c00380340c45840c0f000d01801040a50741d40e10000c1102a0f6910940411824000c1c0c003a01c1141040380071000d01c009041060140000c00c4481c0c0c8001510034202d49106251200d10761005040c0d009100d100b00c0c2c0150103602408880c210606e0500304880280d031800124422100c05460604040c41501d07000d0138254407092480c039001c1c04469140710301071020340015108031411030000d00d02d403006004000703403591647c0e0804280e000a08020045071801c4c015400c034400c1503400b80c2e41c00304010000601c1240d8482 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 200313606 1250 200312356 200312363
    0x11a031003030513080a0506040c09021c0e0f06040803180d0203180a1d090106050a27020f030a0b011209051507090f0303020309030105180604060906060b0a050a020f19021309 77
    0x509601c0346d46071a9494140c115015030380b2949840c00081c04200c180201c03503641c50701e000700d24540200c04503000300038040245110128451810b04118900d400c00c50305000c1d602845500d500d9240001040001d4180315842041c2600310058400000345c000098501110039a0407420800c107902001c9071102005a000c0081c4030040503c02c000d000b217120026024804403402400072985030000e12030110450703c00c0c4101d01c41d45c3d907010801e1101803c0a0460355400101c090300d8510081600107098006803415058142d480d802d0014642e0060010301e1a210103580501100800c2d072180c0b40c030b44480c0000421b40511b413000140c1d0191103080001c1c0548500c0000c100b600d81c403810025660740024150901942c600030110307640c0602803111440e40342c40c250060095640f20395500300601a210700484807161529000300b00e20811001514042d290355640c1501d480441e03800910303000401d1400480e0740c01c004555600304c8a9026500006501520300803a01180181200b008008061016 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 200314856 1250 200313606 200313613
    0x31e06020d0504060c1b0204051509010f1415031303030605030d030b040e030c0703030f0201020c01060e04050c4608070305070e0702190f0218011a03100303051308 72
    0x614081c0303240c2d12490146008080400c42001c550300190380816000c22294208038402c601180180303480d8025990190400c10440040340d51000422200c500a800030400f404194070140441c034807851308801903034011601d100e020b82010710415040e10000d01b02e00f110641e0381b020352040c14026046a0000d001c0a0304495904e050520b00400070704850340303014401d50a0074400d94101d00d001065038046520303d40504155461954244c0310f00b1600d410640940d5000e2010a603101021721032600208503100d9420030524080c03070980e05240300003414074800c04102324040c0c65111003c0d1500079596600422315066048070061802480c080c01c401342d90500005000300d04401e0105010044038441e004858441d51039a901c3d000030b200407144040144d122308450201241c0100c424810039004a04800c0f003c6220b40100b58403070803211204070001042c0f00100003c00c011582c0c1c0c014803240028040c1181031162402d8242c01d0244409400c01001060032581c070360001100030010007580045 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 200316106 1250 200314856 200314867
    0x30b03030c1f150305060f060d0c290a211d0f4b010228020a081818151504150c06021c060f051504031e0602 48
    0x40c02c0c42030040c0c10040354440c1008006030092222056107001c0d80d07801070180c031540d6600c2070000c0c15004000c1c0195803003034111803044085241054a20050884210645903400000784081040b1a00140c2501000d408200040280303502c0341100385040704a0030382411404042081c440a06940d0300c0d000c003150684d41c840c4460090003d031401e01200220217880180c81c034080d180d207080380907140c1c0c45503081c0707034040039100400e021121760f180050400c05041d40f90fa103441c4050898101e65030843d2655403400644001c0000303881e808101900901c02071011404903510a0214041e0540d000c2240c035100c034400503542d51b0345403003504e6070002c00d16542d011301d409098002e407280940c003914005c0d0b0007200704400303c0c10340f4800c5074290382828181e2100c03848804800ca90040c0d005c601520344035428000c0282d20302801c1c44007086041d45810219199050100741c610394100c5902151241e0342216a80c60300e03101d0301c3d05a030104c1ea0404d5810034941c450841d00400300141400050183d48005603 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 200317356 1250 200316106 200316133
    0xd030c05160b071505060904080f1c02030601030506030706090b0c07050d0f0303050c03010b0307050702031204120b0108011b051b01020f030103110301151202040f0e0c100519030b03030c 82
    0x1401441e8084c03100c840002840c800c4d40d8003211004d440054200810000040216004000411a4070340c11038245141204005008125281103401007050036000010301000d581d0502645030011412000f41500c0f0346002c101502129040c403503044200408528181d01c11024800c0038002c280250030110008601c0c681601484c400240440200e403500700440c1e1418254002d03641030b28a484142442c40c0c60740d0310b041d121134000d101c0490b458030820b1808840c02c0d2407003024000900c004410b0041032602490210070f8104143c20640c0301e40c1c54250f0362030907189940701c02111b129003410b100741d980b00c009503090b10200714260060010f60000406859265540e0300460480b0b02408074014158101000c040c281c1d165420002c0c1480c07120700c4148040120140310444942c4004c000246107000b2522034816500303909510041a0003c003200340305800d005030544010681440c11074a00b0495558140d1100800c0e42c03c8000c0668079a0070700e25540f01001202c3c00ba004505c00c07202c00d5100d282 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 200318606 1250 200317356 200317379
    0x6031205031b030115080603011d061005031902010818030403050706030b01020c010801090c0e03060a0c200a0f08120a0c110d09030605060411030403020c010201050f0103020d030c0516 81
    0xe40c2d001d121446030403101408840c1c20b054038144d40c03072401c402c18104140d42c1d0881d05404007408807580355580d503c8024425200411411340680300c00b01508083c5090808000810003d5010f1380c040c2d046500c1800080900d07900ea006c0c07450382400c0020298651004581420174a00e81056042c072000401201f4020005289006c0324850359003070001001c40f800485c5c4442c40282d405010a10480c014802c1c41015080344100022074901241101c0120380007034941501903900c412455500d103c41d46055078440c010039400c003034010b041d04003083c20840c00755540542c1d00700a44291a20b002d14000c02c1020340031a40020417141034540b107418440050030003001091064401b1680802c00c50313046c250b000c0340c106100e40f015116401c0380307490b41d211000540750003030a41d44c0c0716555600318590b184402010b580190f020740e0003000c2c454005400a400c5903c098001c00c2300200610040005a40340c4d007030b10700c64903407501d40001d014a15140c4540f83c14500d101072015800360443c0401c6980000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 200319856 1250 200318606 200318611
    0x160303021c0e1207081c0e0703080c060c0c06070c0204090606060e0a09060b04050d021c0c031e0206030c0a0c120e130e0604020121020d0b0f0406050f01120603120503 73
    0x90701a0f50f0b20194041007081144a80c40009003040400d00030850b015081c8600c90200612040c40485c0810600c1241400c01c29640c000f15180c40c0003285903c0c9400003003002a81c44111101154946403026001d0f03507440b44020301003020040d01005d40b40841d2602e402003a0820351183c42401025141d40004e07020070480282c850280d030200b00005034202d05400b64900f114610f4007031610b0a824241070217a0540c5085090340c00103400011661a180780d1285403001c41c2c09140d01c0c56445046240060f6000c80200841003502c954200140c05603445408880c0c20800e070903078556407611004000d8805071102c81000e89210b440c4e0481e04000380c3c0041c142e00d00300d03004840030b941080d03240c0385100458405070301840d40c503800000020300550055a10ba0055035890b015940c85541c041034560a82e8170102c50802d00d41d03140d00204015040400100441170b50440d01405510304100104090810b8004a58108124916600702041d426031081d8040d41d00a004c1c080154070086010f0481e0340706 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 200321106 1250 200319856 200319881
    0x1506090d08040914160c0b070e06130303080106021c080f150a030c06020114010e1803041e031203020a0f0305060406030b090a030801060c0308010b0f1b0c09011208160303021c 77
    0x3503030048099a881540008030203641f101d121022601e941004035400000181013641001c2d04200003c1c19004241d00000218800c3d982d0707004a43c1400320080c01c2a4503107005a541c00510381320009095040440a58000e40d1601c5410785030341ea6140e0304144071140c018550300468070000200501c84440707284030548110340c00900c240011a0300741c0341481c5003440751003448841c200100e00d04882c10a506a54035200e038003101d09083c0c80d481c0e00148032004c940e5500d00104070702c3c0c0c2041000220210b2960101003400c0850038029040300c05020400c40c898148201a03842000404a03680c0c1d0344050003071500308100d50001d151241500384c2d0b610904c0d106901084400d00000f0308588182c5074250070950580e1740804591a0001c0c0314220b411000000c02d4100040c08040f0400b6400b10011840c0301c0200d00400000301902c0c24041005010780003d04952003043c620070101c3d0743c0c0c80840385d0040304401c101c503825015050440007805450f4002d0740d2020100e6030324035450082d41100342201d40 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 200322356 1250 200321106 200321131
    0x3060d0602160b280209010c050601121a0103080d050a06081005040c0f0308180406030b130204110405210a0f0b01030b010506090d03080402121204030b1506090d08040914 75
    0x20b604d40089101013449642518542c4019000342003c3c109401401c0c002006050921191081f90380c0c2c1c506040c4240c12402c10394504402c5101405441d001e000030500105410254950450700d5403542440380ca600389440c1510ba601081e1030250030b503c084003d02c8050103030340d049000280360300e019042c02d8900f44c130341041e101c1020826019007451134080380e6004c80d016290564074281c0504030b14502402e03a621594540001010680c18000c00780b05a80310003441ca4410110710402023190101190000c00c240140000d0041d03403100e42c0340e80340b8804408d12102184501512003031404828020081c0310f0303001c034034500e0200711110039114141e80c495510811141e80320014440349014a989aa910441002203400400e004030b00081e0001c0c000340c89003070800303420780300180707805c18034050011090f400040400174080134a4030650050315400520024429070800150380b40507011125118a891500990402c00c06104540c01005035203000d00800080c02c080c071001c4075044401c00105030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 200323606 1250 200322356 200322361
    0x80115050102102706020c031605101a0120160512030a08040201120e070305030c010b0a0305062806080706110c09180a0b04080d06080303040f030503060d0602160b 72
    0x11035400b4031411020000d203550313040b4207242c0c003003180144046403e0320019800c004208001009000034680b0b0b101c05648004910f180f031401c0c41c58100300a141c84c210300d15080345540743e4014136103540540304003440c101c59950000b84c5412128803d00d0340200c0d5610617090021030035108140660304958080700d404002c070501010030741c2c89214070f40c0e40c900083d41c06c2d0002001036000740141c0d220b5101c0544005156510001d42c149024041d0708150303080c1d4400b10342c1d008442c00c00d0040e4004a18241c03140c03003440d07280d0f030b8420399592409030685520310412404980f001c0300d210500d45009072034410074020b80e595501010303110440d40c00358a000500032681c40e10444000a80400e029001074212140c56413004004040e5002c1c074a1440881e02a22070000041800311502d24003990080403981c1da24030940417110102c0f619588140c0c803d800600401021403610072444001580500f0702e01d07520303035034880003400d080d840182c010728007440402c140a05109014031a240b50b403059a5800598 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 200324856 1250 200323606 200323633
    0x10e0106110a05150403050f0304030306030615060806150c0616091505090d0303020d0f02040e01090504120e01090e01090504060e030f0915070c170c1507030315080115050102 77
    0x8003800d80b00601680c0c04000407030b4203228030849507548a4020301d000c90804081400086042d0320030b88041c0c0010703448480500512500344504402c0c55440c00714180c07054030301400505880310003483e040c40350000300056a2440e0344401101e280c0c000c00bc054440c249450b02d03400404103a8001c3d81000524004800f040d141d000c1d40d20200c01050741d03114035080c200d641c4200101191100c40c1201007503001e11109404400b45c0c005e045094810348400340e1240e040c40152084c00c001684408001424202071001040c985010501980b180e45803150f40b0101e4400166a041100e038040c0000c070242d8400011584400d80c00340d0700540c816001800241c0d46006410350700c0c06211072158543c04104007000591404039140c0c0ca0f00484541101c0c14506a500c0b5400c44a000b98000380e42c0400840c1304102d40311052151020808040f6903501030894200a001194020200010180342e0365a40102d818145808804000d024aa009001080c00d54481c00d500041b20300c034842c00740c410688000f041 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 200326106 1250 200324856 200324863
    0xc0515011208030702011d030d0b0d02010f050d020405030d121b02100e0114091f02120103080702010318050708011d060f0c070c0305060f0a090b04020f030c09010e010611 75
    0x490300c02008a207680807441d200c028803a030000d00500c05640d0b94003000c044041c1214010304900c01d480c0301860701c403520071103604191030305042076620070002e070306450005030780041801d071003600d140c41c10603260701d40c8064000092250303400c01d540c50312a000304020302aa101101484040c00c0c0242405920210210030a000d2100c102d0314001d41c0198103640d550b0600307a8440c811031a1884000f1a401c19000034403814800c09584144842d0880192040f584d010b04400c140801407010301145425505090b034170030140103000042582e0000203010045d0ba1094000e00d41e89201c800034990540e090b0b00d07149035200c07910700c110641b95080c03549100300e010b540328495160000030405880e1958968101c980d03140790080c211801c0e00001c0c814680807409421500c0042e41c420401071440381801009249003c400406c0400010b04100146000440402d200d50308254180c0d5402829201c15000234104200078001c80d8103d07110000004a481120b12514100e40031030316510450703010402030540707 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 200327356 1250 200326106 200326109
    0x103060b121b0f01180e0619150f0309120903050705010302160f030315060201050a2711030c0607050127030504030b060105040905010620030c0d030f0209040501060c051501 76
    0x30500c002800d040031a0404803070384801100c052410300d002c1c581011607401883c203190001c404054900081082e1401d0264000c0c2460317a50385a103030b00301843c040414081400f64400800ac005074058121b10160287e044146a160320280c045403103100110000d10400041c0f0094031719100340a0001195401f03032089600c142c64814101030414215280c0b02c1c4002030011049080594400711380c00241c85480440005d00b10b50750000c662410602145c0b8251242040c000301c0b44030360000720350711131440203109108903a031040c7c480c0c01c1ca04003040000d040c252943ca10a411040009520341003010642c0b00400b070b140560b11042c84d25201c4e403c044201510400001e000c10303010001031010461001d900f41d0311080c145402443d040e16401c400c41618000c0e8010400704e03a6209800002c0a1103070007440c1681c064100035402c001c1602c414aa031040b0b050b40103c01d01d44d440c200074902d80b003103404540c0314407005001400f084d42c0d1000e0041030417a501c181036620f809401e800765460075890921a0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 200328606 1250 200327356 200327383
    0xb0112060f0e0c04021c0c08090127020d1401020c01020403030306080307020109180b0d060b010806151806090409080a0801120c0302010f020f0a051e01020715230103060b12 76
    0x409043d45020b1100941c003c9401e20042144180b001d0005d000d14003c0300da10700010b0b0781da01d109042a0794205e09641d410003c1d044006184440420503047c02d52481100c0d40d0110346580070382c0d4040c10111614084000d43c80e0b022b50000a00030341d101c0c8150002d1003143d1007503904129460756203003269141c1c0100b000007400904140c0e81049284031a084905d603803607c00d440011015403900c00201000c0200344101ca0050310b07400c20900d59a0014400c2c0d502c600150380902d0b00030452105a91103202d4100d240c00620520f160300c240340c0e00c0d0601900c9020700080c0c420041c10005040036001c6400c0001810000342c1003100100b2003000d9170f64030301044d9910414000c0120b00756801550f085c258a0b4612003103100307441800c904207004106070b04140c1e0040010f002d402c1002503286188803503408070894160b004104440c0010701031140d0f84c021101014002403402954030306080307220801e50444c5404001d6000200c24050158060451000102c0e0324210301c82c428154140c07160703411a00007 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 200329856 1250 200328606 200328613
    0x41e1b0b0c0606010c03180e150103050610051303240b220b0612100e010803070c05191d0109060611060703110f040b09040507050c0d0e030a0b0112060f0e 68
    0x240702d035401180a02c0e000c0c0e11034240103030011503107042d87c000343c489035000504020803402400300c61802c01d64808290b040070310382406949060300125a02140903480d80e030400c10002010600441010301500c091503002000000c4401c000300900212181813000002482c40c2001e920f000b403401b50381585555103640410111494101108001800c004071030070740003c0b042003005602e8920740c2c8094031855503510341c6107105041c042a60740f5034105070041110380d44200701c0c1102013020380003280b040b24000c031079040601c07072044070001c07010f004c43d0300000c2b80e1040c0d80d44403282880a80000c81c1030b905250020045203036106402c03261702040644441240e0480d80124a50741d1007900807100994800003094a4028000c04106840d8440d600180682e00041604042c610b0305000e026001003051906d1421300403116070343c1761a10004800360080c0440741aa0000585040c00441513041e040008000d10350b85d9011004a42c920108084851b0752500d207040d040bc2c01d1074405e48070342c41603e02c0107 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 200331106 1250 200329856 200329861
    0x60406180507030b1b030703091202010b0a09020d09081216081e07020115060c02030106050427060e011d0d1107050118030f060b0108090609060f041e1b0b0c06 70
    0x4c003078200c0006066000100d01c01a0102031007142c520096004440d150303000a00c000103802d085108410702103540c021a41087d0254210343d0f034050414040d41c2c0002c40069441451580700c800070400104000d1501002084400b020070307518000c44e1096030050791403884041c008004940d40241110000c00d0004400144100340141c40407a550088442c0000620484450b0b0511501c41c0203500c414005001e082000007107080038050140201b0040c0e40074894040e40c2c240c1608440030680901c0d184510315a9220184030b8a908000d09011201000704805024002c1c0f2040758209150b0040091044540320a070741c0e071103151501c5600000c2009882c0541c184801100d0108010110050264400e41c01102183c07540c0c034585440786c811680014240382c040b0015103e03200040c0820956040b081c200034100802003420360b84200600040c010344e030307034600d005e01d80c00081202104100320000070050800440490050b5140c1901386084503041d82d5076000710651103420150201a04400007 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 200332356 1250 200331106 200331113
    0x50a120506011137050705040902011206030602090a060c031215170309030c0303040f03060c030e01021215060a0c0b100b181014070b0c13030506040618050703 70
    0x1580c010030145054400060201951894410101e4130640c0c090040c00540c041071390501c12400c54100c840c52119a501003a8075641c3e120f5034144501401241c503031104004582c030641240740d520080c032404105554581c01c0c041c000b9080b004800303000300340c013030804600f2a00410343d041d001d607070641d50410300300c00e4041100054012120210440b8510800c08074407295202260f0400143c24801540c64203412002c15281c01703410001c05001c2d4004200c14811200e0191105090740c0d000350780856003800ca13410440c02132058640540300c5510100b52400c01e000c00c0b0040038010700000b0304030501601e03503808200a038403840101c40c01054250711b01000145480620303991100b0495080c030282a6294504046030748268484013500062504280c4c1d2490009140068014986000b0030711048103000008681300b100c03c05090940c5c4000011042045c413021903015500c2d15018405031944c03032422a0717039000d0036241143c81034100072950030607040702452400001d400074000d024a41c65500c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 200333606 1250 200332356 200332361
    0x160506030a0f0605040e0303040c06082707090212041a0633210901020a09090b1203040b180904030801062d05070b10150509061e070c06050a12 63
    0x10b1501503551150b60028041ea0b551182c2074803d905007010310341d00e1520f442c00407100c00d0143c200d10300703000030031041c032003100c034004a0480399659203188500700e5401c1380f005924005c01503026510b42c0f0300000342d180d46085c180800a0007244036950703080701d40a0b001280311540000300e5846812000c25960b03803000008101c91490702d031058210f0281200c80075030310001260300025248455458400030583c0d485100c07032801d5403010040c0021810724800d818010b140c08258803800040503140c0c1c4000704a86d80e02d82a1454803e10001129501c582e40c0f0704403008c540200101c10f06040040f481880c0720705111a1340c5104643c55a140d201c0f5a007450f106031514040d40c4503603444601c840c1081d03414404407402d42c402d241d80645820f6220f8100c2d1038104d5a03014000d00d00c240180c41d03050100011506441300014803540c5040c41e94075071a481000c40c0035401250b2803000480c03a244c00c00b4403062a814024544503000380240c0d0001501c0d140c059500c0e02c18900244005698660600d04058555 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 200334856 1250 200333606 200333621
    0x1305030718200919050a0b07120c030c06090819081902041a03070507061811030a02011409010c0c0e04050114130201050f04030501090b0f1f030213110301090c02160506030a 76
    0x1500142c003c6a05c400210703c6542e20b81d04254510303034000811005008000c410304400f4841460031b00400c040540c6c0c0100381240900c0d0003403d56885510b070313608214503d030640e070594600c1480345075400390352407000340701c500f054032445c4040d07644c00702c05074424030035008a400784ca5220a0156000f5100104016103a0000b02007408020042c0038040c0021020302a4216070824040b0f140c0d10203802d0b052000105001c4d0842c1d6210350f000b04061030051360441450107001e8180744920b91140700050060f10350307040100008204040c6201d000c42c0f4004065541809280110001c1003c110140c039918403002060307079841d0703070094503100c0324005621a400509400c886020824109035503907803103a003900c03201102201c40e400540c080011801150144c50f034000b01811000e4040212901e4002c2c0c110500d000c00b0303020f284580c026580d403202d5500009500185400c0040e525a510481000140100d6180c03800500a184003e0041680090301c1025039000504485c61621a040c0b414006c0091 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 200336106 1250 200334856 200334889
    0x3110103020408070b0702010e0105040e0a09020609030f061e0c12060f04020a03020a080a27060209031c080702070e0117010b0415030605010b0a080c13050307182009 73
    0x308008520f6400a001500c020241920100c0d210304491001600110030400c0e150b04111040c482000102080c41c0c000360410b0060710f000079038003d1800812824800c503d40e19030540700c0c890304540350b003900013415449441300060f91586156846140d000e0210240ea1912401c1d50501c0307044490800c450317071250410390040070502000301da8400300f02641c2040399488040799000c2040300c24150032061040d0f114480c45c90400c04d0911154032203040c11004c4a8a845c400090b8098104200540d811142d40010040440d000485210b052003030340000e03d400100020819408078840a000058070810390707480140d16541607013031051074595080d90500c20390480d900d5200301d600b291502d01c1000d4074107540d03c800c1440c1c81c0c02e40c280207040d6001a80882e100c614200305808810303601000440c0c04c054060417041c1d507403e0100e03840c091107000d0b4006030761500a03c40300044207480202d450302d00351002d040601045880c0c0d04c2d40e421640d032041500e5010f81080201a140703142406040240200 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 200337356 1250 200336106 200336111
    0x2030c03041e0f030e0907030b011b060204120506090d1106010b0d2009040c0509060a08090304030501110a08060d0203060105061b03030901020403050609060c070b070507050d1808030408060103110103 88
    0xc10303102d80684007454841640498034480d00c405d40c500780400c0c0294012884c1c1000d0001c5203502000910040990180316001d00311010002c0410060303804407402001c4c20010802880345600381551184015613840026101e50142e105405005000b80b40e01c0007090360181425038681152080b0306d92040c5003410b499a511200c420812115000814440c3d44210100d44c480e0051014403040f504541009018480d05002d202c000e40c0c4e135031003201c2207210f0910f45082c10fa201c0d00c1080c0d145001d540c200038025400e040c440c98801c1d80b0300c00546056844c82e0340b4940542c40302760030b002c2d030f20184010117034040e0000c8005210b2410188000c1018400408505800203100d41c0d1084c2190401e8500c0210307650000b604105000e1700b04586d5803c0340b11000504014101068a56964843c25800421202204001076200c0e0f004074240d45c103403034000058544030540b0000050407602c0c089507000d0103004280d804620030200205550070380c0c0c00320004150716425921940c0541ca0342560b440e04040c0c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 200338606 1250 200337356 200337413
    0x80a03020a03092306090a0803010b0a200a0204050c0a020c1e0d03120c02070608071202070b07050c0616021509010e0a0507090b0405060a05040e0709052802030c0304 73
    0x44e14062905a13090000c198440f41d0007088a52034140b61014100c01440e5201c2e2180402143e403040880781104d60700c501169840f9440d003006e1b40d07400c1d85040072000a041c815685000c9201c00314800d07501610894081101e60744007130b41d411803070082a083d00010307400124035040c0343c248034821091a42d8620324402d890301d121070019190021070401140014034013444031241d40308a0081e80040f074090b00140c03d0041c1409801084508028140d0303017009003002c1c0c1150418455811100c407160480c25590305460444009002540046a02e51a0388500b07030004444903030120700207070441d070b50b41c2c050080e0300210801d5204501c00030340b1642165503215407003d10100200880d03c0d0381761044019021092410340300d6022291080c40c020702070b5041c501009003590b0303500032082c00d0314422900022072032080c408541c0380151039006590214680001d02440440c03520495032441c60130742844250b140c0c0b000b2502c00360701003612054492142031021400248180b49903881e1281846a906d440070f = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 200339856 1250 200338606 200338613
    0x82506120f0c0e010809010203060d03120f110714010608030d0e010e06090d0801080f03070b040501201306050403021c1a0f040204050105060c0604030f2f060112080a03020a0309 78
    0x180d42d2041d0400225850b0481000996002051640d0248504000b10304610b002c4e00407941c032641900c0700404000d006c1e01404207041d80340d4855406200d80c40410019034000c40028545580500001c0c5ca1151324a8221551290b050240000303441440010314149040c0c1306100015010840c51403115548681010704030310f01c200441c0c0d100398240d030002d2440c40f01525000d4224203041c1c0015919130446054000c407440000704079480c10345c1c01802c803811070b52242025030043c5002520b02070f20039501c881d4450713502804800f504600204021038130100d03668100581301c40c865880020340201556680701e0707889c02182c0103030a21501942001217030300c035142c824003103410080b607080c408480e07032500740b005604091041502600c029202c25160503802003010b50790350f000400080401560300c814186861085d46d481c9200f1034070160001d8a00d80b820b600304d802c0440d00010f03030034511522000080d003c284812001643d88c00241643c41d00d00011b0080300603511000d1660107058039983c505000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 200341106 1250 200339856 200339861
    0x3010905010f0b1c0c050607031e1709010b0a0311060705030f0319050f18010605030706020609010c1b0b071403150a0b03160c020f1504082506120f 65
    0x1000740300140090080d0615040011031320600812005503000b0004038400a00c10748000402e07103200b11240b03030b250b1100f460b0855048010058440140d1441011300e21100d40103032580e264081031148583c40b035070310b02020f50708803803403a000f01c3c1c0d210100d05020030101d440224a81c10789900a800c00e850312078076403a000c2ca50b9111041c209122100041000005520600d03400d14800c2c000409110904000d08c215110500107449011382c0c0c40248100c1e019407109610000083c200502030310080c9680c1d1070302a44412003126903004070b50030400300510241c402d02003459142840582182048680e40310805202c00080c0740c41c0038440009010201107443d04085c521650f1000307140401744001074240f120780c41450384142c1d03042a040c014040408210424100103981c03c1c58100720f03c01650000411011065080e01d8200c2d0b00701c0c20792685611068000d20966601404441449400c059007000c1300000b4140041c0c034100d129000d1041e10300c94a0080040003840501148907581096081c04 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 200342356 1250 200341106 200341121
    0x20d0602030132060f030a1b020a1103060c0703140903120c0c0f011202071a0a150602120a0e0d050d080709120c0509040213060807050a05090714090301090501 70
    0x1600184a00326010100c448010550088600030300c60003c001020007040c84da0213440c0440d00c0706240030002520000959026031503001142c490a58078400c51200a5143c0490f4581500c0d180c100c03102d681c0460600168040c0100303009100d081c03401400751004c94490320b82400f41c00c0c0c00351007003008514590301041660143c402001145035601041c6201524201e08000d040e4041d58881c8040303103050fa08807804020810300404056980c20361451710800000709c0701c4550803c00d4000007403060708003481d4032910344150a840ba140480d40c0760f0720161303650200040203000c0f0030340810404410612a10080e402c50001034214034440c9010368aa5042880b5118044005400c090410580070b40c080261402030140800742d5608240d1516007916007840d90041c41e0141c13941d1004101152180442e41c1e50402003035908001c5641c513800c9240d1622090311039588076a4051101281c3c07841c00c41401c80c080d00c4240c64a02c0e5007200c04280354040c0e0060b40d081ca605541e03404100010903802e005406 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 200343606 1250 200342356 200342369
    0xd020a050f06070b0907061119200303071103011d030304110411030412030b12071a0906031003030305010b0f07022107060302030a150302031b13090302030703140c0705010c020d06020301 82
    0x1b00f55810101d000b80200503821101280d90310003075a403614091003011580c0780b260800007001e08480200f20440844e00f40b03000480d014400041c03083d080c0300007100486d0341540301b10020312100e80e08030748072110424001801c100700e4000b0404a0300165034941030305083d200c040e202051221801043c01c10f00c1c3c00440341540c1c0d09e8500701002200c56407500c1079042081c1c0c1200c1e03007a44811021003090740d5007504c1c00780f10502d41001c0e0148071400b000c1403e540d16000f0041040c1c0c2e0740e140c030b100d000540328910700c4110f003c07d08050002c1000e60300e2409582c810442109203a042c0398903034013000a070503590040c0c00c9030b0700e1a07248180f040d454244400da000e005913031000360303882c00c2046000003140c4c02e0503511455030761140c40500c01a0303800304a00000b806003022041000f044100020a400d03103020f140c1003402d00d401014810140c000c0f003c1c1091174025100c00c681e460303540c170020855224100703051110303403c8104144079942c000d01926440c80d0020302900c200c4010f80e9a41e0007244d00a82050 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 200344856 1250 200343606 200343613
    0x3030902030105011e030b1e0c0406080a0504030815012a0506180703170c0709230108030910050c03070b0f09030403051c0512040b0a06050d020a050f06070b09 70
    0x41040d03040900410340140001c507601c503061000c060080454000c82c3c0401084000e5400105041680000b800040f41c0c908580504407810302d1045410541c0c4903126600200360410f000502d00c2e40300e441580c2c8100c1d0191110903880e90751181814548112210280c18048503810030341100c40100c1400c80840c400c01c000042d050894104507240400052102c4011260407140304840d00c0e0104034001280d43c070580402106403020019030039400741c11003000442c81110b600180380700540d04600b11404000030240744e04d031214042d02c20b00690074011a5208d5000700b10070070190601c10350f044890700c40307490802d007410340b00b007849415a44401401c0c0c444003011030901030480111036683c1e81020040d0021490185140c0c2e03280d845030281e8084100c006c201d40c1884001d40c2c0508201c810781c0f00c84401030354841c54149440c0c03041c80320541c0d0305140c49203403480104960400d00b040034074107500207102100c5540b400007040548011607a24507000076043c0590000641e030903106502034240303840174 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 200346106 1250 200344856 200344871
    0xc100c1d1f0305090f030a0305010608060303180906150d020301050103060b0a171521190c0504020d0204030f0507090f0216141e0105090c0909121e03040303 69
    0x419451032031144158410003940080c41400041800740114684240c2400305003a0303103840c00320703040000d00c0010a0303160100103903035442d5950540c8054141c5040b9140c4819030b4540038141903070307400707040e01c0740b21140c3c100054881c4a00d481c0701d500754014801003003201205504024082640c1008040c101e2507600400144210340e058000c1501500880380c2c3d10341068040c09000b00241444021120241401e40104407a5404803d600c0c409140180c5041510000807182450b0000058011205c50082e102e035140c83c4154080311100140c1c0021420020504110400000b503101d449040b0b00664204400030014003800001241680220082c0014520700314101e8107940510b01000b00ca18410400303440f001054800701c1a9290304072914503020040014154030340300c0581d1040d07108806144044201e100150481842070a410b400e0394810801d01090000b881004e9400c440c441e00201c80c0b02c0002a4070902404d00030700700d15070f25003541340d100070401c909500a5905a00098842c43c8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 200347356 1250 200346106 200346137
    0x5030a05100f0f1809260f030702060703060e0c270d050703060b0a0e070305070c050601080c0307050406080d0f034a120a020709050c09090f0601050904020c100c 71
    0x307000c450700d404c1200a00c0414100d0380c91407a00c101d4441016451074500400901540b201c605950454035a002484d03940e003411070029548034011100c050020f400c6c2000459038921411044c1e00450080c06c6082c14424000003100c011034621007024804103941903001821b580c2c05940610300c0d8000c1c8040c007186030070350900c8819140b140f40c4040c0600d440d12401c12080340c41d50f02107503000070305150000343c5850780441110f1205a03507002030042d1150b1400400c4a003000301c3c03503049400c001c80c00c490146a0702c800740000c0d60340f9442a460142c1200b140c040050f40110a400c00545907490700050041810300c0d0008840c0c22141205188040b80342090701d035002c200800c10340c451020348904007031000e52003181d6035003604001224a51902241c0c40c1c1c025070082013240003518404400344054038000c0058051f941050321814840c1d140300000c0f50420a56002c000d01400060b543c25141824200c00c0c000650b200902c4880f4a100d503222082c5107d0031446481200302da15134425103044500309 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 200348606 1250 200347356 200347379
    0x8040309080f0c0103020708090d080c0106211b03060501080601090606020f12131220100e090c1209100605030706051b0705062b0c05030a05100f0f 65
    0x4100525550002d4540e00d042c01001584891611091130050b945448500d07059140d802400d5400c1d0300420000848001c004562014200c8503280c01c0c000c019903503a84d901c140c0c001e4140d15040c1030b0340030300300741c03070780111300d100c0384001500e0008443c0e40481caa8079500d050880b1000d900884043d008040103100b48a10cd018020003420a4402005c111040040c142d07220803c40145103103c44002814901d043d004841c0100100825407103441d0ba03800d41c1c10028824a483c98000c54504c00380c540190715450000d05170302ea2000b03143d496014015001050180f400c4020345840d43c0a030b8180040600102da0201c0c2501c42d00d00384c03000c0c1290500005240c015030b1290f0b04103a1080c2c000e40c00074010664002c069074881340c1c048e10b0202d240035075060401c1c00c042058000a0b040f500c0003404c036201c8400c0d000e00c098002640701da480040071211030340038100d8001400c00e80c00240100007089100c842c075080550805180b50710401601c3d03941600a580001c194400d0317851420200c0d0400171900b010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 200349856 1250 200348606 200348609
    0x901050f04030f18090903030b0f010915050c1f09050c100e091b0406020313081f24060e09150904020d0804030b040809040b0103060605030a021b06010608040309 71
    0x4094200d49810701e554003401c0009100072000400150a03441c150315804076080c3c100410b00b44504110840e82410000c020f426410925405204545100d503181d5108455400841d00186848495681e500c3c108403260760100c02c0c010b02c2841092102e5244009043e404482614050340c0040e918080f072034800d0900b40348140d003600c42c25914a109604580118103d9040c2800302c802c2051a0b803004a03000c4040c0305201c00038401c0f01c0101c2c010404580010040580c004050091041c1a598290340c0d955104810804807044003821103085800f83d09400240c0210300318015403203c0d400c290302040985039a03500460004d402182d9030211070510000c5c3d282c002e500386c55090411610346002c03c9190700b002c2d000070b020b031418102100c00d0040d80001c2c0e40c091980461000b02a062504002d40c250b0000b00c0a144240d24000311621558001c1c41410211200c980707070242166962079070203000b50030105816803800c800c40b1440400150074441c017130103004251100d07009810f160400400021a6 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 200351106 1250 200349856 200349871
    0xe09130614071e0c0506010e10080307110d060209100f031401080a0224190f180509180a0503180a180c030b19030212010207030525020d030503090105 66
    0x2541030260865000001c80c02400101e864404480c1c0d0b0f400080b00c0001034031a02030124040c943c0041040c05c070b8040554022258581c1c1281c2c4152610102c41e02c903ca0910300030482c68001030b0100f21400d080054210003805840c0042c209000d40c0040780303413021041d07002d100184602c00102d0840d0b405100c0c1c0c00303040c1e02c0004c03008601c0d810030480640d10f038048100a44135187e00c8910040c1c00200342c1c1a03100012000c8005c6460700192100c0c01a01420150326030701040311030340c80c140c2032807242511684a03451403144040c00381ca00f1062102032a00076203880082500c0d0a84200303500410458040100d102e0310003551745056100c018854070a4400d80c4078403c02034403000b007000800500c01250340a620040000c1c00305030380c0390b0a41c010f1600703251b042e40044028501603288485c030044c00046a00a4034240c9900c0c900110440c201d00c07809000030080760301400000481402c2ca03c003074950310f80c02d000b079a007079488a07000217259800b41c2e402140001c20000170003008038004e02856800188 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 200352356 1250 200351106 200351141
    0x1f0b06070c0f120f1e0813030b1b120603030d0e060f0c0a17060109051e030601060806010c1103010b06030408191d0d0609080d0f0b030304031a070e091306 68
    0x110b50b56100a0720070040030180060800c41c1131748480c0861194500d00e0303103902c000300590b42d409010386030022440e148420ba8443e040c0500040132000b601902555050b8440c2d100c85c60700c070642e218012130113406444590940f0091002c00c030401150b10801c241501400000c005510301100c0031140a60010040400c20505001c80311030307550840343e0410900e1180c03050092680c1c0d8200126045000c0ea8049540a20f140c00101100980494000c9441c00c041e03059071180da803200001e0b944680161151800100a2020000070030244502c00c41c01d11402400030030891801070001d030158109480940d03490b8000034040d958450003501c100c1031441c45041000c9401800715034203404585454155026981c4041c040c0c08104031030344000343c907980c04a03555846404c0100c0c42030041290354454400345242c200700c031203640f60010503241240d5218001003404e036620009503400403c0070b0b11107018440b2828403601940c0e01e031150f079417043c40328568a81d0a9200c0707050440c06d032102c1903081c040080 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 200353606 1250 200352356 200352389
    0x90507030b010f0521060f041a0c09030d03150b070302070905090d11060f0402060702031f0c020f0c0a05040917181017010b0a020a020301090b180304081f0b06070c0f 73
    0x1700401c2580e400000000140c1065031035007418104c0520340a00d4040c44c1085030200140c6040e402d001d0300c2801c40640850305032a030605e400358211140c60368203d000300a440c8080000415203001045418070034419900b18960303c0c1040f5050f20703015600301400f60424044c0c01d81e11a031101c49481c030800b8410041c0041d0901c004100e0f1034000240019009200005414081d0b48080240e0103407103104022804009040340880030060040611103c0180989540107005140024240001c1c61009010303608452030003007080300402c1210b008030744454060030710921152442c0060400503c040c400504882e41440400204503042440c94041c4044414070a00012a640302d1030305403a004006160b0364110303078905038a0000000c900a60544c2032038000c10030088402000381c001c150f50038044080c9181440c103a0780300c0c019405101c009a00c006500d2407a40b049595071f43c00e110b900c003030000d540001003000c940641d118030019600d00b051070800308000c89090070000010301c04048003640c03d2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 200354856 1250 200353606 200353669
    0x9090c3b151f03020307030204150806010e12060606131208091003060806060f0a09020a09080f0d020307060c260415020f040b0309030d090f030314060112090507030b010f05 76
    0x190030703590b0701c80e04050303011000810b440c1c0250304581c0170307104440d50304c0c00301c0c19800340040c91584211180c600040d0018030081046c100088002c0c242d00c02d05000d000555105024050b05070008482500281c036403220005680d03900507130717401c1d10307602039407405a0340c400301024414601d00400122042500d40402040302c0764011502540000044807644000545040091500300c620b800003070040e4070000301c4001d1190044202c0c0c0880301d02d20195080541540f04070303621082070345403240250708100402400202c0542c0280c0c000701a81c2408000f114180741308003070340d8940903084205c02c40c401052005110700c0002e014402c40301c004040d0f01d08441e810b503110301030103240300751150800084046501c1c80c5050064600a910b081010800400c65042140e040c00c00c210064000c40d00d0303d103101d040030071600083c51003039406840e1558175041c9901020014034174000d007600c490213065404000524040c608030f0003440420000b05d40c2504000800c0074000900d00c904000103620f10000994 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 200356106 1250 200354856 200354899
    0x70305160c0308270f0c060906031f030b070e0f030703120f1209050c090c041a0c010902091006090b12010611100609020a0909090c3b15 60
    0x25103a061a0250490b242d00d1010078181101907074640e00c400c1c503413410620745900060710b50711008411049541c0c2c01e0205003403141c1032003144681d0b50043d400700009124208505130412102602d01070b00006941c0c0c039101d140c1c065034159066000520f40c00a01080d500c0c082c0141c0c2003401040300030700750740c40ca1903035500d280c000100b800c41c081c8039202008150003070048442004401c44803400b40706061403490842c4d152944400503a100300141e50200349450340702c85c291026140815407040b5030f2803007a001001150401090504690340ba120b8120050712910f0000d8011042a80e003a200a810020041d08480e01c581040080903030074049260440007121803281150694104114009038002e0004d00b031901c032509052034241403450014121040340e0003405000c0065403080503042c1c075451a0340644045c44000750108a200800340540080403119402e9281654100c286041d0402103040c01e06080480041c00c80004000f0800208400c1c94000c4038400120b0304040800e9008100040 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 200357356 1250 200356106 200356127
    0xd080f0d1a0d031b050a051e0610051507050d090504050901020715091b0b190c050d030b03100905011a060703080112031b050303160f02030d02030408040e0108030307030516 76
    0xc00501040e54441e03030340b04134240b490b11600041a0342500880c0d04000d503a94180c400f00200891002c5504040543c0c0403c58500a64030803030035007041454601007094603da000006020090308104400000e80100700000c203c40b160744840349074528120410081340e600a01d4801582d00401c08500002c05001d070810f04182d410200040090b01750070100e0354029040c24058100f10642c41c01700c0c00540d101c0151803106d230040f06c0d401a03c0c02d00542104c418140b400001c006912620440b0070084c0030360401024080d02034110341c40200300b034900000750740e020302007541c0c540d5488090602401d00a00700405110090300c00030301d8544541d40040c4403040521404400003181341c0ba15040505c51603a42c80316410f41c00b000c0344241d150342441c684950041d140b5010b820140c2640000f494042c4150402005641d00614140380d00c12454102a5200a00c02c84075034000b00004613108114070017031170207081140011a101c1c500b045003d81103030009012250048013040e0020311980d402824941d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 200358606 1250 200357356 200357363
    0xb0d0507120e12030a0204050402031f0504060e130302120a050d06090b06071401091b140f060414060d0e010203090d05070506040f151a010e0a08070905060d080f0d1a0d 74
    0x113640b42d07100701d089002409a5009140d0160000050040061181642600c04540d0880451503680c0e1402040101c4400c0c0c400e4415119101c000540b801b140704c170001c01c0c0e0324064010303601c041c45424500c01003540b14070b0300d0b07001054005c14240d40c8201d45105400180154110400640240b100000e540e800b401900500f125002043c40a4040f0b0a420024a01e50b01603825101c0170445d091119412000c2c2c041c242c065843c20350401c07500d1424051030403210b003000c0e052501e482d003080446240d25910140094005908002080c2c032900c00e48130b00d0002d1000c0c41c1c001030722400d01c009243e0500884220107000c02806019035030100301d0109800ba04980c2c0001076880d041c420703103130a00c0e44a0800351103045140c60480b552580c0720039900c4101803c0026685c0102110f261420810700d8111409054506d41c0001402e01200501d07522554200000400c01c00c803480c007684d584d0020b644140307894014070740701182c0d50001c0d4141d4040c00b00012400404020807a4281011410601444001a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 200359712 1106 200358606 200358643
    0x60703140c03160e19090213050d2004110d090b07031107060b030a05030703050d0c0306050102060402010f051b0f15040507030f020a0b0d0507120e 65
    0x260b104000c1c01c1c1c01c1007900511400c003200d040060511302500310a000003085141d007044507800004145141025030741e14241c3c6521031184281c0d03840103009911ba0030ba4800007660001408846458903c1c101c40c04400c03000020b00680940c09a1480b5550700007102d005244680d085282440c1c09403074000000c0d103528004508580c480c0003414111101808001c00140980d00180005840101181c0c444081703070303c506095501400007100884c07000a65020340320410300440c0c03440e611504081100c94901b10000c0c0d29544002c00c000d0410031000c17078960045020700e080d108a491000e45d040c4240b90b41032081592140302da801c108541c411401030440003114502c00b684119440809000b03201d1966551200c12014001c0c00c1b41d201502240224008010030045c18408001002c003113a942230007600603088580c5100100d03a100e080c40102d004100000520050303400148164 = true := by decide +kernel

theorem cover : BRFrame.Cov 200179856 200359712 := by
  have h0 := BRFrame.cov_init 200179856
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200179856 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 200179856 ≤ n) (h2 : n < 200359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
