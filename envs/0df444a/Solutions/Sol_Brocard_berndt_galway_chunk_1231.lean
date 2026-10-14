-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1231
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:53:17.463161+00:00
-- url     : https://prove2.me/submissions/a8ce0af8-ec83-4d3d-9b0a-11fc9f5aad6a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 221223021 ≤ n < 221402877 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 221224271 1250 221223021 221223029
    0x3080612060609130305040f08070f0812040308030402120601060e01090602120426060a020904180309090e01020c0105090d080f190209060706020714060a060308030606070809030a0f0507 82
    0x1e0010010080c26440782d07141e490308245000740b400001102820102c4080c0100d8000c42c4403035203403403400240c1110000f080b100f80e4062140d0810002d5482c000e0992b01c0001074402c43d00c00a0600041022511510155600600152250500c074100c2c4120310305000b000d80000000c614800492203080d41e00c203007844090031803030005251060300d155441c04540954442d1225132a031003e8402842c0400c03450f86034070345003c20111021400d00b0300042c4080c0d00103000490050f854404041c100c0c3c4506403036649805e40684030003501030304009500020302403580341795810799000c106100c10f4820034450700b0701c07605072040a0005102400d2004003000300117020303004542261024480101c105503103a21000b5000000161380e4592600030070743ca030203000e5000e00528400311b01042444218a115600c88241805603540f554600301c0f0a01110960300001e05030340310a2000507514100100100801800b40a086040c00342400c0001d10342040351804a0790494802944800c03c0810001d50f03000d4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 221225521 1250 221224271 221224273
    0xa060b04030201090312030603170304050111043203100b0f0409080d0c020721060509010519150902041e080105070e190305070b1b010b06070f080d050403080612 71
    0x10501c0c5400082040c103060001410401110b04052419406a80248025688401042110251001500080d800817070341030b5125401c1600980e0035801ca20101ca003900c44120242000110000324440c4080140040000640940c48218000e603410004212403050b50300c0003080243c0b4240a0185515100000500550410440c0c80c00681000d09490705d003aa521030010b462090788408902c5d108a030350000001191000c0000d4030100c0c441e2040d4040f5010f07541c103000d01e0b240c40442c1400c90380e0407034400d16000704030b042540040300301d85c02c91a00e92012501ca41c2c10302c0d44408801089900960000f171090924040071421060804d140c07800400b001002044540303800300c0c0241c0311011014442d03200381380e00403441e0110f07501c04a401001d950410101c0340110344a0b00c000d100d0760b10101440b00c40c4040e450005e06213407414002c0500c1902e010309442d0500115035a0000811000c0d0000c640c0050284000d06030100c0a20544d4825402035032000e0341030500000f880000c0fa44c1e052030b100b503 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 221226771 1250 221225521 221225527
    0xd0506010807090e07140915062a1204091d070f0e090a08030a0b0d0b0406020c07051c0305030c0403050d17070c0c270510150503010f06050d0204050303030a050a060b 73
    0x811010611b049107400c0095448005a42c0c0b100c5011582c0c0a00c10b4000fa4400c0011a0640f0307002410301170010035000406501c500500141c141961300c14482e8980704085004000038092700302184c000e0600000a03440c0e846200d0300f81065242008003940000c0b07101e5402c01c0b41005083c002095054100701d40001519146080e51520322003440020328171142243c641c2c10304c0c80b15403207410030500540d8120102c20002c0c02c1c6403500740c019500030009800d4a10900c072000c125450079000b90706007040000c1d1990660411340c0d500313561130b8100400c00d41620206001c0007002c5503050003503016203069940c0e444042e90340e101d004202c0700340103480142040401c606400000f98411440420344000c02c00d4030603c1030b00c0d240002064268850204241c0d410300080c0005207500c0d042d00020303510700202d02404004c11150440e0039000911455502c0d8010034010405280144010a4042003c880141ca09521680424599441910130342030702d907075490401031400789510440001c0c01003d424030345 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 221228021 1250 221226771 221226779
    0xa12050111030c040323010f05060405090321090111130603060b0f16020630070206070504090b0a030204051f08030408030d1d060108031b0601060813020d0506010807090e07 76
    0x84180034a00001307106c03c00c450000d505041011141c0b281c0d4440e414002d0211240c40f685400c060141a0b8040380030310309103000320340c9200c00401907031070300c0c0386609031800707102e2100e100d00c000000c02500300c401039542c0d21034403c044035040c4002c0003000030300b441c120201840c21134000c0864a0540c8031074148282809201c03006400030049596184101e00c00f0441004140000fa4403440340e810300c44034949001c801483c101240c5105c0c01119062000b55980b03640c0c0d550000e980310b40d4226840381c0002d00801c81885440819800b05c8664803002d44020401c54403a40800c0440d00180c924482c681170140c0118004200c0885000c09050000061410585800007955403030040d41445501a80c0352090301400300c0141c2c05680d00030114001312152547e451901548079402484096034205500c500c0c80740d81070001410904a507001d80d105501c5550341c1c0d40030318075484d80703030802c0364003126860420021910800415018100c01005420100d1030017a0590450b0181450301415402c801b40c00c05c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 221229271 1250 221228021 221228041
    0x506091b040c12020c07080d0906020105010f0501090b0a0219141c12020f0712050405011206140103050a0e070e090c030703080a08040302030705010608010203010614120103030f0203090a1205011103 87
    0x2102c0980e03010005a10761000b90b04c01da00b03090b4031f60090100c5204040c0700c0341020390b0116090f82284c2c0e454000b00100c0e41c031010180b90b0408240101d40c003040590f0400c0244080c400c00030022843e061050300e40c2e01d00e2900444950b40040301d0180c680d84d99484292140040a020802c107241e29040c407074005107040070024100501005d000003820341e010941c03461030380c11901200d18103641b003680405d1220031a04083c042d60854007800d4002000300d00200000c254a1180105072941d030b002003000c00341c0b010011030180100904402d840c94444001c2c0b40001410080c04001e00b02d4900c2c2c441039403030700d4a000c1d0b1905662241c4c0c0341c40703544170030010401708000d04116941e001302480c250510303503640d04040e4070b1031203002002002036107428800601140198042d41c1a0381d01a0f403000c0221241c000088488d0065448040c4000406401000024041c0d4040703840b1100b180140c034100300c1a80b00080012010b03910044441c82500b840c0c00400c0001c0c8102c080407004445e445095041440303100c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 221230521 1250 221229271 221229287
    0x303051608091f0b03030c030a1803030e060a051c050402010e101b02061201030303050109051b121909050a15090b0c09041401080d021c170604090506091b040c 70
    0x20414030180c0c050842500303e0f40790401100040c014088036562031000d44000c0d074035400241a80005074284020242c81d0503208154021a90540d1b614107800102000304945a4082d0100e071060200402040020030900092407009080050f000100c516081c000034054400b0790b1000c074031620f200150125101d4200b402c844007010721943c2d14281c002e591022078003a110722855007160090f00000081050b505800013816a000301c8000d00c050703200c49600ca04104a40c4096400c41e00081c070500700c02c03640742c8003256800000381c100540c240038000812011118582002c3e10b1507013200c00040148001030ba0707d4440701790100700c02c10800465482d010041030018001035056800020620b291b5500da030880c4d0003400941c19000c0040d6920985540d0383c000800016015008211a04034244081042102c030000203032980860408010490a40003800900490b88035076185502000b2500400c0283d100301c02080c0101010a14000c00328240c0c83e4032154184201d060050b50328100c0c3d0f05c030f181 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 221231771 1250 221230521 221230543
    0x1701240b0d021602061902070506090a0e1005040f02131202060307050307030e060114030d081b1e0412030909051e0a0905060403050904060f080c190f03030305160809 73
    0x700503151101003d80d900c04507007419019600000100345100744861300060302c401003540d038003150b0032642d86005201050042d0ac001c590301007542581000100c00b03481009030712400600110454540f1240040c00b16261801c58030540380e8017142551100e400d0214000190526100400b0350443d01d50002d2220711004220004003d8044040f071440d074042d4109501a01940054802644c0c44020180c6003508243c40d4070711910031040302c000c4650041c60514000c903600c18858035060136003081c01d0f020307a1003464a4008000840422600d06600e82e01070400791242800c484070803111400c3c01000501d4a801c1000503030f280006110140f240150704203406010b444030b9880075554031503102c00404403000c0141507070040504000030194041c00404d102e903000c5030200001d6482d03541181809400f40202da509a2001113400c1c1e05290138211140781d412100b50714000319031680c026800340030b010350048011076101c0c02409146060790180100e01c0c55540307004032030303498862a81580c996031906 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 221233021 1250 221231771 221231797
    0xf090902030318030a0b010b07060b040b030709050709052205010f0f0e0a060312080703051003020114070f051e01110c0606010c050f0307050a0b010602060f040305030a061701240b 79
    0x48101e03c10788003440780580c402c1e004220400a9a03661500d901158001c9008440c401e01c0c01c0c5901e031003407030180306024003900d0250081100e5411301105c40f0081c20050300074004d00c05e541d82c0009180d542c10200d1003942c04d00b1520203040308414403103101a124180c00030100301c40d0104007030043c150b01840c0441207444402520016849600d20140202480c0c2c202500070310511094954081c0c00c00035581c0100d0b00d5607404c101c29500c00c414021740740d41c1400000c2c0001c03071072544150300c08100741c003410895010b0800510003529540d10b0610b020503200c100c0d0f9800c0000b0709001c5d405036080c46444013070455101203e240c41b0064400d0b45d1100f500800180c180510040380e8010700204204922591103510106c9070b40b903c41d424500d0340d0719400ca0084034480303007510001c0707030007880400e8250041d003409207c04c0103910303150380a903215040203242c52501b0395a400c0009040c4201c07444480325403c0b01c000000c285201e80020221612184072a042c0b0f644070010420440e203500e41190140ea80c104 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 221234271 1250 221233021 221233057
    0xa030203070306090204030506060307170d11030c01020705060f0a0606090b0307140a03060e09120301050d03020c0901030f060e0d02070b070f02100302090a1710270c0f0909020303 79
    0x84141c1c014a10f075000290000d10200c1d003c420050006149030003a10704404490380c0f55600c0c03040001e0324070912100500342c3c100814100301c40740100c880e5641c0c0c3c1c4105055034100980b0400241c00c98100b04400e40703a6911a40900850072060703000282c00c40070700b00e010b000140c00d0003005000106988607104842d2030010014180501c10301e84a1503003042171251a82e28005004000c1c0901064001c204845030390705c011840001000908e8880c0c80f004180032800d41c0c2ca4034081003011402d100c01a01980191084a07504d607540302221806144101d140e40c400c03d02d03500380401203a000d42c80b80c0310b6130340c81584aa145a034001648004551102840c16521403642c506094044100200250400c40c424203460080c0e401d9006044a2002500c410f0a450b607628826607103101402044003e981029556103500080350300040d03610704c4100d25541f94541080d02800300f980c2407080c10345000300e08a4041c0074400c1d26240a100401e1a50400d104081540d000661203104d44400c00c0001c081d01 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 221235521 1250 221234271 221234281
    0x909070f050c06091612022b080c06010e090609060f0903120c0403052b0318020303030406090606060f27050a08010b1c1505090102040b0f070b090c01050a030203 71
    0x310202d079198445902500c055040218400ba40c40041d41c0030f07180054140d45c808640010743d01d03101450f594004205100c0c070304000b071404560f94800d450001290710441494404a21104000c191406901c4000c1210750300d01140306551020181c400c40035600064180080c9004c00100c45070002010f08802e6603a8a41a00c0245540f01e090740590120290000b00a100f0395010b02801c21a8003c0c1c05841c404896a42518010f00390b8450301150f0001d40c65000700302c44d1107503100f8140300c214600504002038164001a283d50400c48040b918103840c1c00364402040614021030000f40a03070304007861500f42e40709000d8604400c031054580140d0a2288440300c01048508010007482c1c058400f442c00c43c3c4481d001c902800701111900e0240c2a0208640703a40e12040f0a6480d074150440c04081c000011504010003400e0040c0002805640074440850700d01c203450b0007041061502806a07a8400c040c2c500003149070001030106540740c00900b00001566000400c441d9440c42d02d00e030051b503943c1c603 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 221236771 1250 221235521 221235527
    0x6040b120109050f0c0a030512250602071a100308070c1a0a14040605030105011805062d0304020609060a03090f0303060815070e01030905071e030213020909070f 71
    0x50005400c41d0b08040c40710082c028082040000d0340c4400003a60083c04400d82030012141003440000d10b01e40c0140c0400140e040204054181d9900d0110300003169281e880f803140c00c4d50306000040d0ac551740d00080450403c03d850f0b83e0141980d80d081079080c5035141140900074101c00602c0041e0941400185100411110344070910150140d40d9000d9132030341804280c0d480c0d40e041149010081200052901c603400c0c004003daa04030382c5aa0b07642803440e0b08207401110310303069030321b4107032110700c800c52010400d5564180503100300200e40c074250020007020188105070711070200d01811060420014080541c40d4582101c01c40c0c40142d07601707951803540c40c000310700a1801e0b0780700ae0480585224030301c08041c1d054101c0c208aa0ac1101160f0141811418170413a1850030781c0c10b203010811400700f00e16194041d130800c1c1007240c003903016640841e9981c0d21a90000c09814040800f94003620400d00851401e800408200300300c8010450510b014000803410b44c0c2c0c0c0140c4100f0500c0604022141010702c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 221238021 1250 221236771 221236789
    0xa0908041514070b06090a0e07050114280e0603040b060103051305010905030d051f050910080a11030f030a05040302060313121106060609150c01060b1801020705010302040e06040b 79
    0x40700035019903110b2003804e10340c900b40010345c0c126114202010200d40b030b800003405062a0388420902030181c0d50300d400015100740040c481031828000050001d501d5154040c040180140c01614148c1280c3e00c0d04c0000520701716000084920940060041c080460005140c55074080c03020300b4005815140e44000141c0401c00042c010120340c02c0c04800c038200403010001e4100c14648103c28001362701c61803c03080da07070000c00c928031a02907240fa008129502d04030300c030a40c0042440e03041200a03600e030201242070040c0c1c034a098501d440d002c840c036552400e080140d24642d45600020314206040c15600501c184640c0c4000f030311500000c0301040d0916520101e00d07c040741d000306490140c002042015000d840358403070000c203e000c0c1c0e0b4001140c03400d019080310828280100079210800fa02d0f0740c1850703c1c2c1c1121003e103d0701d6690303032000315194134103400501c2d206520708003a40a1104102c0024600109600513504050051100f0424840080c860035000f55040f03601180e03000300d40000c81e11102c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 221239271 1250 221238021 221238047
    0x207030803130501020708490b040e010603081201210f020402120f040c080606010c061a10170603010b0a0e060102010f0f0e010b090906070c030c1a0f0a09080415 71
    0x300001e80c8d0325101c400c0e8007a480080b1403c1c400c18a6051084030f40b51a9203000014246e20030000d20001c0c0f01c500199131200308062401000006c61310783c9600040e08558aa0304220b80750580020702e0071812012416260041258020546580d00718210700c1c20b40580c40c0a004107043d000203034980840d42c2d1901921000b5607203610000c198903000d0040030920a007a10b0545aa00712128003146040c004240c1c5031040d00d042c8c441240403440742e92030320b0042c8540441002700e8039003920000c0c0c1c207681d031450150100c2c00a40e1980b1640c0e001e116070404001002e40004e101c1d80c54411107c1c00d0f9241c2c515a0070403500c0540003078000e9982c07000181e002d4540031019410407860300c000c0038840c00e0246d010300d521740a503c1c000c01100d0000414020601000d503100040343c0e00c804001586140301e6520500800e03c645801815060340d5035032100d1030049891000c1100e00303a007081103054007000ea0203681c000c0368114107200e02950781d00c5001c8107215601400407035403403050845144602549104e00c3c00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 221240521 1250 221239271 221239283
    0x60901051503310210030903141e041d0f06010c060e0c040e16090207020d080703090e091014100b16020a03060509010b0105070c0b030403030e19110102070308031305010207 76
    0x7240a00e03486581c80040242c100e01c500f84c0303a20900b45c828804c3c071804400c550b041e101c00c00c1000315414621800c2c0c00103150508859600c5001c0d250140303502024000419100241e0841070761a070301c0c058102d181c0182440c0100e807403001041500e0307910480c02228290801000540302c810034500a09040c042c12956800504044440915500004008103180c1106010011541d11030842c2030513031003000c80c00b0f940901010307032002c041030702c14008104040c440e040026095540306111b540e0b4410031074079140f21b60090307100074012010b540100d481c1d50303d08560740c041c01e180c407014802c1d0000081c01403448204000c240461102c002500b180000340e0000e00c412401556881d206000c0c002c00c64000304903500f041d0041d1101c1d4010300590f1035040d801000e0b942980e040c943c203000d41e030300024001c2c2c04241c1c5603880103800c0a4140112030710b07400c0c61001209602c0c82810001c010603032004030386046600010080000c65080401e4a07000301c0d21039000c03036202d1001d00b0140d0181c0108030700980340d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 221241771 1250 221240521 221240581
    0x40b0d02160515090d09140a1d010f05090126011806020309010e0d0f08071b0b040c0b0f1812010204060801140105042412060906050306060901051503 66
    0x30b120300000c201c5028001c11032850320301c0e91401111601d45220307003600030210310106000d007c0d041e806000c0400e5520007030300c80c650851355072070f021080482040170b0982a004120042c0034035207041c1300d0440509019203200c0c0540d40350031a030007210700c82c00306003001074404072007039240c4441c003034020401028200d084400381c8951420410b0081d80281d45000c0258070300714520149240c04200188030309860340b141f5120484258007070790100310052041c001c019100018000002c0341021051500340502400083c4d807901e890a086c40304031a800072040c21038180312a500d05c015440440e01c40d10701c2d59641c100003442c5c800c00302d08890000c0030122210350011801040d000c2e40914560304a5040c1b07003041c1800702c9880015540b46c07080b0300900044802840504081c0009030310000002151840c101421001020400c0e08440d290b40026058a442d404108124503013001000d4100030212988025540340400180f080800c030003540d201210080000b034032448101e00c008194113550715200c00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 221243021 1250 221241771 221241773
    0x7080f03060a090e010b03010b09010e01050111010b030102160201030c030902150a02190803070810030f06020a020a0c24080f0414030d050f010609060c1a0612030409150e0705040b0d0216 82
    0x3c00307406c4980c00c0ca4007942c42e283d0303c40704914003503840e42c0c121040c6080c40c0105900f00f40044a15014820102681c1d64843d43c080089840c00d00c001d101480e01185410300344109807000509039034540c0b080c075042600340503046d40944d46605125200340300394901140d845c0084a000c3e410404500d100c9031050040e001c0e0030043c007603003030001d622806065403040b81c145e44500d1424030f0380490340006001500444000c6d0f00007100c56000380781d107403068011110181c800d0b40e40c02c035034180180c00000d05007009144444500c0c4920403486080d01441c203204c4014a01440b811f900244024409040c403400613181020424081c401c442c40f07410104014030041c44d08002c8607040c62000c0c880e0500080c1d50220004500784070b02120700318142d011070124480740e08001002c021000103481a54440002043d8043d06901000108010107890740045590f0100b850140d852050503444884407109400400107001d500c0710071a025109803052203900c0e0b90707005841e1802801481c481c5440d401f25031032107030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 221244271 1250 221243021 221243023
    0xf052509090f05010302030c06070f26030a0e0c011b0209070302041805040c1502060a0b03031308012a0207060302031003020a0905091204060f050c0f0105160f020307080f03060a090e 80
    0x184c1640d000750216034000d808441071160314800c024002d000c00c10040c0c540c20001d4655503803003008011002c035004140121003c0910203520990340c40f000980d0700d9400c7d04c0761400a00030a41d400800742880494400d00c100d034881440300310b0758000e1141000038006180725020740c2c1a2409011078601d004100d89205081800030441500d09031006510180009907602c1c14000400e4002a0381d4060502ca480345415200074104942d80140c3c035020a114501c00010b4001d1038200070070b4640c00110f800b1546481680041a406072040011888458101141070700022004200d030030501e80180d59540c0e03402411036090031034000941c0182400300020b0202543d4002e2405000e040c0d040d2014001d00d11414001403189109810209001160b451909801807000d08200104c1130161103012101400369803c546003100d482c0c0c18412a014040c14042d4020390707000300d691880c0000c0d0702d001000d4442e106140100700c0043c2c181800040022a1a00c0700420304000b410605014003030085401e55207 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 221245521 1250 221244271 221244281
    0x801180302010b0303040b0d0c02011d340605030712110306030d110c01030c050c0303090d1e121109040c0504051203040509011202030f150105040f052509090f 70
    0x80e0019802c00306491014503000c0708440403598903210031450100108240405003040003038210a41d5607035400f440c2d132507a50f040c90058201c030100180482d62076548055034040c1030301d1200d000c008810032030545900c0780d09000c181921a10304040c0c2d166968103008558851f220440311224038181803a0410030400300d0051401190104d00f1380e8603190100b541101c141140c4032246000d9801800c02d4121540264024401c916a03490070b20b142c1310f00400760360b295500503128904258443c8440c40241179200e40841034105081c1c2c0c9400c0d1094107a0401441d480445106256407540d400c4c003042039040c0401101c0c02d0300e40142c0203010480441e03c001c0c0c0700740c000b4440d0078051050000101c10246003c400c0320140d036402800e404242c1d007002201000c0780e000a100700e805119008486814100400a8034a08002d444000200e9810441440b09607601c013025140c01074104002d0050040080083c4942420400b2400014656040007116908003a600c4003101380e11307041181800302d9042d040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 221246771 1250 221245521 221245523
    0x5040503012a0e0d050f01140606070f0605070302090d1b080a080306041a1e01021014130305040f0305010b13060303020a0f0501110409050411060415141207022d030403080c0106080118 81
    0x1c0c0990381ca2004ac04a188030b81c01d801000301d45100401800070f41240e00c0b05030009054a4010300b03095a6402260b803134002d9540940f08030b42031a002e582208024511480981100800b030120021240e407400510702014140c5442071b5100c0c40015040c00d1600902c15420400508021810440d065107550065108078194018040d11a4004020341d5600648921140c0c1d080c440c030090703985070540190707018000c10460800004120000d441c0d40321844420145008070b0002814103606000c000c1e980105e800440096800c00e48100046a00410234107402a003040200c102115070b840d0883c014061071480c00350701c01010901080ba04143e902061140b40301d42020118400070804000303050007603110388141900e5280c00f0803000c134490080d9080d0317035181c080200d0901060b002c845001e03000440380c18006078840718403508c4200c001144858400400342c400f40d10039101e605110f45a2089010103021020002400d00c003c0c1e00940c8544000c082010080100c0c50290300302940589182c0e40c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 221248021 1250 221246771 221246801
    0x30402030705090702030a3e011404021302031e090703030219050c1003151d0a0902010503010b1602090405070e0106050408031b0307020d0305040503012a0e0d050f01 73
    0x200c1c0c00d0030103d01450080c0c0450300114144009a042201c03114020141c0044a5410002440d9001c5d9030001d03000c01000e0b01000e083d44110709225103400c40702c035241d8000049400c4824400581c84496460782840c0c508040540c4e41e6440c00c1582c02600f59010400c2d032010904010400105008070703402c01a2071081c1c2c280d8100c140300c05031001c0d1250310800050615001000e6000440c13a20990751070700d00b03405040100b4190084501c480031782d0540d038072550b020399543d01460341d088a04140a580701e4089841040360344c109070002002030005001d84031034a1400507045d080d01d0a00c24008588980c02042ca4905143c145004c0f5110040d521130f45440000110001c42d82034010000d807410703546000011401d01d0820302c1000c00d905000520030040c3c1c04200000e0000da201d08803003890403030094449607901c5181400f4142120703440850f00750b000726a80541c429441c20b035032000c41080d0043c50600c0383e030a1101c000454403105d46070000c201380700c0c108c048015500103420510065500f05c07 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 221249271 1250 221248021 221248033
    0x10501090e061c03020a08180103050a0c0210050601030e06180d050703020a0b070c05010f060609120309140301060803041e2709151a0f0427170a030203040203 70
    0x42410721159003622034540c03044240800f02d583d014501c003621100c500a104841000001d511502031030b601c004410401c080540039070414550701800f501c0d800502940041100039a003080080d250440800f110b00c03040d88400c04242a81e1198005021070000401540c005042111020158503008c6010300001d0007440c2000300054040c0c41540e5086400d500900410010366840d10b6a0480041504041c00141205140400c40c01d2003801d1a440803400001091030810b20085d0007120164800e00c1d00e60b00703564031100002d9100c2c0084003102c003180c00301081c07010b081d4000303800341c05290800501807101090003c0d00c0c4101d42c4912249001e01d11a80d803030540c40d03142411810144e9000643d6030f41402c1100070b030300704aa5010827180d50003114003506040703007100054161184450420000341d640c141d05101c5203000ca030114828201210208403e140c2800030f88583c00843e01d0411841141e4003035002071051032510005269408282d540e42d410072114054020b400a950690103440b80e4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 221250521 1250 221249271 221249279
    0x120901060e0c0f09031002180a0e010b120606070605070f12060b0909131b180219050d0b0402030a050f070e062703030a091a0a0f030b0d0b040b01050109 67
    0x1038801c140590154400e05241c65000c40d08141294085000140c1502c02d443c110a0141c900c0e00c082c0c40ca900b81107089420350b0f1b00d18000c010084001e600404091014000100000080941194610080c038804040070f5581c2200050840c02440c20180c500c500f84410002d10316444100e003854091152510112035914400d0102150302d18042c20181e20f108000800f818500078040c175501101450f0f49861144a99851950701202d680504039003400741030041c00000396084040d040200507510031070030400020100b0345813242d6a1661814802c00168030061100e403900402c4500c0c0c0b002e801175640e070030040200340090000312000d41b9501c10120105441c0b40c415001a000303068000e00c0c003410300300213500035403c0900341d00a07400c1c12680307a07000c940aa102403006c1c1a00042544501480754508500b841540035400b01d01c0905000802c28100e800e9002400d00281e010245000202000d0b0f07c07012404074100003101a000750006000c0100300250508000c1c181c030403e0b0781c2da40b099691 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 221251771 1250 221250521 221250539
    0x17090102040b03150f03010608011d01020705070608040f0c0803071101080f1503190503030402010207050a03030c0b19050a0605010207090606050d05090102090d0516061e030e070b12090106 83
    0x2039010b00500001d00f0804241d02403211103220100c44c10080503107188860075400642114800d07880b4100503512180c1010b17010800504000c02e03460718070300940c5809440d0b55001d0702d820f00390180c8000d014112020800344103858819845c62940300c00b0b41300c10252201440d50b9a500010400c5500c40c01e00300042100354400e5400030b000d404204420181500c80000b05c54081d5800101e494140c46a07080c520b900e1008020322420b0308e40a00302555403400d05d80002810040607400c40e5020391103003001040020f91200500441a400404003069030300c2d1b441d000310700f02003a10880c91141e030802c000d01054800640c41401154000d03000c850b0101d64070f44042040c0c1d9004c2c4a0080807513010b1008804000f01074014030782c0400180001894008102d0014800701801c20094071240c0c005480f10401c0c02111001e00050102404c2c82c400840c00101002c0b048109408a40209a00d03020185440601000240080d04080c1741c40d0f526001e00c3d68082095000071114042a0741c2007e00004031402 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 221253021 1250 221251771 221251777
    0x60106050418050601031b0e1306030209130302030403020a080309040e0115170c06070b090d031407050a020f0321060f03030406211503020108160806011b1217090102 73
    0xb03254050107082507036072420401030000604031414113458030f03010712044050951440780404a42c07105d842c8a14464280300401494a07200d0418030325201081c4007682d20a5184c1d41d008180e410000c6400c00c2c0c80c5412420342c0544d070300003034109480c43d401040d681804405410f9104003903c0801c82d41040d00d018900340c600d0a0b0741404440d02c000424019060b4000f286803002c9a034034221036441464001140c529030090b070050722050054402d11018400c1403040343c1c41c50721149030a010801c40c0c03900d0001c075000c0141106080c07140004040080c6402400701c21402c404a400352515041c001b8000e0613601800c10a000319134914200154103071614203122440700d41e001c2c006605241c02e100040e500540d0040300000c1c83c0c0d00380c1008281d064800c0c01440141404003c0c5010751074a10320003d0100700015000f1000d070802c00300341d500000d07402080340758400002d1030f1014281c0e070300c43d000100b0014501009403004500d40c007001c1d141904141e08065100c00d401045d03182c1c0c0c1d2405261400c0b80 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 221254271 1250 221253021 221253029
    0x2b05100311190f060305011502010207110f030a051002090f0405010f05061309050106090303030c0c150203070903080c06150a0806040605060a0b12070e04021c090f020910080601060504 81
    0x45145180340106003040e080c540c040710030100e0030030001d90b103c40c020540442d042c0e12000021391944018082c10190010b002c41c100c4280c002941800c10700c0d505c200680902a81950103a41c00801451081c2c6d4104582e080040d00303c01680d00010341400000c0103580321000160040c0e9001c034001a0b0750500d8441c06048604840c0350032451420401041810350050003e80d0f64100050004034501000d882a2402001c054480d02d070113500d1440d0150950308181010014001c1d0f0085e400e02284c41d1140002100780d10750801a41c940d680c000556841840f50409840203101040c00d020f5410000340080c0030340981340500e0782e5482103204000d080560350003104c22a8008001040008038990012a00100003d1080803010707111482030380c10342c001d03180d040201d15440c0140b0030056041600d1311f80c241c109490561030a090100503842060340d800811115030354540c1c603802801006c44000803181d6004090345903d007000f060201c00c01d003050186c005107005501c000109280a80308032011a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 221255521 1250 221254271 221254283
    0x60d0b0105040507020313060509010305150f040b010302040f03080705060105100c03080907030b070215070f090302092d070e0f0109050118080d0302042904030b04082b051003 77
    0x203a08000c107220251401500c03c1040d844284292000d8485500513080070340100e65400d034940c803641e0001015101c003c7c0018540e00f82580100035951102d40c1010380b000b0040d1000b00e0b074007000c0b600480c002d10031640041248043e260020041045241c010048035018004580c1266281c008104504850240e03100215500c0f039044d030000383c0034040d1141c0c490001d005071000159292200c40521508568500058212618442203030b921401c1050300850b03039240041020300540006000d401c0940000f9104030740100028825014502c010b036250b40c0d08003030581c520400c5000610400c102503c1e0980410341840e0060742ca400d10b0f036601c000c1a00140c0d21030b82840d190000540c0d215081108460007e4808440451160020005607110a45540d00140d03110315101000c010081010107143c4916400341c40e50981c60101e90640e0b0940341c0280e08041c2d252654035051516120340a40319800030080c1203041000101141c1c1d040c0c4450b0340f000240103607501c8401091801c03481c1d002c02850 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 221256771 1250 221255521 221255543
    0x1106150a1e12061b1e0201050f130501060801020a03090519021e0d060515040e030301080d11030c07120309050409120e060c07120c0f030c0506030a020d02070501090605060d 76
    0x114032071080800d0001e4081d40d4000b1300141c0303000d41604003041c210f44800c08100303440b06858040c9159484d6031405800b5200810090034a00c1e100c015500c80642407554195211102c4001c0c8802980000700030032501008558032507400e0f20107800b40c078003068152001e0041460700c05004e904203450000661b03008204a13952022100340001542e180340c14603401c4402241002c00049a501c1803d0040740c4044460151700f01040800013a2030000480200a400a0004100e4860f0000c3d03030030b980508030305101a1600314002107501c4c0d4001c09602d400c00d40b044500c0081c1d550910012086103e020350b64518050b0340307038024007041c1c503031541c0014028901d08080d50a081e02c5181004074030389004109078641509646154540b200d56002002d8008001c41150f0400814500c038030001c0414208008103585035844042c1c031140c82c0c0c0710341070051a0000004050600d603904079a01c01d166010219290701032401d0442c001d040c1003808650180c5814049012031818850a60f105940b008412074 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 221258021 1250 221256771 221256779
    0x31d0a0905130345090c03090507050604080a080318060703050702120a1b0510110c01061a04090506180106030f0e0c030c040914010e0f100204050907050304031106150a1e 75
    0x40b200c00c44404c00d0101509070001103a41c00c058050400142d81955010403880d01c81e050550400001d0743c040c5100711400c010400000801007410804c01350441c004540301e5551036110b03100d810f0043c0d0950418052101080001e541540c0028011384242c0c3c21944008540329141050348106440030000c00c0340303505000d042d9601541c0c581112849001034031040403404922500351b03001c6400c4410382850200310306a00003001d2040300300801c2020848441c17020003806000c0d141c4a0380c01060415038442d00020340c9912490015a008801c071a24011030f0369460358006e000340203083c01420906d04145905840320000290450003140080c060101c4074132a03410040240700565045036044003500300b03418550020b10134070104000000c041d0110301e8034040d00c2410300c01c248c241c0700c039528410f00044c00b5545815090592049040c2889681c0c0d442d90f0400b640e2482150440016a104100c2001038204411445950300361080e201c04280c0c030307140c454511008019050244046091840c104 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 221259271 1250 221258021 221258117
    0xf080f06010c02100e09090106230a050d060915020405010e03060f0a0f0e03040306021e0309030702060315090a0626060a150f060203030709050d031d0a09051303 71
    0x228131304251304081011000341e80214040ea03070200c4140c0c1c2c0595681d031003000004c600c0740300e00c0720754168045a50b602d003074800c1c0040c1c8580580d024150040b00a49140f10401415520200c1d072181c105881389851000080d129020394401d0090f240060a2090b52542070704001900b540078403800d8502c6155540c401e0364810003000c281040603070343d5440301a4441841410701c0104055401203402581c1c40400c103584030320b1044802d280780354400d4104104540010701000741c1d00d0300d5a04488090743e075242d000c400300b4144607190401e513026180c0000c6c04008442c43d401002101c10401d4004211100d510300483c4c08540b5108003030558200d070300016410076665000f4005035031804041803603640c4817005080c0c401016080a009a40b0000a014885270418444001050202d0382c15520007041c4c3e8000f402e401480005108441021070464001c0c1c0c3d500300e094014206601307042105141a80500c0c8181e200542d082e800328070304590700b884510381d442804090706030107203074040ca00f51011980 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 221260521 1250 221259271 221259289
    0xc02040e0c0a03080703090506040605190e1903030e040903091401051605010506030606061606050403050412030e130510030305130b030a0e010f150e0a020702090103030f080f06010c02 81
    0x2044140200074440d0314690714500e614002d18000c107545616020903280243c003103651504654030a11091004124448e0b0090440e03032110b24002c42c2a03aa0040320000343d07460451810484d034000804010700f100010110035603c00c487c007a03650754424103540010300c0100c0341040b8020300024070703c01d0107000e04c01800074030114240c03061400d186824044104002003001d141c808683c1d9035100c609000c0709103010048250441c404540742490500c00da00401303542e9080307034401000b1a0301e42000a050600942c280c0d0300920b501f10703d600d0400c4003850001c00c2011518001442403540e122034070000d40041c03103654400c20703c08801d80038084c00c5480a450381d4002c400d2403c401301c441c003800700b00c481c001000355000300000c00c4086000660030070310a0960300d403040361810342c514142e803040c090681000e03200c04031070740c1000c5102142c85100d8480064400c2d030760040e4100380001d00000030182d00910303901d50b0b032495558130320081d214100b100354101000d0f038105000410723005001e00903240c50203038 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 221261771 1250 221260521 221260541
    0x6060f0f040b06190f1706090403180b0a03020d1503020306010e131b060f030c0207050d0507080a0302030306090f091203060112060602100e0115151103070803011a0a0c0204 76
    0x140d030500550403680200c1c3c00c420340d0b40000040020100c0c0c15665080908114800191440c1c8002031402d02e000c08c241e0000244090108100e6820308501c03002c1c400113200141c030039442e1250741d42c150040090b010307501035220110b49030302c1c000c040b024007040391020701d00740c990003000b0b8500c503460031703c0a10310903802404651128400d0703407104000400110041c0c410602e0b408401008030b141c070380c02624031462403030007a09040c00d186040380d11581c00f1414030300b03a8108443c0c107030300c038100d50510601c2e00d241c54019000c0391003060b20207410315800001440c402c00040303640402550303800800705041403080c2d91000c09a4410305c0c480c00443c0c840405154403070f42c10300d040d104404840d04418180c1d20103074011000740c2c110401418904070940109110511114003c1c000b0f210707802d508000300c80d064415105008000c111000c881c5120352403c003001748091080300d807200e105040019996000784035038111041910100383c0e2540e20a000d0f50301c0900c0c1a10340c540b05050365007d100103070008100d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 221263021 1250 221261771 221261779
    0x3092a050303071725060b01080603011b0f050f0d05060a06020f0601090f141008190b0408090301060b04060f09050108090a0b0408041208070501050a0504080a180905090a020306060f0f040b 83
    0x1090f800d950248007905c200280550307004506082c82d00005000c140c1c001d00301d140241d04000c800203041d000c40090801403602440c114540403040c03c01140c42d0300a84250034200100004c11490300d5039190885401450100c45030410641d031140c00780d82c0c40810f200320300714580008004200c003036826881100990f52501c03020952071034103120701e82c4042c401c0303541a5141d4140902440b02040030480341000c5035161a12030109942e5407106000f026000740000d0050070009a8103a03d034600b0b411600c02040c41d4000c0b244ca540c1c482c100549480c80c0e0604500018003010400601c96218905850040c1818000b50400c1c40b11a00c4401024000030000d4411010400c00041c540c120340c401e031001903006c0d0a0f0360303480e00d0030b61800c1402d482d130144c040201a400e140912001c11041400c540404620303052240e180c440341c1201e9144260580e20801070a4500402c02440900204030318148030700c2201a00c01c20b5581104000e040700e046044560011442078010569081940c4178001c2d2900080c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 221264271 1250 221263021 221263057
    0x13021303080705150f2406130f140103151206060b040f031506060203190c0b041103060a11031501050d050c090a0801020a05160303092a0503030717 65
    0x1d220500203502c240821110b9034805081440540b0240740c0083c1c11100858004002e810040c20b0030f40244401e080f5a00c0b100006079540c0165a111801c403449005098030048441d99074143c4517400e00f0f07080c03080d8580c040c242e104003481c0e0b61091140b100501c0c1c1403030200409038180f81c48603103130749006602250340343c0d0746042c0864910040805417000300004040074100608510742210303058811113070000708500340f950a0142c143c01009030340c0d00704011340d40c7d246080c18280301141c2d850744402015020072910010301051221001512000300020740884d05680c485440142c00c8401005205200900510105000526549880c83e4140052408508002c900c0d00c01500320742d4266241c2c090b0003400646230585040152180c0b0041420300000c50824031841c2c8041c02c0c521913401110100d03200300c0e01c443e04042c026071000754400d030414400d410303072014140c05040031021043d142031589100c1c1400183c510340001210380e0140d01c00300d0f0b0a000601c01c045440c003504042d0f41c0005030036a00b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 221265521 1250 221264271 221264273
    0x10e0c0d090516061d060901230301060f0206060f010f09030b0f100506040b1204020607050f0f01050a1505061813020d050601080630030a080103060b0d0213021303 72
    0x160260001a90150700a04919442041c20180711030f0164440740a0283c13035002008000c4c8108000c0031070000540d015940c075948080104c0b0054052044101d403d205200412001040c0b01c02071416500c01d81c81c4c1042e001d1008800b40e1340d6000c1214013982c4a0094500145154490301000d0b46089690034518042d031f840360b640303110b40c400c1101c0c540f855016000811150034142c00c007410080600391429072505080c08c018011601c43d103030110300c4d1039080703c0220301152a2101101d8403207420600b99076004c0c00013108a40c9a00e0010421900c82d802c0a0214038881030a1003081181100600e601035500e00d000d0600855400c400d91511100310300040b502e00b5520b42c103c54111204003079070016902e040010f540c404560000c1c01c11410004900b0410006440b00810501000d0000024103400c085001c0c041d2107545108001081d9404007240c3c142c0c02c50f4000c041d043c1602d100321401e0141c0307800001803001c115000307800658006100900280c3c22a4540d006180c81d00078224024051516 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 221266771 1250 221265521 221265547
    0x11071709030f281e240504030e09090d080603031b06090d0e01200c040f0207021201020a0c12020a0c12060b220b0102030904061502120a08010e0c 64
    0x60341c00c042c1d040c2d00b10103500d110020311441c0c0710001901040c0d0300380d8064000d03115814081c0203180d40700c1c1c010080d0b1107010188a07a1040391039604940c42d0400c4542d40d4a2803414000d0507003950102d0100e84111078071401450640411480788010200030f22102040c0c020032a01400054502da405020800401301c0108808103110840714251008220a00301039070300300c0c50440394000aa040041c201c106a800d60392108140c000c8528000c00714441c8000d1100303545c100601c40345240d5103d40340001e800c9c81100301c8d0b0007402407240221010000107510f42c0b4214240d1141e91501d40018201d03030035510005483c0b6a40241908035881140c01c4c2c0100d59860f040424026040b10b1110351703403008000104905401001d10340d40b800c0d2a140d10050040780c0d1510480d01c600d0000100503114080c3c8181079100b0001d48000c0c0e54018400d101450750307940da44c00280708845904005004040c080c140028884003103e01c52003003550b40240303070381ca8480c9000780300074083e04980858800700031562210a03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 221268021 1250 221266771 221266783
    0x201020c0f121002070203121207052a0c040c081e04050f070e16030b0a172d01060501090e0103021504080d031d070308120606040302120a11041107170903 68
    0x200f07880050313840845004041c45c0964850b0f00c0f94240c2010000a90050005120650860503d0030b00e60b031221030b08a0707080e101ca031880c020010f480313440d921b8681d1001400610042041c009407810004c441e0205070845402c601200d1600002101c00c0c00c80030b84441021540341c1c02030040c020340d5003c078030005e9240d06002c0c15070321218101000000740700c0c68440c04800c24240940ca410100301104040b00401ca4000380c1d032040442c0f511840c00542d518213401c3c8880c82100c07200c02c0504070400c2e0820320382c281120300b42d41105003943c03030702001040c075500488a213019241d0542c2070981907883c41e800c110700c4090000c45401c10110600c40000c01340c408011681d005540341d1408101d680c1002d000c034082c482c00308a00445644141001c10110b22240115a0b501c0303658940686180d58000200d071180c4031350360000750080013038048220b45900103d9480040b41c42040c201484105840400c4150751036041000c0c4910003c00604002403a841c810f400001200b011403802d000ca4240004e0400c1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 221269271 1250 221268021 221268043
    0xc1202030304060f02040602060a090203190b0a0c0906120f09080307051903060b07080904111b070906050a050d02040609021305091e1303020c03030307111006030201020c0f12 77
    0x40d0001c02400100300da580540300c2da10b00074020841c00c06140c20002551001c1c09410400b600b40e40381400410341d10140302d0340e02e000300358040005a02d502450103040300041180d80000302840d2031407210b442481076080400701da2440d030360081009082010040100801a5a41c1580d075864520f6030014158002440c8200480c1e25040c0e10b03451104003d4009030a03d10706001054076000d001e0000d0720b0f40100b030b80d035260340112080307455040035408680101001c9540440001e800300e401904c115142d0320301002da03c2c19100380d07500b003507a0700041825101c4601400b41d2000c15501c1c14440c50030400310b0800320030300050010555591301c0315070008a07409412207003050400c3e000240b1040c1800405030703400815003103080e00102410a010b483c81500907110031400c1c2007541c0b410061520070002c001302c06030010180c1f6560f0034080e0001e0091380c003175144d82c83d00d40102092180301ca0401d116100807207406801a2800054040400100209101d24540d1120b058808180121400c104003410a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 221270521 1250 221269271 221269273
    0x11a01050c0a0c2309010e1305070e010e0709060804020306040602030c0d09030302091503010b0906030c0f0c070e06060a0c08030a020d0204140102060c250f02120a030905060c0606100c1202 83
    0xa1080300342c5001c00c8104c16001e02540c40040100490362940503107990003c0d40d80d82e0750200381c40924000f0305001180c3e0103c0802404c040000c03401c44c54000510b4060750f2991604041107a4400e403c2e41c44440464018bd071540101002401040442d0011035012211140b1a454041f9440c0241c04580000000b27034002035003c60900d2042c104110400320b03000c50440160705541c54100700054500c103200c24940200c002101040035000c4400607103400146880c0d01c2922081c01c0101190303901564840ca0182c5950300e0b0200316942003103401c0380c40140b81030b03485d9070512509854403a0b240d0700142608015640c03c222500c1640310903c040c1014124107200349180c0702180c8002881d04101810341c640c2c0307035410481001c01099007061340e42c4001c1503954000c10500d4500b829000c0300c044c0080a03400400e0b008040d14910004128140300c54820740710844019203c00a000c16800b8a4202c0d42c42a427121000c52424501001c9140e6401b256140c681d4003225a6a540e030300c24000341a910000d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 221271771 1250 221270521 221270549
    0x150c060501170703080904020f1602030705060a050306010f0905120a060509190312091502030609010e0c0403030c0f05030f040602060106050702010c150e06090a060e011a01050c0a0c 80
    0x100a010300549004011211601c90005074080202d600c40c1074038400200103100008400c0b0f610345503501503400c00c00791451020744410070136061891058202004a10a028844010509141030000d68010151580d202c40c195501c940054800c48039a072050b8040c0108020000b400380c0c0c481c244940b890348184003070400c000403450058117a40c4058101b200c41e4000018540c01606560350a0b001c031030b05445d00c484c0c0d051101006034010221100060710407600c1c000500301c00580c41d001076004050558001410780c1e079036500d07646840401d46400c0b280c00b07010001040400c0c410041d4002907400358074580c02e012051b94030140b0b16807200015103901d05000c902042225014408540105401d0034282d03d840c0c01c55000818070180c0b614010b200c8140101441240c4d5050b0344003084940c5a44c080b41c00c05c0c141170b901c5695490b4a401d00f203405504090b00076602a106010f0b1b01c0c940b10744440311003122600c0c0c80c01506c0395003000707448000394810001c5c6000070071a40800b075002009040c3d26806 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 221273021 1250 221271771 221271773
    0x305010c0c02040b0a03111011061e0a060b040506070c1706010e0106020c01120c051c0e07050d02031c050708070614010518071101020c01091208010e04031710150c 72
    0x1090340c03080d0113054400c1e440140c040000c114940e20b011005d079011a60403c4415021906032000e0300c18041d00c148512860040115031071403071881540c022200d441e01c01466450030580410390340e890040300150501400300300014108000580400c52140603200f41c04c0d40c80d5148124420b20300c0c01c0b68005544448010410700319070702010b0f8094134a91002d0415105001c1c0040c02002800c41000c0e24075940b100050b0813a403089058490004d503240c207107030380701c80400c1040b405080c801c00e00b4144e5000c0c44000203800d1410409090350503038041d028101d904001c46078507040440c40d00b11101030080c10041c48000440407801480c2281c0700b50000030b204464101c0c40030320090160006400344440300c5008000b49180c00c0d216a00500514191040c1028800e88038064018450309404c0f940c01c0103240170130025000c5000389160416954016280e0b605c034040c00d048882514054046a084c002502c088600305503125803211054a8a1103c0c0c4e80c2e851031000880b030740c030382660006000c4a030760030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 221274271 1250 221273021 221273029
    0xb0f010905070c080a18050d05010c030b0109061407030201020909040b010306050106080c07170c0106032303210718061d1009050d0f080310060311031b0903070305010c0c02 76
    0x40c2c0203041440c0c211240200e0355a80040c0e1710031a4461000e100c507211102c000c03543c5890703092010385405029203401890516149020341985500c0c0c1001c00d00f4074020068552003261124101ca0581e0b5070101100c900e440b20300c20590212006804654003080f121a9a898000109011320301c1618105020741c5141051802c890040e000350b0200400c42c814080c2040c8a6801d40c1c420035000307e000c00000c08408000c0c0400e2041c541c40c08095401d1000000c180480c4d4403058403100031026041d254046076540b0561203100388200c80c142c0c2111b80e0441809500003492242c1d210403941462040411324103000c00d4404215480000050620203841c0c0c402c5035442e114940030641600c0c24000300c2081c0c58050f000843c5406010b005031119041c400c11300a85450b6014415048110355949040c80400c50060070002c0c0039402c08603051201c0011003104150840c2d01c02c0d100c0c826203144141210942004030f5026003100350741481015808004103a007845142012138143d20303241c4e460348091042c4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 221275521 1250 221274271 221274281
    0x60f080f0f01061406030a09050d17060604030228050414070f03050c03010504020d14180d080403120b0f1906120501080604030c0503071b1703030907030219030b0f0109 74
    0x101e08641d06240040241034004181d411600c142101c00c3c83c5c070b80d9038002014006215802d4080e0041c480c0307500c020300c41c0340c22442900c64404601c501003119543c10052210604c0b981c0720094111b0502142e09100050320200d00010380c1c00c0b07400480704141d40e40c0019050724010112504407640240510504c540c00c100900e4030000305040c10300c22841c0040c3c1900e000e000522810b40a10b40000d145e000c035614940c040c040300e1010102c0d189550910a01035860b0380080360310081e041c030403d040c50311980e024a031014415071b819510040131111191b020001b4210000c00b4940202c0a265016240d6986052200c51008081032210803a86000c0d40203203642c41788140024080d20380401400003540101d1915402078142c03c0441e050149860228914850200060300041c3d043c07640128505041001c5801c4462541014031810103104800781c607440259051005030780403444c10001414004902d181e0380d554211881c1e0465030fa600c1e00342405404855180d450360903040180f0908155100b1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 221276771 1250 221275521 221275543
    0xa0b0709051c0605100f1404060512070915081509011b080f04170c030c0c0a0e04020111010608030a08060a06140301030602091c0f120807020c0112060f080f 69
    0x146458400e42c080081040d0744810030007404203921200041c55600406000c3c500030705186240d0100195106801640e44a0080140c0e02c168100280000c8030300d40084588003030030707031400580822442c0c01000c1d40101302d410030500c514401c1c000c00140080c03007405032041c81a02c12400b00391a117080e2540d5400c461101c00f003005429407000f41c060600740c1c03005a05510004400d0780e0a03164466080002801d0000340012203169800600c0c600d0101c008000303890001e0710882141c240c0601c1d5010094100c0f4940140500e02042d0b0001a015600c17400000d1404414072000061080d2034108507030465224120003c080313080c10043c01907a085c4144150b0044c01c0c54940308a60b02d02600651106100620001e000c0f2340c1c001c1051001940c1c1d4800c12407a1100780e0319800500b24803440c0c0243c003c00c440c84140e03050030070302c003a074031b030319801101e00d5172080e962580034240d003601c58001035a042101c400c0e01900980e03a50700200d1800074548010000d05a241c00410320640182205860000781d03140e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 221278021 1250 221276771 221276779
    0x30611030411010f05041406091507120302030c0a050d09021f0816051b1204091413020306181504080316020d0c021023041d090606060307110a0b070905 67
    0x38404e1982c1d54404180d80585089055144488030540c0010303059019000c030071a8801002800e0501da48164030042c4460f84c855882810802c80114081e000c9002c21130310034845401c1040682c0700360340300c0e1000303144452340b01d4400200302c80140c020641e1a142d044074440d0407007070140b408980315013040115501091040302c444081e02001002000c5000310040c414115121559500c00c1c100103115800d45480381d81005612280d4800c110405010040c40541410f485071010031000c8a400c05480303561a00134004041a03184c412041c00302504e0124404d409000341151400007424820406020790f0041c3d40290700c0b4100b0041d158418048084c10000303561040202070081a0040c00e00c82c030154045840c0208941d17001c005507a444824480300c0901c0e06007003240c002c4070a00001030000e503240440200d01400502c214101020300070342c0c07140740030f81c0400c0001c0d58902d0280c00035a4402d60720b1424036603080852000c5481c008402d04215146d00030301d400c11444030f40c402400002441d04903 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 221279271 1250 221278021 221278037
    0xb042405192c03090108180607050d1d010b0906010906022d0105070903030f030605010801050427050d030b04090b0604110f042d03240603061103041101 67
    0x414080d07001a40c51070441c0c030360780790181403080600c20000400c519501104004600d040c000e1015140c3d400882418085880d010204101200e102025089500410010803a03502d400100391210b4000c070034085081500c0f558a038044001c100c41091104003e88000308510f5001401c000d45804014046070400450010070440142c1c006910901c42035500104a501c490200f40c0c03625120030300907440f15560806082c421902d511800c080d003101c1c002e9546a0601c440710b2011001c0d00e01d544180341c0040d0040c80140980c0c03400d6800b1101020300980b901842021000c982020f683c80064140e80c0c6410000c0c199010f180c040c0140c2c1d10070dc60440702045500040d6030b03541e0b00040b000c1c1c030240c02a9030710171190152001040440d49141004503e10742c603507940380c40f02902e011490b40d92074616103000c05205102c4204115202c213503980286011308504002e0300344036040340b080e01001501c0351110703c00004580c13a8415040c1c1c0d4000c4403202a62440c15003071002040d20583c40d064100481c030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 221280521 1250 221279271 221279281
    0x518090706080403050909043504230a0303050a1803320f030406030e152202040507030b21062e0f060216080309010c0f0b042405 57
    0x11610030181c0c1d01500304003030356032124141102e880c01075107842034000c0051810700083c46032200d0395009030034244580b1407109500c60140310611082c80014000140184010300901c007907400c013031503007002c070485940503076521100107005001141d20a4001c9a0005150715905512400450303d41030300b08200310f0344500e50358800440a03045221080ba08a01005114641106401c068510000103048480c0407044400f82a169407140c4071b6800802d2a004c00c17000e4440f00030400d0300c0c020707038541c4843d5441d41c0e4140400e4441741c611004031a45152042e0b02c200143e80700d110303ea000b021107039800190a00b5034401e11180c81c9284d201032101b403101013503244140700d0000e6041d52050800800b800020000c502071104400da4046102c2c0203007c00c00c0c0032a0341c822400c011821201e03250308441454010000143c40c0d01e103980510441900700708480d002c81e5001d900d106009500c51060041c20001d0340e110300d16880000e48045903060140641031120312544980b014520115072801c124034140 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 221281771 1250 221280521 221280523
    0xa1e0209030d120209032d0f060106080408071401060603061205060705090f040504140706080106050d05040c0b07050718110403020f0126090d0c08070b060310060f051809 75
    0x802607503038200403607981864420200358042e100038040186c01c4840048602d100444c1041104641030110300e10706044200e51180054490300c00c8034802c0c003610250742051811142444010400e84014a08000344000542200001c00318008403200004900741080d6000342581d910b0307440381300c121008040903008070303c1c08100300380c002656083c0190344100d1100801c80440303411359020750040c541400c000c2030099055031003502d04102c0c0240d49545072110801d580e50301080c0100c1000a406000321145805035510154100c3d014074000d403800c0da907820316010141c0c490349088030150000481080f026150821b03c0c082d0210103001400284000c0082002500540c4006807103400c80c4040015940d01440302d0f0130341c810b900022204907805001241c4c80e001c0c0140c620221520030117242c40019480cd030403045d0321941c0041114034102e070a03100c0c0350420001504c4070341d050040740110150240144501002002c105490141280c58801005022030400004524142c00d400070800c4081e0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 221283021 1250 221281771 221281783
    0x3080a1a0405060a0503070605120a050c1903150b120108010b101b0c032108191505030d090f0f080c0111010609020f03061c03020d0e06090303030a1e020903 69
    0x109980001d1507599100002c0ea45200c4c540c42550140285000855010340c0140203080300715022842105945540f1281c2044038000c4030040d950590601490320b0700c2136a003162518020891130082041c1c03460300440040c1d611140d01c56500c1404c0043c050b41000c07140040360780100034490082141018041c081042d0016a80300d600c20010010301c084509152030042c5440035411049292010b6101d20f484001141008050f10251050820240490b4421081c180c072070418400001110550464154040c0c01c1c003170752072960044450008501c0f9142040450600220344da1081c458625064502c8601030184d0451002c0040c148018051007100059500e4a5203081c07800044101701b08445da13004010540240700d495000050300420b48039050701441c046c2c9022a2070340c00150031307a42200e0507d14070100c0140075821040117424030602420030316496080c050b06541c60018103000290855008441843c100c5548081c0b0348083c0c0c113010414000040644003c5181c030100c0d00000e44d980e1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 221284271 1250 221283021 221283071
    0xd0f0b180f0d09060c15020301120507141518031002030a14060907080711030403080403020103050702030a0e0f010c050a050d020115180b04020d0f050417070807121407060903080a 79
    0x30170741c06890410014210102204090009011500d0356140e540c04400b444d9045020b84051248480200c1e55610120021000d214001c4c01030031002c00460000302c064100e5101003c1c40c109480760860b81c1e480a1012192244808400503624506072410034116a10000062040c004a2003080016158a520710f60010391a00700034400d41d940351700c101c130b18826103019005280000700f00002007140701d00141054034801d88040c0903d03540c4410481c1d5a000b99819000022902c5100018900b005440071800c150189808004511a9100c0394541040703050b040322242c0c003036000c060740c09074280b140004010501c042c84009504e06081402610f005031246019590340c5d800c0ca5000303a40d2541120300c40042d61805000401c00a804d020080000301c4065070001d1014801c43c2c00020044211469250301420386410148540c5800c030000078060310007014020160601d840021640001c3c042903403140c000070944a06500e0000d258500c0900a01146810600d51802c6c07201510b40d916051 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 221285521 1250 221284271 221284277
    0xf06120f050705030a0507030b160c02010e06090301020418060611060708060f180f010506042601020d09050d1413090e070312090602010b0d0308060d0f0b180f0d0906 73
    0x1840c03890800d1814501c141e0300250707240c42803034030381010010041040011240101000c02d05540c0e01c40f2884403011100c3d401c94005030808103524010b6010b18508000032001030200380c1040b5008010a089070300540000103248461029000740c3d9040d40a00d00141069251848014100c4134180341e4855000d401c1e0000d100a6000003401501c51040e0041828401002c503103641044500d101000312050307030a03402200800e0b00108050900c0011102120102c003c00300c2500a156001070f4429081c40c0103d607295003c00040384d070f80c1001c1c0224140745019601502d452141e5503409000d603941614600c3c042c01c0184883c1c0c2e41d1a182c0d51107181160103009000c40c004849194560400350385170001050701017901c640005d05940451140150b405a400030010a440c4004020811648400040c000b40c0c030080060041d0a000e24144049441002400400d00050303543e00d141840498800c00e11115240c1800910542084078040180607900503064043c010140102424140d014020038 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 221286771 1250 221285521 221285543
    0x20405030703031b0605070324050913080f0c071e18020309010e060906161704080a02070b07050109031709070b0315040501090b120d050d051008061303030f0612 71
    0xc1c00c0c2201050342030b10b0f42d00c02d00822280c0350402010b0020031445030f003e03484000364400d5001000927141a0010340b94020541845940c0b0303511b40c0502d400d16032604544010b01405034410000c4200060b0409403055005402440d040c26418030702e886a248144c2c040b5624640c0c00c1000803080c04180041c008074610140c0d890351755010642c0904443c960015544c071540e010401c080401140746401040e030b401d80340c81c0080140b841202d10b4a810071a400e05502524080380000d220b8100520f000d802e9401a00c007003e641714451304c000d402900302500c1c1c81e5100d548500070560701480e400032045c05003405c0c1d400c50508202590b655000c5024100f1441800400700d00400540340601d208d001000703006221541e141d1b1804805040c080c01883d01400b02041d0041800f580401c00c603261442603a01d80742003841c0110504041e09016240300b0b1070b6a01105c0c0421103010520507580700c1e04900d107940c0302e1a089490001c1c1120400444054944d240c0780003031100340f100021040d1420342000303075219 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 221288021 1250 221286771 221286797
    0xf0702100318060b090c0715050a140708090706091203080403120204080c0913020654010f050a030902060d0912020d0203070f02090a09060e0a0c0902040503070303 72
    0x401441841c507081805220b400001040194a0700a01900c281c1070314900440d48a2010a544500525000401c0c2444151015500661650119900540750348022070200c40302c00040c0e411020503206040054803040400c1780440c8108890780050925180651049161900c1035807140c59200340141001050400308007803500c14008a54500101e0004540d00c40c0c1d141c0441e66280c2c0d4040c0ba5902442800c2c00080c00d17040003d0000881c540c001d40031500d4a07020107003d64003900c0a0102c560b5220803104030548001122440c103d00f20071000a41003107244041c0c20868a4034581441810031480352403441003139911201b075802c24041da08002c1101c441301d00c0001c4050040a40d03a005462800e15032801744501c40c3c0103074004099507003e641d810000040102e031a4820b41c9000b42c140c0311408100001820b1030041294015452f45c4000b130803134400d60725a0180d4000383d00c141c88503400003101d40c0c180010a0a44401000c11210461a2078070301030109407146040c2c03002405024880000030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 221289271 1250 221288021 221288027
    0x3070905030d0e0439140405060306090a060e040b07170702100b01020a1205030106170405060411010323010501020f0a0c0b030c0705010204090f05010512061602070f120302010509030f070210 84
    0xd440317140e0078009800c03590511280070303003800040c60312800070721318441080600150380103ca0942c0c40162866145035a00010b00455200c05485604440e95030800090342e90840c0c50902e00803031181201024505280d10020b1540021881c40070009480c0014000300d03035000206c12603c0824084041103440c402c40c0140c3c1000b28032040940b0a03149001ea00500780e6101e0001c6050b07840ea907d40070341000c201d40e085801c00208030340c0200107901c81130100d0301003028080300c010011014075010807000c0365512105259030030a50f0420041d041500140310790b41c0c05003c0e05c00c241c040c10008003042c0c0c82e241c03038401091503d0320a81c070b400200000800d89a0b190740040f0f9000384c1c0c0000081d540d6540c0c815100004000050002c41018902000131641e880d150482e089000a884020501601c6024080c52100c0040680c542548904240001c4001c0d0300d10921000b45608600c5400c080e81c2400e001c0d00392013004005181c3da4004202d00c11034034071007070251021250160b0356401c560400c502c0a07 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 221290521 1250 221289271 221289311
    0x150b010509010c14012003010e010b0c1f0204320d080d0b0d0f05060118060303050316050417010203011d06030d05030604090602040905060301150501050706090606030803010b03070905030d0e04 85
    0x100601e40c0403988000040d0146c02103040340d010301500c0c2c0080e03a803610120728a00a4902c000701c940c0205100c0101c0268085600e10307001140440107140036950b050705004a4400040035003061840720000000041c89010424004411b507251620717040d2650754220715228501c80201015130795010a01c06484100e074899121307901840842c00e0095a042240e5200400d00c0f403030200c11201d0070541c51a002034010081208e5068998030700755103451010801241c00c0c103104030b00700003061200150020442a0184008503028001a034035410840361580390384141d400c0011401c500e1040c004c5e40c0c0c60002e444400404189455512031711400d002402034101480054115400801c000c078442c4036942c42a4001d59048008001584001106c1d40d113044481c403496000c030700107018080104020790030881d043d40c070410300040c49903107079500d03082c0070b81003a0031850840320044208100c00c0c0d00300c001c500240408400408900782c0011000b071850101ca000c1b9405591516900f00d95801c00c00b0300 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 221291771 1250 221290521 221290541
    0x90d0807080f0a080406050916030b060d17070302060a02130e0a0e01050a0509060709030b06010c020411030c040519030c03060905010b03010912120212070e031009150b010509010c1401 81
    0x10569a50f007154034001d01a502c107607404d54003286000c001c101c0107000060700d91540603e80308a074209900e90b45500a40d1280184490382050919084100141000d4103d4a507c41c6c0259510f0300e030803941c20700914018004080044461040282000b40301c00041040211106000c1c107850350b03903848003440f002c0d00d41403800d16580c1d8241418032180c8800c1e0b0304402d03c10380501c4207d82c0f441d03841a10464060360a4803014080107440e03000300c0d40c29440b8881c4180c0243c0080d101050380468032000d20596481114682000140403409029a162000d052001c500242c082c80c00300340c1c01d503103075244510307030f24403005040903941d52050701000b034290004078034180001d00030441541c0e1414aa41c1507041d228004000a0081c3c5c004080d141d040c0c400d80d489440e1809040710030b035070b40d004142d410792506610b480c0c1c540b280260b580c50b0a481f80c05018107035442500c0c000460101462440c094503442d001e040d06000040c0051036a90b684a03036a0754041e034000042200116130001c2560041500c518 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 221293021 1250 221291771 221291797
    0x405060d15050601030c080708010611030708071a0601050f19030902030a0b0106080c070b01050f03151801060609061715040920030a0f0602070c051e01020c06090d080708 75
    0xc106003051802d60140340b0658080e207080c072501403250012608a40e088805002080140d00140078080c400c0750000540b0405004903441c0c00d103030f40c880348141c1c0c000c80000c8541c030b14a0800e54198000d0b2516942d0461400c2c24801d00306408204401c05c1c0c1d008890480950702120b00c031200d00c1610075048194900d40140c10b951350310483d41000c021040e024007032072000c00c0c416004255501c0c045011140a503810050044869003840200301440d0031000d02d007a8944541c244102101d00d0f52070307885004580303e0800440881e6a98107050954070694030580034401480c40820480d50072909030041e91800c09070440299a13000c103821f1400d144c107810180c01c04d00e400c03040c03000c1000d01000031894002d40f81000088001d00b200b011340c0c40017440300007801c03c0500100703800010740d0743e0080c264052250b0f00d202801c41e114008500340c14a5822650592022504030b4095540c061108848100080e2180303881d01c40c5410110703102d2181100c1c011b040d03410000700d590a021500c401c1e0f0b0070741040c1d00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 221294271 1250 221293021 221293043
    0x115021c0206040b1b0a0309050102070606080f0601050105040608061c051603020a17071e0302040c090e15010906050a03021e0c070602030c060f13051e120f0403020405060d 76
    0xc08002c0d95058219030403150781c214070000c910300308580f402c5414000d8400401d5860000285000c0b009804060b1044600350f40030301050000400718090304001d440b00e01c0050901c003a6000c2000e190020603484103060040400c41440030396031181c10a9032010341a0b8a00e64040c0701405041c801545d50700b0b01600718041c120850101218801400c0300305d900880c0c0c10813009031921131019641e0040094940701c0c0d0300403c82040100b51110007a400d184840080c8040a692070b008102507885014442e0000303440282c05028444a140c0c02540092000c903003480c51807058000070709143e006002c0e000c02e008000c9844181c19200f50121f48450740c0c0e00484a41c900124405084107400c030810807041e074040c064012074200d100006440840810000800c01501c45466100c41741c4c0c80a400b0341078420a4554810120b075040014880781c59689549141b01010418449e00300301c121981e0f000d610004000c44e81d140481e0106403025070350102c4d0006102d485200004031031000030f4000801c604913070 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 221295521 1250 221294271 221294323
    0x3070b0411040912020c060418090c0e09010902100c02010f0e12030d05090f1903050306040209040c020c032401031203150603021305180f15060c030403060b010203070b011502 77
    0x1307098001110403040d001c1365880840310042001d1400313113014401400500000d0400b052002e40c000358552805202c0e07440c980d47c1c69070360410941c04100e842c84a143c0d164150101142855071040c2c041030300d14a429540b407001036000030051040003d1800806c10300200034600d650390a05030b40b50b0048064100e03660f403025121900c0c040c0c102284c2c684818003403036482e010643d1012810004c048a040b0080090f41c0d15036130181d4a942024210b0b03030b0080e03400d00100029443c0c1e4031036203020723905030b400800c401407001d0101072500720450700c803469030303440c4221b800c551052429545055981c40815a400401b400d001180100382c0d40341b0f0b904959646000005059030075a00903c81a03240c101545155921441171040d80c0300030201e425030a464140000e01f00000c0070300c9481d000b0507110300800306207010100003034881e0848500b081c1c103600002410801c018030761055080b608401e00180d03080c8049900c440700c0f1640c0504c9a445001441b070000044942b090180e550200007402403022a940e00b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 221296771 1250 221295521 221295533
    0x2070b040507050303030c19050918060406080705030d031e050115030c08190c0207030615090516020c060a020705060d0204080f0c1309020103110c0303040b0a02070503070b04110409 80
    0xd4030103407614040c40001240e5030402104480c41000e844404030714100d084d54130f40c0ca0078a4200c443c0350400c4420b1048a4103070f5180100600d140302620311360640c82c10048100801c450781d035400740507103034072a150400070340c4c50202d201e1201500d54100094800340d611020f071381e1011201c10208445e80350900110303905484120f0b001100303120707903000c000c05100f000054402d1282560150a050046e40444003015100d03000407000100078416100344541c2ca6843c01d00b9140148140c40d141c01c1e07000000d000e048990322801303034071140900741890410340307101c0b0103911149540340b06402032000241a005544c0208460402841b0203010f807961500c2205102c002500b05000344090303406410344040d8050b0001410f203840d5080107000b88419090340c03044c00001c0811510890516450b0081810108100000f03041c07034406003806540d891409241445412000404180d09039105008810218a0000a440c640b07603000d9117030032445e16682884080481d100340d00b10742c4642010558010030030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 221298021 1250 221296771 221296793
    0x2a010c080708040e0c0309060f04050a060e030c0f0c0a0504020906040e0103230d12020a1205010f0f060807140901030905100f060510050f0d0b130615080105090f040203100207 77
    0x1000c920702c11251700c0d02280002d180c4001e55880000c1d40c41500451301c0b850390141c8080d0058490422500c1180c2ca42d40c0e41000d072018142d0306015600040b0700c224500c42e09012a1015000ca840542900e5101000160300c40d100e60040302d01a550104000c45d45458110813a8090111500d5000341981c4d06d00d41500403668040c890382c03070b008491b43c15502c01040041d007502c040e43d0588811000f411201e1340d00009420403c2c0450030003444c0c0c600080c22002900c40c7c10b0183c11684101c036103403400d2004a01c88455184c0c41070302040480d108021ba0541d12982c1c052402c507110100a0761a5440c1c00100c000d0b15200801174803c0c06610240c080c41100c581c000b2003c002e4128051058960342e00402c500d6415640611002c6101042a901c10320b41480090031206110200050b4004840021410350000c6d0503002d800c040e41c60800b4001002c1e840d2450b0400c00d441d01c0c000d41c180d0f040c40b000c1410b00c10060941c030408400c2c0400706046503000e106282c0121066081103480d00703014140408444 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 221299271 1250 221298021 221298029
    0x3020c1504110a0e070c020307150c1b060203031b04230405010605210a091a04030801090c09030f0302070e091522170c060c12092a010c08070804 64
    0x200003481201c0d00350810ba02c3c14800c4420400340144590b075442c000340d0303144600c9942203901d80143c99011410b085514184c0b103032601c1554078071284589501e411070310050940c0706105040701810003004210303400030449500c003407942c81258052042040d0030101740211380000481c0300c9103241105a0803041084032071070401c100c0701032280b40d90350001074540703100e01d4a002101c00d800050b4155110004158143c0105080d0000910b000c03a076150a11000103054001010350070003410b010515900201031800f402c4c452404100c100e0306500068400f054902c030040241880304044002d00d0b00901c0848014140d02d00700b00c00c1840c00349001034860840f0340b10414005601000700780140c0d849031a0302010340c454651003030000c0041d26101912040045040d40100c0100001d441182042c4140c80c0205440b04030b16845d0000c07032600c020f0240c0010300c04800d5602440030b012080002030355951802c602c5d40340c1c10500350070300001204c1d0f069400c480940348420020b41e0304104500b120040040b2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 221300521 1250 221299271 221299283
    0x306060b0c0d08040b280c11071509030b0415060803250c090e03160803070905060c0d030b0a030206040f03061413060b0103020d153f020103020c1504 66
    0x90304141540e000c41d01381c401512900f1a180000c80749002ca415543c00f25540742144004d090207500c41c841903036810125400003603913900e8102c0d8480300410081c8081c1c400c04441c0c01d0890584c000082416a00e440060203450030840800c00f84403d1030034100c0701c15a529410311110380c850a1141c1d8a5016890340310410a0f0200c4100a85040507941000554072480d0014003c0c030340000311380500041400c49502e408100b000f520041030a11103410301c184201140c075120306d0070007401741004020b944454045c0c042003004c01c2c240100820084602025030400140c4044400b002c5610b0f10590380000390003000010340800c24400d2024203004a0b8401c0d603003445840c0c905c458080300a0006d540003486039290328030001c0041d446400c101ca421406140060802d0300c1c2001c4a802d850b43d419110341c44919201e400c0c009084e8443c41c20f45056003540030801104502c0000c4811440b0f8034403050b03180900b1035041c030f085a11a230100c50101d21514111a244090b0081050341c0d41020381e411100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 221301771 1250 221300521 221300533
    0x301090302070e450a060608060c030c070b090726060c090a03151503060c02010b0103020c03121b0a1107090b0f01030b0a0915051c02280306060b0c 65
    0x83c0342c1d5400c12a84840301c220600e03480308a1188980070b90f2120700000051000312130302c1c804400181080615480e9025000c0480c0607071900a07400d080c11000341410640302d20030010421000190380803101601d82c08191000d0320342c0c840743d8030b50078036809030012506601c2c08000904058007040071020304030300d094191903da46602d103084145102da00030301a00003030200f0341000030a20f2030341d07420441100050082088101e181c226103100d10260000c440e55686c40c01c1000b03025609115558800000782070451600d61a88022541d0b4019400704025111281d400210169842d0703c08944410048418588803100004060302203c1e10300c4480380c0520490000064407107590140b481c1c0070320041d103c80116000d8100450240881d6141c01d50009032501c00040c801880c0c1c030440400402d588484036645040008008001616a020341c018400d18a4004050703a1454442c01030f204040700002040200c090070034038201c10543c0041d06007403800d04001120380319039005040014a07801501c40c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 221303021 1250 221301771 221301781
    0x90a1e03060203131b0501020705010809030c0111040602010b0d080d0f020904050403050a140a090e1807060809010609020c030901030c020a0605010909120201091a1f080d140c0c1c020301090302070e 87
    0x30f03283c5c3c0030702c5002c0c0140e10820040000394000e03d080703508006e0000650345000c01d0103e0460a5825a0306404559030f400101005501d0342031041c404aa4012522041120031586400810f80a0040c0d80810195500300e105c03c2010301b58101c0e040328501500900840ca0541009015a00403d0022000c03c030070040601042c100f4400300c9a02a010303441d01c0710300c00e04003014401b1110004180390851611807002d042c1017141040880001e012036610740d08540f03000e00c252070944a050b400300140c240140400b512083c0c0110580c0c044807020b107030018007100420000c07840c0900c003400c003130701191910001162405480e0450001d8600400174510400d011210803400c80e060f096001e0f11b909004030f42d0a000c0d142c0c003401290001c080101070721a04020100105d8004003651001200381d01c02d08070b1004194020130035520f60041c40d1102802c004a540b00ca0391602c08554030b040c840c2c05503d0b03112485142504544030307c05d8002c6c00030011103905180282d07031201c25018210090f400d500c0090 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 221304271 1250 221303021 221303063
    0x8070e0108150711060a053112090e09030a02120a0806041104080102040905180d05120a09061103180c150c28060e0102090a1e0306020313 61
    0x240c1211090341c002c128510032020305401210010300b402c0200180c1903c503481030780c01041707514041c4800100000f010b0424031000098205d0240c0310012071800b12510702c990300c0d400320806040c0d98219645441c0340e110703100111120f0040f038101c581c02003444e1060003c44200040034124404103070302100c5e00401595030310804e03406059040c070005540b0200042d0356003415089440040c0448400c6420f00340c881d4041402e91308030f80c201c01002596281000000e559518000400c00910406003a40ca194582c0041540c0308a401081551280d4400305071024082d90100c00004d4024000300107110640208180030b61040d1011043c454504030000003081c00800d14416140c401001e00d049000c014200001c6a000b0185221150051680024001040510341f00d240b10724040002140c400d2451b0007011140a80c0c00070503141c0c030500c0341100035140c106140b01600c0310080800e2510305102640e86240e11641c100618460001c010700c00c08203005a03132110a188118580d90540038240601 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 221305521 1250 221304271 221304299
    0x60f0218030c1234182d09020310110c010b0612010614070f0b04110a260c1306050907110c01082706190212041103070909240b0906120705041103010807 67
    0x4014100303c1c6c83c0c2c0c1c0b002914030550003014007a1014090303820160341d00c600e54013102c01c83c2c0c840c0d0380e801300c001501c0c040841080c07241d40e6503401c08440301800e211a08001260b00f4505006000900445031641070304680110280d4000d9a4842c407041c240101924180d05401c0003a10215508408809104070500d0070001c4d031020384d203c04078210120fa88a0b0a84da03070041700301b28141d05500a00304002069100c2c0301811501298100c40030030150300d060107001300702c4001090802000142666565040001300382d070030078420300b407824845613151104000021411004d92480d0000c2101070fa4102d8803010495a1140216101c04010017001c00005800d81c40750803006002200e140d40041e0008200c140105025030014084800300ca8581940d030044030300501064030359200c03801040c0004011441c000c0e6801402c0c00c41400080302c0030000c6203045034080c00b0944510100c90b40040c00110800c0400e000305001401441801103511184000750300a0180416500a221010030807041c00030301 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 221306771 1250 221305521 221305571
    0x30e030606030a021c020603010914010803070809041d0609010c090501050909010306051b040612050a0b01081501021f0902150304050a0f060f0218030c123418 70
    0x83c0c900000150f003002942d03490341e0b4940203820100741460300941c503004e001c0c5003e080002000942d0704c1c85002c84c0003081c00b05030300c40880b5502c20007060001540d44000d4a100840c03e0b18081410f8407400821486c18202c40c1010038144618010444038810540000c80401300b191100e40003552540d004403240d20a00c42d030b040d0030822000040000502541c0043c0d0321070800b405881d940c00c0000b8804000c0d0b80690b11010001c0c0020f120341d2804079541c8102d40d0015507900040240200d080300103403040d00700500c080d10055102105c216144d000384110320122840c500c03401d50b2030340400380010060203000400c2e4022040d400140701202e0690048034001d54010b4010001c000e5590b0f0f0303100004001883c111070060f100c0c810380b903100300c0a0002c0d00a641000ca0031220406941040c9403400c40c00c5007815108801c8107076211800100820000206440c003140c2402c12034201b00d900c0244488400044842c400c0044001805400030302240c8511541039010b208a010a807401040b8407030001d4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 221308021 1250 221306771 221306773
    0xd0e030a230f03040503130e01290c030f070c060309020901230303030106020f070f030317070207050303030c071e020906060a0302090d031e090e1306091a061002010917031e13030e03060603 83
    0x203080c0801d148052b18a1010070608100746e8603002021604c2411038102050b54600010041008010000302643c03400182241d882d01f004940c01503000075541010600c114080c00b00d0904c0c4169214541c0c40c4c01c0e031412000942102c1c1e49580d6240001e542e1101c40c8403110050080740004590040c0c1c1003404400c984d0140e81e0000a41d00100e100d080418014001c9010743c03040c3c4500080945081c4040c52003070404031400d0b40c13a520341d8203006101c2d960f0600a84c00c1603443d035945400582d145090f10343c102406480403034607008081402d9009118076450183d1105501d6410401c0561088913510b03604c0da02d20340841c01c01d0820500740c0d01461280902d9040b031303076020002004800f501040344c8465001300c00c08a140c3d00c1c070740c486001220712898044121f24400040290608240111100034165031001f0000d45026071a803100f070001403000c1d642c5501300007001c190407410700400348080107030001e41d00e01c26080501e10000042c0072100114082003201c0f202280c01d14010035040d10076003002d8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 221309271 1250 221308021 221308049
    0x10e01090b01050f1b07080601181b021b0120010606020c090f0705090402040b0c060106090f0602060604050603070f0803030a05060405061c150906020d0e030a230f03040503130e01 79
    0x45000e005d0b0725500d60070040c05214100c00010259010004503000b0b01003903030194415005905550140c3c0c1c41c0a003085099041414040720465000a1907484411060040c5d664411f4400040740c00c1c0b281c0e004a5107480414540566800ca01035110400710b541e01c2c0c08450104403c481400b04c54041160011100c21032070000500c418001e078010807100c4c800520040c90941c6821010703546030080346a202a50348040018404c80c0d0b00029808050981061860425864004025501c1e080100224040e079260004240141c8041024030003500501442c903168039262030516540e6042111010340e00b40c00c1801003001ca050034407406004c0c0c3c0f4041c103d90365190070a01e0300400d500c1c900801325180512604105a482c0c0340f88100800d03c1c2c820175000d070303880c40c1944410b005d40324456000d80054204002c10301c4a590000801152100d0700d6048217240160450342401034000c4040718084035400108000c10010b000c40103090000c4070710041c5c1c010300c0d240c020413400207a090040c0c0230800102c0e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 221310521 1250 221309271 221309287
    0x30503040609020a0e04150204080d0509150a0c1a04030509090402181509010b0f0a0f1b03030b0301050702070510030b030c10020f0f0d050412050a0209010e01090b01050f 75
    0x14001154428010000880c03003500c02e90100d9028501640000301c5407280d81c00340300c1001903d0400d2035105107820429414030303040200664841e140151804244000000d0003509501e40c000c43c01d2001043d001410389030407214101400b0b081c1e050034101e91005a20b1005500051036008050169070185d4500c1c0c18203a0f650f090011410b0050401d03640908075217201780c1c03e14030546a40f803250034800a0140c00685410521000c6801a0468103c11905111807000ca030b0a0205451207070580c2c0c90000e8180d09040740c151103481c654650b01108400c00c100c070209054150b08040c100c0d56050340200300f00d5880702001c9840d190a4007540ba40801081100504144650004204850010140c40362081d003900000d608900404054003d604040402d0700b4404081c0044034181100b423000c0d0140660700e080080c12481076008014507036031403003044818440100038040c0b85543c0501007100658442401d030b0f088110034464122182c1c100106e6114a5100700c0c20341c2c402c41d60100c10641000d01d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 221311771 1250 221310521 221310527
    0x24030c2606010e1e0108031b070305060f04030c05060f04110103090b01090518100b010305070c0c0303050d0f18020f032e0b060703031a090103080a210c080a0501050109050d03 77
    0xd4400640c42c031130300301816409a40e21032214000d00241d401159210300554020841600e11501204a032300f186d4000c00102e480070844960141c4802001c010b0740c4d0300c525040c0c48003010040083e21178401d08040010703030341d0821b1065014500a42d8945c98400b41400110b0640700b445000410440301c02c00100b004240b560025900328100c42401912070484038000c0c0e16081407110320100c0c050300c030004441c40c0d507018414507401000703c1c60304000e120b55944900e440c103078a80c407005040000004440d188031185500c90300c241501d143c000c0c0102004503181c02c4001614400980c440c40c00008404a00c2c680054075490000c20041103040d14103404540c3c5066000c507a6545614035114900010250b440d4001041d22a110b83c40000c1c8040451001426440400707030000e0181c0c944400500104030890706840580307046240c100c2d40c3c03900d040340a040f02c050380f0008620ba10300340000f10810941002140303105031100102041141c0c0e032900111000e03d1a8070446400c28081c8076003402180c4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 221313021 1250 221311771 221311799
    0x30d0507031116060b0a050d080903030d060303020309100813080c0a051213210204091419031701031a0c0405220e01090302060a24030c260601 63
    0x120506001654518030001145180c0c45120030035219440111083c00308401c1d03205828141c82e0aa40580180342400c02084514100c0140500921008200315203540d5003081110440040100c0030300115549150203552600b01440140c8a0900d100c42001c1d034610520495210314808448204003940a840e015081d50245005625501035840c081c008120208981c0d8400d4032070301e9200360f5071011070182c1c0d070307000103142c0240020072881c1c1e050000800e40441c0d21869150111000a4444c40754a82039040134640040d0100b1030082d0b410464410041981010380d0324001d8540c6185002d4084607442d1188007408010302440c8248211b00042c0301240300c0a1f0311078610309255151584440000d00c0c100f07038072405200d0086401100c1100e12486000304604041900005c2c090543e42d980c0c080e448480003040360300c0f25a0342f000721501c040e0302410070340701c410040d4000184e100c1d102d0400009400f41401090900305821010094030724100f50301c4030541c07404078082c05403a420480034080c0d4407 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 221314271 1250 221313021 221313031
    0x12050d1e0f050c0105070e0a0608010608040201271509080a0803011205030c01020c0313060503070914181026070b0f0d0c0906031505060403060507110304060309020310020309030d05 80
    0x101c1031249003d9404244a00360040340390340ca034040c0d0140791f00d04000810103035810400c01c121601004011450300f200003150402ea090030101004401110b0702e0321800d0340034541d500074559124002404c40c50034009a8040e044036510102c8850322030400741d0703480740160001001284e0400040100040710192894110311640680303280240310401b4500303a8102a0302207255400024445e4015100049104001c00490425030304500e803000300900076802c0c41c800c52020382c0c407083e0128002c2d9903009000746118020484840b8a040a804c420030401d0207001e5545983c2c04001500038410000c45001080d0040d1801001c1e030f83d0038000d608850b5009010340b0400000140080c0551842038064000d11400a50b1040302003450580000c0650320501d0078401c050310704540900c01a140e010459081c0d81d04a01c1c003041c2526034580480305a4011030b549641c5000c00300d008504180d1540201c036605008400f1603080d20a813070148d404070310058a180340564400c0081b28803104a0307400031381d802 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 221315521 1250 221314271 221314277
    0xd0c08030a062d150807030e03130308030907080a0b07030c03140906040b01050103020f040504150b03101a090d020904110301020a0f1b0c05150903030412050d1e0f 72
    0x100303a58011541140c0400c402c00d4042058403805140190140c0440300c3c01803900b41a079807400c0c8114200500408000f0302000f0405440d42c2a05180c600c00f003044513000303d9034444403010103559042c810126001914001240e00507100d0000300341500084862225410800700100354036045000d800030001c10003034400345070320f075030242c140040800350b001d105441e030f440600741915040c60107212030302050304140d060502c18000f183c0680da180d419a401e8580660340010101c0050454031015626580134100c2c24070b0003c1004120b440506002c4121448070000030743c00c2403800340304910340c06041041d94100c00010b42140252509a1038950010b014113080321160380203401013426644990088030100b08140ba00500d0b00354040c15880500c400e18051104101b61503075410020182ca1240310b1040741c0c41c410100d441134911048a00481c0b0040480b44c1d00c40c0c2d5507000792007401c078141e829607403401800503483c0c4070341c00380080724410542c2103082a40030305490404c2d00c43d181e41c1c08101e410 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 221316771 1250 221315521 221315531
    0x1e060c0c150c0303051305030316030605040f0c080f06150304020f100e0a0e0613020f1308010b01080f100b0a020f030d09120c051002030c09030607090e090d0c08030a 73
    0x11949014000d29031001d840c2c2e030b100618103040c1005025a08064401201d85002c1c0301108003280f0080142c2e6006610858581050a215a011000780c002500119800703864000c0e60341241c0b0a50b8400f0403aa0b0680d00e42239241d0b940c43c101035000c080200e0300c42e40c201d10108102c1a41008407030003194840d1004105041660900c404a8080c055450071040414601e001b10b0100f031510407000402410440c4103c44903140105c04070703d80000209012000a4021030303080d0800d1401c00a403084501c01c50000c4128682c4c41154901809c580d0400502240000d80800c91062040e8080c501c03032040050301c01e06240c42c1100e0400b0943c004260b0100714051096440c200180a0000b130030030700b801200c081500d05103030034403506c0345d0b84000c070b800103000c40d03025044d0000e000842c8001407090007a00040c6c5079610403003a002644552480719525008000070480c443d0b4001d011403081e60f0f14200c43c040c07140e8071981e902c2e0341c40046000060103d003254816000080340a001154415142c58021034 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 221318021 1250 221316771 221316779
    0x303150619080a06080a1e03140304080d050105060415210e0618010c120c020a0204050906151e0d0f02040203040f0302010b010801050a15020a0506150301061e060c0c 73
    0x4600c41c400d41094000a5801c0188021840c1c240221400341900c00b02601008034076645000194441e4121003100c900e64a05542c113142c06a8461031850080030076442c1d1f40d24040c07a00c0e4400354072085d04020014984000400d80f400c1c0340c41540c040e9006812204207502000a042d5010115a40a00c0360861110300c2c040c01e0448502401c00030b114010010803641c10702040300881e007a1090241d5495078580480d00c904158003200d105142e0601d001d00142c091130034031089081110b00c100c06504542407406002c0c3c3c481001441c0c0b41715000e404804445000d2003810416580710204107a01c40b49100710003101c0928200c01040c152038030550a0302603600031503000c5000e9810448064a90b00c1c8190342c0f01041c1602070154156000c0240f9018031550305000010f01d040440c0d0080c2030030000e0602400d020103008200c2041500d0308103007100e2451030407401800c600710700402c44500035401c1a20000d5500841d640c0e03080c041004040840e030150030b0400c102c800055185094614040b000c400107 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 221319271 1250 221318021 221318047
    0x509010603080f280e03100203040f080c10020307050315010f021209060705070621050123030a0212070510050304110103090503071407051806030c09070e0909030304050105090f03031506 82
    0x3c00404c42d6600c0e4080007802c1007081508110a04044050090040041000207481440c18903042e07580498034907112003000454500d44030301407124205142c030000a006880342c118002d144030301a99001035040d00c101c84011600300964031040300240e48020f00c0407402281c1c15000c0c0001c12070180030305041000b143c940034a003090680c8801c0100e481400110b101245c040824941004500c00c01e10095151910442c804940c01c0c1100c4511215010680c01c25501401201a5190004d000110b441d0a1250440d1140c8582c80f4451045414050b0031003000c5c010800daa1107203030400c603ca02501c15001c019809051441012541c40c041001140300003504980c2c0f40428090b43c10003009070a040c44180180a0400d865140a81c001081049016035000031041ca0445055602c4000742d1a603400a0b949134100162865200b507500d02006011403000014611450041c0001e02950300c5118a55840c5d4000046000b41500200700141255100c2d0002c007680300c901030010f0303107451103034000c003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 221320521 1250 221319271 221319337
    0x17180a050a06140c0a0c0b0c090d0606090e0a02010206040f030225090621060f060f0605070203060f160c0f0605010e060111010c0507030809010f0e030307030509010603080f 76
    0x100d0302c00b665424110b0440240000551380800c000d41404d1900503001e90190903500941d070000c02c00c17007180000414504008003902e032001c20151190000c04400c0c609103024081c0c0d4040c03006007924101604000150005183e0b04050301038001c0d04058480f0380301c148114005c000b064055200e100d0440113030b041070b2403a0801c4c08041c09100c0401d54109035038403003900d03c95030022850080213007130501203020b41101c14481962118001401c000329000c08401b8210340e070b00c0f0402030703801c5080c0019074a82000052107610b00c02c4060701c00607030b6010303020045c0c3c01c004e440c42e91034211109100044140500c000d103034128090302c0c201c420b01200e41c0e00e1406880d826008000d010010354240f00c441e5821010044440e0b01b40d500030301c0340c602d445200822a008119002c0e033040002c40100341d9491081d401107500f0760000000b80960351190141558030390040c0c0d840b4000078588000100045018807035001a20b9001b03c505150440300c2c0b07680d68007508100703101032151080ca410041c21043c81104 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 221321771 1250 221320521 221320523
    0x11404080c0f0610090203060a1806050114070c2705040f050d080103030815190e06210d0c060b040c02060a1109030606011404080a0b0a05010617180a050a 68
    0x15269075984000440b42060341c00d100004031a0b2025041c000030a050342c0458013a14446140186c4980d503450001f0f03400d00d8a41c2c00780070031000780c00740c655105c4015000381040d00d4082e29105401e00d40c00c112004980f1a1000c00b41840d0b40d046418000c1f50b100075651049000c03460389042949c680700003441d04480d4265821200307120401c00700b10400406104035085000306007014455585140c60160446400520781400740b410407130540c0c1542d4690a0048880ca081d00c20030319960b481d54004100418181c0b801481244207101140700c0c03a030401c0081002c1c0c0700c0c1c04060140468010000e54140c003203c0000c0350314a840d0050108503407a50302c00c8058a0308154003d2107281442440c40c0c04441c5043d6401810001c00c204011041c1c4001072126041b84081c0b07444001d03002031401c6003441c2d00858000446c14040c1c6505030081c001a510a1402100b16960410041c2d984100036500d00c2032040d00c1048800d4000c0c0016a012131050105229a200f0800d88000b0f008641d119400c3c08030640b0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 221323021 1250 221321771 221321783
    0x2160f050109050126090304091a03060c04150c1109040b1f08120a090305060a0213060c02030604320f06071103070605040305090916111603020d05011404 68
    0x40204501c0da4841c51400040200b820561140c1803006010000c54128920808101c0c0c400000310703072113810800817070b0001d1010400801c40915407c0d80346c0120301401241034840d11500e00810b01212840307007101d0850388803144d000d116201309001900d22045207071090b54801402c2c4c072011080e44900e10003c0c4a24410b911134000d81c6802d640c600100107840d2810b01c404241004140601c000010f695414055a200c880c0d880b04003145040325014440d0304000c14a020788000d02c02c005110f50080c0c4210b02c14100010116611064203d90349841994080d61590203100800d0108070610036400d07040d001903007070f0818a06107401e400c3c46181c0c40902255554001080c1c11920403041c0b201e10b030000c803103180c00100300e41050b8009030380e4000c80070054845661100840c0405004d44126000000d001c0d00b40d407000d150081e1015582003075078617140b0105036110700c03005100c0c00216406c1c5200c40b1400310140f1090441e001e110304100c0d00d440403152990380d403a80001d5081c0b00103655224034402d030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 221324271 1250 221323021 221323049
    0x30405040f0f110c0703030815030a030f11010c140703110f1f050c03010303050307051603050403060c0801060906110102040807030b100f0302010e0d020319080a020114010f06030504030216 83
    0x107080c6008582030100b03020510300052014904d07440d004952030084030380500d070005154442c07170118a00040e0440400f82e152180c3c860100c20140c014850407004d40907502c464144406801c1d02c039007030b613641c1444600090059034640c848180700b113015001b04ca0080c68502c001810161101e8a4010111611201c0707900c031001406240821042c0d40b06010602482400107041a14003c0e080c2d010600000741441804400103240701d01c40d205841030400d50703100c094803450303050030040c11540c0b0601080e1201400c2188000d0f5850003000741c14102d600c03a40d034210743d061030040104d900304001707040c0415554082100080d11001005407401850040c8038403040c0d4104480d21a00d449640e0b40a2420101d1181c41000940c0e0089500e00c0a4001a1501c550004041c40083d0504180300648148810081048000d001c140c034050304603203005400070046000c0014404180075800d01c14514100b003801d4003441002e2194100580151081c01261003220614800c0403840c8204d800052801807c8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 221325521 1250 221324271 221324291
    0x60507050d05040c150905030303060d0201120207120f0809060c0901091806261915140f06011b0609060e1b04060515030a2d061e050907030e030405040f 67
    0x1172942d106900300a828948a258941400b19441c1d000050170580304004011503003055900071902c1c400c0e491b01c11041155034844074980344001510071800040010445c030b4030b0b030740301a00409e41c0c117010b4840c030b2005060565860301c10801c2d9900281c8e40380e0420088040010326081ca058a0145c00344581d0300c0498140e00b026102007043e004c0c1005610381c8ea004c000784004281020034201b11244200803118162800741c00c003540c0750619082a00440d524003105800410440c0340e075075004071003240e0405c645480d48001103648010b000c10040031a0040d10000700058200e40c40741c0c00071441030760040b07034a500032840281401c03c1900070801c000403680c0b0100c410301e00b40c418200039200403a10403895112149001020f804018140d1030301c1076851094145400c0448030040b5010010450004240c11108118010b0881481805400b103600000f175200002d40c901d01c1c0742a9540a08200c03025130700c2000417001742c40040d052001901040102080d03640b40d0380102c114406404501007150186 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 221326771 1250 221325521 221325539
    0x9030c0b100b120c0708070b2a042303150103050609010614040911090106031508010614010f181706060a03080423041a031c0903060507050d05040c 65
    0x4004039664040d4600510000081070b041d540e900c0b0300f05844102c10740c0d90469940351881164000791010802180710300802c242222801e1060200e001000009e000b00b240ba00b1011031500035000028030140b20901026810029405000c04c0524581002c0710076a4042401c3c1040051f1000310547e1400044c400c0c480e04011031600301c12200300070003c0a1420304400f0300207141251071031003541c4605000d02400100000c08a000c03000504072809560f4420300a030050117010803110143e1200c0c41d0029500c41d0610880046030010803181002c4a403140c01100d22890070f848620500000c9400c80c1c00290000c00884090611035032204c1604003c001442c0c5044001403845115640290007070000660000c181d90440e000a07a80048541c442441090404144103503140c00a10f441640070059603d9100101040b03019001d8542c020140d144000302c1c04d07898144800464500e0008000250440e44103a40c0103410346032a60920b92156050805d039501540d043c0c0d07210340d00d0344041c044180 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 221328021 1250 221326771 221326793
    0x201051b070201021902040f14060f0f090406020306060f030109020703080a150303030e010b130902270c0a03020c0109030807112b0203160807111c02150c0109030c 72
    0x1191110311030400005900003035550280245820100074400c1d00d2408540b16500145030794185004244100007181c14280c0014104540c0d0910a5070b020201010728180145c200c00850005001822039560b01e41300e40c40070b9030028150036003003141000b1450103c0100d4010714060300c40b80302e000d0794920060400521160004d4010907066140450034002d90408000c0038003100e80c182008102d409210030400d00402d82081c0741900543c0f00302d072501e101d101c140d10000c5054800c480e000c481151180040396000e0084160b82c84452802c07021650055054010340a04030315403030003514289003140000d00350b4429600c210042228030050105094028899101210101c0010000d0040300b04500f070340b402d4000d5110304041d40a00c80900c1462007841120052584074a482c1492140c2e481e04424540c420902038440c0c1c41c2880762400309140c1302d4800440000520300e018020f6a40380c00300710b4030300c10400002c40303121020005003090107401e002d4064078501038bc4655869100e0b504040e1000c00c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 221329271 1250 221328021 221328061
    0x10305061b120708220c05030d09060207030807060920130c0c1e0b070f0908010203100e09070f1404050a0203072003040b030a0209010f02010e03040915030b07020105 73
    0x804280311001c800304041080b698004400c1c80c104003643c9a0b14503449440301c2e00c240b9208060469404402484503001140b0100c0d41c080c0c00311803035a045464110707141803860040e10010b82106008102049441d0003600c03445010780717000501c882c81c0da550402071103010458400d00c0c1c2080141d0326200d2410400214045480321000c1c4901540100010034a07584903030001c20b150382e03c94052148034160012808569448541c0c00600c0c10320580c00351001a01c5d00c0f1312030000e181c0384004a000761060098a003c0c02c841748442e02d100b0b0500400d26810000140081100d01c5402d0001411805440f80b18000780071200550180c0000c0c00140b10035180014151114240100240007243e64810070180c61180c0104120780d00c0540354228031700710320482d804800f50391404024003254900d590700400c8000000d8981c4001200c9640c0c05900b078071034400c1c007229250014001000300103010381164842100341c10609002503120303620030361070201c15500c000050391746e40c0801c0300d42e03108032070f1907044a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 221330521 1250 221329271 221329321
    0x13902120703030f03020706021209010905070f0b03060103020304060f0f020a030605180a021c050405030301060f0c0c03080d020702130e1204082d0102121f06050f07020a0e01030506 80
    0x482d0858030068403030501e14900304100340c0d00143d605c0c1888260340c155180f2000c90f440301222418011075081c0038101c40e41042d111802450740002d00a23107800011012141c000301860b040d0358071600190002c0d0401007083d0b0710640c86103100000240c00e4420a05484032100b00161540440c400083c00c0310a1034011502505091300c1404105031110381d2290720100d404405640da05c0344112661580107217245c403031501814142444100000070010f14140c5416603141071480401d494116440020403401604c011541003091010901200060001d0310f0285e40240c0f5142807940410b203050400c442c0403002c2991214800c2e01c250b07007448044140c100d00201c0701e00701418401c0c07594071008440e880320003910747d072414049500566484540440a0303040215221403c40710350b1000d9200c00c48642c41c0c48602c0191942c030710300001c1038076019a6109c0d600d85040800d105996a03980c2d000e50303400e0360302a02c1000000b0b4654071020105010394420b40248c41c403803c1c80032016981c0d8500105002c030b8 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 221331771 1250 221330521 221330533
    0x6180b10060e09060d020a0f09060306180201081503010b060f040f050f06160302010f1a010f050a0f030513050708150717060d0f020a0909050c0301091101390212 71
    0x10765a440c0f65941d0048002c0310700d41090400f40c400078401e41c455038880c1031030b0100c0c0c120000b802107240d485481120302410b0700b03000c03038006000000c1284014481c0240458450307c049902d200ca4990462440e180c040d0000520100c00c100103511600049202c6500b0300c0002400d0044e140e4003c40900103000c181c0c0c240c070000992100080c40c030b0245440300002442e14079542006d1503c00d40020804030700808042082c080c500700789006054005144c24023044c10295803c032180d04c0b40c02100d00c04803d0f95200000500743c1c0404034050039001c0d040d20142c0c25840350510102d0820b1103a0350080c05200014901061000728040d1b1080004081000703004a600c0310300c080d1004030f8a5aa400141160340c0001e020035881c00c10004c0e104400069000071010401281800035a403010880602500868511005403010076099810210006022502e42c444490300e950080700c42c1211540329101081213030b25801a41511542c1e840c03400b440581c0c02060344419424400b11251b0008011009400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 221333021 1250 221331771 221331797
    0x5030607020c0915090711010c09212603070206010b03060612090a050717010605041806180501050411120a21020304050a120c0f030f080706180b1006 66
    0x501d41d00380e00b62aa000d50a0040000c2080b2880c094880b41c0000c020009a00c5082000006005440c1c0c0008180598601580070b001d650040d90484120b42c0100700d00d0f044100000c5001303c0c20100820100c0c2d40c8260900c0c02c420782c00f41c2c4400d483c1100072003103c1b25224503049100070b1400d90184d100f40030903001041070003c0c82c0c071401c003194a054102074400c91281c50f6444440d00c1c012550380007038407500400f9030120310b80400b000040038000c008002440615120400c0004072040b0070300e190300c400f103038021000029926803c0380f00d0032182884079a0181485498040c2580c0048a0440306c01c0c00114012103d85040f5419110b03036494080182005c41d45a650407403001e0812151210314001c582c0d03003104180c800c1045501514000c4e168034040381c0e40e0000c40040780c405020840c2c401804c2d807004070340c1c404540070110803030790441e4182903045055204c503c81a405550207442342030f262460300f00303000d011040000300c46105028500b0203140c80d9141c80904403107600100704100480305000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 221334271 1250 221333021 221333023
    0x30e19060c0816180b030a1406012a050a0b090304061b0b040b060a05030703050c210706080c090d030e0f030303061e03031902031801050a090902090406081b0a0503060702 75
    0x1070110400d41800f50601300071900342071070850346078404000b8841c00410013104040907009800005411800516952503410041d00c0c500c05200460303a40f90110301c0c115440358009142a0f40c01c42c001c00544483c00840e4641d2014a4030440e620b0080d83d0000808100e2a03504c003051900403041c007528103203910813030b960351043d40002820281000340c00001040cac0c02d40d56800c2c42401014020f017142c0c901d541da403918640381c040300c2041c0e0744100103101c210620a071100c0081503400c05181e0107042b4042c10540251031b400400b80c80320702c41110512031f01100362224508114030900a441d82d25062604a042007a410000701c03006020b80c00500130720509842d9404220307800c02d007841c0b280369005500004a4a9402041e01e000c1c0b9107c1619010006a0b03004001854902c517070058144041c1d81c140015141e0f03110700602c040c00901d2414080140801c25409030103803c00050000c101e466070744048a1070140104641c1e042189242459075151600c1040d20004160580107401e1600c3c0401c406 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 221335521 1250 221334271 221334301
    0x109030519020111030a0f0e0f1e070305010c050309010b0f0f100e0d0f0203060109020c03041a0904060915050906090f040218010e0403080109020c070510030e19060c08 74
    0x340c1e0420a100c10780d40d5814000c0d08604d042c08541030641e034403450800d81c6c1c2000b600a00d820070400c58902003c0c000d210308080f03884180d0038801401842884510182004c00300744901d6848118040c0751000303c0025002e00a11120f06160f47c1e503141c4904220104500719860580064481c020242551049498854030711729520400c4642c450309122129080c0c03200d0314020070490380207103c0a95841000420418254070900940c12070f1810fa886925401c100d1103555001c0318142d2003407008000c2e1070040b1214481380036242840a0402d692140440e055616641121070919158400011a42c002c90100382c01000106c0c0c0a80030382c2401d07008a85403900181c0050142d18014001030290340307600051081c80c003440609080d1660703441d19481d0b200141540c04400094918000040d208024001d44040306000720140c100309151504008070401010801c005168580820384040740d004d020b100f00708100c04007070306100315035482e113041260f02d842003090a11141006200c1040d01450403 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 221336771 1250 221335521 221335537
    0xc0518010516080412050c09090601091107020d050105010e0c04060903021e030304090f0f0509061f0f080309031002310b18040b03120904020304170a2001090305 71
    0x101d40da581000d01c050707401c500c03807034040a400081d0005001449a24041060550314060404e4a2a041c101e81c1009011041a110002c0d181d1254005010086107648524001d640c08120b152806141ea0702040c100006041c0c103591a0755548010845c0b416040c5000e03520405805200303190905000020304103001078040070380145000b4840c1070307051401c043d403038070b0415004084a444959542d2000064401c1008008841e1f0604001d140b41c001c150003245e01400c8082c014114079501c100e88101017031060307003c20000c0b00c80d820b00000c1c0d00d02e0008a0ba0050305518014565407640c2c2000e240c9801c1800710028095441003256020509489501e022061410b0f6050481001c062010160881864214555100000404100741d40045901d01203078142581e003400300300c42e100101a1030300701c0820000560f29041000121600d002d90045500501c600c2c00e02080759519105003c450300004000c4000c645103480004a540d4101100f03502c600c0c03410002c2c00280784036030f001809401140c039 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 221338021 1250 221336771 221336777
    0x30e1c03030e0106031b080d0305010b040b0d240509090304270b030d03090b13030e0103020a03150b040806010f0f050409031e080610030614010503040f080307050d0c051801 76
    0x1c400100b1800a4001000941d00030640b04030600b07141041740c010784060302c6080e999106952208191350f01034014627040302d01d469501402c0c14501101540c10f030b03214240700400a0b503212b12000c800d0601c114400c00c8200012030f28000503003000144001c5140c041c023103804541c41030000b04444040c4220703602c880ba01188041409110200002c2c0141401c0301506502d030107810000d61644e0b81c03640c4006904c5010b003a00aa60382c50f00c02c0944840c200351400500061200580400594003980003012456a24030b800280309001d040712800c85102c98001c40c003e51400101001200c3c420414103016288c5c602c0ca151100c1c3c038002e803082c01c21b0300e03030b01c80e150159807590f0058061500071390303403203210000443c1002c4030069a10700043c5003000481c3c1c030512511b91540003100f460311030b2103514191049c403004204c030888114010769840c0c100a004540701c84080102c00f0020700010081c5000d000715854086d160848101104280e4888900300c504001d0203210140c402c1c0105800c030004050207007 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 221339271 1250 221338021 221338031
    0x10b0f03030901180306050106020c2e030b19030809012006041b0305010e010905010606050a020304091d2406040b2202130807050405060a1d0a02071509030e1c0303 72
    0x404e101a00e01080d8000390036240390000001d8020b80108144101510031180541003201c1c0c0100079214041564482200300b20319401e00c41803500035030000c82e00312801481c0c000d03a0064000801c46201454000326282000424002c8680d60080d14510b00d0f0050700d00c050710322541c0307105030342e60b1043c1c000e1018140000c1110884d4817107803103501e100f000d10b4021009000001300c1e105c80b54040c0180c5c0313904480ca0740c0303401c0f4000740307080c03041040e940c001c5200c0d4040c5191504d00b019090240c004040c3d41c500c0e603000e03100b80240c0c03d44100005041d04015185000d000b07503403040018101d510080c0300c1401a8100740d1901000c3e5907529820100909040000ea45842482200d80090180d65074050403c1c10403c8081061180011314100701c80e4204c1d001d01440ea54241844040b00d100d101d650b4180c0e1030703000070030780b10213181c02c1c01ca81c0b1804c003250040c10070b10540c460f0040003102074010010b0700d64843c5400241503100080c11021a4140c82d00032001c04204126491b07007255002c0a81007682e61 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 221340521 1250 221339271 221339297
    0x2030c22021c1a0f10090e061201020313110301090c030602180a0807050a1403120f0c0a061d0a050309010c060905030a021f090c140402090a08060108010b0f03030901 73
    0x302e5220031010896500411460580071121051402c03c05041440f540100035a08083d162400101c1000d03401903480c440c0544c903207072244001c9840076241591020588900028401092000d1842982100f124001c011580e0401980e20328030036507114001d0b410f01e00b400c40071039607060550080320340c08840140d840a811040c00d07103800e500f0030b42c2030740030220b4800040e42010004041c0161403080300c02400391642c03000c420142c007c1403051181c258001e8510000300412000240995920501056141000c0d1070101420b007001403000715917481d0703694500404451440d81d01da003000c00350401030070044c286480c0c56589000740c064260401241c111588200100c58004000c507543c0b00c01240c0d101e01800340065140d48185003143d41562404404100d030404c1805840032898000001c0680d41e030505241107440c00c500c0240130f80158081001c4811520761002c01c000602846000e0141541400100d90940701e10b4818544245d034081c001e10107540d000f104464000c107090070070700d400c90302e9 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 221341771 1250 221340521 221340547
    0x803090d0908120a0e061209060105040c0e1011030f270306040203150a150902030708090601030c030303380f0402040e0a020a02071203020a0203010c0c08030f0910061202030c2202 79
    0x2e0b0503180020302440e0802e0100000780000d03224166040cc582c1848401c4000808840201c081c211a80e84060b01c840f101741c656018000d8014003405540a903841c0c109001410f03496071f404070000d010444407c240300d10450744190040c029020301200035041900703050700085c0d50b03261400d41081160804502280840c010340d44045446881c44c14007058065444008030b00070341040b90b1400104204a000031420751000c1240c605881e880031400380580e0554900b01c008146011055603003604140908030716851603c8141250060030314581c1007203541c1d4043c41a031803e0040c14500807801807006022004a0000e129484490100300507141c84045900700e10b00030b0701d0340c4411652038599020106040d03003c1203448216000340d0003408030703010038002120901035800e00a4003505051011038400e100c0c0f151241d400182d070383d040380d2074000f045c0c1c400e0084900c1c590202203200b000150100450405001c8921207a008482c0d10030b40941c030340d400c4c2280040c00d020031050b00e5800102e90042c580 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 221343021 1250 221341771 221341777
    0x3050d0c0e031b0f0f0a0927110109090e0c2205010e0a05010f3203070b07060b301f02030a0f0e1b010c0803090d0908120a0e06 56
    0x10700600310340d40c00c0700c4043c03e1104203240c0e00a43c2d001d05040440100b032400d10208990003401d0103011805264508540c81e0000c1c6280740070942c90524411800079154180e00202000e0303030052610010800c040d00000d030500e40150700030129107041c98074000707842c880414903c40f42503083e1004113000803020402d0082c6039a0b00384071200a468031002043d200160080c1038422000c040c1c0820180e603c98805003c4e0030b52900c03030f000d10364043d00c507094542c0c000c000780b08080c1d442d000e034929501d407400d03c0004c0c00c0c14207030380003500c040c00049043c0c1c0911020740100028102d042c1d272440108120740d200c5441d5080701c1e016103a81d0455081000d00350450803c0009585100700729030110031011051404007030b42c000d59002d2810f504154044110100350310030072046110040c02048421214102c0f402d000c2101c8190f0343c1409a00c00004021949a800a40c8510080b03c05802100003417240070b40500000d130000280d591222412076112468101180d01c24030003802c020520301907400c00544944 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 221344271 1250 221343021 221343047
    0x1b0302030403150c120501030804091116060c03061403060403030e25140102011401031203020405120304030605010608040308070305060a0302031f110c03030112020301270b010b0703050d0c 83
    0x24450a801c10008650340324045a0f85191740d00f2215280c0d1041d10300a0780d10070f00025200a00801040282805550000021200f0b0010180c00c0586c540241088403a000c0b8003500c016031144a000c19130fa03850b10888016101e24000819003901d13000202c2d0f6551401040201030541c1c484191001000421402c0d0100c0e170351100c3d28200b44502d5a41c89814001886604908200d05e82c1c284425030042c020b0403901980b02800b064540c0ca15144c0d0709100280d8005d140925500700300201d49a00c81c1702644607403019190003143c1d1649189012310031507005901060402905505000010340e200b02c0c0b290700180c1c9490b010450703840d0306000546100250744004c0d41842280348801e01c4001800d40407851007132002e02044611800c00c0c01103601c0c42902030450180d007003000140420b40144060284160014000241c0c0c01c035250354000c03090b2020200341d0311560701010000100611030301003d026000031820305051040c2d6907005007803400ba0481099072140c60b4130015081030b00c10400d00d200f00c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 221345521 1250 221344271 221344283
    0x1806090f0a080706080a05090d20030a03090b09030a12050a1803120615020c0402210f01031e020a0e070c0c0b0a0809030f030610030603080d0c1107061b0302030403 72
    0x295907101038031030f41e0710000c0c49600046881c860018000c0402031007528170802d85a070280c0540c8008400c00c40d084940304041145034801d0000310034030902c041028286214468400050204203400d241c2c0d0710100040145641d43c0c02000200d101640c4040c3c5802c5032800c22101040603110418070740050041d50480008096030642103006055000c500d91040b0903054108001041e00d42c001e03041c903103d25841703000150380014000d280d241444e0b8002e051030f001e00c08010003a840c840b110140c80303100070781d840100150017000510602c52840e9042490007075170000b9840101f025408140c0c04581413047c214901e5420340002c070602d0180d11b40041d55070703001c20100421a00c59043d038520b6008104000000785500380020440c550010448980d0859a0002030441c1e584008004000b1841d85844080507122400040010707189009170070010061100464503903540f407030050641c042c20f40380b40515400750904101d101d0b04080c0c070f01040c507041c6047c0040d01890382000d034034500c103030741c001004 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 221346771 1250 221345521 221345539
    0x3040c0e070e09150603130614090a03090b0307080a0e03070b1602010b030304180203060102030c070b0405042304030323010e101d06010e04110309010906060504021806090f 76
    0x1495000301c1c0503640d000300f1100302050751100e0f04031140180b414610141c0104082012070000c1011400400d1002d104060115007600c025043d010002c1d8107603298011684030985a00406400043d1040a015044105400e5243c1040003e042f04030107040250300560310420a000da010620484540d143c000c82c141803c0d080c82075241c80e80c4c5041010030401546000580c8421745004000c9900703c0c0d140380c802c290a504040c07107450080d0310240c1081d040d40b00400582c10b01b03041c103001040042c0405824162242d00c0c05062000743c8000301c501d105403540c121350706480300420414140d0003503003500c1d0020b81d0002d0042021045a440c2d2002d0302511190000026882100f0301890303c01c50700c140b00707110030b01ea50f14507070001e10400c1e032000351102140400041441d4401c0c14103603040c800080010900c00c2d034000b02e40172075030b00a81d98104565180e00e07018060100a0160b84024001650214a8138104002e0040140804145503103d400b00051220b2541e54246031003801074070041c00400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 221348021 1250 221346771 221346781
    0x60207020a0519170a050a08090f0d060e060f04120e0a050622060e240706090b0907081605010e04020c01140906060103021303030503061203040b0a0210090201090b03040c0e 76
    0x840ea0620f20034800c2c890182007481d140e0303400100f11210100d90200082c00c3d040b24a0751002650b801c00c901c03085d0800d030780182c054ad00740d644080c56100603018520001c0d08055000030b06003081001000c4c80401000300f0140400075000e410300a550541d0303850f01d1618404900700141c8441a01c4e40507981c000d401003628503050f1078034142c40c4400f01d40d589003050700381d40d82c0740c0541c1d4900101c900a03910414200410540c020011000d2004410804200d450040540c0e94182100ca4100e025030307204480300f003008501c4004005140180c200c0800a040a44481c00d025050401c0c03805000d0411010301c14100d1540c4850301512009502103009028050280001c0207410104807034200091141e840800c00550080c4221a840c101000305040b080d400d41d00c1c103440030f44c006000541c011100195a101c200300032b1000d031010300700808004c0c1c1c0d11307800304900a1401090380f80f0310b0002483c003c403030f000503a0440c01ea40308035202c0a01c0c154a80d511350401c1c4c01c0c0754860b640111043ca8190003000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 221349271 1250 221348021 221348059
    0x40302010608010c1709071a0304031418030c030f0601090b01110f0109020310180308070c0c06091502070f1208040f0b030709080c18090307020301091415070c060207020a05 76
    0x40c1c031941003e5042c100c40ea03034100c00c3c5d0b036680c031b22403207080740a100310000c44800c03580300001580c0c81402810214100c411040d1000b33032a41c00a03488003112180d40c00d5510403450701340890000311004800420403443d0103281140c4450040c400c50b000d00d6941e81d0f00030301c2e0364005c203252036080400c10107542c6aa00200401406492070420882c8240a03803200c0c950700c03406e14401e084500740c0f480c0f00ca80461046507025920b440d409440a001d010035030000e90005598404624080c0070316542c0c0b140d50a01e00010702c100741c040c0c000001d0139900300480a214200581c20480c080700c02c0d0441c400080c0407039080821440c440c5412001007000041d601282c03802000c3c000350b0051f0400e54503110503642e03984080d5114244001003507448441610041c1ca420b611310003403900100752006491800c40507a00003400c440d101c0400f1030309582408541c01461b401801541107a40c9100c501c2e02007403616090013001d203900713408018611980450442c05544900321401c0190902038040201240d43ca40d0303079 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 221350521 1250 221349271 221349287
    0xb0408040e01060f0e2704060b09060103090b0402150903070902220506120a06050a060801090f0501032604180504120509030a02010e1206130b06010c02010e09040302010608010c 78
    0x10600d940750503000060701602c03520100d618002240d4441040390030b080e0402079140b688a0112000c030703003680c006405140c1901d00a80c003461140400240d500360b560140184c140c00100704a05052a01d40080081003100c0c442c0c03580b0660484886101c0500c83e0028500b81c0900c040d216014440d005000c07030090120380c005d00c40030304003070301c3d00401c1104243c10b03402c2104907001e40d0760041011304c08401e6641007803c2450f017000c0005004a007064035070303000c00d01c140e90079440440012840001003104000e10b108090341500768210500941d81580c444002030b8040b503905107490030f14035401850041070101581c0c0584049980b0050342003000d180328000c0e15003941d00780d072040c80c01c643c00708042d03019408442c0c00b29800390140c610840300d50010b48400c4100c8c41c015404c09445660101517900c00d000d40b80c4070340c0d4800d07000c41c42e198080c02c2040b0302a4009082034144201e490040000d0f0fa040b401c2c0801401080310807003e55078031303841d00324003428090380409041d60070555400ca215420500c9 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 221351771 1250 221350521 221350529
    0x27020f0c150703142806170102120f040b010303050703050c16050f0103140a0b04020403060c02210f0403080309011401080d020d0e090612151003021008061e030a0b040804 75
    0x24400c4841380080e409484200f0b40780c18040c0d02d000c01c085621401481d0034400591944400001d00540d078130380c5010035540703000c000c50599500013500b510045040c2c181d00d0f009122240400045d240c2aa81c0c0c003551034043c0405024000007040c1d0404040c480e000310751800001c3c006070303800540c400f4024070960280d406203e100d14034907020700d4032075403081c40340599244440c0e0303c0900310740320400248014014550400d40047c1c00700008400305285000c1c1c0c103c0011164001c1c4089124444184c1642034800c10032a41c0000c02c1105041620243c005e64084e6074000004070364a441c1e88162500501402c80500000001c00000103a07049010038111710310419a000e07200440c080820444415409280c526440703000300000c50060300b040140840d404141130200c0380585c008060170b509143e400c41b400b150140c03100b5800d000b1400d01800e0001c10b5526400c0c85881d82c00d011300050300b4090750380d050345507180000942c000c1c155010094040410b400c890203103640d0405040000141d032203800307 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 221353021 1250 221351771 221351777
    0x30e0a150917090d0b060a030501020f0901020d0c080403170c0f0703020f01050406140702010521060f0609030c1909110306030105090a02010c0b0c0906030c1327020f0c1507 76
    0x400302e0180052a049406010f0000e1030001200f807150b40394a60044041c0c034181e0400c09549000c0009082417005000203031881c0000da403154002c1000a19085560003003000700b100c40c2c070b0503000280383c03071007a541902e5024035503c1e03070b10f541091158400d01800c43c0512181c490b0480100c207818002c2203d8040c2c034000e4901c41c96480c284401510280305901c1a5000102c5000026920f03a8109000c0d08609205250041c40d00e0040c0c0201d46c0110084480003180c2c6020074148040c6290010f0b464480d49030a40700b0340d08019a4000103070f01c0f220310f41c11aa0003000d80f40e1942020001c62400c80c0c001d8144c0413410004400d00c24050200d9410031988140290320b4000440c1c0d0030316001a410150f994165101d40250f413184e51100700e11000030300348918440341031240401d147d4941018511500e0210009503ca086030078075040b1844d00395000504045142c014003c80c20207420a00707465889110000d0703507841162540401c00d10441c603101e8543d020b0302c15222898440c9040f958000c3c44a13036 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 221354271 1250 221353021 221353043
    0xc010b06070b10090e030d0203040203010b04020c1e060403080610021c0c03030605090c0418230a0f05011401110307050613200108040f0f050609100e0708030a030e0a1509 75
    0x807089412a030f902030174914076520134000c0ca64040415001142d12030301c080c0c00482d0300001d44022030142d8014428415180c0c105545402d2036565036241904490070502c002e0035182000d0314090542c0d80c01804580c05102107444145a5900070008107841003000f0840e207403006020200100b411405d00d80840019007041d4000420b80341210750721340244820289645807d1400c1400c4680c0003a40c141d10981c0b031749512822540841220a10350004c86140c510b04071440c01944031011180c103902e00042103440c3c080103000d4091340010b0410241c40130308020141d003c0c0c001e40b1620b140254080103115200303900c1003126035055007540c010301c2031241c450010348003c00c20340312508c03c0d2803000301e60000d10628001000714040c080044221400b40088480d07008440d220141444412950701006610140b001c80307031107804d4401d0105031103c05014001e400d0a1100081d140d11920012208050f01c440320303800c0c141414000d04041c00d03485580180c20035542da40340f4000c2d184100050b21480285 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 221355521 1250 221354271 221354279
    0x80708160302090c0a0c0c081b03011a09071808010e01140f07032304140d09060203091504120f0201020709020a0509090c0f180f03070312050c010b06070b10 69
    0x38516010580b0360081c43c0c001a60380e43d0000d005160000c02c1c170f2008121b460402c000200c1c055401d841e01511400000d03003000b0380f1400781079401d00d80e4404d442c1d000b80e143c1300100320601908c2d0103440420004413a090ba194403052012100551220404040d50703560081c0000c8804c015444490b481742034800a00403104000c0c4080e104007021103100c1d40c00080180050b000500c0391340440c840080c1a2114444441c90481d0913090300c10440341151991011015908599020001d8460030a11480c240420310b0034017400a440f0f024591086001d20307014680400d403800e8003425107010b4401441d0500302e25581d814136080c0906010020f038094041c2034804508200e041c0212955001d00c1e4459070301e007081000c28070080940c02840024025414000c0c0c07903900c0c41400c000e03c4408150344202401d0889c400800c200740d5203055945100398040b660800025a040c003030852140d5150510076250190812154090100807949070b512400c0019807804001204050a001d0521003d9144500e511 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 221356771 1250 221355521 221355553
    0xa0b1c0b0112120c06020409050705130f0b040e0405100e0d080109061202060901031e020403022e08040c0e01030b0403020c0d0302030f0a05040506160212060c0d1a0a080708 76
    0x35580b00944161070f0400c5841456002d420300d402c03064400c080040c60241d41d2030f46c42e000c41d04140d4040c0005407000902410b4002411900c07000740c15048003420550b450411071000a101d03031322030304214030791b09400030b02405420b002841c07540315208030902440c040701010302d0f190718800068401081e41500081083c074698801e40007a20301c841c4524082495640030044580c021151650415031100c001d0760080c40310b450b21041000300041c0160300c85041d0310400c111803d00340004030340c80c000c0400c401e0998211001d404000c690a00309520a6192414481e03000c0c0e0441e00292003851081000104110544c4403492203140203500303640c0b1a207071100030841c05006c2c0d094082c005034020f104284880120b84001e281a11a504106282590701c2021662940188040160520415044009604149043c002c440c946080981198034001c81144494040c00801c0840180d82c0c83c0c011134001c4450500b80f548180080c1000500342e034510819507900c03018052442a401131000c3c0d2104252 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 221358021 1250 221356771 221356799
    0x2040303110c0d0209090102071506180e1e0a0804142e0f090f081e070e040b13020301022205010e0105030c0a030213060503090106170c090a0b1c0b01 66
    0x48010143c40d0210465001c0000081c00900244540c0d50f08001c0d15000480303080407221059031052010171b441349408811450401219282c2640303178104180040640c1c070100700f004c1e100b20f04007040f011550208030120303e03281d204e040c020300c0c0c241d000030085800508a05a22400301c030803110801c0d01d051905620144100034030000d0610080d901c488410a07008194510001140c0e241c441c0e40a40e490380307a41c203122080e91203148250401aa035681c40e40d90145a48140c40701000200b070854a8502040000c80004002030481c48481c4040790b40c0c403524070308041080d60014029034030307611255892a81e216500414221500e200740d000039003540102c80914010405171035a81c155a2003c0e90380e4810b138009603024040560821000200010342a1064058103881d50b4290b02ca140c450b15403030854500fa00520b0b15602d90381100c5511400002d140345156000f511000c1968a44140c41c50141842060040c2c1c081d4101e9202000c12441108040e42d150180d82078207c3c03a40e0364002c4100d001 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 221359271 1250 221358021 221358043
    0xb060a05060c1506031011070212060105010f030b01050d02030c27010516020406030507030c1503050145091a06010c031d100302030f070207050901050f120d02010204030311 76
    0x18019000f00320030603e505000c1903100d4400ba0075552484564154101140e1440b0002c2c2035030380b0041b450750150708000d01e8a035224240d090040c0721700e50401c00040c15200c601e16464080588842001d500350b442141a58418454040195268100f01c0324413126600f000c0204070f00e18241104000445512080d25202184c06841d21898013891007505009241c1000c026a007083c2c44050000005404001002c000c60090051100007410120380311035480000c007286080605010052107429001ca000c0c01d81c18560302c83d00781104c20310b0241040d4203500144104512a0000704d03420708112741d900084502803081441030102654036101c0d5174842010f40746d440c000740d0108041c40000c2c1c081e1300143c3c184204118003607442c568140004202d14200e03a440c0c000250040b0a102c0602c101403074080c2c1001c214005440071902b00304c00720f040460b051043c43e21880d0b00403c161040d031102c0c14a510600402010b54560f1a20407101078040e5100744000c070006145a043d540301c07240003150035a0300c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 221360521 1250 221359271 221359273
    0x150a14010b0d020f0c030d050f0a0c210b041119051201030f020604150306050901050f030a11130905070e0609090a15020f0315030d111f0204080303040b060a05060c 72
    0x61031a6114000940104070481004c0c50704102a490204040000d40b12400f00d2000201301458440c40f8860360241c00f8021107007175801c0c0840b2818a680000e545507030803200405030b6a003480e04014202c09801e2420780300da003007031814080c3c02240600d980103200000c0b61880340c3e8103201420304121128030400c820318892070b14000051000900c20300c1d14200d510300080500b070400e0f8980303205215044147c4d0b00100804e568050030480b6091131005180140710880c0e84404901406020a4407040140c5c0000e01ea2451041d5048450366040400080541d80d07900402640425161076940c800c240e001d0301c51030b44c0c01d02000607094a4040140341c85050000003404013802680c1c2e92802501030809003140e0301d0740a00c0015030020501c000b4512410950100e410716240081c14982459a1f141d800001c01c60030b07100e4035540d5500040c00c00c3c502c4206428080600c141c401e0080024016030304422018000002400305000500c40241d01801048810b10303805503444013013060a1003001100700b59 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 221361771 1250 221360521 221360527
    0x2270901082a0111030d0207022d0108060118090e10050103050a140304030614070f02030c19150501032004020405010c120915020a1109040c0b1b150a14010b 69
    0xa02c98607501050302a1040c10003407406004400c0b030301d0440d040044101d071103540c0483c810041d0b1904841041201c60003400140d07006201901d4501001e62403240d4034107001104011800d0760b4450701c80c2c1c000c0400070703c0c040b200681d2650312103400703000d4042c05407040303200389000c04510349064070585040360791000003001201c24643d1090f0300c40180d091119407501051000101161040c02000700f00494001d5400c0700c6d1500840190500503400d0351901194014414000380d81e000044c0010f00d0348181d00c0b08402e4440c50316102c07040d082c089550408071410580000200400400060000d2402d90309000803001e0340d9091008078004c0344100d07400140d006608402103580030701403441d8400d4600d04250000e84036150341a82050765208040164489003100302800300180a4142890003166003244606040d150a62034044502510102001c0052001c9111540d4410200c05807100300c10745088613281c10200c00360070011110000b2070b41c00c0c102c058104e4031085070014142c0d4032580007141 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 221363021 1250 221361771 221361823
    0x7050301050111030c070f060810051e0307150306050901150c03080a0b031b0a35030c0f010902090109090b010b0f1201080a021801030b0c07060227090108 68
    0x50164401c0f052070925000800001c0b51041040c054940070742051440d0400107442c26100a09104000b810000a00e00c01c110070b001035694003c0400c00746000c2c6520b0007402e020030f030010742040034079801296205400801d0103005901508064202c9108680c141d5580ea40c41c80c14514180360302200d14002220759866000080c0500200350704402801c80001c0d06002600200349840c0712042c15040b4906107588405451a0072000040a022090030705d6205152252008805942100991604001211500d080b01c0810000e8a01918510044550a10307544032130070b0082880700c40036405075018100103c0e00000781d000d0380f00901c0e440028240e05030718100003050f4540040c2c20382c64010340c040000321404501c508085028002881c064030340b001c845d2040003103191060b0304c03588141d112140100040781b00c180700c10b0307400003c0b054103a40e98001803402000038800c2c008850032041030003400f241d00c000320390440250130a0036181c0300f810740d888000a07651030390220341110580a00e038807450 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 221364271 1250 221363021 221363027
    0x15170f0604030f1821140109030203300f0f0112020f01140903100608010507020c03060712200d24060c0c0812070501060501050f0d02090a05120d08010905070503010501 74
    0xc0c404c21022504440503030380700d05210003c5000c501d2110321202c40340d24a41c1c24002200204c411030b412000081107054a2039501940360f0150385400038a642d003021040c1c0c500040d840d0201c04c04424419105142e00c3c0040e04c00f00003000c2035400401040c8403000200c1c0c04118420280e50068000300501d60100104004440e014480080c50605d01024080d12405031010440090319640c0e000c0041101805c0080c0c40d400c4400080075502113500405000c60306032404900250042c14502e0710714410807008040002a0040c41c011403004000c0807641c080304410358001d030043c0000c0c00b5051000c503c0040600c131488070444000c0104410501c0204032460050181c615101d2040203000d05140e82c6120032400c00550b6095044c00a00004003c010048203108610151100342000b906003400900f42c2a070500807019460300741d81e80000c03202d0f4a9921038129000030000144500c68119881e0101030311607260240d8800400c1104d400842c1441c160700880744145480e40d0b52a040d030386048011 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 221365521 1250 221364271 221364287
    0xd020607021909020a0f03150308030f07020102250317101202030a08030708011509060801050f01032418180803131a040b090105060312090415170f0604030f 69
    0x1040d8480d6041c100007648103460003d46080c140907143d0410a40d40e8410240942c2c9540c1110105001a41801e000082b404805e41c2d400020312104201c0b0350340c3d0010140d00a104800d14111043d41e8150640c040c0f600400d90207071210b211f5900e01000000000744858a42c2c1c0076940760040225042c0d05101146080e0404e901d400e00040480c1d050244688034425281c2c010703294034000500140040c0060300203c0000b02c2183c0461078041c015500d0310000404a00f418010184298000c034941143c40e0f100e80c000ca0300c04108144981d0481d400030b41140b0f448046441440a508030840c0c1d411030b94211482040007a4000605088003c50b0729680d43c80160700040c2010700c0401c280e0446000305c1c1c01c80d0300d00789030280040da42400c81e003004e00300700224160081032240a41c0c14030013003081a40300450b8031030741d8444400d01c8079120000000054050100c00c26081c002c01d240c25400107004810000040100700e0101c1510b1b82100101d0581e5241c2100b200c018020070b50358000391240030322803080 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 221366771 1250 221365521 221365549
    0x1905030a060b030118180c03061a13051b07020307030b0a0e0a0302010b031e0a030f030e010f0b0a081504030810030f080705070e2214070b0d0b0d02060702 68
    0x141d040d00c85200c02840d0b002038201600e40803030011501d110901d140315640e002138150810098520241d0303030b03943c01c503000d5000003040741c0d4071381e80608040d600d003804003075211000409050503601055175000061600301c5074003906680b00c00b0780700414000300e0101c0d40c000d500079001d4941c040c1552114a0454405040300030110ba440640f00a02c41c03040c041306238010b100e0f0b800499087c074a401054645201a80c0600350b03d0111180c02c40a02e10004502810076818205080c044059174010b40c01082005980c080c035508110010883c100070354860200d0355011184030140907141c0c841c140e40c03071039071614081030070b0046401700e8042401100808da00c031012241c94034000350c99994041000c400ba4808503055a000b1540004104013401a2000780403904084407035407900007800718519121000d201d040d0040c04030300c0403d0040c0c0c8004403003030441040881e05020768a0940741815442140254034180c600014040b41e803030110b100d80d0085070001c2042e8186129a000c210041c107441d6a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 221368021 1250 221366771 221366791
    0x10503070b160f0b07121b0c1b080c01200c060f070203030d05040b0f04030e0d0302070e10080706020304050303090f01021f0f06050f0915030a050a0c03031103190503 73
    0x114030000d0b51120b103d1900300c1c800c804159031070900340c0d009808101c242c2c840c1741c0f0140c00e2181040c00c1c51005802207000542500e0f114641d03000038101641c0c22046110850742c10000000045400c640c0081d112055060030b0341c1e0702c0f1104081201c95426a03049030b02070b000355000515a10f1591515a003d81100c020800ca80c40c600f011032307400285141d111400040401e520307103040000f0b004480c1c00541e840742c9a4a910080d40c58542d400a04002108403503502c00c2180204050a1500c04c21201c005010300070281c46140c185003240b10a10140d91086403d107104410780864410301c08800d41d0110b90000d8001d40c2081c0b8080f040121944464000364114800c0c0742541080c001c10031041d07519500283c40028121602081c110259416a04028000e5007600c0441020340c60714482a540128000364910070702e00414002420480003c0d8080c00d680b04110850f4148005c03900004202c03486500d440c00181c106400e010344900414022501c1540042c4102800d04e00400c015548105480 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 221369271 1250 221368021 221368057
    0x14040201030e16060305070f05070203060f13021203030105040c09080d2003160302160501120e0102070b07080f100e13031101020c0c030607030204030c031b21020a0e010503070b 78
    0x4400c4031403495242c1c13003440081d032680188030a090300003500200304801407401518200380c68010a507070300405003e0109581241000410000c00c1e0086204410350003422445102e01e4000d20540ea50820f0103521302c00c0b0329140d446a09c1e10700903030300e6000311980180075100520121a069802c900503016440d0340002d18009501d81c0e4405000811210b4120752a185462045090080c80c0c070005a1302c80c481540045010710140c1e030001d001d0003044158100129806a10702e10160182c000c00c04001c00b40942082803052081d00100007a02c600b124030b084507141d54400350b07440ca81c00064868000150049000b00c0c8074049040c0703030703201030728040e0414a00002c4000515405c9034015802d100c950b402c5191003442d20314080c0720142d0841044c2c0b6041d428203055464410415046100c001d100001c4409491108107100a20400404c0c00a2070940340365081039940301d41003611182240f20b580088404500000c820305950305aa601400400c0c2050901020105543c0010081c004241c440 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 221370521 1250 221369271 221369293
    0x403021f0302190f08010801111c11040f031515090f0902150909090106080c0d06060b0a0504090e150c0c120a0315090204050f04020f0d0603120f0314040201030e 71
    0x84502d0f024500c80e65039030848145042d1000900030801a0800c40b601c2c0d0420210075511705003442078036400c2103c021143c0ea41c030f044851200c0108500030600c0c44400c0040350003d0024a41d20040c01228014400511400c81c0c0d541040c049030184207100e504030351a09014040d804042d809505a00c140031000582d944c0950009151004503000c4030303020305000125503646080c4442803903089440500203000d02810310b01c441c0e8640981218480c040d0311542c0d01c0c00180011a00507038001c040d92481c0a6407a406000c0c01055a0312500481c2259803d00405003001da000140c00660b108001100c1c3d42c90381c0714481c86895540c001034540c00c26100d00c0c0440680120705c580200400c03001500d000a0001d0503e130751080201040d071140540c1c0c0e2045c04200320a4407011081074110000300c4005a46051512301d00d406801014005a1450728001010081118000f0040d07090015078580d0400c06594141c2242601c6500782d0110080003400f0101d001540640c200384008a40d1030240c405940c1c00e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 221371771 1250 221370521 221370547
    0x140d150b0d05060603010f09110904030c0c060c120e030c01110c04020f03090706170a0c17190b04020f04091d030a08011e15120b0409060906050c0403021f0302 70
    0x10754800d86007a002281030204c42d207404d1140700060080e0079800e20107805103840c7c540c08142c105480034010100003002404161207608070b420600c0c0c1c071000700122240c440b81d0040c0303a035604503002c403000c4e8120303821608103901840d281040301c00b00a008141154040004441c0740000ca056141c4910980309100b40c3d594890000d0050701603440b45558491404500d00c0385010007a40c0031034188421400c1c142168000480501d0340320716030340c101107a00726010704126140c2c202003003c9007a554a650038001900403001264401050110041c001c6054000400080344a8068203e424420400c01084030360030b0303a04107099010000004486c00e1392050200d5046a01c0b00c64500700203542c06e07006100004e5851010030226440803803a40455007454281041001e07042d07101003e1180d800c06030b40c0c0e41c001907045401c8010010b80b05011441980c41e00f20045c210700c5e40102c80c0e880c100400501d1040e804002e59084a4000701f2400740b00e00c0888048078200d200702030b81d10415400300400303508405 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 221373021 1250 221371771 221371789
    0x3070c02120109030216090e0312040c090c02060403080a0507050406030b0a030f08040801051b07021c050f01020c100c2709151401080907210b090303010807140d150b 73
    0x101179009090440c1008022040040d0507800c0000344600d44200c4c0d0b04001710003c00e40b001300150f01281c2031585c4030790501c1112000c0b154061034106081075400d03c00c1a5010404600a0b41720340c845e80102d03226001343c1c00070744204861040004034103001c20408184030760400e0001841c05004990440c2c1c80b92074041428003140350179a5944d45c0010100300040092140341d5004142248054541d5403484120900c0e1180100c06441a5400c12491344c1a1501003900c0c840c40c2d41c0b00d41200c3c10300d90000c070720383d020350000c007002c40182c014040d02d01c0050485016803400130381c0d00e964160f5281c403100c0300c162a4001d4500ca8020045c080c40c00402c010044e4460310f02050301200381581c20520b4000e483d8080504045420704101c8180c060140200e0002000005e031021410070307114031080d401082c0000745a8000242c95014428203000d103620300440254180c41d80702c0180c1b81843e07210742c031185091208505940d0400110600040450103003419102401c45440340170401210410018115003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 221374271 1250 221373021 221373023
    0x20c130e1002070203071406040b03250e13050603060c030702071701090c0605070f1202100f050f010605040f140f04020a0e01020c010c05100203090c09180705090c03070c02120109 79
    0x70b600003201d1055150800600000707080300200050156400800300d105401944919003000d0804400303c0c0b20300800c0f20400d80c1200d10140742d00d002c0040d21000810007440e101d0000d024403247d01c503040000d00c490280d180704080240042c000c90b01d9080313400c601c0d0b6200800d6501140540c6101050305a029440d0354000e0140000100f203605803400d140d01040c106600c10700500008010502c0001c10a041c107201c40398001002c60007010103a103003a810b050385444c5044900c0d10300448807041c483c6607807055004a052001400070780e83c0b0750f2015251071140d03004402d010f142c2c140081254001211a0754880b01c0080c0c40010740c0d183d503e000c14182d03008100190701140e1002c074452401e503070400540c0015034007407904d084a128a611070030340381c9001240341402a030700080080e195107800c10a00c6e400d1100540b41910a10b80301030409486443c6c1c0c90107410034020711100207280d1030308610b00c500808451401c285580c540c104240c82200d03121a080760040d0320320f290315100d84001e1041003901 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 221375521 1250 221374271 221374303
    0x60c0a050601062c010c03090f09021801020c06030f0601170f04110105210c0708040b040305070e06060d051e01091401051806011d03030f04090c090501020c130e 71
    0x40e50400502400b1601a1000700a020300c01d032034541c4c0c5100c082d04601d94000000c2c200706a5000c0c0b942021621220560403c41d41154000344c0060500301c3c40e8010044524a00c8030a00081450001203858141030785085920440c1840030502d0040c030000c1ca5034000a05060009a141030001e150070603500444444d1030614000040009000307544003a1844481b0904e41149002a0002c2405011604051001e050706601c3d0002d1241c0c00d1520840340c1d025005000c090711142e6401400c2c0455000d80030840d1640280000007602c410303041e500a000c1c5c1802495281041340c00d080d4003001b403800515008000c010701c0101400741c412800114068144100d020801e02c03a0001151355050060380401c2c06100c03c00420003c00d041100020b400007400d213403007490900c02c040100a80016460076aa1601000610c048643c0466000b801196030054090000724038402098542100030701c9000d003d60040d803050303c040d2500c81c2c00da081e0000b0607400010550a404c10311441c105c2d95446021070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 221376771 1250 221375521 221375533
    0x1303120b090c0705010b0a03020a061202040b070c0302100f0e06031314011b0207030215090d080a030f0f0b0306010e0c0706020c071419060c0602040b030703050402040b18060d02060c0a05 82
    0x30b20800303019803c4802d2007507d0a9080078915400308102003001d01c140340030400c4c90807440144422a4040360018080ca003141601c90200c3c0c00e100300c5500f46444101c0c0f0a1541d2142c203000c89000301c4008980803d640c90343c1c0070040c100014001161320003400c218644205508035400180000a20303181c0784048000002c034004130180b08061010700c00e001500f13540c0f084000b080141c0c1c810100401491078041c00645514171140071401819005900801404022413440489941644592031400a6003c02d112250750400050b00b00d030320100c55260103420007001404032a05c801111a0015002e0320300710b24108040d2658001c17a00005031641c00c42e00880d0f802c1141e64001a1481140c61044501144204160340c00c10b0107645c40c3c1c460103040c030020800201c2401141c0d030603500244101102c881d039030310700840020000c10084034200d04c15498002610824140001e840580d5a00411903613080d484410030418810030380d107006c903442081003110b445070301030500c07520321550b1040d402464 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 221378021 1250 221376771 221376773
    0x150f0a030515011103030a0c0e060a030f0f06031a0c040b04080c2809050606070b0103030201050601110c010f0302090f0409030c060506010f091202040623040605091303120b090c07 79
    0x1404910a20541c3c10001c541c0d900141e0040084212500040c1072280095040c10411303060703c603071104a00c2558403880120360000b8850701908800d11500d0305203400c002c0090300c03038005c1044031302600010b081e480d1136480c05101c81040c43c08058108411842d65401c0560310950524a81e01580018519400c0030782a80504d0401c090b0701510b00305a14945820058155901c4840d00da05100d01840c0343d031900c0118107544c07108401c031060342d60098410074840da1641006130107020152422800134484414180c840d800c0800c54942e1814160741b0b80c107114100d004120f000c0d410900c001540306100004d02c2c8410761b510300c00c1040c020b2080d00d82948d1400182411030480c1d05c01000d00781800100c007820312159900c140791006542d00452221110071450000c10010045c2d40c020412510701141014488413018141c8580711808580510680751208144220400c0c156a0194050005010200042d0203005160050020300c1e8001a10070f02d4140003504191041e03501031304401c00000c83c14 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 221379271 1250 221378021 221378041
    0x30c1e0d090618020105030f07090806070f020d08071d011806020a0507091e05040f0f050106140303040b040e04150c0c02040b04020c061f0806100e180c150f0a0305 72
    0xc0b003101c9400c0e03100075070f481c3e540000c1d1240c030004007408810f400900c001900b040c010440000030308156070443d1818504950003826811100351044054030402c403003518032910440b40103101e244c89503a4aa1031807000054203959490742c91049040c0503191030303032504811300c552a0b00003c00c031a60040ca40e111442c10002d0821050350480c2c64240d040689010700380c0180265031100c001d560f540090283d499081100c082018007030020302d500101030307006c81406015000f100507654003581c80c02c3d420800c035081642c0c81c0f1851255106801042c00b081104034541d030141507105000c0c04030000c500d07181c4104442280c507403804074008a10354140c5501503051900c0748038620340c001c0e5070031481e02d21070b02d060b07542e10301008145e5580181e800280b001c00030703021804500141800002c460b0203003031000040c0740024160090a80c55251100019200740d442800d4200900007000540542c100102c00c1c03000079042d071141c00d8003801040180e000c14014402c01400d4800f200d943c0000d15080c400803030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 221380521 1250 221379271 221379281
    0x9093711030907092910032c060105030a0309050418020a09051902040e0a0b130f0203010e061f0e03160801091104020c0309010302090d06060611070e010b030c1e0d0906 74
    0x4081c0100a40c607416440d0005c04c0001121070301c08035000108100701d44811000b51014511f00420002503608201d0036062000840f4544103009040c2e807481d070f0700c4d142403580e0b44140100c060b000400000c010807503030170319600401c2c1d40c80b031650b03800300c0030078254003c244000c0349940002c6482d582d8400300680c9042042031b00d00428286030040d0300e05480d240848003214405400c411301a5a00c42862949a8508507013401d01040315900b4094014540107083c029042489406020000000040c0c5540742078030808548021080e034a000c06011400c044400c40804001e4680510403903100042070740303501c014a0001c1490800200782c080081c900008130000a9460302c0c0254014040d034111004040142c404000c4280b800685038190000094070082040002a01d01c6180c10743c04901540e0050000c00c0c8105410112400155190180c2400c1072091044074400304050000c40c00030a070040c01000480b805070030095200e031030900c0c0400254007440001818a0380e40c4041c1e810007d043c002c03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 221381771 1250 221380521 221380541
    0x40905040f0303050702060f0c1305030f03070c05060304022d04090b0717010b040b0a12090303091b050102100f1407230909070e0109030605040303020909371103090709 74
    0x1607c074a0404580380c0c000c810002e45802c02c8032401217250800354401c0d20820000b0840101164200341c412100b654881d0301c49842603034007110105011405090541c200e85c01103901420150700680000e00c00910603001c0104411a54503c030600c40b0300743d07035a0282801960140c406405507040044c07001c1c200b181140c040503030914143c4010041c2448200a460031942ca46810ba0340e80c035102042140e4660303a041c8207005040c03818003102d05241d815407080c0d08040c0326800b03a2030051962120604421101d218590050380000003070080200141c0294101512041010406809503a0103030f0030544200c504100280c9000165001d40c0e02010f04503e400352000d01107464008130001141c40c920004100308140003501c2100980c1d030340703d912090300558100c5e504120a04242c54000c020f944071585181c850040040824549a11440c0c410181c00070b00803c80c41200c0d08214000711a1400c245e0640160360310409a90000c0b124002523208014800203040124141840c09040b0781301500b07 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 221383021 1250 221381771 221381773
    0x1b0303060f010e010905011808032d0f04050112090501020d0b0910050f090601021204060302070c09020c0a020d0602090303041202040e06060307091113171011160206040905040f0303050702 83
    0x14000007a41c05c2862142540d01c2841c00b41d07240a2400c0c0313819a4843c16911075a69403100185052703222030760201c40c1c3e505d59400c000304e1307031062000400b208550040302c1080b0040613040200f001158021b0a000807510000b21001c901408561034032401ca81080341f00c01c41d40360300d44031056507504c2e094403c2503004094041810780b0741e003800301150711000b180c1211402252040081501a8001c0104c003260409805c200380c1d841c1d84330140140650028481160b10808000010a10070320500a8074102111000204010f03160307502001030381c00c62008140c501e240d007040086000d440c144002c00c043e2103003c1400801d14424810300003210b50b840b0300c22189400c5031007445032582d0b01250348000c0301d0340c198000c40c8040b00c1d01510a181c0c4691015082d080044000009119064851001c0080084030a40d0b40c8d2403454079580003543e01c05810071904070010005d03288201d01900e00101d119001030203e90800d0345401c821400c1f030b1800c1d502a503008020380b0040301007641c140540c1e980080944 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 221384271 1250 221383021 221383037
    0x60603060b0424050d05011401031b08031e071704150801080303060916020102041508071e09090c050d05010b04081c0c0807052401080c030102040311151b0303060f01 73
    0x24403851003002d0328040c451181e6501c040560902009401c078010140308104d202495594910f417840708040340040c401011200212f0000e101400030007a104210a0b45095581401e09000741c1e5003030745d00c04c1c80100c5007202d800000c00c05160b02d55000d0310180541c4c04540c07242d101c414401414900c81640420160742c0b0800400c10b69480310751303099403c80d141c50040d4402481200301030340640a06c2e00b050340d1500c0421403130213903158404441341c0100125103d0682d032400412070003031203485000c10140441d00740d80040103401c006030710107204e400140c94400e04240003003103000e0555000380d0181200320000300d01031004500c20700c1481c01c581d0700c0159007030046000c6c0e0005070985450307a01c00350104a01140c0041400001d01034080c42e20a140300b00c8621401c0141c401c207002d9420b00a058061141054407842c40c2814400c880a503a0007000c40050002c041e41000020040000012005101030003d201c040704d00c1d1241c4031003002aa00619140d2a0110901c5401039451010034100000c00c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 221385521 1250 221384271 221384321
    0xf0c0619030527010605090901020a080114131503050705060315040f0b1804110a080718140405030c1b011209062c07050d031416060603060b04 63
    0x440c03082040810904001c900d681c0e03825141038070100803103000400b4007044580101d4281d03041d0301007000e80c0c03801c84d000440c0b5110302004a080b80a0ba522100100e0301007001030140d0301400c0c920002c1000c0040404901c000c0302c100c8281910319028401c618405407510520401905102c400080d08054866a0031803401e41010301c9038010400300315024a036500c0c1d40e0f02e07180049803c15094001d018000c614a5148100c0061070018210740035903070f8502e40070b1311444e82d00c1d186a481c400c03283c0131401402c145003000c4c2000c1d840b0103840b03120f801c4160b0f0b80c15062442555011000c1c41240100059074840c4649041941040d4117105a0800105170100074419680c00c41d83c03159400d100340f0000038144210707180c030380000c04030288104d441c600c01c1120b842d4408402c1d01c0c01c103200c1c1c02c40380c1540c00150b52a81401041900301000030041200294071525842540e4042d01c94400301c81c1c560b40340403181e91078030011a01d85400987d00c107529422a5110707411701d030084240e0030f0810341041d0560002 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 221386771 1250 221385521 221385547
    0x1c060e07052b060e041a01091107061d0d02060f01090c05030a02071b170115080309121513030206070806030c06130b0d09020a06030207081b030c0f0f0c06 68
    0x91954090705482e9190107401048089603c100040c040c0ba501c0c90500e42000d050140040c001201502059079607540003050060850280000d1140d40340c47c0c1a04140c06c5a41e180090842c140c05500c1107203907501544c261032420481e808603580590091b0595081000e0500c25800c0140c01400b1010705028640c58440d91040440e039021420020040e00c4511914210000c1140642c8400f11003226070004a01d100c0d000903806604140c001c001c01c9886030124a02e04151054460b154080c2c04c240300709440c2c2d09000000d8000380c0c4c031141c00c3d240036003529060b4012503442590807004081c45405c0c0b90041680411096400c03492604161030545044e500080e80d502c028500e40740562030104085550b8040058604090014022115212502c4199880040003110010391050042c100c0000707002e400b0b80308444c401d90b0403480c1c0d20b10304014480a2700c00d0031640000c80c402071000300514080c0c2c0e00b060112451502c0d440000e0000d204180c035185284c03100320b2a21900c9034404000309030324448 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 221388021 1250 221386771 221386807
    0x7020109120c02060721020f0c0a260a0503030f010e060a06050a03020c0f0f01150b0306040b01050c0a0c15170a0506030a020a0306050916050d171c060e0705 69
    0x1d803600c2c155a00d00194408210b060103003840050411407040b03580303e113100c0113084082240409500b252050704020034129551030102d40c841d9001035541e041402141041061550f440c007845070341644141540c11111320b03020030300380150742c250408007d20281009050300c1500604c00c001d5404410305004002500f07062441c403c0b40b080c42400200411024041c0c2c060350a280000000c0d00d40240c3c4800202d5110300b0b50841001041d460414a2102c640844040005481c407000c406070a55982c0000e02000385605120a41807005c180200d4207041c104000915515100c0c61148006a14082e1209960490707046107009014411490424900c010384180b68010420040412151070309030220307003050f159603c0a50080680c0d0804400c0c0205500618021602c585c101c964a080c6a41c9422080c201801495801450000614046410010b002c680711040c0c0c4a0031340341009034440310740101e0782c00c1c0c0100100754440e0702c00c000540108000030340c04652424101d2074190404d480001c407007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 221389271 1250 221388021 221388053
    0xe0a060516031803030210060e0c0f0702010201020904060b07170301150c140d050c0d0f0c0303050901270201080f0f010e13060614031b1e0d021c020907020109 70
    0x103207140e00034109062089040140c0d0746103500c49000c00940340e080003515040043c1311040f1150a11200060040e04082414444e0070380c0302c203a6003081d01844460946510501e4180c2c115902030002014642c0c0e58407413980145040c0c040c0071340c0c4000da45001d807101901c0351012401c0e1a4203000410601c5800c60342415076030617a103030407000e5a1062070016142000d10700c902065105801c891000b6a42100041900036180b070701b07c40c001005100304440201c50600b404000500080c3d01d503002900070f80046801113039100c0046401f0100315000e002e440f80d603c2d03881100441983c0000c00f90350304900026044608d55444c1d54541c9400e9080c1010440d040c0305802c854140c460010310b5180c0040c07510038055500c003c06028080d0b0b124608a00e40f000d0340d0040d8400d011344041403a0042c1080798194000c940604503100000c00700c82c0724000740d4031040300f82e904004156078000040c1e07030311402c00c4a03803290007074072145048050044c0320315148028181000d6a14141100c80072405581030b1340080 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 221390521 1250 221389271 221389297
    0x120303190f06030609020a0f0f0303050a021f0c1101050112171e25030210020a050403060f020c12070b06060d0e06090a020f0a1a0307180f060e0a0605 66
    0x60100c80300180e0003009901400078495107001400300403c141c50b000001141d008486040a0fa40c0741e100c459074003ca0b41c4501c940c0d1076044482080000c0c000c102800b14140c490066407106108541e07441d840b800c890a21440c01d0344d0300c81010b20310310f4000003c110980c922000802030740d810700110b80b0000c10801009446c451281d000b084003901500111038038000440044151598021500315203508502009452a0848005911403446100340b0040300b40d095802042d00382e9810748442c0007940400c1546c0104241080040041552030003030013280b1424240059582d00d4000c01141458407807101c000b2000300401c2f001012030b00c41801241c1248048404903a551201c82d0180d0050049a004082900428003080001000881c21044489c020b41d003421101020504001c511040390003083c80c102604c80302c80d031260a00303a028683c000034500f0800003012000d820202d03420460351108104c440c98980a000c45035010803404003010003580c0785e404080c02e1100103080c0e400b40054040203 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 221391771 1250 221390521 221390551
    0x40605030103060b2206081902010f030c030b030a0305120106020a0c090509010f0501080a0302010e0c101b0212030c0708030a050f0a0c06020a021e150105151210050f120303 76
    0x545c1c1c5084900040420300810300c81e5940c01d620021001d00310901c1900300742d01800f400c50b413142e41c4102040700c80f254140d440444000e42d4030400d50041c02643c40410805548030075910054400300040d90f2418069141c1d2500c5060804001c40d110005030045411074000d15103007800581d40340c500e441a9030210b8804202a5100b155a900404440240e02310090501c400068000f00200300d42c0b400601950003808120b40c02c454460b5071740d0161110030b82020005080902031882102c4254903800103881c148507800c3c0d1a00090541a6888003040b05a040044c001038418400c001e208018006038020310305100340004041c007280682c0c8803400540034001b8040000602ca054110151684100215150407048000956070700700001d5440000e019080003021248002610b041040364102e0866103582c00e060502c9100ca111018264900000b84510b80c0b07110786407240701d8843e4000601c25140c6030314110070019100751201c17060b40101d10124019a200b04003200312036100d9005880c0d480 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 221393021 1250 221391771 221391791
    0xc0d060b030d032306090109020c0106090e03030f1003050a0809040213080c0118030209010b0f0f0d0c1737180b09030310060c030c2003100204060503010306 69
    0x14148003403916074140a034181100700203405030f0011181d00d0000212121071207503041e08011006003070780c950b98440f412000400c1a80704940040000d081e0f400c00104a442d40d170b00802007605c40700d504c60381c0309810200030411613003030820219a100c603000815440075855a2195501c9045c40c030300150100400041c240e11940300d5804031080c4070304002d01811243e6858450544900405144600103212110342c103503d10340b04154401501d8009103900300603480c184d14100d0582c48650291010001403000c0c0812120340c00150441540c104400708400c98002c400401864051150b00d04004840060204040c01403502d00c03030680e2465500042d0781d06241c1ea21074050194000f00f0000c900300700000440740025214441840d128440c400348a0300c507110340d01e80703e0008481d00b00c071001400c581004941d01c50403421051501a00300507804c01c415466001e1170707040781d0015854010011510041d6400c04100e0041028660001103050600b07100008205201c1803001405854444248403 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 221394271 1250 221393021 221393033
    0xb0901050a1e0309060b01030e0c04020c070e0f0603070617060906030304120c0f050414040305030703141e06090105101101140906091605010e2205010b0c0106050d03020c0d 76
    0x2e12225290268802056004003008018124001c022151603083c00e064074001d50207400750300303003d0b480d07040905118000d000900c00250040c2c60b003641680b0800300c000640f400011801070084030741c004c00c0c445525201c0141468800d255122000b00900c1410003403e01c105501c402d500148100d41c003d1903920b403400064610b0003103400030111140346403045010000f900c074402d000c5840240e50441d8195135141000101c9907800c5c80c20940786086000200000d00c20001503a1180d0a400d00050b407182c41d42c0c3c4050188800ca402140c045c90041076074034050200981e05906c807604584a03903166040c0f00104185100a41c03040c021b000940c0240448940290041400d0b0100c2e8000345006107011003100380d4410055443c1a880d000310440301c1c20400403401c0900644070103860300c140302e0410700103101c9000901280c4400501ca180c840012030702641c02124020f0055550040e01e507506c880f04c890840700c00d940300710301c9071908a80c2d04001a40204070300c824210200d60440f0004040c2c1465 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 221395521 1250 221394271 221394287
    0x4020310031203090506010e011a030a02071b051e150a050702030d03091707080405060304020f0901091a120607030509030c0d050a0305160804110f060f12100b0901050a 74
    0xd0409860509403002e40e58564090034100f4002c00c1107840a981c2c64806039642e803800e001c1d83c41c0a5800654030b2100d28403c1d0001d50304291080c00046c544681500d402442ca6005205480780000082d004c000310703e4100c0418810403203503000c9100401d0302400048000050060b450254240401c0031282580104103850859402605440340c0c0c2459200041c02461902d07000c440c03990940d10310288030309551080c0c0700c020b03500011543c6014148010000d039500001c0040713074484001c4030741c034602e5201c03800c255000b88080302c00440e0301407480c5614104041100803d601800c04050155003d410014042d5003001241c200040c968561080b464114401d1000090003885145141c00d40c841e403042c011b01c521141039030100700b9a159000300d001409841d152620015207100c000c580480c075584030f003820b4000c2c0180064082103c540120b0155000618400c00040021a4010b803211074001c1d09640043c8602d1039080c1030307040c2001e00c240c500a04d1445170401c98045524007109000d0694 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 221396771 1250 221395521 221395523
    0x3022803090f1415070509040b0604080d0e0102010c0c020102070e0403030603020604030507050114030906061221030103020f1009060509180108100e160315060b0c0d03050c03060f0402031003 84
    0x50b042c0c5520450400c19030480c2c0301400e1182a200d0049038480301003107060b100d07001e4005981c5041c035041f062000c0202800310f0101c840d6011900300000912060200490703624441300341c941001070b25041d0b00190031500c2c0d51192a0a1180308810140141ea0100d202400c2d225042c01c010100c0c0c0704c43c01e0480080034107801c002d400100006012060210020303141c4100e6100760f0306d08580d491540e19070540c81c00162400c42c0c5540c009070208040d840c000341d103c40c1f000070318012912442c2c1002800c000010701c1e030302491400080040103005500f080702182032410301c182c0e6104c072011080c12000b000d6803020303c03130b08003040404201d00f07486030b482192030780b1000b1a80002d1826942c440b0501912803152903010861f252820062035488800824003a02c850039024540b0216461515000d101404051030341d610660ba400010070032028581c00382410b40708400c0141050b01b134210000e4111100034020b011242c50074400c1180541e101e00c50035428000036a40941c0b00c1e00e0f00100b041d942c110300d0b00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 221398021 1250 221396771 221396783
    0x6040f230307080703120c0f0f1104050a0c0e0a030305040509090c0402210907032006040f14100e03030910030b030601230d021008090f030d0c09060302280309 70
    0x1d00140c0a140001e00d84145e03800365458601d800340c490015224100440d0006102000070086403000c40c0001440d01142e5000d0300d480c021002d0311600160031504102c0304000348079625403501c00301c113600c554800c2805206a812040d02402c64034007500303501541c450f00303100b005214000766a88005024003c0b400c04003400540d06c91201c00010840c40032000b20b40307180740c10150005045c201001038090100c9420208a09103400d0325608400c2040c051b006445d00080c0070000024041c5d51050503100401d102d01c01191142120810080c458015810722003c210490041c1030b49582d0100c00c49210340d03400c480000d42103c8615099018014400c10142d05000c1e030400055940243d8000c5103043c100b452100005041d81c0e010800c04c40c80b1a800039410640043c06003140034002c07070240703401c8040c1030115850012080441c0e803855200c0a0812455600d070711b507030b01c420740d080045000a0040742c10250705044100f44004110b500c4442e000b0034491307103815110303100b070b00950100e8a1550054 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 221399271 1250 221398021 221398033
    0x405091c030513060510230f04090b15041d010e2b0804020103060b0d05060a0914041104020412060207020103050105010e010f080a0b190f21080c2806060506040f2303 73
    0x440c01c1d100d1007c9075804a002d6010b07882110140e2500b40b04001ca00380e844500303281181c540582e81a4090f81c2c800d101a0010380e01c080250b51600c1c1c801d8804540c902810010415000d1044001e04060301d41c0800350f07054904034405400d40081e2542c002580d001403508841e9503865000481c054409a0300401038a40d00040005c52540140c000520034841514040312442d51040124203c9500d00504002d001d510303008940040c000d407860801032000100058100303501c8101c04400100740d041304440f06580001c402c000c6507018080c072401881e0900740080c00140d4900040d081c110641048410417202c1000104541100d9105504102c0090a41d41c0b2080791034074911881e500d940030340004020b01c03100000d4117030900754440045000010112544c05950ba682201f030782c0004c54565640d0240c007005640402c08031900c604c000502e40107002c07540b1020b00704882115030580241d4001c0804210902109001c904802c040b2040002110010707254200f210650350002030300c0300d502d80030300707 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 221400521 1250 221399271 221399309
    0x9051203250e03070f061d0307030c0b1b06060906040f0f050c04050307080601061e02030f0f040e160e060703031103010902070b0a0b030703030f030b0405091c030513060510 76
    0x215480b06001c80303007982111081070702c2c3c2e241080024078512600b400034000307688180312240391b0100c0115500002e01207540390380d00d03640c4540d5219103a4004014030703071011030140c1c140b00c5240028071445094401030041c0341442d002003000000018241c500994072460780f0007007503400d60b02c00005040c0e1318a040019041042112003281d1091144c0d038401d209000000c2400c04000c00d407070307040b101d441d210184141c03501050b4085000c480c245070015400f0921038401c0f09040d9900901c5c400034000d021641e518100020005410000740203188100620204920826040b03041c0421340d1b141190000d40b290403610b000c40c007400e03070b1002c05685c0010100000408146c0740c1c0140c0125032188000749007a0740d0b100c81110458100d40d4525607d5070200b0b10410200303001c1c0780d0076400242e480c030300030940d01c0b08040400d040c6c032003d4032a070340d07580d1280c0081c2030740041040411980d00d1040c0303070a0082d8201441000d2460307000280140246980d28045090100c403800302400500d418980031581c1a28 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 221401771 1250 221400521 221400527
    0x60504080409110424090305013b07031403130801090501050f07081f090203130605100308041404021207030516080c03070f21020304150905120325 65
    0x6481402001410520f00800d070250301c2c8140e80c240c0d00c1d8061198080b10300b800a02c5802d0b4409a425410f0005148002c0007056080c00741c201c402084403017400b14402e54079405000b01c3c182c0c4070102d050348280064010a01c2000c1003180890b41c220000c00c06c082e000d401c20070b080d846140301070784241c040c9620004103000d064000d848a41e0240d0020441e9030b90f907501c09407501c0402c50f51a40021082000908013012111094040301400e030040e4080c65110b500c050200da00594070040000c3d8010522000c000290043c45c0d0b011f003000d52004481e03440c43e41c891100b40035a0103404445490b450100d4030715195541030741c240124500c8248040e00b4200005001007000b9a1070040c02d5602210b000310840c0202070340380c0a401d910b040a480c5955004044500c9241d044c0b9010400000e80480d501c4480d814455100c0c280654070016074070700b407600c0c18244d800c80200d4220052420b01c0581d034040740f80031462908051b1150304240d0359070744211055241488942c0d441d0002698508801245a8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 221402877 1106 221401771 221401777
    0x40c120807170c10022a01090b18010b0303090d0b0402030109020619031a0d02060307020304030c14010e090c2205030d030507080114031902010c06050408 68
    0x107030035034030051900d500c0680040b2244000c288128204401c1c00348100c161101c0d0411443d12034984001c04400c0050b28540c40d0074007080000c408004420740100850035448000d03a14203140c0b801503680441d0441080a800d90329103002081c032400e00104460003000000c00700c40d07050500b6900c9124500000f8802c076015500c3e1581000140c03940340c007415507122072003003441610034214001012101059950f0800003000344c000009911115400c01d00c403901542c4840d966911180207918600c22a07000030721384a04035400003200c0c016540708001c3c0200903030300c2d1400000702c5401c0241c1c840c0306441081c032690b42040348103c0c048450000c2c0441080401d10040070315543d10000b0f0820403060910000f294413a42007120403030f80a01100c1c050300e1000940c00d00c02803100007007561003403200c2829521450350440d0b0347c15603000c3c034440b1401a5001001340710a14061601034180c0d0 = true := by decide +kernel

theorem cover : BRFrame.Cov 221223021 221402877 := by
  have h0 := BRFrame.cov_init 221223021
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221223021 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 221223021 ≤ n) (h2 : n < 221402877) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
