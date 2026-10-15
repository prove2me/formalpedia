-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4088
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:32:21.644665+00:00
-- url     : https://prove2.me/submissions/c84e5e5f-2d9c-4ebf-92e4-51191a56839f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 735071942 ≤ n < 735251798 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 735073192 1250 735071942 735071947
    0x6090106210c03150e0103051002040f0e2a0d0f05060d0b0603010204052713081909090c0c110402030c033405040303020615060a0e010e03070305161a0f 67
    0x2d0030260013400c800403880c0c001521401c1c01040010221007507505a0703024a04403030102c01208141012842540101c4104840c1c6400804c03803100c10000507540a1600f00c00306560007003a08980544240400a08098560100707188000101510450b014000d4a0006001c00d00b804404260460074040000d03103c1c03001c1c180000c2558600350100d500815002e40180c82c5031105c41403151400c0c01e0402c59080c1054110003240400b8100710100c445150081d0b002480c2c40801396a4003050f20000740c841050005110000504c07940620520102c8020f58030341c111490080d103041c0c028040c107108a144500e1040c420b01146800000079203500c20910012350810a4180c007840c1003e60401c001000140c400c52130103510300c0e511201901c101c82c400c1d000c81d00b1649550186481c1d02c0c41d04803305030062800d000840c0d98038480c44401440d41c0041c140280c6082c480008681483e01640090300c1c107a00c00483c8411403c010324200e0300034006a10704524000c50a0080e040c140714001c012410000c01 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 735074442 1250 735073192 735073211
    0x1005010b190207030f0b01061112090105031f0f09060f080a1b030803151201090f02010e180a1a010c030e090a110714011a060306101e0302030609010621 67
    0x2000000d01070758000e45c00c5500507040f40361020820600340030301000030318406507032801040300044419090110910590a1032a420300445094000912080125041c864000d0310b202d615080000a40705680e81103500720300300004c440c02c2e915281c0c0048010b0603a004200000034010481c6031041c0d038021092141d0052644010001860f070381c101504410b000000d015008544624244000906540c0401451600002142211113035000501a1048204240010740c820400300141c888028081d80c2c080e011f440b0203c441c00d00c01c842150215644103090005680e196804070714080c001d10f04807411035a00da40007402c0d607001005290240e00540c020400e018281d80040d1a80c40c4040c98181e100d90003800d00e9080d080c2050700c2c03812154a406010648100f80030860340313040d85d01400b5149191030381e17003d0014400080035840104500b00b401c49030b06d10351035917032821940d10603a401340c0c881c1041c00400c0041c000680c04501806034002c542080802c0c52500d40c0000084c94000040741c0c0715 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 735075692 1250 735074442 735074447
    0x15031115120910231f0f0e180105041509150c05090f01031a0f1203030f040309060203040e07110a12030f050609062112120106021005010b19 62
    0x220055142080c14403400c10040520019400700d048082520600140b00e041c2c1c040e030780c0c0c0e0141c482d0001c0e190301c0d0040001c0d1030595610410011031240c05c40c048440f81d581d002d80000c1c4e48981c0050200c691090140800070060444603121281110001c101b242030950740d0340d040b0038205c04418582c0b91603820b52401e014503000c2c007030112805901c00f445820340b01c2000401940c03103030203840e1294040034041411548684144401c095440c400c48100380003500c1004001d500140590394807183c824040404d2080600c083c5004039030b5aa01020581098a00a04124a03036001001150b00034041000b041e803200c40e03030300d806c0807041c10085240345000541c13605001e203020006d468444402c405071555a45031748a2141540070510820180d2910341c1000040c020646501e58001c5505801410f01107060203a80d02840c9260101d0318400183c1c20340d4a02500203071100c8490400240041040c1501400004084403010100300680e60400010201e6405105201072aa503421201443c9050 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 735076942 1250 735075692 735075697
    0x15090e0f1302210a12030f06081002090a05030d0309143c0d0206090708070302061e0d0e03030f06040216110a0801110a140c07090b0109050405090f0115031115 70
    0x4090044d10030341a25400d010707078280714400394200005e180400004440c00c45220700800c1c3d03440c0c600039001e01000010345030042d410000c0c0c641c3d845031003a100010709a4040005514040d60307900c0125105c00035081c0340c83c072a0940d20190352150000386080742c0c130151100e004092194281059084000d402c0103d010b40e9094500140140c829004511401c0c1d400140e02481982d00c501200c1000d515442c6603903c0d20b0075444000d41105040c05518031000015070003031084480c45000304c1c1800c5000003124160740a22004004c150400024400210034501145520242c20340382546042040030710010800540030300076250940340400c140b504d0340e03030882c3c0710300404c2c01100a209151360328003a018a503101c0700f1071001252040d41c0214529a5000a50b034040707004401605581d464410f145003c1c1405920b864100100150041350541d2a44211405110342d40010510f4a001040b11421210012498081c0c090144c904000140385a1075007800500250307198018405840c0e40d024160 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 735078192 1250 735076942 735076999
    0x302150f010308032805182407051c0605090c0a1706150d2702030d0e03011b02030c0d0e0a05061e0729010e010506070c15090e0f1302 59
    0x981030314840b000081c2140d0006c0f0f000b500d151b07021b05020729141e250295140d0800b60304100b1203513012110300c4101480d081c000d0b4051100e06080f85401410219401604020900750b486596101820300c02410700c0f0301b9895105914581c107914000f6810805041804007000600c0c12090010004080e610b0354540321552032030100320740d500d81100c807204201034000d07a100321110115507482c0c5210001084244401e180d0080c0180c01c14504100044400381580b210302d940640d2191b00e00740011844001a5034203a000d5400b9540f1914211480c80c02c200c3c40c500c02104000920f42c030752955554102d4400205c0b90100d0b00107681d40c0c0b2048002710074003802442009820400b00e40304040c0710046800056441041c03150307200d0054000d035224003580c020f0041510100715140140641c0c1040310050a205010b07030560002c00ea5646c04c082c0d59000c800c140e24000a5101d4000c000e42c01c644000c040e04098154202c0c6828500760780601039031080d402020780f2400100c41c0703e8186445160302403002 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 735079442 1250 735078192 735078241
    0x4090201090504050c0714010204030b0606160b01170c01080105031b0102010b090f0103030f0c03170c12010605090a050307030822090203012301020a03020c0f03010f14040302150f01030803 83
    0x80b03250081385103d046d0000f0308143e1308980c008480840c800d10601c00c4605899003c00c4003003160315030740140700090b000b00c1c0b20300103000d8510484e203003c00d14006541c0d0003032070422110030f1548035850b807040c20320381100500c40c140803000c40180300303a031340128030203981085a043c20089155421700403030146c03140c11055500000154140b1200280c60b102c41d0341038a000380c581c41e2fa004220301d0101c421502c1d206001c0c0029044001d03030b01c000c1c8000c0135115085a80300300791070304018561440d005035840a031301c01c1d00071440c002030341d0f4800d0500a103008010a400c8000d05a050301d192102e0b800c0740720f52490b94082140b405046582941d40d8151310700507000841c0c08548135030711160008141d0300301001c00c81c10b085035049180c03070319840080c0a5507038551550161145444000903c25840c400d504025855501c0c0c90410714001102d02c16019403000704450070b083d9040c203080203418074002c80c0740b545410714204c08000114900b100c900d411290700089440c1d8a0303881038034942c01404a941038034013 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 735080692 1250 735079442 735079451
    0x2040f1e0b030607050a0903081b060a050703110f190306080709020304030e150909180d180f0b0f0906040e0c07140d09060e04020903010501120501060b0901080604090201090504 78
    0x440361680a4501d15000360200e0314a038a035050281d43d60700802128000007503502d40f0600000c2e005601030071101410b10220508030005039075546c100001201e009624a544000300314800d82d150180d08030070f1441d00344061414000e00000001031251001e0703540c40360480758000010394800c1d441400108047d5064800c01c0b52915280c001950050f00e06400040c0d45d001c511440c0d00d00000c0350001c150559a005240c429001c040c421010401010742048c14910000c0303090502c814411045c0b0132075241d03504404510041c464124144603500b1a13215101c1541d010302070008403008481850b030341002d5107900d90317034120001080740c0700b207030000f00b03c5118180034415901000b6000d0540d15219100307500030400d80c500501e586900280c404c0002441001c4c0801c0380340d0081d40700740d405903400f80000d0314100b003c80219080d94800c4e0300c018102d4244040042c1031140c20311845000e44204c0200b01e142101050000b00f000070080d04541c8203a175201c5054003168042c1c41110024840a4410700 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 735081942 1250 735080692 735080741
    0x608070e01232b0501050604050d05070302060c010204030b0c0f03010e040c1d0105100f08060103020706060306020c03091f0807080c0714031902010608030d020f0f36030a02040f 78
    0x106007005070f84030b4100c0c400c44086200802202c0e0301949040c2c800140c1003900b0140342000f084007410f0103100503202c60145500c0400581c44100c01800725800e103000250341e452462500604280009100391075241d4180480d07206441540d04583c111064008204040d0300c0d9400d1200c170181c6258400c000469810310942d209865011078181214011548a42004000740081c0c5488901070b0341440000c2038940010030319800399000d0080640120742c0020706640b87d940e003000303c6c1c1c00030908240e56031001c280c3d5401c615003803000038810394407204100c811070405d18014081c1c0c034000d81841c062240c000b00103000011814207441c4590f411006030038000710000a80354580e8054200e260b419200b1003404400b250050040780e04071103001d0001c5140101c1c60060400a4110122041314010204082d84501c11880090803038040c000c40307080035986111603656842c83c8851710030341c4010490014460365a03404162490140d40564000c04c0241903000d04100422140010009a9040d590610b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 735083192 1250 735081942 735081967
    0x40e07020106061e0207150219050102090f01110706080403050c0d09030c0518130305040e0702070f090c1d0325092a050c010f02031f0608070e0123 65
    0x5401c0f00e082e91203080d01c0c004645421601403404d00441c0001d640855400c01000028507007514100c9668815180b1101080d80042d00e000f11401080d41c8980d004281d40c400c1c0d1a005a070442201f02c01d00741030940c0b4400149054075040180708580a124802c0c0004050500030130888410103104070a81d1403e94112502608405580c003090318000343d90403000c00c0c0c0c1e040c0141303e050801c28091854400350b4a400004400c00a002011010000709120008400c445561010f0180c40320350040c102041c1010b52a80001400707a00801e401c81c00d004100402c550042c10320f9120b070100c0c128003241e0340e080001003842c242021700f2454008000b00c80740c4210040b0091468142c9030b00701c0c410700c80c9007080102c11506401450300380701d08041450140000d0b9001d82e00400a2083c41e41c000b0031070300c0c805928134040360421103600e500360341d06183e8804401002c00e0502c0150415042010070f6007030440d002003106040042c2281440b0782c105204540d40b8081d07505a5180514040b00d50792041c404911 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 735084442 1250 735083192 735083201
    0x6020706020c07140a170c0d05060106020f01020a08130201030e1c0216140d1b090603020f010314010612060f060513060914090c090a080c100302070c120206040e070201 74
    0x800c80c2d03a004030100801c0f0018075000e24070070004014118501c0318103064030528100195401d4140c64424203640e40341e079481d034000e4800700d580244042c1c541580b419801904001854840242e564410000c980c100c98101e400c0640295204088050b40800d510050b00102801424480544610f0311000c405410400900c900b5280541c00d4460f80c01f90b48049846030b200900515045171320b900c1c1c0d036900e02d040c880309644007980038400c6140c2c3c0c050603050706508006141c01503a016a2100020310542c2451028605427100a1030f042110748002010481032102c10b003d507404010011442d100c0c5241203070468006060b000029998003a96490060800d9100c0000c03844401c10003d0b0026480e4065100e21301116402d10740002641c0040040280c00c060040140840c55014802101a80c4031001090098103c2a005204203400d404c104446c0303000040c2e8040c1090b00410004001514068094084a004075020240b182c5140f000070b006026640001e0005141041000032245c2d05412 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 735085692 1250 735084442 735084457
    0x5091608010218090405071202010212040305010902010e18070f121a1912081c0504032003040605180a05060715060b09090f220c0f09090f030c0f0602070602 69
    0x110040f11128241401641d88040724054010381000b90100203031800209406155032051060318116030040060f81c041c4c0d0842d410030b0728140c1d50780b51660215600035000300302c1e2500031901d200c2c0e040c18581ca070310003104000f09100100810920801e032501d002c1c000301c4a9017184004284180f02e00821461600000300c0401e43c0724410781e91030700a00d00181c3d0f0b05501035880030136900503283d16544030b115a0350301054074481400c1e07103032070030750710805591185900031480395841c01882c607100c081c0c8908a01264060700c08a8200f0001000001e03005400c4803e03140d1044883e155422031040041c030558082d1384903d1704074000003401800c002904502c0070030f6601104041141a0311000c2000702070140d246103640180c0102c000ca41c0a0b4100300205501000ea800e41100340140d1100e206114400c1c13000490b98404820780602c0111000c120000240802c07840400403440e907510340e80807400c61200c0203001e20090440c2074052260780d140c000f1000780c1003c0203540e0703902d5030714013a4000d602248 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 735086942 1250 735085692 735085717
    0x1112160e27060d0503040b0a0917030d05101514070503120103120c0f020420190201141003080304030306050a1202041a0105090f12010c080f090303060a09050916080102 74
    0x100150720b070f1402c1c80400c3c0c210b903000401542440d080c4185101d80343d10240219081c010000400604000b055910f00c3e006805240519185c169400d0700005641c80030f88540c0075282000300900000a04903001513640806203400400ca6000d41c1d00d081c0035120318403000e4454000094140302512110301d100f4100c6c0d204510394200d824007150101da008031161001030008111080000161800e90005820038001291003a40e25805101405656114651a601d0300840f55090042140c0a10420301000801103e40f00e4514060800c0d120102d11804018085000880805c00341440381d0300c10009400c0241c02c039103603140c40d480320001660f00d0220807441681001004400720590200d00c1940c04410b854090800300c6440402c076081005124164011080041030400d0780824000c80c0d4240c0000e4560b0511401e140e882c852804000900380c0e030320750f8010000d001e61500c41494003421908000800101c0d42c60748404c090516400c107245110000d842c0101241c5c03e0019401011190920b4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 735088192 1250 735086942 735087019
    0x10030e01090f120c15020702040212010810060f0509180a0c03051e0115232106010509040b0406150503030c0d02070816210f08070302011112160e 64
    0x440013181d00404000d0002c200031450000480b03140172a0f006480903520050016040458000050440301c000742c0c04600a03a101a201240c5000c062040e0805445a020a4440b031420480840c443d814003500b60f11041e500b255070590008414003d00070b03030f907900061074080c1564a080aa940703461100030b40040358001443d403502804144200501c0960b600181540310b8079106000300141e1090801200c03048040ba09180b140d550480e501c4030151038007000002920000d143d0910b0140c05801043c000c41035241400041441007007003550003907000f60041000e8070100030101030400c260384071a415100c00301d91007907900b8000c00d400400e280c031542140c10103075865510f66651809008000c81034902500309220305002a000169000d01010761600160307001c0d5581e1200c4240920181c07001c1070003140c42002c1590a00500000150b070b5122141004103401031f040c103155024241d000107001d071828031840a0700840490040c90802013650900c882d000d4984085845800e11801c03429005 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 735089442 1250 735088192 735088223
    0x2090d080918150d150c080405010c080f0112171c0b100509300312070216120f0210030903080c04060f051c020a0f1b1110030e01090f 59
    0xc41e145220344103142040a00f90a2801444025251039000fa510b581300d981c4025102c00c101e001700341c0301c1c03481c0759102c2800f8600360800608444070170901c841004491000d00807081180280c4905540600308104000c0300e175480c01a2031018454820030b071001340801e04501f1200d42c03500a4407a168002020b100d02005c2c10200312940170075100c0b000108000784441401401c1c450503081c100c100914032056003038807040009890f210400746403400c59000040031176814001d65403654100c2c1c079038001842e01072480281c03c0355041d00c034010414226000051042800502c4020141d1243c0180ca80e415100c0c2c5454010f0103480b0010040d0081204a00403460a0b402c0c0411241160801d5544c2101082d4800c011a915440980080e81030380407030800740820180c520040c5a06c5404d51241130f882100c411015220040c00c0d082d190222440c1c0c0c5001c1c020800194504140c143c2c1281c1e0200b81d40d201c00c5003900141020500c41c0780c3e03586001d403400c04106c4402910240a0300a0034a5002e1000303 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 735090692 1250 735089442 735089479
    0x60112060e0a121209050f0a031107051f02010b041d0f030415180803030901060f0e04050d0807050412050109020f0919150b03040510060815130602090d0809 69
    0x101ca00a210141d1015066945131064070081110445000b000c80c82d1002a01d072585048000c4c03001446503005401042d0405810040740d404c2c560a640285c01018034200004a1045294640c0c0b00f007a4000c24aa0b0a1107200b03501015840c98000c0c000c1040000951025040c09440c51101c0090705c00c2c0300440c07117103c8001042d5005c440080d0001c804c1d03c034404108481100003104036043c132400d041c1d0081111407040c00918441c0f20618000515540350090700c0308280b249600240c40d000001082c0310201d000854600d02040e030f41d00b402491521041000c491501c00c0c0c0c0e12400d20b6501c0d0441c0d41701002019005070018a000f00c0340c0c0030810034083c2c00c03c00003034005d9070381a203584044004c1da0200c0f521600955001c072101011041e07819a2051000050b0740b08480440303c540254111008190789486a5405000000b004107008081d403202a40020f20240400c0d1002203040039180070070110f60125154140702a09070080c9907404c1c50076040c00e40090700c0146c070440444400590b40d00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 735091942 1250 735090692 735090703
    0xa0807030608151503030715050403080105181b0c100e0c010e1309020103060b03180714030a03080a0605031e01110f0d05070311041211180f09010e060112060e 70
    0x40d0070065424a03114a41d070031143c01c220b002c135560940014044070001c140390215503d00442c42180114091500e407400920b04401601700c64466000807138850188800110296409000079912408201d24108010010f00909076281030b94410203030060940d04003600004284440302c2e04903040d5005103c01522002100d1346200c1e00301240c1903040034160350541004081c28010f0500141e12515040e4503102a0700c11108a04844980510000da0032003c0215900402103020700344c03842c40100740000d1f03d5400310480507041002c2c00c0041402c60003507500c50001032800904a440140c0480500503c01303100d095144129441c1203450041c40310110101d030b2125446a1507586440b4072001ca280046c4000b03400b004c200350b665104001e240c0e5000780100090704192403002003515051820251f0001000d02850080228070b030350f5001040b542c040160002c0c0040c148103c40e0b0f80300f1091500504101c40703818654407601000165803002c000700d49131400e0240400784040000111324980d03e2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 735093192 1250 735091942 735091963
    0x9032009010911090d0c120f050f060402130b010216030c0f0e01050109150e09040809120102070210030b0102100903030f050a090c0302010f090807230108040302060403230a0807030608 81
    0xf80710412081e0242d2030070054400078584104851281940c44007002582101c22080c2200e584039200445070034403200b0000d041060300e01100901103441d0643c0454500d4402c601c05000d80d51311807000e1400383e8024000c0511040b480111f6007402c030f540e41487c0c00c001843d0721a08e42c0390b291500e4040b516541c030f01502c9040e01c2c2c060310740c06400b0b8a80840c4082c0c5240c500366030710070001c101c3c1e1540c055a590340d400c43d000380d010300041910b88910f041000180e880700d0b0000b08aa031302c104a98001610b80c0c0702030840c1c404803418001001511180140d04003c20b21207100c01507031a05c0384090805405501811542c16459400c002d59500e4907003e030200c5003041070207040c2d803414031005c000640c0700f10841c5400280d075180c141440c0366034510943c680328980e00b05c00300c10141032003611155000b2031a07000f1a035031b091030300b120b043c00c1c2610041e4803170401400180810903010714160f0b0a0504407421aa2440740040280e03a41c50f50b507000814013403058440c040000d04000c0001034003400007076615450b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 735094442 1250 735093192 735093221
    0x1e090d0e031513060605120d0f1d09091f050a0510062309061b011a060d0c1407030314010f150e0f04050403120b040c05030f07090320090109 62
    0x1a4450f0000c0c140254803641e404c0324400e44400e4081100d8682076615083c968041c4000c0c1480b142c1151301504d99094000d00c1c404000a02c41c0f00d80894034007241014405a0590304001e40c1d86444020b036007403e003c01c1c1100c1c80700800308040b4405541075480103100710002c440030813145d200c01000ea140303d5003a00c500310011342e16a401d0800e0421a880c100301d2010460889864603842c08041403040e0040e003164140c0031142070304040f40910030301030b10280c0784540340801c440701b41403000030310140a01c0000d521515680d0010310110340c081c5078586c602c00040700040303880e81c0c0c4e9490000c004c2c2c50350001030824a042c1100003d144040390125001340d600d0704203600701c000c2c85003408690f0700c0b5500220b6940034114600d401c21a8449110780c0723014074065900c1d038031030070304000302c40c1e003556008054580240c1c13070007440b1286250710900f500d800410f8021002007548400704101c6412400741c00182050a000344c581d240e00300203100310710001e031060b50215501d0b0f03030703c0070900100c80c1c028010100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 735095692 1250 735094442 735094483
    0x3090d2102180a0b0c2107031215150e040506030c0f19080c03060709120314090901080606040e03070f020d0f08040816080a0c0902031e090d0e03 64
    0x411081a401a1001000c40b550300b18000d5203240000b0b881211503403041c500b8010008451528403400c0c4840c1c040e00c11903805c5140079a002103c503482c1840742610241c200852403000c4a43d412040d0041000e6a140d205181a542c0d04e500c1c205101c3c003010200c50001c41c80091075a0b8560a03d1f002e00340c82210010007078090410303103c0910038039602c01d1a491764441000040000c100e18640e450201920b4240018808540c1034024545020b50251a20080c09504e20b8100320303462803000d43c6941c4e680c0c5450031511450f280584403109020b174181560744007201c6000891000340000d001489050111401d000490301d200100346c40f0703c030b071200182141404444010141c104412050103292140c034400300509141e8480512a0700075810aa520741c11035032038824404006110280641081d0001d8040e9042554404c8008200e40c4150085113030040b0018076200010b210b600081a04180b04240364076003290140c2d29900045101004640da080301c6d2a01e6080009200c80d401440480420 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 735096942 1250 735095692 735095747
    0x17070206130b07050c0a050d030641032a040209061206030c12010c080c12060d02010219030504050915130f02040302150702010305010801020c0307081b1203090d 71
    0x502c2c12004100c103090100c10044a2411141003004049590151001d003189540c0080010241c81d101d42c001c14011a101d0340b4004100b0040c06210bd00c0406000d281c103c600840b03070850065400b81400b29403600414035503600120920941862082003191480210360744c15041008034010301c0c4026030805003e1100110b80072244281c59003003100141102c40c4180341c1c80000d164250020560120759464100c0f1800d2142c000700740c40e030490305010002d410189500d07500c40c01010003c00462141d0801c103600d0065900a1182042c0040c4c0190010342410213404c0c040c003554428031516004e030031020001186050000b6081400e008010900b1035208400240d40c00603043c04a5000c0201d6420040000180d5038111200c1c83e0034000d1326416203039031641c0000360031940140d01c1800d0341d0f401041034680b0910b021045071400c9500440507034441c0107803030840341b8100d001c515030700c0381e44920324041000c100600c002e144100d240c00216541c2c0e0f800901c044440d0402c490b101c5250703080d40401d01 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 735098192 1250 735096942 735096953
    0x60602070b091309051b01080403050a210515030c0f0d0201180504090b040614010e0c0c01090605010e190b06040e060d02030a0b070210090b041403040905071707020613 74
    0xb0074100034000c004084070640b5094002c01ca800c02002290f0340e9008180080c00e00c82c0908070400300e00030901306042380e8541600d001c1e00c43c0c81429248e00030461491440c911a040145050681c14074102c400c0000b03103080d208400100d030320404064480c0c410800098441d01c1c08004051b0850b070040c01c0540303915050f50041d0740b02c0c01d80c2488942d81858888002c02d00f500c8500c035510150713001c2c445885a50406040c16000c803aa046244034225410400505c1441002c10311290450318003d502540c54052510301801003409650080400f030034040006680451911698010410346038008034500d0340c2c066043c211141140c015401010621003046041c6203501819070001e0050035207040074585a00003030501d800d03900d049800e00000821b00c81c0321641000020389681212808112042c2c3ea9140d105103200014001859064a01641e02803407a061090324003d15800300248014202494090401d008807943d020000b82c034180051012440003407420b02942c5010540c0c1a03030600f54454 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 735099442 1250 735098192 735098197
    0x210060f0b0f0a091229091209300f0a0c0e060607060c181703030402060304030903020312030402090a02030112200a0e01090c0e011403070905060a0201020d050a060602070b 76
    0xc3c00c1c4203000c80c000560081d444403080c9072a2045140201030356012590600010400c498814100c49942c10040308034000116000da01c103080038081e482e00701c10f4001503007584081c8165042000c400030f20300680700031600c3c440c550540080a44804503110724483e0307901c40180a0207804012260820401180c140c89103e400c001c0103001c4510304041d40c1c441070140c40d208084c003000103550102c07480ea804a80b04d0643d0143c00c00c03120740c7c50f041c00c00458543d0359000280010384074110000128007018080e46607080156809802e41310308180c4500d042c00705400c1220306900414800e800103407910320500c2240c2c143e81d4220728101c6000510307194520100040d40300120307507403451901d0800310f90b180fa00180081884800c1c0ea042503060500640030fa44100400790140b00c001404a901682c100b8003088022002030700c183d44a80c1c4113202280d07080c00b240d1110781c000800080302203100d9410740082c02c88041c1c410f4207000ea2f407611540f40c0100c031a248515001600308041c01d12090000000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 735100692 1250 735099442 735099457
    0x60b03070506030103030f08070f02120f071b03031d0109030f05011e0b03070803090d240501031a10051c060e030301090606020f0304030804090c0201020705010c0210060f0b0f 77
    0x2100e18150300c4801064080c0c1c0282c0064010421510a000403d58440307d01c5038090608c5c60640b403600d0154030065902d040c2d00d01c940720749180100b0b200300820203070016503a81c01e8000031071a203d03c00750640c10496101c035001c254002156a400c824601c0700c0385144c00c01d92401030351025000e600d503031280c03400c51034071100840c4c095407910014240d184d200314001038051086000001c071404a101018a002410340c84070007160001c2c041d1000b50380e500c0c02c0441049400028401550b034207211031401b03007200c1500a05030070349010004414071040c0d801c510f4442c0181032400c40e0549450b610016160102d210b40c5e6442045034500201c6040182d0150b00058490180820a9a810718409085030400d80043c009180d466034200091641040110381802007240030314500b50454036a117040b4496030145a109945601400d84468400d41c11901d040e80c01070020020702a6010009464080c0d200d500310450f410054003254808480d65450112110a1510342c6003420844294155030807902 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 735101942 1250 735100692 735100699
    0x80702091f0e062409040903050c030a05031806090d0f0314180706050f1911061003060b0a081c0c0b090607020607050c03120c0412060b090603060603060103060b 71
    0x1941d580c50105400142406040c0030b0903002c00500e050310600c2261104440381c020306241030040c03500f00550300e004a90303035180306070340203d1103000506095405c3e1046200300d5901e480001000300440c1e42c40409103002e81c818100840c10150405d081c1a42c03503005440d94180c6400c1040e1020249024015a013641c400078240401d24802809420008050854030700303103108070800c4c00c030201c984240a0352028114905002d41808804110180a80203103690040750503c5440391074042030043c0009803c11941c1011141e441c50030003d014521131092004503021410945800c0151604440072030581c5e400c90000d00c184540211700ad900038203e4100c0c42c081c44403a0700340002040404030715034400c0144030001c00c1e00e402c0040d8000d1801c3c2000300a501045014407038502e0400c004021105903000104441e096034a420032810f9040c460f81d8010000b401d07080c660b00d03082191a401c1030505040440701603100d0780e500800d00d51036840450b041e540c150092001032000403030700e90160760507101c0607 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 735103192 1250 735101942 735101971
    0xb18150406090302040b010306030f290108010207031701080307021e0a03030f0e041404060e010e0609251a0304081e03090c010c0302030f09011206030c080d0302040308070209 77
    0x1855103940a500003400041c50080140158180340c09849010942860200400c03460745d1580c182c500d1203008010150141100e2108a040805007400326010414030813002650b554401c86000b07610046003100803841c0011a4035074200b05a00c550b04075050312010f5807802c0010303400c1100f10038240c007540313408102480503420507032a0300d00d00401551003a200c6010300590400060721046000160511030742c100803c4600440e800c610403908568482c0f000318010f41034800783c9002d8850780707103c10751a2050b41c040094121340003846041c150390300d1101c04c5c1e0381e580c82070081c07001c260203024003580399030749411075418584100700843c1c3c400c0c055a100d605040400f00720954181c54002441c5006030084180b00342040c00740200241440242046042c8260aaa0180d100e0185140f01e011031038000c0b40350f0b0701c04c0c0d01031000e4007800c030120036040240c1e0f40c81c3d01c3c25003240320803401ba180640c841d0100e5201c8845c0a44202c80a80e0b410460543c01d06603a6070801010060003000403400c01c00b070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 735104442 1250 735103192 735103219
    0xc031b040e09250803040b0d1b0f14091c031b0b10060c02030c040b03190b04110604140d020f0405092116060504020118080d08010f0b18 60
    0x41c00784550240d5802d030301a2021a8442d114442d124120100700302e6801e40b441001c01450000004840841d030100500c1e9403a80400c844100080403d00a00c22031901d040128074805039120034440703440f0210f0f031203200c8101c0e5050003104240c061941d1103038005801c0604418040700c920b1240c52030a110346440a100d2079019085a00e40546010491310040c003c0203002150308448607800141c5020301d807422409200d5000243e850461402c1c550141c0c0c1d840c09555140c1d241844604010308a840c2c03071403c082030700c1c500004001811038095030498401c00c51241140b4001044804403050540b00380c109845d9101041100071211740f00300c0c0d0013000ca03901c000c660b45544c012644150101c0005d02501d51420541c4060740e450511401941941042080318810803e01a101c03029045031000400c0e0383c0b107100584500b00034803980403d13241c4806001440000000b1490380c240c08981c1c44000c035999512000380e41c12618060079003074601c24801e10030300d140807802802c800c440007030010381c1841d607 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 735105692 1250 735104442 735104459
    0x705010608070e0a060b070206160c05040e10060e0f161e0e1008010b040e0a06081c09080309131a040e0102090118050a05121c09031a0c031b04 63
    0x105500203e502d100240410a13548668401c49005050302511240740c1a1540d0018119204500081004c20031040007030050062015600e00070300000742003005542028010346036200b0500c0300f9100380300d041c10070125428810080d0503000d85960000e0f0340329a16007280c0c006203c2c0d590035142041064070702d11804001903a094541318107a130350702d961602011440504c01451540c9102005210941c2c0040001c50780440440c3c00711a8015100b080e180c40d01c45148001d0403c2d584011418414480404004d0074540741e86019070328035031584405270355110344807a01c07030080f8403241e5030000c2c0700e86440f11400000e801c440035070459000054250000340c0c0008007114001d84141034903a43c0822180503558019030311030010101c1501c8400450329100c00604102100e000d514040e00400d42001600c0c00c0400c805005403140e400078440314260310400920300381251200340e806050a8503c40021a42c0302442801041210b03042480c6a8405000c4a4000848400303d040c811041000155600c0f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 735106942 1250 735105692 735105703
    0x10804110405040c0608100513240323060f0a05060d0b0a050a1503150905031c27121b0c030c2603070b0712020703031407050a080103080705010608 65
    0xa121311000c071001810041c0050040034018400780b19044000c5060110741d40303804200444003200c03803002c40c604214400c1160010080e42e081030354800040340c0401040309181c050f501001c050310081c002103903158100e42c1e4072141130300e24581c2d01d1011008628507a80c3c0340c0016521100107064000880f9081d51010714114080ba10884516910000e10032040030314043c1080d000c101d10142029142180c941101c0350001c1481c200703c0c0783d40c440c0b820003001414002c1d40c2c00f1815110204000b8200c10203514041c00d001c40881e400242a40b040c407400030350700365241082c43e40280e1001800e0441130701c255080e01c0c1950516a198045102d0703580050400c15503a00514400d80307584403614a814400c1401c04903490895690f04a02d50480140540000c10745400356001000181c2c5519003150540344142201098000240001000d1042c19010303041184211040c11000311241d603110402c680c02d0003005102c10000e58218010408607024001500300d95000300d0001038000e41c0c2d080d8245c5131a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 735108192 1250 735106942 735106951
    0x21b0d0305070e0f030c10141b0d0801031a0a11130f06170703050c13080a03142a0c1c050f01020a050a120e010c0201060e060a080606010804110405 65
    0x60348071801c015100758040c0c04100d0000c0142c841c5101c0c8600000005e0f12aa5180a01070242c485240007464051141c244507111400c0c4c0041c0a075030303d040c10114207210880b400c08004502c01c000d6140c00c024030aa0155040b2900401d0b0b0403142c4c580108480d01c8020003628183d21691280c0c070001505525500400460b9103119801024a140072504010b00f821613010320244200000080001200c0b9010f20340e000d803103482c0c00192651448034940c1e080c05440b07214040709100f011b010800c1c01002590b00b09090084c1c48504901c07840759101c031041d210f1000303a107014400f010081588000d060b2800c1c0d011404640640300f1420009011078854a0845510000e9025800000d400c1c000180414150004207000039494200c0680700a003a5224404403641080b80c9000d8220910140c0e612410304100210001d00c10507541c010000d0290015000e011030300c41c07000e004501c15240800c0b42c5400c60f03d41001030603060350380703000541e00c14a0045c01030314104039030320761000e041c0e580d44641d44c80f8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 735109442 1250 735108192 735108197
    0x3011e08191104022b090f0303140a0902010e010f0309080c0303040b070804020109050f12010e030417030418052d0f0f13170d05010e0a1404080706021b0d 68
    0x900c0c000c0c2400c2000495504002e805580704100300c0040e00c58114550341000f130307220304500219044800200041905010142411034220005030405515400039032100744403040d4001a074035100048401c4511609000b40030801d100c90000955000d0034504583d80c085090000c0e500076141c944019940c0034452401d01034100001700010441c07401419a00076499240404551801c0d03400a095807806000c1c8601c00c0e0f2404880c071a49071383d1501e011894030555002409a11001c5801b640e0700d420502840441800080540d001c01100009880c00c0360040e2122818110159081c00010f05020b46255480c02c4000c141001e0603820030784982115085100c104810315005031107400c1c0c488050711900010140c1003e21585104001d94040d500d908040f101c2001e000c0f841e03c455051003210250200c4505150000441c3c01e50480c00e148144035030441485034441d4030310a405c0c4100d0032a0001c1c0380100600018000c076490340d000d0020b290a82c41243c240078450810340c1e203003c2d6202d220800 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 735110692 1250 735109442 735109483
    0x8090304050306130302070f0f21080a03060e060f060f0904110403030806090703022701020316061d010516050c150108010b010e03030c0d08100918050d0905010503011e08 75
    0x10154100b00301801407a003204a0009141090400442c01106208198ae080700600500300c0303000b9446c0b070320f000959010310a2650baa10241014000e0310321442000000c101070000503409003802c00003690f000300010b2095203000c1c011900c3c880c0d690403080d501d54100b56240c1205072070951740c0004001840c043c1d2505c0f01c40340340c12420003c9400c8020300322002c060041c0071901c40b18600a44680c0c2240c0d80c000c8101c01c031080000100d1450284828999a2103040354549003403100700d5120100c3d042c82d00c1020382d11084041d026a003650030a503980f00e00409800c0c400415588141d0241c143d1401150a03507888403024540c2c404000401c0c0c0102e840d9035510700d1001c0c9d140d038110b2680041c6001c1074010b141009905081d094640d084040c00c41c05010313245d8000b540c00c049030072100d0b000d0b10340214100003958880d84503a115800703090046a291103006880d1400b54084c14403081118416510300389903a0805a102d072204600400c6480300045c0480d0100e01c45905102d010416100f9518010 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 735111942 1250 735110692 735110731
    0x9130905061f09060605070204021606050117010609020a2a0209161206030803130827031006051e041d010b0109090b031504020d060203070e040506100e0108090304050306 75
    0x1112014103030b11043c0340c28079150701004203a800c40180c03182d283c1c0488005032200032020b1420310303400c800c40d0003e102919020010500d00014910b91000e06030110080150a4840342040124481d00c203124010880d02c0c0c1040d0b00a0b12407000200c2c0f9000b003290311400000080c0c0c0401d501d01d006075010000b111a400c1d041c400182c0c845400d078502410f0741d2003032001515544400d02c43c0c0c40013a00f90b5011041d0800da0f1000d00110741304441e500c00c1201100d40c58050611100c404400074681c040d0320070701582c102c1d1007103802180620300c19141b00600c2d80075000f00c450085000d91460984060b0066111285259240b6840341e5122000c1d00c0000042035003126040010041c5040d0740054404500d448116626030700e000840c40541403c06641c01c24503212070000460352901c0394001003501c0c2c000001c000c812507222110840715202a0b806100b242ca550082010149074400d0040024000420f2009a913114000040e0071011541c1900d14064845011a0030544112120030f031401d10a001d01 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 735113192 1250 735111942 735111991
    0x907092408130308150103060812090405010f030b13141e120c0606060901021207061e0b03060f1510081815070c1a040318050906060913090506 63
    0x550024580c200300e0305008140e40c01400c1c5a10181c00c0c000c0041c1485100c1175980d00035400b03e40030384250401c0b1244070340c20000304003199015078a072a00680c28000001052002c002801081c0c030b900031403e58241e80c61070710354103506588a0050742d8940e122152854035000901828024024420180700a8480e642282e4600742e04826061400c03441003001d044250323030114819030014402c030b514950321a01100100c0c60b00e0100d41d030849422100080810800c83c06501400011076141400703140c0c0b003004940001201c1860746a140c041d04074000040a405002101c96030000744501143e5100a00c1c00105500300d0b480300201001c00c14440520240c15480c05048030765112010041c410014820100b5a0f05040075001006002c5030b006510100420300c40b11b1000d0755000c040c0c08189103840d0030001d060038180e4440443d840d20700207011410f4240008024819080900106d00e416550410700010b0049244404007007a56075072031038009541413101501500c00761141c00034028000700c41 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 735114442 1250 735113192 735113207
    0x50d0c15020d151401350c0d0c08100816030f0219081b060711060d06081902040b0409051e0a020310141810020708120c0408010f020909040209070924 66
    0x1b400641522000304111500d20b03004060142010040f402155031100c0303c0d0501c1c01d0188400c82145581001c04916602d0b81c440d04c41e03445030050389140c036141c83e540c2035079980f1146041300007810003046040600c0420064500701210510141119182d00101a49121028442c1c0c00c2112203420a00014208108002c10703804020811550503107071203031030b84d00c0c140340d400380c482418002c6030302044c04800f010403075104500500c1c000302900c03101744040700142c00d040d03540c2104038031892902c0c94071149400d003841a941000d92102c001c0c00086e241c4620307400c090081c05da292100d84a188054070060300d0a1020b20308102c1e00c88408601d04844100d0f20b2f90030480103081200c0c0b5980d00008045420002034481808074080000603a92a054202614035105e8031100b150341c0c0c0740c4c0605019070b0500d103400501c00c460400c8002c1006d480c0c21003200c07050f48180c0c41d000340d1104001010402505e0040e10898001c110380c100300d80026500e90004120b0b24010b4940003c07010700708112500c5a800120 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 735115692 1250 735114442 735114467
    0x3120c0d110f0109151d060601260f04030909020a0906050c031b06011a070809010806041b0f08090708030714030c121305041b0809010b120a050d0c15020d151401 71
    0x15806c61341c01e140c061460f0f862400030b2581d8104000c0704480d090034007240d142694200e0b8000359080f018a0603842074440c858040d60708600141050000241e0b4640324800c0d5000f80c44296070301100f441c5445403c64081d080035002c030099002c100241d2444468480751080080043e2003e8400c5602d040a004101d000b40000301100e4841042640000360206c821100d940909081043c00d944075140807174001d2642d0030944a49022884180d4041070304030031a1010a030031591440103543d10300710040c3c1ca43d4154800c206950344244407020000c0c40040d071004036100e24030100c0f420b081807403051920305401d0015000348208001502c20302e81291200300000b070070782500c003846074094444d0140070207081020440d0411804801080000728290042101076000502c542402c50303926614a485811204049416200e03071516480a107000b2091f0b81c8107550010050100c1c1d1001246040295102c10807003440c45540f4180540102090303446a0090709500390351281800f01400090248251000c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 735116942 1250 735115692 735115721
    0x1181203080906060a0614031b180f03010c020a11030f0d08100504020306010801030803040203151609120503090607060608120a0f32040905130203120c0d110f010915 73
    0x501400002e4004620307040804900f540035a4030341c0e404002080700030030003040400b924000252002e0550010903c1088040110703000030811850bd070800d0b00301c545c6a42d414000d6081092070001280d10300c2e07940c050715003002d011740c0c01c030044004030301c1d0400c80c414800c3c4000c40c041c60244241c070384918251402400381a43c0c2180b031030809100281c1000d40521005122110000000b0110b4501303121140c0340e400c030290004624286004550345008001e040d11001400e040800190325100c2d8401c880c400303410001840c078214014050185a41c0300311404c0e41c00d652264000500340004001410f60b50010601041d140d480400307009100702c0d02e0040240800040310101200c0c148075805441003400000040c0003850084606a0600d0040b58490f0307014034074103c2040300c020a804000e261040c403c4050703529004100410b0380300c1d4090000c86500d5903215043c180001030192110703c80300b0031004212001e600301d03d5810303421b460a807581210380404800b44c51040e0b510354002d40d80b07001070301e1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 735118192 1250 735116942 735116959
    0x1103030408161b0306050618060d020402030c040e15040c0f140c0a060f05091507051204030e1041160b0c031b16020118120308090606 59
    0xa4888403518000c000841c41004100300e2190b040007100002a6540700b4800b5440c1a010750301e04120000b007008540c224020070210b18503c000001940e05030f481050b000b00785074800c01c020f400707100007034100411388507444004100200d1070f0a2090441c0b4030402c408004260030440360024402921a2926120144080e201100e00c98130380016010400c0a0381d44040c03611082a0400a46001014980601618501420301a2003110380d001076118200e200e040358504041c49050180c02401103401c1c0700020b9040c4034800c401c1e24040e9106410030700034640080a00d0344c100004250500d51542840410381021018090710b0303901c40301d544240070082c0d410505100c07400c1c8640c2030300c2c0c1009010502131340024811014441c4003030f068070442e03009403250980d4230b44101c0c0041964000d8501e0303101150390038040200000f44400b2681008507a4101214038059940107503290783c0003c640c1c040d00b481d04040861031454040c10030640b40d00a56880705141005441c43d0f080040182845000e015003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 735119442 1250 735118192 735118201
    0x201031d010b041a0f09040c09240b03010503061302040b0a0915140307032a0b1e070f020910150c350c0a05010204150806120d0c051f0507110303 64
    0x5c0a09810000405603800c0425039601c3c60b02c084000166007200100d54500012603034654080c06102c0211008000c12400759512500c84000030b0100340b099640c1548000e00003021100d424114003d007502c00303040840e0b03119520780002c00c104016081110781c165601c651108074102e84c00c41c0d1004003070b8001030340310411b07503500400e440e103500b8000a81a055080c0c80c070010000e02c100c0520070049907164490a003a2101c10000c1264401301600b55842143c107030f54008020084c00311a1044e912484104d50000682d0900103000700082c4074113403040c60b01e80000b80402c1c0b0b41d40c04a203440e41ca80d8840212030001e1504100380c255000c035000c2c43d03510710b051600d10540c24550394010710b01c41949c031545a20512802c40d1602404540043c072950010600040741505081c03681202c0240e611010941e075a1081400344200c6c0101042446038400e0012904c0d1900807000070600342c4c064400d070fa1054140f12088a8000300c603441d410480d5544100300150385600622001c0031904120185203503051 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 735120692 1250 735119442 735119449
    0xf010e07050c0313060806011d010207090c02030d0f0e150c090607140304080303151210111218010c140301030b072001200a17040201031d010b041a 65
    0x200140010180140001c095011070003c000755564100c070300d103400380c841e5284c40c0020000746090769007070302041c0380303515140350240650f4080c1d40803d03040c0c1c000e1000500e0010818094014102c100055000401c0610784128103801400708100407803401003a0100341d8140c0c075180c090398080f124420000c40080c4103406c8d00580c00c98842034011100e25031103020b5070802040c0f220040e07420040902c4001030029400101101440c40351b81c0030011811490303071043c00e0001d4001c4a4070812925000300e120208400841e42c4008400d51545407851b091800451003400302007015528001c020001452100c900e41090042441c52129440d100e514110078240c2410180010301004000041480001d02e00070700c41c01a0000102950342e4123600f00090b40517030740c002d120580340710904513099034040d28010b41080031240c6454007907a881d40603603180c03800540c5542e8040c000301d0405880c1d4040311540b400c2d24540410710042040002501014101040101d9075200600001c0301040c007440311587e40c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 735121942 1250 735120692 735120719
    0x90203101a1309020f0408030c0f01140f060904060e0a0804081605060d0b04020d020a0503090715021b12030c070e10050a060807200a1514060d1103070b0a03050f01 72
    0x8070a101c0245e124114100e00b1411800383e134010f0402c81c800801c403014005da00040c1089140c8030a0000c11401d5006c601c03810841000b2074860500041380302c0480c240303042c00b80c59958002e00130100010020603040d40307207040c03215a407025900f01a012030107200069007031024030301c2044000900d0311039500e4800400c00f01e001e40212221b20750780c4c03554003100503100c1c1c1e01110405845800300310741c0d031801e852029010b60800d9603041d4082c4a0007034003244035000382e100640c40c0b0055030001c21011104510303444810900c58041500055483d21030441391104001924006c061400505890382c201180c00c2c0390a10b0003041035407124113110082040340c8803641c500302034400525024100e0f0b07a800109865101c02c0c40c1901a9507541c8003603071800c500005c140441c240e0710400400310702901e82c90b01207050741d0b810170b2043d1121000c40c010412514200303c0d090742081c422000c40b0b40d6900808006803d06003954080072400c02d0004224011580c140310f0541d0020743d101c611090340d410a442c540500 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 735123192 1250 735121942 735121949
    0x1d010b130506070c0b03040807050f01060819051207030c0308070207060f0c290105100c080a2001051f050103140f06040209060705030406140c0c19090203101a13 71
    0x114400038180f401e00100c201c45001920301c2094082d0749003024a00440d0650103180300b550b480c020078180320b40038071060103a40d00b01c9520100502201d02d4803500c003011000c9903c002c40d0300d4861210b0040c000c0b4086070141946070b000b600d55000c030404c141805001400018010011500101e4052254a070000c01280075042e080c80c041c800d1003d00e2512114031441144041307210707141e000000b90044d07106910307141a100140c40d00651045001d800380d40d034404d406030081403880c051208443c0a441030007040342800400da0488902c20303022000b00c0c2168025209688821142c2c0c01c1d01c0450001c502001004100a20301006182701c8900c01c3c481802d00a06900150f059502c0030034001d644e144c0580b141540d00408041d552507403840d0041e960f078040d110310301c08201413080000c401c8911405480d0b4255000010f0003041d0500c00410047c03000c07420041200100100303020660070124400396104181d81e042aa04040c00d01c06d13103103062520f00400300700000e402c001c90305802b45546452400c5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 735124442 1250 735123192 735123199
    0x806010b0a0c030909090c05010201150302060d090c120b0106020d140711130c1701140a0b0309010f0f050f0604020f090402070203150c0a18050a0311030a05071d010b1305 75
    0x6840c0c41c40d04480c8501d0b66401013064070b0501c441001849084c107c11001c84109800070003401c490088032500398031203440080e6200000b40494070080016801c280040c500c0381040d00541500c5403c000e03034140c1e054800317540c0000020010310070700b0340421a0030711945007801c0108080060000b03107101841070f00d8006014044882e40c01c80b107507c0e0480c60b410701c040010801d1129081040300140325064401490280032466000015005801da00d0500e0100000c0e010580190602c00c20917000c0e40090005200b0350342c0c850a41c0802885486081002d0b5105d481c0411181003048001c000700b403014041c103205900c100958083c5800f100d08440c0f4240055a025840c2c442600001c0d0510300045d0038034200e000f1040810540d00f507403100901d0654040d81358a00c2c800044400032081d4021070003800d0300090212014400b2810414000d162004014200c5841d8421555a681001115071120200000c03090690300c80380c1c240c2800901614081c4610b60502e02c403500c503808005064400e6600 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 735125692 1250 735124442 735124457
    0x11030105100f020c060301080307050c1f1107031a0402100f08061903060c170a0c1706040e010c08090d180b07171219090c0b09041e0b0301060806010b0a 67
    0xb2941d00034012030038500001005030b038580d03941d0202a0b46940c000380c401c0780c00e0b00400c0f4180c0e1951801d024514069848024002c0c0007082030307181a1000d503182c1450090038032032200300100280108401040c1015031688055450810b407050050070346090303101d1014400e20010100d4290750151009034003480c00c0383c00340e40e240c5500d03000b9241c404c0181c1010b00780c1c034240720080c182c1e150041001000d810790144000078a55500100300c2c11034006042d1940010300c5d030074081c2d06501455a03095000040280700154071455410700c1400c5426082c8040c1c04582071408004013404140550001ca0149040007a04004a42603100b0300c0c40c0c940c000d40d182035101103610030a02c41d5180c06902d0202c0340310303105070f034514003034805d8226000c00300d0b551104080043c100e5040242d00f4055800550345c0110b03503007401c4d07003403250070102d41d00030a5486810560b40c10010340e0581c0c2304426400440d24007140010f22075109800e05083d1210341c2c02580180e03204200411020043c40101c1b03034a44800d00d080036 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 735126942 1250 735125692 735125717
    0x1021206130902040908190c0b0c030703020426010f06031104020714190210030e0606040e0c0d0b01210c0b0906070215120901110d0f0f1508011103010510 68
    0x8018035182d00081e4005140c20b0080c820446100c0003030815103d440101c54010080c103004441c2c84190301d0004004045c2d40000c141d1202002d80559005142824094201600c0d41d5014050046040c030401010f03c21041c0c2c807001e41000c2c0b055202900010388140209403c40d07d91070511126441603074000c03070b400035201e800d108400c0120605000908140c504250344800127a031842c4d102101039200e1540c801240d007100e4064801d0744040301c03510b401341c11250b4030141040014178003c0151a8a402417a0410656075200c0126010740d0344900d11083c215410030303074041c04842000c00c00540380c00f101041040400c0900480e08111004580c0c03095131194124040303401409203610007034114a012865441c0042d01030003800041a0404540145a4a030740449007640d20801056207845002c02000a80001c0398110803050000e0701000310780c1c8a540350030034084460707494070000c500d070b841681805444420300908400701d0000d138003241594100b00000780203a460070700c01b0083c0f054040f04d12 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 735128192 1250 735126942 735126979
    0x130b0a05180a090608030c0f03120105010315030507150305370209060d0501061e0905010f0207030c08010e16050913110d03050310090e0712170c010b1201021206 71
    0x1000e0300c1c3c0c80205200c845c0c2d1302e821171640c0303400403241c1108074002c1141c510f48010000048da200c8070b011140c40011a460040190020005070101c1c0c042c84500d504040081003003041144014541c0b0040c0391821030310350f04005d0032500c2c003030103031f90b810000600880402503140d17039001d500e8807040c9840e54078807101161a0000344075000c01e49802c464040b411241d08102d9901480c102c54040d2900e4102d04907812068005c100d110b040b49000c50039014043c826544900c00c1040e8170b2803940100c820f069125182c2c0381c00c00840e075002d41c0725030b07458840c000d40d0b00000f80028041191600240c02c4a0f0b4240340002d55400c0004101c0300604034070544520038005811b03071103d0100d10140030a100004d25044c000d04030b0380308403022108041405400038221620b4801c044c0300d05820340142c5030701400c10078a800b1a064025003a00c80115240880407080903440c01080c01b800844000268000b41e1002d10400589101c40604103920620810482c8100307030441d00e40c0000101d43c6c004240d040d6400d80e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 735129442 1250 735128192 735128209
    0x90b0f0622080a030801050a0e100b031506030a0917190f03060e090607030506030d0504090903050724110a0e010309061b0509040b1f2d020102130b0a0518 68
    0x20a5207100d200f08000a2641014038039050303a5054403552503868442010401c1a4801d48080c81101c000e07000c2048030349038840c05075810202c0c130001d15074a818007c00042c1c840d00260f034034111099444120204000003c03d501050010343d103181410090b4107480d00b21074243c4000c0704000d10120f410702c099210b00c01d0340f1030009010002d180741100d0030144165540d407042200c5180229240070301240d401d00c2e0001c0da0b0460300010f5a00c00f884d103402e2040c100068040b010f811018442e080c04540d00182616280d82024002038080c1046407072a4148582510719140c03165803000420011a4840c0703a001c6444000c02d4001c0c20085500c421a203000e400074800f1410050044100141074251568424010041c0a208403024001020440708210000c0f0201d03940640d4801280f902101c1b10340900244143c1d0207072a0a1001d100d04070010110301010080142c000503540000d500624016248560020345101c04079181000840038000d4401e120703401ea01140c5000e02c44200d003441c0d40d901c0c1b6 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 735130692 1250 735129442 735129449
    0xc0812010608070f02030c0309280803030a050a050f040b0709030c06030e070906151b0206070f020907140a050c07080118020117070905040e25090b0f0622 68
    0x110080a6944540041202c0400d490b01c10010745462007a44902c1d10000540d100b243c0030340065071030300900108003c800c01f000402c5064104004414181405040d10f07000b0040901c08060740d9a841c00080c4801107a6005003900c02c0c06241c0390901600e56444400b0540c0540d000814003815211524103540322026030b440100740c1a24144045121641070708002820004003048900d20791f15680c11031306a6800740100311501c5c0890449a03d5a0312485420300c00c944000280400580c1c1030b0041011a403198000382c90000c01004110214100503124603809515072400310b1a450100d464035060340708400483c001c0060202d40b406122900340483c07001001414004c2041a91540c140020541c10303050590115080c0c0104104141300001814441c10701030381c0d14551181043c0c10070006007180c0d40c0c0f00e5502d04c560305010300310501c444004013103c81032500030300440d0303d410024003e8079000392900780280707011000541135440b10020766000c4a0200c145034210303000075060b040303440318561 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 735131942 1250 735130692 735130717
    0x1c0b0103020705073b06090601050c191106070312020a0908011a030d0206071209080405100908060603070305030d020c0f0703061a0a030206180114130513090507060c08 74
    0x21000402103144800182050f6100160104480c5d000d003036602c10703c11030030b030300c034122006000000c1c0d040c94441da16503440041410040e040c840030007465868032031250540800809045210700501001644100300c03100c00300c4429243c1700707241d90020605610041082d00c82d540201d001001903024045520152282c1e0000b04422110382002d103101c9200c1c40310040c040c1c01807030030111603244049601031088a05844801c0840c58220b20900100b0000e0829160020107000210b015903e003d12841c2c07546080d40e07580141d41c01c241d40cd41c140440a041076101c0d5001d48000c000003100802030704c42e40e0b01d0282005072180710300e510240c2403d050028070b5005009251000c001c1001c0e80e40040500c040d450820045181c043c000e020840c40c640c04065400501446480c0c070607100c0308404042810103150285403a403c13288014802c0e003101002c8424546823a60034412818550150b0100b0f240b03183c0144250070360b46e100c1c20b450b21964040d501c2044a8411210288400c3e01c017203a4240300f106 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 735133192 1250 735131942 735131953
    0x61c090c0b0d0203241804030c080c0609150613020f30100501080412032c01050a02070218070c0f03030501051915030b01030609020409021e1c0b0103020705 69
    0x1d0b510307100a61044858200c6a80c00300b012120a84101074440f60b40e203405010000180352150000021786d000038012410800e0450650000a1022024003142c0d0350f48002413065040c840c04050a024103074444000040d005000c0000565520400e2617100c4c100c103500580d01d500c1041030710181d1207940c00c025201c944d0100241e64203091078101c042d0345109080e009038070303468442c09001032900e50f102d00d50001d0300750070104006c148200e00e400c080c000c06081c00074400c405011050000c1c5844004803800720b4420b40c030300d04034038800c0c002d0952201c0c450001314500100d5500007003240e4084019603820551080004880310700a03001481c8503604440c210786071071018600180901000d0142d0780c0202101403c4180000120755130000b034a209404410f03807400d82071012401070480380c0303110341050b03113071036001844510b54070041000d0001c2090140e079552212301c1d0000b1006a581c0c0040c01207004211a0680c449201d008518880103007038007144010b55003004070082d0103003030310107042800784 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 735134442 1250 735133192 735133207
    0xb0a050603070903020a150c020f0112110405010201060e09070311010212070b061003020a02121e0d050114010503040c05011d091303110a051e160e15061c090c0b 71
    0x1003c01038044901c2100d181c50341e261251050b0400b00c101502000128021030903402c01071410a010340403244040c9031400304603d40449400550f58a07100f03244545100107014051541d081c06440b01038441045440500d0a2164249544403440c0c48090701914007c0c0c0c2d140080d0f8030a0169842072003a850f000c6468800508049109039420744060f8031a107418507100010030f029000f5a4440440303500685405180e1980840180e400340303482242d14248500c0414080446e14050426110b070050b0000d800e42c18100f00000d4803a62a03c828140082801044000342d202c10003a01510f07000e1810301c0c503079960305002c2100c51811410700c0760710110010402080041c40c0c4005032203c0c0c020f6590040b207031141705040351144100c03140604642c12090020703120211185561140c42c44200c100c038003201c01031107105950996500080c3ca000014020300400c0041c00e40c03404c4108608559652902102601c90028802a00c031440d07101d41c0c41e143ca0900f03010041417100010091890b0042d44c442c034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 735135692 1250 735134442 735134447
    0x70503040f17072312010f111308010b060403080c0111071208162705040507120507080c040e3c010f030f1e0c060806010e01021204090b0a05060307 65
    0x2c904124902c0788550072000038000480306850208440c4500301001031034644080c011000c400c011040525901c45c200c01110034020700c215070240101c18241521501400f030504c07031183c2142d110b059143e05084002e003003a07850004907012694003106040d0742c0d0190300b801501418441382019050716010a003d000d010071520282080388840e40d0340710a5541d0103001c07003055143c141c000c800043e030782005d048442d6250640844134010641c090030310f45175200005401d8990031280c40001a00440b40320031820203e02907190805c0081c00e05408074030f040480e0304098011841b440d46201c1c222408034000585911507290504043d10b4030400702c5000700b10f00c150040c9100005518804180c0c0000751000d038a00c2003400b40c0f5030000040d01c01e0400c5441d4880e000b0940744103180408500040e00d00020424841c00b0f005100c0340d10313540c5103894410005001010900900f82c10740d0440e041c00e40c4221b440d0030440d015600c4001e400a6401c0c80640407a420f0401b40d0003464200c0000401e001d00c194 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 735136942 1250 735135692 735135719
    0x9160323041b0e0604020901111e07080a110913120503270d050c0717100b18041716050c03062d0402060d0f0f050c1608070503040f 58
    0x140103030551501d5000c15078980310054018459540040c10a4000c00c04620b0301b40c008042c21801450024200c8802d040f195040103880c042d9010f00383d9a40490029000c0280315010050208c103025002c45030301921800c2d01c2103400c0d03003058800c0c0c80d1480040c4003010010405490319402410603240920b00c1500540300ba4000d84a202e4020b000c2c13a4508008940e09400d01e002125000244c521500c645106443c503410100030050030340500c0c0c0c8041180341907906202c5002401000420080a12607280c1d8211000046200d0042c902c09a550100180c400742e2550015030283c44605c081d510508610528022840c0391142c0b042c1c0c006a00c4103100001a0001c81c10700c040b03090310002d441e05450019441c1010145400e0541162a00e5030640c50740201194402e0000d08620310340000d0402c407008880e000342d03620900c16034410000c441850b40707100d542c0d84811004031280c0750000c002d41504140b82c0b01c810080c00e9120010305203042001c2402510020042d02003034001c0503032220852442d00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 735138192 1250 735136942 735136951
    0x828140c0307050a120f0507051c060c090506122512140106170a09020a03050a060506010905181b0c06090f150703050a0e1c0306050f09160323 63
    0xb0b02c500302c0302041d18540301507075008171007002c44102942101c0790354130440d0820010003036540740250000002d0300d4454078080500028071080c0010018040c2c07500ca41107030780e401c040c4000c0060b1000c0c00d20080d100d050486100a8500da091031030342e914610200c0d08680c0e41c0c80c15958900300030100d140581e801148003403101d000303400c040c00456490301010312030000c00d206480c00150851051005402102c04041d004071480c5008100d001c2c80d90007007942c003091070388101d40b2544003620790030a1103010700c9100d40081c424130303006054618000015040358441480c44100703003a24004514101540051600d4016441e000c9980700c4040700c40154941d44121803e030b845008400032940b01000c0842c031502184840030f080c9003203450305e540480c005c0c140105008045a985c4248403040c880c1081032440a101d42c3c0402d040c0800302101c0142540d6841d03010b41d0264403c041081400d81d10000195401285002c49944603400010110044d002c2040803c0c118080071340c1490107050715a420030b109 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 735139442 1250 735138192 735138199
    0xd0509040e0a021e2e12110a09030b060d170906070b040f0201023307120f0609111c091b0905070f02060f1f0e1003021002070828140c 59
    0x10740301080c1002c01d52150007480b0281144507404129401b03000340701c1580e2480851070000360701280091100525403207403004c0000700e4010f1104004110320050303c075503c81e5096503d404440c007161303a8580c12103244085240b0500700464111051f4a441050310383c00364008039014414100b13030034809608440c07140c042e4014040c0074000074000c0140800d4100940800848114541c05020391070001c04000e01380c2c1c001c010400a0702d1745001c8280c000c24051810610000443c1842d28607003004a456110114140802c1407061040028040741d00102c600741c2c0042c01700d8031001070318100c011490640790106024560000103e6400c415511540c801c000903214280d00406e20702c81030b69111030450b90905000302c01030028400715074001b00324103500034144100c078020b900d6810603907000350212009884445e0300031040040d840e2194081d4180d1032640041c01c0d07220b040c009441c0d1201000d40300c82190800082c02c22410032000040b41d400203402403014072081d81490081e60301c440c2e030f00004910 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 735140692 1250 735139442 735139459
    0xc0c160f0509190216020603042f03030304080f09030312100b03040506180f0a0b0f010e0903040b28020102070312060503030a030506030c0d0c080105090d0509040e0a021e 75
    0x101c0d420b10141c810b001e041c1c0c41c150350b98038410b468001006548140d85c8506182044407855005881d424065809a0310031184203201038180d20200078030103400380176848404801d0740403412030b48022040301e4100340c12150b425540e01d8404812520703846039624180d058400028101020141c028100d80075140710b40c0da40614a079205140801c40c00180e4020b041c3d0340110000c106010300030001d13004c0200f2080c041d2040c04c4403c80440e810b00280c01000c1d01c02c04144400c10800400b00e00880d80540000010317540340c0d050190702596030380281d00034840d0080000401c1c0008488455501c41041802080070a08591031880203010b5000310342d045004c120000000e00d806081400341e442078401c06401142050100c00d022005000007401a07501802130450446043d02c3c0c1c28030000005020b103001d01041072925440d10700b11000281080c00301d0f00034010404096900c402140e8903184200c40220b1417450b1a40c040d414411004002980154814141c400c5110440710159001d0811541c3c201d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 735141942 1250 735140692 735140699
    0xb071709070b0a0e010c0b0114030609240403020f01020d0624080a1112010303050903100501140d030329010909090b130c0305060103033b090c0c160f 66
    0x15038514660182003542d0b00e080c00b4507000c0520a514100380d81105150040824440f5200c0042d909800c7e0450340c140c80b02c420300100b050401f0041c007600312043c500208400d001e2040782c02030041000e00c0f00c81c048903601c00894181442082020445400300008560700d082d0004c42c0c10007481d1602c110079a003109540450758203d10f0074140c0c083d00e4256105c0b03000c281da4ac108800002d1001204100b1003640611079a0b00d112046402240654425114255114030040825103071980c030400140c0c07480e04140050201251003a0348181c490019210812080594907043c0c015000011903540c4280207940c48600c450000e02c07020140d00e2007070700d86800c2a40c44200b24825a10780c00c80150507211401c01003001c43e0708820411042c94040c0504284c100e449a464504200d000c0c2d000f034000400ca0111520b540c4101c030980e558101121401400c00d04120004040c8042c03c11035461080b1000c000080e444440c540c00c0300c7ca10342c480410341d201150340c408002c800e00d000340a02941c42c5200d10020 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 735143192 1250 735141942 735141961
    0x30f010e28020913151d10090c110102070f0201090f0305120d110f07060b090f0402040507030b220c0306300204050103111306062a0b0717 61
    0x40c16008004806409010201c181102942c01066615044580030015542c1507104d03205e42121004003800d5610110300c2d0800b03008005a111418040700406c03d000d000165501d0f86140080710710003100800c0c08607510750103071a411080d01540d6495400001c5a404100003005141c0f4018402d80702c3c002e120341c6500f40380c02400114040108a5404100200c1c11a8118000b810f5410140080400c0c0e07000d0327408008555410183e0401c00200000c1902c8003080150301901c4c02030300c000e45041f641e0f45051442c0645205000d071019004a03038850100d201244280c0164129810107800060310040201e03840603904200c40c06000303d40c7c50400c01c00221481780c002c8408a0700401505d44140e1000040e140d86481c101a029403203c00c081c15a1006885078025140214040d4400000100c01802400345c2d0212100820400d6440d06200744103890700726a0900d80c800500319103c00020307441e0508d130041110810040c060801c404100001c1d154480c1a1550305ca0a0041c486a03645641c40d80 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 735144442 1250 735143192 735143221
    0x50a050d1e0614372a021f020720040e030c07170118120c0501060b0c0d021f110405040e031c0e06060105070809100203090a050f090f06060f030f010e 66
    0x42c8000c1a42104006804c0c441d82d000b100540041c44462414505010541103143c580d245021001d60861005030420f00c034440d5500ca43c070400340700e0561904007a40e17101410004070390442401500c400703a40004980b1079034031401641c0703042800c03aa541c2c031461141c01d6403000c00740300da800c1c155000d191141d54000180500c5503141d411440c8000220a80d070b9844184010104151080004126051020031400d0103140700802c07540302c907140d60718a18080710f030500c1b29143e400e0003550b02010000c4041110b010100006d0180800c0004040444c2440740070381c3d10540d40616402401c0070b001e8840d480c1d0100040c60704664080c02d54803c2c018040059040d07032250000203406030002400220306d54003c20003031050f20300ca681c02c0c914182054002507202c0e0414508107005910100314446a400d085540c00c019010407624480c0019018001859010000340003944490011002c240e480d1242020340e50000202000607403245420441811000c9003449421442c2c0d5007080030807180380c1072011 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 735145692 1250 735144442 735144511
    0x1503020c0d0503040516030f0b010501021b0415030602490203060a26060a0b0901031713030305092103030609150d1b050a050d1e0614 59
    0xd02280d200d00c01c0103603001d800040003540d85004904110042900598004010b5441071010300e000b0b98050078040c6e20844c050b0482815507202c003c803d00b0440340e801d8008100d660468021a0b01d00f80d0300d64840b60b080d699400100014000300d02c0ca850710302104114080403811850107040302030740d01d08a0310a8007001d80b040208401c84015091302503099002564400406010303040741d503540364103009103030420075002601a601b03241264202c8000f4411503400800009081c80084810000540c000c0010b100041c80da03008940f1940d40c00702040180d0310440181c1c8841d84140e5540d0901501d40e51003801d005118022001b03c3d02000007d800d0542200d06100c4002c6086968080a203d05180c0c040c5c1010300b268030f2022025619554182508415889010001842413420b841e807407000070260401c51046407404024846034440003590b410440c3c029207103103aa011050142c7e4040c1120b04000303030115042002c3c0b00004030149052601030941b200c14101c1300301d0401c0411103c0020b070f81 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 735146942 1250 735145692 735145717
    0x70513140607021e10020303060312160503040e07030b04050c0a030b0a0503030a050c061003050d0c110603041415280204050d0506011a070c06031a100306150302 71
    0x68144100e8200424025040c0c9010784460300d0021183c000403900b018080c41425562102280c021203400d00c0d02c41c0714100003407170000390308604050700040d4035503194040803510340030045580d41d8401c480780e218492a542100a0300c3d65141c48407402c00f0352090031100440030078202a420341c0e86003000d101d103d01c03031512082107900b0003208a008074054190030b04a568885001d130008a525542400100301c580700c9038a07800e0350b80788604c1007e420804010426103080045003420404600081144440303035056241901040d110b034540140803100100741c09800820101c1000104404403140b140961341c030b10200c56030f10401e01404030454400325080d2088482c0122200d80100e40341c920700d210910141005410b1030b0701c40380410700184c0d02c164103440540c409001040010241d10031088240c44100c26107151403001d1301c072151422054807460003016518904860000f0400f0700c80908004005c1c0506540754076030348028040c003801d02030043d80700c03540e4820860b60f0b4024405c5400700c1d400359 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 735148192 1250 735146942 735146977
    0x1e0a020a0b07260c010c030c03060504090b06060310030501050c03060a0b0306030c190911070b060a06020c1e09180f0304050d060c0201090209100602281b050310140705 74
    0xf04103202c051004110100108109100c2905144428081d1599005090398001016004031a008040c1d8406a1100d40142c7c90603d0010214111000c001d91146042da0300310390f01d840381081e84040039402c0d48007806a500c0c1078240106800d0050040d4059101140c0d150640c580750b0144003060300c0240d4805500d81d012080382241420040c00740400500455100018180d503002030b101078400b40f01c04071100c2c800c0005d0260400001075206900301c40c0c01d86100540500303019000c0d41d504100f030001e030701c00e40d20400e1800195402c04121080c0c140003603c140003c0c2050382021202c0340c8101809440350284251110030210000142d40440da402491940c030044940c40e0000144008804141155201c0c2e1040703026032140e02d000c601a21082060000b00e600d8904000d00b40f8606a55203504100c144403500c901c0d0185903840a013494114842c549041d00f90740740c4030b591442e00d508c8150180100924441c440700c00b61301604100c0000e8400d00966543c850f004c48142c03240d88403031061130300003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 735149442 1250 735148192 735148223
    0x80c04060c030c24061a03100303052a1b040b030705040e070806090703030806030d08010330090815060d0b07030605061216030504081b1e0a020a0b07 66
    0x2c00c010f0060a00414400b10185410301d20b91120107001000c0110081c1c940c00c0810011032034440c007007240160790f030307580741903040c0840c0c0350b05040c010b0b100140800c00041516070751107042c0108107610180c1c148a0301030808000916a4a8041c101c034054820381c0740d80c407214150b007090300589c0c03038448005001d460741034180310822005043c0e001c2001114401c0c890003140500341000f4050040400400038030a0604d5494020326403a00108032601941210945480c0d0a03044944141501e80c80480040d00c80c0030440600d41058060f5070720382c2d040c0103c11041da4403c0c1c00034010400d4940b02029110803940c1c0e201d481010407410b8490680041100284c40d01050000c50040c0d04a241803074045900d595070800100f580e046550222403003d00c0e002446580180120103010511950906100b0b0f403519803101021405503d00d0848801c580d850903a40d140014006012508440c00d04011490110b403559591282009c100b24084d0942c1c0401280340244c070026203003481d07404070005004110 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 735150692 1250 735149442 735149447
    0x1305010b040b220b07050609070506070f140601180b0102010e060f07170f07030606020a0302120c150a060905070516030f0512040308090c0a030309151803050607080c04060c03 77
    0x40582c03500c440c07216181c0c070600c0500f040b012207030091500d15880c039124240f90400a0600300c001c2d000922607030040000300030b1790700d40e50162403c0c240c12540d0300480700400e0400040c0f150410701181c0355802384000206640c844042101c0d0206403134070341007000d060800c005a00700d030601c3c0c0c00ba00d0307164022000120903040c40741c000c3d54001100d19280140c44031614001821800943d000c1004400340810400600c0d0f142c4a5000100100e20043c84200e525031030207921150100c1e54a6070290f00000e0b07244102d401000b40c0c8050481403045080e06107099040303000141210700039007000c0d50511011070241c03071258040d58a5400f60200b02d42c0205402e81c0c1c151540d00780980c0d5501404000e000303001c0b4034101080090320440c0641c40e0403506c1d20340090a141001c0350100c4032882603102050034000700f80c0c0000504182c2d83d0a5103174003103030034252070141c1d00054501c9907100d0001d0341440200422102103039540c0940002e444200d00c91301c2d0b031010182d250166010f0f1100084409500e00d01107031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 735151942 1250 735150692 735150697
    0x6090c0207170d0504260d0e1c020f13061703040f050303040302060409090303090b18281104091403250206030402061b01060617010801060e13062301051305010b040b 73
    0x401806ea41450b0702a624a003046402d8a044000c184041412805410042c1d000d41080c2c400441800c090714040c0c0c001250303402d4202c003850140c0c2c1c4111694015415079071000c406450706044901100c50500c1040c0d649074030500804900803046440010a42000000d8034107481c1d00030b141a040504020264004080806d016020151540b01c003201042c1d0340400640954003042d60b2450800c00340001c54541424100180c0aa04000029015200010044140140d80072001c01c2032015101d0025010300f2007110007400c0c01902e585101a2640c0c000001c0c070801d4034110650005040010194140c5c607454000650400d400304009001468070300d005000504040b2101c2c1041c224a540315821102103801200c0802c0c100303034076140780d5100c0c80005030040040400a001b50340c104a580c040364000a40400d215115034802c420400c0724640102054070109800d2407035040c1d040c00912101d07002845558050410189030702c4060b1041c0c06018161050160f003589031510f084411809907 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 735153192 1250 735151942 735151979
    0x60903080c010b100905040c0804120c020a080708030301030b100305190f0f0507050103060503030c0a0212031c0501050108070f08040809150f0d1103151306090c0207170d0504 77
    0xb55a202d48400345a80c842d000304400c8080b6a4991104508100a0004403140360003058140710500041100240f00e40d000d03082c8030701d00c502e0b2a0151000d5071001c2420030307140b60803060490050074404280b00c4000409981202d004410142c0c080d180c8100f0b411080e1224040a0015000302d50b84075020482c10542140f0700d07102c1e261031081140b00d0b07101c040003180111011140f035002904200569a814001d000103840c088002e5403500080104450340d403001004002d0180a89441800c4c854205009440350301e4a19042c08041400ca100100f0041c03000f4020720340480c1028011405c0d0921419003000803c0c4503460721003507602c0719124402c0c150069041d0383e0b0b004680590703a100981e05007010340180315140c4407464132650700b05509815198550740d0b14044860a00401c242c10b459422600d005031000c0d6102c0042c504010040390107814190010791340c803401e003800c13601c0711980010100119a00491002c089881c0c0c4135003a6104e50300e0003910380005d030342030000b4040034101d070641c1c0c00c04 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 735154442 1250 735153192 735153217
    0xb1801120c08101a03070e0f0703021b15010e010b1e09060d0e190206040b03090312180d08011a030c09090702060703110a0914120714040e060106090308 67
    0xd0340d5200d0b0158a8001d02540c2c0d000040e0321030000300d004108504140d0003400c8102c003c1c2103030070704018120240700301c01008244018013080c08603100380e00903030407260f00308280c610041c4102c1c556175100e55250b120700905901403200c10000100340000c2d003421416548820200d902c0c1050080c50304140310100c2128003000750301004002c1d100d550341c800419580364800b80210f400c4c4940e410640c20940860101c82e481604071071a040140c1e6031400300c500740d89045003170a803640c40300b40ba041d00d58040d180e241722803154003906200000b10038007201c0e11b000c10408100d6200070100c03a8101d031110020b10503102018440d0202013100c140a0003e194001c20850030f107401c00c0c41c4200098051102528104050380207441404146580b42c01241c454081801500e0301c0d04e003d070f22006121581910440f042c069071000701c05110f40d12070110141c505581c10072a048544c07225040f2802c00909168648541d00c0c04561140c0c6110105965048500e60344a070601e00d861500d400c0c1e00c603404030307104280c0c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 735155692 1250 735154442 735154463
    0x10503190b06130e10050a170709090602030a0b043803101e0209010504060c1b03031e020a050604030f12020d062c070513030203120d0b180112 63
    0x20544502000d0b02d0211680c20b03e40f44102c1c0380001c08003460310050541c00ba40206000309121076100c040c205022658003034021800161005101400c040700e0b034001a210300d040008030010700409030040c50160030300003402c010104403503040008441071a510500d0f140c03040c41e10280c1d9a0800980601e0808141a00c1a80640d0480c0040c1c180750a22031002100d076621001e0402c54a4801c10840c03840501007011807510003007400180080c00340e40301d10000c0001a550340400c100b81c00c528101981902c103585508a034403860064109180c20380225640c11001ca580b06029100040c1240e41d1601302002c0c10081e00c41d034500710b030b60b0303032030b0400903010310008000071098454030b8070060000e61404403001400ea41400d01c1058070001c80d800c840c04445080c5c03c1c0d450321864451f00c0030342215240c01d000396603500c0b5441548902c0b52541c0003039814003076002e00301003c0d000c4400802d40d85000d10700c10400c820b103443c10080e030f02c0b00d845084280c3c0c4200c0c00043c0200b00d210207140c50914000c481001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 735156942 1250 735155692 735155711
    0x402030c0c0a050d020c2706040608010e010c03180b040b0702031c06030b06040e030a0c0213060e150d0309090209131a0a0e07050f0d18030503090709050601050319 72
    0x1442c1c038100103011640c2d030b8814070040c1300342030b418814a0400b404c22110b05040c02c141c661642140c40950070350310007410306500800c1559a540e0700c071000a00c412002413202021034540d2038024440ad07641391010a0502e10300280c0055007441007803a06600040710304040c1c0300d907207907100c4d120f000504600035403104105840c1425052010b09817400510100030a42da4114504892486005040580038500300042d91200100c08401c1d603004844614294542c00300c80d000040010030340d50404c5030894584100442c020a901030014451942c035000600c041c6410b074140130018982031009400036150410a01050a05030020006004010180c1e0702488400d9002c0c2e044a45203000349160301d07030503050711425041449000008140007400d8a59038609590041c00c5440b442074030070651480012290000c201319402424000011003010300f0000c4c8514028010707a00507103460079503200700c101c009000815409a548141c006130b49960440c0c40380c548006484000380441b4101544402d54031 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 735158192 1250 735156942 735156967
    0x50705030d0222061b02090910050711010e24070509032d1c0c0203070305071707081c050f07171b01050c04301505070c030c020402030c 60
    0x3480d498801000c0014280c11051800c0c3c07203614194422004c1c02403407040b040d80780b032080109142450f0140e48200c00d559400320464200320048100b10708262500d0188107000394013000300c030300c069000c80082100b05d98a0f8289036564201507011182e0711004010303541002601c80d285608070515091550402d43d40b44002402c1c20044d0900c8428034460549181d0b80350b207c0400b03600c2c1030398003401400c0f042034641b90040003440043e074403c09102c0307803803160021514100807480c000c680050556030001d0b11080001400550405110414400d0103130203c1d1460020606044008000380080243d0b40d0b0b101040c0e034603402495985004100130b022040109151440302e200f86c80518000c2540c3d0201044252064080a80081e4007070385050100480e000110084034250b031300241700341440c440e00341d9003c4641c0d03901c00f500340b8100029040980800904c040841c4440301010400d200656030309a0499100014000140010b014100400054181503004641200154441628114800804 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 735159442 1250 735158192 735158197
    0x307050a0b0c1f0902090a0b0d021005070803090105010501080912160c17010b0a150e0405060d050f0706030606080601020d030c031518050901021908070e1c030905010807050a050705030d02 83
    0x83c050f80b2511202a0011850072046890703014502100800940b052900480c0560b00c807418000e000d06542c24840c096103003d04190b520305a84020041d0340d80c507181070264040e00d07080c40783c40c1c007003151040459864480810145005078003140d04d203040c2009081401d03146078100c2d1007035603800074001d804140044400b8400c018044d4401c000704c2d5001844040c840c1601c143c4d03100d0801081171110180c0250f521244000c145603040f180440d060710340c1d070005500e034284074100a14520418410200d81c00000c1076041c2240d069071401c11401c0d68404081d140c107501241c0c1039005800c82001c1281c1c05010780e00400507000b00d85400a203100c1c0c000540748050085420010141c00811401410302003d802510380c084003a40007942040c200c00c100038552100d05803c07005001e961320014034030621440c103a51810000400203190f100040f207100441b100451000c3d0001004000d020990754083c0c2c103954001c038070740d40c0c0b05442e003000a00d04070382e150807410080781d46010030401e00003000a207001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 735160692 1250 735159442 735159493
    0x5250e0618030c031903030f02090a1701050a06060c03050304150c0c0221030301171911010809062e09020409060f0906050d081c09060605030c0307050a0b0c 69
    0x81101d0011400201890662111100e611990280390704259070b1403a07095000700c1540c51b007004940740d115000d15101174021240e00607049803511600141100c005101d100c0180000340003046661106941a0160354090003540007192042500c080040d00c108001c65011b40103003121054040701c04032002c103403041410b0100010b040c080500040d45400c41c9001900000180f07507010320120844d51030741301d000510940c1502003100c62292490705081c048400542c01e440428070a5100a10b041c540a0000c5007000780020642d03000902d0036440011554003501090307445082440c154032000081a1480c19012509080e1107800110002c20f4006031000d0100c0c0742c00401c10a0030300078258055003480d802440c03031600b441d000304000c0d290404005034941c5c001d400c02d81e441d11800e425034a802d0308501d9844910f0300d400c40c0e02d400d01050358402c0050350412400d0fa000300b50b101081582d50140d90040300d40c0319499402c2009000c0d07c0034001c3c490800a1000e81e00c0656480304084100c040e40c02 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 735161942 1250 735160692 735160717
    0x4080306011b0b1503010501080d180305070806040b0f042a09051603050c0f09100e03060709150f1b140d092909010c0c1a070209010905250e06 63
    0x401344031075448800d24600340c0c5602038000b0015907162420b00780d0740e981403800e6401805220360400300e131340380b81c00080c201964018084903a81b5541d5522282d903030340c0449058403081c0060010070501c41c01020090f005075007010038110501ca15182034054907090400401803609102c10026800c0800d0091920500d0050b21201c070780d45a03000050103860005101c0611142c042000158404050f010380e440792a0a9450b072032805105003081c1c558070080c0055030340c540700703010800c00419446090001500d0100c00501050b5a02403026185007069500107408140d8566401d80010b010703a000c1e5001c00d0041c0703c00d100c00c4824414580c203000ca214050400a01540382c10300c00140f80361450544448016101e080c2401d2140c400e407540d00079558413038104246580c455050080900c100c101030080982104900c00404441004540c00700400700d001e25008030001074400240c2c800d0600c00c21801410340700310b54030104207480f210301d500880e10600c00c4280c85070703c282e1100ea014000080305203 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 735163192 1250 735161942 735161963
    0x40e0f030405030d0306030f0f0f1509110604050102030702010c0203420c0909090c091503060f152e090303020c03120d0c030b0d030504030c0902030f04080306011b 72
    0xb0040c103060040c004026014141064010400112904c0004621582183d0fa0b42c20100d210300d06140c121036004806444c0e001310805424824080742e00c000b000754828000c01c0d094450308018804903028a02c155405030b001881104e0142d4040d40c0c0088503648003d098400d440c3c031900040d0380d09448804104542d100c88108410004602d000c3e040a064100f03007904003d15003c0349010700c40c824800940e010f07241220210700041c6007027100404100700282a007101e860700e20064142900c1034401280b01e03228880c08980d04100700351019018000c00c8044080544400050003004940c1800d4244008110380501500130011020390800c0000c0b5598082002d01c2c0d07041c02490100001486442500820750f810b080e2401c6a003280c0070404c039030720080345680130803000740c00030000206c080e0f030008031207908407040690210091058038071481c00300c0a05502c80343d03003204074001151090340c42c940c0c00b00072a0219418a000d035610030300503d070482c0d91541040c001048200d40c2082182d40349800d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 735164442 1250 735163192 735163199
    0x1521050f0a1b0c0f0f0b2403070306091103120d110c0607031113090209181302091f080f010c08010807060e061c05190b09010e150a030b0a15060804020f040e0f0304 72
    0x6417401404900c0c04001c0c040c7d4001ca80300020f03100d829910001304229618120031042102d465904c00d140e0780004c0c1034074412225195010b07019800b103c002c0160030320b0251540341d5100b14070265024204010000c00d95580c6404007600144050b042d40030340780209000b00944100140d20360405051001805a00d900045007030000200081484107200c40310300c1c2c10000c2d2039610b65156124150101c9002490303403180c40194100c0d0404d5902d0020b418004030740411682c00011315040a4240710b0f0003088903020040c41112000c00c2801607082c903400450041101520601049101f00310050040740360000c0a8885100f2a00321000912031503140c2c010800b8010000320f104a00b221520418040ca10304000000c0b0389603414016038407020080c8001c2040d400715901c08810740d00014000c0d06513640c40c2e00385450348040c00c9456100150510030307000001c25801e03001c402100d0040d02c6250498031680d00f0820611743ca4140f450300305540714401078918504002c1601e5410500000c3c40c1d0742ca09 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 735165692 1250 735164442 735164461
    0x30c07052b030204030305120411041112070206100306020c0c0907020a030e031b1903020303030f010e01050a050a06030209030a050d361521050f0a1b0c0f0f0b 70
    0x12030701c1d8903a0506105110800201c2d81210444451415000701940d595586290400d4804a5481c10907017241c03404518540c005c2c4070300020000000035201002007540c5524049076074080488100c002d440c15041d0420019070315030041c01c450180c0c1c200745c82c10740c00c4070404a50424021203019005900012074581410742208005d1118942680039000c2d20415910441c034402d5900d41032409890b030f010a084441d507007505a0409140c2c0101940d9403400c1042046038110028060000740c05082400010141347c43c1c0401c504480d40508880c034418604030f001c1d0001d41244081c55014090840e54200003002809000c43c0100d0ba5106d04100c1085980d100505400b4003812400c40708060300107410100c51102d8180840700d80f06070604112070080c10840d91210102c0d054648070040141c0003da851468005600c00c2d0390710902181e4966030042c2c490296208201f000313403a6a09541c43c80400c3d44a40d2410032054000c3c0348460400c100e40d541d941d600c01c86060141c5030f2101302020f2100341d01 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 735166942 1250 735165692 735165763
    0x51f140c07200a170115090501050a0e0103030c02040e0118050f120903070302040c090f1805150904030f020a0b24030a0b01120f05031201090f20030c0705 68
    0x1040d41d5102d40e100000760042800152180501c1e14182c000e6414084060004d410407010a20800c101c403240c142d450b945440908001c0c05110f101e1100000301089003058034035440d04813501656507d052650316024400100b00006d03140185540b07458030318001d00701a041e2010000c1c4500c00814607484080c25450929030921115a0804402c0102e41403650700000c114003903a4046400040300c043d440b0081c1c0740f841d1075500c24081400200c0c1700142c0e0408501071079a400c90810400d102c0b90b40d5a850f1302040c6554042c95550068030040410003087c4102d0032410300810a00485642c81e007251640392140f1400c03203c1d070010f100d1681000318071030f00c1c02c81d0508241600350000c3c421304c8510b0f03581e03000f0000e050080b80c18401e400783e8003d080c440c0800080c0740c5560000103413030751140d020035081e074804400d019452001d4100f02d2040404c2c0440d1113a4491002c0c0c0948070785052501c1c82455006600140c541548201c0600484001c180f0520020140f407072010000c41d0541000804500c0c110b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 735168192 1250 735166942 735166973
    0x121504050a0e0705060a0203090d061a0d03231b0c040e03120406051909060f0b060405060a11011b0815010504030b010905040c0306052a0304051f140c07 67
    0x741c00d00c40c0c09a01040005a00815140219041c5032148007802c1c0882c914040c00803003680c845034121420040c0309090f800050410a00c0d40d200424110100070301c10702e02024400140044d0402122401480d6000c09026100d140348200c58640b040001c5600440d0001000e030660fa608842c0342c0241d507146c08e22500402101c1c540145003410600719111450381c02c01070000c0e03c00343d1241b000034403205c2d80d1080a42c01c150301d214200840d88043c1450b0000340641881c00744d40d1454507400c0c1c0c000340340c41e8056608880c0003c020610f4251000000c8404194040804000750340f180c40d008001d40c100481c00009104541c0c400805191a84624402545109055041c0007040105001085044140c1070546501e01004286d0b80c6440c42c01c007103005900c0d40060000b600d40f009120701013230381505551041d410802844100c1041500400c903510090700d00401952090300e9a07641c10180000200083c1d0b5403060000340e4038140118200d40c04c030304440f1004561400203032042003114150502118 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 735169442 1250 735168192 735168211
    0x110105010b3c0304050118080309100b030c121212060901090209010c0320060f1b040b09041107080a0504090e0114062101020d061403030c060a090812150405 69
    0x1034901002e0032201e08403040704908552100100041c1404001d4204580360007036607000c47e5940050707040490140e007080c0d500f0309290044410001410509004810602c10001e01510103892080208a00104031200d815400c6c0200b00815101072013540c0501100c00c41002018070510780001005210340058105a083c0380c41844030314643d0340e101500e680403e42c9410090b22801c1c41d140d00491400b0031803980740c4d03d80302d014204042c06402d000040d000d040c0c04010340d0740200361140039800a0099009501c08081c0034804041c0d14038254010819041403240d5061800c10240c0f1204210742c40020303d1004504005003c0040d0000e511a805240c07480303100810003030348185841c3d0400710000e04014400d5461091118001c0d5041e44621420441d0a0003155501c0601d039060000d016580300e068203440307409240a440381408401c0700d000d5810785000d03000603507400f440100102281001501c050074203000c20594600c0d208001350055441e50314061043c080d801c20041501c8c0001c10f00c111 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 735170692 1250 735169442 735169507
    0x2040e130c0b03100e090c0102010501062309010306030c090204030302070504090b04030f030b060a030902030c060708032202060a17010f050f0f0319030f110102030613090201110105010b 82
    0x3107485078007070500780c800c2140a00d9032619000d8410358080416004102040400000d00440c4400095506c1c0b00c130b1401e80007071045030307a2038005845090b00d07540316210154140240c840300c2580080240340000c014100080c000391a81c0b101100c442141c0c101c4181c1c280c0c009800d0061503010844c000007010308840c02d00640d1115179841d80c0c8003070090700c002d060003002100c44076564025040300c0129800502013a80f40c04c00600c00070003402c850305050b406030060407140515400d000c42110440d5410580300b074038649990400307421400c00c4c02c2401055503c1ca56000c00140d613034000810700d0050583d600e007c404910342c03001c01d11a0060340b0414950001200802c810b4032000300c0c1d020303010b000303c1d070082803c10310b070020a0078008203800c0d00c20180c0068030040e0415800581031046090103656040d0601e0160b6010742c200e205c00d880040d8000240480c442c41c01d80c21790801a040c0e031041c0b51060408240142c2182500e10a0700120b980040200303580c0c103032005643c004c01782d46044c21311948 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 735171942 1250 735170692 735170731
    0x807060f180303050411090a060314010203060d030f0207050307030b160e03101d07030503120c031509040203010f06060203041d01030b0a110712050d05070c0507260109050102040e 79
    0x504581c188000a041c16202e4000030103000040740c1c480b40001707000d00041000e00c1c1c55506040201101d0104458090301c0065241c0744900505c2501e20856001d849000841c100d52820303500ca081c0e000c01881148034100d0041500d0f1400d000c19001075100300020f40d09810a01322580c11411081181410442d0400705c3c841260fa000540020301d00030550009510310182d0080078540e00761518450ba5840342507000001c0200020060005403000501d203003150f2642c4031701101511054a000e040742c8141c000000241c54000d50068005100900008145000305c0c07003541540c40c0d40d403080c8056040402c040040f031440c000d10482500c0c0515604210398116038840011400c060142c01234159214000b01d0b2058040040b154182d4000c1540e6483c0409400d00401c4ca91211030303284190b03404c0c4408511118060108520002d034000040c03c00c10303003414805040b403008000d101480d510400c1f0007242004003840f0b500c000c42d01038400940d9442c10f007100d03061804405840003514000034421807 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 735173192 1250 735171942 735171971
    0x30c080906010b131703040503011d030904180b040b010608090106060203030a020a02030c030403060b0a24030902060904110c0d09050102031602030723151626070807060f 75
    0x1605603010000c0440c0c61313008007404002001150381010ba000030548140d01e80304c01e40000500b0071280101c0091112100d04114240d001e1040440d842469000b80f140c200e407481c05400040c24130101c00241c0440e80388903262003402c428240c1c3c059a03000600d0700140641540a0300f0303181d000c5080b00080c072405142540003035072880002d05108240da40440c1e83d160b50b610a10031102d4617074500080302d032216240d007002002080c10382035241c46132040d200c0010b0349944001798a8029140c584081c400440c2c542d00170760143c468100100c1e4001400c2003680203960301d501c64000c08105600b20749444204620a0515240d40000380c1c02c244104481d0800160781d000003110640002c074480d5036540c034414400300e85414100e400c085a0a45a81d01402007480d00d90794152000c002140c00641c040c41c56503d00e01c0c58841d110b00240900c85040403400803481d8a945c80202c2d24100d4102d8555060040d002c0b51260048a4110341b8401e00149090910035a400f0704041d582d0705400c10840c4000700000b0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 735174442 1250 735173192 735173203
    0xc03100603090f05070605250215090a050a0801060602010e03040f0302100c060204060c02031009150b0d06021225050d0509010b03010c0908010608061b092b0201030c0809 75
    0x180010551141410000c1103201c1d034501c01c10a60240031214410b41b03c1c0b1001d0090780002180590501c030b10141100c04002c0c9821011503141c002d0620b0913820f081d1002e504e07150303000301011500880c01c90b5000600c3c1d1188100c3c54002d19010b800016030a04049000342541c211030700b0b1008650083c0300c280b1034050a000002c040340e03411030311259503140503003090f101a00c07030b108003074000392000c41d0000e2002c7d00a0304165442e4400c0741660a161900c0a0b94022910366010103041e888040d800c445503143d0560140c80e00302070043c15200c0100c269500d4809a91080a04402c40d888100a10501103400615400b0351400002c5e03142c0c2c09850181c0042c5a03014540c0d0034140152214041034401c03000790320038103035114040c3c000e12241c0d4403c54050301c1072459209502c4290b01e480400100c244001c500380d401240354006549402c1c240030b120320241e030024100a50311601615421080306203641b10241c030411400ca080c001c0c8405800007504682e1950b002d40c1c18070280b5000c211041c0300c00300f0b0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 735175692 1250 735174442 735174449
    0xa090209060a03090f0c08070f0602010c0f081e0103060b1807120207030905030109120f11250503061f060801080d080405011e14060a0b0714120f070302060c0310 71
    0x3c00091100840c1400300c044103800d071016202040185003c44c2c80040032a1820603204582140190140c0e120012402c8914001c50340000445000d900012588607101060300001324419829454135480340c0701101240030b0b0b004680e01d80d030f140c1550341c69081c04038191030001e00a400c5c40c01c151034003240103042002e68640039803d440c0c0c00642c4404240c016400e41001d41000303802004002c071945403000010380c0d00b40d010800300d02c45018a800b843d1044110803040341418000d411a50841d900c4420003404911404250404031400450242c404201c0030b44100c402440c145003841c02c1100705084e0b030595420a200f0006044d00600c04241c0018408038016840c4c545021256a24205030740100030300c120381c552940c51a100c000380c040d559081801c00d550889000300d00740d225041000941c82140c841c030b540b01d07901030000c103002c1500c10340d281c0a04900d80d4241c070303050745030a40000025800300c00d43c0040d0500102d1601f041c940d0402c141035100c036443d5841c40c0745003031a499075042c84841d0310 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 735176942 1250 735175692 735175697
    0xd02120d05030a050717041101090b030c0304060b0604050d1e060c02160e1027020f070c0503070302150a05090303070c1701050103020105030c07050f0d050703080708070f0f0320090a090209060a 85
    0x10300823031150348100c459000500e1442c80c159100d060450303500e01c0301c2e441030714140d4403d41094008516444d10308201c90803528000c0c81e150200465940c1c400542c405450010414030a010710100410464020381215900650151202081a1742c04015070584c1d038204c01030b040682c3d01008410741c41c00c29140140c5000e15203180501e201e0000800451b040c95000541c950300101e003515610b980e41000d0001180300d1468022026107907800c1c155a4034161001962009008620000b0b00c01240010702070440c0740d2a010b0b191480c1a0082482c5078003260080390088902d410070808050140c1d021005039508000034801945075800082042c00083d0000304060800070341c46040000810401c4080d050744000c0d80c14946410303101410b103400c01c810a40101e40c80c41e000807a024854030750940303d010143c5030301075492a1448100c441502d414030b11824581c0d40c00d003103804a00e660a0b211001a00101c0041e070751103211090241c2c1040c16800b40d2945030050000c814640e031032106403a5041c2d140d1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 735178192 1250 735176942 735176963
    0xd0311101529160c06030203060114190c030203040305060903270a140307050405240a080307060b0a0e0a0c1b05070b09040902090a0f0c1103090d02120d05030a05071704 74
    0xb02e0319500401c40c103d4000b00030f001980000911141c140c0c02451141f40240c82c1c41d03214004000c8103a1592207640400301c94003081a4030407400d04d01410141100034000c2c81124102511b0b036440c00c0c03620606903441802075002040001900312515000b440f0550992420007207240e501010072075080300760160120803402d0070005800c41c2c40820030780b00145001072041c8070604001e000307407a00d04010241c81c07856211290492400781404800030b401c482d03198000f1440d100c0350751190030003460079590580d4040d048031800120380850301082800340b182072070300240c565002d03500a841006c000c5407a80c48000f070801e0401c007203040451520101c440101c0040d0b65504038800060040c00d0040c402540302210390107200080340c0d40d034855044c006002108204010849405441800c070282205541e54005c100356001400c005100580181c4050300c42001071620b40311540c2015400c00141c1c2c0018808002c204140c1d072540540d50300003900d4108481500520101e840000100910250815010 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 735179442 1250 735178192 735178207
    0x50403021e0102012904150f14041803020d120b21120a120b010212091c060f1a06190f021f0506040c17060d0311101529 53
    0x30340248101d1980351048801c05c04024401d00880285428054003440c5003a1004448810900d03a400c26107142103030042c401460f165074105462400d6401c00e4109071280a450b06042c1040c1013504942c0c40307034015256100c0300000c014401030980b001303003040600340250010389071038024900c0035014040c002a40d040340100341c103924010a098080c68076520005c2e08040d072a80c80244188014410001440300341c800400490f900d0290403a003440c1c1d04010848001039160070361b10b03844c00320340000c1d1060118100792908006c90b48414010044103031910043e4421200c4d4400b69018950112441400d0201182116034140d403070103400000d0003208494495500d0007080041d0040e5101490055031052201e11080504402e0f20041d00445c142403900240c2401051a450b506481c009000496661038082005030381804009406202c0300c501c17000201e00341440b840d02061080140414017500040141c1c0040d56913910240140c44554206c0c419852039002203100104040740c001d4840e1103 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 735180692 1250 735179442 735179447
    0x18091709010e1203030702240106210f0b03100501120605041e0c18050723160c050916022e091101080c161e0206030f0412050403021e01 60
    0x18015520b40c030403005080f4404140300000110302c03a10440d42603075101004490b400d80000c4c1441080074100c0c48400c01405440d00ca141442c100c0c6050450380d03c00c10481e99411800c89000a1079160300703d8a50400441504003089281010100904104829031402c10340d00004800298000c0c5003e458201040c00d00c44200e601903520302c9000030400101070b85142106040e205132040b0490844440d200785445642481340301d1145126444900440c111155000550303000650002051101400440700031540704801c1c12003684600700c0c102204d81031800f08110200028403200c12400d04c0b9100901069010a0340b40b500000011400304442c5240801c9800355946181c540b42545001c50740c01c240003203480c10461140082e22080c125859030709076180c56108095420003060510901e21000681a00b000045c40c4400031380c850010140e580028002c2e4420f4440a20090102c81484184075619100309010074142c10302c50718203451640400e054100c00030440d0106521480504000d90 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 735181942 1250 735180692 735180707
    0x503190f05011b020105091c050d0c03320903130e0907050405040605040b07091d0c0702120d0e01090f05240d090b13030806150712091809170901 64
    0x3c0761a070303804034a24044000c2c0242070803030304c50301584194403048400b420b40c10303905a00c01040b40c0d1041e01c1c20f01c00d204d411015040d400d086008040e503851000065200406140400992800f4000a07685d0328420400c00e001c4040c0c02013007a03070401c0203013580c05040343c0940c808441814210355841e035210105d050500c0043d512541e0400e0030101044104142c4d40d02140c852441215040b10320f8888200840e0000321500401c1402100d0b0b0703044004020700c03410a65800741050040341d2500e52140e000c5030180c0c0c45540d4881e4654407504664901d00d4002140e010b450340d082c60061103032403420341d124244004a00c41e4600500080a610748000840c02e0f8400d1107841045820fa80c64242551048c001d007400c62064540d0720242000c11100050100a00c500540640da124100d460f07035401c11400003c40e5110032641d0728108060b50008030892400c09100c42c20351116500149440800c00700c80b45203580c859009ca2401045d90001004141a000b64000c10000c0039180c09000006070b6052 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 735183192 1250 735181942 735181961
    0x3020904060605040e09013303140f101a0d1a1006090b09091815010f180b0d060b0a03050709020307020114010303020a030c021f020a05070503190f0501 67
    0x103041c40008218550071070000c00403100111048411607030340e50811801c8a2040505440005095148141c901d83c40010040101d100c0340700d015800d40d590741e45490f55032440708022a950010084540380305018814100f64002c1200d0a1001c455900c0b415000c04921291880c480c40b80b0320f0403071080c01002d807010040900141003040c0e4a04240a0a0360381140600c90540040c00009010482800c880180c560201002d020010140c9038400c0440c03000023400d49800c0a0302c100740010802d80c1c440b00b1002c1c000c0c0190103100b680c00e41801c07903041c0c1d10410110040b01190a044c00f40d003198803240001c800385900314074000340c41d48404000448444150b80b010784184038080c0041543e240303950056011b1410b540082181c0d00c110350b45e03003d10f10424403014016800c800020f0011a00034800300406a100a0440d1000072040f83d10306c2d14044005d03952401030303101e00010403c000b0100400c0001d040c04400a0409081c0e0344010442440840703401489104010b0052007041025040751a45 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 735184442 1250 735183192 735183199
    0x81e070623040923161b031707030c1709062806031a1302061c1b030c1106090c010302070501180503030a11040302130207020a08070b1b03090105031303030209 70
    0x284007454481111280100d40814044640042000004c00d0340000d080c4509075100d4081c6c0c0c800c504212003240622000a90910514918105100301240c03130441c822915901e000881c82c41241c001450060b401d5001c1503155144403d000b49030900043c096070081da5160503180303528800d144007000703140500d68203103e50b04150010040182038510244440c980c1096800c050340c40d14800008031500940194100f1000c001070300140022000d5a40c124108a2000c035090510a0b0b480030b00001d00e809003400659900329540305280e102050101500300103000708030302d0404941a80c0c81d100c00003105414903074005404000c0200a4102101005c0741c0c200c00c07115025207040c080d482e9030045500b24103403480c0c0074055104051450550741541d8002d460007039503d200000e15802907202c06c401341e0f8040701202c40000c65290403c0741002a009000310755840f241541c80400120700d1442f91051190020b0000c901c907070340c0c4503080e04d62040ea000d1039106510214102034001340701eaaa0000e80 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 735185692 1250 735184442 735184451
    0x5012102090a0e16171b01050a020a02180f091614030c04060306060528091e0f0c0f110c0d08070c080c0a061701141306081e0706230409 60
    0x118026131100d820101d862001615000350006106552681e440c0010034201c408891180c00c40c030b500c1000502000c4000d401210500ca0090300060544071f80040380c000f426855130b04100c6e49800142109400c4451080200340c0b55005034124005004103004000214058a020b544143e4042020ba0940c0f98040c00401c10591a400c100001d052103000f131500412811304d0102261901d03114003002560440d1211003058180002480680480b0601d0b041862000c00080d80031004c0c1d210345020210700103c0015034005144014000d80d2450408a0900c02d480b05141e007489404690a50a14400c80310107071000700d01d01e4071070981d002e1030f403020b0250340380b005010402c1140000e1b00d5040d548102d8401010a07981d03c02118801e1134100a5400f40c030b1407000400103800540195124480020504100f0b07140803103005044405941c82a1f10550140d05080da42e04071002c00600404a0840039120440c00c2910141c082030f90034a40310f520b52000300c401d0400c0d2100c801500d0190109190601 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 735186942 1250 735185692 735185713
    0x2502031e0d060923060d0b0103061802060c0a11040603020901120609051905060a05010b120406021c0b0f03060c07080901090e0403020d03060b2505030705030708040905012102090a0e 80
    0x3044070360135035181c0201301d80010200c0c485150002c42040655031041d40c02a80340c0c20b542d9580301400700300d882840d4200c481d5000c0c3d001030341c519000c2e19960b0f80140c02046030041d5420210080402d0b040380c0d502580c0b8014050015031503441d01d140c19583c01d11240e460510685c5000401402000c0020f4264003648096540380b28403d2041152240901c04a0f140c1e51140c0c1502c03022034000b845111000202008040c03017800e050021340754018020100141011080000242404246501c103000b403580c075440d074486c0b45000c00020301d4011703069000b003c0600c1d207066002914441d50201a02401c0085800092617114071440300c040c0c95018903240c5181002d150195841825960190200b801c084001c19482c0d94a230654904070340101e2540a440800300c81880c801c03000c0c81007603070180410084000131030030030802400c00510902031243c3c1c544c58885007404690042c0c00880c0003816400e01c0041150b0414402e004050701202c03609a03548540544400601c180a43e0b141e15015171410748 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 735188192 1250 735186942 735186971
    0x3030b060409111209060c03010528080c09010b0712051309020f0a12050702060112060f02030906090f03070b2202030d030b030106051f03050403090e2502031e0d0609 73
    0x81130081c084800785440c544a00d50141d454050840300912039200920041001d4604103501c0d0070201022043c04489050f2103482a01100310f681103400030b58040c00a105003814000043d50040906029103030900c0110b580c0d0300e191403004070901040040c003040c2c20354001c41099982e001810346074801c56907014050f07021a410340010070706001050f0300081d003400300c6246020f41842451180c1c003904803607080003449482405800d000b40c41195840c0c40c0c44c2154019032000314020a071500080081d131403d403600c02d1134000603405101440c0c0040c00480c0000301c00e114440c0e00510000307561100c00300394003441c24000c038a80303d01951520030052030307030481905644003c250300b0050b4024040300c0e488405000c40c1c640d9200740020861584041c10308803170b210303900150b005882490448180b41d030340c0c218040038010607244241486019040001c000c40e6044140409400c0da0001e5420302c0c2c41ea05095030a0b142b4808003c20315040054202c0143c00b030790380110050081c810f002c014030310022600 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 735189442 1250 735188192 735188197
    0xc350c13060f09060e030d080703020904060905181c0309020f0306040b1906060c061104081605040f0e06040f0201120c0815090912090319030305191803030b06040911 73
    0x42c040411145030001c00c0aa1181080300f05861014000b480429080325049400100042c40481003513824081980f9980d00c40c0a42002001458004030301e5041007100700c400329041305c4001b400c541c0451031400d1201031945000300381aa030741c02d0024072450a800403502c605031500c150340c0d042c095041000f0800413541d600303d00541d2006404e072544401c0e80d1019040380c2e024011400420340c080711030000245240c00102210705103600705e070f0407c0d581da00322925241340c1d0302000781180780c4480c0038030490802d0700c100e800307050110750203001b482c64007000756071158000340c00038140780c400e0300a240540e40210700d0211a081c4500c020000e00c840c540b002000d900c426100c014503581c462030302017080c0c500504024003600080300501000f8003003440b07520155108900c910f81501a60751040b006001c2850001c0145000b92804100c5141c444003446500032188035a40c06c2c00d141c40c0d90300364a0440c036190b51100383d500d810001441482000000c000303010b658000300c191403d060840300c44404e507001 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 735190692 1250 735189442 735189467
    0x61224060301180e03250807020607230303061e190f080f01050601021f06360e121b0316050607090b07060216050a0302010c350c1306 59
    0x4000705114200e0b1552244602d1b0f00034203d00581000c60490030032800c1c4000300b194030900c5014645040c40d030201d070858101043c181d03030720601c00007240c442c02d02c0c0e078800201c22078000015520794a04400028503415218441d17442950100300802b4040c0c0b034811000e01a001072120310f5000d039644980034031419406001e1400381d4054084030311150b1005018190261030140c018020070b031140c103050802200340d5002000b0707950b1201000142d03e480660000e802d41045e50406019118802c01c082d600502d15100d5150646402c404003501c02d004030780c50341444d100210703540d070398082c003000d03182801c52011140685000c002100454800c2d10082c14260034071842c02c2d124140e50700b01c0300b40c2d1010018810f81c0d407003500c2084000c0c0029180da0051041810f540103150074010341e510b80c0303031030090391400440250307640d165481d078183d410030403a0141c266491208191070400c81e180c2d85c00e076608400704c200b000c1350550200310911105c40666024980100180b40345940d5184001c1660300540c2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 735191942 1250 735190692 735190739
    0x827030d0302210709120605011d060d020603151207051906230403121218021f11121201060903020303120a0b041107050705061224060301 61
    0x54a152128020b0090301c03512003100205007180308101500010660340144035204000c1526030201c0c10002c142100004503020740000182c0d9810f284607288910017421f40240090410700c1040701070741e2109401e84e10540e041d1101a141d459440e21a0559810040c80c10391244144542c0380842000051103001c848044803424202014607402030318805243c001c2d83c0001d0540244000380d10300030594503200481c1c02034210b14013540c0ea03c441d480c507038051900c88001100b01c802007490f1900c074055402551001810702c22883c117154005194011400304c07650140080380c031403031503250085400101e40d80e54482178900e0581c00c44007100055104505406183c13502400100d119441096044143ea5001c0c0040d442c0c165040c0d14001e0310341006144403142a101c688030946c5488a004030b01c64400e0441040342c03107048915100741440c0880d003001c1d001350024020f00d0340d2840400001078000904140303020710791030307414103102e080740300c50070207e80141002000180c0c100580c4e00c41c401a04000c03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 735193192 1250 735191942 735191953
    0x150303020f0d17010608040309090f05040507090c0912150518010510031a1504021b060a09020a0509090124050f030d05030109021303140604051203010f0b07082703 72
    0x100980d600704150f40f4000a15200600500405004032040c80e005130280c105940915518000081034860421441c01d1300c4e1380b20400d2008202007004000d0182c04015800d00280e0440030f030003404020103209900d001c030700107507146081c0002400c4214402c46030320301c20f00045c5410b402c0d449604416100300445581381500149008008001e81415a03070f01c4801c0b1024180529080d11000c10050702a80d0800c468541c0c080c0107660b188010320741e081c0000344118040010200560814200074581241541448403000050341ca00b2001030a03140100d80d1490030303031200803105005040c040d0040105140c0256007603840910182d030002101e0084952032440c500740c900341900c0721114010310001c120b0a1005202c54038840d006003c0401e8440390429409542e510340002d4841001c140203455046141400240001484207000780018a281140b45500d42182994040a10b2103440c0014a0125400c020030014004039010607034842036110003d2200b2450301d0319070800300b40c80c6200e4482c4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 735194442 1250 735193192 735193213
    0x1002100c031806020417011a040207210206070306090e06040f0309030c030602031005011704080a03090b010906080f03190f0302120f1602010b090a090201110d1101201c150303020f 79
    0x140122000f50f88e1609858102c60750a8040c00040d41003001701720380b030b46403010b01021008010220f403000056207600400302824170103c00340894040d0740051010038140400c1900c0101c001038160703003195004c0c5c41c0c810b140030b1034201100c00c00307860b8000400c040f11000d000001d025154028501a91082240e500303465500e90054038100c04602c5040c407603460b0030000070045825100603001110140c06d000c106aa10f0313650f07031145010709802040030780b9590030003030041107410403100885902c810001d61074036881000c60180161540300200030031003001d0440842500c25010342c0c0c998001c2c2c6007402c001d0306005001480b00c40080b210070140a2121880132002c501c140a090305110004e050503403e5242c0d00410406048006420307418411000700e5020b80c9072040155040306c4255541e00f002502040940d103003907410360807540065075203824904941c00d400e007080f100441c030139101918065414414080141c4034024001c403d05c5099a000818950007090401080403004265800c4101 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 735195692 1250 735194442 735194489
    0x118180c08090d08090c041d0601060e0916090f06030c120524210303040c12021302130b0c070602010f050411130e0303160e1002100c0318060204 64
    0x80488040005034400500041100d0013168015000605002640c00383c402c65000f00301134400031118012028002a51445958030900c05d240c0504814945943c0d4003642400041050383c015150940380d412001021400b503014900c16002072048140350408103030b0b91403000d001401d01c0c2a540010032182d4100a1803101a889150310544c00408051100b040301e412240461900c00c64480c0c001c1000c50040d840d40f201c400c0a180781c103052070300841c0e4034034040c54a42006091544400b110f51031304c0c0d5813100182c2d90030760880005211060010307129800001200446041e80c0e0007010701050000d43c404040f0740120b02d4105450050b0000d00120600d000700c442250411540980b1319401d446115000d460010305200c00c02a0040c1c01003946841c2500c800d0460380280e404200031024249000c42003508114508000e4170111441940044509000703920754400201c5003180d03036038414400c04254020b5000c100382d0b00403070b00d0482440381e03680750100080d882400f88602d07115600d00050052803 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 735196942 1250 735195692 735195707
    0x4031202010603120c02016614030306010c08090d020a0905090d05031302040e03040902030f180d09030b0c0d0509030a020118030504090218100906080601170112020118180c 76
    0xc00b0307010741d02590310b80300103030320128008c101c295003072001c6541105000303d91b003a001c203407569421000c4584011030b440d1440301c04241c070002c00c2c450341050003003024030380e00007590600958001502c40e0381c0382d140d030000480513003150708000d5204400803400302c0d100d000c0d640150b08c150b81100031100c03e414080403d0300d0300e00007180d00c0320305024088820001824541c0224442040b00e408481c141a201c0d40178038103a07081100c070310720a404454108141d4001c42c00c02018185480006401d0b4204103840060915685000141107195003801003860180030100725445084011340421482c285507090f00c1e02c1c1d40c003042d0680010b40c00c06000035401d08030703d000c03408039960580f1114a0149000607001c082e4201d04032482ca18041e0700c0c2c001c0792079114080e212136820f1249c1d9030050500d0406001904900e40076280c0342c10409900054060311010780d44040c10349801c01c2d00c02c07a40d2007651004072160079000c00c84101c9160035070310000d10100244c03c2e03207200122005040c00016440b240032541d54 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 735198192 1250 735196942 735196997
    0x40603062409090213090c1208091504030809150417030304060b1f03050606070807051c0306050303070f06020d060608090706022404030e032505030c0604031202010603120c0201 78
    0x4404c1100e070000010320b540c411b0800d10b1040d943e0301e032602c1d560504504020042c4005030754074080068007041900c2c1200345104c6103100c983c40582441c0c2107884040183c0520300700240541c840005103a07420814500340d40042c40440c00031155040c056055071344940080d07400f03d81003418a10725002602d03104c181c2d0f5520b1050103c691140110303058084000e000c0c0684060b4010342c08200a4010071580f000800005002d14010840c40c0b40e070389034415080c0c030001000c204140c41c015007400a540c022040b03903800b07508003e0320216810241007c900038072903034003049106460104001030351500000d07260701c1902007070107407041c03107584810590301c5611415070030408105822685c402200072000d501d800c90301a1410351050502c1101082c0b50060980c261040300c41e20f400500c80d807056440408018110960103003083d08400400b10b080d50055010080c400c50705201c004080d94802d5110800543e041408428082e80410014040c1e21940c5026800100176295406490750004109c043c40d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 735199442 1250 735198192 735198199
    0x414030705040e12220321080103081803070504050a06031203110405210f01060f060201090f0303181506031718060a020a0c0905070201240e060406030624090902 71
    0x142c0c4d0284006603101d603c02c03c5043d4510007401d145183c48040301350042c1c01340d4807405c10500310040c401300610400c0789500d40c40081210600c01800001d0480c0f00b6181c00e2441c58050350502241c00c030000b4140710443d0040c503045841c0004001c40003d0700d0300803c1c207d90040764524045400b414080f01a2010200c540c0f500c110704100800243c104550050740c041c82c103000355406501104007542c103003c620081c1c50004d81d11820f0901103044009600c0c001442980003c010024183d17481201d50311015070040c0c140b60b580d4101c80c001ea801810460142948210125459401c100007600140704602090740c2c1450142600d5113a0f10059045650101d040c1c1000c14060b00e1580c01c0115a5000d4824a011409000040b00000f4200c6017040081c1120104c0400c4500e0300040007030031142c609409880c00403d40c0585e405a599110140042d00d07440004007100340e50f0307640420090140d40c3c3c80201540e15181180c0719841000700140c41a00c1c80304ca4044c100d039650320341c40050700c0440c0c501135070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 735200692 1250 735199442 735199453
    0x70c060507080f13090903030b09011403120c070b04061707140324030d200a030f0c0203031b0a0b1807050f040e01110d150e060d0c0b0414030705040e 66
    0x30f0000a82c060600d60400c480c1c071007415601c1e03c41c58000d50740401c0084001c1303902c41000b13010a00d44140c000c0d024110318007c2d0145082c41c500040d82d20b1040c00d0110159140c00034251000c1c02080c0102d00160000c10f2010341da8594808004048100c0780c2d00c14040405000042107900c1c0c403c6031802c030107803440e0f0100d605503101c4140c5410b480080d000c640c1c0006503920040c02c080e8606002c00c0081e502c03075481e0103010714882045162481d1a561408403d50010050b420001c4d42049441004d06902e10b07069000c042c00b4400b10f03140d8482c026490254040b030361a006440c500020780c26003902d02c2040c2002064444407401962a41c10305154101ca4016090600550031b00451541a440d07004002203a40746149030218211602c3c0f0b500580400c00004400d41801c40c0741c06100b040c000c2ca4502c40102922300080103401c00da020704014450071075114014140007071120340c14060219152140d030f1b220741d201c03c1003e21001050300355020b40164000090980b0f018490b045903189840301500 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 735201942 1250 735200692 735200707
    0x709030b0604091403130806060105041a0d15080d0c1101050d09080f03070f020a03020d0e04140916090209030a0609020a0803162a050103050901020c01050c070c06050708 75
    0x106150007072038281c22a5039020399034041421003290094080248001e0350381d904524400d040185c03410303004040ca99025205200c0d140e40d2000c119411075066000d000350380c4401244c1c880052140701c0d022090107003003000d4001d01c4880702e4041021149075008030b23102d00b145d49600b640c120409107000351038030390034035460384c45035010b4401000c20340c50454001429210341d0340d074429aa00300b00807014801c0300100c20010741c6500b21401c0d80c80c1004600042c4400311107560029961100103980c0003c0140101c2050001e882e00d4100c02d0043c0b040381c010092600c0e02207001540c0301da0407a002107842e80038440c00901040700c1d09c00ca41c24100c1c080c01400c1200070740d4840c40e001d0603140000f240c20003800d1a0010703508000788013414441030740c0c41103036591140c00d050401700c0c501e4007402c45a100b0307290701e85020104181c085070b6089030420700b0003140c16503403003d1940c02401381c1c01e0b10081950800342001616807681d030040014510805045e0080780d1035060807126400307100b000414000381000400c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 735203192 1250 735201942 735201953
    0x30e19080a050408010905010b0f011103071e05100b0f0109031e050c220506102319020c030609010b06031b070204060b0702040b010f050901080907030b100f0608070903 74
    0x5144665850401d180f400f42e50380b019908403071100d88140c51a035540c0b488084079181814103450750800900c0c180c80f100216951061b120712641100a041088040166580009400c1402003117900541030354202070840340f82c0c00203408000310851003a18010030040b5298007802000c4c0c252170700107a0f82d00300c903200409280079826080c03006507214460f0700da4002556650071f90246881540300402100e00c0036440354001500c6015000600c41d0705078608032148280d0255884062078040b03034855501c13100c5110505074501c50303607200c0401d1407a68585080130316000200c1071315401080d81101c003940d4403228168201c64644002c2a4024000c102140c0074104460785135034040c0c282a5901d1070025030340d0010741101c9290340300340c0c080b4601150030340561405103d4091401800e0920140c841c0c0400030042c020f220386000d0506000d6601c021079900c8500708644000b550f80554400c1003410b15540102206a0911901c1100c001a100c0071a00314440e100042c004d000c10384030085082c0c210381d1070 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 735204442 1250 735203192 735203197
    0x30a0c02060907030b06310e07120f020a03050708010c0806040605030a03110f031801030b0906090a200a08090f07150804051006090c0e0102160b030c190201020a030e1908 75
    0x200798011f4901c120040694501d00d0450380200012001d00f002c2e0b1140881041510b031020b030309082640040380704014140e400900300071480d43c80250500c2000f42480043c041c42d40d1030300040d0092081100121f00c415056101000b0b40d2521785500516641e44000c01c820b446c101d0040755050341081d02e51780000390044060010407050710f0141e810f65503079a803105185070441e048041d4507403801b00c480415940c143c07081c0c820480b81078903540b00c24a040c4002c2600e04501500400c4029501d000302c00880c100107a01c400c0040b00c13070500e5680c801490900a204060075a00b07600c150144003e140300c1d0200c0001c03030b8403c0b16041d015440b4a002c0041c1c055030209001002500c0034000c1d080c10354680d01041c0701d00b1010b017988040c0010801c0c940131008024130314102c107943c1954031034004400b80004070b0040c0b00440c0d40c4074001e0381e502e6451b101c1103025409000001c1e500d001700c0350303030b030080b469010f4028095000c4650b07402c1059103036800110b40d4844054000c0154845c0040032800401c010800 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 735205692 1250 735204442 735204451
    0x30e0622080c1e152205010809030703080610210c0816090e0402010507020904150f02040e0a020c01111204061b0c03080718030c1403030304021c03020a0c0902030a0c02060907030b 79
    0x842401c00e200c80741490100c00301145c202181400213a401c0c0815030700859050b030003c80c440001c5044c0703965a50081c4c1000e102900141c400c0481d03520520340180708201440c05000d4403074440d14400003a080d80b00c040c24020308180040b82e5208001521003400070412524001a030b030b1204031081c0b500311880100c5c100944142c1c100001000198003680383c00d0720450166126845101c20302c40354040e9802114101c02845d080340d40104810041d441841c0350082d00640b410384010313a2400703201a4240101b8401d80342d079070b1301720303001c154071080c1240a085e0500c110b00860050010803502c0035200458092800b40d8400300e61b06110f81800310f44907031050741d4011600d003080e0a02180240b100e07200300c28941c0c0200d03101c050880c030501031034407904075040750040c0070790045040d4240741c2d00013844e806180e0022502c0c500c0e512103000c1458420400503201a42182c4804034003511414000d0195204440c180d0040e410203411409041c4009a0a40b00e159034501421010f415030380ca5045032031000d007 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 735206942 1250 735205692 735205729
    0xc010c120c020f0409080c06090303100315240303030e0109120804050f0f0c0f03010501030c0e04110a1716230102030f1204020a061407030e0622080c1e 67
    0x8030743c0d9040d11988180b04540f0b01801c401502e486d24000d20600c2c04400500b2141c4540092040c03001c00d144a030160301c00d903503028a00380000c5804011402c014051920092441e201d001c00c24201c20001010f0541501c0c040d5400340140000e641616003a5010a8030050107801c140c0000300c0c50310f204a1400350131522610503100034510000c08140780c03d02d001d080c0310042c1c2004000303003100d160518074000201070a80c002c2c015503141d6240c4e400c507820107105000009030340c040050108010f02c01c0112032240020a0904a02d8981c01c0000c000040030b0510042445130754546120035442c01c81890031600842041104401405c40011b518801c1041c800d0551100b131002d42158003544000e401034a0416030f28540c9861300d80104a4440040d83c4540148506c1501620314003a001040f2869503405043c81c0c0c02c9000304c00701042041c49401840b140302659004400006407409150781300f154407601c02c0b9111011804200b0080340f0325054110310307130f0380356500c0d49400d401c1040d07001940743c00c5007 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 735208192 1250 735206942 735206959
    0x7050417100c02010203011d010302100e032a010801090e0601140a18090512030108030d0b0f0603040c030c050301021c090c1d07140304031b1b0608090c010c120c02 72
    0xc1c00340c0058071000c0140802607500400180140e81711080c1406052103181e4901c402545541c010411420195190000b000340c400701202c2203441c100715a28442c514002d1034500015026480e401d0314603003201950000d01800e00024592030240503a16000841401810050f441d024070303800d0741c103043c00240780c1021410800050b6945d2805e0500c48100c58000c0100e44a201071401d01e0901c40ca00040700c200200c03d0005100380d8000200340e40c00f03180c040c0d00001c1d005403400000741c0303603c180540c41750707000000001308010068664110f00031244244c00725180252160205400e038060310541c1014070021030340750794080c180380d040090400c0c01869080b801c5903d8005118081c0c05892402c130507422044107010085034002c40d500013070702ea12403107070f400c5040581c2d0091000c1c0341030f10f16440544460116a05110b120300c18041402c191489402c20301d0307034809016140d10f004132840c052502650802c0d0085500071612503044c19401240c115903404810300036600107031600300998101030342 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 735209442 1250 735208192 735208213
    0x711041803031a010806032e060b19050301080604170405040609020c0d0e0d03050304171b0c04060b0d0203100b03160212070201140f070c030803090c0f09070509032802090a0507050417 81
    0x9a1107009e000d40043c0302000d030f0710000301580d100544280b010a1082080820040009213001302d0599001a4440541e082002007480900080d000b107410060f8002e15011000a2042956008000125600c0c080c1c43e01c8812942054078240011301c0826008180c2c0191500028822001907902c40d21035020100c040e48500e80c04030842e00000000f1501c02007200019207400740402c40a4130002c1c0c2128140403403070a242d15402c03036004100c841c200b05600440480c8c010f420080c601c1000d4141c01844545030325050002100070320803a000d480160089441c0c400840303400320f084440353340e010384844c44031404017212041150700403088a803515806105440000780d800203c40c00440c02b54900c240c590034030f200032906110131260b00501c60100090881c0007515003104003a4020309604056441c0c10809002c64140703d80c0085003164040241140c840a8440504003541c0a0081e070740000c0380ea032a0b80c60314044500940c1c0150101d48c003030004000403403926461000c048580e0060300c450805 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 735210692 1250 735209442 735209533
    0x10c02060c060702071a0a020d0f0c1b1418070c0311030a08070e0102010e33040c1d10050d0c150206012301050711041803031a01080603 60
    0xc2c20b44102c40143c104003004c105076080300040c40159a114414180b0700380e0002000780d650001d46600809001201741d5020019000e80024070035075411003000440441803884440709c100c0540103d031007020340d01f902c0c80c8503818450003642c0c2c1c840c00ca845280c65170310341075000d407050451910100e0030030079042400c41d200e02083c8090219521591030b03042250403c40005800482c0500c0d41e181103a141504021a034100001e81d1641084000c02040140f50405451500c40350048100754000040e6410710041002501d054004c9610700d0444a0001700c1c0b8009144581805071040141c11620388400d0101e17150092090803c0352103860b403a800039a84409900486801f12005405a0000e070010820464179840d05000e0300c1d0b1504071046280c8240c00080c0550182801c00b0313001c0007000417a54180e444940c08518189520002c4105200700c516000380604100071001a041c8a0700b18100c042e5401100010b00030203008024003945624081c441d00020045803103501400c5254803040c41c7c0b40d4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 735211942 1250 735210692 735210703
    0x1a030703060b040b0906010f120f020c070e0c030c0403110112090503030402030607020c06040e06040216080c10020f0403060c1416020f062104050102070b0a09060b030c030c010c02060c 81
    0x14441c00000c561001004200000c86100e140094003d402c800300300920f0b07030791020300281c2040180c148070340200c0138950b0000060a500c032143c007000744009400300b800310000980e01c007160b601d00c800161580d00e4034071110440c002940c1d03001605100344000d0000031000494005201810302d4007000c59030103110301d0026640c031920f058601307030400414441941810300040e0761042060008040c00150003010505500c1644a02c5400303241c0c00000c21840d507215012255098980e14800c104900039081907802640070040380202ca100c2c07020641d0a48029000b0391360300c1030418141a003800c1c034585030306014014284d8048100048005480001c1c40d01d0000703041100017000c403088803034540c0d106004c00c181ca031440f07842c41400c080c032100340e00c0e64076080480300d000040018000580c483e403800740c2c0680100070004180307404400070004100078a5005c00e030742d83c1c05075901303011900242050580341c00869a020b03805821040281103554003e003500d006d11440903080760711301405080c00c10b0811 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 735213192 1250 735211942 735211949
    0x60a1404030803090c090f0a020a110d09080618070e0705070b090c10080402032805010608060709050409031e0e06070605060111072405040305030c100e0a020d061a0307 74
    0xb0b81c40401444250401045a4080813000b50f9010f01c080c00d100a0310f1080d031000810041c000c0740c00180c1c0c0d0300540e20621800665003105000c954081582c80d002600d0700b1090700420341e45204803000034407020f07041c041302420282d005001d059a142020405002c404004045206201003003112000150900922910900740d9801801e4101049010402500a1840d454003007295a00034003015a40100f910244034a00e00744400b0f250300342003000d901c00c400d283c101030110351a043c1e0001386018007060140c0300c0d001550320032241c0c680314070401040b80c5101c5405000207420b40010207255018884e10b202129060822011039211400050710a5202040031504035440700140242540c20031100759248000001400031035041c401400c1d9034004c0005810310350600b524a015585020b401110050764011055a80d504d0402195a58a068000201d2145854171441818000020170b00d0814143c1c0103106000340229511903401a2030307075034103056504081c1100c017603003035508000200c001c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 735214442 1250 735213192 735213203
    0xa0c1109130303051f05042003090109050d0f021506030c10050d06090203040b2214160b0f040515210a05090a0f140a0210050c061f05060a140403 64
    0x1c0075191074001c095410140102e20310380f110700075160b021140c500c0342405035101070380d00040801103403550544509211003041e0003404004140000301c1d030190442e01401d170185089955103c207512003250503d20003284603006070800e218840301511940c151541202d4024100c4481c21001ca000a03620312020001c1408100000f0344012000c000307000324801040334850450640c40c00d5180c00e42c41e00c0b00104074810024010700d00b008403a00d03515403840090f82211441404510070840656902d60100225101d42c0720003000150000f1f030701c1d0880c0c141c03401403111b031401d00c0e250800b4440001086000601e11140510440c1481c42c66500013030303c081039401710b418580c00d1125080d42119000307003ca4056801540a10001c107110310f9003480d2683e801103045013109040c81901d81404503c00d07000350b00800391603105070000d42c84006041c610030400c003901c11945400c0c031208058107002000400b105204035081086152007000303001d5400c403078102042c0301e55240300101e00b19801900100e80 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 735215692 1250 735214442 735214471
    0x1803020a0f0303090801061a0c03120f0612011b0e01110f0105180c0904020f010e0405040305090f0316060c1703010f14030303070207141503040f260a0c1109 69
    0x185940700404c0c40090040b80000c11103d82006c9450b1001d00616a02c421640c00000b08180108000c00c226040c0e8030b07250304028071074240702030100500c503000d07660144940407160140248074410701c02d40c3d0440c16898030f00450540f665105903051500c1828150600c009992007005580d030070301c06600700ca44100c0000502e0700c1c2040085849984d210070700c0040d54464400c0c410340c0d03142c1810042d046501166071141500004004a4440c00e10030b581607089030518003408105900140034101010007203604001680710794050582d59141c007510640300544c88081001414001d6101140c290300a6000080070301740340e190b10b0307015402a4452400400840010030024600f0f00b100580890704030055803450810750402036494155001d07207076440060044020165940c04001d144494040c040e15480e45480e08010100c2c0300b0300807007a10009800c0d1880703800110604011901112400111800c00400d82e504580050010000301d684190185000c821a55020303001c3d031041c07401c00407019 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 735216942 1250 735215692 735215699
    0xf18100302040c0c0302060a0203062b0c06031104050f010c08040608150603010312080a0b0d0809090109091a1e0405100e010e03180f09070804060b090609071803020a0f 74
    0xf101e0901c84480c0070810302420410000380d000c2100b90b04120808009603c1c2d4030f5030000124080d510318000101500e00c05000314082260a1410800d58010f0b04440301c6144d035403000350141e440018456030321001c100010700481c54450400c4450b2035061614031884076141c3d503504040d1b8803503003000c0c0201c0c940b107080200145041c506035502050560391350307007154996510015120160b039401300c10301640c5000120f83c10820740c03203401031000040c035104c1050369500b004c2201c2c0e88400201c80c060b244440c004500c452450080c41402603007e09030300703002d40c80580d90404086018001103400023140501e031503044c14a2140c0d034091402000506205807034240038030200c07401421201c4c101c0e410030000f041c2914010042c0e94010f240e0400500e10b004500001458102c40c207503e465100c8450000d01c009140d00c01d24091155200d000204505400c0004029400800700c5002e40d01810701d01c0094107241c031a17035000040c0c1400d05841d00400380c6a80c0000c02c0400f054100001c25840c503003003003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 735218192 1250 735216942 735216949
    0x406121413050118020603060d020f04020d200406090b030403030b0a030b01050910270f050901092904020607020f030708032101030b0705070c17010209040b011d0f18100302 76
    0x40100e003078600c000c241c24684c01c0e8042003103800020012445048402a19410740d190320b400700f01200c8000308119540c43ca10141c14006001101341c0801f4a400306030040b000c00c0f10703101141e09a480d41d80b60f4008640c42c06440d00600c1c0d00c001d0044040580b180d000901c9070702c0b0f409100c401b541c840ca01044c441c0d0b04042c01d100803110020180c0358885d0042104104003524996400c44e0820001500d5040d24818030508000c0c10341c900300c1003e81c0f072800c42007125032041076001c030000c14403d60088469000001c0e03140c0c403108a8410103424001c0d19008100149440d40041079103901c003a0102510030300c07240c0080d00741b4100c2d920560182e0000140303200e05254491220340e00c0c01e2004046481541140c039540714203000140310b03009008001403a9000c0c088aa4081d1008003010a1410822142841500d0103504407945280c083c43c10305401e0100e9600400c014028a84410303103e902000d0b0240401c10b29481b078030510342e00b200c1100c0d030a42c04013404c80461031161000c051300483c0d040c07852060 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 735219442 1250 735218192 735218201
    0xc120608060105101806050a0c020d050c090f071b030c05012f07051f0209030f0d030f0b0108151f0305040b1003051911100c11030601050604061214130501 68
    0xc8000c01c101e248516561705544040c0a06035001440c025488901c041000d40d04001e1025010b90701054a00d00003040140000d0300d12413540c0156003030360903901c0c1e08604030324214041c0c4881d40851360140305414440c5600840301400b90003464010b1500005449850850b00440140c01d40343d1045040b05000b240c000380d03c1d04000442a01103442c10071103440d801d4581540d11189070800494034425040d812003601a24010744d4010180d842d10a2540456986c542c004000b0002003030030200d000844c1c10b1075204002c100c81040c7c485890381e40e212042440c00d040b170041100d80c0410b00301e41c00d0440f01c080d2100090400c1141d1000141802c0a0415081584000b010542c12690000042c00000c50101c1c5001c40c0400612006040c00801d14055096100c00c485881d04100041c3c11003580d9075001c0f001840c42e90080100340c41512451040c0740c1c072400240502c42e00300000304401c20240c3c2c03040100c040c0031320566100255842980800f0340340204c05613004520030790300b0b031070030020320a0a118 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 735220692 1250 735219442 735219469
    0xe0d03050c090f0904020a0b040b04062717120a03091505010303020a08071a07030b0f040e06130804080102030a0c1409090105060306040e06040b0907170a060c120608060105 76
    0x2000d040070040c5001400302c00140e091107001c2c03da850045170440d00c0791103440000e4281d5880c441c2d1a03a46410149241e030304544101000200709d03820081910744064100d185100100d0300310708649007040c48134054200021981c0c1c0241c400c219419280e0007000c03015050011040c0d402160000c11800c140c840c0c2010f480c2e0785c6c1030441c41c040040000030b400040c10b880a5034841c150688903007503070910308080c0c044e002d1400140840c0748200014613500d80d00c116824441141c640d0011420034062100704c1d2080343c902002da80c000340201c0d039160042d1440c0c03600c0600c50742100b0b01d020b40346c80c400e0342681c00a80b880b501080d1030701c141c6d03542e1a81112904410003201c41d005030030441a24001340300c044061013a140510b20020200b5001e480d560013419840032a0b004444003400c040c94091003c032000c0301d51041502036802d0108451505071100b8417600c43c103000030200c04030583c0314a0010700361180c42c40103111a6401e060314441a600500d801010040c0242c46658906000e0101b480486c00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 735221942 1250 735220692 735220711
    0x70b0109230121050a0b0702102d1802030a0b060907050a09120206040b2d0c0c040b011b050d0e0906060703030b010e0409060509011404032007090e0d0305 68
    0x50103100401800751070649410f40740d080390044070341007050500441030809468180c00c1010003400e140c001491504202c0140001c0015510300803403c50040ba454003403560708000105004204107094010b4001c10b0041d06915201081d10390020b45080d4000314226400d400010411055150011907258010101d0918038545031100c00020301c0201240030300c080600c246d59890066440e4102070714040d04036001d103141d03541c5842440b0403c45034005070710001410900c1884a040000c0710541c3d2091546200070074080000e501000090801e8551490411440091460200600321002024079001d50702070f2000442c01400103101c825082c10160140c1107040a20000d074071244111141645c0525000903240085001201e000c0c03550380308181e115041491605c08d005503940b04500822402008210381c60031030380715900b0107000319406400b00c1d1500b0f00381400003840c100e10042c80c074211340c00d41e5550754640f40b0101c00c452001c944084694020801e0062091f05849400d82105001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 735223192 1250 735221942 735222011
    0x150c040e01030b130606141002030c0c062206170a050c0a260c0a0e09040f080d0b030d0f030506220c02100e06060102070e0f0703020f070b0109 63
    0x2000300101001071200900420102c400220010464a02ca04840380e0288041c00250303a5000403c009280b000c032124404c0301c1103018440524000400c480c5100d0021010f4030301c2055003402c000d40c640201c000001225140b45841e001c224400791000007074803658440d19021a900124403408410003020b08108a01d0300d01030000542c0c000d416500480c0c4140ba100442940800711464030703408440d9403404040780c80061210350120030001e812401d21507694900e41c0c1c1c04403420004480d43c142c0e4060942e814100d4400003017105c540c01401c2400e80c010020030091400400310345080c40c0c0301081c0300060308038420030040d43d505000d01900314100301c0d51581003e20b9102c40008810b0a4414a8851642d03401c40d040c4c0e07070b8028001d1083c2c800341c2d0041044208120028213860340d4040b5106401800b6102011421b06900f0055902034141e407820b103a03840d5203034401036000754491440d0301c202d0001031081c01c0025031500e403128040c00c640ca80c0030038440c819000000c200a010540e559000009 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 735224442 1250 735223192 735223199
    0x61d0907140402180a030819081003060917040b070204060b09030606010e031905010603050708060403090308090406050d11100c030c120e0a03080301050321161b0602150c04 76
    0x60421008241c4411500180d403251069152940c0c01e07010840107400001c490000014011804040d00e46120b5000e0320304080045480e085a00f0401201c2c01148100384078002d2020074002e900c2003083c24424880c2c2040c58210b0000480940c1041e17103c0c007562000011711000f1420306014190041495603022818188002d00007901d0301030040c2620b04000c2c19803600f800d295030411150001c000b00007075042c5102002c1c20003034042c10b820b01003503070302e03100d200c2000568100004260b0310841d01513603030300c00d26400c50762406405e600203201a5800750b02d0b482c01184030f42d10500030440d018841d555041c9080540c0040c01f541078000c0400d44140080907a025000ca60407220444813940d01001c254956407103d5800daa0103881c01c50310a8000c0d901250100400081100a5040c0d035001c4045a00d00b400d003408003072001c042d00b1550840140140300e00100c81442c01d281640d0305125612020f0728034130745039000340d031303400c81340d0007400141d102a140407490070040f0755250700000410507013441c1a05 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 735225692 1250 735224442 735224459
    0xd0b1510030b060d0b03031b010e010c0905100341060f010e0402030c12070c05070e0c071b050415090501050f0d0b1b032d04030e0f13061d0907 63
    0x105441192140c1c0c550305100610350701402258610740b10588c00b2598070030903020850007400e102e40d10451a600c0d0a0309000c41c2c502a161031011a000288041d401800c0c42c002100a40141c4440800d850b402030341c1c100210714002608065080c4400305c84040b40c0721805410031260000d011580903001070700550650766440041044200016180982d59440381041c2640c64405d02c1a80054903030b020007031059141d4009c80c0f03003014174091011505a5503c0d035a0018882005440380020b5403420481800052943c920011f18901420702109006a480b00481c0543c0d800810889400c61060014410600c6030707c0364601400040d1144007500c41c06101140f1000c171070328000b81404e03085c0d40024000c03070580d10100e0000120303270034159100c3c10b20b54040c0d00884040134210cd110031000d40e10011410340300960f58407a030707003543e10300300282101c40c14050480500d020307194001d55070001203460710506015040081586800c8080309038000d11312629240006007040c40180c20030b0703d04002090 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 735226942 1250 735225692 735225697
    0x1e0c0f09090106080f16201204060c12050c28050708010518030309030a030213120f14011404030305090c060c030a030c02070b091c06051003060513031d0d0b1510030b06 74
    0x1303140c40f02d070044400c1141c0d8285000803230700845003e907100040118000d40e20a02e1200414420060194800c4000e44c060300d4a0160050000c502da01440d401ca162038909074051580c10000b05032820107600c02c0e01c07040d0400c0b06903040743e41540e458800380003804907410510519038481902071030540c18a0521184c907441040040030805030041040d90002248008450040400b940340c151050f403d4580103000140264098405000c0d0f442c07102442c190600940201c1051188215510355031960107900815014114030140d1041840b141000d4607040c0040c60640c502100841d110b1050078801030075100c000c503a100454010240401c00c950000302a10480e500443e80d2004558840300a0701046e80e2102001d0303c0c0a0902c02440321080361800c450040c1c1f406604140940d0b44d07080d900e61480d07100d108000340020300d80010842e1149444030141c00d0810002c10034071070039440f6120340c004000146d881e040c0c4c800c81d1a450070107902d442c0301040c8201010382018000300c2854000a602e90 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 735228192 1250 735226942 735226967
    0xc0d141005030d1e020309060a0207301407090c08092e020d020f0d020304030216080d080a0e2401120c0b0903010f0e10051e0c0f09090106080f16 64
    0xc4c1c41c2034660740c42103000344299010a41d010b040759840f604003410080d69060039114110503007070245014000388010700598010329a6810041403102d07015614105441000c07541c078111409406004603031001680a40450045107503a83d060700c1c01c250010b5030802c0c3d07103680c40022000d00459148841c103d0300420f54040442d4940040c0c8982e0003c4844000e031141007200702d03d002d800a0848c15482c5185d000d10b0083d402982141d050f284040c0c2c0c106809240c5003c4c480050340540e4038810b04034402c0505552240205030041800641030427058980918864980c01d00728050784202031100300c1d05045070040503051511052006c4a49481c1103085540c016034425540020345220551000d420280e40e103000214100518516511010f444482c910300c0c0104103410203002c115110048244642e40f03844c05511440d10752030314140d21109600001f035108019400f4050044607a80d110302d000c2c000c2040c0e46900c201480c00c2181c000701407200902d1007000c80d00f201c40341350b007240d408120309946 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 735229442 1250 735228192 735228227
    0x919030807020f10061d271e0102072901030f0f050d08100515030703050414010203040c03060b0301200c0f07090e0f07060206040602030c0d141005030d 67
    0xc1c1c45245080341410b56030781600d8030910848040c61101d00c1c10307a10103011900c0b4011782c034110300700c1c100718044500401c0c0d1f07044543c00b5184030407851001002007800055215a81100d41030032401190000706881442180d125175404180841032100c4055114441200d14032274614501d40500c00602c6030302c040c0806006098007000440402458030781a0b980e82d81c208045034050519000020580c0f036044803000e001009401000907a420004402d40c0401002100503080d075072402c0c03080b0010400140142c0704040c8200080118110a2008501680c02100000c41c01d509605280003500d8002c81440d00a80c5000c040341082d03400b040445c0517240100c2c1289940d4a41d203040380b840c03d003640030f100c036190051070f00c0051158810750145c540005900c007a908041c0d52106c080e600e4000d14401c1a0140e044003000400007422980210303070002010010500f0500b009400b1400c88030002d040000309840c5109006c00c83c1c40c1446900002c2100718000e143c000b80405000381224000e40340c0500 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 735230692 1250 735229442 735229457
    0x10f14060a060c0605150303071b0602070614160807060929040b060f032e0c020d0f02030d02040e0f180309011121070b0916030201050c0f030a090e091903 68
    0x445c900ba06c1c03040d801c207035004080f283c03140054104500d00189441001043d503410320b900090359400460000102c0e0143c4d2a1981000c0f0701d02d0108185030300c1034100c1c4d042001e8040024002800d050090500140142000604d8040b1481c1440386803030400100d001c010400206586840280c115035030307006038091141c1c401510341c00e02080200c0c41c010040e0398140135800c103061a0640c1c00e00301040021440101d000c600d038041600301d0446030031035902c4d00160040c10403659998040c107c0499000c039036104581c44e0490f5400341c1c9049030041c1d0003819401c24500140500204da03a0341040e08189042800c591105800341d00650301e00c54507803d281170000010300203603a8a000e0120519420024660800d0703400070403a0310043e0b030720604040300d1032800c2d1400300d1200c5038000342c13401001e1100d0b555600910304680040d28075400071550205584a18960000110014006404000350315120030000d01e06240d502e03190500e004046004550088140e040c0808846d02e102e50150f03094101b001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 735231942 1250 735230692 735230701
    0x7031821030f0608030c011406010503160c06090309060807030e06061005130b0915090312070203030d0f050a06081606030509071706041e050a0b0a0e010f14060a060c0605 75
    0x41c0500942d440c00c0c100249015400946440040004c01a14602c84000c00c4407260030210314800c1042603410600007401880011041000600407a140e24014100580000246c2e0b89180503180c1700c690840000301c01440c01c0103016007004000303800800ba070070180900308035150010380e2048000e2049202d46014000c2c286075a00a400315100010305c1c01d440b031509074440c088502a40e0110304180d000340d444420401180c40340303105070703428250f00030041e01131824102503894868000c01000e03a41400b0070002840000d860b441040c6500512480124052620201c480300f10740e280d50015610303400c4400c80f0004c243e1401300399401d50344c1905001401d5150204c0325841e10301c1e42c4d0001ca49691a5403000b81e051040018110b20a91142c2e5608202e800003044426402001620041c0141d1000c2820030000300f54003d6507a10a00590000842c00489411030382560a8600110302c2180d4423050b204106003100c0c400d81e4481c00940c0ca2031031562504800410503680d450001c0c00e090764450205 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 735233192 1250 735231942 735231947
    0x20708070b010b0c0a1214130303020c1e04050406270c05121905120408030409050c0a0203070f1b0618060f0212091804110a050406051c02121507031821 67
    0x446034a007d4140c056103d2208000a07204032403180015030140c0b0030081d1040f41d5151000005100a100c2c0c3c0701440c1e00401503091101400024004541068440b54005015180c4051206000c140300390010411445410020f135503c0f000d4200b40d000740800c2e01440030b00d410005a13903062078903a03d15490f8810082c00e0041c101002000c2482e540c150000700052040d1000000e00240d0b2809141005103072128110302120f480748045807405038006014141c040b6a904042542e80760040702080003142d60703c00c0802c0300410701d400960204003aa026200540180c0c0c0002e40580340900f0302c031001002001c0080c2d45e405091015001c802400030f10040d45494041e01010340c03c0882e503181150741800d1070022071602c5a40b4003207000790280d50b00051545802e001302407c0301c0d0090203c1d2180003040804079200e40c21010103980065982c0c03a07407810f01c5000c000e0b074140c4c1c0c605040006ca4900308200e000742500c2c4400f58075192110411458404101d41c2816408102c02c1c0001d441d0402031800410f = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 735234442 1250 735233192 735233207
    0x531020d08041a1303030810030b09011e0b0916090306050a02090f15220b070308270d200601240207181e020708070b010b0c0a12 57
    0x2504a2240c03251042000015405001610490009040000316446012446006504005204000d011000c10200c1d00070300d2040c1d041341e161a103182805c0e4903611040c410340b1003039400c0c0030303169034a082c10341d04100040f08482d10300001410034000b0390080e0000440c1040050700c0444021803030848900039038040e40300d2400665103c60309201900d0401001c00094100e544580e0080030813505813952860880c018035060701400a2140c20f0100665010908900000c10300b01c0087c078160000ca07040104501a242040c400d58440174145007040b001300740041c801040c05201000c0120522070350034041602051041c0d203240121340c0140300e03003500c81c12100c44400d50b82d480c040c100011071005003400012507003848200d90094444140030041343c6c0d920080c410588001ca050102000c00e10290b0841c420090201e1031003402c480d89160540d040382c1c0040000c0b5403100001482200304482a50054010440720003820b042804200744192522851711004054400f811a180801d5000f08c08 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 735235692 1250 735234442 735234541
    0xf0d08191101050124050a2001020c0303010803070c33030b041802012c040209060702030d080603060703050403020307062f13090b060703120f1b0e0405 67
    0x1d1040b542d5445c148190100454a07a60317001c048003007110105030103070048071821704982ea900a006494420442600440c0f180711001e255001c0148080c2040100051406040f0b507a01444e9a990a80f81248442c442c50748070315080d803d15a42e4901840080c031005420300f190301561210448112011002800130005580e406850315517050021a1000000c0d10480d00c01c0e00e0f0f50595243c481ea062091040603211204015000d1394124690b0429030003501c1c2043c8054146030803c00705a0000e0308003c426140c940014100700104212890b00b040f049422070003a040810003802c003502c000703450740318011010740001c0e00c510440100320358082ca40e50b841203003a50013a8840c13414420811040d0700c0201c04054910f034075040482d014040b03105110100400500152400d08959026948845000b0b100c8800f55600d03d08001c0701892401540c8030f02071003003103004c4c5624401d0000f0b00700d80704c48110940907501d00b40c2040441d500103200b00c035108514440510441c440d0022038000c0e10701300c86 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 735236942 1250 735235692 735235727
    0x6020316022e0e2d030a14030705070f0509040f020307030203010e030c06091615020c0a03031101140c0d021e070c08070803031612150e060f0d0819 65
    0x305800d40700080d010b095482c0505a43e40e41003400f5628041001031980b058042030f104520154449510355144580c2000e000090142c401c2c110054072040c419001352130300405250400039000081083c1480400042c2c000f03152031b491900e007000c01003041210011b000a04018081010f4010765a041041c4002035900400034031101d1103a0014a4030798015092a000c1071090704045610a0000b00b1120030402143e803101103024a0b221020444541100c0303800c1c00c0d40520303514a022a16104448805180203440740c8013001c40c407000031421603c242903e04e6040e0154400d100204d0882c030110346203660901d8000d616495a68007044855030a80d0b021058060001848010000090158001c442c1945c5c00d954010b562a8009030f101e1100315048555080c03c12031481c00c55006003101e000000d50f0220004003581e50031040c102d103403115040800082400b2042003001d1804c9014500b440009172400b40c109111a43c50070307880c1c040c3d80c8103242100f842c1c01040300014412080400008201c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 735238192 1250 735236942 735236989
    0x20c01020c0d030618050603030f070f0b0906010f060503070c08211f0e0103050a1b0803070f0506180304030206030406090b0406060f141003050705090a0314160602031602 75
    0xc600107002040d1a201d61600107034405440781c00b1700300a202e82840342e400600650f143c00d00c0d00d644410151721880013294880c65003007001c80400c23843c050b454459001000141403070b5040042000d40036500e80d010300c08002e0100104481e05138001c60f000c0250354881c0c4182d844041c401494460701c45c6842e80c004a4100500801c1440340c2c81d80c43c20503c440040401c907000300d07251440078400c50400d000c0503010b640040a40d0002540e81c1b88500151075089040004440d03c9401e85410b507801840c042c0c5114400102010520005010b00c0b50040e1400304d0034a40d108410200544074000c610000e4855103021001034140582508110642a80700b00013180034506440c1c03480007050710780200b000000400f50042041030390750040c0c0e82c0103c40280304400101f0303146001ca01420006080e4010050244020380044d11400600f0002e1032141074480070007102030564501d0212282100c0742c54071883c8008101607a008400c0364503e41501c03014524910550000c0303108400700c511894540c1a18 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 735239442 1250 735238192 735238213
    0x1d010201020f1810020a031403060604050409030c02100f0c0602071e0302150108030f0412060902041505011103040b19020313031119080709020d180501140901020c07050103020c01020c 81
    0x80c40072085800100b15849241c0c081348040c101d0b07131b0307044c48071006001c40e00502e00003503030fa020580030b107070301045c002e100a1030f01c0c0d1110081820341e0500b8004402040602c1d81000840c5044a800e203448541071812503c002340341c40004180381c94080024000c0c0e90300007440720a00ca61a81084075801c00982c000008500f45c1c40c00030340d14000a00a0300c01625948000b08020ba004401c0760007460302d00c018107060a041c0313541d408101034030080480300565100600b03001070f1a240036030a03001c005801c1401c10340b4540344c009007034004000107198140e0801c00060007681228400e6500003400c8a15041024844402c180c1c5544107103c440152072007000000010411480494644100300faa0451010110034552110b21407440c00751001a40240c0c2c0140300b074600d00d40c0609400d6181c0c103400f050985074041c4030204141e2240080d50981d440d01850300002c1c900c007217003d402007600002146010041000d468444605009007410903400080f9001e09270000d4040e9103100005200384c5864102 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 735240692 1250 735239442 735239467
    0x70f03060e1005150405031b0f0411090a060905030607030207020307030b1f06050a090e101a0c010b0603090a0609081b070e060f010203031b211b07031d010201020f 72
    0xb01481414454103110341c059400540394002e80d0100c1c0d4003e0003c00c0c103201c50807081c1d48071000c03e0094540203100401004042c0d511401341d03007684081841c0031907555909509104407814140c0000d003d000501508000d6610009044c50740018035240060b210089440040d0034a0310a5001038038a110726400d1109000c050050303100c201400f40c400c94034880d5141c009035001e01444c45140081020288200034811035411082e50005800191021440c1c5075048064030500001180d07002100c080307070307840c807405091003807201018044031058198034210801c01d03510300c03a5650042000352140b00100c10030810f0010f4481840244004507000618400696a90000b070301c642e600c06441c03072001c1000c0703007010090b008043c10180c0c00703545560754403101442e01042a103005081c0410410a1540b4114100142c460a40a4200c050130f9400c00040d1080000c0c2481035002c0315003010440803002076004940b45142d2124940a00c15455000d80183d0082c000c0b042e0400502500003200d000888 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 735241942 1250 735240692 735240721
    0x260603010c0201060315091b1401021921021213152c03030405041d010b0901050307060503060d0f030210060f0b0a0815030d0e03120c06270a0803011d0c03070f03060e 73
    0xc20a0742203805840d100800c08200810910016010810301e0420840dd480400c141100f0248140101e0300300c075051038001c10996110210580c4c1c0c2403045107003030003034541d2202e0301c0d03003014114034003211100b81c48110503170582c0c1039042c0e081c40d01903241c0c00c0ea00940c03824802c4c3e80050400038003c021000a0606a829038412401e1403041c6520b00045018603180049800d8180e481c007500410000b424860151010351002d48095809400c0700300200000d0050320042130510300c2079020b01280545540c02c0420f54800da0030108003214007440c240b00c01480c40e01900c000280c9840c0c1a1001d8446100e00a86140c4038002c0c9505400b6903520041c01d5034000031603065400c0c050382214400900742d401c9120601032060b130b10403e03400000200d80064555a14072004021900c0541419101c0910507850400581801c43d00305a0110042100510424080312031403640000000301e480c15140700901480001c0210043c002240c0412746000c8c400e0b48480080c0c00300c5849400c1d2030034290b101e8072101 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 735243192 1250 735241942 735241979
    0xf0303050f09011b03020a0e0910031a090c0108060f0d050304060f260405030c0a060b120313090f0e19050f0f07030201050a260603010c0201060315091b 67
    0x19101c040b03001d00c2414850600d851140c802105209104000205c01960145401030100001d0030005000e0340c0e5038180c0b40c2d020301c084d9442c5d003030401e145140280d0202d03614080d901e03102d80d100307041181d146800306080e22000c400740fa240d00710382d071007900041c1170790140b01565401c40078020b4030b00d08108000004205490050321840b800c4148560b0484602800d0120b140c050344464020a81c0000350011550f001703480766003604e042c0700b005030400d46810f03015001504d48940b941d055401c58100403007030343c5e488159074002e14541400d200700307010b54080500c0b445a0080e6115686404031045a0203034204061030310907102c002a40c500701500c2036000315000d464a024030000c80784001800640a11006010350141130403500d540c0042d1059040420000b0900407240035604414103510b810410503000071000280d00c0c200309050500710f55020442f002903a14100041c400b2030b5401c004481c0c550b030841c502007401403040c0b80c001c10040307500e0a100448a0503c0c0302045082001114100706c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 735244442 1250 735243192 735243211
    0x9080f07110a0b13120c0b070b011a0309031902070807080105010329040f060f020d0c080c131e0806090a03080c09060a030509010603052508031e0d090f030305 70
    0x256603c41d20b010b8680d00c00c0c268a0180d81c0c5004004001c03100d08204c642c100309004045024206958046080302c0340c0c411101102c0c40d041c8080188401d01e088142040d0a01c1100c128508502d0441040c5a682c401c0d20a05032b0120111407811443c50f01c2000074a0203801c107102545d00065541e038030a0302902081c0422204030080203803001248500c10a00040750000e00a46c0a1b20340b2541c0f2100342e0b0417070552080c0c40044d110070001e40007561600040c515840c1307007440026581c05155004003550b101401c14030b02e0020801018941950490311081134079032003035507081d50715a414401c104840c0554010040343c001c80081101d035003004292250000e000341c942900355551000704031540d00c2807105055000c5024400001003070310075484141e01c1a041000001c2e0b650300d9442e07251408210f000031044030b40710020402c15000c180c50f10b030001040c848008500301521a09048100e240503401c001d641803021441c0c0b0b9504c1d2541e00807a04150308541d044001c030340c5600380140501421075110b00d0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 735245692 1250 735244442 735244459
    0x1103040f0f1718041104170102070c121e02060d0c1205010b0c07080a0201051c0e34080d1b08030c0306100f02070506131706180712020409080f0711 65
    0x38105030017000100548500c0d814503181c240003a5111200143c0490401e0390750030310101e800540740c40c0c080c0340074045004188400c07261614041400a0a11018506100b00b2032144001600e404040d00e603403442080c404150088140800c441004114101166040c00e210000034490452802442a940b20724290350505071542c1c1030590f55096a080240000c008000010615140326000c03099a1404080490062800c2070000d1810b140c0e60300070380259540c4041c1c0c404a2480c800301d06401c0141c0b03050031150754070704003101e601c8a6034821140203004d8200e4401c3d0401440c5044110242c2d0710290450b2039040c10f200181140c0c00c125030b498002c00603101c2c6a100d42c2e01800541518450f50b40c024a1540e041205104c00794100803a21000384051130400f0030b60821a41c40e0484611000c00201018500954414459002e0522103109504001c1050260201c41d05400b024560190340218a081842c60610703540e01c915a8000e81d4154089401020003c1444140388450000c661851 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 735246942 1250 735245692 735245737
    0xa093e0f0711121b0a051e0102010506011407020d0203011803080610080c09040e1204031104360503190f03060801060b0d0f2408101103040f0f17 64
    0x2495071031114140700ca50007400c1d00356070801d80041410911001a0005a1700343e46c03400441c080c0d0345860200f180a00d0303100554820b41d40e091091980c021424a171803074081003900c0a002d0355118191002c3d000380d0b01500a0b1096403425048003100040d0a401d5200468007070034000e00c0c07080141e496620900070030342e200c110188503440c1907010700b450001d19403804200904210082100c0c490850711400b43d141e644945030f00c81d6028000844c065410b40c1d900300c0100080004407850318900d00c2802d441d144098003045045504840e01c4002c4030f51a2040a02d070741085803650003101404518064014610304038194811403007040c00b0500d8800340040f58079004900d007032350028000c040c11200240001031144031385802c0042c031610407210004124030820501c8100c040d00c001c0501c00c9840321801049240c40811280121241490042111010454103034845100150020700300021079140d407801d000c0541004481594400950741c2441c1203444203012580004842c043c1c40d200b404000d1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 735248192 1250 735246942 735246949
    0x1503060a0329072a030e03010f0c1b03022a03010c0915020f1207081b010903180e0c0f120a1d070b0406082a090a093e0f0711 55
    0xa080312115420044408440c4413907200303a68200840607001c001c41001c0c001100d84080c811004090044500491001c00030403001c0c1c00c102e0912030101103114940c80707031000b190740860700c520600078554801100911803c000d24180d07400b00038569155107410f45000903241c200101104660515140013001c0304440703016615240203040e940f130303150405481030902692240052240038802d00b4003506102020019a400034480a544807450703554000d904141504800c1818080036110701e00c01c0392605003454200342c0a03002d02800070308100402e82c5c881003405c5005448034000083d1112503c3d10301038444d1005055806121840340c1c50b81d1040b14540b040202c1c01c1d20030f4420005140b864035103400d80031a141c0074020944060000d54807040d10480c040f010a2001860040b1035090705ca1012070200545541c007980591b149510300039601c2d884a500b03114000000c440d9070070210140b0000c00000515015642c030900c4500d400041c042568204507024140107402140794684034074480f000e0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 735249442 1250 735248192 735248207
    0x10c12020310090e03071a01080c030714040b060403120c0204110a27080f030306030d0e130905190f1506030f06050601021c0305160e1503060a032907 66
    0x15020400d0b400051002c410181c20001500310158201da291100c0c40d101c01a43c0c1218100090201c0d03d12401005241e2003000080d0000c04120042d1480628142491000c03d2600764030f40d008541340d40582c0120303070740c007400d6600554000310501252164544000c01c1c41c6012075080344500d24124200c02d0089448080e40d121100b42e403103000d202c0c05083c4007403902541064040c440c0d00d10428000c40d05072400c0c0321551414419100541d1a410300700b04050070710000b1074030b01c0100200d009800845a80d090340c80203202e070030003500061042c0d00307042050070b00e90040b8000d0301000a0080070300800199043c0c20a40d1401100d46680790381c0a00514401e48107188000b41454010950788004902c996000582054050041b0382c0080c64000400182401c070303140d20740100380d80d6020407050740240020340250612030303d00b0600034204a030014121000c911210401c0c01c2e0080001341c0305850303401c448405181c010407101c1d50501040da20844c0b01040e6180003184080410119000320301071b042 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 735250692 1250 735249442 735249451
    0x106030b0609011b0c06020a060507080f04080309071e09200307050c0a0c0b070201020607080402031f0b0a121b06081602010209150405032104060305071101020408010c120203 77
    0x180300d10b00140c040045466008003004840040d6010f034580d000502010201001005c140d00500142102e80c2051822a1030040280080c8040002082808110030307041c00e074483d03401903d442e02c94031040c0c81546010402d07040901e000e043c0045568090000054010444800090600c030341c03c4100c400c1e016a940c003642c01c0c050b030751081c80800d00050103040034004843c01103040f0f50300d80d40c203611203a14410141d8459403559a001070881c05550307061142c04d600c0f0340c00d810800311030700780740e80401d82d20024001d0300034840541c3e0400c2484108690051048940001c2c92222080d4940c108001c50000c81203044540c607041603200c42541702d1000126084034126200c80c5801c0d5552142c14622428a12091045540c200001a4507617203803820710b00040083c6061603111070502e0180b514000b50001e184000342403260305d8107007a114032403c9806444072450041a962202082543c2441e642440080913500114012441042c1544100c0900c1642c1c3d0f5035114070719814006d081207110556 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 735251798 1106 735250692 735250699
    0x3010506091206130b09370f080408010615020d2303040c0e010501020c06030c090d0c090203070f09051e010504050402120f0a05071d0d080307170106030b 68
    0x5c945500461800c0202411807003601e460002c452803290303551440300c01c244c0715001500c0c1d01c404519420780c09902d48541803441e10340f0030641d80181c040c0310103c2d840e00360000345d40c07287c10600c40801c40e8180c000e400c5184541d281200c540c4036000c42c03c91980e0510b0264804004050019032145010b012001411801c0808001c15688113030321050442d0701810403c0340c40d6a0f440116030300504142e041c40c1c3e031244120007080154084903c0035200007505070001840d03249603001035200c1c0d40140c4d12072002c00c0360320b03100780e610800c030b4011280c000c14007801c041c4004403170890031816142c0505095040c0b079a960006026a840710328203002030710095060000c80d06c0d100a11a40088a03240306002e203240c0b40c100104014200b5900d0805041c40003c0414140c03100404041c140d034012050b513a4a1404420140c404c0c110f00b62014030038000e402c00004c60500c02d100782e00c006074004 = true := by decide +kernel

theorem cover : BRFrame.Cov 735071942 735251798 := by
  have h0 := BRFrame.cov_init 735071942
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735071942 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 735071942 ≤ n) (h2 : n < 735251798) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
