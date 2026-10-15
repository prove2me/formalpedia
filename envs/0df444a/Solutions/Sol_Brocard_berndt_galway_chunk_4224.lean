-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4224
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:55:34.429826+00:00
-- url     : https://prove2.me/submissions/c833d671-8c6d-4a8a-9f7b-e45badd8b4dc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 759532374 ≤ n < 759712230 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 759533624 1250 759532374 759532387
    0x21c02011a031914010209120a03120b0a0e090c1c0303201c0b040c0f0207080303090d2015091b0a060f0203090d0b06011b0510051801050406061406 65
    0x3034030040e00d000058034201c0740020000104c14254100c8020f80001090b00300c6d0342001342c514598402d480c0c071046001400c03c0e40030044100d4280900303400d42d0402813013a106603040c214105d4856a00421052440c400c00355914000e44501610180446100c003045071250b440341006416144421a00c100018465a42003d26407244040d9940310100500e41d200c4401c0020a030310240801d0202d03c0d61041c5407140340c40c020f0780c03c0380e91542088115007d4600b03066a030f08001e501c2e8002200c0d04101c0c3d8006039520150303548610070f0030703034118140094071000d420104242481c10300c141c41034080c1d80034481e0a00109050070084008461103201c00c10010404d000c020030000c0d00103105003c00c0c4400c1301c101000507030090007a6165030380042c0106880e101c050800280c1c00105498232404100d07105070000010140b207008000c01600180140400600490b10b40000d200050040c5601c011110642110b100d0a02405010b14000d44d404501f2900701034a14414032402c0d0782261184e0001c2012 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 759534874 1250 759533624 759533653
    0x50a1d0a03020d150f0b040606020102030c030c0705070f0b040905151005030901020715020909013c03020301051602070f060806040504140a050a05100504021807021c02011a03 77
    0xc0030306590b416199541c41000c0c500d02006049061103ea200c014100307524219080c0d0140e0084000c110115020303c1401d68440d000ea080f44410b84e5031200071b40f4101300280c5109000002004018441c00481d010180d5610350510007540d15041400055030000d4100242c01e500c2c0505a000652510400e20010342d00300040e8002d40802400c1003404008400207120400030740c150b8500395044410303500e072010b072144e085009610460034548030f4981600080340e40c0700d43c05481d18404840c0d4820340f40070000ca1003565444003155420340401002d090300400141c8083c028907005040c10880f851000600c5080a810003040790400070718168200020081641d11500341600145c007560300140e251240d05003480c0450030100400840d1140110450410070006010b03a410b1707000f0300c282d80454981d00d8041c820b80c0d0040d140654011650084150b60440c103000f265000501d500444442040c540100014124449a20340c0981d40d90908005040d0340854030810f0080700314042c041c0740300c49804 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 759536124 1250 759534874 759534889
    0x10b030402191806152105101502061005030c06040b0c010f140708012903061207171c14070503041d010501120c020712020f10050a1d 59
    0x8003074481ca200380162104402000300030009001c00c9284030304511502070f18080600020300c0356141d410111002807507098480c0001d1614240000a25650007401c000c10201804000d4130451040d29103c80014810320003500d44020301c0c42580241143c1e1400c0581ca405035006030340664000d800c000d0a1200c280d5428003240c003035414180d080d0b510707490004443d40c010500d08003221181854420484c0c07652060b00300042c458105d81c2d0300c44141e0780c0c0b1842e4445106041c0104654013074980a018003c1610000c0950b912001c046c0c402c0c00c800e05010f400600c0e02000e607000211030002d2100700c1102c0b000510211210380070781c01c04210366050341c1400a01c820019454580d80c0b006c08242c2e0801c1213414403c0301c00038000d91003009915060700c04041240c039005e1040b130780450140c03400030ba03c05403907001c5ca460762201900600191460189400603084d00103d040b684007200c0722958980340e40380b10138024a018a583c070603485603001c11001d001000e4000e07218481f540e44406d00d01d8945e84149 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 759537374 1250 759536124 759536131
    0x405220b0f030c1c050304090207231b0102031210080c0616110a09061404060504090c03030f09050306090f160e13020d050114040c0f230307080a0501091a010b03 71
    0x340e0130408140102c1c201d400d1400c84500061503070000240c005400c0031241c015141c01401041803076202400c80c40350b0810b201044246136001e4100d11030101ca01480c5580520a8000600586c0c0c50082039190b040d000300c0003101e050b0038140c810201070002c0d203c10012481014802c1d1801c0d8a411110003004c0380040b1544070080035403003080150b00c503907191107200000030441c0b40c206000f40c584a060311401806080c0c01103008a161143c0060035140a0281d002d2140d00088034202150640d101210a90700242800f070030300018440000d90f544007003141621036010300d005401c43d0110000c1c075a080c218203214010561000e003406010000000801c680c00842808203d03812b09080c2c40072400c9000c440d100a001940ba00220030240000700ea1800e12640c812508200c03010703100c9035020995226406850052110581400100540441c10f04d800d120b0040441c2c81099039007004900d03100076408220f84603510344050708200b0884048075038103400140e2140210358100040780c556404000e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 759538624 1250 759537374 759537379
    0x203040e01030209090c060c0d1b02011d1c08030412030501032d0804060c0b0a2c0312040f06140c07020d21020304031a10050d0303020405220b0f030c 66
    0x81c00403c5002c00108500341c4103d1002c4c02c41500c0304250021a40c0b035503008022070010800c09030030300c0ba14518000007200c0d0075134145c40303400c05451030000701e04550020dc011140c21012140400c600b40380051a4148090b10500d03589540780b03407514003001c00c007014020304030905040200500000c0c0c0d008a02640c0b10300e000c0042141d04d4100c500a10a80b4003108000c0e00f01c40c0300140204005034040c4656880e6801119686c0c0340b0344440e4a5030085440c0024840b4060090b00b0044403e02c00d080a0740280d172500504603424440140001c03103d00c40e0a030303411115070a080b1050010003503540281d28559a800248080c1e501d01400710200c036228281c8000e214254490100082160103070101d003000a5000f4174041d078105036080039680b50b10500041d10350041803104004408401c544042c42015003600c4414928500800d0042d0000e0100c001c0b81807540030300021a0649039010340700c901c0381d0152544e4113610b020483c40700460302401d00c480d010350180c0713041019030b85000bc0d184a841406 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 759539874 1250 759538624 759538639
    0x5060a0e10020702150d020721030c170610020715080108240708041b06030c02100b1008060315070305071101090c2d090e1504050709020d0e0604150c0203040e010302 73
    0x80300c503100001c2c801e89000418901805142100030030040030f01805203809c2c3c3d10204000b0b99500c2c0c00303603040741d849000041860350150001c2d006060000e92030500500c18012030b00b02c0358a540e4800702160b00c1c0500340c800503a4032001084a0740301041640c0080715200f08601481d200c848500d6079840000348031005001d41e81c00031804114400d50088014a25843e84207010398035098024060b103420f05450006200c0e50a4250807800d4030f204900c91008014109841001c000c2c00503540c030b0b01c00901e142c0e818060281e42c1b080c4086000104c911178046c070f50740007645140644010345003002581500c0d9060385001401c0d40000e0100c1551015512400c4003a03102081450181200b84047c04058902441060000a00d000e054015216544000d419a0705d18039011a8601080c14110f40181c0103078848542044100e44642c02400021144a80860941c640b15405407a240381078408503080c0c2201d11300400c120456100c0c649624040348042c515140c034101070f140d4449010300000e481a440b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 759541124 1250 759539874 759539887
    0xc010e0f0616050324040c031b090e0f0a15080f060a050106022d0d09091b0f030e010207020d0807120509030307060b0301020904152c15040905060a0e1002070215 71
    0x140b500c5d140424074018418440052940303c010f000d0050981007001e0f61050303200078840b2030b01644031b02c800d66800f150035000710b41d00c4424031442c501d4040c082e003448658840c3e0110380c0105a0701d20401030700100b0003d01c1c8502d841c42245191401c000e00c00240f05260034010b02c5915404254102e03000c80052045110070b140801b080c03103007c0b248030804414825040d0038910aa002440d0748111001800c00b000b50300101c83c2d0300c14007100c071180103000084d0f525103504046030081d070000c80359808440006044c000b0990124003a444101404c0d2112000490410200201c0c81c1131414040882e14180f8104041003000c6542c9005192000348142d440d59032103d0591006d60684148990041050015107450311080c082d01c06140a42c40c8102e842141700c80d070111000c0e00507045d0030066080504c00d0b42d910303031801c0d55008201100580c007a442d0385911000c00c50412035140640c15890700000c54420012101c2c0c07400b44059148941140140810702c050707034070490b08190010740009801e80d01c01 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 759542374 1250 759541124 759541171
    0x5040b1f0905031b0a0803070b070518030a030e10030c02061302180106050406020d020703110915090114180108030919120606140303030613110c010e0f06160503 71
    0x39050304810f402d0b1045a101c0060081d01010b2140e60201c00ea5202c00c2068840d03001c5070b20b038801d80c0e0000c0c03c81000b020100318094803800050003298940c00390019844503010000703003030a156140039000110400c030616803a2501c00110f1301304040609040014410070407000e500d40d10024201951080145164000c0d9150005200f1040e01c90210055207586c5568020b881c9801034000c4400500c1612244105540009028003e030381d088601404008010350802825200091119507822422030f03110300c0075141c0031051406451207010402030200758909101804404446100324141540300401c081c95010080301c11403079003510f031040c0195075002c1d20349510100e5030100d4400300f001a40c6a0602880340d100000342c510395445121b984414008041da207020503101c5076403040600c0b0b2001000d101d03591101000b003051009450601c440900c0a6086a40201340c244c44d64101096000302c020302842210350003164160b104070841d02d0204014002c0c00010300308408203912407048640355 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 759543624 1250 759542374 759542387
    0x220e03090307030c0f122607060c212702010c170c01110309100f150f05030607110d030c0c080a020a0507150f03020306040603060518060105040b1f 65
    0x2600103070490340299a2440e08002c080c04a00c00e020741031a0640020662040c00c004170040160800600c4000d003c1b0501c480108a540f00c480c481018420400304000131507900400700e5580c0e0075220258008a001c0348000710750b09083c40f0142d02450041450b840254011410528003560681050100c00d14801078132298120f02c13010700780500c018051542d58955000400800002200078804c8044861800099000030317035110308203400c489500c0c40b4607000c550000d000c0384103007a0b000c00d203001560348000d002001c0303030080a00700344460014051810300700002900318041d0b241c00000003490407142501d50342c02191003802c140d01c03640884480e5101e61b021480035500443c08507030750580140040d5980c1a03116088489000d14000040c10289014001c07080e2035041e1074044070141d08500850003540018401c580c455034540300400428000e00c01c080c8150942d2105e2210303108070b141440c3c42d051050b0b206510031401d03d0380c200f4458030340b000710702007104800c200c1c0542009004410707103c8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 759544874 1250 759543624 759543637
    0x9032b0b04060b19030c21060902031602120711090c0408010c030c031505031e07170c01230f030910141f08031e0f0415030b220e03 58
    0x1c241003038070114030800c00c3c07801000c0c424494146000d880090060603416108100c030700c00007203003409030055100c0f485150b108592180d154030004446468006050498106440c000c40c820318440c400b00500760100032200501c9881c5103402e0412200341c2d901244114000b031090b002e20140b4000c41d0310400c400741a50041c1c076904000780f051341d8988400800400d07201c0301c503100190400200c06195661100341d603044d1030780500030700380310441c0e01482e1283c0302034848100c625101d031180014500c49043e0382e02080c25544006001c0c1079072040001440104a244941d14401c0405540c529a4064508035008904101d84050312650f440341c0181c00c0c14074006558200d141030424a00b00910540001441000c100c500700010030a511103107030804506000b4803010307034020401500303001e50420000c028000460002841e000003401205600e80056104c400529000c1040300b0034240c0502800d00001016103801d041402c036010a50303511204c1c05000c10100790b0760044c150300f039601402260b10 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 759546124 1250 759544874 759544879
    0x30c09061805212a040b031002090f030106170d08010b04050d060b03032223061b0703050a030e0402035b050306060d030f020a020414060909032b0b 65
    0x150740d1912940e080139481600d41c4494810550711203140c1a03e0117109011600602500610464850200c2e4400951004100681c0030398418803005490358240242e40c060700f03c0e074403c45200400301e90b1030b91620f500301e002c80c07080c0403108005220458034181600c003216011115030940e0040c80c200007000702828a421038050100241c485131400394003868160b849104082000166507415841600d80218520010300014550b013144441c41c01c600074121201000d404101c00c0e601d00c92000e80380c03001e240d02c12038482e08480040f40a054002c4a00300d030103001500d0070f600c0c514107102c0c038000f480034104006040425400840740507005600b4085043d00301e0101100306403007140c600400980e8020600d2031444200d83c0b010805040c0032603500c1c020200500080b0001090b56000d0741d480310031141c004210711803440f40300c0149c1d0300c900038854803440c2006280914144031050042151000b4068009a40204900e24129030341d00520084024034540702c4120706041c0d14050003915400c01d1059 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 759547374 1250 759546124 759546133
    0x3010b03010933020a18170d1d0603040515011202131d071403100c05090603041a0a0207020301050906010605030a0f021605010e06100e010e091c030c0906180521 71
    0x24842d0401c91100186c4060700d0038107407031542e900c1d46c2d00f24000c9070300011400d43c10032025241d845004403520902d42c12300310030803c102100c4401180081c3c00840707003a03030580d00004804100a501581d05800741040c1588c641d00214142c01003035443c8448026030035226601c0c0b0088000d9400b480d0f14516400303c540940703580e84c0c0c0e2940030241c0a072410901c141302e1301481c19200380148a42c41000140304080c0c80302424034160f802000520b4000030001c2d80d901c0c01074000341b0454410807490a00c515000da80060303d0719151300606084490013005003006500c14001440103036040010f4a60000d1039800214850311880740140103801104829090707100340303e2030401000010b4201c40350714081d010454030541e54903002078040030400c2c400c854400d4200c1d4010322503007402c1d184166024903d83c080b1500350200706030320580d007a80e075070f541c0c00003035507500c445e901c540c0e03006414000804403450b164160003013a10001140003881c2c0b140340e00c00c92a01465464030195405081c00581c255230595 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 759548624 1250 759547374 759547387
    0x6010c021e2e030501080d140c0d1e050703020a02090603010b0607050604064203020d050a03020c040c2f030304141014060f0f030111040503010b0301093302 69
    0xc01450b10184522180c00000401c1440c2588a807080030f04880808009110341d6500100c20340345842c1c1c1c214003105e085010041c400c5840300400001080040e40c0d0f4801c0842c514180310140d0042c503e140c20010844200419804a5800180482906c1e01110702004076107c80c80004e0041c507403004203a0300004046410414040042034407842035004820600403040401e50303014000d250420002881c150211000d0291424800f09854000038090300180f61520307a000038510702143c550488965205814040c20503505011a14040505450900c56070007100f030007030031131040d18080e510b090701d80c000c1490300d003d01c01e04a02d89140c00394041d13070b07030b0313814142050403210443e00c06a011501c550070071740c0f032413030028442d02911524501490b1901c0d1140420008030240d4482c0c0c0c00e904c401085c1690956647c01e02c69101720104001c41ca655880c500340c14035007034600075000d65110f0791422428101141c854120382441003084c1c40950718000c110018448019408550801506d1010542 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 759549874 1250 759548624 759548659
    0x6160b0c1b030702030601060e0a090c0e060301090b1302360603040c0824010608070306030c06020d0305060d08091003091208190608070512010b0d08120a020306010c021e 75
    0x1c15030b03d4003e40a944440e03803034000c150346452148600c180c2044009804007c01e00c40d81d4043c0c82c900703d0710b01d000d0344844098800144550401e80100011642d078044c00d800e51700d40110410909011407100394104442c0801e1000143c1707100302c03000142452071020b203d60840c200c00e10403c441c1c000300226120b0030941020440b2591601607a005e41c450410316800b4607827029103d225840d20003107041c180f40c0c00d0600880389144007908c8003041c55100d100101c006001d0302d1041001c1c15003a40100302030303904548000c081d187c0181c1784901540b00c1d104ca55000c905103004850485c40c00341c614841d100b050110440040c59101805002c04894407107a68215506c400b00c24064546440140407126000703011604591062186509a034030580b17041005081002040306081852030000582c80300304804940080c0e4010801c880d1000c00249140130341020305560f40e00b2661040c03086085261070707030000c1c090401e00d82010b40300d003402201c1e4072444204501190700030308001d03180c0b001c00e0504004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 759551124 1250 759549874 759549877
    0xb180301020d06030c170c040228030f0c05180603190501080706080c030f060108070504030206040902032502031204081b0606010e04140414030f040e0103030e06160b0c1b03 76
    0x10461740e00d8840140066111082040303842213145034400703400021449420840203612444913101034000404d5401d0704003800c800384036582d0341161000300341c1841c07050303001d011504505071141c1844400d0080c64002c5891145c0064088015900a50780780c0310040844040c2c400c02d250150700d1400c0c0800411048000b00d80c1c0c00890312540c84005080e220035150a2a9020444510030b000303580c100004c0e80c0790701c10b07040e1030303044001ca0805030701e07194403a008180158019040400900d23000001c0c84407039040c103428041e205035000402440444209002520f0384508a82c42c0301c400e40c0c0c0d10104041c0010401211007c0049003280c0403030521f86a07580c3d480b1541280c120317012030114140d5014a01b441d0040303410f013620040b01860107a5883d5154000c031003200009030210302c428040c0c0261188810018000341c444002c09480c298550b06c1c00030704200d202d40005005000034015820b041c50a0340c810124160302c9800c000b460b40e03480c2e4514045000d603412049155400c580050500f050200 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 759552374 1250 759551124 759551129
    0x909050919031d06030408070b0402010516050102130e0c040b2a01140601050301080c0409140303040f050c0105120112172209020918090a0210090e1806010b180301020d06 75
    0x35005000c0c00e114008204817800112000b6000071020006800056501e001d001c0e0310034414107041d82014240b55046170a403488505c1215207a44c0064112142407a1490200c028258030000a883d0b1500c8072507401e0340d025511030a400000082102240000310f40102d50a01c002207464070f10410454640501800d01d5500f45454025150042020340d441002101c0c140d4890000410300500e00b10140002841104070030364507403001004c8000b180e40c0034802540100e0140210b00d06482041c103016007046110f1803000d0600200300b0983d4078901c01c0d602d08904441003030245101244032800d000502482000c094041c1c0400010400854060702000703a61240d0010081100207440d40144070807845105810740e8400400082d0440480b0056422648107903d6010b9403019403803940401da5007c1d54207003c10202d400d0603010700c010803555520f0b82e03200e0255040c01c0c140134034540c20182ca5400c103005010f000180021a4600071701d0740c1445824064014000315502e09018811200501090 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 759553624 1250 759552374 759552407
    0x31617032701090206091207030f050304180504120e0112051f171c0c0c03050601051c0b0103020907020106180b040b0d05030f160203010203161e090905091903 70
    0x1501c0c0441101482406911540900031034940348980c0e080111440340c40b400440244511034010000406214484414600c160300843c0c4840c00c11071241030404410b401140510325100422000c6202a1019a60f00c1039600f0315142c00a0503900484000c501208120b0b80c00742410103000d0400c1440c80b840ca5440c0d10a0104540d41d03454140b80642403803514662000e07a0300c8091442054003442101080203101801c05404200199803003195003149507000b690160031120040003142001c00c02048200c20000425030b1120503076440c680300c1c9006010107802035041000041805000354403482c090040303403a0509001041d60b04d00400340074102c52541c0114101500c1c03c90074103000010040b266030150156042030080340d4002116002420700403001c2c20604111809601c01780300a50054104c00da4841540b80043d40181003512131000c0c044040511402c0c2c0100ca51303100c410382081d108044004074180d20341001d102c0c40c1c841803510001040b034010008004140d0010000310620409 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 759554874 1250 759553624 759553681
    0x305041203181d221e0308070c210210090c0314030c0d030e0118060207031d061204020a0510080f1f060e12070b041706060303161703 59
    0xf100c3c0c540303908040c48540c0801e80781d101d03004142090282d403a042c4801e4900e81002c4c0c800c10781c0340c4a011900305580f0680b1030840422400340d00f4141e1000546500545d5410545e00803076442d6902a080501c00762005094544d030040e03855840d20900c251044410b118805105e465583d0411140c891003521085a51032100010f03a43d01407004402c0c3e62104000901600780012028000e901600c0200001c240555039074003c904000005a480300312135018500068440c0c50303620b405002c00004d05005104e4402907128030700144e56040c101e50071481900c03841710440e11144080b445c0038401e504070a50003d2690590ba030340300e40c0541c0301071295160030642041501c941c5044440e40d0003000200d00c030b141c0300d064240020b40c040c8040c3c2c0c00c460303c01b800e102c515400c001c071000d003044841c0e000000d00f80d0340000e0802c250070b1990651005000810f014004c2410240000303503076442841e0610400000b6007210405100b1744060b012000240c01c04542c2d500c1c40e040320010080b0800c6100c035542c80f0740 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 759556124 1250 759554874 759554879
    0x906050f0906011713020621100b09042c0307170403261c021306181403100f020702100219171605070905060316030609030504120318 59
    0xc0200300d8034060041a120075400e40c4211132600c0444500402841031084251004001030b111030000b0104048148262010201d00f0706804041250144c1031050620700400b041c808550003004039001c41500b120b0000e403c5460f12500680444a1b0040e40e1a03034034008203c424940c0c01000418002e07118420070801c000e030144002c44103000d98000030b800a40349012044c0208113100300c02d81d002100e202002d052500582c0325481d60b102d01d21160445940108100d040a0a804001c502030903a90800c0786d040b00b034884c8040601100d500c168032134150700702803548941d02e040c03111143d10345080c1010310000b60328031a010040d5100202c00c0b801171075a4101c0c005418804107102c030102d4004079591080d8122030f142d0419041c5020000f84a031407040005504d51006140384101d200c2c420000350040a2402a800040350070052106019421201404080e0401c180440003601d900c040001001d20013070030111054000e54000140062001810303009040c0c01c030b400c0c900244000c0b1640d480203038 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 759557374 1250 759556124 759556129
    0xb010215070807092328120609060507030c0806040606080a0203070306030c08060402130c05070b060103020c010e0c03011a03030a0f12021216020316081608030403080f06010206010501050906030406060306060906050f 95
    0x51080d01040c4d50002110400c1c8588024000300d04043e5005010124805206403112b074100c0344291485000300f03554011170b9095507000201594090b5080b14108504ea00c3c048000d41301c42d2004042030f01b4285d0000026440c02d01039840b1001071900100e0b5030040300d4840c6d03a10303a658181a01c0681c414210303010701c6454581c65000b00d020445159592609080d4507640302d40c02e10b40d010f402c1034107068091101c0b08a43c0401d201c0c20500460000082004010fa41c040c0343c2152090705003081f90182004280350251400800c44040c0091490054051081c40c42e040300d01c804c444940c14003d07800002c0500c12844014040d50140e5000c00d60714400441606060b82e07248a814513040aa095070103143d004500440e01034007801e40300101000048500b90743e0219964800c40e012404a0501010b00580c1c2e400403c0300d940c001c1c000c0c0000e280950406001030058059582c0f487d1184d03900000080800001d034000c0d10003540d03c08003e04c1129154081170018100c0390080500481c2240403100242c03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 759558624 1250 759557374 759557419
    0x21030708131e0306020a17100515070215030703020c060a090519030f0507060b040504051c181814040c061101050103110d0305071202100b0102150708070923 69
    0xc41a21548030b80382c5980e8034a00a5000306c0d001c001400080210310084d01c1092029a01c84c10481c01071200c11424501000307070241c045200300c010b280c800d011200040e01c0e0b444040250480703248003a600d0350b681540c110080c3c460521040c005006041c180103c41c0030030342250384400c0c496010b8880d144104041602851f00805000d00000c0c03c8035007a10500d17018500038070200b405484082140741c40000810b0540d40207440c100d409a010b0344000002c501c001c0d00f030040b5002586441380d14000f2a41c440d1040301c0150142d00340619a807048000401da06501a8507a00c4445007040200d281c039040481440440b4420b2202148461a0030101d8220620805040e030394000c03203420402060074244030320080c101d4030031000e100342000701c20049000344d0103000070203480d5030080c01494000008102601c0c1b41884072810755020342140c2005803c55020359a10151504d0144e0b242c0da07400c0b00854510203150b1040c2c464040d010f080c02c100c00c803940f605111504090340c080303a021014a24a0040 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 759559874 1250 759558624 759558659
    0x90507180f06030510140103050601051011150108010c09081903020111120406140108060a0b0f1801140d030c060906060506120402100216052103070813 67
    0x16800082060200100c0001448601454120001452804441c4800448646403c2a1041c2d80242c8a0b00c8030030400c3c2c002d544420841c07071401c941551540d80d480b503440c00d0602400e8815542c8001e4020141d02c41d6111212601c9480c088030071942503114011114042030148501d694202955441c0940c05200c100c0c0c100c0b1b2180b0b000380601c0701d0340d05c0066a082c1443c2e038218119503c1e85402d82048004502801c10350100c2d8100e008541842d190030301c100c0f005442249581c0e580305004110f00000032507100d6000c201c0e80004a40942c5040000b11107400407143c40d54461009013030105114a004401e6050b15000c0d0649451203004004107e020310280c0c100030b00241900c1558400902290416202e4610584000c00c3e02511000010095001003c04143c03012440703082005500c5c112030071440c2d144203400032f0403500c00e038a00c2c0a00070b44c4060080038010f907101d10800c6e55615442c00b81ca01d0030070038031003a2a03c50b0304031718043c400760380300444042c0d80710070001d40403d800c01e052409451 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 759561124 1250 759559874 759559883
    0x90210050903060709120209040206041d0108011b090b2118100b06040513150603090308060901060519110102070606030b01060809060a05150a0314070605030f04110d060f091509 78
    0x81b140c002d5420400314600080080340c100d4414480010000d074441c415290742c190f0b0800301c444560410143c0d6084923750134001c0c1882031500108803c298024566000ba901c032a0149039482003a00c1d14051842c6600071042c0e041c0100600b00044c0c0c002d54102d8011841441c41595840b48034000c1507030685014511181d400281000100301603c0d001230401c5030301450400c0890f4901020443c0342c1218100d900440c0841c0d00c8ee0002c0d410564806070542d40110f081300c11002c603505000700180f00380a4000301d40b64500249000c2c9280c64002e400440e004800800255500c03520b0345881005020144002c0341c19a0300b0f10008240a03000f00c588610854100004184964550250001800f030103840041d044500c03c451460300d0b107681080a0285009545181d42c1540c207a1031145800440e5220808200c0c05009100c00740510038540c80d0080e0b0401e07541c1860450280016141b0700741d008000702414a0200151b420126642103003110b01d01a410844140b080a081d0340181d81e00c02d8002170 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 759562374 1250 759561124 759561149
    0x606090f050307060c1b27052403010b09040f02090618070c06060503062415270603040506040303050711061b0c10020309010e0a0c09090204090210050903060709 71
    0x4913003072082240b00080c3e8003e20b114104503000106061844042c1e40101042c0311094541c8241e000361455a0810403d00c041d003040700e8540100710340307d840403c0400c401840180341e0b040b403003070380c0942111000c0103008102c1040d5052510340a000d680d0304903412801581d465000444600d400344804a8414a441c1a4040ba07942c80f00120350780004064100d030302c1542c80c9000318680d101040018480d40040c08884d109505400070010000c00892186100e400c0301011000c03469407081c1038603180170410701091040c0300a0700440340411455406560010400301c1008144980096828080d0740640c40c10001921051011540c0d48401011028503911482c007060240401980c5000e0708040d81101c6401c2c41d1126030124100044420302c0c800641d004410301507480c800384540c0000603002130003030855020b20b41d01c03940c0150b618440d60f100f0554400c0e2110030364840f504419042ca13402041c150112021344005480c41e00120041030085c4a40000a414a40258010003c0c0c8411a0300740 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 759563624 1250 759562374 759562379
    0x150105130501230d14030c010605040b03070504090c05032d070620070302220e0706081b04091b03050601030926070602030703051803041d07030914010606090f050307 73
    0xa5401e08201558a80c204004e424803c1c0440d4088240709004940c0c10301569458040710070301801d50b10140c0010f441103141141c603080b1990009102c1003183e10944021444c401c480c01c06400b1400d196016682600a40000d04410840070304000c801d0340e40d00c00059241805804000c0c0d882055020382c0b404602d46180c4001900c040c0300b030f07603568024100101d0b1129506d0b035021607401480743c1c55182c0d64959141b6016015100c0d070180176645000d91004111186c54030200615900019203014030141c0c410501402d011142012600030b011040014003035052410000000408041e04440c0081d140002041c405d62081c028006002c1c1c001081507400c03080f040c0c9101e191081e501f40d4040005042101000007115400514410013250701c00141e645441d0003000f065188101014146030000c100901024940c111207100202d030b1509101031541e20710a00764000d013101e541c06001003024001040035a00150865030a507a1959103000c0050b039215100f0b0510590303406002c1d4107070001c190030f = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 759564874 1250 759563624 759563669
    0x4060806010e011a1c0b1504140303070f081b0f0a061107110f0f090405010207031407030215060d0f0605011401020c15072405041a0103020d020f03010e150105130501 73
    0x7014610300b0340240001c0342c0441d44d000803550344801c141042d10800100d42003007012903194127001440d50547c0a180781c840150f580c3c0c07400030742c8c0f40801081d000000c995907100c404402c094371990120401164903914400003001d64620002c0c0d812640c0c0e07070400c0c0c460420901d038041651026540000c5050140400740c0400c851013085803038403a0400f0490f04c1c001c40303556515140300d001d6406140016500c0c0b040b4140200b4009454084a8135604100b08100000c7d81c0016680303108102c1c2011000c003a00e45100180703030030421445c09020f618450240740306010055209904903100d1209000c40400d0b00d0005985031998181100d6028a04081100902890000410a5034413910580f0707038200c141742058180803000c5103080b500690301e904110805c903001c11140e05459800041e034080e580345a000401c0440040c000030f00401c00d07004182c05da5102504460401c54103181651802e02d1201410b6035140005d101d01d5120b490740943e145107400701c0344a40d505035003200c0720400410000400 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 759566124 1250 759564874 759564907
    0x20d02090a180614010b04120f1110180e0601050711040e0a05100506011707271203020c0607050706111203190e060f07030e01090204060806010e011a 66
    0x441c1903882e102c2204126010040514500d0321a20001945010030b00280c14019016086003003900c000b0803080c481e032040c14a20000742980241e421068419902c0c0a880302c001550b485a0000685420a100507070032020f80c19a20020401074107002c0d40da050079259010301561a9804140108074031000b040d100c82810490305c1019101140744d0300000d031490b14003c00c480082d0381d903800070407452580303442070700815400c10424031341210a1603102181075520300c8060002c00501141c88482c0400c0100c901d034040902d0b81000d81c80000640c0d9062007529034010b01c50480040c0075a0302614800e1515106840245401000801c0a01d0420318252140c186c50200e220070b500c24440514405804040154071584140c5000c049640ca0201450251195003030404050b03003100c000c000407004852000c5c2c4d072198a61402007503000c0c04820190040044d00c40181d0400e00b00038022400141c00078069040340d0040804079072503030360b0345000b1118548042e0b0540e0b0b0b0650401041034040304012 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 759567374 1250 759566124 759566131
    0x405190b030c030604121e1d031e0c03190f1112030c1606030b1810080609070e22020d03090801150906062109140601081501050d020d0209 61
    0x34100c0d40ca450001d80040d18020049600b00c6e003540c031015042d4a92907204401c0907900c0540e0360900542444a10080c081d804400854000c000200d10021500d64042000343c10280304094100c3c031343c030300c1d250465403140380c480c0029010b40b080d03004400c4030080203002d80406541050500e88210a0350b038030300c5004411005440d0b8040701003041e50100103018401815017554640050040010105100160400a0f032040c022300d441e00541000a03200d0308a0071590442c800f0304010141d13a01113640304500700b644c108420a1090714104140d1003800103500d02a10301034aa44000741e42c818000d601041c01010780010010071901c0c40b200182007030410040198802c0c00d00d56840341d25003c101e42155068800440d50b121000010840c0341301911811010b0031071842c15a070824a00100c0c001503150182c10080e1056130740d810f0005101c0130b20b441c480e4850a28003540c8445d40d60760328869907100201d0b00b1001294004c400050344d0318190310f154072450b81c054480b5041805a80270401c00040c000c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 759568624 1250 759567374 759567379
    0x150a0b0309031213170406050304060b0a08010c05040323030d020a0e0409120e3012031f09150303210608070807140102030306060a0509040c110c0405190b 68
    0x307202c041c005420f600021842610a1042540443c81c0e500b0190000760610280510340395081100340807281d8804204e0b039019410440100c1e10075603440205031150800d6000303001c25445c0c0200302c0315580d404030007031003102c1c0a0307080c2da5504e0b06a405a260b4440304c040018030303a64810480507030940c0c0b883d000381000039a5070030031880c0f00c40442c1c040b5041d2405004101c0c0c45201c00d003480c4170300740d4010740a03800002d016102c000c0c9000407142da00c0072900082c0c8200600b140444818405840104090074001803006401900d9092880c42e003031000d142c24001d000801072012001c20700c0703c268400d220951020130055110341e85546c40586441420b51840d03000311802d40701c400503141d550701480006100c0f5070300800c0e985103420001c0c0d00b00421600095100e070801a81c1407826a40017060366003041c0d0813500140c0e581c4603004160381c644501030043e0303085424151007030039150300802d200c44051080c3d0b003030700c0c014007001080000302c450854440c85980c008000320070743c203030302680b1103000d07034601 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 759569874 1250 759568624 759568627
    0x6010b0a0c30021c0912080f0c030a0908010902060403020105280504080c040608060f100f06080a0605040b09150307120f060e073b040309050405150a0b030903 70
    0x60038615030701d182a800350111202c800b0004a05010350400140a8508240c0c00b150b80c18802081c004108004501c100c00d58032004915a4040c0000042203407100980c1c541995582c0301d101720781a441c0e40103040c00c0004604036020005a14906008584250b6401821350380f4150543c0d00664094122100d00143d9100c001c01d80700c210200d2041b250640c04280d100c65848501d000c071410300d000006400180960b060020820002d900000d0b5150081e0210142c01020782d110082c038600310b8629400f034003222407849070004070b07190442610b46c040c4c40059410f000c499203a80510042e14040f040c1c0035000000c100010f4004803101e000301c0c603600c0c0c00400b0796600d6503465084a001508509007640c0d00c00c00d0410000030003600344948240405044058400185000d01403092035030807551120f0301100103008840330685880404080c2980d20040080074149420300a0040fa814001e43e40241d1030704001c0b90320178481d41c020f0140c0f658000c21341403004e410f02c1d11a004980018003908105e200 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 759571124 1250 759569874 759569903
    0x6081f09020d060816080307120311040f06020706110c10031b02150a140c030709031a0414030405060d0f0b0928020304151a0913110306010b0a0c 64
    0xc440c00100726542803218082645030a2601c0300d81071440c0e081081d82010708041c41000040004002d6402068003c956004140c0215074154050003d1803080c0c40c200b134001601049101c4840030420a840e050750881d0181500e88000f9101540ca003664031801d030b40050241e626518090078032400285003480c01044100c83c1500c2c2090070200d207080b80c030140e00203030100c1900074904118517070b10130341e07481050064590a606130207650764090404180f4039000030004820500800b411030045510982c6034242c444030b411440100f900aa40c110303000c5500300214400741500000392029104000d04140c605100c81c0d9510f001042e40d0130f10b045006407908122a0150345015440744200010382004001c501641d50844541d80400803d1031658414001e010120740c450380c00e14070f03815a4000020f9032583d819420b5100d82a00707405280d01440107030070440116066110125070a01c41c4c400e5412746d41d4603d08068440c030090040c2c06605005101e03031a0103520441080c1c0741c250040c0c016010048 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 759572374 1250 759571124 759571139
    0x60409090309092c0c01090501080703022802151b070302070801021303030f050a0203090d080d0606110c0f090a021c110405100516060c050f03180d080106081f 70
    0x340e861940703000000004540d400c1410303060308844c400d0030b84d84e80a00f218050090011348002114050141040344000000d100341c1c0c02a1b048840c04200011032003900c0881c0555141001c000e070f511500180510400000302c4844070464500813612030f0360700090301d8240d0a005603a034220140503001c42c81035200014461000784003c2410039032a002442d491811410017a009000074600401000000c11841c4080c43d07022080d18a489821180d10700c100ca0281044441402945171001c0c0d80c91030301c9030004503160020042d100c0c0800110a556200c2c070640704020090b500304181e02c0c0c2112003540001d443c8031885c1d0013030000b00f140c1810090f07003101c0003455804031501c840c034840c81507500003001e0001b0b2070443c0a804400c003035484c0091138076130202c4c0d0b60030000b04402d0000744016104c00010811502410940c0c0860102540e800c0d124500642c001e4076a1141032251610380c000c090210703c426120780d018038183e84c165180c80c1c00684889280d100f214103030880110b21203024840108140c2e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 759573624 1250 759572374 759572381
    0x2032806180b010b0f0a050a0c080d15080a05061b070b0c090103050a06050f0f01090b0703120609020f0f0c120403060e070902090f01110a1a0405010c0c0206040909030909 75
    0x600d62070744900341c410550300d80003682e040183c000807091802840700c80c250b403480b141180c0450031285030058542559010035218142100d000605a400218004110026603400240940e0320120022000303030380c81c5502d58031a9003c07440500580c12100c0014516000e00303c48640868921031454900354036900c4606500c1000d5880c080c041c040020034507034640c1d0600400c3c0d000040024204450b52401c80011400e220300302c22107001d8018010200313816809080010018035040c04002c3c0d441140d4a4000c0910070903441c0e03110384500c0c00f0030204210710b0324800e41d4039029018059600d081c10800d803803034a640008030003414510070201a00c0e03814404030003600c015407260308041030341031402c1030240c01c02403550002141188148140d54407592100c0202480e850b080c200f82100741c0b10700361500d0400e912030f00e0140514005090035544110f124510500c114010f000800078032203407032403c1b42c1d05680c07001c0280d40210180300501115441c2e0340240b01c664400d0070070260142c1c3e03a00c0c00c2d40c1074 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 759574874 1250 759573624 759573641
    0x40c02030723071d061927020a09030c0b0901141b01020f1b0109050d0c050708190507120b040215091302090a06050403050304060315170d0f050702032806 68
    0x4183c100011300d40c24885070038005401c49400c403940019060a011014031058042c402d046042114600185007207005907200c03d05400d403264103554441c0113150142c5001c3c400d200440d106c9222190010750b145c0d4150907207401d044169600552800c1c09402c082258001c7d5261030042423100507040e10003202440105030704252080d05a07103880840c90000d000c051851494507040c3d041c100308900040001c03c001c0454116810180211809414120721306607894210340d0452080c01d00c2e10749022110aa0301d40308511440031103941035225840ca08501c0c004031001815001d6013800b1400500d4010f140b035000c811401c10395810036010b81d001410300c1039140c03180440940d000800d20b0386818420780a0300a0701260500c1f5141c10318640c0c400d5541d00c1035226050405580e4030304e08080f0320a40c00c011004010548188080800000b101d9485d03105034039404e0041807050703444071207942c0208180c80750140c0050281c0716105190304114500340c500d15a031a01d141c2c16802102c0092480d01c1070060 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 759576124 1250 759574874 759574889
    0xc04080105151807090605032e05032505060a050d590106080a06152408040507380705030336030a0806040c0203072307 53
    0x640b002d000d01442210b40d4a540480545a0000b0410a520b41c102d00d00200301e40051a12503925a100b00b24500c40140150021842003062000c1001c19071100c07006000f9280c0850948003a0342c60880e080d074850a010761148590b01c80510104001c3c5411009420703603542074100545003070103480030003040b240e007603445203040011105a80708850703560f1a11708800781041d6410b400b006074116070000c410b00d000280c0008010b480c4007516000c2c0c0c01e4102100615220f800c8401740000e9180881c054864400e030b48140e0116a840080c00c0c20901e46c6041303600d09440b01c2c0f100701c0e0322410400c40d02214006d10a03580e600c2001c50008000d207208405031003003840151244607115208011401d602c00a61000700020800d0226501051010080380d0300406680f00c481088003c0801c0003005442076987c21111140d0f812015a14002c00700090491040682c1e175075241e03039552410002196203914200c00142d1040c4a8940003070341145030548a106521684081c3c5212039080d140341c83e095820016 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 759577374 1250 759576124 759576151
    0x919021b0f0c03070803090906030c060f1b070e070c06141806060d0c1e0801090c030b09060103120f090909060902090a110a050304111002010c0e091603050c04080105 73
    0xc05122050040b0704000310124003900c002c9142000150392805100303a030340e100340603a00219116682c10014407040e0000a02403684034001e002c8403007019000441d0403039008007180c0d040c01504001040c3c49080c0c8a020041102c151109101164080342c03d22044801c10b5984810f401000546194140304504017894682a481c0b0050484c0c2003410180200380a042e4401960000464800c0c00f5025610b5550f00085041400340c0660401120b66000500a518100510007030000c104d00070810749001d50048181610b840b1001daa48500900c0302a2281c41d2241960030168811b00083d43d40c0c9660f440d00c40501da881c1c00b00c003000c03076444072400c5685560360700d1448110304024030f16550184c82004108402070344602c0c06041c078400d0007020402c0042c00000074003004561220381c60640030103040146200040030000e4000d00c43d00c1c0040300841c0c0508130b8010140b41c01314200c2d204030007003070f00038a032001445000d901074170001c2e00741c2040d000240000714044400340f040b280b0981110001c031 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 759578624 1250 759577374 759577393
    0x906010503100b09010302010f02030f0d1b020d1205070e0901181803051c020f180a09360807110109050604030b040b0a0e0106060e0f010903020919021b 67
    0x14544074110b102005120700b46801c108003950341681d424112502030070690340740030409101303d040d8410b810000c0014180400c103203400701d00580c00b4545800200103560b40344503680d441640e0703a440c039401d03d000150103560040305440c100d822041e00030400b030038080b04180c11500021400e14007600440445089000400f250504900844080c2c401c800328000d1400c0803500d0042052003002002e410303000710b0760a082064032040d8102d03070a890b01c0e2403105807140820061000320b5150720b2030305d03803043c0ba2000c1d01144042842c0f0403500003603048880207415108080700d03407c4c0c00782140f118284010083c08081c02180704c1c10000d0404038803610b0f400740f100450784009081d5000035000700d40940c038248024400126690682900141c008401c00440c0d500c2c0100701c00039020b40b0500340c0640d401c0100c002101500590000040c2c0821070f42040000086c200464800080e48400b81d800035a0f03801007a121000c1c200315025000310194007518000784501e888a8100302402c05541561000c00366 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 759579874 1250 759578624 759578629
    0x606030c010807090e0408040b030118050708060f12011d0304090507090f14030111040b04030605010b0f03221a040519170a1808010915090b0f041a09060105 69
    0x300c10509000d007088200da0501c03040c010b19010305400380006035540c560218040c4a10032081d01c0061100c2905d00c0d90300d684a11482c089040800d4111419504241c0464503240c05110207d22071003018000c010282d0707503007080081060345204200d00f107559038411404204c049100c1030f031510300007070001d5035170b580340c40040d508407000100310341c04001028506201200b0380c00c00744002c8500085d2002c8148013400c1c0040c0c01003003079608403c241e0000090000300e41024070064022280203040410240e070348c902c1d007180c0b01c2c070803100c010240c001c0400000e0301c0c4000304900c00d0000d0880d040039031001c000560302e05090145500e0441e9442e0f402004020400c1070402c620172078080c04072010420400a0355410701018910303d010549401d02140039248280711704d09050b824081064a0341a140d6110f440500030850b00e0002c0d91105101001e48284000c2d500903441c3c400d502c0300d054005a55081750420701020041c0c0104d80f030114440000d58428010020a8010580103002c1c01c12035151108 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 759581124 1250 759579874 759579883
    0x303020c1006030519150507020c0901150306090e03090904230705040501062f1213060f020f0304090c17090706020d0e1c031e05070215040b03070e120d02060603 71
    0x403002c0c00e01c4014415000018910541c54a0666071b03442d000c901078540240590400b000c41500c641c01c001c1c034100002da80c5210b840d60b07041c4083c440d01c04211580d01d82c0780da041595110011250701354402c21281c0690700345140a5a481802102c0d294000e03401c0c0b241201c10540e40103d07601c0c00c3c1c1c1c81100c0501441c9044d03c6454010080c074148900d910054040030010700c440c0d0b041050a102d40c1e400e00c0284078000388000305a8180510503a81e4401d200403242d104940700d4068000080d040211800000d80002904d8016205050046080c2480c0c152500701908451504608003c942c100601020f003510302a14050305415010740510303030404000a1a2000351482c95041102c0345140217400c0c0c13141d4a15540c00f1149030001c5004c0880c1c0e0500f5a2400013106040110000c8a0400c2c0d04d429841406403501c80e1003152180824040e05202c5a0307240114004c04d040000c08001003120360f40a088008401000a02942990f5095007007441c1818141c00c15100580c121200308012444d0910 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 759582374 1250 759581124 759581143
    0x40f0c122f01080a09021c0807060b061c0b190e07020d03060f03034a060301030b06040509420403020a0f06090f0f0302060702280303020c10060305 65
    0x3590410a6580c1d00020f010030400f501003101c00c2ea5400c010019920390002684410300004010000e20f0702e14500ba01c62a48070400582e00e481ca490715260b601d02c2c020080741e09900082d83c1000d445240600c4503401003000f00c2c0146c2e4020110302c052500010001c281030001c1460074500901c07481c1c480c4c400b07820300320f8003e0924100362500c1410b1045040581d0b400003030381d426240c04000c01202c404aa5450f51041080034130b40320340084801e00c84c0c61640c81400559031505d440703042d03610300c050074080700740828007004041d800704a0000d041801d0590040342d0090030042140c4001c10045804000c0042c2c0d00d843d122070109030b0000c287c14801e649401d0458060960074500f2031318182e00c00a484400f030600040610600303412101c2404403e0b044140c9c0c040c0c000302c20040030804c900c0d1010307070300c005410b048001d130080200050200380046520650445188070481e40c3c01000150b88122400a11003101031650910415926000401c00f905101c1441a4005445030450803c58035116141 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 759583624 1250 759582374 759582443
    0x13091704080d0806150c03272b022707050a0905010c0210030b060d050703091703270129041b0504180e0f0d090914040f0c12 55
    0x204140181e42d00d500e904481c1c2d02451105c40f9032a07410483c040c07800c5100e4030700300620f4240821428104889807410300007480d00308541c40c0e842180078042c0d610441c10340041c0300340320003075151255002d41014512401036088103c0d5105c008844064503400b00b5000703548040005e00086042e5203110380145442028190900305290039000325800607100610040300c140c1010b4445621440b40d0f2148001c1d05d80825008105100c07030310300240020010075504009a49000c48444064644910841200c0c09080a00c0c4010081e2140d0038005040180c10102c060381c540d130b91507414010303035050542c1114506010055002d5842e00b8010803050b2180070003040c40e100f040208491069030420121030803900d4520038800a0640e285c1c0d107078010135121504004e24000c2d5000b0064481011030b20f858080059100c002c013131500c0d9000c5508540f20703568241c00f15090f000128010615a1500403500e500c20003d01310038940303e000e4503100108900b022181051380c0f403503a4403c4541a4502c01044686 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 759584874 1250 759583624 759583637
    0x1906052d010c210302090a03030809120930160312090e07030b0d08040806100b0a0903080904020c0114010305100b010906030e100221011406030613091704080d 70
    0x1c035251a40200d040540072440758019080c642e42c50f030300070b4051781c600480080601003004c1d5a418042c00b5450110f402840c0e03402030015010f9103060040684811000240c2400c9003001c01404800510f03a0b032500c10100c071404000720384c01254007000303814000b11444a520f4955807070340c41c00c21055a84107a08806004a00109024001e401003503140c6c401b24925022030700010000114071f0154210703070044c14404001170041100000010143d0281ca00d402e09000802c0d07448035440524002c0c8040d01001030914142040480c038124050030b4000f100400052402180c0000242107070043c284402c1c1110010780100144401032201d080851107428060041d140c4040c0005d081584901429040c182c0c2c80707410400e0345100300309091208865080071951680c1e000315660801450080c5211106d110074000b1424034008000000d90380b002406603800c50300d03010304002442d0041c80400c01460740d110408400320301650301305243c1d030040791030345a0b5440c2003c000c50305060b42c1c03542080a000b032 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 759586124 1250 759584874 759584897
    0xf1c1104050717041b0b0901080603070311130f06060c140109020d02150705010609020301150201060305070e130f1505010518041202030f030a060e01080a0b1906052d01 74
    0x412400004a40322070a24082199886140c6010641702c035000042503500c003200045900400d8070000c00e04040262a482c1c1e00d551203400701681c503c0c041c00010080b04035205c840125050002008060401303c00b804900050012540710813940d55034411800034000400078402d101440300004550170b8510000c0c042d555080e000300710f0101402500a02a0748071200072807220aa040549490341d5020000b03200440e030707c0070488040d410a004043e0030103c1c204800c040c0c14014890003085030303030100c0500840c40c541900f000030fa9030000c0030301c84a81542508400002c403950b00302d1117034620504009100701310284000c0304440b0140c02041c080d4100050340d241301032843e08207503407107035005514048980482108905500603903d6680500380c000c01448500c0c4100d4000b00300ba01d02407a8404910f80e80c0c0d0030026603c0007045405000d900c040f201080120016041d420951489071402203080c0359100b0210300303080180840004030351421000340ca59520320001d0001ba917002440c0c00c80304c108 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 759587374 1250 759586124 759586127
    0x110c07030201051b0a1101020c01030c1b0c0b0a120f1e09021306030c170c0a090207061b08090d020606010210020d09050708150a0c05040b090f1c11040507 68
    0x1200e00010341800404200d0040c40b98038542142c10030356a590513507211650515281d548404071003c05030250181d03c003000310b035500c28440e01c00d0035089039036000c07003011300d4101810b0540200d4005440c90541030001290070b812250052015000652310400d4100c08101d00c1000c494002d4030080c2103c3c2020040e40000701030b500c2e5907412080c4c4070400240360100f0310000d50546840d0314101c0050f810800700000344860759200c1c4003100d80e050031045500f2280c10355a40c440b41a0040d4a80c0700d100f815042c00900c40300c0e4007070841035104200000c0c1d44a0541d10740706214107550b0b407030b5000480b0700f001c024a6000c2444108000c2c0040d00082605007000400030307484040f00000800e0003a8041200346500c692600020b2403103420000b50790180707407600549500c0e800a100d42d44030450160f80030503540503051282c0e01c851002d95071272500702410311a808030341d503029a41d0707550b0010f1400001c0284d0381c0c1d9140d8502d645d0001c038400c41c0100c6c100c0d00e001c0c1d011002146009101e0b80c9044100b0000c81d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 759588624 1250 759587374 759587383
    0x30108012708160605091f02090a031502040e0c0301141509060d060e010303111b030c0d05011d0d030b04021305120a14060708010b2a030d0e0d03110c 66
    0x2582c8255001d4030f0740f001030144a41880c50540203808a814481030140b25a404100c50080046c1d50444640c2d85010180c0fa000360f12034160301c5600302a4056040001c03d0020410b5000d072881e001016291540d04d0070325040c4404180c903a540c4075140000100034040c014484500945026a020362070101000700343c41803030140c0343d00c85002d039000141f0300c0c1c511f9a560340000d000d0120700514402550311703800d0040200c02c1c80d0780b400300584035603800c05002041114084092590003030050060340150001c0c08014006840c089402d5922088400329104900000d009211403060041504038140000181580c2201805a00442c41040410000c10322007036400c0940701d090351052801c5034800a0649005113150b406060708100b01d100008210f80812a030b0b0007041d203039440341c2d8140d881e56992103c0f03224001f02c1e583d203030340a070010307102c40031466400d15540e06030b82d070a40b41032084413520700e000d80b9084004c0c52010b400a945562046070140729000c00350450604103030521030642c0e1503a548 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 759589874 1250 759588624 759588701
    0x60806031519090f050a0209130f0f020f1e10031103040206130e010f0e0106030e030d0c020f030a09030b07020619270b09010b191a0702060307020303010801 69
    0x50140d80d65030a034044220340040901e5540700c800001040010b00340740b46c80340d0b180b6804a100300741c0480810041007200e084034150381d801000a07501c0030025901d41d4207800720220100d800101e46030085425984100c2007900fa0403030000c210303000036003140c1044240d100600b01c003024145801c2000d0840324040b01500e9200303a05681e82c9d59180250302c18100900c205501602a0281035030010414500c140c00ba80f080f91b90003907102c04140d80b100402d40580790104440700881c0c1c82881695041c0c2c015801c00c003481c1c030b03150043c0c545103184034075068296408408a0b07000305000c82c1c1c08008000110b03e07a941e00c541c00348007409281c10304203006800003c0903550400d41d141c540111942c030590b4811409aa00d030095800000b1411506d8401780c0c1d101d00301c8415000e5480c160f04840359040c500368600328840d1821340001142d081c00e800e82080f44407880301d504060002c0c0f00c5100141c5890000314000e42d100d400442e200d62420f21805e082d580c040f2840c00b41c010115809403621045030250120 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 759591124 1250 759589874 759589891
    0x6030e0c120a0311030f0c070305010b1503040206070204060510020109050606040b011b06060807090c110d210609020325091511010e0d0f0f050909010302010309080f0406090608060315 81
    0xc80e003006004132031842c081c04081c041c00c600001401d84a0302d000156050440707200f64000d01a0403a01000c00000640484c09204001e1041001400500d09140101a514030081000882c1c544840101d03403140e0b00107500c000540c1d03449244c039041c480300b00318032a480300302154148051070110000030320506030b0301c2200d00c4252100c0d450300200b0025070000781c017030300e51102121503c7d644d60104501034100c0b0480d860102c0d240403076001100b00b012403908a8800743e511600c0c24031918a00004000035690380325000142d0324a030110340e03103a0310b00080d4001d0344000400c0600b002c13070190703d90842c01400d01311411b00800c10170130407050740c03401419400c0010030b0812441078021492180c1c050300413100c0c030040c2401441406c62005400c10743c0038040b030003140e0741d030000302e0729105060b00c1500c03802010030b900180c55001000190f20a42000324501d1044035013a08040075900c95140070b4006800c03031408180224824440d95500c440c4c0c0d90382c08001100201a2120164400b41140202505006 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 759592374 1250 759591124 759591137
    0xe0705060a051e130e090607050c07262e020313150c0905010c02150c030f0c0604030305220204091b0f05270106031a0a06030e0c120a03 60
    0x74a0500501c00c2e5403c5010100d8030052100101590403015804264201e2005420900201e451030100c1000c92007209036000078645a05ca0190540d03003600701940c44685031091a402244000e030442c86003243e800d90211240480507010b0b106800c00c498070b012600e100c405078000104a105050304030100c0d1110000050b60f0340c440760118684440c001d04080d018900b031248910480c80b055029000c040c0e42c070380d6102840c64070350004450707007010498042d500c41040028184a0102c0d84000d0030181d000008492400042e080c1c402d8080d00b0601140009400c03880030042490340601856030f02001081e0b81202d2915140342c80d02ea40d500c110006806a40d413080d8403001c104038110b40c0344462110300d4100007190342d1400300540000041c0250f0340128008100c05e03818114a1094101e50700c4450441640d076030030040d0440040c281e44024004800444069240c0c40c1c40d050f52641c0070381540d50300482c801c1040c5038807901d4400f8255801d8002e241c0301c02034018521000c610303c01c06030b6061500d035 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 759593624 1250 759592374 759592387
    0x312020702060c030a11070b09060310050a06090608090115030f03440105090f090a081605010b0a0b04060e0415080a05060f01061706041401081f0e070506 68
    0x40240140d8000942024000074200b41c410340001c081e118a40c03040e5a00d805801582080b11303120503a600c5030041e014014048070403c0d16100000c1c5038031002400c038001d0042c0d81c1e80000f0b4110b14441e8000400300e003400300c05008140d4030545541c2c0c0a10240c1c02804405010149c080c4444a00d01c401f41150007120005010140700d54407540041c1e1079442c58030001c4a03502c0c47c841100507544800d1810110801030348180d425001d01460403035100034401c031941e94801d1207414000388020400205070103052640d90004081501411145c003004003214800c102e6850720508481510300c3c981c1c400e0102c80310070801038420a0484d820b40307007070b07140070503072070310316001240c0a0189400300b5417910000320300c041600800040c1903a07000e40070b101165100c2c1c41d881080ea00fa01401e0080c0c100042514908945070710b01e9403900c0b0340040016100144020b907a400802e5140c200381c00054460300310905142d0341000034010040d0843d02c046040007030b00000c40d011503441c82d49206048c002c11001c20361 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 759594874 1250 759593624 759593657
    0xe07090f14060f0903070609090b0301090209040b25051b06190b0f0402030c070309240e1206150405010602010c080f07050405060301060806010212030103110d0c080f1b091303 77
    0x780c4800100c054102c4111135147c050240c180f0070b09000306000c0c1c80c9400440a805c1c9414040e00c40d615070094080d074107549903a1606400c920009252450300034400135020700301d4101d5074401c1c5e02c2e10442c0d9202516512400c0010240e0070810241c01034540c401002c0c401810380c0c51108510200d11602c0000d070120420011407a40c0240c90240c5da070240c070202c204024000c080d00240701d054441c1e0756500c0e1f03140d00c49240003100701000048401c02c01824888540751802035801c88450107000b40040080171924101500c0c05008680314000e40314510900c0f184e90500740036072405403039580000d110580c074480d802041000010581100f103000c09012611140c042c02c21200a4100507161594075030b11444040d00084080d52814018400d01c2014000301b05c0c0181981d05807540245c45041ea080c00c54104000c01703028078010390f004160800001091441049030202c1c40b11410041c0c90a10300e00c0e41d640564010760031507140607051403020000c41124010255400a41c5420b2031a440b6100001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 759596124 1250 759594874 759594877
    0x9130303060504020d0902190f1203020c040f0b0117070203120a090c0617010f0b070b07210c020f0105220f050601030c030212010c080a020c0a05070e07090f14060f 72
    0x8150400e1001501c10083e545c280c02c0325200500070f4400784201071403641c041708081a94400c400054048010030b0151401c1140190710013406807040740c01130b44503d80090100c500e06000c001e010341c0e03144803a4085503001141070b0404240c94601c048540742081020f51070303210b9005001d00c40e10b1700c0000121080e03440d82c05101d640e03420124901c00181c503080080c1c0b081104d603507031030303980d2604600004402d041d0400e15000d50398004901d0742400000e55a2016256014010a060040d0010607540c1c00301c107034140105220003000080341c003808881020b420017010181c81c05499040904000c0d10402c100d10301843c2c06115040100d0000c8181001b150b0112040c000a01d1400b90a00010178030003442c2543c402c8d40c0c0220741e4100a0b900f111021401ca80d588607024011800040000d82d000e441395000d000281d074104150346120140b55105400d1808503044500d050881a042c454802d60000c01b14001c0e25640750ba05003c03d00307010b80c01d01c524103d07107030b80d034494071300090804002c071103000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 759597374 1250 759596124 759596129
    0x30c060a030e10090308010b040807050609010338031c0f0c06020a030f1d1c05070606030507081515090a060e0a05010314031611120a060225020913030306 68
    0x14182d40f1140c58803100240503215504003a00000c880c18004554900c004c021038049031740910080c0744803441c0c1410310130103400400503581410341d1460300380401c9081020028540d00d41e4805d0380803565603450300302d0400c904041003900981c031840101c3e0383c0c409089003403503107004141003400603a42918011986480040002007440340007240c15041039425420201d81e103c0c4100d401e11500d207054241084d403c12405641d040c540c4018085c550440d215100400100064035200f46080311035207880040d20b0b1140d00484450b0b0080c041000107803000d0101c0d841c502080c102900a5003000b942481001004184552140d401030700454042c14855016000420040c20600aa8503041d42c5260082c00240300c19a00d02003040c1c0008910301000c011240240000700030700c000e5500079190301d231001010442e07164002840f01c03100805900300708950540c841c07207180b015075203041004900e240c041c0c59803d0903002d101e003d250784005070382d4000c01d04d034000d9200b944071300822054241200a000c050f03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 759598624 1250 759597374 759597401
    0x180603060a080f060402041a012106050303040b032e060e060706050a050603150c040905040203012a111603060f14191d0601030210050702030105130b1302030c060a03 73
    0x3044010030310f68010856500c11402200d08003d00c40f5081c1401c5441c14460034882e000402020f01c10b034880c880c42445100300d0108100005007207840340d000c217207150310a82103106001c4011003009000300700d03040c8a60020140a20a2200d409103812681a15000e07001d23042c01d12a020300c0c004c0182c0c42c0c0600790750516400000501c000e06107180d084006003030545043d0b0090188000d100c0c241c0c000c40b849907010b61000c0010600e0130346800903010003080c010f0000ca17803554840b141d0581c0624011845841070b003254a04504901000c00e001d0703c2c8800e65000b002180e042020300200081c900d500f8202180d802410110b4a01107500c8260010000111040316100081d011301281e45406000c40030b05504500302080a0f122181202d1401d03260884010740a0784080010701c014101104000d0700f49003242010b0782010443d50009080d00c1080f0b8580c006440804101010301c2130186483e44c11040301c0040c00c410b4291900801d4648803d00c1d55a8060040001c60803451803007a4850725032803000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 759599874 1250 759598624 759598633
    0x13090e031c0908030c04050f0d03050316050c0105011e060315050d0311010614031501050906190f12061802091b0c030412050c090c0a0c031103160b0705180603060a08 73
    0x341c140405a0b0011f00425028003621810303040c00782818003140d2070a40e05511a0360866440c0f801e070300c06450091320000100b05051042c8220b0074001d000d414040c0080d03200c0e5290b2400304072a908003080c03440c0e205400301402d16040001480c00d002c1804d040d100d00b0f580c242480c4109081c10f40d4045c6001c41c1c0c070a500c0d0701c0d0800c0021002051047c0ea0034001c0c045007036614654110908500c0b141d028040d0503030203200c49000c00d03018500f00440354004c0f2808100d806c070703203507840308008585100fa03444134000303249860203001044114403941c29010741070840180c520301c0c0d503008108000380052000749008003451401d03040220450541e00281500e03002c5070f07911038507060501d840c0460b200d41161148030300340191000d0300d403009405201c1c5136030081c02418a4401c1c0000c45440603100740660511900e810008803100060006003488103102d0560f005c142c1c40340c5405406240028050010040140304c0440720200b028928401064202c0b001500c03030b00c40c14000303400c015160f4000a9540304 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 759601124 1250 759599874 759599881
    0x7030b100806092d0402040b060a0207140607031b05010b100e09090a020d0308101211030d05030910090206121806070f0c08030405071a13090e031c090803 68
    0x80c00203400c2c0c072070b1a080d0b80040e0640c8400c280540e06050102c100000490a45061900b40e0140012194040c2c001400851855000c40129080d584a0388107440180c04c9242e0511003210120282004141e0070b440c0c03545003a840d03403402000c101480484042c0090b9203c5100140a42500003120041d4010708500d90781c00800c8003d000e026401000500418081001581101c00842c0c6560001e401610712002d5246603581120040c400602c0540b0103000d4442c04692144541c900260b11482800c2040c6400000c40c200340c504481c030541c5c602000380400420090034008514040d00058600000ca5421841d20002e1810f0142d0301c4000070310b5040d8400c0215074405840e40f0004040003d060b12040c1d1902d441c11a080c1420040000c0850141c02e85600021440c0b4003c40c0e0150143c8252200c16407903524040400b0008160245a175038046004030b0b10981ea00c03ea24010b02320418108000c0203001203158a82c090359a0003d401000c5030314400c0901c0081d0071940500c0e5201030103507624035 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 759602374 1250 759601124 759601127
    0x108100e0114040e0c03190602070c0e040b0f071d030a0503220e060612061807050c010b030a050a030c051204080102042c0109050c0705100603170f1207030b10 70
    0x5154162030f0b110354144800d00c03c8886020418100494015018003a03901000075424140c400900040320b0711a401c0251074081a0860034900190604114450882c01c21f42888071000f007004e400c595813002010140403035103400044818078466046032102c090410140000c0c1803088144014065000000b9601c50100d44400709803c42c4080d12401184c0755215070380002041801c40d401500000708010103080340380c500714141e90151009164a1200025442c142800401510001c0c0401d00100703008841c84400c2c02010004041034004240144060300c0e070595510b0018006414401100032140a12800303101e102011f03035100d501326985076520304950b8002d500030b206800c0403400042141c0c404030b11942c030840341240500c110500c0c3e81d00b48480600145006003485105407010000c00000400500032290005400880000c1013403441c24400c65114030500c14084100d001c00c00340c42003000d07640c1510003580c200715600f40f081d0749400b4160001c01e41c00c1d0845074444040c001701c000c04d5 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 759603624 1250 759602374 759602399
    0x51902031003170c07050f120a030305180c030705060c030903150406050f06030a060b01211409030f160c2d05010f050403020625050a17070305090108100e01 69
    0x5910510480f079081a03002c0440c1054001d000e1940016000100308108514159100f1011000001e00000080c107185000600e0281c1c00202180031071340b10010004078070104000304002840e507002408211018000103511500a8000c02d0f201e84004100440c028400304141d410882010301210390400c40030100c40b40e5150708803021a410742c00d20000910101e02d25945901402001c1c0007050b480c0c2c06a61904043c1c800300002604001c41110482d0300220061a1210000044840000d4206011070040692403000f85801d6180d8030030800914030385040c8040340da2640344581250401080c52400d280002c490b98403484232001c420009060002c1802407404540701c0002a03644003507662001941c2400340c034080c1e0700115100348001c001605108008044000d00e00c0158440d625100300a401030b0302d8030701300c265510303071244a80108000c090351a881517004071114050030410340740c2d00144148144132106040106180100d80e100340076031038a001510411900b800d803584c43c1c02080502 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 759604874 1250 759603624 759603629
    0x1406070b1f0806010311040912080a09080313020a0906080d050c0705130c03050906070e040e030c0d02160807270b120d031d0d1808100c0807170a0519020310 69
    0x286c512056150158034140c444c805c7c0e119402400e2000c0c0c02c040410036a24500001c1c04803c4d815102c20034100000d40300001188241280443c220b031520301e90040c0040055641c1140c0400c0303150850500c04007000080c83ca8006c5418a001669900500441410803099500458000110b6200302c004140d168010620262032960200116030740c1c2c044140c0c1da0b810685021000c101404090a51810070350031960b100d490f0744041b07138544801c65158502e8a03110020a1006801440510050300c4480306911b0042036548000c22541c0e007004d082000c5034402242001c6190356026031245035070341d16000307440d8800c0e00400034151002804400d503118a00a5840c40001c4e143c01006c856902103c2c145161208902004205260040000751103071011100722080802d00240c00040025042100d00d20000501101180d50003940a01400ca5030028142c0401d20008544840340507140d0b28607241d01c451881804150340d01c619078110018100302401e00400d034000010441802d80c2914031408 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 759606124 1250 759604874 759604883
    0x302030714030304023015060a0605030c030613060503010515040b1c0f141009060506060f0a143a0e060a0e0330011406070b1f08060103 60
    0x10007a0034400341038592100b218001c0d4000c002104a0303402c0109901a6003482401d15103081b8148078001c141850268040e103001004215070082240b01e08003070803100c0c024072007403c02074158205205d007400f4900000304414041c07170780c00c81a10104c080300d400005c0102005402040a070a01001c5032204034501080d80f03010302e08000b240059410040ca07400700070a41a0280c03016400242d07180801e00b082804240e44c0200c1c0069003080001c0180964400c9540246c80001c4c40c0d42e4915049082d10402001e041c8140e40600080200300e40d081c0c2129400c01941c6803240d03114102c18007280990188850303180000e401002c81c945510a0300d40741d0f0100200d0350392541822840402c5110030358081c1f903a800003540000d008a0382081054000c014030100b400305490500c0300c13030b01c456150a407809420b81c12542010b5000101c00030303d00750040c0035010546070108054001300c041603540c800c00c0ca00404100200c40041c0080100f4050034001260040c042e0340318a507160160f5548000a000c140c9 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 759607374 1250 759606124 759606143
    0x3182d19080d021513080c07150807080603070303050301031211010606030603022b140f030307030f20041406040801020c030c0709180803040f060924020f0f070807060903020307 78
    0x220b9070800f1215903813203081669510034000310039944131b914617000241d003400c003481600e0000c1000101140302281d13003441e6603554810b91070051002409200040c20660003508058018030119501004a038152608103440480c030810500c4125800780044404410035448d014010580d2981600074104690084030440311241e0000c00200f98039200d051004810030021080c3c1d80040e402d07498069032851440140c070010001100c6603404c560084844000291f13403000c140704101014450782d0745a91382c0400600041641c25481000c42c4243e008101c6180542c0405a0069070b95030f04540140080e84000e5481d40894551240d6a802281c0c1d203041500441501044002540c0301e941e410250000000d98803071103985540065a202070710580707507840e881c407c090204265000390b515562050b00c6800c40e2048200c1042d083d120700c190083c500600410051051000000c01d503148100320445040c1d55411a2130080e2081c03107080ca00900300703410200e41405054010010b805520f02610101 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 759608624 1250 759607374 759607393
    0xe060d11040f060503160f180909150b090609060a050312040914070509130f05040b0711030a020c040c0e0d03030e0c0411160213020c03182d19080d02 66
    0x1390b9180c0002c480d40388134a10107050901070b05101c0ca0603180c100303500d41440204080f080e4504207007441c0d60340001c00041d0f00c0306922810015001ca461249504c250410080d2030641c5e00001c0381d050010f40312611802005010443d1903480e91491001401d004046a6100040c440210b00380d030803500c40e03000124500012920716041c0041203611030505075680c24502040340007000340c842080443c502d200355a81e14210802075180c03059030f0003503004150244451404035030080020085151040640e001071000545950f000556200010011200401c01e8050420121b811280c440d8000d940b10088649200a158050b40480711414488059450001c040030038801a2240c0c4040c039040903000b040180304a0350910b00e64025284020301c01f0800d0411403040300240d03040310100c0342c0300d0b420002c2c18440241040c01c01440f0f00c401540d5a590100031424601d000c1c812078942c0b2a00000c42d07104142e05550780d102250a4507070000c004075000b84d15210940c0e9210000c829003009485081c242 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 759609874 1250 759608624 759608627
    0x80609070f1d0a0b1018090b220f050c0406180501080403030c02070f080d0914150a0e062803091211030906030c0a090b0f0301060e060d11040f06 64
    0x707620070754900b60030102d40d0350840b80501c14a04401400c1004480d036984011003180e8600107540050410383c0d441d045001d0740d0300d60401c5961100c0d8000110303d864081c2c6009141c6a040201c5120300d04070007403d401180f45c050300742c00b50801c0503910002c2d501e4074040040b103540040c040c006507002a9200507221b5814025002c080302d00340209408145400c0004000074801e0b08003805080c1d840c811340341407903540d1001c00400e8800703800c011072a8100c507070003100060b40314034103000602e502c2800154100395980400c010602e4403458105100c80010000350b0340f40240c4440c8151240903081a6948401d40311569044c0406085d0150803151103012581840c440e01490548a030850068002c0b01c0c90340c00d0075980312101400c200480e02091200070308a0785c030311b0050740c891130805844c0d0fa41d58209090040207420729030825601540b0a0100001c5c103139100b400e507815190141031082600c0c1811001540f94010b501c601240380342001d0400b401c40d000000a441220000c168404005454000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 759611124 1250 759609874 759609899
    0xc01120c021f2a021c020c1206090c0607020607060b03070e04230c0102071e080a060b0a1d070507020604120c0320010e060304021809030306010207060302121f080708060907 76
    0x180e040180c0c000707405d050041c00282d0f072410784203040e801165044015100814000c821000140d40c4603001031003009400c1c3c5044c420600d4000d01250a01e24001da26400a80c4034022010040d00c050784e03410304d0143c10f80b000c0100c1406001c1a02d0750207024903080c68840c145a00c45000000159256010b0400c906000100e0030f5499205801410700d850824244541e192a9001034004202520704002820325003403140111b0a40522030100b20303803400105000c220720103071b40080045215083c3d4507041c2801b80c1c041c0360b046106850141d80d2180c80340009012030040350088402d00d444c480b214000c00c002c0c030141c202101d04c034104602014040103540c50035212960b81c181e000c40c200e920400e69524040c80150b500500c0140000c64024000352011008842110740e05a568800000c0c46003030341e0100070341300041c0031500d4254035001802c000031058940c0a4400740c419003e1070583d84262a2100301034000e48061811a0b03007055880d030a42c3e6944600f59000b00040c001c0313010109055130b40c0031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 759612374 1250 759611124 759611201
    0xb07060b0f0612041104021e0403060608060f0a05100b0d0e0d0503060f06030901090503030f070216141207080d05130b0702030601030807031206060503180c01120c021f 74
    0x2501c60f10550b0b180d40b501c440103c56507042e250301a5003041280b0280703040142d0840f080c00480d00c01902c4908520384201280c031184c0140d40c05521200410005c1c0f0344061a403a0b02960000300401c0e15150800c803500c0012160704200142c5c4004252040030240a6103c00004405081152003036041e099080e24184001d540c165041480711030004001d0922400440c0c00000d114000940c00596844203070a50300290354283d1036403008424005c485504103c90081a10200d17a90306000d482c10141100d503e030603070012030142c0c0a083c0307030110101003442900d000b0b00000042e500c2441009a0040c150303480488a19419841207030041100708040054400c0780c0d6000e4003c04050b4215202c3c05440d401c40c4804034100a0300726802c0d11082110700075800200080d8441a40768141595407201a03412000c0031404c0e0b80c4905449880f50b030380b0054414520303a540c040000c2403081910b089003002c0111000d401e2044004003030807020f01039903100c10504a245201c61101104400840201c064280c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 759613624 1250 759612374 759612397
    0xd0f0f05070b0f1207030c1b020f060705010b091e0a090f02030a030e01120e031608070501020c1b03150c0a030f1b030e0d14090604080d0305041103010e150c040b07060b0f06 76
    0x4003041003d5070a46123035400c0c078600082034582c1400f200000100581e00400e0100c41b40d035103561204280381008209940c0103003000c05100340c00c0501940706d8031511740c0100f04038956511008903a040c4181d4030040400cc50700a000c3d00c01110f01d60a0280c202c01d50102030500080300301100a07140102446081402580c04001c0c614152005456001483d0400400c0d68079620410a490000b0401d10007406440d8640014001120300007001c20715aa070410a0603009070404039190303041c200c0d401d50311340d44455409404c41c4ca0ba130694804038020721503030010800152030250b038031881c0f040d17401980d070001c0c405550070b01c4440032103c0d281d43c40d0303400392091341c0125003401610285c4041c188050040224050542c6040c1035480d00442c0c602500c0c403000d580420b94440030302042c030490b40300840c03100800740c0c0248408510fa2900039a035042041048100d0702d054000704003005880700445004060580101740c64949906110009029005e610b510840300581d144407107051070000e895609520f03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 759614874 1250 759613624 759613637
    0x9050706020f3906040f0801110c03190e0d050109051e100b04150b030f0a151e0312110d0206061005090d0804060c050601050d0f0f05070b0f1207030c 66
    0x1c03020b50040c044003000c2d11403050220000c1460f02900c62030050300080101d40c600b0038015113403c1d451421a0f42c415201082d00408201811907058000100c2e0b2500495241040d04d0044140c01200d0510b01606e18580c03141c1184201e41c14054150050813915018509039210304d801000d0b42e0a000d202c0100b1400d042d00076800c66072140000b648000200d54020f880440c0d1410303102590300c070260a58100a60306d203404010f000902030600d4003254400a410340405c0344c08082004560030f07008521401612200c40c9030400d00b0404003c014030000d42d4408418201d40e8a00c03d0007401e40300003004c03034506e1703849401030b86912148001403e42c0108405000c04400e0000c0075011202ea60007901030310b401011804509001030306000091005004540c0d42e00011185803610508101040c0d21031449040030042020102e405250440d64141e0311035912064a0064949181001e140e5400300c005c0341e80206100e03d0180e04440101400124845d0454155452005c142c00300d62581002400042d80b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 759616124 1250 759614874 759614923
    0x312180703120905031e1b0307090c090e090f0d260c070507260307020a090e0709021206010f02010c020a0602180904060902190608040b0402010e0409050706020f 71
    0x9030a03400e400100d9082c6040d142070f58440300802c0c07521600c14003070701000b00301c410054032140091250031903009440ca0444056855200029506d003a14042c8900c0a5600c3c01d2401000b4081e01416000308000b2000650300e184c40f005103615040c440c01440c3c094007a0040d00b8070024410701911180c0186500c3d00c588400303524003c8002614010400c4243e0f450802401d0042141007000b540108200c0c642031006800b1a03280250350260101040c5c83d583c003d04c410001030f62402c00032419658090000911040e030300803400e141132560f40c45480424030024004801d1181507080724403500c400c2c0c03a00400180024012402c855907901c03603c00680194421071b001405c1d94004120300c007282400701e48150920030005100c040181c8085400550351482c540440c1040108408000005041110894075044006e040304100078001451031507041d00142c1168061700794401d140c100908200700010079850200d40d40d02da83c0c02110702600c02c81c1c1558031250030004001142c21418002ca020301c05 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 759617374 1250 759616124 759616133
    0x9050a0b1503040b0a091a010611030f0336010507180311090403030b0a08101b27030f0308040b06040209012703021807081023040603020603090312180703 68
    0x13801a041c482e446481d455144049010b4403210304414140c4101031519501d00341010b000007107020501c4d5050341003400803001b1003103c0300540394080d040c81c01c141c80300381c10004002e944140e095041d101c1c1c1030042511012806056101d075104075550344403140c05200409580d001d03804144001005041084d48c000383c0e5042080a240d003142c442e0401240c4130309424002980400e864008500907072051010701d0f5409050701407800c5006504001402c86404030384002c200620400c801d04001c420140d0762401c000860710020001c40d00091a012145010f04e002026204107a4082d03800c12070300c002103080f51806101302d0b405440c0586941c40c8c0080e04050556200304004a03111207812020800009622226004007241b1000196121549040c1a02602c3c1c080081e1440702050139282c82446102940511518403a211700d001d81d20410f85040001c3c090030113600001d4124a0200c107020a4020000c0506611b8000c3c000c00512035035030880003110003c115005902941c0040001c00124 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 759618624 1250 759617374 759617393
    0x5070210120f020c0109020102100203060a060c0f080d020306012706140c06040602031f0302130207060b0a08010209010908160302060319230f10030314070c09050a0b150304 76
    0x2180c140004182c00c0c00014500c0300301d070402c1806069594403100d00c0c0c000c6680c1407103594062080440114150705240011a0090946000b00c9007403111444900e07091011554889400c1980240101c0c0d84079000c0341580043d4109841c21408501c0703244010250810740e4541030a0304000b1009610032038030f00101120101100c1c410400c0d081801c0100448001051008a00c168003d00c005a80c1e403d09125032001020509805d06688103d4030042c001652843c83c030706a6a51000380150720780c4044d007000c0004203140c810300d940c00008900001800c15040d000303024040002d88450b107034543e031f9542c1c0743c0e101e0440620f507208480c1d100c0c00a02c01480d104d0003850f007041104513415100c84074906980111500302d80c1c00342000c1c0c042c7c00408046140019510744c0041690150442400c04100342c500c0c9a1041c04020144520040d056000003035210969204a4201044c41c1e00c282d40c0b207612400601003580c0545c01c05041c603421074554148803000e20340600c2e400e0360312031030b541e03440d202c55189 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 759619874 1250 759618624 759618647
    0xc1d06011209080c03040e01050d0f12030e0615190b03041515140f040b03060a09020118030623040201050703050304170d0509010b0306130f0212062505070210 70
    0x8542d0700d0150101145120300900340c82d00c100402107075114104a2078005000d4164882c510400b042c04060300000c84c2c0a41758410740754450070b00c2040034003551055014043c04201001c5510400d13042084414a0f0216800301e10006d44e4640001c400c2c00d410324400e91514080c061007010200f01140016002c18499143c5406040001810074001d802429044c540359010100d69016032042c001d440c1703400ca0450b04a00001c039010080c0482d0003010a481d480300420040100e980d80c01d0300429a4007850071028020182d00710301000075220f280a03001000c40c05800c07180b922925445405520511030b040e8003a5070142c4800d400d01c821694200e0710317580000e108179003084900703508a1005011002034107640400d00004140e500d00f40300d1041c00c440c10041c110b4800c1d4410342c1440505800f0382003401030b45800010009038604140045103000c40c40744520760451003070b0420010242e41c0403802044c00c1c0110f00041d004021600030854081c0540100a9131022450450710980f42c086d410349001c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 759621124 1250 759619874 759619907
    0x80c120102130e150405070f0302160b0117010608190f150f0207050c010206040804092d09031b02091909052b1b0303110d060306090c1d0601 62
    0x900072281c0c0c148402c0619a5101012008400f01031003644442d00c504000e8564041d0f8042040e49440b000090083c603080c2c04040c1415070003e07102c080d5514180800409581110100100d561342e455000d0507518641801c4503a54688a404100b069004c18401e01a5841140c104080400ba495030f42c80561350820485101c50804203c101d043c1013801000f89114048400580300c1c02c440c01c01904140ba10042d40d411900301c0b10811000405400030f0f1016115050790002e04d8154101c81ea8135802900b201c00c2c1c0658040300c25004c3c1e4400311341c01001c60544640d8840000149442c0001d0300400f90300c000940c0102214002180d11050410070380b40c0f00f03035854021580c1c0040381c54041c100408450030100d90304003800106400e25035042c41c14404001d504e489401d4a0700741092a1442150301030040406d51144403046121501c0000d40e0300411100c1d81c00c104286c1c0da031030075100070300016604540f40c12118400044000c90b000340310000001494007140141e552034011580304916801002c0b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 759622374 1250 759621124 759621127
    0xa0b2d011824090b1309120305071112090105070512130b071e020f060c070e0c070510050402221a040911150d1401050a05150f030c0f070f0318080c120102 68
    0x78a5130050040306d41c05034400071a80c41e01d494000341a200c00501d9103040c804c60030f648040307126001600b0602c02004106503600e90a0810040303031984503000d0301805510440000d508080c41180c003e1005281134074032607040d15a969a00740c0107002d1188050308908001d14114a0482caa0407900803042c801440310403904070031000200c00344c115603400300096209020904c00c10300c042e248541c00c40d110503809030074101d641e81c8503036944110b040030762800b64858000c2070440d210f0400901c0400c01400000300d44071620507110008113074184092007095040040f01c0381504040c0b24882d100341c1c2202d040c074001c541800500941001c07814195456003420001034981400342c1c0b0504e56070310070340f00145086515010410204840301d40141d40308400b2102802c10400c40b200403151080140d410454580d540c00c1510f4101d1701448160340d201100004892003007081d0f5a4110074030354400c1c0c45002e82d400113906a0000aa428061000c0c903510081010310540340cc503003400c144125000025 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 759623624 1250 759622374 759622399
    0xc03020303131e0b15151e04170312010506091c030207080115060305061512090307120509040f0b030706142203030906020a0b2d011824090b 62
    0x524601e03103d03580a40d00409850140302044502240810404600b1140c052480d40b4510360000684036139031004483d840d0b400398280031481010300b40c2d0014002903202100340c545e840102512a4001520260081c1000002042c286814400e40d0084940a00003202c0c2c500718074074541ca94090f00c1d070160190720441400290a2000740643e02900300c4148052040f5490100d0140c29580c010304110701c1541000b51281004406409860031440605030141c071680b46e040445083d4410070301c01900850750703041d20010240d00300f0014500161706643c00c000244150140c2d2040765189020315906411405003001082d04c101c00c1c07120405003910803246490203100504035a43c03030710f2900703118032030440a0810a15400402100c003c01a42c00a0420a500e56035841c80350078006008403450707040e55100080c046072004400d0724400d0005030194043d40c50302ca401180d200f0f40c600180c040750514443c0d4041c0c5e0036060400000b810691450507403103040032000c3d0301070201000362942203c00c50300c10 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 759624874 1250 759623624 759623663
    0x6110d140c0a0f08040524090f0d0b0f190228170103050706170408071211010507020114090f0303011809050d080702100c0f0c060e01020a021c0c0302030313 69
    0xf0420040d204440080d0b4461410003845610080d2034000e00d4001034440d040034000c100340003154070b080811103000e8141440c5200141048250030070103450668138104004040120026040c01070000d9a88000c40d0281110460140c0c480c1540344c0d110319103884450458590a02d068581066043c00e01014106020350300c0100090f00340d0003558242e0103047c0030003c4980101d10380c1101c030a5a548022146059280d103a202d104045009020416004041c07808520a10410900270241c00080c0558104510028003900407101240002d050761000314a211500054060204000c0030145040d80c0c68441d01000741c051302c54900440d11b85442044001480a104a842490498032070300032900341714034003d00e00383d800961140708034a00110404e03292b81200c41da010158032460070382c1c000c241c6803401801514190399041802d60003c1072200090780c010030302c8080100480c01e0a80030304810701e000c444e03015100c0001b4000d41c2040010452620035000c1d20040d040c0612144141f0302c440442 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 759626124 1250 759624874 759624893
    0x50a0f03020c0d0c060c05030714070501020d0c170c0c0d03020903010b03070609091419050901090524090307030807081003120906030b1207061d120706110d140c0a 72
    0x4000a00600d01d40f034101719151040d50100d40007490050305501c0e00a1000e44103070fa040f6400f02c20b19001007a000b082181c2501111309000c02041c003030100d0182c009010349088040c0c109a500c01c910000000e0704180700700300b0b45410420305002055084200401039000b0750140d24000d801d5503d41e6130040b0030b52401c0203410024616642c9946921789411098401c0b98a01607116409401100900182c140384881030112085400c0000072035844500486004000360f000c01403190240ca070f105a02c400c02280c008002005054540340036a07124a101078492203111030017400702ea65200490105032040c1c42a0390701050044031242120b4903500c9040e003a044000e890b80c001034900314140042c0b40d260048600151094811591031440302c040c040d103642040c0246010407031401c0840d03d0700d006243c18900c554202070b15804074a215500195240c540c04d01800000c5900c002c0100480c960018203601441c41c0780d5252114401ca8507546203c641c400b2000704181e1182c030040c5070200c0c04048 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 759627374 1250 759626124 759626143
    0x1311030a0506010e0a0c120b010309061103060f03161707090e010c030e0309010c12030b0d0507081e060c070311010e0d120c02030301030b09011805010b090610050a0f03020c 76
    0x1801030101e503141c5034a680c003500c0001c044440250806c1002c41c00d9a81001c1c240c000c03110501c00200348003043c580120014030000704058403007401c140c03400c02004202c20045004000070341c1d04610340c84141042c503640e032030122086044c0204034038042108a031880065119503502d1004e441c1e1560399507000b001071b541040e03c41c1c2c580e079560f4958010025018426500a0780d06240038504195041c000607060b0102c21707030040c0480b4ac3c1c80124003080d502c2540040000c6000400c1d400032108036042143d6034a1542c000ca042512a01410001c6440780200301048101454010001545c48a51100da00d40062004900b4132500d00bc4005100b00203001e070502d503050200040c89038800380100104541562420b58002915108507108450f46c003000f22810749400200c40286901e424041c507006000c0078541c00b94600440002e501002010f400c02d07040c80c01b0448401100b41c581001300103529542d0008c50b0042881004418011030040e40400b101908508005040003d05103d203401e280040 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 759628624 1250 759627374 759627383
    0x106150216050d0213050907080d0908060609090303010b0f07020a0314070509010f0e04110402070510230402190503250f1202220207080405180606031311030a 70
    0x30810086000766058110001e000c00c0754644110115500882c007412200700e00da6501944400009001041c10080b5000800c0214203d8002e00c0c4691402440b4000c0350040504078007410340483c1c0742d880c0c0b910815002c4c482e95800341d03245906e41750f10384059a110004a00d00341d00244540005a0342d042002c50040d40289400200340c003040d0a903038200b40d415001280300c1e08080005010140b603030114241968025101c041d004d40300d0741010b0b60380048404141c0d9000e80002804001c115011850725090300c00c80006101510a140440c40a50240c0004031007402200e8000703000742c6403403440351104580174032405031002d8803440443d05101c0b429009091a13030805140148011900207103000406000c0600c5c1155410164240540414400007a115001035121a4401c2918044510710081015804c42d9580d140f07181400c0103030064410b00e4419240c03201289013034000c030807990303200fa94024180f40c0b43d0750314580300d6110401c07000000d507a0041c1e16180030410b52010000e800240303000c0c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 759629874 1250 759628624 759628633
    0x50609060f1e0706141305070911071203021e090618061209010c0f023f12240a050103051306020d0504020a05120604020915100903030e0d0b041401061502 68
    0x40c5c2488a420a00c0684604031010700e00e02c2d00404281d020450800784c4003500f0011550035903100e2292100e02544101411412149502a20b00c60709540140300c10300600403460880d15201d881e030f00340d0f400b0b00b00f00250440b1040207503d50f0000481c1c8441c2031007400520403400c00003c540e214206450881c0c811100b41c4d9580f0702c00c251160407030b080700041407a07440240414403101840b0f4808442c40c0c0002c020380c5840c1c01500e1110f0b200760b40596282424a40040d40303a65a034000301c80c10103829a001c1520904200e154441108182001d0030090006040305003030610b880700440007001d0052101030821110b84581c00028014002440328840d05940400d0341e00b0580108070210042d58000352140402c9540c4031004080400c81700d6026404072603402c09552400142405040d8001d001940300c4075070084ac0341015006a0048260380c0039540d10344090004c1418880500211140506070000043c0040d00003103030100c0a03500206a5000403803255507641e90144021840c81d07065015800 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 759631124 1250 759629874 759629891
    0x9020a050d1a04150f0e040819020a170708090f030c0301060905060f09040b0c2d19020606130e100213080d0c0b0708072016050609060f1e0706 63
    0x81030300410404004c032a20a03403420380303000d40e4402c442c10544220402d490070000060140882041035030354201d40300b051540414940c060080d198040803104485154401c40030000c3c000c200410384090660202c4520f14200101d13040000e003a59010340c840e45441155000812031b1000e0040b540145a0341001203000d0504c4004c0001040301001c0c894001e03145041004003154885d154150460000c4a1107a518a0100d1461240061101c51401c40c010b80721550300501c80f5080040010001480c10084e1642c4007450423030711148103468899014420620b00d00c4600d001c5d501203008000c5940c1150002061130301da44007aa00000208440151100410442c050041c813018420001600d031106008246590744110585c001e050a0100154880045c00d118055003010301d907103150541002a01100c0140c6554411002185e0384403150700c05000a0203061400c19a04c0d20303600204031038140010f800c46400e268009a5106032011020002c00c0c044031074090090140c2405401c001c65241c2 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 759632374 1250 759631124 759631129
    0x60f02060c1303021c02040612060510080715050417070314010510140d0204050c0d0c080f041202100501030819020d0e0603071101020d0f0b0306010e0109020a050d1a 73
    0x38001c00d103044036030040100d41141030541c040202982e0341203070705100c40707801c503102c401c00184c0502c0025005450114041022008101c0090000e0f00c218814411951800c004c10f0f40314205100d19145030340308402c24441100c0d0a0300ca6211001e60f4900b450416944044a020b60890141d182e4515003040b807080c070502c084501403559100d602c3e8000c0c040c5040c2170304003112400e001e11421640c2902e00321107a1556455000f450700c0700750000d00038412410f0903101c0700340c182c0c801203001c58500d15010304014141e006100d181d104001ca030035000c506507102d45800251684080880e0110700038501c1428041e1224455075010394080c1021540f10002049010f840c0003000d0215419540200d0352041c200b64400499959103d064071011f8482c0c07034184066664840043e004400d43d4008648582408850307800806000f034207120920101030a04107042c0c640000307000326502d07030442000521101c10250000c040302c0307100b0b2505600d84130036068180126814582260590485428411140e2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 759633624 1250 759632374 759632383
    0x20f041508010803190e0d05030a0315080a030207120804031205030105100302160f0302030c15090106060807320c060403140a1d1302220603020f07020424060f02 71
    0x60040d00f00940c9002681d034070600001c02011185000c01c0841070010015807100100100c149a0142c200c07a19a00c0f0035801501401003414400c14605160500141146000542802e016010380107094050304018103012040c03440e65054444140402000001940c1c8102607626a502a6907080d04ea504001c00c01c014807442d035550000b010300501246003c40c2000c0e001504442e4481180b580f01300151600b40c2c20b40c01144240c1141c1d008010300445140b016003c1144a00d440000030800b641e00d940040da0a10b100383c528100144840b102c081d02540a94541001d5905408031564140054002d2104540c000001c42126420a106000405030040624041100b00c591400e04041c040c24004100858502c80c500c240281004104546d869200c50075407000c107801029942c8184020240e407800b007070340f940d040740108031150005400e4420300c01d0350300364a180d925680c0340142a03020000941400090919072005120089103403901545480c0000c20030354072440c485034090030000c2e080 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 759634874 1250 759633624 759633629
    0xd0507140304230411030a0605120102130b03151f08370b1c1403070209180f0f060703060e10150915081902070b06090901020f04150801 60
    0x3140d0090000340702c141c60242d41c400c24000302c0e080012128403d4070015001d4100800c40e01c40c400700000070700030007480fa50000d03c00d403401607030b100c04c840ca02c1200c0f840c200d200f85604078900e500d14200901070000c0900085411551090505200b40004000114650740d20080e090400c6e03405484c040003142c00420780c0d50700600b50b0b54021115030032100b07401d0725458401c2c3c00c3c047c00f501d00c42c42c400c000c03010395002c04c059040140020030321509002034280941c044030019117140b40d80d5048624032000000496800c50383c0a00240c00584403285180f49140750882c04052034012300c911a8899001006007801125214006003414280520050b04032400c3c3d4000c400458411760230441d100200c141c400c001c03288401d0038010a01041681101c0100c0b0541040c008400300001c007542040e84621014010f041c0400c060305c1c00074019401504034407442da03004040043c540e0000740d1a1a103141070f103034002014000503280584e41101000107521940205201c1e40006420b0940c06a00c648910301 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 759636124 1250 759634874 759634913
    0xa09020c0d140a090b0a050c070305030a03111c0b0d0b040303060e010b1e0d0e0316051c020a0605040606050d05010f05160c1b0302040501060305160e1e0a0302030d0507 74
    0x5080008000107060041a0180c50030011700010300400031440345017144c00c907950030b07030030303144140c1e03d1b460240e80b03039444080b900000a09180744800c0c400000021a100041b29031950080c9111000000018002c8002d8042d03000001d0610b4002040c0903d604a200d24480d940004546d030800100035076040d01a045000250402d000c0d031001d0280e000d40305019a4000e000c002d8950240403800000344c403007803c002d00d00e404045440d001c29601c100300b0f02d00c0c9520401c01c0e16444200c81c038007204840204044803005900c81c00c424408030711940d20090b0014010303900440c0c0c079610f40010456040c11401d048905a658000d0899000c14504c5240e4200d03000d0380b00040243c0050000500109940c00043c21019100c00b800d9107402da20400c200c015070340034006000d113694540380600207007004ca072a038000f021100890003e82c1d00c551000355503118020b0034101c00547c80a5a0340102c002c3c80300311500f18007000808405071307408105010003021300d40d403502d0742c2e041e482c940f000c0e240880752000c1c0ca = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 759637374 1250 759636124 759636127
    0xf081615060f061103040b280e10080a06080d020a02040b0f010806191d0a1d030f0c010b060409050603071215111204060c0e09011a090a09020c0d14 65
    0xc9401c680a040b0030407100c651524005801c80349130000d003107110316840b000c1031003c001000548a625804845443c124110300028541411201550503000041e115039101070b410b030054410318080c48102d034200903c404000340503038444080e6441c18061244070009030380b14110700f008601d07190051100c00202070341e607041101c0c400400a001000c0c050801c80c450168050103501c54801000030b40b00a00c1d00d10785001d40042001840d0300e00c0c040070b03645100c0450078103226a082d141d00000305087c520a0a00540c034020503c1420034568109141407103095403540d01da00e03a60764407400a000a482540f0000645042290401d4505495a4002c19004103041140c0b00030500039070405140d0034203000f005c1069010607105141c00e04c166203005400104000a00080c4050f640c4030304603043d91a19442428a081c1c000c018480d5800d01c181407040b00c40420330141241c804024001808001c0c2c400d94110362908001000ea070071903009009144e11450a8110043e881003600c01c41407005504d0743e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 759638624 1250 759637374 759637379
    0x2060901060b0c0307080a1101060b030604110304020906040f06030b01030b09190c060f031415310e0a051b010815030a0314190903060507030e07120f08161506 70
    0x20f40340d0007400c1d4083e003604008202d4102181c000c102340c00310042000002c000103601e0b03212001c01d0b900103540690140789401000380140100e4021a0301654006040c401d955903044200005492040b1038503050540b40d400020004041c080300038003843c4164484801071500b00d284624002250004100c400300b510f000c580415100880074059078030030700d80b00210319101501078025041411940d18040a29820004241a0b600741003119880c12070348281000b0021420309420080010003032607604509100c4c0001088541c0302c0103c1c0f41501060744d002210549030541006840e003030f4001210011055241c071581d1040c9019441911104100140005103010a91b0348039084030003000c1c01031540f81d03041d0703080e011010340d12881038000c80540528040000181011280d00c41281d8940c1400301044216009000308048624034800800390030b45880000301d015450044140d50003100d018400010030b000b400240002a5008a001e41406c03d03442d0000c040284100920344032803500906 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 759639874 1250 759638624 759638647
    0x30a230109020a23090301061a1209070e090304150804230705040c02070816050f01051b0a0f020907020708030a18080a0302010b13050601050405010c05100c02060901060b 75
    0x4941912403880d001a15040d4034002910383e481c19104283c0d5011404002002c045890070040c9941c140542c006d021165440b032001d20507114035401c0104211013404010200000c1c824515484040344048a00c0345d0b50301e800280513503000380c03035252035030f00b00007414803008540360507010660300e01d444d1084123494113480758100c081d544103c0c0c002c1105030300e002401c038074030800512014000003001088800500f800c040c0d0360f10b4031407080780e42c02d0150703140c201e031103a0740000d100d400c865001e401038450341244030044a00c6e81c01410306074040c6aa42c20b80e401903000800066003400d2040c8100e480340740150040010544005000d001103500c50481480320120202c02c2d6003903980d0608200011121003009040050600d4101028a105441141060503415000a00c041e20251214180249000599070a484044814601160003000108140c2d48554810204240103005440f84034528002020580b40c6a880e404016803280050110515081c81650001d0041084440c82e05e50b45222 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 759641124 1250 759639874 759639941
    0x109020907081e010b27090702280213270f031731020622051f0f0e21060c070f080a02120f130e0103020d02040b03190305030a 56
    0xc003c82c2d2503c86c00c6940b40c44001e00300344c409a030350000344015190311b04640c00964440da1140c0c1003410540301c0b500211940103801d00102714030f03006000d03841160803101d1208094103a03840300780f21609640c02e0100d900e00185108101c1c031481103200d10544109800c0091031b044401c423180e0074a12622050100b1103c0d40400305411003d44201280c01220b21401e21500b0840218003942022002428102d82114042651000380030143c41c00311080d12842031140e084c003002c070303094090002640070681d028080c0603801403203400e80c600380d48000a0940880c11030703080c03c0ca0207007010100c05400131a601080c844c1030361100c03502c03441d642851102e450301c140036041000e000d000c9078030004400e0340080c800c4c0304030b86414a06440440e928207000144c81c1c4158003200c501c041ca54250400442c5100820f0310b407d040340c2c0c008000780242130346a001c00c0001d0a07040b2081c1e40c140315103404010180c3c1e1009407107076041d0080c0c42d402d0b100c0c0f5041141c00140c51480d0b88904154900050500c240c0c2d80304007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 759642374 1250 759641124 759641137
    0x90515090612040309080a050f070b040510050903071511010501050603130b060d050a0f030212031509090a0b01150e0402030f0403080c2203060f27050109020907081e010b 75
    0xd0b0803074164a07503081c203860521302e941000e84d45000d0441e140e402d11100060103841400131004880955980f90035602a03801707903003e0320f6030003081038654841d242c4c410340141c0400c80b002029a16450359401c1c00d41a816026489000403400340d01d0700d5410400c00384a85801850140c0d80700749107181c2900160094840c1c1075006044000c540c0c003040407526407924051a160b0311804032584c0240c2d5040c000206c1e854000e08800500c07610005c0b49690074910242d901944580c1d85071040b11580400b040003500e0020003c00207445451100001314411811007402003d80171914522012048030040011215880050046004109018144c0c8903a5001ca902c1901840c04039840e07218284480510b202e400d400500c900c00e00281076101c009205a10170441e44240c508100c14a032035081c2400391b500380c81c05481c1a0702c0000084030f50849604940c001c0c02d2107803000056002d0036600003510410107591000c0000e0501d0100705003550520701e10300b003811560100c10803945c0b4100300200b2912440 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 759643624 1250 759642374 759642397
    0x3120f0714031b030901050301121104090c08010b0139050a0b0a0c0305042a03210207082e020d0c1106011a070204091a01060905150906 60
    0x1141440065184195115294054030780da0780d1446150748666a0b40000403010b4600c0110150540c1010000045403101c030710686416046a1810f411854004225141a5074030440b03611039898aa899100e00046288180d5005161604010000b400c45180d11007560500064542081c0c2a100840310080c2030b031103036410720aa011100c10b003441107001c2c40d14024042e209070100c000c2084261100c0a1150031512000c22078401d1040088055800598015148030403281c8141c000f402040c45400041149072041e591084d85c0e54ac0b8613540c08190b02081582080c3d040015600603410b024030700050801e00c0007400126480907424410310b00002c030410302c0391a0a004072103044048d4041e43ca41040a2074104280d810307843c4050114240e03010743e048180502c80010580c03980200505001626680000707061506c0e035800c2c00300420042805441d034014668a8400298036030164601a000036560200b031a0302e403006020f013444040c88401e00400040c0402c20701622441c6c1520140e0141 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 759644874 1250 759643624 759643627
    0x915091a1f0513060c030e01031a011d0303071109070504030c060e031f090b0906010f0e060f1f02010c0807120c111006170304060c03050304062301091a0312 69
    0x505074162070754030415402460044188000043c0260056508003269000e920b501d042d811742c1070011001c40d003d0813480c441c0342290080940c020b5214800c0da03601183c08400c114403c0702810002841c503040380d10215890254040300913810b0800d584d2140d0002d8850400b03608007800c541c0c0f01c0260032290700400080200c07000b000b505550303080000508008081c0c0c00b50214000842c103800180ca944882542e1404156001c00c0e001603000138014100c4481000c090021030a040c1c1c009a00340010303107425132100c1c613081c03d009265030700380840c1d1043d00d14210720740c0001642d039000b03030940780708403052401d100c5440d0800006130342003840e841c80c0000c80b11002420541c0f1450070b84081c0b5219102c922076100780c0c600b1140d0b2070b409038002010303952010307903907030030782c244814a030f6924486ea02032140020002c0170480c0001e4000c2d00950b4100b4461280807902c01c0c850070101c3d1f400105800c00580c2034681c031004000050070f03403007070070b84491249080301043d01400000c0f0360340d01070320114003000c1c260 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 759646124 1250 759644874 759644929
    0xa021b030303010e0c1e030a150303050f09040b040f050937060f110a11070305070504051b0307020115060807090e0a060b13060201141b0904060915091a 67
    0x2141c01b183c0012070303000f981c0b02c03004084415040c6184c1080741d01c0e49406282500c81302071100404070312000c5a50543c1c1c2c8901d0845450160030302900941441a0080d44448402d211070f42e882c010581c8800c40e280c400101071a22002052801c0442b03056400a64600802500740001642c15031f07071130b0b030106525400d502c3c280c5d20f0101c0c000c4c504140e0b040c40d400d107400b80448075a860300380200348241c0700d59105000d01d80249003460711400b80784402005944441e1041207075040079080382d0340c0690561080c080c100512100d5070510f6108a40d2200141d540703660500c2085d40459403000a0800d625043c1380794500301c0700181c2140e49502582d0951000303100002c0c4030883c0341d08200f01803d407201072503881d00708003143d160f0064a640102030243d400c00c400d0380d80c03030b8801e407030746504c140c004000140200c1d4809220141c103901425165070080d44400700030804407103500444050075218110300700860700d04140d8401f2604a5101480a03211500040550703542e40304602c1c80c00120160643d08140 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 759647374 1250 759646124 759646141
    0x60415030f060c140d0501050109060224130206030c04060306150c03082a03040507080102030906010626010303110d0806060708090a24020105011e060e1809030a021b030303010e 78
    0x1458103422200644c0c002030001c5400e2010380009040f10000c0c0c84038181c00b40c440e882aa242c000d112201242050f46588090403280e982c7c2180750804880103602d035200546801060080e80304641e441e4103000300080800c0844d41c184a40d5005142c1440304075091001d00500408040920324050200482d0390003141221882c1074000c82c0604c602c401c003d0754003907900c4036403406030001c03502030703070140900c05000950740018021a44101a854050405a0b0901809503010002488100c01043e0381d581e010f0712100b12204c2860186019445400e00803c442054030700d414441010341041004c54003e105407904c0b1001641e036610740c803801c540d0f1a803a612010400c152610341c80b034140801785070a0350a12704000d10303c1041d8842164002d00040e0b0701c918140b8801c403010601280c020244e510308006441c8034169044290348002d04084460302c80341038240070124255a103400700d40000450107a0341e81c0412202104403030700109200c9001c00c2c0720011b41c8a001c144280820b0400d880002075151 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 759648624 1250 759647374 759647387
    0x10030b040b1b0313061404020d03140c06070c050d0914040b0d0b070c05070e0103020a060c330b03070513200a0c03030b18070e0303071703060415030f060c 68
    0x1a2803045201d5103e04c1c000f001d9100c452903041042d03842a240a4410303031040c000541440c070603500546008032400075660300301e542150014513a000140d080c80f521030440d07014441c05018000ea95038100d144021070074200e0900850040304807c0c480c044908200032416090b441c1c849650464000420740d40c0040032500d416000c0382c009100c03400e508100518542c0210040803d240180102c41c5101d880e400002c012060a0001039440b54a10008002c607610408110400700c0c0b0034283d640c405100e80c0140501c0c1001c03481c0307621f2484a80b07a8100d42e1b1300154411350a42e8541100100703d520310300404035a02281a442000c00c00e80c4805160b0a00c0481e000340780c411454054143d139591014400081c0318500b5218101d000900306245104e886c50546003400b200d01c0d41034120807607900c0311102550005100007844c1e4050000b0710005012814608815420030002c040e01d566038540079040008640d50341c0e01e14109030704510818000300746480805402281c0c444000514a00c00b500c2c1a03410 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 759649874 1250 759648624 759648661
    0x50601020a0f05152a030a060e04050c0910050105040909050c10031509060503300c031b01020c1903030204090501080c0a0e0c091504090504030f020610030b040b 71
    0x44000b0201510410100041d0408040311140600c0c18035101c90034444c00201601010700050703282c08045000c000003500c01150400305824002800c142e45101d20482c0c241c04030b0b0146ea003900512603c00303c60520400c402d030301c00d6170110381e05030040c20000060701602950107108201d40d075039204281089020010703140300c800f00410300758040701318400040140c20200c46076000031940381c00001c0c8011382e5000d034406840005000c0c2410100d210039150b000040a84404801e01899020408110902c0300502401511401440d9141050383c1c4002c0a2441c0c0404250f2a0784104417a01100502007110750310070841002d03d10f03107016107042c120040d005541200b1a15841c1038000112103800190240000c42e0030395114140c5592000a40d8a4442c2242c400c4407a140400c07103441640350001a0b003840d94034550303855060a403103254446c1103910454084022030341c100058410035404101c0603521400c14040d03010404d0440e6108056603c0103000103012090303000c08100300c8407081000c4c0d46c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 759651124 1250 759649874 759649883
    0x318081501090b090c04090525020f0c0a0503070512010b030106140103180b0613021c02091903050318010e1306090c170c03190e0a03080a09030e0103050601020a 71
    0x580440c40c419641800d0020320510303001624003204207115080c9400c02610802d00e134266103082c149081041300203000020080d1082c9204076407104c010070662902d110850480344e000b40800f0000781c0c1602d1411490140385446020001010030042da000501c59040e030380c00b0b4550250702d030b841e2148103000d004003048656255091013004103040c0343e182d0012030009401d03a018007840d240c2c44d2072280f40c0d072401c8034054100d4462400050751410140f07403400100d6501000149000324442900e0408001d622018280a40000d070024045c42c2106010061351135003001c50b00503030321f113075106a640e2003500c2c80f04070f90314010300758401242e024250070a540761024003200d40751340c1404002d80007000e580c000c00c1d049a240403000d0120601c90388401082021604000b03002d5103030f0580107003181d080200700b201c0102c49165154078951007406803e003c0ca403081c0003424900e40a2a01908c0040c0041000c0c00e054540084280840d13445040120f00000030300380001c203500c0b001d004074101a4140310160 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 759652374 1250 759651124 759651133
    0xd11070801061d0c0a0206060105090f04021309060506040803030a0b0a080616090605091806031e0604031211090420070809090705160803070302090d2913031808 71
    0x203070032102d41061040f0001261010b8000759030368004101d0070f000703100d41500181d0106001682c0d550084004054440c001001c0c3c1e400c42d44988000360680c3d212500411307018159050800c5142428043c4030090103044030100c0c145420718094650341e0200600b86114551200e00c1444207855000160340941604400c1d1003080c80d02800c0c40e00305e401900c406c10005814a0000540b4a1080b03064a288080043c00300e00c2500c910521810261005006c0c0d0743d150003201c2101c0e40d918860318205100000e4800501004e1a10341800b070b1101420f01040304007281042d000d80202030f0044211100c4040445000030740803010801426100b07000c0c4248440840e002600d1024840624043d1580c440e049405105603511f960048455000d5166810b5220b404400e200700060011005943e1001d014034005003015030910006041140501003550b60325805150702684124400341c581c5000800381c2c007041d0608182071020003540b00ca4034090100120400e031a0580510300742d502008240b04011103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 759653624 1250 759652374 759652379
    0x20f0403230c0f090a020c07120c1202060301120507032a0f1a03130215030621061305100c03050601080108011a2704050105010f05120d1107080106 65
    0x301d501403001119814688110032040140c41000403900d405040142802071003081150901070209005049440029002e101d5120744120401c000c4000b80300050542802000a0501a0790b540fa141c12034000658103080810150b203400d01204e04444412080c001d401c07a203410241d0802109810040102a1500800342c100f2183c00d884510b913450003140111f019602c590800c0d40040602c41c4541d80742604215400e00d2032050091a4030100400145414000c01e6001902e1801d40002000078440c0101c00e105c030f14108507100102600400040d520f000010800556581340d0040030f89074080a00d1001c4420450b00b44010401c03401054000c0c4200018504041c0250104640d0341d40003603001000041e10000501407078605255420440d040a03c81009000d00009046d806c0d0403011040280e5003c100a100e02580c411800f4000000b01035040c2000c00c000030a40303500161040024442198104002082680c012011414200c030303043c601c482d046051050780d80c400720442d403074040300 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 759654874 1250 759653624 759653633
    0x30a0e03150f060315040b13170f18040c021506010e060d0b1f090e0c07320a08030a0203040f12030203060102010b1c1209180e0d050a02060f0604020f0403 68
    0x280f40120320490a9031120740c00144141c16540c800c9601401c0740c41101d0200e4440741c43c41001e07510315406901821888034084044202e5a4010721070410728110004d501c502401280b03512500180c07003107030103204016080b14000d6503891542c4881c51150090360200d02c15070f00903c0550218400503055903145c1401750503100040070310040c0d080c0580350290081c203c424127207140c0842848103868911080342030075440749440c080200070040080d001c10403440440e80190104603034818000588665181c50001c82600c00101c03503055159910900b072240000e00c00f1025030b43d002c041d0080050701c030b0fa101d003012100c0204842c00902802c80c1c90404210499064004501c106000e070000d1104540400a004041d0160086803414640d1042c0840020700640c01030707451980a468214030442d101c40da01442d400b8108a54001c9669031442d81180c08001d110070042c82989007070840c10191016006916210f0060200381d1034130f102c50001d0710307a5440d54140d84c1e0315014690b1050f15140c0b80d152 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 759656124 1250 759654874 759654901
    0x21c0204030c1202091f05090f0703060506031303052d04030611090a120201020f06240a060206180106090213090f09050c010c06020d0c20030c030a0e0315 68
    0x105890368000c4040c0820743c145000e880c82c2016602900891035540d5120300c5080e1a102c003000000564030199000420340e446c2c0380360310b000307070040030200003182001100641218800d500003402018148100700c1208021201079885680500700b140e40c90850000d580201e45c07242001c6505084c01d00c143c500b081c032811000d0000e83e4490103080184d1901082d5143d001d005a0103901e42c440455081417004022404040d08003a10600403202d62015000a45042a00c21520100b0342120a03031187c80002d44100d0800e0200d000f44c5000302d41d030b414860000d445070b0006295015240c09070404040396282588003200403c0151400c54139803e01800d400c100364101d20072160f5140c10003010f80399100b0a84500758000e64800300a003c1207100308015100041ca01d9001c5e9000c036400d0015051580c160f0007041c0ca0300d0350750b90303071540e15069040007002c80c03100010099600e6841481440700410300003003110030340580345c101881c00d40c1031000002c0c80d00d0100306550a0030500c090a100e810740c0c03400c4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 759657374 1250 759656124 759656129
    0x315090114150a0b0c0c0d12030f0905061602070308190906110604020f1504170d08040b010b0304150f061701020f040308090d02031c17090c090a021c0204 68
    0x71900031180c84a00070000304448240950b82d0044501404021600d10b07500207003051520034043e50700d00c080c0710000680020440e03809443c900014100c070f11103558107100e060001e03500c0c580c0c20800c4290715103426540d01c200400464500c1070224040702060300030080300d0003d40d0b021004556030512410340300e241a82c81c100385004641c0d00701000c40c1c1640100701c80c08a222011005220658403602007180010b81d0000c4a83c210000080311015214a90300034000703002c20100d1585c03c005801d01003440d203450100ca000800c072a08050000160b10403866904488050500548a44560820140269201600102c0940703480024000314590f900a2000c84540c0d9259002044020203620700b03038411881d502443e250100001d000281551000d4401030300090310314058811254082803405a101c0300c0c40303003080f03004041e1821855220a004a580e800814540c110b82010070380c90f81c0e00c042071b440c0e50380f0502824001902e8100240e0594050244420900e000c030300c4c102640e14000d61050 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 759658624 1250 759657374 759657401
    0x306150908010b1c03081f060908071403071503380102030a020312090102040f030506150604120602030414071502070801110403030c0602040807060302041d010b0a0e03150901 77
    0x14055030464501300c001109448880c8004840b003d1095404590004c4020f006080e00c5000b8120f02c0d00d9800b0044000c40a070515440d8281020f04006815160844907171100c603c0340e9841e104078200e40c07004030365001201d151080110390110602002d90141c160340c0100801d84050020803000182c4901c000760780340290200b020f50362812040120380302d00c076100103c00546c0c4100f00103403008100310700081d48003610000042c141501d90021000c2801580c0c416036555010505201d90680480b68450818000f00c0b05c06281a1811280000c12042c0800c00361209a000c00010f050282c68210090288000303000d441650b6112010554034544004402c401441142c002003030b84801446a206c080c6001c120440c241840c0d69002c8a4086070400102e070803503028440029020020800100a1301c440d0701c002da2128281881441e210f500d000a100054034a0401003000310b100d42e0449642c502c951510499101c501d8010914001e0046400c001c07040301c030820440950419480441c89110b41e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 759659874 1250 759658624 759658631
    0x91e13060e01050709051e06070b06210705040507110106030302060108010e0601050d080f1b0309010e04090b0103020f0a0b120a14040b0a09170c0709061d0412030615090801 76
    0x4844031030b00b01d8070102c07001804070354446002d1105141840d4419101d026145a0039007000490020449642083c102260411000018001a89000031407012034200071024407541042030b400c0b0545e200d1091088a005555401c082695030748074444c4141450032031002401240d42e40e18000359128401d02c03402d8519403810680c200c07884004142a030403244014507400341f036401c1c5c2d02c8051666010800c0c10006610400621190110354130740580d144101c60061501c40c820b550014100c043c551540e50f22891405501c1400140c8400c10141900c0d015144121100c13501340116001c4042c68001c0c034039940d0007003070a00c0e44810500403a4450800103a00380542c3d11041c0d112505190140c030010900030b900c00016001307944035404140658000c600001c400604084420140d40c0006218946500700d4541800503194500401000741442c0f0140d0204000e0052180000100034100034107141e4150381001c0d80900c01e80006019192140000703042040c880d90182008583d4031840409509 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 759661124 1250 759659874 759659891
    0x70f05360604030818031501060224090d08090c0409080403110406060f050a09091406100e030307110409050607211a060304050703080301181a010e091e1306 69
    0xa102042d501126800080b1900b0690200e140145152000841e6034052081000e01c102940700e007080c044c001c00702600640070383d04410360140071302c410303a013800e02030b00c0700300303030501c41003140c001181d540705100c0d40b41c1140544c940b154051b04180e040342c1166400790400c0302a40a001e03000004004680c810b46030f070b56206075140113200603110741e40b24003408640005040e61059004600808068086180100b40d0359103859001c0110740d120400c5820706444c42c02041f2139400d050340c1c4140c0503007940c141405a80601e000203580c0e8030806400074104a8921a0b090310b43e00d9541001d40099445015a4000e1a0061004101c50400c03180b03240840c0e6040303186907591080388984001c80d05a50456002ea12820f002c0c8001e0340e0010f00112110302c11118000003091200c809513001c1c00c101109180240107014500c002c7d0f0301482c01c40c0070b948501d81e05d086103680e000196414540800d030790300315082d900d80041c03955038040c41d2094080c074180007081128001d5580c000d0b4407218440d4100300051074 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 759662374 1250 759661124 759661129
    0x709050907110106140a0506160501090f0b070e1020060106031b0302090a0504020304150609020a1d03030d051e0a330311030c041506030b0603040803070f0536 70
    0x4081c1403905d50420300e00c18042c019824051700500108035240015130240c00300742e03102421186000c03403e0b100f00080403407080c10446034030b012941080851503e401c4602d0050001108540124a84000e02c02c0c100d111801180042c100400031600d0f9200f81e032107940c2e40710303030142c081c102d80f200c0c15640c0d440340101e0f00d80490191082d2050b245014001d440c1071802c14003440f0080d8000360003501c9403082491098800e6074903001d408041d002140e405a20340901540251200034005801801000682103d2420b92800401d07130344451601c55020a0580350300e100080c3c4291403c0482820030003006c00c110200390344d600442100c0c9003041c462100018a00304a542040740d050751062702c40d082480030808100041003042d005080142500d401180400002c3d00312000244541070b01020102d0800a0940500c5221030865050b144149140351669a030305136488010904001c4c0210710030301c1c044481c4240b01742d42000001c00074000e44440b440318412840c440003440c1031242107181206020300d0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 759663624 1250 759662374 759662399
    0x1b02130509060c0a0e0d0f051c110d0e040b01050c0d020606130b03100c020705041a0f04050402060a1b02060f030a0e0f03090409060b041805070506071104050709050907110106 77
    0xc0c5685d1355a0b03483c040298080000c0040e1b0040d05a610780d90342080d0b2030104009001c0c415080500c0d110000701e01070513800c080d0002c2c41003031100c078081e00300604da1401c0c3c5410141d4000010821100001c0c2d03c0214001665603020310f004a040350701c501c2040b4008543c0004070540214012264204003c01d10501c1506032100c40310140e400da0090800722001140070b81101100c0388840c0159540c00ea111380215003140c0c021703207484165200480c111440750501e411055640001940c09000f50715054020035618420480d80000300a900810b41c0109454550701d04440c542c001c11140d0b951054000382c0301560000c1e22840170051900c607005840307010000700801c00b00d03e030401841c14000d410040100a0005810555203a516001c0741189941e0301d1007500c9054202c0c5440703c00140701030900907d064290b411082c01a08204400c0c00031034150000e013821034908690129030740d994560101c0d90703250180e2103a41c00c00c0303065040c0704c030250f044201c46005403400002042416907400c0503030041c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 759664874 1250 759663624 759663637
    0x5040e130f1103010912211404020105070515070e0f01030606023003100614040302090f09010f0509010c020c01020a0807120203070f030810051f1b02130509060c 71
    0x38003050648900010b110120350012850300800015004030313552100012403185151040004080c41807800280c001d441049034108080348040041c45040c0180c0350f88041c003c1c2021b0b0500c1408034400080000410001090000c0a40840d285050a80c4058081622051890300c10520b109030030075130394840d200352400c45803254014955240304016070f064809842030040b200001c0c2180111035600c502000b5070061411108800300e2600c4c010000745400386144404a5500e010001080035075182d0220a41000b0300750070400031030302e4190840303004000b40030b440130300241443c00f08990080c0650112118890603020703036030b500c10307a1001240c03101e4090500030722030301c400d1007540c020500700549a4028415401101e150481c4d64441512010b104c46007100003680b03000410031203a00010b01200280820b942c0c20141045840320080b9405450003c1d00c1049103015100e540139100710448140d50f40c000d440d4035008a200e03d2082c3c00341200300c50200d00c0344070f800041580000000203c030b07035 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 759666124 1250 759664874 759664883
    0x9030703151e020702130c0306030b04081207080f0123270a06080a06151e060e12190503090d0c090506010e0a0e09120408010506030d09150305040f05060705040e13 72
    0x5080c2c0a10407404024803140c1c07070031f004040e41c030500880081d5111001c240591b0085032010b232144400b040003030440100030880d0080000760024800307020200c0c0001c906441a5800000815044040c0c519020b2000b03071260703902110303800c00584484503400d0000400001060504805c0d502d2801140580b0038a10403811079900c0320b44d00101081681d4003c04980120001228000b80d840f203001b8010403035520082c0302207111210801145400040707034810f80130140c1d015120344610003520f54462071680c41121600344901044000c1180520032968480c4004104003032809031410a0507078036103a07024400540717141401060301076014103a040150709006054031032040c14840110301010020f0107042e03442c03007513888120040c0c0c40f22010340050030700100005150325203c020036107049004491602030000101051061005404681da60b1401d907060110742516180f5000706030050300034000d071480c040c40703051200e40c03a84100140b0480340c031034010001076220059a005500c00c0c0030001030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 759667374 1250 759666124 759666139
    0x180604050a0b0306190e0a0507020c01090326040b09010e0405010f2106020a03020307022e02180a03050c0a09140402010c0f1505010f080615010509030703151e020702 73
    0x565880c1c0d2005591000c0c0203400d01e2151781c10300c08038014042080d000100707141d640d00c04025448101d8030440b030340301e180e1b480204100803160340080e2820501d0701010b0040031610000985070081261001150421645a0b9640d180e64500c0740800360423200240d07000a407640d003850f05518003800790381d0507286190245648140340c1100d081417039000348192540d2098018020003c240241f01601c00401280c40150341c928040c10700070705001c0a1810900f0000803042241813028004101803180400082e0050b5912100d03001e01003050a8050120340c096226007021040000101d20301c2c1d0490819070702010034548920610090302d0344034840c03001020380c02c400034000d98421010100c20380d00441f21825900600d454154a20761000e401c0704a19881d03200401401140303109802c000e00d242d002800080c2000d410646414450016090404c0404160100d0316501032002d00700555002d5000000c03042e14100c110060f0440c802e1400f020030038291b101c82b070300d1030074000c84019507401030100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 759668624 1250 759667374 759667379
    0x3021c02071410021005010b070b0609070e010e01030e07090f050c1819211e050c040b19033f080a180303020c0d09061d06070611180604050a 62
    0x1078210003d0200078118070074020020031581151040310301030803640541560b00c818608060fa8070207806009180240b070604200007005500803100c2220010034a08805400c5034000100c0c003404481c3c00c0282140520100001e0018003503210840014204109220650341c1080444290181c400031a05103008100300040070300e000303800c000b07403900740d1595030144036100c2c8088000c2c1720724600400c600011000d180001d01150071134034841c07640541c1c41c115001006540d410b45614051f54017500464903041407584035075850420700c000780c0248a0301000b2552724100300000140007100860760442c0003c1045104001000c08442d5404c42607036010b401c41d50a9086170142002012001920303900e400c1d0503500b12003175800280300c2c0d009540158480c11000030140c00c044440d2090b00602c0a1044200061030b0807000e07602d81c40c810802260745000c1484003040c000e1160340307801001149401102d801c034a4690300a00428008414402c1c0303e200880f00344a800d20940c003075641d000750444000c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 759669874 1250 759668624 759668629
    0xf1003080703030c050d050a090c0b030601120e03090d050a140a0c180f15050a0b03060315090102130e0708061504090e0703020a060504032d0803040203160303021c020714 75
    0x1a440b9050740751281c68108010681b40441d5800c0d00c9642500d515070802c00d0602000560b00f00182020004462950414400103442e1001603180008840e4489440400c044414016150340ca0405050540b140e226868007d44803600715030101c404c000003c0d20a241ca0703100140303800300e641d40884080b00c3c1500307120700d0780108140b1000d0304807070b1034072921000e541d004140690342160b00d10410480c680b5040100f0055500202d8000c415411401d00401c0740994002409110140c0d0080b4044a6074540008941c064402e022003400100210807000652440100405104480c556a01e428940340c000c104056021009107540c2c4014061000f03100003c0180e10507140a5141070884040507569400b00e5018030b000c1e0b0098000c188080750420a100318513480c0b680d2050400100c85c2400140d400311040c1034aa45400b4042c1c80303000c0f0000d801c54070b00700300c500b00f010202100c40ea041952031030025070301c00d800c1c0380085041d0142c1540c1c1803202c1c0009040001d031200c40c82c944403030382c000800303 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 759671124 1250 759669874 759669881
    0xf020d141015021002090d15020408010c0e06042702040f0906120302060718080f28050a06090809031603121115070512011e14010203030f04060204090608060f100308070303 76
    0x86d05944030000c500081c0000d01c50710741c01000300702118000341c0c640b451315071002c2c01c4510109894040c0314042050003650b0350f038441120191010841c1c1e0318001b681201d0705c01c00f04484140c00c1001c6c1403000401095451440c019942114103d600601089890741c40111001c01c0321100100543e000d0004a01000d0080804500c032801c0c0031450840c559442c90f81d90302e800c10800075003080350400c5059018400c041040c0d0b0403080c00c5040c801f0484000c03660b6460703480300304400c00b501031903644158904100b1524121404250010219201a110f45c05400e802445a01c4115009240d040c0c0784220140113084884c4205000c001030088009407410b08055620001c0401c002c004041150540311000001e00c2400307022503606040709040c2900c2e0b0469242e00395082070303007000c0078240c000d44107aa0000450350311209181d424070704e98a892604401074011b40c1c0000f0703402406c01c1000300e850b01000505511903070f00c54040c09030320380324107000c443e1006181c080a00103c90410498010031300a40 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 759672374 1250 759671124 759671137
    0x605060706110d0207030305090d0216030b3408010f0b0d18050118030e1e10020703020907020102120f010305030301120c031b0611120d0f020d141015021002 69
    0xc1400d483c002100b2450310481e0301903101140441c0d95442400603160007041255500c00b05400104807000b581080b00c0e17011041440010003110f070000005580b681031140d112003100c5400c00c2070705c1d80010b01507001d400340d42c9648072900142080c0300010f40f52411a1400c802c80f1142d040551615413940003100c080c0500004100407007299050510000f03000340710301c1a032003241d4821840c0400d840e28004054038055014a8400c0c0c1150a041e005200b42885078000c2400881d802c5000702003a840c2607040c2011584041c0d4442503420811054030f4064004006464500c48140340d26a10954400a2808280000740141d88288010b0020543e16546a2105401045100000b554a40e40c1005038055040482805482803404101d881d4000c900025001ca0841c050300391b4104058081005000d41084010782c580c407010144180411607044414520100c40c0c1480100441980e101480b5001d6420000300307032004c40c0018000d060160790100c0041e050b80a811004d0b11a80104041e40001 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 759673624 1250 759672374 759672401
    0x12050f0412050d12050405030406110f010e160504063b070e01030b011d06210a0e0f06011d041707030e0f030a03020304030f03030608070f030b0a0605060706 69
    0x400022030301030303400c480240680d407140009008583c40310a000701030b80c52100802c40d0450401c000e110000b503012007505c081e1011854144a0380d01048445460306040341004400e035482c040c0d03c0e20075103d022070040007420660711403182050303441b820701084401070310980100000350014410400c2c5c45609002c4580b40034101841a00c0030800811b40c034181c16201030001c5a03e03151500444c2d6094007600d0a85d0209007409600e1400340c1c0102e544045200288511400d0b000940109803429554980f07400f00d601000e4221a2070100c20210081c402d1148400091061100300c2e07100c503100152040c113880710f50000011440c0c1c0000c4003401e000010348100d80c00040540909104454003010303150a5002e80c0c0d6030890300801c40184081071040264840c0030b5008085030801081c0c0000444088030b50003414010160b0030b0b814100d0090103150030404080c00740c00d100046107003103803841d03030140e9020b15081c0304141c8031506100704072551032050b01d070450810310840020400e43da00c0a002d00b0a071 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 759674874 1250 759673624 759673627
    0x10918051312091d131410020a0810050909120a301109010203070818120d030e0312062701061808030304020105030c03042105031504050412050f 64
    0x540c1d89003030300c0b0030008400c080020360742102005555500007819541e0030310b80380500440c1c10024a9a40c0f103594140d005804001c40390100600c10408003c65072859001c40d20842d240e01604100900840c815110b0f0207500015010206092614080841c0202c52020081c80044030305031180780075812000314034081c42050004074201d001c0303100026080340d1442c00b540118140249107075040700ca204580f1002c41b0810710903460141d0700001280d80e4107070807100d441e86440781c800b00c54084240043d001070b0841c0c5448510f6252800001c0e10108070011030b14248405400b86028651300c1c0a2a200c0142504116010880b941840e4841103c004806100740720411183c00c15070014403000e0340180c0c00141561849807070903a150100c40060941c28020310300e181031540008145e0302024115010034003001000c90101300140407041030403000c01150042450761101f01a0058000f00d401852110707051038503203503c0c6400d01c502481107070b10580070f9520603425501110030b60000e12007203800c441c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 759676124 1250 759674874 759674911
    0x130f0203030409051f0308040513021c020c2406010813062f0937030f03080717010e070e0d080a0e01021f2a030c0e01091805 55
    0x30180000c20251000c401d0100360760030891098a0814090002c001c08000e0350a41400010700d101c007101c040b41d0007260b000e0309500f05036100300028460410700d4070411b0040401c6008004070303500901110205c800a0311902003003100000c1141282202200d50345000c440010350542c09980c200c1c0d08001100d0440721a1143c0c1d07a81c3e0703800c80e01c0e0507415500000c0c081c80e5207560480e40c84a18144008405d07070305411700c0301b40004580ca840204403038260021601e03030700d402640401d030701d07410121a0784045603800765624280b003405903c10074400c3d03000428005c0010649802031540b5480800b0317021290180781e2030400c1401c010180034040700200481d0400240240c1c4d504d403015544d82c2c1c014200680e84510010000d8520002016000d055400c02c3c4c200c2c0f0030b428025078000014445a050220340c10309000800c1c4017030f03010700c40c60490980c1501007802d06654982d0003000041071135116024850403400c015140c41c0c0481c45640c5031040c04111560308480c16070030042c0c0204640c9040e000003c0d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 759677374 1250 759676124 759676129
    0x23042a1b0501090309050f0301090302100c0507080403060204030c050d02300111120a0b010206070311160f0b0106032007020307030506012408060a0b18130e0f03030c03130f02 77
    0x10784403d01070700000d103011014055890000d4100f0392400c801ca0003000381c4882690082e4032005804a0b070001d066031516a00b00c0280900100c40350103901144403540c0e5034407440c00d0002908580010b40b807a9142d4180480c050408401c10566140c0090100030507001c2c0c00103640c40f0f809285000010142200420940b514003401000c190540701e0324003584801d0b00c5c20303802e4142c4c0d6004000705482070610140c5405a6000b2030b05a4006450b441c0200304031007201506501b40c85041d10313001da07204a2440c29000c2c0909902489078942c0704410b000c8999907541406c0b0191160070502611070b13008c1091144541c00214000c04120380702805032424103640c0d44030181081002d82c01441751135640710445214a60b075400b40d04622800e41071a01142c1030000208080c46910701840445240019402c0260034120401003c001c400510202c0e441d074121540101820300c1c0500c4e02d078603200c0c0d0703043c2e00d401c0c510110030f4920505004052900310f6655060240c501c0940c841c090700c0c0075075245a00c1d000341c0c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 759678624 1250 759677374 759677381
    0x60d1505100207030201080a090c06180f0603050103120305010b18030a0605010b0304022809020a11010921080c16030c0807060221090a06050604020423042a1b0501 72
    0x1e01550040d1582c589140005030205800408010140f468038400c103000503580c942100548011303241c03c641b031070080e800102d00c0c004240c02c001c0304144560000640c1c141e240e003296040e6841001d0590166405107001da0549500307015000d8142c1052007005100c04415052000c4150300508a624041007a16407200300c507001e8101e0f44803280d0000402c429405e01400c6041c00241005401c1031000700c4480c1140890710038092035900540010341d900240744907000c0010201d909100030004194103150101a1100c0092079480010300500c141251a001f002d44520914401d4400e0340b800302e410a00c0015080202d804500780029841100f01280702d0601828107103200380d100682d1281c2240d6902080c0e0000d0910882000c5088100160340d0004208801a59802040428aa150701000501a00a54001012410b1400742c0180d4024011800022070801641d0412200785800d121504001c600039088007640f9089a60180b4180f007000c07003198249042c02e01011000f0190343d00c13402d6 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 759679874 1250 759678624 759678649
    0xc260a051f0f091103240f04150501120c020c1005130e0105090f070c0b042334180b0402040e04050d0816030b181612020702060d1505 59
    0x703680b020828055038040f48a044041c8860307110080c00e51800c4410101c00f60120140350011540350b5800d20a01e80b50344505400016008100313101c69401408011003822030b80c800c59001542500100b05001594818003161051701c1d4041d085034000c1e4814032011004089011042000400040014000e0012050702800b141c0c02007030b415501d040104400208084c0216582c004030009100c3c000740c00c60320641216038490b0080a81e81c0d00c50800440d203400c03960441c98504580c40094988440209045000d503100c1c29002e501c0342d07040301c0f20600395013055022481c15024042c041c40304904c090324100130116020804a130a4100201113002c1c0d030801c1d0711002c0e070400c4000c00e0104010040c4804e81c024400f85ca1b049041c3e29000f601d40c0d41038400303001b05c1c0c2c2c107060340c0780d162412303a440e5540b80c001c10b4800740216203d0f9040c40e06081301203a00e04074002c4001010b030000c0d4200d101030340c002c48030101c1e0014281404d012000c800302000b0000c0074a0f25510346200440011181c440102204e072 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 759681124 1250 759679874 759679889
    0x12131d04061a1c0507030605070c020406090903140319061401030e0115120303020702210d2c0402090d030909140415180c0305010c260a051f 62
    0x815040500c0c0410a90700912011507105200884915041d29102c400303201c081400b408041c00c0c1c2c4020f041c001d00300503041e007001e4030850403c0c0402c12950b40081180c2d403001d1080ea000c00959035140000002c550240b200100041c0c0480181c04064000001450700034500c1d0755280d442411403184e4008861a40c2d1010380302ca100e10302d03083e001d90307010f10030003074110060f20082c0549140100304103010a4203005080510749084900c00034503100f903044d10788050b4041e00c0301314140b800c185050034103100e956000039039207d108100748140c1c0c801c4071102814070b648902001c80d4180a5404116501c12800c07103900175a0900005130190b56084d090020507010307465070030b4490308200760b800a40b400d800450900b40c0740c0c0c600703000000b1103400c1e04401c0118440c2002400ea50a0f0844000c0301c0075104015161075803003500030051060642c4890348540c032980b5080c08018140c41b0940075203d401c2010910369100800007104402e103504400c0d0320244120341c2e842112031041c562a01c00e090b5800646 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 759682374 1250 759681124 759681179
    0x103120e1906200a082a01051e0c09030a03050c0a08040b040e010f06123204200d110109030212010213120201020d180512010b030f070b0a0c02010311040602060a14091213 75
    0x141080c1000d00f0300390030604ac40e4516250440304004250789040e40b07000101045000242050103000520081110719440107016035600d940d605209115042401203601c01d421120000400b91050b0f0001c1c02181c0640d1990351a130030482100900401458030b00ca145048080000e81080c000008442a01003080c42c1003042c90601e8200709110355004010806200542d15655240307030764185600c0b0700c80303038807500051031840c0c10001200c409980ba0b02c029002490038a00320100d14040d0042c04444176024074203c0160365641e41c811302400c602a000e4090b8000000c1e1040041c85142c451404141706040c44407d1942c1e040420b0791030f40d4603800d00c40641d6499048804030b240a01009620283c0e10004080590a00200c000f240c4180c080203000d100d0200780712421a4002d400410b00200b0480810751101c2d0384000194588a040300c0300c0303000c24641008007032120300c14652640600c5280300241604075454038060b41681c445600c101030307100b461b50000f413031403441c00e03018008150915180 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 759683624 1250 759682374 759682411
    0x1b081603030507090803040b0f1b0f010b01030902010503060405060d080f120f0405071509050303120411180a020a020f07030c03020112050103120e1906200a082a0105 73
    0x282290701c0908560100104c0f00c80410840b000001903a007640e62441e06103650341e01c1c01754007288074411108144c00200940301010406000816410301c48075492009000c2c10701c0d11801142101c8000c1402804181c0a001040443c03c10707510890788820040c00040d80c0c8901521107298503000081800c8680c0c500103692491414800c540940041e00f83c1e0010a660426a680c1600e641d4603006107a9403824050340c0403201881a643d00008000290960b55104401350414010740030031601a01d0b0a0b00c0c0d00190400d40c20030024081460b201120070341440c0d102c1000c410081e511400d181401c61040c1842d01d90041410f00014000314400c00340402c85c14594800900816900d40d14030004500c0c040040000c901311441054800c6c4251514009200c8184000b03002c0b9421a2090000c1014034800440c0316074109044003e101c448aa1620f40c0d20041120f4039600d4440303080c0185203081c00e109005500c04074030b0380e04401c00b035009401801003201e07130310306400c441d000c4907036016039609000c0701c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 759684874 1250 759683624 759683627
    0x50111031215040b1e0a0f1208160c0608390a090306020f090f030f0a0b060d05030706061a0c1c0302040305030d051b04210c15020c0f010e0307061b081603 68
    0x1b240041100e074845550301d07450581c584c0f420f01c2075030300e020706070740d100044902d100c00703881d8080f248460b440414588051784804004090b004100c0e42d04800c01000f084101005015079001c50300f8050880804643ea0107a140340d00c903d4000381800c00c00e01c01d408502000003803072800680400001c0c18481501ca005080810100d100d0740b03150b0f24001e420524052051130307004940c02c3d10351034010a6051003900d5000203d044081c18503c081c0c6180400310b0307003800b0003a05030001030460700c00c4841c1c000010070a4240046038420304103008510b038424501c1c018488908042c100c48407255040060406580c0d88807541141c0c861115662281e1f07072401009007000c065840384088a45407a030785400e290400c040324500700218020032000c40e030603040c803008000d681010940640f80a040004804d400d560703010b590b4800c0341812601c00c0d0484400381c2d011794450032a200c50110000d00424515180c20b0041d14886042c1600070505003442030710501244040c03000700745020706c1c28680003049034141070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 759686124 1250 759684874 759684889
    0x60b0c0705191203051611010305060306010b0a03050a021e0703021908030c03130606060216090e03190309061503150603050d03020f09030f07050111031215040b1e 72
    0x40c0c840c94001c8001440c0020151100d415941901240d42003c1001c0c00d040d2224041c2c00980c0c150244084920001c01c01c40c091402c418501c01c2c0c0f41171201d41c03680001c0540329282405075014507041070204c80d00907442508420741007407065000604c2e014a91182c0c0d0740c0c255580c1c12034542a58005603240402d98108217405004100d50a22641c8590340e0f5240080c2e44000740850280260104c00301b071307003014800304003000d241e481482040310f681c3c2c403c00a5142e00141100600344240700c10f001031354070228090b140b8101000300255280c400440030b60b40d040b84602001e40201540d481c4540d0000f80281f28112401d8500d10745001c81c50320f9854025548a42d840d50321140a042c840104006040001e134644400710605000d6103500003410303034980a004800769141d25120300b07000751445280108884003512803c0e61180ea031105c070360008540d41e2280d039240b00080e0418200180410100c0b280c40010200300030400303c1c000703007608005001a82290311090300c03c0010111541c3c1d07454100e4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 759687374 1250 759686124 759686129
    0x9121a010807030f080d1503050d0e0909060a091a07091401170c0f070c09050601110303150105090111030a0906020c2b2607020a1a07061509060b0c07 66
    0x10002d09481d421551000c0d0410500c0c074004007140c00214003022458115006514040b0700f0290344100e469a078200296684a044000004602090144413140c241038011500c15210100100b0b00b0380c1711107828100806403c0030540d40c11288a0101c0d18482003680d4550040c071440d0f4070415a1400c04a00d1030f059541c2414030343c14010001c0b000f042c08511460001c2e440058840c080d03844520380e000b0804207101d03c66008103801c12640000ca46282d03180c3c0b0090242c0400c1e6201040c0081e02d50705140d80b0312003522150241c50818075246442e6110b00700409103050189000110325088401152468214040d0540454240a028000c4aa040010b405031003012249003544100d004007500d11440c90101c00004250b16810003801c1c060340c080030018409450780101e041829132000781100ea000317104102e115003807550001a08030b400807561b03518006044c40c9145800c680b80d68400007800d00d1b1208141c4881881e2000a46984a100d02001000c0b6594405c0d03450901e9000e0ba400c1c410300f034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 759688624 1250 759687374 759687389
    0x10b0301030317071119050c400504140d09061b06020c0307050601030c1203050a0f0201060e0c0706061a1902010b06030a0906050f04030509010c0309121a01 69
    0x1400104042603210400030740c028541814080c10b80c6031008105c03085203c4101c00c0e4441e200d42103101811110040711021114040c10945202c5500181000600d108602050301c02940a0a00400038090b44030120001c0031003100c40840c01001d1802003040d41c500321400e80300f0b411082d0f00e44c01d4014003404032115442042c80c080518900300302d400b614816854102d01c44946002f1004010081650704031b808101480307089946440482c81c0c0366549050134041103c00111086001030007481600c40c01411a90544550b42009110602201d14140d400c54520440d903c414001500c1500d40c40c0c03083c00703520002e22240d0380700f070a03042c400e0581300183e010320a0300508000d44400000da8200780da041030010210391856816800f0b0880c054058002c881d40e1110000081c0414a40d190384484600c0c0d20810b024019651049450070301e5640444010740031400401c034440b50b9612070044240828880c0c20071515030b83d142d400114440440b014105c43d81c08040700000c0d102c501c80d012342801130008 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 759689874 1250 759688624 759688627
    0x2101110053c2a04030b06150703050301050d0f0b040602040501030b060301080c1c0602040e07120b010807050d02250212070f060f0306171501050d020616060b13020a08010b 76
    0x1a0502c41c40e1a80000c003615145201c507407043c01880641c455400381400350300032040d04c5036200d0400d060700c2c1d1001e4400b98403504207001e0f000000305843c1c080e20041b0b0341544416045030310f032006200b800d400000084550724428001c0c0d10015071010081401240107180042c2c07124101000942103c0c01802c8030b501c52041400104081e01c070010761001251010f40340e900d41c840451400100300c00300310000130302c40c80c00481e01282529058014510500c4660343d1700031102c03d0713041c0b8031040f5086101c400d4001f6101078002040c00740244024079501280400052811800107541001c100c54070109006004095600c0c000350b180c04050101c60714013582c0605180b529156104010364018850901031207180180306007c40e0090348650024501815860440d80b151072680ea2241501d41c401c01041c040c080c000b2482e8100341800d01842a8040c06142c038150342c04400911031100f00300c00300c40036a111440d40f01c003502c446003841c0001051040150300c4803498a4040d00c0c1140c16001018500d80 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 759691124 1250 759689874 759689971
    0x1050103021303140109080d0b030618100506030709060308070212030306011d062704061509031112031209070e063019030206090a0210111005 63
    0x110b41c1c0120044035404180d0642c801e01040026024262086001d4040200415000200c01007a0070034400150304505540301592401d6288000d0500c00402d03010f20b50000c1010481e1030b48662009400000080c02c4542c40c0e640c410051013a5070054000300c0380604040350304000c50400d03040c1c1100e801c001502441c03d42c90300070b0000b0820003600b1929441e00301c02205074003451b11010112a00c1036050202000c40889460280c1c0b44820b1111005004500c3e0a6002034140102c0310b0748441910030740d440665013403171a141c01d000a00351640341640a490521000d001040805c000c0002080c0c90b40409040d20b080f071102410a03030b8907031005080791103207030804c4040d0707071403000048141c406031840746072128800451000043c40700040300041c1c032410b40c4240c003e881206000b10543d10075402c98015030703540d009903a180c4140110081d04056010742d00307844280110b034035200041902c0210341403c003660138409c081c5d850036105c00e05412540704004000c0c0780b000085445034001c5011304c001c40d00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 759692374 1250 759691124 759691147
    0xf0605040902011418060304140613020307060c151416090501091a07140f0d030b1507210e040605061206060904061d060405010e0408030420060c010606080105010302 73
    0x2821564485013a52000515200e0302d07542c0e107043c012808003d03059070346030714042c031301180740000402042c0610f1003140d0010700d221429441400c4915409005890900c1c034040c401d0310f02903c864000c403090004230116822450462080c00e22154942010340d50500b881d2251105c4108502d183ca82005613050b4140541d0760482820800c60320f0303503641c98111025000d408450f60161060003400b120790740780da07420b031020001091448190300c02c00352111240c42c01406d0f0112080020b10303540140d80c244556250f402d05170080c01403103020b00300c801710b0013501592204a01e00d0100543d004a40c4081f40c40c01c540c20280310760009014140d03040c0c1e291042000e03a15801a0b00140703007602c203400c0015444080c0e02d443c4c001c0380040500c01c02c400071002d20301e490032071003c00448141e40901e203040000124208085041030180b604100301170315680305c0e6120381000186481403a5260341e441c84840c1d0854540030b00410b031031010040002401420a04005c04139907040c1c1c0300604150041c0300c80132010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 759693624 1250 759692374 759692387
    0x70506010b0f07020622120b0420100203030a060b1c0e030c070e010905101518031203020307030c0f02030f03090a080310030b09060c16051606030f060504090201 71
    0x444092641546801c014100042c85100f003e00c000c0d044140411480340d007203880002010259042c018000485031100c403070902007240f041c0040d08909082000c1004075807410b101c400010700781c048135004030718900e01040c116006a044500168000401c04c41446154421140a480c034544070a10340070721922032003049101c42000100320703a40d034440d1009284d800c004440841d40038405031151a580c0d40340c481c400d038800f4480c2000c0709040000042c200e42d0140102401c0d1a0702e82d5800c00001c000c3d01003210901080e800500e02120481c00100102d41c1200b40e5403603410300341e030300540d0761700e0410700c014103481c1100b40250902c8001c3c40075000094021054410001881030000e859548000d406440c1000c035180c080c15441002062200e05010b00180000b5030740240b842c0da840780ca030303818400c1d6100c0b02116001d8901900380b00b5080140c4010081c140e909000b00122044100410407207081d511040e0f000310042a1340702d10402d0720003004d004101c010320303007241d0410180340d40e41c0018045 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 759694874 1250 759693624 759693629
    0x304151e0c030e24071412070323270904021315050a08010c020615060301030f06090b181207080d0e0a0c0e0420101101020903010216140307050601 65
    0x7800010034020303c482d10340d4054418001c3c01007504489201d0051800c204a60204806842180381109040151722001451001c006881c00340c0a141c40f4039618105c406c09643d41e5500307590044681402d0010121401604440703002d0010119000541d000c200403080c0784021950144810b0010000540c2c7c90000965001030340070404105207113550070410216042e5044264040000303100440d44010540c040e5100c1030303807502241d085448507140b449105280b561340d254002d0003040148005440d4401e070300405480b4070008141c102080d6a901255072040720102036540701c800181194031801c0000b4020310090f000094a44030380e40e1110000340c441e0103da2030314507468411144003160100006190681c102c03094901d4a6140e120f9007414070000d0750191110942c0340d8010140c844d0300c09d095001803000902c4ca0310340d4031820030107460850751185c00c00081e540c24094441a1380b800e00080000313000c44150b000c5049110702d42020103001410055032660f105002600c0080e6002039510306 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 759696124 1250 759694874 759694877
    0x1501020c0405130501050408040f0e010e04080906042d09020f0f090f030a060207060b0a05030c0f0103021e03061201020a020303011a04050a15030b040b0d020906120304151e0c03 78
    0x542c0d5a56034040c250012140740c008040d5841e040401060240301c002810a4564240c42080d00c95540c4c00c4451407000d0a000f004003000851011400255540c0010122030001404003401c00c0d640c0e40b1a0035012040c403803800c2d0071800a4000b9610341061206040141c98400350440c00e00e460040045540d01900503524010800010310352440c2d5903e92140d46030340301c02000c44440a0b034a00e4204040d400070001290b040e4101040501c0a00d4080300c141d041c5c0d6000390051890300032000802540e1821a182181895401c00102207660000b10240c3c4114000c0d40019950b410f2000c24482c030f00326092040b042c20307441881500079069000c41240e0445504454010f02803d086940a46c00d10030781c2d0201d5406101d01c40000740f006214000c0b0b0920300060f0320100040441a803c2c441a2281c8480f00c81d03101c08082494401403406001c125004071001d02072603801c070901c124480c9143d0083d00080d5070001c0e01038064540c40e03401103d0b18150425103120007000b00f16442c0150118008000040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 759697374 1250 759696124 759696131
    0x1518150e030301150e0102070302010c0201030f110c0a02030f0c090402240a09031208010605310e010e22020f180a0e0f031305041d01090b06091501020c04 68
    0x10a149a03800001694080c80c041d60360741e59481480714075081113200184040754440024004070343c00480d200382180d0f0183c4030441c0d0099183d0044000b81303103845400800c0755036858918200381451014008a04400c0d0051024082900406150041c603104100495000b00c00c101d0b4280c8841c2e0b403d039045641540c00f00c200c002c0d4030403031044e0600d40316120500144041078044043d035120034038604503405041140390144443c001260651000d004030008190104000d0a0103090030305008074005810011076454041e0034404804504980d0048041804580c014001b090441078400d030045104280241400c41c0140c45121066800b42d02070702c80e922039013080e800b5440307118491a503c00c83e4141c042240c81d02c1c0344c00304c0042a510901c002030b8031170740c512546010b80000495044008641e60001c12500e05400c010280c80c141504102025506844124540e02405880c081c980728002c5070b94185401814003003498001403505000120215540d2050398001c01c11701c840300c00a44020 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 759698624 1250 759697374 759697403
    0x24062f0c010e0111060a06030209010806040201021f06080f07030c0b07030909150506031602070b0c030301050405060d020d03050a020111190e0406051815030f0607050304050a1205071518 82
    0x140c4d1050030391120300303020b80200c100700304005030642d01800560384211900c0700940d072200350856503203a04030740c000d0140c0d10030802c01c8114408000402180041128041019626540b4190904d08400c581c41c1055203c00421300070441316810100113002614030303c0f070424440f80c6008102c664684110404140e640302c0680380c0300c90715840c5030701400c006000380c1c3e170346d0910b042242d080110041980005001d00c510120300e4034444000c48007040300310320007103003581d0800341080000d0801411880e4818145044080161a240d860780c034064020307281e194a5090440c40607003511320103182440c00030010404400000403010031a600b0210603d001601ca46014000c5401800aa0022580710b0b51010710440320104000c1e09511413034400d030301840201c8150701450768807516103c114040c1d820203800901441c0c4560041c6034458040c60032140004040d0729840994a90301c03e104c030010f100001c1d684c7c14030070007a400b1110487d4080017004403000d10415104414040350700207050a039140e03083c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 759699874 1250 759698624 759698627
    0x620030f07120e0f070501080106050f13080109031107061e0320191715100c0602070b060f100914010e030d031d0106051324062f0c010e01 61
    0xc0c2e040900340c042007008014003849400c0e580319035080c0310100341e110340007020406510910310241240d10586501c0d050102203084145242c0003404501c00384408460001910760317090180001781c90094403080c861040b03424809003440001e8004005001701146045000131489401c155135580138640010a103804503800303035140266155885c049a000714600c0c1c10055000c2000306d80400a0302c0f12400e64a0801906142110845007170043d0500700e50b48030100d042c04003031241803100310b1a1524a21861707980e000c0803a0040e480c142c0c5c0000c0c19408212042c1824000c290900004403101ba100280414000f4030510180c020703060001c10814001c104d59020307510500c55a00001c040d1043c600d42d60f103008000302154581174861a11034441c1d503954000610030b010503039a015148206507800800420040d04806811881544040030560001b0081c3c40d510300c0900040d9480d881804c00380300321408281c0c0c00e032819110818503580800080c040000301c00150381c8083c24540c411900c01d400 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 759701124 1250 759699874 759699887
    0xb040f11090705031f030809220f050a0c021902040b0102210a1b0f0b060d1505091204293703050402060a1220070620030f07 55
    0x340c26400031040c034144800180c000c009036110364105004610791004064000e48501c0380c9200c05061580d04100d945103030304280e400380c0100c4442c1c150540784450b60003070304000c40d840e600c42c04003459540c03024032a08a040307001340c1c4001105403005110b21a84003440554584642400910a070340c0d401c1001c032140d00a1058440403000303100030148181d0450f030404590350002e4410710020301004e00705a105142e011700c9074003c4c0e0b01301314980d040c1c010710360700c0044850000c0c04e00f56220941d01d594500051110a0750b0501000250001c24281441d0011618000c10180700302e01b00e440034441480388481c040c0002510040e4a02900720b010412403c1d000700b482403c950304030301e1246902075074a04e402500701101e529029907941e41e9110f11984120308848054030001d42c07203031041000020305840f500c074030b940141c5095000206284664240300024501d10601c1035051000b04540e000c0c070040388120070100130502c2c1c65200360707070380d200d03160009200c020204503041030480f0114062910405 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 759702374 1250 759701124 759701153
    0x9060918190209090715030507050403020a15031a13020f1b240f06040518010513140f071a09031b040c03140114040b180f0a02070b040f 60
    0xc06684103840d864031030103056000940181e00600e250804281034400010700ca00440b4a102d60340800c001036004210042c1c4005400c44040210074000440035903902d003c500f0041081c81550000180c51903005401d4889400400c40711108901c45d076405d64882d14000040c0e151030180c0169121412407072214070303010340095072150444503801518180b00000d0200c203180364000c01050400280b20190b41c4214085450b4400c5501d4000030810a01301074010541040340000f880b84c150b1411100b143c2120303004c40c0c0300d120789103c11040400b804846040320600f0f14503403000e01400c801c584030701551021036114040c8210004914134264407014825254201c8009050750103a001d40100e40c00072056503c1300780d1180b0301e440c010101040c0a840307030407010b0300345002452582c0c1c0391400b2800f010560540494100703403a5001845159550102e0100d0189480c05508081c10211b20400c0c540381d0007862149814410841d100205180e810000e41c081da110a028140304a13910f0020301d1004800c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 759703624 1250 759702374 759702421
    0x10521071d040b13081e0c0f0607092309221a152b0c0f090c020a1a060a0302060a03090b1e0606071707030f0f030b090609 54
    0x100036002a600700e41c030086001d5405580f40781c4464945000200c1d10a907011070080c4443c2040009290701480c044101e83e0072040ba42c03a00741000074031080541018001c2e0009015500001c08122a031504a14458054040d100d04800442e0342205074000007226a0407040c8647d40c42c40000f2a0b1a07a01d511145010b0b0985c3d01651a0440b989807820408410001c001c14444555000861203005214003042d44100282032018607400c02d0300001102c840f295186100009800303d02021405021403d0010504940e040c00d20501e0b10f1001421903420007040c50840d0003454042011070100111003031040c0407918103940c5911031000003501e030701072540025001407020864a01040c3c240c0d015038400340c0144051281507440150490407003008000b0a0022210b88020070480d040c20800ba040705072082e0a0f0500000300060060401e412401048000840144e1813481150f8003c030a00c40c605203d0505002c0c22400f900000c00c0c40d1401001c0138040e14801000a4844100f07409c80b8002c0c0808 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 759704874 1250 759703624 759703649
    0xf0903121305010f0804050309040903030f0c08040b0c0f1806130602010f06140a2709050f160501120c030f0c030e01060b0a050a080925090b01030501052107 69
    0x21000711291901c1c861041c14081140019008091409058968891684000510b20b802c2c0c0d000c1c01c200042013030313001c103030200740d81d4091180b100d213054440d400624100f03450b407801526003450401000c2000400500c510b078414042c200c50521003205450120507161901c80b8a40510303404508103010340240b203500508081c40001d41c00e41c0641c401e031200400d4031018805640c6500910403844c0140d002a9000b00c0d4400080040d211800b1030740c410701e4501200c81e46500c04020401c01a02c0580c031054809810006551808140411880f40c0c510290400c0007600382c58140007800400304800c0d0f4084403500c41c4160481a44031354091502842c071001c041004402c580b10040040a21240c994030300d601e402c10120303070000c2032010b032508000e03c1ea41d0b082c90316141c0c01e030444543c4c0c0f0250030340caca89101e0820282007440c200d1170103580318141090309210300780ca000c0c005020703a000d50030118141441c1c0401840703d52074941202e0924074042c9a00c0c203040d0003079400907240c0120395001e031802841c03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 759706124 1250 759704874 759704887
    0x1e0303030f0a0e15010504020d0608060726040f030f3f060506030103062c030d05010e090a260c010914031305190e0720120f090312 58
    0xa014206806076658220030007030f40e05007241103540c501207080ca0f8a10044020010800c0b494250000c04a4907094000841d9150b507400c5200d2800d03001780c07940000b05034808a03100103600702c0d501d540103402e640340c0c90518506041c0c440911100c507040024003000003252041e5031190041011400c3c9940a0b054819200742c41130f14405100c2041e86138881c130700507800f42c1400748a0039010318029500d0091000380307103074a0342e80e9100041000c0721004040b0501c1c0482c0c6100c100304c002c1d400400f40406005150741e500160300b28011103405030803d4403014201c1007030004045000070b0300021260301a940b0000c5209040040f1850100c041161140d940c00107150860a41c040d004014110320030601d40164003044842d1907100e002c0c00b00b02140c100c40403601000300c0c1c80d01c6160031801404001d0823090107074031811302d032820718412988500490745506092400c40340c00c0421500c4414440b0140c980e07020f0f0198800560f22448052800701c140c003152003502703598240547c6001c03c00a010903a9980b1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 759707374 1250 759706124 759706141
    0x151005060a1b030903030e0402040f12060b060f03010609050d0521040f0b070b0a06060c11010507020402070609050606060f070f06111216020105040804030308130b01320a03021e030303 81
    0x4409010840001f40c103541c6185060419000362020358805816030081981014041c41c43c800652100381e9516442e024282d81c00d80f5490020800d03c2c05081d05140e503581841c202030304440281d44042c3c052aa00060600400c5010540c500340103840407822221007001c0c2115840c41c021604140c2c422501c003c00016060301c03150003030012078441d05d01d003401b6a40341e0030300c5803c031141d40c4100e8000c580c1091310304000540f0480c1c0300c0001c090506215090042ca5008a022130300000822913240d40e850440d501400b03010000c46a0008084907410b140461541440c03009008240c801025400d1142c400030401905400c030301c5150b860f40111a4540e03070002c82c0d07110302c01d1056641001568060307400600c0d481c81805074611072030700800002d241501e56902140d015200401514141640a0300d06001940120700300d802040c2c2101c401441c4c0840032054011200024407104a10002c40e02509185e00c1e450f03407040c1202e404a440c22409644002a624142580003415603d07003c004100302140 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 759708624 1250 759707374 759707387
    0xc0801020903100e190501060305060709080118020123071a070813020109060c060e0d030606030b0d0c0302060c0307050a0501021b0c130f061802030702151005060a1b03 74
    0x1c0040701150980c0898242110880f010b14480a0f8103401480003011000ca4100441d00340e94410000010001d90b251540342c18184140d42950001c0c4c03440d0030420824500f405a084607508a010001003040c4550000c0e0043c14009070b4154442079403400da298402c150016039600c0b1703810016410301803444002d10861302004440c5040465591070100d541d045060790300020702a41070f12881101810841c0c1035032410300b0302e403040300c1d40e0382c84443d000d101c1c000030702c21018002041e13140851100d080c140050b064800300015580203110914000c0302084803500420100c03038060703075456514040e1008550544c822842d0107081c510a031400007041060560080031030010b0741c1405052240d083c0640c585620184441980c0221f40c1e110030684480b640c2d00c5505066081c95000031615131310401c000c081c40d40510101c030404d03408001c00802503010301205c0303080388086061162360b00e0700b074130100b002d42c8072800360501422020404c0150280550b400980c580c0982030440c4007085c60b0700d0000c000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 759709874 1250 759708624 759708637
    0xf0c0f0b0402040510030f150f090f0c06050c0717030c0303100806010b040803090f030127060501090606020a080a36080f0703060504020f090708160c0b0c090d0c080102 74
    0x40d0307141138000392000c0303040d80003c0140d030741c02082d18450050544a10341140341e19030043c540300e0351307910460144140c1403040d840010b22406601c0c960356a281440a0b400740d1541c032000a0210401c4400c0703450201086ca8825108182124003070a501006840d1960181c803103208050b100000602414001040001e41102d4005044400e96030301c40c1600302c2540528841d03940346500900c111001d030b00c1c043d4242c0300c01140103400010a0010504030422140d02851348485002c4848044000e009541c00740034094104100d050003d1890302c04005c0d41c0d41c07442c1c0005000360b9408182100c0070ba01c02c44111855400040c070242d2412420440c125070b03000802d10465900c007587c41d001460700004202d130507040720084060800503245841d1f0601406006004a80c055422103000010b80c0d6154196030081100d0390302c90f103842c6400400100194200c0341d00c0d000703002140281c0000a420180402d500c840100411034407900c0d560040741204c501600020a003100002c4081116401540178240c03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 759711124 1250 759709874 759709879
    0xb0c1e0717120a0b06070b010306090f05070902090415030f0b090316080405040510030201050315040f0203040f1415010306020f070204090308091005190b010512040506250e010f0c0f0b0402 83
    0x46211044c003080428480c1e00d000401c000c0b400300040000c02d00590010b031a450050380320322800b0905a41e0345041c111250000c104050780440e642c00d0b94101032140754440f4400308204805e55080d91200c5d00c100c00d40d030070000c240186150009104c40818000d48503100d03061851410302080c18640b501d02c541160051a000e1864480001e507180125007111040702d4068540078076540300d01220504100d542401150002e490380518003103640988003c44c401c81c0151b80160070f400701d45c0703003d0040c80300b001401c0c4940d511203e15949050fa010724518112a444040160f5a0b05940400c003103e01504801032343c464540b4401b8418075130030080480c810942202031f07603a09003100c06a00125107040c0c2d00b115503002004003000c904401507001088008050420070300b0980901040f009105003210204e4130380c1c020005115500c101e146100345080041c2030110a034502c3c0d224020468000a0f0005040041010384402028059400040c8040d0400204da00c00030310b40c10f010340c07504801c1d14201e0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 759712230 1106 759711124 759711131
    0x16030509060405060706060504050c19080601030b030604030906020105011e030f08040b0d0606021c0e01080601120f05160509030d030225030c0b0c1e0717120a 70
    0x2d512803040340c001c2842408c1c40c0502c02554000382030404a888184410040040e00001948140009142543c0103982d0742c00102e02500b000c0340c03810342600030315081c072091592000c002400e641c0b00350000d200c01c0c0d03a50040c18684030a0b08000c4142c0b540b0800040c00015540741114920074010745031742d03040a03150b01c603403091070388010a1707031042d95a120020001d845d014005008020007070710b880045450b007180054241d201508583d07042148160014009a0050050050044180f40108150186440c2c80340c0180170a565035640240f8402c06284000c0c8680225900070701c014016080f806440442a4042c1d08001c11500400200018124480405501c0c8020950080d550003100f80e000d82048048020043c254280f907080400903204c8456682c052081c00300e506109071550f130b1081d4100012121308940c1c803040781e2000000d908080007c8011804d0081c56001d4041 = true := by decide +kernel

theorem cover : BRFrame.Cov 759532374 759712230 := by
  have h0 := BRFrame.cov_init 759532374
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759532374 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 759532374 ≤ n) (h2 : n < 759712230) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
