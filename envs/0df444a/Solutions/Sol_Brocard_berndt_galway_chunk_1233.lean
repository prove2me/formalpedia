-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1233
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:54:08.922288+00:00
-- url     : https://prove2.me/submissions/b8d471b5-4cbc-464c-b86c-a1c49c89932f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 221582733 ≤ n < 221762589 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 221583983 1250 221582733 221582747
    0x22403070e011d09011401050c1e16060f031e1d0c04060b070f021f170f010b03180c1005040509090c18060105040306050903030f0a050603030403080706062112 70
    0x9401071031038031240e00300034061207014a0401b04506206050004101080050210f05142c058030102e130030041503082c240d146040041c500e803102285410a0500c070060340003882c118403130245d00700894801240201d40810440b070200c82100e01d03162140748c5000300000c2c813004100c106880c0803220b140c1c141101704000c5a40701e10400d01040e42c20001031300000d207015a0b660855000500d400e0400300445405520726411071030b04000030b02075100680c8000920302c0c2d80c1c0e0708030441240644983d810806114603500c03014190540c80c200e00f0445101c2e10307104000584a410024200159115141c4130181040d0824066a0322485213100041c040c280300107031079075440704000c2034018a21f1400c401c00d080e01c2e038064a42810442c0c03c10001c8007080c41030150902401d10900115980d01c2c009196107125500a00080106030070042886101c0d5000420745050f2030308042040d90740c0c8800d240044c014141c5030f0000c0c48900381c540703140c414100d0408040e08064002e0000382d0b0300c008000c400712101 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 221585233 1250 221583983 221584037
    0xb1504020c1f0f02031305060702010b0f1905061c0b03010b0d02150405030d050703031a0306180304030b0108070f090203060603180a06240e04050703022403070e01 72
    0x280d0700c481c0384000b0800c8200d00150900100b0000000d2220240208009a07030044480007044505510748100b00041009456404545480200001401100041e03403002e00c3d100924482c0d203032200302e0301c41140200b11090052100424590350340ca9281004100d044881029401140c0390068035a202d04040c01038819000c00289040700203081a403c0003c2501781d44e039081c0440c0400d22002c292528104146120000c0c80d031101900d07a000d924008060b1103190900381144000603800911540300024815000005044486440b40404070b01500d1401668005401c40484c41c0000a40030740c00303e01842030718600481c500c402600d6550172002da1000b03903105900540308100080c0d400d081d0f41b907050081c4849600380c802916840e1507807426551600040d14401107080d200d410000c001416240050500c0c00c1000030324a0300c7d8a4140d21100d8912000c0c0c040c0c5041c00702c2103401c000040203610702400c0b0b0200a5101d09041d080288400441d6131202d0224806505d010218040040002c880d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 221586483 1250 221585233 221585257
    0x2107021b0a030305160f08090f040b030606042d06050102070b0301060503060904020d060509100e150103060207060b0a030c05030706050301180c0e1e03011401060f0c03020a0c030b150402 82
    0x80c552440e40c00315443d501024240030846030a06140c4001b8080182d4496014020038a85443d80740d080f0401070039281c1d11010038821881c050044600d40c43c08502240d105a084a000500343d0b400c0d42c110a0f125100c80502002040c0800c28400000c4e01d5480b000680e802a42190f14098a904041100384000c1c0149400306405200081d6585032641c44a43c2c410310103860180507c01660f01c9a042d01d40543d5003440581100d064040c5044035445a2100c00d500c030070092814540402010952200600014050b150000f96110034400d06400001c4010030140081c7d0300641c1d241030441031030040e402400d02c1703400b401c81c0020700f0521801c1a00d041e03e03507140411120b40305c41d81403100109911540f600c141f000060b84402e107941c1d0b4200384990610001180d803901c41e43c0c60101400c54000425419251240d4401406484da01c078180c0480d103800d40c1480c00c0ea8009a0405a2030000810001420446110404020452013860301030040d81d007a540014030400300e0b010001640146440151 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 221587733 1250 221586483 221586499
    0x50103052202010512180105070509010c061a03030403050d030e0a0b06010c151d0114040b040807140d0507050d020a081c021614070602070f090e01022107021b 70
    0x7036100304800390310700d42841410510b19012540c1c0c040d0060720821902180c1310001a00c0c1401d00301b00a005603a8440e1641c40c003a0314240f070b1000080c0c004092900c0180c0745590711000c00d60b0280080719170b0403418100908803511680d50b481c04603a180654482c00c0b00080c140550719410860011b5680d038415408034114041d40d5a00c03004551a50104509581410f511040d040e500c0d0010b100340d10004001100745d002001340c403511f490950301050100d0000e400030204000c00b1500103281d140d0840c0d480030245a54140b1403c100c0d13202c8585940c079007000e001f80403d900072950401c006200151050b01600c40102140b0b038144d0325084000d82c05041e642c0d003042100d842004120096118120602d001810161a0b8075981981c61003460110b5030700b220300044060800082086000a080354401024140e0500ca0b0704000eaa010b8480c0504c49a180c4800008550080d010780c0d101b80c00b0420510100d01021210045141c4243c031060054000d86891135903040840b81070781464500a42024 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 221588983 1250 221587733 221587771
    0x3180c121621120e0406090c2c0f0148020901090c02100e03030703140108070603020a0c050d091401030b06120703180c080d0305091506060d110408060105010305 71
    0x59a1484407448043c00c00c4000f0340d10703515650704c0703100d0500038010031800001c2a404088020b81154042d42d0380c4414464a2a40c1c030200501041148a034003006447c409481c0301c008005139000a070501080810381810007015481c600c2d50701040c41149040b8013101510156040b80403030030010044040d40050100b001403165000d940c00a4010300807a10484028542c444011130031038031002440449070304004203010002c1d9060040003801d01020703444062a5160126441d40c030041e070301c01c0009140d004101e400342c150040c8503948805802c82c06543c611404d119000301450304038003c2c025072000700d04003080700354407c0c450306e109850003824a52800c8a443ca00390034401008001c0010143c030f80010601c0c100405c5100075900f4405d26140381c200b81021001c2d810224032040c660105460807041110603040094014421400d0407240403584d01d4440c0803410901c1a440d90a180d0307030a1409000c86161002c009108454251003039a03843d03600c4070011001d81d46c0a5500c1811442c01400e04 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 221590233 1250 221588983 221588993
    0x1060e01020c0424330207030b04020d12030209150c07030305131d3c04050f0601061d100c080d0906090303020a1e0503180c121621 58
    0x3a0003c07110900070503a10038441c4503401144820381001071800c1c0d580d410f81c0784c0e0009011900f9000d0306031910b104417000038880025581c0182e0f00c4040c140c1d00d50840402d00350b485083c140300703009e80c000904035581a01090090301952042102c680208074a0301b2410701012001c0c20f842c10601c0c01c2001c1d10426103551001c6072503030081c80400b28241d0050800080310000094201d03006040604901c800f403605901c060241541b018904001016664900765408202240a1581c0c1d4030841140456103d60a1181c0b400900f1000300041e4402c2134004140e90b07801800f411803c1c0c03032015100c0380c0381001c0c5040c0f0009002010046000c04d00800002d0f0008210001a0100302e03402ea400041daa0700c0c030348801055908800c425004030340d002944c400c2e0140d000750b0703c10641952840304d5a28100703c20380203103144070043c050840c1e5040c0e403d03d444400403c0c0030414130400010091301e0702140300911a07880712106000d00d0300920700110000390403425041021800003c1c016007051004241e169 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 221591483 1250 221590233 221590241
    0x607030e0c180402010908010603030e1005090a0608010503121303030c031101020f07020a09200306040b0a0305060708131a060112051302010e0d110d1a01061701060e01020c04 77
    0x20440035405004034048250300c070941c001008410401e800c2200d0300349800003501d10101d40e00100420b0341404001e2000c29044208410301d203006a6140da00d2480020b001c81c2c0500400c806035a001c0c3d04100f0000703115a000200c02d041c0e8130200c05450000c2e07559188200e251080303240c0360b0716600301c22000b000420f01420400050501904241c0401c0f644072060034226800700d8030020a0441c0420074506504000e096039020b4030680104100284c81043e401c2038508840450055a00002000030b0550701c541d0400210b0700005001c0705103840d00ca1400340d4644104407047e0b40061154800248c4144020403483d4806401161501c03030044c04030070011003144024452070600c1801d62203c0c000c0d900034400c0c18400c1c02081c000c070098400e944001070802c1c130440a032511904984604d440459541d40e1a00d07040542110050f2000c031003440d01e803142c0da20020510121855007800000c0941e001204858034100d0105481c2030f41e070f00d40b90203a03020703854085c0090060b800045085510700b000d80c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 221592733 1250 221591483 221591501
    0xa0206010515122a030f13110a030501020913060509010b07031e0309060c0302180405060d14340e06030c0301061701050c0c0d0c030318230d02060703 66
    0x5800c0c40d00461a0f502c0a840c001503d82c1101c00c11600c3e242c84510240d1090480b03403e0042038181e1442c20860604000da0202400e0340303012609000c00081045001054000c0c244c00142461901c183d4905105000390080e64440b4001c0c0d4180071140e013502020700c601c8087d01c01c002c140a09903424011103c0c1c1641000c04200d0902540604200406140d501501088583c4c0d0b030300855140c0040c5000350650348402d03460300c107140c01404151400e83c07041d04e032180e04460685002580c0d1340c0b0400000c03285070016001806030300c550821111092808240c1100b120500400305e5080300b05400900c19800280380181ca51a462b018107025403c6800c035040d421060003000c41c2c08054907030000900315030f40390b1f1000743c01c10802d41200004ac04c3c00e02850b40e0003030840841c6424440c2d4000d06c10780b60300016041f60108050502081c04140c025488040da44c2c41e04443c40140103050710b05556070aa11010b034401c0c82c0014040342281b00d000081807200401c45074041d00e01620f400e00181e0142c2880c02d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 221593983 1250 221592733 221592769
    0x90803040f050309041503120311032d01030602040806010e060d0312450503090603190207050607030509030703021507020f031215060a0203070b0a02160507090f020a02060105 77
    0x419076a0307550314011030b40c2c1d480c3d020740c6c4102420b280d4501050700289084440b4241800d103d030a26078444034200b56544a00c0000ca4a4006507a104034500c0000010102d14001540300c000801070040c5c0d40c0c0600261000070048850b180d8807400c0100080b1000c442150744103465071085800a482094100d82282100c1d5001c900c8140c5805403d0480c10094200e0340e155a40c40b6140d030b062008190903013180320100a00c150781c0b4582e5164243ca0388680c00d0254042c40b000000701e00c202401d222301c0030408a0f000307411929501c1c80d01d020768035200c054604c0d500103814440800c00300b040c04000c55140c02c1e8140c004181c0c01c0f500c03800400b81290024040819800340b144d9001c900740f0b09000925415011002c040c09524145250744981105850003501601c401c0c8100e000a58000007240d1100f90401031424050b0303921036000000c2d10826000c0c12401f111740c1265402c105d070000c0c800043d6034840c075007400480c40340300c1d048049000d80d210000c0140d0049004203c7e42c1000c0c150080328408903 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 221595233 1250 221593983 221593987
    0x1d150402090d120206130c120c0b030103030f030501060503150d030e0d080c06130b010902030c090a08010509120f0d0e03161a100605310f03031101090803040f0503 72
    0x2000095a5031111500c2662400011643c500c1901c3c2d0600840798044409040f00003124413980701e80c403031991540501e442e207050216458041c496403280b0103008100344c4a03034658079a102d05d001030558020071000c0c1e011030b00740000401d44501031415244201002540003c054080700c00f085140300c148803081c1e091100d010541142c40e01d0346210f210045c0c6c01a00856030781c4111001032850082c000f0305065400741d082221000090850a0441c11100200d80150300c98030f611071b9a006a210700300700301d07900c009070000001304600c0c1900030b5482000c2800c255040310038002c07148412803007003e180c04040c1008220908a40d033359603001640b24140c0e0021a428921030349502070720b540e4841420b80d200300503c0600220301e9910410194020f01303a09040060301d2601c0390180c40d0740954620009049825048a6440c000071244444000e900130b0144481d50380e074808c240809280da0200fa400a41800741103200c25005004142d005a88218554910740d1107444200b044004058125224001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 221596483 1250 221595233 221595247
    0x20c0d12110316050f0309060f03040c0e040309080c010e240f040305150a0b1c050a0c060f021006150c0305040803190f030e0604030503090304031506050a1d150402 72
    0x4001502c6180c03000c000c422038907242404c0541c0f8000008502109992041141240e2a2100d13015980307107900f002007564803a20ba0b850b0207203052901d86c2000f4121001c0f10204400e065204180808842403203003502ea85a0410004481e8a52040c074081d811803101e1300e040642d1400c1c5400b001700c41e40e0080c8618102142d015608042e80d000d40d10030344e12540f019801001200c840305003550004084e070010404080400046030f0408051401e296101c4544220701e402d00405106903611190301c040420321450f100c400140c20820313015003500040c403a5480030307407590000d442103006641504260413541e01c50080c2c1101d0000309848100c040110034440001c1c2d044003003000d4038604500c0d0307600ca0403c0342c2002000341041000d680c00e000b05814119400b4198800fc00c0355900310390945040d0340c2c2d80c0d0743c5440e43d0340340d0301c91a400107042070710307001042408070102c0d0712010640302c0407220003003d0f0759580004880c024410f04589008500440401d001c003042144003504060084d1002d818524 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 221597733 1250 221596483 221596517
    0xd0506010201141605041205030c0c060418050a02090415080115031a09160b0c0c01080f040b18070e0609060a08030a03050702070302040608010c110706050406080a09051e0706020c0d12 81
    0x44038174801c440c2355102040c1d12080316014084090128400c0c0e031000e080031710f00030250300c904060500320414569a10086980c83c3c40c560120b0301840b4001d40240604c0d100c0c1c00c144102c500940c42a102107500c0c0c800703c1d1940b1403130443c4170002c9075042aa02030515024015401c40100c000d4141c5c8543c0c4a460300d03400030140b0089801004024001081d83c0f036002040e001d0341890a18564981082040c40421140c1200424016001a08000041941c1e88d5448009640f06105e01c07103c102071103182d100048003140f201c80d440c403540c03003030300e888450b600d44c0e90a0000842540c007850340140c100784640251588a5401954003c0302da04c1181d074003640d01d03000303d401c960f86034104800c1a5142c85005547d1600000048004a00200204611450518010a5405140900d4042000303807008031340d084945070010710405401506884031180c038178040c1344141c0d401158081945c055000d0000748035001203403000b0420704c042c0521520301516aa400740c40c280f400c0000c804d128100b14010380d114 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 221598983 1250 221597733 221597759
    0x18030a03050706050109050c0a0305040317130c300807020a15030b010c0c0902090f04060608011502070302010c031209140d030b0303041d090f0d050d050601020114160504 75
    0x40d00039181c45640b04003074104842074a205800c9414440d0603c402e1000802c0d45c00c085580411462800040c00d0300c8500d07040340d0b03042d040506540352041c8581481500020300402501003881603814400301c9075506171295404406040a80d0a088142c1a034464800d0350440e4541f41d511903a2410316008407940001c0b039000300c3d0b80141108610025000c4000c82d01881010180042420600f0041d402ea41c0e41d6608080385009484902d030300800d00c603000d500d5202c100030301500010070504c586a107918000f0712082e000d100d80000f02d80048841c00c5003d00110f0207000f03a03501a52406290b8007962402d41d5011000c0e52030032443d59446e200000810004028003a0b001d0084000c2c0c401c104000e9001415920359a401c181f00360001c020801c50038403005108920a588070541810359a00c04050b00d007031884103805c25110b4066442ca1072541c5502000a01704c1e001d24281c200140d45458004900321114180d034101c020440901244916099540f50b81220040385405841d150f12440101d03a90 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 221600233 1250 221598983 221599003
    0x3050d0203070c05010507150c090305010e0a020a05180a090807021207061e2003120a09020901090504050a031d031207061a030a030e03101406150306030a02061803 72
    0x10781012800204200c1e41c050000028002440c003241080d1541c1c4a580381d00c000842d200c80c030075554001e2080b205004400000007183c210000300304d5124002d400030b407280322041d0200d01c288000d40000c075640c40c1451003203060400030b040c02411942d50b211490018042d00009a8002909101c1c07000103941d00507a101d06000c010024003419840d00d080a880c181c1180c00484240d8801c900c501c068076407100049130340014800950101c00c0011181e28114031607140c288401e1000001007040c2102190421907044d842030b41c41400d00d03130303a8038400301c00c4640640e03005100750010038503000404e1040b03070482100d010a500700c04620085200080c40c2c11380d0006410042600400d083d07050140a100e182074180750801070150070040d680c006501e800008000030140f000504805034280c50812030019074202d02e68003004803410811031a0b4402c5003c6800701c0c071403c00c420f112800d100d0308000f034138001c10016005040c50a01c550800000360400081d20a0801110301290807507507040010340c8030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 221601483 1250 221600233 221600237
    0x509030106180f0605091504090c0302040509030a0e04020703081306110301141903030f111c35010b09030a0c030b09150f0606031e010303110d0215160903050d 70
    0x20042c80703c01c0402520a02d0340110311482922042110b0140c1c0740d584148416400c0300c0014400c103451410010a004076040a900280b9180800c10b15940c00401000300c3c0c1000e0300d5094a901e4060200000e0344140703075000703000541800c041b84d072a040c1c40c0c104824232407240c0d501003003098400050003082e4209a110091192200469000605024425000300e1403034000700b07903403181140c8024142c00c509000070401c000d0b4513003030218581c03000d1001000340e50403040c90f4070580700481d000800c444140d0b1401b040e0004281c02c050119600164107180100b52030504e0101c40c0e1900c8880200c0ea04252026901405050821400680c0440d1004059445010400082d08000c24980c0c03400340e05c0044000f40099440500041a504061895016804540c40d907a69501c18100c144281c2c07903011240d00100395500044101504802c14028000041049a014a680000c12a910110100c00454246d10b941c04544040050b0b0260712903070815040240340341d540e0340d60380da10b44245a040200 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 221602733 1250 221601483 221601491
    0xc06030c030b0409050c04060b040f06212904140a050705070f061d030307050f03150915010f03060605090d06020c071e05090f0a0504170a08011406031006050903010618 74
    0x201da00d0148038400c049c003240c420407814542403055034403100003240a00c0703040c0500c400f20240c6164640100000c2102e0000c400d000e03070308521040c0d110300501813400c100f0240c4a02a0403900b8101489000903007400c1c01400b140580300c0c90000c90003820b01030940b1301000410403c4401142020f140302a44a03c0307140c0000321903100760100c118080c0082d6040c0c040b6001002402a81540a403c0e111210407001486035251104444606160f00300c01840d60462514810090141c4440d150101120020780f0742c11030100b0030b8201281102c3c03031401260040b8005002c4504281420700d04858880d01c1a1030041c5481003180e007151a0004c981c0c810410b18220300003c00191064041d014024a01561004107030f050088050b12000c00041801142d903913940001424490500a01d030404505c444045959021120000348822800d02508074050743e5000d020700d040c100001103900c504140c0710030b0401541464401ca030b0903400055810307810740d01e8800200d402c0c2400f0400a00e81030340703c01c00103 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 221603983 1250 221602733 221602753
    0xf0b090f070b0d0c0e1503100314010c0e030f070e06042417071d191a03060112020603040201120e010f2702060405040b041407020d08090304030c06030c030b040905 72
    0x1d0311001c0c1007890800403024245c240584440c1020f50000d100c0e51820340d102d940b002d00b42d00311224280d01c00b8001210080001a45e000c06500110030300c0c1c4150b0703071505680d40c00414980d80b11030a401020069005150420203088070f488070310340004000380049805c00d1401e01135800c0c1c048405013940c23090000301007041421341104468510010440240120a1419044040c001c00f00019030041c040c0da84002490054914100c642003215580c0c104221904102c05c1d03103400105401083c00b9100301c80000c03940c10780c44074281c4d00b410384c0100507500d155156401103840742d8202510746000e513100d040d0000c48480a0250040d00c1d0709002c070000b40e13a00c02c000c0c201d200c00d43d030710381c03400000780e8403146071001d41c840800312010745205680c04119800300e40d01141c01403002c0c820b03030827200e110503080c044617960208480c050900700307680b40c24094079610080c0348c8070b00c038500c0b0082081e0751201c0c0400030b240c040e4002074410040c0703040004104411402281c01d40301c0030181214a500030903590 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 221605233 1250 221603983 221604007
    0x906050f01050a0f0b041505130303020102030133030e0708010e061b1204080f12040f0605010f060203220305060a1b02010b01020a0807060b0d050c1c0f0b090f070b 72
    0x3d0002040034070b5590714500d24240b105d80051042d401244008020390078010400f900601c00c43c0d2006004030407001c0c2603940c07420300034000cad082801008450710340ba0110398202c0189c00088040482000210003051080b014103130020041212603940e10301620317a0001d02d440c800c2c80b41c9200500e0010140c03c00c1d29009510a035006011140d40c10901c43c10b00088030201c004051062b401a0320004560b51140b020301b01150b0b60150190100030300400b1402c00003000300c10503906d54014481e481c28041130340c0341d803108513280490340107400c01a8000e000482848030340c050007004240415405204140d181c1d12110700b0310300104d54210784d8a88034140c1c920f40401c0007282e4145801c0c030b44020000220701400003507d5110300c0001420a440200f01a01844150341c080c003a01040280111501c2416152658503405032880452007020002810407088200a0941140d0b84d8070000da03403150802a980c1d210400c0f0090051030461040084500030488100700750400340c00312404145d1a0440e910b28 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 221606483 1250 221605233 221605249
    0x15020304062a0c21050903100204050d110a051c020a050102060c04090e03120907090c03020f0d020d060b0f07051b060f0f090a0b07020f090105100e040906050f0105 72
    0x400d4541002020040c5040212441101040c0a192903d03c1081c80c09041ca200001c4503a03a40855200c00fa081c051061a0424010641c18000b601a100398558444000080b40181d20a0b560049003541c000c0e030025900b0550b080607000018141045a40c4400100e5880c0700d1520840382c01c4007500c51103006524081001030024413007403004081c0e900d810303c054502c50080784101c0300103940301d802103810780d0805d005803010300034204030100342490000c146990703800e024410312100c00d203002c4021841c070b40720b070003241c40e0042d80e041240d180035032035a0481d000790b005451611001d0354a138804241c0f4000e003001400a100803601e010b455070090300b082c3d07041506d001e10148410b1180319001803280c031200e06403075441c0c01c0c0721145074503401004002c0465100303c3e030303456602200d24480482d800ca60800a800014026100950825600020700180410078001c40d0b6001ea6921044018144140c000702c80307200c0040c00110b4403544541d1142c00380c0b4011b0b116410a000341d800140a03500b04410 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 221607733 1250 221606483 221606501
    0x30a08061807020d0507060605030610060f051e160c030605061503060d0f021912060c0221030703020d0204030807060c080408031b090d05070f050a301502030406 71
    0x110700307064101044040e5032440c03980000d80034003d0125026051054550001d4024400601920a01d14152995000d024903c0c014580420001c6092402c2a0b2081083d504041c1c07000c03400d849444100701e6003c610750841843c001c900c10000c003440002403480c100d014021407084201240c1420054108800340c1d81c10b10381401200d10074070030040907946540144071207a0304052200070b000302900206000c524140c3c4d0302030b801c120f114800a0f40038220910301d1001409120100048551010100c0e15008814940c1c1c0750116809940c1e400c002c2c88000864201145d810018179020401d103041040e600294810b540340040860001d09001d0140641c911070300f2580380441061519a032429a940800780c115410b076102c42c0102d8070741c84110030442d042d0480040c10740310603017010310301541d0b2582c1601070340006994401c03002855040c400b12400503038910729440b40580504504060205221040c0301c112101c2038100040441c884074a4a180540c10460160f03032032406040c42030a0f204075013 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 221608983 1250 221607733 221607769
    0xa0c061b020f030a0803010e07120902010c030822030309050609071811041214011d03040905060a12050730030503091002040f0501110706081306020705030a0806 71
    0x208451440c0c00e42201100d0006904548142e0703010414000310749040740b1500000c004080020010a82c440c0c65045d00348990071550300c1c04140e004c1c01481d0340a07a2394a0034000c0c007044801c038000300040d00408034240e101416a5103c2c205100ca0410130754003801084060340440d03541d41081003801000e11819920024103002469054035283c03000c1140803445542c05c070a280e4800f55405404942000c8034001c152101d042400b010142c240807922005c0304c0a0b94006610384007071982440c2030010780b141c058090038051800c15181444590180a009107069030192030500c0200f10328041c0b0700780e0680705025400500200707052002000004000c2da016520005400c124850701c00c69041020220907450b24015031603442d048051841e2507880c0c55a169114000314022560b00601440d601c21030b2426600c6001c440f500085054498160b0b0142000003206440000c5101a00483c2a403202c1c0c42001e005251900135202e0500310b07040804d40c40d002a811102b40680d5151210340300c0a0600300c8 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 221610233 1250 221608983 221608997
    0x2092803150b0a060507080715021213020f0103090f02030d0201020304031701030210030e0c0a091a0103020906041208070b0703060603060918030320030408040611030301060c0b19020c0a0c06 84
    0xb01001694110303c40c45400104200003429801b08680e071800c0c1c0b500d4a9010a43c2c1095140381e07142074021390807490103405126540e000107034480b180d0016940342950040c0030000c0000f5024011030282c10300c4401500e02d81e4201ea01a00143c034100009222415586d00040c1c03281414a00182840012030b41e2050340c03011a401803016a82c0d000c4c4442d15640301341400100003006c48000c0d0304200c02d0640c0a60311200786100054032222035005481c0c03e2440741121800243d00c400194104c0c015401c066402c08010310003800442140e080703444009000385040350802c0c0840e0344881f08000106c86000000b511030f14208205034050007014082c12010380c0a00c0310b0680350340d900e60702c400c81801c090105a215120710803160500d400940140040054980c6d03207213024200220198014494000082c80801c504500801c0c0031050300e040e600a9034800848416640301e24070741c494090500914222021814141d10b0306520082c402000c1c80e40282001c00c0700c0781400060180260b0190042c4481 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 221611483 1250 221610233 221610251
    0x10806010608040c050607030201061a040b03040f03140c0f2107150e0709090213020915090f04020c0c0a050301060b040e0910090305030a0609021206040209280315 72
    0x4201a8107440342803804522954460600a030000c840c1d5015680040001034554140759043d00000141d446682428051a6203c0245002ca100d14460b404425000380040740c0020391190b220340c3d01d140a4544024200f1000d5407901c5181e02c011074a609580c03281007190901202803101d651402ca400000454900c160850307010705202d403203401460106090417000c0c48000c154002c00000396040f0844074001e8440c42800700600746400e0684c030a07030100e06603401201072802210008040a4403001c0600080c072940001030f00040f0201c0c1e0320450103041324000f0344540c8090160008600c006000440c40d0005220360001144c0003503000f81d04220051100d08103d2044a04031003040ca902c40e065130325840f400d41800b075404808117840f81400701e01824541d020020b980144d5a51404000040e990fa40c420120f1052050300d030400c04a070350010f840f6180036805051810000f034011801e045020050400079012044160301982d05a9424400e014819880c0c001049502900300300e0b03948 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 221612733 1250 221611483 221611499
    0x301020a05070209180d020a140d020c0907050d14042a05101413062606060730030f0207050601030b0c0f0a030c0f0512070503090106030c0b0304020306070801 70
    0x8290078011340103102c1c40c808038002c6908040411000f00c420426641c245d0359a0300000c0d22030f444010151034402070041d82031004023021500490000c0e02c2d400404440c211802030004800000340107806001052060180311080c03806070030140c03400e12940c010240b41c117141802144001d411b207900c0310246504240e40f410180e51101d403c2e02c10444140556036403078013040301d03c030303180349040c1d10303814004603d003d07680700d5801601094400c90f0f15045414003003540820702d2500003200c40f080c10300d144000300b001c60800c2d500a00ca2640107090307020720048210501003c0c107841e1039002040600900d10210303201d906214481161009000561034004503440f43c030382d149018000030300b8040060003c0340d0004c42c08000c1b500d4071510341900c0c0d5141c01091402a0046c00307000004030102e50f042548117403051082c011504403c00f0190080140c0d00e030200120b883d900000c0c12000591350700d10b004008610360000150080540241103940e070302e441d2046c50f08102c8040d2140c000c3c0141c250050220903 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 221613983 1250 221612733 221612737
    0x20a08010c170612030708030105182802071e0507121a070c23070e04050303071413090213090c0801030f08161506060806030309060d0e0303070903110301020a05 71
    0x2d101080c819030342d10341070005403440700d4140c81e5801c1480b0004442c03040160000107507048030821280d03540f00d1a100c081480350800e0840321110b00280034100400700101a15185205c8088403c00508100d00340c2da034001c4840600243d04802500c10389146c041020403c00300303000d40700e991b00380c1041554682e54119154415181007814844036000211101d10402c028980550883e030280140a1f4152100c6551861800880c00c2d40c01041808141e110094046502440d8004011495a59000c80c1111201c282a0840011060800154100c001c92107600e0014082030300005030768503032103240136084e0f01141c1e00483c5000d0401c02d03250135041e080840241103030f412481d140f880300b0841c80c1c616250b220b80300c0d10320105450025807005124068003840d034080845101080400e844102c280c4d02524100c0348603505910811580c03d090910201130401c03080b2440340802e012204d0042142581c004444440008001070010000c0c84140e4405003401c0038141c1c0214178100612400400b24 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 221615233 1250 221613983 221614007
    0xa060f14041e020301030b04050706031103011203170106091811030f190203010e160314060f01180605090a0f06050d02090d020904080306030c010809070e090709020403030c020a08010c 81
    0x2603a44140340c1c00c070041d540c101200c0070302c84820110350765038507841d102000050a88050f2818480d208000c00d1444c000d102e54904051078444142c116813a00000944120301c0c0c0e00e00310104850302c1250800800034002881c040d000c182c0702c21102906095400300317040802c038064840181001c08100041c548001101d411003100c8622145c0b6903181044c952690913078030000c0003514400400000d0031510100340e24010300b283e0b0b0391034004082d054422010383d01ea0340a0000c04e06011000f060321860404070369680804181004520102c2ca103070b018058114a80c800d401107200049c0b02c000358600305800d51301810790b240e5054032260810b50010300b28001c0d50700e0220038660000701e08003903a441c04400ca00b1994014440c02e458503052038a4041c0d60025a070039802031081003800045580507104640c46140000001e01d1141d26008100b51203140103420201c02d03004401c0007042c1802540014000355000384c9401c580c2a016206204840c8000da200c10603507490441c0c0c2e9000710780c0c4800701c580c107 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 221616483 1250 221615233 221615239
    0x1203041709120a03030603060605042003150409290702060105010c080d021317070608041209031a010501080106030c0e010c0206090a030308060f09010302060d1a06040306050a060f14 80
    0x41d01d0486000c2904442c542007020481d205282c000410143e040d00900b090340d01c681c009106030381e80c40c41804107840b503c002c1054180164100300360880110400342d40e0015003040b001030704502581c082401ca030440c40040d01c401c041c1d072161140021452610100a00315001c400d50300740741c00b1200a4071100c040c001c1d2410028490030580c00e0018640c1600d40740d411840d021036030b807c0c8908807111102c90302d203e026640d04103c1c0800b0800200802d9200464240740c1b690540c80d6640c0e96240100c04140c41c0f400b00b80a00c000000c40401c031074800090400c04004514800e40d41000005050341c44142d0110003010708080300044840d60291152110040a0820104070030162001460502071220082d400c540d61420000605501c030305468020007003616208419404007040c40303e410005d00006c0c0d0403140030000c500c0040216030000d10025220758144d4150700240000503110380c41648169202515031051103019070451188900a08403600d400c0f0a207840d100e20420f01c1030140c842c01348 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 221617733 1250 221616483 221616487
    0x5040c0c0209072f0d02060105220b15030c0a081003020d020121050702010204090b0d05070303081812031807030213021c0203070306080f06060a0306020a030207020d0b070212030417 80
    0x5a895014104a00440c5001c000c211040d51070600c629540c45c006010440103101700750000415040841c4841d611001e11030440a52070840440b40c3d010306072401c0c1d110740251403136a584991402081c00b4501030394510074410b43e208204035008050036009424003102d5111740700100016605c00301c841d858141c0c28209082c080b803803583c5c8034518810302419180001d00701402c1082d13156066000f0400d5801d56401000300316030400c10b008030540103100c01410303a03110040c00e0010034022400b0340d52140440d07444203a804850701d840307800d110100e00080440d403400300612084141803e90b0716114110782e80140030716407943c0c0004d5000032406200d42c03285540046d03601080845604040c2c0480509c040c00d540e13a04060f40700800800841c41040042d011300800450040004a401801804018220b606403810754484100070340c41403249005060f800c10070480140c1f02c030054802e0250041d1502d204614002802906110321602400510f6004008210000e801c01250001c4100240c0042d9 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 221618983 1250 221617733 221617757
    0x60c08070f05010c0f090b0a03150801090803070815011202030604020c060f06040c180302040b0402090907180920130b07141009110405040219030602030105040c0c020907 75
    0x8115104040000d89005011040107090040c150811146014560382e41d00111240c081e04039648003007030040c010b96140c20010040301a100350004840202d2040c2c0e021001c1c1e071f54120a03401c54044450032034000300d0100c10003d14680000178a584a0f1035800c50071545440e110008005968440704080319680c08804213090303460703d905840c00d900c140c170112005030624050024010000329032031481182021040120365208080c0342c4500c40c066803400e07044a0442c2c2c02c12014000320881e0907000769081c02002d001d5640e01f074042d4010000c54841a26140740c0304150f04070100c40b034100940b181d00b48207110003140128841e148182044000c180d46aa244101786820040c1e550311502081101194110030301141881030b001c480c2c0480708560741c1044484007030055510b0100301a1282a140b4405c4081d0304041c2c0010b41d0240c030083c00b000e110100036281c00020001c0f900180c40303041c0d0200040c00f150400c0e100300441141c82c3c2c10040100d0445900003450441c0c010400010030003242100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 221620233 1250 221618983 221618993
    0x11412040606080a0302060f150108040b09030708030c0d0c0305060a03020f0f1f030b010206010e07080414060a060e01080102030c1e0d020a0806090619090b1c05060708070305090304060c 82
    0x1800c090300b07680f42610101c101c581002540c460059600c2150460002c0c00304074002c0c01203900741d2602c01d0685070b001159a40307880740340008074014503034059800104036901c0011140fa000f90f01c20f2039420364040d2120030320501e1600b21402d20548005040c80c0500380300f01541da410b0306600722503040b03c030113024203043d8000c40d0309805452021500700305071400d0050880f44218032070a400e03100341c5d020442c2d00c0000004a0b40c50030207200e0b049507203201402050f40c10307115a0115500030301038107420400c00710b988600d9241c4142260410880d998a080501408a03444000b90041040400960031428440c2d81040c05100c0c141070a42502c00e100301c113038103001d441025075400c09500c4400f1034850303114107009041c01408694483c8622405000211249408481041036041914000d0040c0e400d00d1320302401804180b1455500080600c0d40368016881d840320705610500c280060000d50070600e002400180d0040c10307000034541014204207101c9000000d50702200c0603403401240041d154209 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 221621483 1250 221620233 221620241
    0x120303060b0f480a0f050303161d0d030c151409030a0c0204021e1b060601090308090d02040617010903090815010314030c060403031a0114120406 64
    0x80011480082050300c0c02c11101c0e0302400c45140710440c956040300c003821107250242c0000001864182c1004410b508403c0681030400da28403201c4100e80d040c500341e466581c0d8600d14008112000d40c800020869221496241c402d14086a800e01d001d1304240c00344140b1141c1c4050703254501910051880030107041c40781c0585a003490704030707420150040084400c0005404009120940001c402c000300d29031000000444e02c2c0c0c12400da54000741c1c05038a1342004040d5001d4001c3c0204c40361003000b150b0b4044587c00080c00c0c104200d03401004059404842c140c10580020803803410710540120410114130800b0441d1000881101e030030462000c28070005000f0300c1c644d0810746c02034002e03039564a40844154044c102ca54001c0e2241c1d4201d940c0da039112030f5102d003203480f1101800c01c010f00400002d540c000c0c2e0012400c2d8800141e07820105016801071501a040380c054000070748030101d5104901c079071140b00c00c0002d001e10300400c0000c170f4146d5195a51184204413440401d144c000607050017a5540 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 221622733 1250 221621483 221621489
    0xa08040f030c0b0a02030412090303080a0f060f090b030f01060609030b2505090f03070501050d0b060d050705040f0f0f0311010e04020406030b04060b0301030b04080d1503030c110901080712030306 86
    0x1903802050f0130a115900000c0d0001c0301c0458410594580d0002003901036181070341142e6044c3c0c2c888004c0e13501d00f15a00c0103009900f481c00b141c0d64803071202150b0340b01d81442c03080240500140c00075044092800f01450b000c01c84000001c56450040240200b0754400c0c019802d40340c01060034461511058843c90380c4045040010010701c0c822103144c00b40070350010007032000b03407011601341206c60424803c064407401184a002c0c040b5030b04010181d40c081143c3c00590005800802050501c03443d00c10141c1510303800c41d07031980040c9000030103008910318003c40502400c0014603040c600c41c10850310b00c0001409000140c44000300c10483e29a6a01c94911240d4940c0058400d42d251661401c029026000440c240361065007060390204131140d561040e00d0490fa0002480d00064482d500d504c1c031a81c5c4050041d0b002982c0b10030641081082c40c4102c0401184240c0e0b403940c0400d41130800841c04d80040b01c4a40c4104030100041001e40e40004054081d02c5030215a04942c0126180030740042589134 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 221623983 1250 221622733 221622743
    0x20d0305070c0e010b0406030c022d01060503030d0510090e060c090f13020307020c030a120e1503040b100b120612030d060902030a06080a1e020d02040906060302030d050a08040f030c 80
    0x3e00201d0b9010741c1038041c204a4945072014044045004400d980b9a09030044c400c0380662280500da1000714000d224040b4580e04800019019480d480402c1c2103034070940401c10f136107490700d0a001003410020100c40060041240030406080c20000194640e140600090203501001c11008290703901d04031800c0b103004c3d004080c401442000005107001e50012501c560145c011003c0f040900e0034049a01100b0950000041d0f405e030304811829600c5030a0714284035000408030141c441e84500e07180c01507024600400001c003d46c605620040d5802105810415179008103100d068540305072583c440d500f0640486d051079a00c01c1407a44180795005c0c44545a200030b040180c0003401c1030b0990700a50041112030000d10820f922242d542d50f4489012800a129001021192194180a0081c4011544001c1070003403015643d80014080d01e140c0c1006990213580c2c0c0d4420011444d0401c01c00000c1841820464185028108041c001c52030040c0003500d0701d50780507540c0c800c042c40b4900c1030300007680c00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 221625233 1250 221623983 221624009
    0x7080f0a081c0914010c09030309031203020c10060f140f1e03010c0909050c0304021806060f0c0d080609090c040902031608060108210313050a020312071e020d0305070c 74
    0xb504196002e200c80b415405245c1d46000c9441207582c5c800c100700700c1a20341588921081e071749136554200d040d06821b0384100405509210180c0c0d929420b0001403240d581f00740300400c049081c046405000d1a49070f010b129104c90301c0307402c0c9202e501c40c0c9403502160142200c1c440035212070200114440c101d00486254103510381210702c4145a004510503068481041c010000c42c0c1c0c40d660100e0781440146c0c1c01079840200612078103a969a01500240d01440c00b5044d68240381d0810405032084c1c01c602c0d69488140c220241d8031002c507078800105644107000b11340c42c900904110300041d840d5030703400c0c0016010751717110b603e5507003591010001c042c030088200c10705904250741c40405a440740420b000b00c0c1854000ca4400c04403c4201400d4500c0d103401c4406054510380b00d0007000001c0710b1800404481c0c500a805488025076014420018040a0300200c40d60b0381ca40b924120980407e080408a50910300c801c5410158980c42d01a0403041d0349420895039a08440c206544070403420f5101c00105c45e02 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 221626483 1250 221625233 221625251
    0xf030b03011805011107081b070f0902030103030f0212040605090303121302090a0b0108060f1c030e0a0603090b1611060108030913050603120f07060509030c07080f0a081c 75
    0x3072012882c001a010300e00800244022003041c0e0001c0c40740c0c010103400c51005110000d50300d0628500d581065014000719000300d0f039241c44c002142e24159000d554000d41c0800100140f58200c4140d00c0d000030144050300030030300c070400a0038a5001e94010001042404601036007683c804100300d0f4213258400d19034509900c1d001c80e00d002c0c0c020031100304a01034000100403c804a400f03018071000020140c42c0d001040e51103505010000406910980e4041649012110107102d0703d00240800c5000390745000f40b61000c0c2060101c00c00c0c00c0d50156007010314001805000c03601c594111a000001e008003440044810322007150454000341f09031401d0f000d8100009202c010010051400074020340d10a10305c0c21003d8101011135408545107501500203081c03c01000c4414070007494269801c2c80b000c0c0c00d00085032a480c04035002180c85261540c400a001c03140c4050420403200204000f0300148040c00304081466198200038400401000001c9041c5005818468440f40010b00c0140b0410000307403 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 221627733 1250 221626483 221626511
    0x150204050d080a090509040c0b0315090a0c030b0105130b0901020a120c0302070506070b060d06180b090c030a15050c090d030305060118081905031213060609060e0105010f030b0301 79
    0x21220a003000426401e0f100005c01c0d00b441c0300c80500c6507800c0041e0008003403800ba8a18040d41c001003078a4211038100703540d04900e60b1840441c6010f0441040005403443d001c0101808541c0911300660620906101442070b0324a2150503d041c0c6a0516600d9201e14200380180d282c441c003400c0050825044426900340180e1003800485018007907806c80360701558030b5080c000c00b4401c0e00c5019120b2899080051100c0c2001c1c4030040c0712074820040000d10000105100400742c2c00900e0071980c0383c100c2030034440e035803000700312889203e0011400f03010008515560b4008090600101810f0341c1d80b2040001c0300b022201041e103024583c0a00f0b112000186450010001c0a044800303c0c0410900c2c4031159282036240525025520315100400d417480c0c6050140ea02031301c030b0500484140c4020402125100d141c80205405044240e480003200a818034210382901c18981140c51400c0c80c0100811055410403220f604458081c2480f0450a0280c54114098215059096015800e0008e20301c40c0130 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 221628983 1250 221627733 221627737
    0xf0303030c0d050109050105060f03071701090b1f08060d030509030a0803181c1404080a050d2a0f0201020f0111031005060405090406150e090604060506100804150204050d08 76
    0x41d04401c0c0030410744e030325000e80f0b5007124028000e0980010050106500741050200115081903079420165840502005501600d00d02600030183d82900d0300206412401c252004500c3ca24089841c488140c3c10602e004140f031030001d02c000c1c4074030800c850300010f041c010012290700010113019500100d00509003140c141d80140c43d10602c511080082041403040800c4074220864905010902c8000442045800382070350078a004c07010300c08000c0080c4c1ca203070811818041034401c0e070140c40d0343d03e44081c4c00f621340380d00340c00e20005d29615400c505240c80c010000000744035622140e440e82e0304240d400101e1410200400c502c90755880c205040804002c82d501443c881d0000d80c0000d00066254001d210341d138052440b4941d0041540c00101c3c0000706141c2000c1c055048202480c698580d40c0c040018484c1020b4503000d02d1074000360240820320034140142a0300c0b08041d41c084240c8100c1c800003c0101c08010406000c1084a40500210f6029038040700c00405c0000c1140078011034074208100a6 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 221630233 1250 221628983 221628997
    0x503030c040f41061b0105011e06030911130912050715020c01140103030806041a3f0312010801060e150411040e09060105011119020f0303030c 63
    0x4286000000a003824000f41908852582c440d01040390800282c807200316182e06000c100e41030b4a140c05455190f860f50b0000c1c149880059142980705003401c01c9581c00c41d9410303049400c1c45c1d103c140c0074103c2d240c02d1044034070446a03e403500044442250030824680795040f2002684040b64560710a20b0080c01d0308000700450003040602410b0301c550070142c8251240c01c1c80200310001380507030381203944400c1e4060550b0000ca0760010641c2216880310003020b08013600704030f012400000502c9a10b0900d8031483c0d03061004071240c003400800903000034140c0c2d40b003046540e80e01038600c1e0303804800520a44a00303110f100b0040751100700c00140820035803641c010042203070b00e520000000142d03590341402500111080e0352840d6009894001d442080750717503103c03e8141c02a440b4071000c110b281c0c41a00410040074180c04414407810801b103450300380f20041e849141005a001d860742c0c13014501103042045151512100c0310f10350f4840c80407900b01400366140b194507001c00300401c1503a243c00001071a00c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 221631483 1250 221630233 221630249
    0x9030606260309010f030e0708030c071404023a0204090204061103091f050f030f01081b06160f0614060306071103040501030c02010b0307060f020d020705090606090105070503030c04 80
    0x41c981104a14a540e406414031080c0002c140078020380003680203500c0907003410908020b0345c505540382c4100b1303455981f01d204044515440504200311026040c0340c550b040590868080d860704a400040036000503040301c0303804060030f1285a011040b081c0c1c822845000c62240c0b8155251965400c030700000390814455030340072841c10500c184040501100f2140c050500a002e40e46e00b900c0040c034024444904890300041c031504010144600d940000038611564400e00566510b604004001d03040042c2030702100e041a1601d9803042c1d1942e1508180e4142c1822080701214542c000d040a1310101d1911002520052500c0207080c488030002c608a44a02d600b036041303584603102c1c100201c0e0451030a0000040c0b40c2c00901051206600c00d8100c003104900701e20001ca00d21813040c000a0174884c05920550100e440e0700b402000703841c2c0500424001030084d0025010451410000c1555030341c00400c07091103280c00155a204682c0941c094500391074000301100d44901d01169560003660180c000e04d88 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 221632733 1250 221631483 221631539
    0x2114030d0f0b0f0108090304170a0515013816060203040803100509131b030b0f0103060c030c0207050607050313060c0209060609031515130f180507120309030606 71
    0x403c4d40102440c40c000c1484400440c1303081e14040311003100c0000250918607601915400d000822020048084000e96030940c9803065450102d000348100c100303400e240c8644003554800032100380000c100441c40d01002c600941da070080c0030203503081c0143c01c0720024001880403041c84240f02c2c005010350700c0f4416607144400042d451f0001c0101980c030403201e071020350000072200d03c005899504400c00d2416190318120310719071a03540300c0c00b00080442c2c0300020020b101c801001031007158001c4889504a9081c20883c015120700001e40314222801407a0090900103000010003200308215558080c54414246100c1d440302c900030150104070f48240d1094072000d011440d50701d000811906010030041c01014511884c66071034507a010300801c510444141c014000001e078440c1500468101209500018502c6000c0d1503035003120403184101c0c000803500d1103104001031000070300406480291300006020300d040c2c03408841c1c42c803261700020040c4d8200b04001511019502100b810394801e10782e401 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 221633983 1250 221632733 221632759
    0x170a0908061f060e01030f0e010b01120501050f061e0a0503010602070e0c07030c020d1e0204051006080f0a0f0c050408010b030a0c170f03030c04030b012114030d0f0b 73
    0x2d02d124107811010b190b80003105100300412400384415034085441814080351003003865031034070200e134030610081c00717143d44809a6070b0966900103200ca242d44104c0000b000b055040c513021a45459000c00a04c0c004d050000381c1700105000c0002c00e03c1c2c015036904955a40b480951401020380d0403c0c800c090140c41849404140d1034502da501710302c1006003540c05814045d8944044440c180705250683c2c108a03810300040c04941d2401101c440d1101c2208440c0c0368070035078411701048510041504024180100060001c1c1e0340c000d0040d600b000d4614001d80450325991212401010005a09000d082c03500c5443c0705200d4004024004640b0114020026500d072001410344070302580100810903800090140980c0700c9802024000702d40d007104aa0700c4001f201000d80c55a0b00565480c901030601140c1082004403001d4a18054a1107200f9456291407a03400d2040408207400010021080d9032442940041c08101f88d03003018040b40f1081c820034040303244081c0145289540c0038002d803100e003031031 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 221635233 1250 221633983 221634001
    0x80408010b011103040311040207020111060c13050d080405091017101409060a1505090c0904050603030c123010120305040b03040503070b0f090721020d170a090806 72
    0x5d0b0302126004101c540a40c00032104010083d48661022410300a0b800740000c094a802c00600d072140b40a8811250b54420745402c03400e2042d802c1e802240b04454901c1001c0002d11004140e074200d800031750300e06d1084d440301440f0381400c400b16006502d84602081c0030400c5140c00155480d00f1561402c010081003413141c9044e02e40c00c004440c0481c007a401040440c4140e41d044d0310051100d056640515a001c0d221800611405c40c01d46000004d810041900802c1e407405114082d0000811802540740c14041555291503039001c00002403201000300e90482035119070f00d400d40e502d07006a29141e030318202c145400103490005541d1140c0b49121200c01050f65040c80740074081213074060329020304043c600452058a944000e00c110b030180014481d0100240207607002c180260003c1044e003030f00d0f00e40b000000385014a01c6c0c1c03020f450081d446814074038603001112201041d540640718010a040b49007090200c0e80018108035010342d0001403210203070360744039000c40c0a603007007607040d52004d44a105034 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 221636483 1250 221635233 221635237
    0x30c0316090e0f0402120316060c0305190905100f0f060609060c080309010e07060f0329060a141801020c0904050607111002131811031b07080408010b011103 69
    0x251920101890b0210b400da102071214164090b10060100d44201c00004009046400c0401c000141903041c480003c200f06550190816885c421303c1d00300210316001c65002c25070f5002406108903150788400c98000c1c0542400b80c0f4003140f0305001c0070b00a10044255500041126400d03075000c1c140b0380080030940c9031040c0808011a1a240d41e8015194091303191485a42d001030070341801507585006240411000b030ac004001410b0f1501c44030784620a030728019050310300b15a01402c0c1c50310003c1808043c41e045c1c500e84040e01c9000e55585444008410741915901d80a0f0b820710f00c2d02c1404100e08006945100c5529050b1400380d00f40c4040900c1c6100b40f00120340c00b80e41c0180150020b20006040c1c6104060400c81c04540c40b0494440d031504220900403030b4091030002c500038143c0e420501c407503828900c1d0103c004141040402c81501240d0508100e40005450300c1258900081d03809422103241b4107407030080b600950f14943e1030342d0ba18084c40c028442c4081c03540c0410030000a8032401c640102c2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 221637733 1250 221636483 221636489
    0x4090f03110a1203020c010213060203030420100e0d0c0e011d06150a0207030c0b0307030c020a0f0b150a080c0405060303070f021c080a0f140f0d05060402040b030c031609 75
    0x16204007001420030f058020f5006001041c0e141d41d0b09000c0c0200e50010b102880300104000c0e002b459aa0030281000c007110b20500d017500400300d00c111414181500da6528184080301c0c580740c0101e50709808400501600c1005034050901801000040782d001e1102d0281412210452144280c80c814946210841d10080b291a0740c40820941c201c1c1c1e00406600051802291901c140e640c21a140c0d85c41c1d05003031801d50045003080780003004016110b81c25200d590a402241d0000701010841a940c0600d003684210b070062004014001007444006120206260800700811103950b075030700c0b1155196610a515a400e00c0f507030800c0d020508504012007207072042c82d01300c48442d424066a400703011008860f060800c999401c0c590580020900140281000742c03019950508a94014240101800d6030800d120124041c01c10003c0600c0c0c1d89502124241d900c0014082490355074500050024051035004204503440002040a9841010000c2d8032805000700078028181d44401e0407035654800380 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 221638983 1250 221637733 221637743
    0xf05040e0a060b040204030b0f0412170615130b0d0b060a0512090a0b070e0315010f2112020a030807081306050a0b06040906060908060c16050c04090f03110a 69
    0x707038003407011031910341001e800f15030050b20140c6000e981c0d036a0300702020002c07070304051408002814071041004845520068480300d1800030381e8200b807040d100400d040e002d801103106e400000b00c07142d642210081501c8104088160840009e507941c60103030101c0e840f09201d5113130305150440e140307a40e10b019020394070801d82a42e034007402c2020001140903680b50103000c00b035091240e40150800a401c00181303501c00d0499544103460403280d1401e251401204158000d110502100184001c0602500250494504400c0d00620300d2107060243d44605110001a0903062400401c0d040aa000207407000c842d44a2355816074030b581c80e540c08950500c401c1c1e0314580040380310015040811391b640c0100b900490103940c005413580321403001034941e03406a840242d44039202c281c00c0183c0c5800210840003042450050b01c11450060080c2150748200710441030f556200e0240d000502004000c08242460094010485007c1c5400c000c7e00340c9082d501c1c01c400050551608884002c4086621110a5485 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 221640233 1250 221638983 221638993
    0x60b041d01060b49090b0a200904180c030b07030203041a04050115181410030308040309030f0305180d17030c0c011803030e060106020c150f130f05040e 67
    0x1c0b0622500262404113000452540e0841260810045010540c0890203800340010888134078600206140301c010005512940b07001582003d4098414030301d50034100b02c86006541d02000720000b030041074030304040006100e0482c1c004040191203204402a80d000c0d20343c1528582d90402c00324140d210845004044620811409008851003114107800c02d110341c002003458031035041da41c0c10050183d0711940a5007820b03503107000c401266200740d4003c82c841000510403403409080000c100c0c1180d200040803c42c81800040038184600d0740c80010b9036011408814001007410024090741100f081a0035450f5564ac1290203460100c42441d9001e6010a440c8105103890f2402c402d6034000a19070030710300d0000c0280d0b00f1000070a10488400483d482c400d10303046081c508004080b03682088801a03180d000700c0041c040c0ea60000ba91100110301250283c44002a202d01600d03e8040c540501e161404085a1070600c4902611a06e003a160709201380000940d980f0100010354107040000d00080d046 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 221641483 1250 221640233 221640277
    0x6241c020d06060503010c090f080a02060f07020f060a020a03020105061206160201020d09050f060a0b13020d020f0712080c041a1305100207140a0608070c060b041d01060b 75
    0x110005800040b80603541c00107040c3c0d42c0e00080303400e5903d8030000c0800208644003d1060b01c0300710303c02c100035018070380c003c048444180d03002c10454030030540c0f121030a56000c140c0104564400c14110b40990307014201c561101d1542901a40d1907590003800c401550801d0002405814144e0302d64120021220050420b922907620303000b14414924540011950200400458081c0600030140280d2190000307203842050b000d48a82407280180c810810203007406a102550364440318400c030700102101005a44045060011000707202d241002d40c0d4440010800d2814442031280c0010b079500140c91307140701c40d969101030b0945840f940c0500c0c2c0450848220b100c005041a001401280503c60710400d8050b8035000041c08400e40d2001d980c00680c0000410306c001030a0908030710f00c1c0d00e130030f0310b21410240c10b107240038001d0382000744003070300300400340444506001d0103402003154a4005003081001d400030340349445414944019001c0750f0340c2007400c0000c00d440940c048a544402d00551030070b213104 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 221642733 1250 221641483 221641489
    0x3070e1b03060f0108071815020708030f1c020d14160e011b0302160b22050607170919090b2b170307050711030607090905130506241c02 60
    0xc01400c01b004002e480326107004000c201c000d42001800d15403030070074010180908024070b0400c0c00d401c0017580d078006200100242106000f80e940141c0c090404110002c101c1e10854000e0040ca2071804a150a090f61140410741c0c015907540a4040c43c048070715120f200380b0068030080901000303070b80000d030000c0104495118803980026980c0c03007481a0b800016042072540500b88058200c440740c4178001604451142040c852031b083c0817041d40c40f01d643d03680b4023000030300c03140221030014010300380c0c2e40740d052a00340c102012280d41e28030003000309102600424488032009158000c3d650241d10300206201e07140341000401c002040103842c80c6100c010400a101101e040c0f60710100c800d055500c505080c46512940034610070095681c0b040e0311040707241080e80c50003541089080c002c0c0c12560902180b158454007031030984820003800319254480030701c101c180036410100607009001e1075045c00b07030603040d0203070070400c800038480201002074902c820400009116007500126455103005480181 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 221643983 1250 221642733 221642747
    0x90f0109020d060306051008010506011103040b0a0504081b0108060103140408091c0326011d090705030d030203190212180106050409030f0807030506031f060503070e1b03060f01 78
    0x21140c1035000c9080c44d5030796074410686000b60b41219904401150030f1055440c01d102d0f05900503000d10384840100384610700795440744543e01400744545400107028a105d4004c00c21a0020590f9030202e49075904040000c00c103030208000b425001034140c9020540319071090054000c00c80300710f030750454103448030781c2c65550a60043c0e0319541c0110052002c036030341c0c200221000070801d01a4450300603440d05918519055900d2160740d003083d42207400180304042251b94601100300300c40d640107103140c603400012840c1030100e0348a10f9052003401a03090000f981034011794060701c1c000383e602c600103460802c110300703a01030000c42d0b0111645203c00550000e11040e0008110144180001020b50b25031010070181d5200030f40030f0307000c5000c1180d00807007103920445595000480303180410040c10100006a10340d9042500400708410030340f000d91210780030b64002d5009000c01000c41c0c035150382e03403404410042c3c2e00b1034000320340c6440394800e1607020344100e040f0380c41020700400d12500580356600645030a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 221645233 1250 221643983 221643997
    0x1608060a1d100b030103140106050105030c190210020a0e030616022a0913140601050333070903200108010b0f09030703050c0a210204020328020702040b090f010902 72
    0x4000b0b40c4000522030460500960186014060080031250b540c0352a80c20f49006510003410804104100440c0d19545401d5401d060104460400c2c41480c403103040745032003038035503c24040520001d03030240711680050713030f044408005505850042c0c0d254a070002d0317103440d90403119015070000d5071a0682c3c6895600d80340c1d140121669482801003581000c02c1c3d036054104d840019500104200409102442e0705840c0803038a5100101451760510f400b1070380300c0c0405240702e6461802030380310b60350a58901540000c1400d045c40018840c0c5440c2000802d240120320090700c400341407030488600325244a046845860b01a101d07580300b130340ba10203075a92680c00384038042c3c02c071182801103c040f03980510a1100450180000b050071441d9001003001c05181d0341d0240d40b5a40d0801c02400c0583c401c135003241e8603260106d40068a80d914541300380d100401040008101c44408030040300540300c10f80c041c1400500a03101001103424680501c000100191414070518008400400c0402d0540e0000c100c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 221646483 1250 221645233 221645251
    0xb0d020f0d0e24040c0b0c0f03120601140406020606010503150d060f0e0c0a091a0306010609030b0c03072f101a03070e0f130206031608060a1d 63
    0xa01112210140300b25524500440881c1d0402900400c85070701000b414509030548841010b802c1c00c060f903880110f01941c0c81903034525080450034607242c08060100305415070b110300681e80c0c1c1d588d604645065410f0304444040c0071603c2a0b01c014500b49a080684054807001c0c0c00424064442c14015a05074000504410321007404841c00c001c29201e40c40c4c1e1008181c4140c9000c02c5104000c16214292038091028410f190b120800031122a95818564400c80d007000800040e0305103d2010721905280ca00b02c020b405105500c00094048d42c050703920001c0340c0c00742d5041c403104d403a000304000d10740c4000e440480014507403142500408203040c1a0002400215280680000c02d1801c01410000020300140b1960f40d20618001005401c0341e400e852280f080b006043c190b1300b0907462168240c006040000c154842c01c0c000f64091440d03040b4160755607002000d10780c49140010422080a0151010000141c40340380420a10b003440007001c010380d8020782d111015041d400e11018503048009041e061 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 221647733 1250 221646483 221646487
    0x1403040b0c1614060c0a0c0b06130c0503190605090103081c0c021e150403183204050603030901050711130b0109080a0c0308030403020c09090105060a0f0b0d020f 71
    0x102036500300030308402e10ba101c3e2000c40c14440c0101e449030704090f8010030145001e0700801c9001030140c0d1190224803a00c2d0b208195170500e40720600442d2944036609c05403c0e0682c6080c4040381303071a800001642c0704000b20f64421094029100384801921181e1140c541c100e00c055005100140003080603000c1400041030410250781c40108420903540d03460003120150308405050381080d1031401000c00c0c0254030764000c004600c1e2542c844030348544014009007c11001c403802c0c00c82440c03500791a40051680c0c0c20160103000340b104020700c05c503075a4481411600c0c005452959981414000c261180390000c0185050a07001c20065520764030a080c129100400e81a602c0c100b982d4420059040340300180000400194290015050382c540b50050380b0598480c000500c00120045004800c0d00c3e40300f003200b5202c3d222445c00b42c1c0b612040000041d4000302120820140b50310550169100f1703070301120020b21045d0359400c000e4000b202da00078180480b4003004900e8840400390000d005031005440d1242c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 221648983 1250 221647733 221647747
    0x8060606090319141002030903122206050f091603030e0310110406300207031101180203010b010e0d0f1e030201020a030b0915010806011b080c0d1403040b0c 69
    0x2101e1591596040350316075800000161034131000c0248480c3d000010300e08510354104481d400f80d0342d02800381c08144480d030300c070001140d000f445442c40761110101c2d01c1c10200c0216902d400030240c90100c448203558141d00d00016000c180008000400d6050144c2e5040c205013540c9044900a11000b5881e40621a0454070f44502c4064443d55551420041803d0f494504040c40201030130515200d134145910305405601c05011301d44940c2c1c101d47c0c840440165922410301e401d60701801c402100c20482c0d4038056298658100030203440141900c220020010b54940c04015202502100b0559401c94070343d90311f000000c2d99034090207481500034192400c065424002e64141c021049404a0050750042a4080d0840d01030050190790b040880f8014800c0c948486840f1080404540f0141040030040200d21540d004030603d6003620f00d480103000c2c56803994213007681076a115003181d41d650b1060130007240d00c2511500c00a0b40200f421000c052454450303848004034214040c1105e00c1010fc1000b2103 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 221650233 1250 221648983 221649013
    0xb0f010c14030408030304020f030d080118090b130c150e040f09020901230307030f0201120b0a0b0a080604020f090607030e1801030303050f0412030e12160219080606060903 76
    0xf400003424040001c41e56031070144144411201c032000c0071402940040c13101c80503140c0001c1e03d1410346d5160f4840b144600c0319510000f000c4d001c50700b00504006038070418413542c2d0106c00381e040076a03030013401d6201c00e0a645090240010800c2140b110005050b00b404101a203050b410041065801007000b04190400d600041d80d4030000303070b10040b54807240841d0094403500b81115400b5424080b00500031840c559107030004804104031000341044041c26295810b00c180b540511002c54020300f040300b1082e1941d002412651069185002281c80c01c0009600e600c0c050003194101e21850f5001402d2016002c240111a00400000c906101411000070640d8507a01c14a072110090107202e19840d5142d070a0140444030003410780403603202288104400302d14548044551254540390000b500c00903c807115051290f171110b0860700b181e001425243c08425403282801150080307404858070b24940c5017110443c03003a8850b0540344d820150004000d46007180c09007a003000040c003034800402e049004 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 221651483 1250 221650233 221650237
    0xa0e03100c080c0703020a0809060d0504230705062d0f030a0b0103020a0206040803070c0b090106060215010311040b011b0605010e060103231e190507030b0f010c1403 73
    0x11103485569581c8003590560002581d908104a116101e260480c00d4034001c2d100c1c02c0e8210007034405803000940d0513540d25110110b81180302d0313048c0304011500f07080c580703041d0b212012040707103032041d20a0014a1400c0030114040c4210783c030040440340751118a12000744c0c08103c81c4641c1214a0f46100c0882a1200c0310008140e0441c0844403540d40b0324042c0705010460f06003c0c80e1034105441440000354642d00000ca80f03400982203018682c0302ea861040444070351021040c0200204091028024002c20542041043d01c82d150280d03882404000801c140480c3c0921024048a5242d03a07408a181000c3d440300c0160031040c0742121a401c0103199641036510088001c40f0195a00c4004000b50304103615000c0e000708091034103108c0704c1c03000541c3c00b444c89121081c1110141e480030100b081d0003018000400e6070705691400407054505100d44c00b110307501801d4205c0c0710908020004515500c13900c10300080f404010b1082d4804040c100044a102403014012500143d010a0100c604501040 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 221652733 1250 221651483 221651503
    0xa020405032d0f0c04180206070213020903030a0201230c0a05030703060e07110705090714030618040b0405060c040f0612060902310e06090c07060c030c08091b04020a0e03 75
    0x113007207800303002040c4030850f025000182c0c640071071a60002e00503a1b88204441d03141c1d4044801440d0902c004003803030000d2158244d00c6603d40b10008045400c5074040d0059140e04000007002c40013040d00f5441c0040b01e24080f5005952080b04000c40f200c01c0f07010383c0c0610b400c40500d182c001039881d01e410703500d000c0c40c03815598a008180d0307081a01138603040400c0b0070800381a0986014005041840014003040703005003282082e840088002002078840031744c00c03948140c081c902d21407141020706008105c1b040586040c2c801e07006410000707818092980c1210304540c1040d07003009241e407404000f19007240c4011004504642c5481002652408a00280034a0400300070020809040540d13405c40d0303000340e0850506e00410804e405c00c0320701030407100294031080907603002590b59202c40d40d900c10341c46a03060040c1424070300041200000d5041e03201e02c030380080a8551142c00e840700041203030344039100c11203860b10002100300b2060074103064019004c00a041c0c20101101050600001d0400403454 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 221653983 1250 221652733 221652763
    0x191410050306180c0d02010201090c03030e181302102601060201060807080c060f07062d050402100f02101a0108010501050703020a11060405040c11060a020405032d 72
    0x824030951800b88110394001d01c011003008460002e410280391903200394062280300d40164604141503900039040200c0041d0301210104a09881c0d14010b0100e103000484140a011842424000c1c0e40102d03071180e00950610b0080b1403000c1c000d9080041c0310014031084010042c420f595464002c6200707a0024294003504e00503034031036041c11402821151181d206004aa00c0744ad42003000c0303900851100c040910641c1c42c5e41c1c1d240144003550b15207114200000703202900d400b6900440111400091045040100211480d0031710b0713000e85000e0b514140c1e000795000700c0070100ca1401ea40a42c4801700012003c4c01075450303903c000b0084904a414801d10010301015100c5254007646c2d10a00141c0900400d003041400e082c0c2d0381d10001d5850b1000c0f140106483c7c5140703040500b0b5038a80e0180d41c001c100c02001800301c0c1e000c82d00010618040e03030900340344510550012a0403060349000740d034103032030f005401003214240021400c0e1101c2020314130012403040c0c94190340002c8805108107202c00d1114 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 221655233 1250 221653983 221654011
    0x5060d060f0c02060a0603030e040c020705130903030501050607080324040905072c010b0c030405120102090306071409010324080d0f030603110603041b08010603020f0411031914 78
    0xa10300190074104d0041507900201d2408200703100080c0c002c80c1404418605903000240c061402d24242d24001140d0071203035001001c00607416049120350481302c01d00e48255020b0061f82da89405014060241540041004405100164000700c0d0360707810394441990682d054694030108000302e0215a600c1c2c074141c07681c0d0014581070181c0e02c84c00741780311800f03184580b03408024800107400700180d04043c029010003000025280170490f0080040c0e41c05800010803013441c03918100000b43c000d40c00054014001d006a5000480303c42c000c810383c10504000034605132908403c000110f0003090401e05085400b204144948030050300e8412402c05481080300410700241c0210019000001c0c1644080816082031414000152507144034a00a0001c0d100c444d240e03183c40c40c2401c50040d0700000714540e24002c190005115005400c80c8046070f0007500c0b030040c0211098180010f4428001003206021003c0000c039a5488a45801200720b141d0170000040b40c00c0f9000403450f0107481070b0b400f525000c3c0d103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 221656483 1250 221655233 221655251
    0x6120a1212050105100c150b060f041511030d020706060b0c01020c120a120b010225060905060c06011505040807030b0105010f050307090302060a02100f0207050c1c0605060d060f 78
    0x841c0304481c003621007120501c0031030f14982d0004090304050701c03004202d40808200707e140241250000c007000080140308a444111641035080e142d00719100ea540c02642104d840c000a034001d0f0800c00f60f03c2e04002c082d43c501a20b81e8508406540101da00700c0d00969a01800211840001c0240201d0140940007695914500160324581800f200440000c08000c011440e07481e50018941140030901c05030110748020910f0040c2d0030402c0c03a100c3d0700000c030a460f1800e000402d0015400b400d503211a1aa0078085407124180041800780c10751580700c961043d001401400d02c0c1c400e0b1640d804e01145049481d0a0311030035880d080c41d9069008030740e81c8089000502007076070010240000c3c1070003846c1660039440d2261004002c0055480041d010b00d400141c008410b0384240100c05201c00590024002c040e141307000440254070171202540d950040c1c0c07042c2c00403450305e03c1100c4440210f0040c080041559625004020b140141400e81c0c06081149090001050350007011a0402c41c08400552140c03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 221657733 1250 221656483 221656517
    0xd0204080a060c1b0213061d01050109080309030a231515180f0703020d0c0e030d090602071502010204050a03050c09061c06050a0212090616030b0906120a12 69
    0x8103074410a001c1c001303140f41904155003007010b04040250111500c1c65034250b00c4500300c00070285600898442200c0070190f400400807a0b41281c100d400a03600c80f0380080e5104e403940e071640034044200e43e16801070322400000c80d03000b6800d0790640744a626619030541420980da842c2c200000100c4a240c80d001080003070100414003042021031058994203039070702e0621810020f03410002c00c1c404a9440300408144083c1c805c0e41503400400d0211b074200a0312894a501a0000e200041c585219101d40c55510301e0851083d840c001c111211600103007051030409a91640c103100740010072046650921000883c0e603500701e40500114040c0c000380502c04011024002940c100030302a502410300c0286440b0070f200a0b403084074055400c03200c00a40750300c1e03d0003120040e10680300760a0302d1fa134a0205000c007281d00405d0243c001c000c50707034080d101414052425015550b403560b03e95030001205c00001c8460610304400c100c03000b00c000036100080140e50344d05000c815000c400200007604030030310b0030030b0039 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 221658983 1250 221657733 221657741
    0x80706090506160807060b090109020903011118210307060e0f120a0c020d0501090302060906090c0108010e040807140601051e0a0b0f07060207030302130e0403080f0702030d0204080a06 81
    0x90707801c140b4101c80c2544040f14030502402c02012560005501014040d10b80d020404030140208141c0440d6901c80c50030000c1c0d0052804984694a0300c40c8141500412804a90380e03982e100f42c614004400d040b0400803402e1120011b10408040c44240d071401c2d107018402800c62901ca00000a50754800444e50740c5084243ea1601c8120760200c1a0007c010f1490b03400d9a0040c6c4451810341c0c01c0d40c0c030034804603070510040c480041c842d42c2084021010140c000c50140d114016003c00c4841036650052210b646000d4584491b0102d241c0a00520841c100324083d154018000d0701c465140c03140b9035903a0a0a05015061880c41c0e030032808c018406894448203021503e414541c11001c405c11180008454004174851000f074a81c001036048280514031050320f0f24680c00c184115242c046a05024001e540240000e61001604602c0400c0c50755101140324000e54065031058025520351070540018000501400194441400001528400b41c0000c01c0176003030460243c03031018000c0c0391440580d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 221660233 1250 221658983 221658989
    0x40309080d020a06150812030708060d0807060c05251403070b06060315060c07050415180905030c0712051209030307110f0405040311060108010e030f091203030108070609 75
    0x1a0481d21004a0302a4000349200d08035401c507a0010307005808605444c5c10361929840004a80034081420070903113400c43c0503503c2507005880c3d4205d00e90750001004840a561100200900800d01c80307040410b02c0c7d90b01003204184030342030003403402519803c451b9038900e0301203005d551901034014090402a410034480801a01e1000035800d02c0e50030743c1c0f5402606030041c8464040c00c008400140b0300c07083c02080c0d140c002c102400b0f0a50300c0d03425000682d101c400c6405002d0041e41412070f158010581c814400d011552140d5444405590b0007203400c02400e4a00e00c150342ca4400ad204241080d0400d01c0031b0b0005014030301c0c403010500424070701603062100c42018445001424440040241c4020046403038199001d00701e01107006102000400700c83ca03c224031a041850700c1e081204054100401060303018203401290001c0c1c1e658203055081c0c811040300c88107075030000e01c2428903600181010b040c0030070340100081040780112208510f160801d82c0b040540798441c083c01c02500d82c02003000005 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 221661483 1250 221660233 221660249
    0x30a020711041811030a0204060803040819032c040203010602070806091504030c0303110301230a0501140f09040f0b1906020706050c03090d0507090b060315151e03040309 75
    0x80003035a00488188540002011340b096900c0303042805142c0c1d00340f10300300490380c1c010010804180c840890f0344d078179001030140f001d281c42020300860240c075000d0100070010754140d45868444003c5401c0b10800e044003c2c840000d01443c0103441c1c11940c039400a54081c0860f54002e00101c0d10f0a03001c14a0814080c00540c0160440c050300e50104002c41e58035940940c06042042002c1103e03d07044000f04000b044220070b00d0300110012030210b00c00b0382e108034842488442c00e081c1e079014204001e40d200e1184652030220b0380f108000c0d0045621070025102d039050281c900c6042c00100700c0402c0030b0300c014407640c0c00820355480e141480e6240602469041806110300740418506010000e90b980009000359000d000001c00c1c098508075080080351080310001d000815403085c240342007513482542e401594000c0d42031004052850170140d080c1ca10030f130307510308040302d0070b007c98800e00031580c03400d0000c1e00c01c056007000b042174004002c00082c80765013402141e082e603030b1900381001000750342c81d5000500 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 221662733 1250 221661483 221661491
    0x10c0e0118050a050126010305010903080c1201060e0f030a1514150904060b1e1215060f0a0e07120f0504050c13180b0f070c02030706080a0908030a02071104 69
    0x40b585030320f2440b1065072000c0c200181c0c0c0281c901503003161002c5d0035103003020040c4103000210822106421611426209403640109a2602d025816240c0070b54030b0305d041c9045184004200706841003504114040d0b010b07180c4017052242901103400c00c001c480007680c181c540403c1016800003544500310b1320445c58020450300e405d0240c520381110300d90398501841a1342c428042030034000e040e40b000c2060100248103850900c00201c0b400c14260900d01004d01c10211500340740e620700000326000e12038900412401031140d4420081244c40c06110350300341d0b0003003003800c00490741c4944003900e0780c094022503c61645045584c2d100c40151941c0080041c07016060109200004000058409503080100c408150b984241800203000b403e12000001240c00b034100750070117201e4002c4d0b0700b60042014008001280e5184582501c2c41502024001c1d0150300510041116030b00c50480141c22041640e0082091030694460409903001a40d80192541d80010308400708041c00843c61740c00d070001d8074248 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 221663983 1250 221662733 221662739
    0xa05180a0903090e25020c300102131806060e0906030a0204051501081803031305150a020405090a0605010801120212030c0606090c07020d080a0c05010c0e0118 70
    0x844040141100112644440c40300301010701844002010f0407042580b83d2091400b038521402032400e20440c040c142c42c11980c1a02414400f00b1140190394010f410780110900d004c010381c51385d01050281115403098041540b450038028001070070404148118041c500f4205500d0181200c031082005176072510340305003082259080000444034209c201e42c0c010180d41d410010900703011040b81c0095000f440d280800c00461070852041203400420380e22031010350365610201403007140240342810f081e802030000403c210700070902c0040f80b070720582c259039020f01903407220000c040f016640906002c0d0007290921a07810122800365124a1844090041c5881e000020780300550600030304d07041c20f458152400640d107510360358078498000141141c0d40c450700c02d00c10b103480b41002e640c014030400c1e150b00070540d401142d400f6105410b800a00c0c0c050003026039540c61006600c0203419206010700e1090a030b010070028460814401100c0d00c8451880d28140d00040ca0004406103442800e0b400b02c1d014 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 221665233 1250 221663983 221664019
    0x180303020c01140706050108030301140418080a09080615040c05130501110c030a111903080a08041a16030c0207030c0317160f030f031e15080111090a05 67
    0x64039110028240703c14450042000b0f44000e04c40c5242c058003032814171000055065000008504891140d242110300390500d10810060300c00e85201908000502c0f9107007801b050052009100107001030502c103008560700c400d410700700f540445207a110812100c60701c6017036040c14000c0c0c0807020010316000c0d20b012144079198030500701ca40103050403c05044001e89002c0e000700500310390100010100d407540b05003840d200c808a0f18405a8a01036005410240700d290554001c400940703900c5880305007058000380045590000051068400f411041c0d2034039000420541a1802005a44660a0505c00d0542c0c06400e44110441713040456100200c10408501b252504c03000b41c82e804040e0030701030005860403172040d0054600c0880303042c41c1056030300b0412060769020041e080c401d49981c084c0c0300c0c4d00501541150b40340001c445d40000e565445060100b01503200f5030101d031040504100d11512501120300b100e40141002070b81550000e2507040314070b0034040702401440201c990340c4c40700e9000c03070003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 221666483 1250 221665233 221665243
    0xf19091109011d040e101d06130b09010b10110705010206010f030303051b0c0a05010501050621040f050102130f0f0b0a0f21060306050f06090105011d120d18030302 72
    0x50302008034071180500300d05560b45e401030b00308402c0b8201120b907034400f00440200201400e0020320100681d891402c1d0b0b014102281c00da108848000650b50741d51010b4071765400c0941c000700071a105540c0d4800617070603941c0d10f8211908030401d55480ca01071803002640035190400d640c11650540d4407400041010201950803401035944c135103004640c43e15440d145a00e0202c441c091809449008610000e44010028151584034080c0000b4413141c0d07130340d00c1803201c0c3e032040e610001c0500d00c044490786000c41c0c0081240383c011307115059000c00c0e0392258403030301e0891b0004c42c8010707000000c2b00810044080c40f0400c0001500c40e02103200041d9151600296091190703200110610a0300140c5101890107441c48140c0c407038130f000900003011203082c0d1400082516000844209161102090a070442c40400c240710710000783c240c601350307428a4010740b000320001c0d01460b01c0e02e800280682054031010804214501000000c2c1280b01c164100900400c02c201906841200d0004003000031a0340015 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 221667733 1250 221666483 221666507
    0xc031d060d090807020406030b100f08060c0a05092d06090d030c17040803041a0c0717031b0706021504080706050408070221060114060301140f1909110901 68
    0xc04a42c1407070640100e003d51000a03510030300c0d15a000041c0a880c0d400c0300e200300c4c0181c1507507943c1c07900c074500b240d0408500d020f8114039a21180020b80034802000060450184a041c02418445907100254180c0514407007108040d4540501311200c1d00c034200d071168015421642d45080543c54000f0502401159002404004400780107c06001c3c07408090003070200c41e035034403c0c0d0301c0e9194161590344e603000d442081210707610301008002d51a540b100b9030300c0e00d880300b80261400c0c515100310005100840d0366243c2440c0820010316910715614801d103100826004003030502c4600c0c040c2e0183c1440200502140c1c4d018854040100143c075000480c1d8605030f00400014458440c5e00303100c03070180585040203400000c0020b110440340e00584001040e070280d00c0c1154a2a0780750425200342100e54076210303070040014001400300000d444402d21110b24041c2490070110803800010740140e91004234903c4a070401d280a0103080c2c500d0040e44506422628a00d28110600f00000d01901c0c1d030704 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 221668983 1250 221667733 221667757
    0x20d1103070314160b130c140f1516062901090e04060605090408130b090312032d0703060608060901050f010c080a030b0a050409031b06060f03030c031d06 68
    0x14041031131402d440e1410001500001039480524050850f101e00701103221042e940b64403280c00000d0080549140d100e01070b20040c1141c502440b410040c1714040c850344500f40342585050250361155401840055000c500801d404645495054a10446404a085c401d40000740b5010300401690300907000070201c40944942c105a0f0f521418198005e00c440d40107035900064840900040c0080c601c06080032007032100c2e40e01a4180c2d1031442103078500c501031209825402c1720038000340003c0000c2c0956400980c0f001d03a0410408082c0300440342888080e0b4000d5054106802d2080c8681d240c45070802501e81e500b0144c0709824203d0000d503106805204a030b12504091000201ca80d109e044c0100324107a21000301512010031880c0540580040960640154a400f000240616040c0107010303200350592104034a240704182c2199107110f400304191143c90302c40b28000303064440c0c00b050a0084d8065a50000f94441d90310703008020380441c428441100d40340b80b100303030816a202400c03900300403030380 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 221670233 1250 221668983 221668987
    0x5010b190203190309120305040201020606060d0e1c1202072301140108010f0b0f0a050d0f08070b060108090a110906041e0501060e2e051207020d1103070314 69
    0x8004a20b9481002c0c11500c60030f101ca0071805206415800400100c3c0c82a0301110849404100860480d10101c80280c010b901080100740700d810301400812400c0c1c0d80084c08686203202c3c0c3c5465140c0f40c03ca40c0520000c0340c000b21182c0400354891600b0404c0218060290319200a0b901c950341c00c0303501a0071880903500c01030300b5090050025405450620703440540719441d5a56945201c2c000c10480c11078550a5003080c181c001c2606d04203080d0640d8a100030042c548031801c120920201c1d4249500c00c80d0f0303226040074400c0108038918090b004081c8604026020f618008000408040c0c000d070442195500c031480e1000000d0030359890076080101070321009001c0d55054001405404001d0402545030441c03400f2041c107101a41060313060300e805441c0c084012120a040c017070841101500c000200307000c1800d41280c4007680110141180481c078065050540110010408503401c1e03420b100076902c6100302d00b0460f0b81107400500c0490540014508102c8141c901030003013001c004200002c5240 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 221671483 1250 221670233 221670277
    0xf012409020a09080d091502072d0308030c0705070b040b0703121d010501150c0f08090d080d0519150e0903040b0304051011180d02210a03090905010b 66
    0x850103c0c4001896040d0842c0c00c800d1074184043c180d003009008010b075100c10000007150349030000940c0d600300d1716800c00007480e40000380e81c0001e40e0020445d81428000c0d60400000c0892040000355025041d0070361140d076900203528000e860446142c0c000c2d000a10705005c02c00c030f00013041c01520281a01030414031b28071410320704030758001c00c135801b5115a0100c0c0c82004d00092101503000e00e05903002c0b0650f0350003115081c01c1c00d4842400700f120080030100032031080c0000038178010281c462281e01800c05d148001c1c041e13440100d65000741c4007108038140d4bd00100030303803081c1c14202c81a000107100700800100341d15999818070090f160180000c3c000900303000c1007040b4010001c0302c1c020201c5e218015145d090501d406a292004184076100c0207082c031512030100c02d451340c11502c24000165044041003a24030030301000f0385010f10140e83c49400f5025080e40c50b041005192000701034240036010002052070054041d41c220341040c0c49003403401c0010b108040c1f43d04206c50826004842d03069501d09 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 221672733 1250 221671483 221671487
    0x70b09010503100f1d0603010e121c020409020304120c0308061c08040e010602071508010e040f06050a0209040c03090c05280e0106091203020606060d110403050f012409020a 76
    0x142940554406583e4240004900d1a0343c005e00108842010b041d40442d19a01e0406080c5c8581d12550080c0d03421001110316100d81d03aa00030000440d176000e200100043c85419007040740c10640c00581e1031a000401c220403c50a920740c84c0441260b030401c00e42c411901e40b0014042c440040c5036601400d40207480400184000c01c0300b0000030341c880e41950760783e034541c0c2c90545040c0b402c4c800c1030b016124100340031442800a40d812410416580c3d02c28071160328000d40c441400401410071b40b00003503180031800101d01c250040601c40c41051034003503925100d000a04c4215400c01118408061801e1200c40c00156112448411105c045440503040780302000b40d28045207400865042c0c416503c0800543d000008081c0d41c1200c0c107a4492480c5039a80365405c94285060300341c010b0040c0c1007200001e61907c2d18001401007581700b51701c005081c80d0002c0d00030341c1c0b540c0076410568084e400b812030030741c070300100340200c08034944810300c99200000340e881c200401084134003441c0d503c2c1d41c01003003200002d8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 221673983 1250 221672733 221672761
    0x21003151413020304050304090c080903030a050c07140a0b15130e01020c06040c05010e0a0819080405060d05150a120b0a09020901030809030708160512010603020d1b0602070b09010503 81
    0x32542d550110f650342043e142a40e5079520038410308407194180320f0f00d2541e00e8007070660a4860210358001e145142c0e0703019a00b90003000024081c19107540240642c0010500009140f8a680c01140007000c11040314200840c02c0c0400a04a507080c50f02000003510b1511000b00342c006035041c1040214914411a8034a806401921455440351243c48100810300840c22600000c8400a0705c82203400c0320350f0400e000c40c03074a160041c42d00350340c00303207034104103034201c0c442c1038042c40c1c0c00740c442c050500e0707250000100380c1ea0180c03040220b41511202070004001c65480a0340702450101c40200c00c1500c1c040210220f0700c00003a028248080314000a076070140d0941290320074540c0109031a24030760b182e160070030142d0001000c1c00d011707100d0264007040c031040011b440329602c82ca20340d100000d40e150004101411000340c3d03100c0410b5495400000058035a000e0203141140308450659415142800340b9410a003154481c0085501001d82080191303401000c45191f00310038039007560f481e90f440c840c0d12034007 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 221675233 1250 221673983 221674009
    0xe03070308210609150d1406070906020724180509010b0a030c02010c021b0a330f1b020409050601170d03050c030a0903090902070f0210031514 63
    0xc00d0001004010889400352902d4001c1140505150544641040c48010701084a0f841c280300c0000100950a2810030010024580b00b000180610102c0c400883c0c2080d4041e19260041049210148002f94040c00040050304288510380c2007850130f444c00b000071480c80481e500a210700240f40921589801075444081c04018144401550707507540d403c50181d1200881200007490000403120380d40c418001d10b0030b80a440c1d4010402210300c400029184412070718202e501003031400000407200a240c91030302e01030025280d80704110303070201ea6032503400360312003d05d00c104000180e00307199184d0081500007140051400c03000d030a191a10108005000340c0c50040d0180c400c40000040400490b10100c41841801003600c0702498001e0058050740c00c1525070480c48142032001548031901a0310001826010b440c0c01c100c85552050110100e81c01050161824114420028194101006c0b681d182c11901d181c108006418884c00988251090040c8628124086401e0100d541ca0447c84004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 221676483 1250 221675233 221675243
    0x708130c030b070305070c0c21020a1212020f07090f0b060c0105060f040c02071a130608040210110a120210060b030f0c03010602150a0612080a02010e0106150e030703 73
    0x15498032402c101202503412646200080c3c204400a0a140d20510550b100c581c0d00501e20301045003001d072090700030301c400c5c4a00040b2180322102c0d00c01682e100c00d008170007001c002e01c090682d00090304001100d141415011419548260700040204500140c064100e4100040005a034820044100e01422a0fa5a5240d200e28003090041d0f403070740c041d031251b4011101183e80c08500714040382400181c1c1c0602001c90056049a601044980318105003428440d0f14540010f141400031400944a084180c12a0001424500c20041107042c224031000303483c00141000180500700f55501a510001010000c01c248025800344040c1402003042c5d00000039188814005180c4441d00e402460300111031403030400f866480400c0c0b42c00001c80442c0d041c0c8503070758080c000303511459480c150282d501a0400c1c0c6040e07614000094061214801000b03020706c2415070766681d044440e00242580d03008d1100100c00d0749000400c10040504181c003841c5661b1500b03080c40032103410070010b401c1c252240d002406d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 221677733 1250 221676483 221676503
    0x3080403120c021501050103060b0d0216050d0c05010b01090f0311010311190201060e0903070f05070b04140111010e0c1e0d03020f0d0509130522150b0d0209070813 72
    0x1c034464004c03622116024110240640907a80d0f28011805d4521a2003540d100003010070140e248150030390018251010902c02c4002e9202c1d40e40c0e2140d16003d010100440080d800346000400c201c02800742400c00002440c0c2510440e0402e01c1c24510034105220041a20060810100059010740c021048c0042440c40007504e9200c0e0b0b004268255001e038203400c0042d46040c00c08a60b5608150007503004e031060500842c140815070390f41d584545140f0006503010311900100142c0c140310800200054075980418640c80d150755000540100904003900600c0c1c0d041c140d0424038408000381209807104101c4501513850014240c00e140e00221400d1541c102d4500c0c14248107040c0c0010380e0020900e1481c04450340d03414003100c21901c5004005d2001c0d48145014a026100e40d441c2d040a500305015803e5280c00d030403c4c4043e4800c694902c2d004803880010380c00f4030840c5911500c21280061001d6682d0728245541d03a0000d01030400c010000c0c01032004180109005184044000381c0d0544e11402c011 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 221678983 1250 221677733 221677751
    0x9030f010e0606101805060721030c0809030702010206040602090604050406030c38250b0405010506030c150c070b0310030c09110a1d0406170105010806130308040312 73
    0x81e031500802c032500c1380581889480d81307002c140b082005800c201c03c1d804540c02e01a083c8820402603a000300303010784100200c080f001c600210844005408410651030000e892015504040c010940007400b4600c29003044c4140c40250340c020401c240c0c040d0707001c040140e981c0f000f20005107803409540c1041e90400c0c40d102c004410405c0140ca00b030b00f40c3e403019050711200c0d00b030f481702079061a800200c0c803031180307010000100311042d42001904040414240008420806003203100400744598030548440e05010f06000a0020038450140c01c0b0400fa0b01070710120314410042402820910040c848940c4006404821184184400f602030000d010761141d41c0d04010503c407440c5003141c00700781ca40c21a25000021754080511842c2501200c4494150a06040700e609580504c4422455030110040d041050000c0d560b900c9450003074001c2d10014a500005030307102c03a08548058000d05680c1d03000c44240180307000c11006800103c0d03418035085e02145e54514081350b0070449210001202c1d0300f40a809 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 221680233 1250 221678983 221679011
    0x110708030903100203070c0f02041d060618091b030304120308070816080402190527060d0201140a1e0c05190309060f11030703020102030108060a021201050609030f01 73
    0x900726841e04808072056041c2070b820000c100d110945590740801c2402ca00d800004130049603128000f4002840010015a08084c00d20b6000d0610350460362a084a0204420b038600b220010301c2a100c0d03182100300902c0c040e40740300c1da9000d12800c1e400459606254500c0c0c90396040044030301402c0c8003020262340d551030b481e0141100b03c003550148049001c0400281c0380e10035859020202d150181d5035000349458907001d00080203802040c3c03050820088001041b80d44403200304c1c60004030340c040641c00b4201d2410030855a0100034249a02c510302c2840e5000240c0e81c0301d54404116120310030f8003607546995101c04c4c1c1d480308507074000c0030101d203a400515030126080200e401e8814020303000c0d22a103c8070740c1800c21000c1ca80c3c8030700030042118142e082c0b220612a8154151604d40c90a0078000040400385a40c85c40d002b1100480040c1c0d000801031002d540c05100740368011a80c40c0055080c00d10420408a00c03000502540e07003c1c0380041020641590104840449407900500130000c105074440c3c6 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 221681483 1250 221680233 221680237
    0x906020715050f010e0c19020c042a020f0c010e010903120306090f05090d1805060409091101020d0c0b15130b040513050c0f01050c0303010801022701020d0c0311070803 74
    0x100c01c03c0b420b030850000408000d0800d016104408003c0c2c000e2400040c08000c1e02d0150340082520211312854000d04016215481211b41075894895111b030034001a070700841441c800d03a0002000c64218142c07503102120300144154400b1001d0030080040d250040048800c00100d500281c02d20185114481100e40c0642c01103099408018080c0303d6401850701c0c0c0c03010760320103585600b141e0780910359480d0342a11810141d45508680003185441d41d940b000010450f42051b0080c0381143ea40d5103141c820061008076042d8490400e00143c0900716060001500043d1941e03c00fa111080340f8000070f808100d4075000c00d070501c0c0d0042c80206020603a0704198020000a61000c0c01b851808000c100c072010010300322405035a028004242c101c030703000280506489452401814030000b03001070103042c2c0041c400b440c041d0600c08001a21180e09407d20b000e6900046400450084190f22400d400e0b640400e081c01008817a041c15107191182c0c2c40c0895001c000444c040000703004283c80401c02d0300000c40 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 221682733 1250 221681483 221681491
    0xf0103060f090206090f0a0512100c0c0203060c03070201140103060b09070e0d02060f090424060f080a020c07031704030302010f0209060a080702031201030c17070e0109090602071505 80
    0x30080040c048014070311802c48044000c0030b5031001e02071010700d01c1c621b00511800f4141c84050710042c20b1940d504003081e6107040440c00c40e64070390001580030f002e2a03e01c0c4a00c2019101603d450341e012201c6801103500c07071502610000101c940000002c21541c002d402c850800f0394040840b1203150b0f0349080640040c540300c40040d215040c00400304140c9442000e03140b640040091640090350f045a0070071800354041d580a40401000f4400000280d486220385800400c0750b241c8050520001805602110404c0c0c1241c4144a40c4031441c103050f50f48420300561100c40c010300141c0c1d4503034514110f494410254002050380c8980039000082d4400480039104682c403d400a220303e10030410f17120241c0c001c5104054100c0c0d028048503c03680d03c1060500d406c101c2d00d005492a2510b41c017403504c0f03144008d80099071a102484800c0158034083e0f8081c0070540c00402c0a422024181510154401c0c03040c4690424103442c0c4071108103101060b0304454000d5484521400380180d042181c02c040e1400311 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 221683983 1250 221682733 221682743
    0x60705040510080108060114130204030305040f0b030f0f09010b030d03061d041709010909060e04031707020604033f15081c0311030a05090d021504080d020f030f0103 73
    0x41c41c1c6102e00401c50903050f02c8800000c2c0840e60300b041000c0c4031400c142307010182d0003000240034024104603840217001960295603096940c40c10000c2c90310900c9039580c01128802010010048d005060401c9103804c8410b5149030125030300c1e420b608a02414062900b02e505002d2102e0b100381c1c5503016403144040b149805031440e200d0a0258081da0001802c48029210b2007104d1021108403240728001c00c5039036014180340800c25100e4211008685082e007103408807803105c038140414903402a80ca1020118840d1515192303107440c03036009441d400085e1005041c400322080000c08644030008600d9261004018280c0e201e01160014061308072a808503070602d490711f40f0b042c07400000001c1f540d003580c5c001e01c010040c001ca803040c4070340240e64000d10310007050380d00c0c440701440100000c010340c01900c60b40001300d120b0a01140070f030b007031861f4001510b040d548803503290066282e0140c441c0c4c2e03019420030a1183c80d002c103160b18001910824001da00814800001c00084030200c17486581a00d00030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 221685233 1250 221683983 221683999
    0x1206090a021002010b060702040c1701410f01050c010207060b0406080705031b040f061404050604020405030a0f1703130c05011412040f0203060c041a040f06110c030607050405 77
    0x2d48003d0f4221460f8165943d0001410040b85001d42002e40040802c01e00d80e01d041c6820700c8007440e020b1050b800030b1700103180419072900c1184520044080b020140800c0d03807028034080952120261280704480d200380e005588500e10304d45168026400d070b50040448200a45d0364035854a8070400034041803128512462a009021583e2440007901d102a1680540240824451060b104002096114085900589a5002e541c640b25580550301c020b044000b0300640b10000c000c10403066070b000402c1e1500585c0705200802c481c0e940050b03050003036a000120142c40410340c0c00e2a81004804060898101d94000140301343c0d4010803441411240c068503020780c40a03111001195000200c40041c01c5501c0b042c00b0752042100d40e0341c1d08c01c0e00644210200e0720039045640c04a42888001c4400d06812803000c202085258003114540b41f0040d02400440d18203070074000d51602c502c019000320f00400c0782c844c4421101030010805a41070302c0f00201110010b01c1c204000400a07070081c00741030300407800c0d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 221686483 1250 221685233 221685259
    0xf2106020f07140c211c0309110d0c0b071119050a0608072f0f011b020705032113090501090f020315010503090a0804080606010e06030121021206090a02 67
    0x701060354420350307034010401c0324804c03428040b120304000400100381080c0a06e903a16441803402c5040521384080d075840100d0780700b07140e00707200310101c14440b5603900074100c3e01150000109084080c0d4155202640401c0e00c842d0306d41041c0c0b0305004c3c403141058002d01100c655006210b1404250411540203e41c00f80106842d10300c2107030800340075500240400c0b100c64030850483c140b0601e01c940c0102c0d0b0844803407491515904180380010f48030070421141d40d201c3e94140310510940d0003201c1d2b00068001440744500c0d0601081c0c1c1c2c0c410512841d10044e50154440c0d0208104104a40031031800c103c100c0032480c1c40d6620034009000a12625139580e00d403805c00c0000c0c042d1402903d00c242e01522040c003072007461f40019550359100500c000d00798090b0700f0f8500c0005070a600904043c080c078000038141e919100c070014180450300030500d4031a0609000410400c044420804214503103400010035514203071002c01c1d901c023154048074609010740700400401c0b601c0005c0e00202c0c50300803a100d2803070402c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 221687733 1250 221686483 221686523
    0x40f1d090703031d0619030b010305010b122403070b0307020c040618050c0f12041b08030d0b0f0a080607030f0209060a0503040f020405040b010608100f2106020f07 72
    0x40520000f80800c102d80388902d026001072400b111851301c0600080e2414a800d0a050b5030007070315400c081e0200341da81c1c50241031564035115007409021a0b40718180741202c000760302000c0710300c01000d0a8083d8131301601c512801c58022020005030030040e08841c48a0f0315102010740c2c0350401c40c0c0b044014800c01542100c64a4140130b800116070070030414822400f0680c030a0009807200a0004004841c200a141020820603008041c440b0300c00d40600341500381b600c0c010b5103280ea05040706141800d29041441841808011543d040d42c07840000901c28250001046414650125950740000c0400c0001120400424814895209036400f0410110010f0b10f0034120301481c1e09840d0808001e206501c10342d0301610046401900801215410329001d074001010344000701c50440703c241d00c0d003004100d115084014150003c507102c034504007141c1031080b1220804040e03c28886415030000185d10449a215260760a05802c40810355403213212801c056020307440403104481039035100c41c0103c2104 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 221688983 1250 221687733 221687743
    0x41a0c0c0d02010c0c020d0f0212010b0f042c07030204020a030c1209120c06060302100201060303171b03040204021c02130b040e010314240a1a0f0402030903040f1d09 73
    0x82c07490307141c0b140c82179019000d0002900320341504039120056502084090303551840603070341000e86800041005000c0701c05014155102a52a900607810400c01003010410000400b0310020105c00c2441000003c006241c60101d643d4006500030384005604500d2036850303003001003065030646411081860490720303842241e80807200035109915000c4e41041c05407040780e1540b0541d000b20300c0031404a0720f0381c00141342c0711141e038244d1001d40e646d020100101078005041010340c000d0b604141c08a4a030111082010030994034401c000c0143c000001400c56644d58181e40910701801d0126094030002c0322048000e522461030102d44100c14080080d121512000b1181581d400c83c0c003040301c5901c0e40c2c0c1ca14540c0038048800080c5030080355401c02e0740c01150b1403501d41303110901304046d030385091100c1120b00301c3d02d81c0300c02200c0303c02150b0f0f8166403030b4031449817005144c5030960740140e49907500000642036008a4000c9900751104020000d50320010515804030b8161011821085855402181b9556 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 221690233 1250 221688983 221689001
    0x702030a080406050712020c010501050117040804030f02060d020a03091707081902010902030d02030405131a190f06020f0609011518060506040e150301050717041a0c0c0d0201 77
    0x55101d400540000c80e290066078210041c1d0500c0c225000c0714143d0b038802e036005031000f442203a5480004110a42c4c1c481a5080e983e07429000054082c01d050301d80764201e201300c0c0409400003110541c290210f44a046c1191035506204000f1900c501003040001c1c003a0294003000d82d6480202c040080141e03583c941101c41e01d82e4058281460220070780b84000c44407501d10040302c10b40d503845502c0360160b1002d01c01402c03d06002c1d405956214240020000c20031070522980c44420324000c080d1240e00c207190741c180c0c200304044816070148400c1a6400c00101038941200c14064582c0d58005260368000440700c107007855a0040c0c030031a03078642c601c281c225450202c5078410030170400003c00c0f080654844100c1034200080c80030800c0350304c41c030110702640d00960000c40b10a03e61010001d8001c3ea40d0803d41548204800034401303414412001000d9000713810a40014009030400700d400c12180350315110311a9400349038030000b071801c1000c1358001d070010302c0d01d0607250041800b00360405206210305008 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 221691483 1250 221690233 221690237
    0x905030c030a030e1201020a0807020d02010204061718010630031e11070e090c031522020409050f28030309140a080903010c02070e0c160b090a06050702030a 69
    0x400c0c031160310304503140750f081002e845c4c005103400c10707507400385c0c4081c0000d000d1045d66441c0c0700b009041c1540000d1800c00c510180c1821644140014480554000014500d242c0c8104510710a41c03242070b242d100780110040d0f4a0031940c0303032180000d00c6909640300d003d60300e10301083d0300c0c228014241c41000070f58002c160050002d030103c422007018100016480c03480d5615450040300003085543c1e80b42ca00040c1d90030075140000341da4100607100c00c00300009507138458140c0140040c0d202a0441a01c40700c40644002410301ea00240b00ad81000100c1c001d0003040d0f0000d10a02889102c0e0070240d0301d03102d80e03025800240c0100000a421004110203001c0c0c802610310100303040f05011b40703048008000c42201224100c405400030484880300700072040b44580a070010640e241d80000c205400c40c0d021112000a54000310820410f220070100c9440e03200c84001201559142458404403d8150684005003910383d10014007480c80800070340da481c070603c240c070100211303102c44000781d0f5a03014400d00400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 221692733 1250 221691483 221691493
    0x2706030d050403080904021c0203040302070e070f020606010e151207090b1804090c08060f0a0f06230f060706050405010b0603090d0f020f030f0c0d0504121e20010905030c03 76
    0xf0283c14264018800c8c1210525403c4030f11440340d90310000ea034400e03582600164800101400702c0d9810300b01c400d402c14400c2c203000d1211304004402070340760b10005100034141300b5000c00c0503071540c1f902c03030010000141c05084c51b84c0c1c9000c0e500300041c2041c0282d0303207200055084480403814050070000c45000319069484880301c2c0401004100c05403249032030443c0c40300d109081c0000c14031070030005640540c408030601440e518204c0e45540c1181c007222401d90340b850030020104801c0c1c0c0c5082c01508010303052a6443c020451040120706c400c000210107a0b0410f40000d500801c0c0042540200d000d984100024400031440d00c0c2040b48a01060310210907640012048003606401940ca40c0680009401540d2400b102210303501d0454001c0b41c29030103250000a442c0e1140401481a5041d0400c1401c04909050620b0300b8030320041c480900090141c48441a000d0900911981c9904201d6118034803803244d0180d080c0545807007216403181400b09100200100f0b15140106d503250a041340500249 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 221693983 1250 221692733 221692747
    0xe030c10090510090f1707020306090d200f1903110c0604050d1b06030209190b0a05030406020906030a0209090a0c1b020f09070201020717070b0c092706030d05040308 73
    0x80018040c4c203c04642c0c00980081c0440092500b103403406090305048201034481540340141030500304000d10840f090340000064454082c0c0040b210440c90b00240742c0202c0c0f01c0080301c00103241100f940392041f01445500d5011401448000c400e032035051080d80d44020745134081c0300a59944140120b0715034014030a100078400c0341003844848051602031024900b1140b081001c0c22448580d80d04940000b030340006144210741050440c1c0710200c0040701c6844282403508c4c01c07100ca94004c144d00001081170001c00300742405074a070141c4842000c010407403540c0c0d040c514400340095001d181610b0051078103000040f0104942e00c5070706020b90345d0fa01c40c500e4200d4084050140e0308040c41040b644005d40e210508455141da206151040c43c041c1c000599031002030412000720042d009c110403c14030208802400118261100d0b03800c4200ca41c0c10980780d280042c002842e95640305528080c111003401602c904440c1030704018000c003819000d942d41d801c0306e00c1044800303204900019041410800002d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 221695233 1250 221693983 221694013
    0x20a0518030c090f07170603190c0806010e190203060a291201050307080a05190609050a05060106080105030a080f03060103021c02030f0604090f1101120e030c100905 73
    0x50300d50303000050a4502142140c0c001541c0604142c4400b01c031340f090001004030301900b0200040160240d804440018075040c000240d4503900c1d4490222140054440d003402c20644859200161400703400b40c1e502d40d80c41c0c0f609184102000c40c1e03160101c042d2940600c04052991080360f020b070501a02090502e0b050170314030951007080c2598042d4402c001c191080291200d480501400841c00b03e000c0e0b41540340070105480e26106030000c60721034002e0b00480b800204001107121458070740007002490301200d820403000030200e105010303007180210640041007240c0402d5081c142c1d4029264856036980b03500500d0740d030789001500240800000c22144000e060b030040650ba2142c41490090315003504004903000d0740d06a100f14074400d40e004410300903001e050444413603110382c05840801c8003200039203a00705551460540600100c016200000d540d0340b18081440c54015040803c1c015078081814141d920b500c6a0f120385998000c469151520317400c203002d02c0c0b02d61600030300203140045100d866 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 221696483 1250 221695233 221695267
    0x1707050403030219080c0d0201090c05030f06180c040c020d022107081b030c030d0605010302030f0610020124031e0b01231003050f0f090607110109050a1b09020a05 72
    0x58844030750503c04003c083c0d03007c100d0860403101c2540040f41044092030010501540e503000244242c100c5803411804400005109900c260200036039005010380044c07040c00d2594117840749030000d04203200f0795403d0390001000f0041d034801c4e83c2120243c41e0458011030ba4600c01c002c040180810810480012641c420082c2007502019409034039074000940c1510700d1588254528417a540010850b20114121442094001d180a0070250300c0d501d80380104200408004200c180324007403815455012a10035440049103004100b40e1a200c003075036102d00400b40d42c480c44112480b111208194001c0041001114032145d48910401d081ea42440d45011640c0355068698800f40102d9074202000d40c0e843c003c0122a24050f2000180d50400041e4034851390f1005002d4032620710003030306000c01c0c2000043e05ca50b11050038904035002c5130a4903202800b4042019000c1c1140c8a0041c144050110000c0300414140000c1d640c80e000c1d55075040303400c05038095151007001140d8244444811700d258810 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 221697733 1250 221696483 221696533
    0x409020118030b04020907030b1c0602191d0409080a030509160b120702010e1b040f06170601060f0905011b0807030801051207050604031b03020d0317070504030302 72
    0x421984035200c441c40045042203580c0140d0f1441d900409200c00d6041028070150089050b00e41030141003800004107001c040700d2001407944000b02610310b814003409505480414000f0b10314501c421041180c000d100d400d401805008000c0125480c186a2030030740719541d402176000180c03034101000e088080c0d0081c20000e241d80414007900e8042c03155800c1883c3c00f40003038a10064042e48034031012060910b60027004000105580c50074080d00c0302a4000252060580b800380404200c000d40e08010070060503001c5205483c1a080c0310011511000c01c0d0313070200f1150055011a42075030f81c0d07804203c9a4001c0c2d6000c0307001140f60b90b2070610a1354411101d0400c1260340c0b03000e00d40c20350403d98a085041e4028041500000c130464018031451030640c0400d884515130000601d42d450500d00080c1507407040f0b200092203a5090040d2440c80c110018864000b950000e0940341c600302a0b0034040c0c01c076a415031020700340a1784800041c549a0243c4113607415241c165005008000700240d40c1807400011403 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 221698983 1250 221697733 221697737
    0x80d0c06230112050f030a020f1005090619021c0f0507030203040305030103080903010b15190f1706040f0608030309070506031902030402040902040c031406030318130e0703060c0e030604080904090201 88
    0x1c0205c0c0380c1700c1c01c00080c0303581c40c21039000780b5a81d0708214185c0e080a9200303050101607820f1100380705884a0001d90640c0190007101d40e46248a004030a14009200f60201c648008002a13001d68220b4296485004c015440a205000c1e070756940c032040741240b008070b030024003041d4148010b0022444201c040d0141500180000584c14141800039055694810460907055000550030340030324085140800c401070a0300303003140030340820100a4442c85940c0c00120801c418080028103a586680215582d60b1042404003c016198801c0945a9108a4803081d00f44100701c40000d26061035411288200304100400d2000300000c40b00760042c0d40060016640192242c04110160b034981c4240109020240ca00203950100d216005400c181d00a20b50352280e001400042c10300541c000d0713120544441102e5507070b1a007484150358002000110b44600ca0391080e11004000c110f00f642c810500b0310304684800304004e198004250740c035081190014a1410240500166802d10342c000101b0342d4814 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 221700233 1250 221698983 221698993
    0xa09030c0e04120f02190c0e10081204032d0b010b130503011a04050601050403060e010b010e030f0703200429010801080d0e0a080d0c0623011205 64
    0x180d15440841185034018a065280c4502480100141d2044581c0382c80d0203420320108000c02104007079207070304e540400c9041504030203410700104a001580000504030858000300141014500300100e40d5250240c00c00318400e1742406044c59081c40140c80442c0d078464654400f800380b54800d001409407540d20244c100707502d803051100107241600b4440c045d00700c0c3c01d02035403150300e1104244039584055012501a91401c0441e041014109400c0b0582071019200800c058542c0f41c01218107204540c4050105c1e0310346040100200d1041d0400020102e0136603800344082d07540030030180c59190501051082d940109810070000b80155498006446690800510f441d018404141980d18001005010310b03c3e58402c004000b0f00800340d040303100820b01e071000203581041c09181c0e580b000805c8000c1400b9111140301041d607502050640908080400e6039041903990324040c00c5410445011038100c1e041c214500c0c0014a260710684000c03030200300c0c0031040d03440c00284562042c1ca10105482c24055 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 221701483 1250 221700233 221700239
    0x1006120b240d03020114060a0f05060318060c04080d09050102030a0e0a0f0602010b0a0b070506072d020a11041a060c15072a020603010603020307030605150d05010f060804080a09 78
    0x4107981a0b010303034002d40021940c5400001890307241c820003000340d44250b14500d0203014000702d0004210544409890155894540c07802e2041c48518000ac5c9101c10310465003000151100c4001600c102e8581e0411a02c80d40e07008542a82c00100303500881e40103074018400d021a5038425002000c440d0b0001d000d000a054440a854001d115a40c0149000d43c0d1154000c0c4880d04100702d44c00300030401c4100c098100b00d2950350702c6071615805030131175003049100008000d842c40c000748490341140290701c1100d514400080041d442d00c0e02c02c0d4069911280500a00c3d8060410f40101948004190485079038541601e040001e1500100540e0490303101300f6400c009040a03d05500340101903c2e11440c4400d80c95030700c2e80402c080300803155841100c640321800c0040c0c403450266410b40c2c815090143e2641c3d1421030460003070206038052a030100d500d00c2e40800e81c1c2c446070020304000d80444424400b581c2c0b910401c4040e1b507418490389002824400004001c0f402410281505100a29100900c40d275 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 221702733 1250 221701483 221701489
    0x3080a0f090210170f0108030a05070302012c06090d08160507020306011d0c0f0301030308070c0b0403090620071208041e050109080a020a2705091006120b24 69
    0x401c24580e20040394008112020b0f03404c083e00321942c803c0b00306103140c441e50704100446440c0c0c001e00c01c1c201305201000c580102018000e400001d01220042c07200c40c141414000c0b00a2040303c2081103130a00d004910120f40300a1000c295044000082d450f5849191a012481c10a41d102c7c10090820004148200c0c00169418440107008205c4407150160b2419084961400c040c8050010201c084d004c202000c09211400d06690450350103040c919281c0c0d07a080010b4070002c500725401841c0680e00820041015001442d030b82c150f41380b40d0390700030443d0761030114004040d0010300c200c80c096004520800807500d0010807001c04074445e05446060070f13560701903370120305064064403020300c1e007848043c0115640700c0f100900501800c001021400081d401182d401001303070045d81002070300807901590100030500d200440c000070140400c45850802e4005840300d400c00094003019040c180c000542000c854182c1d08055003191050009449003c651400c0500b0700320720170b180d01115103003e80180c0e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 221703983 1250 221702733 221702749
    0x6060d06030b040503040602060f250c0501140901050105060c1009020f060a0e012c010f0207050d0f02090109050105010518010e1f110d0c0201050d020c030412050f01050403080a0f0902 81
    0x3c2e01c900021070300d65040541c0641030400041941c00600070070307400c00441851000c1120010b950407000c3c05000c4082c002e046400d4100428090007542c00c0c82c0c0e850b280e8805042d91644501d00c000000c02140e600d074401c1080e1071251405220490b4880714111000d24455405100702901c01070516522070000c3d404112960021080c100c0440c8002e040c10150b540c11449503881c801c1c00d0280018404140081080c64615244900b0b04000d012020803100a00810500b8040c00c0c0c010001d981d910414608050469440b510481c081c0319408000601c180e039901699060ba0700584483d070400c00607003c070303001c560000640d950401c038152400c007001e600c0340380542e880e54940c0744130030300801d915000181400b0660301c6e1a0046a100301c180c0308805522010407014a542403a116584040c920107200282c042e4040c6000b05001c00503000545100b103100c950107551040090715010090448640e007219021500076001c1140000059070702c51055028545902203541cec005414142500414101 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 221705233 1250 221703983 221703991
    0x4111308070608130f061505121f02130608130611040819020a1406040b18270402120102070f030f09120f020111030d0203040302031801051206060d06030b 68
    0x29802541c0d0621145900084042d8040da4000c3c08000c10340c4c2c241c0e1502600700400b4400b40c401e50342d80304201030888041c040c0100600c0014544044240a082c101340c80f104480700c140301801d40c110480c110100c89000361038450401d0007141d15160302c0d2400035110520000c100b0b0f031a015221004000003412486030844800c042c41d0001d0321107041c4020185040e50b91009078a0340f081c810300c641c0c0141d586003d0181600d240201044000b848000483c0c01e074026500700890718080821720b1601200500019030311060101c89010500c4d03030038030760302c140401c5161000c0b01e25000303240002d000d4144140102034121001000603e80701d01178807440c0031a9603c18088000800078110480e1455000b44214050040c074004601040350659030354100208010000703041c00410611400c2a04040c01520203a1204502c10f5589207007601e0002d48030340c400c460141004482040c1c0c40700355441039080d0340040800e40c038410000c3d00c454003000801d410912100f000b450b164038022000454102c549809 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 221706483 1250 221705233 221705249
    0x501060806070e041e0e0309211212060f060d0c030c1e0c0605091e0a05061503030304060905010b04020d020d05070e01050f070c0b03070507060605120a02041113 71
    0x41c1c0c101410010200380380380c81c2c00340c8030358100350451a6044001d560400700d500c04080000d40018940201c03030450282c00d0340668040c40010701214420f40c0c403403203e60300720078030015600343ca4101d1502802c14003580505120b1040c107140040d070386081c1400ca44c5a00c1000402c0700b0301b0725040d4015403095941001c1c0c1c61000079260206428460f822016140003410b00b46040c4010340900740c4001c0c09401e2154000d0700c2d03140c443c400304103142e0381403280a0404000c081030004500100000d15175420036094120b500740b00326000036244881d0711101034034800006014600e151626192070000c1e0801503016100d55503584c0340d082040c0d895200910107015401001342c0c0710010244400221007005000c3c5082c41018862808240e070302008a4180e00211015640c440300c0c0d0781031003a1811a076420103807100000205200c05150000041e01c0c6180c4200f000f4003106884078240140d944002107030303e10988c80350204100501e4190003407003001105040e042e04103000c1d40c51805806840307a0003044 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 221707733 1250 221706483 221706493
    0x30903050f03191b050f0f0c01110a0807020102070c030f061e0c030b0303070c03081605060106111014072106060504030b07030b0906210f0c120705060f0906040305010608 75
    0x244036403e00403074002c2040210289213184002d040903040e4815445803803d0315900203041c0340c10443d400c0c02d903030084a80d20020010312403207403030300c00c00d41c1d101e1a00800407840308030000d00594814000c45034400d9004000d00502c031700d50350f51032203c1c46400804450654540d0320034246403400403800d4920003103802001ca455010120060308a50203107444a002c3d8004008480209241962420071240d1004c04650307608643c003080c4a0418900100a1140c0118000000d00c0ca40c0982c1c001600030a0307500307882ea4801c4905080b411513090489a5090580140000343c006001e26a11503007a070a80415901e1078902ca440b8400b169080d1301320401061004c1802c1c01070012010483e54031107040d00301000b40100d4140014100a030045c0618812080e1050411030401c806c0840c500d1154001c0880d0854011486100d0700e405920119a000d007400103101207159600184040403900090985440c0c0104807248401c3d60f41b00ca0780e02c5421820812000000580c2442120300138480d0b01d020f01 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 221708983 1250 221707733 221707771
    0xd0507060e06071101050703140304050109110324060406050d0b1605120408070206040806101e0303080f090a0210122019091205011a01140406030903050f03 69
    0x600100412035203070740038182c02d000d2140000d802c44516070b10420700342000b81e120340485c5801c0310b0605030001c01e440c8500d008401c0c001001815042000043d12031156100c0b1090301c0d000f816a41c01d0342d00c1c14001d008243e4400c4045e038156040a46401c82d101030f00224003d038840c0081003d0429981c0212040f0000004200036034111a500d505c0c0704002c1d14146103042034290140d0244d000c09440902411000104c0908558801044800601141099461502e4484400a98075045214916101c102e180015030081800818481503e5168454140c039496100d0304084c00c0c5030050a0408503c92001c00382c015035030390a5a03000384030f6159079161241440c640668203a40900074902d140d42241c807810160a12904140c46030440303c2c003040b030152105000700716411a101c1d403101a075010310130f8540c42400419000042e81cad04080e001c01c040c2416860045412252a251090350490203100501c029803003501300e10304090203480d1490174002c070361000b09000e61050300c0079100c01d403807000d0035 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 221710233 1250 221708983 221708987
    0xd05030d0c0504050d03051c0f0903090503030301080a1506050409140d02010603080405041a0a06020d0809060105010c0b0a0e15070f020a0b07050a180e01031a060303070b07030b0d050706 82
    0xa111900c0941c5002c40c2060302d0400801d44030441400024217000d0080789a0240c682820312011461105230001d03c01c15854207044030041441c140c0580003c2e010510105041c00c00004682c120b491a0005003d00d820640b660218002031100103900c89490b1000050f040d61280102120540903640400e4446000c9850f24a0808680388020540e410000c0400100e114034003503904407036081d64049101006200c03c0c03c8412014050164088110907010408542c00500e8034007030803542c5c5540c0301a80301c1000c1706039a02d400744501c50006680819103400601d448202a800c03540d16000403804064001016050962074010001c0000d000306c00c01000d2035100980c41001403d90025000c056003d031903a030a940300c0100380e0001e0141c00560300b90140d210703e00f900540000e104034552115140c444107807540c0002e21007691240801004c007010208411042401094001e00843c075000c85641d0f043d070800d40003070812040c5907039450010b51580f580100701c2003003031064001d410020305000e00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 221711483 1250 221710233 221710241
    0x1808030f010e040b070e011806090524040303050f0c0d03150e0417091c080703030e1902040b011736070e04170c0c0906010f020303240d05030d 63
    0x3101840d6040c080c00b0100303030004c503800c1e081328140c0307002002818801c0042c2d07045030408030f156442807040f07c1d0000300541c1c00303074040c025218110380740f402e031612030402d00d14000a51903501100341c00030041000002d000d5401449100b4821100904040b503120700c0504241c0007030111000b0a860b100e490800d0900c111190014054903c8440990b041a441d501d0b02500009007140309800d00141180555864940c800405a10041c010449a52529000032290070152007200402d0402d80b4200e45180080782d125201d0024000c1c00c0d8094079280c0801c8040c2204803c66410322017580b800c80010f0119080307143c0301300c02d60900208900717103084009440440004881388504519066002a05000728024007291100350800c0000d48481c100400441304280c4840d402001c0004c940141c501c0104c0c644c00c1c011012283c0aa082e0f9841c0b0054406800e49580f01c40180c200700000f03241c1100010740511840f03944a910b4500511800100380744400d400307400d503450761010070401c254181d2809 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 221712733 1250 221711483 221711489
    0x603060f170c090a151815031a0c1923090109030b040c05100804030e060a0804060c021e010603050120090d050111180306070f021b03011808030f01 65
    0x102182503244400c4498851038450103140c4244518800704011302c100d40c100a020300d50011740540341c19030711702c1d0007990200800c182c1100c3c10700f0441c0740121226052010000c4a03044101060000c07000d034416013408900603c1c2d00283c8206122202620101012680e5030100686502c0c50b200c10302455210f03081070b120000e2400b43e40801c00440a6640708044c801129404100c0c03810688443c9882c0181c103a65410198010185030030204550b81e0001849000340d001303848001c1458184820700180b03102d00500800070510b40c4020400180703040d44104500100d910644000c449060b02c4190381c44254024502243c0d100c030001d00c01d0050030f21409100c040070210900c404500c1c002002110b005840c01d0610500d000e40d21141480000e4200b210181540d0100c0780d5500312112500a000f00e02c00c8291f4020700c42c0e0000220954041d240031b00030b00126400900300c801d080a640c0e000c0040c2003480603010b540326008ca00d80c00c5903c0300d86205480c401d51001d83c4a241c10340b000c04141b00164 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 221713983 1250 221712733 221712749
    0x7050702092802090604080303040825081602030c03060a060603140105031c05070803040503040317030f010e06010504080601090e0f1513060b06031006031d06060d0c0b03010603060f 80
    0x40b4420180340035a92192203800e200740b005a19004000700080450085a001d007107140400401c10040011407001003c40901c0074042c103051900f89400c0c0e084112100000030940358041007001e40340e02400281825092004040700c64040c10400484e081c000203564581c42a9101c040c03d001da107030540030311070008100440520156141400080d0340c0c00403000400303c4a1036192641d40203511441c00c407010703560013281c01c076580c1c00e1520f8402d98130340c02840f0079a05450044000950805903008407401085070440410490b4240707a00a036103a40c001d055a818000c00f080005100002800b140d4000d1120240000304c24091102d203509001031111508200d401511004407041c113540d000503089044855503144001c410701d072a1005000103403102d03600074070220800c008040340381d5038031040e01c41c2c030b0307606101c890a5244c800e1840152170307800d040a0b0304604001030b01410541d01d005051400360403d451226902d18454007d41c0c4281c21050000c3c2d1510700c00c0c080d0020051400700101144 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 221715233 1250 221713983 221714011
    0x10c0203030d021326060a05071d210601032a03171c020c070b0f0a120b0405090a0b09150a0504020f030601090b040b03060c04060f0203040306050705070209 69
    0x1a40081c0d00c03407060440c0201540d03404110901c0100710080c4020141941c2c2c00c800c074401810032006400d40c020006980124071812000903080302150058600139030064a074450704001c1070b6081a250022941420b4101d00c03003090200392082402c0780c1c0c940204418000d89407650450500500c540c91446144c07080361034120050719041103000184003140e403c0728120400b0420002e908549200702161074007201c9101904507042c04696000b001501c4120085550350340d550210421580101d08a01d807242009004001e10640110940b103007001d07040070300081c00b84400001404031141501c024026900c2103081c84100200c00143c640c1195140d402007902240c100c0603a94117640c020310020200340c607440440c0454030f90711811a92454002c0a4410030740c0c586007440b004180c1d0728010383c440c50800d00a4905420007040080c0500b20b0910480d181c242003002c00e0301c0c010b54000c07400b41144010440080822540d204081c050880b40e503926642d908540100a5201d0004c1c0190841d1391403 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 221716483 1250 221715233 221715257
    0x20603072318130605030703060c300c120e03070210020312060f12060403030c030f0b060301030308061201060e0105090601030c090509070c050106080c100c0312051909060b0a0501 79
    0x14a008032038290300711010103d05485aa102c0b010f032981d07901454051083d4400401000401d42112410582c2a074809080300c0d030a904050088400a4109841070308080e0000a611001d801202c40c550207418071010351440c28084e032007110205107000110b5000440c800085160905002421b0b00481c0300640c14089000c00c24061400054160362085103044101281d47d211004107848a1060074107031000b0b40b405003006030140603050305040c006807600c52400b4a412091203150303c1c010000d81303c1e074116821503030309994501c4040d00d00750344150f010401e0148007000340180300c044c1503d80e0603140d00354074010a1026441000e842141403600b000d0030a09902e41c08500c220827100e044501d0300d829203580d9000d50704a607420074013400e25403c080300071996100c0000d8807404940182d901e41d00e2035400500888140820000090000304036813020308104800b500416084803c1100d034a0030110380c910500d0440d1102e080c12a03460340c60b0802050245825180d01d40100400c0c02c1280c40307610 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 221717733 1250 221716483 221716507
    0x1030c15020304060905090a11070507050f01020a0302060a0c020a0804090218060304020607060b040f06060201050405100501060f140f18090105030105091e0c0d03050403060e0102090a150c0206030723 88
    0x149030302400e03001e0362242e00040d424039015040000327002c203580c0c1d0103580c1c0c0c80c40742400b5441d4000e5014043c000d005014900c4e03019440082c1842c19150983c0c0600b81c175441d04109007000c0c01204061000314418819a100481c0c0d2031070040009240c0035200580d034240003c1403580e41d11402c8840361040300141304110140e10780b541221883c48e40140e0014000d01d030900006c004000308000340c02c16515010b400f0400701e0301540720f03502840c020f00444032802c81011000d81642c0090003000d0000f04018140d504c2d8900810500c1e922800d40c05c0024240340148440064582151480088020644a000d00c80b424405102c50241006034000c1c0550314241e00c40c65542c50410340c802c003040e03454074503598a8100c14060125210703001000365000060710300380245036070000c0c042a1040e5161506040290300e0510807200a80300203001d80d2078a92401c5400841041441c2d80f060034020340c202103800580e15a4003c500c0f811654130f0b449a400101c501c0c40b210548051100c1c5141d0000300302900250b4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 221718983 1250 221717733 221717747
    0x5210403030c05070b0309030c0606030a02010906080712050a0b2d10050405030a05010e061614212a040b07081b01140f06010e0a0b030a06050901030c1502030406 71
    0x398141c140524216294a8030924044c900d40c401d02d00003d010050003030307615001c0020800729410008484094840f50105619410b052000038041240c00d0402c026450294145541c018910b01b1304c4d0385100c007400204800c0d20401c40d0454550765a40d003c131007580c50081d0410244040e0380c42c40e80d00ca03800c2c078080c0c01010442155154400c40a40e80c110f4a1603105904a50103080003500396a2641c0c01440c00758013802841032503280703600400740040d503006030300c102040200115a0b174100e04500214220400c0f13900c038a0820a0454600c2e840180d0900055080e81c01891200803002100c4c2d1505c209400e1309040a02c0160308160402080104189041c1651400f41d088100c0640d190400400301580030700802000b0707440d500746400d621054506284052003400d02c0e5118142c16500c180045401c00080403903180d019020070418854089008041d5900200000000410589407000500034075004d0340100c42c03041b1591420320010012500749900c1c03404a00041d4106410480702420314 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 221720233 1250 221718983 221718989
    0x21c0e030c1216020a08060105010e15070f0f12080103021f051806041e0603061508040b09010f090803061201050708151f080603010501050303030717060f1804052104 73
    0x900c00120f0024030316000741d4204200c103540142520051903592401a850b04024070603140460304213800d0b01c50500701105460b688079905a4030303a00e06090755440d0700e160300c0b00e20340555001044101310301c000f4201c0c1c60002c109942c29260900c25600d10320400c6088450040c140108858801e260540603030424250703200254000d085102401206001c519076000b503500100003211340380ca418046011380c043c41002c0da0700303640d4144507107922210340462696104500c1c20008051800040c04101c0402ca01c541100c6d58000100300b1110112480c0c0c00d4800c8180141c074405000170600040f803034100d1408500f400e10200a000ba883c011101502c0c1d610000c002e05072a603048181200c02d55561100c1c400029890700002d54003500c0c001e0001d0403642d0071640705020303628020022030a0304c3c0c000142c1740700300d030103a03107a030192500c010a81000e00e002408013a00f1550b14451203030aa920071040000d0014401c40d074203803600d81810803034a004107400412424103070a5025940380c0c0b00d2a801c440035 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 221721483 1250 221720233 221720263
    0x5070315030f110d12030b010302040308030604020a0311131e030203120a0315090626030306010c0501060308040b250c09050c0c010f06150201060b030411030a06021c0e030c 76
    0x15099500b005003c003503001e2041c81e44400b450660f00304012150441288a8107036a9040051212090066080384a5400060100c0c0428400214203203000d0300207080c040060300e00403502800700c84600800f500513034034140300c020000c41d09001c40e03002859005650740c0c040c05280140c9180d81c01294888840a03c000410200010101805da000741c100075400a099148004a030b075840689100500150103000750342010031800e042d0340b80719264425142c101580c00b552941e214a0300540701800d682d0030131260740d5290754001012034603440180004000e800344003640e8658484c1d410100c3c40a940c006519442c01c80c83c4c2d9400300f85850422000e0b079044040009040d203a5500001c00d502850308282801e60a10280590820040d08800c2c110380c4003a5050528480d020320580c243c030110b0140c11404a8244005004a0405282c0e1581d5200240a894601146807240c0041c1d03032018034000030041485114414060381c80c03048080c0c2440801c065402c0c03120308488030b500c030381c85260714003e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 221722733 1250 221721483 221721503
    0xb19031e05060607051902012606120c04060e25050a0302031003050109030c050d032007110307090203060307050103060b030601030e010b0a1d0705090a0312020115080c040507031503 80
    0xb10588400c1e0840342c2d12a0040101da5080840780708042c0d01034030030001240000c0d5030329005185810280000c0c00c541c1c1505205070160341d80c2c0000e0128210704120f4440c0644101c1c01005225151440b840c4064612489880a03d00d0440782d03401d144002407050440e83c00f0403810f5400308a0b4000f0a4403071040d12844e016950380c03a2007803082402034440d003000d0429460208000304140c2c1010101004902c00c005440120318001815070031100440e03100801c0003408000441211002c40090981620400c03036401403030b4004000c40c3c074018a40e002000000c1d4000240a080d1500b046290b005001c03d19003886001c0c1000580e004500005c0d03e11070501d5243c0743d410446580c00e421108050300c02808144000b030b5150440c881d03104012000068080b142408940e08502c21806c581010801a1020808a00d50341d81c03e03d80c000c05007040002c555a910501c0300f1050b46054107001070950300b00512842541c3d404001c1107400182c03c071f41c01d040c41d000e0800c0b02c06001e28002012250050810341c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 221723983 1250 221722733 221722741
    0x203120f060a1a0706050f13030507020a030503031914040809060d1b0f0914030c15040801020f0a020105070207061d0d08030703140906071211130b19031e05 69
    0x2c0014842c3c0c0c01c0780110606044044549907000d00282201c580520030a02c1103489085000000c0107040c1c1d00e0f2803001085011210109016200400c01b2070310185c80e0141d41c0d95240c603003904541042c1c0300b1103481040946440041e00003401740100440408004070b98509141d0f6030f1101c6803041c1024280995400f0a4400008909520110360b80004080750b40c50030482c030038014500c00d500c20b2000040703541403001160b1160b03440e842401e400005401081c811b03440d0700412000504542c1c1000c21280c08000110f0508420300140c41801c801441190b152503c407140a429128018410b41c215803101c042004555440504102444101905d10310750740c001030041003445100101c05480741c5400001c1c00040399255100b8603009200c0d0002c8440ca032503100322a40c031090155000c800094242000c3c140c428803d5100f004410b600c82c208a11346020344418085840d2503034080420100c010170740b00108051150f000c1c60200d024134041042c00518000180e441000304c0d080780d91943e40e64005 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 221725233 1250 221723983 221723989
    0x1e051c1e08063c0d140c0a0e040803221a06130515060c010209040513050708070605090108060f09040b01031e051e2509060e040206030619090903020102090a05010203120f06 76
    0x80140e00d0317040205a40c0c0c1030b600404a654400326102c0b4203000c0d0000710301c000b5030100900c0040d80207541c001c0581d03113075854a00d07040b00030303800d200312829101c41103107460000104e4010402217041d050b00022541071811100f0820303100c03801d1905607400340c1880c00304038010300600301b68480440c003151107035102c4000b08041c500a01a12400c250001e1800c0180308100c00040102d9140611540c00c80b00c6054546c0c90460311498507106a01c08a00188410480e641c015010b144e400340d00034096407010100c3c800009d00382e920a84055950071072540c010700c140130188007410403c48103050b681e03d480032151b541d00d640c0d05512070bc070403034010150503004106900340060030708048000072000261005500000965119114013182c4e10b1412070001000c1300c0f41c46400e0f02c102d400610850944e510407041c8800004030322480480d1855030500824004c6c01c511075201998060f038001a11100d003a400d000710304074140c01040c195441070000c43c5c1c1c01d03003c0554050740121440100301c0b007511542c002c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 221726483 1250 221725233 221725249
    0x7110f01020c010603110406060801060311091f020c01020d0c08030c091002070611010603150506030f060702010e07170a150b040212041e051c1e08063c 67
    0x1805445500004070801d0502c01500000e040e60302441600070214510300400c0222800f41c4104000300fa0118010010a402984041c031442026500e0740d141c01070f075000003100c1c8801201c0c4a40d40f003402401d480d15060341000036841e03204003800101030f03c1c00000310140c030a54400e000202218000030029501d4036021050307032420032000c1c000d002c0040030130358041d440d04214041c2c0d00004895514206842505005800032030780c104204040c034101419080015104c02070030f50740c1510543c42106000341c01008a00d110b414298000650181d0141c01c450810b001a4801030702c14626449003050540302041960810f41d000c2c241100780060352869401514200e0850307a80b05202085045038030b00c1690841f445684a104181c880c2020054412081140c520018050f6030200d051900c03030804024038002c1008550902c400310805480702548120198400100004c1410342070142c18186425600c90600e03400d000044000c58013401760300d420b0202c005210301403d43c000300055585401c68 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 221727733 1250 221726483 221726503
    0x1e0203070306181b0b0414120a140c040b130b0a03050d03060303080906070909051f03080c1c0e010309020604090507020f19240b060408150c040303080711 68
    0x4014046124078a01003900c00100e10b4098031307035001400e4525a541032054120b41a034800c03411103401c060422208411100d01d0107001c03070b000449041448880c40c0300300444e8282503c601108103d50080f4410139081800080c00c0318004c9003002008005641d507110500078190502d03500150708942c100004000310040c0c0e00140040c0580034031805525416000320068030702030f45403204103031968170f40113942e21400c942207800603c4040c4140195103664008982200031708d120805018841000f40c0c4071146103a004849040c4001020721403500140254500f0b111489845000b0101a0102810849040051a04143c1d490800204650300d00c82520701420184008112a1800e01c2d40a9a1000d8483c954402842081c03014007000b440c0c01250b1406070740c840506146d03009038110032184852205980301c0c2858980313180518645901001d03000808041e001400645c4042d01d01e141c9804014101c203440000800c41400800d8000c0d13045a0401024603084e0303200c10110410600f0094070003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 221728983 1250 221727733 221727743
    0x130c0815060708031e0f090c010c03090503030a11010b043606050702010e0f0609030a03021b030708030a0b0105160305070203010905100b0a05030f060105010f02010b090a0203040308131e02030703 86
    0x4001e204d01003d251314200e0003005004017400f40345d1101d1483d118002011602000c965002e42e9801d02e565100d5000619118840c0c20001e1156071070320002411500040e24101c0040c4030f100000e0206042405003202c4100d06640c01c21804524000381402c1c02c008451402c05551845541800302141c100003900b80741d0001000c111900380075900a000c0c02854103a00f0041c0f180130058610700c440414030500403403640c00103516208085005502a401a026020111f40c4030b82c04032203800d105000400c280c2d8412800e055492900703000c0d081c21150014001410000300b8001e04d180300207580d0742c0554403501801c003141c070b550980c400039003d05503444008040707001c1e48040e0300f801009600320400c400702c121500241c40713440303800341540e8500c5092510a03a0740701d040100015400388008445800103403001207002c01c0c041000c00e40c0e410342501c01030b000c9a4000100428558000442c07604820404145066840c4503251540c40c0d00c00242d851010384240c400b1101196810091280196449 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 221730233 1250 221728983 221728987
    0x1b1505070c050f1b0f010c02030d0903030f0306080a03031a0406030809030c030a020303040e0c130803120a0b09010306051314010903110a0b2d0f06130c0815060708 72
    0x80400100100a103040807140c912850012030b024040105095429452000c4c540c0c82d81c2c0d50b02010010341c07812048246041c01040c1c07200b9030143c0c41c20b0001d4200150161500e0b03105030705d149070007071003603207080b407021700b0545498030074010b52101141800b00c154052030040f40014040c8009501d410000d0303501c42e4010316210002040203006009019007450032015584d4402169003415165040f5210080d41a0800c010034400c6410089040d90080030009900b802d01c1e40d0860b070742c05054000d42100d0700d1a40007080d01c03504d403030040c105980e10131480e62051111a02c10b80100705d460394103000085c0f007540c030b0b1800a803525940c01c032060309103900014440100301030809580d000740640d1314240e0002c0d036041c1c5000b00300d040c001984114130fa0b20050079041c664800444840030030304010404404007003048822040000c1d01e4002d0301a01120200342214100301c0c04200480d158400185101410008548001303600440c40503800480d69800c0c2905000b560f00248082c480c86100404103040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 221731483 1250 221730233 221730241
    0x1e03051b070906082b1b0807060b4c030614060313120e0a09050f0106021c0507020a030206041203083607082410061b1505 54
    0x4002a41c0e07084603100102084040d0f281c01c18940ca0303180c00c2949911740c014654a10285000241c0b008a10301c009140c4151040e00001020081040980342075a94120205d820780c1801035a10503140101400c9036000c0c4a01c00e40e0014030300c8110710a0003116081800b00340030780313682c030341c800c4c10003421410845050000e0f80c1900301400400c074034000c25400342c81c192860030320344c282601201c1c0500c1e0102040d01c0f1340c000540d00c1e00700c8150301500c400d0401036004e400b814107444030503044001e0100d95801156603d48040f5801e5442c00c164040c2086500010740c40e1940c007000302d402e40244140d46040d03582c8002600104581c03110707a900094101c1400240002d1401c040f40b0b651941a1180c0d454640d180c0b078800b4903032180f01c00340a6a80c150080c001031000d41540c00d134a07039080c4030320107000e44400d03907500c001050524428400c80042c0340c7d1940d4000c00c5403c9030030410340c0e1041c01c0890300308400703061007030040607802848000003a92041407002c905018040c2d000d030b00203007400b91040c841132070 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 221732733 1250 221731483 221731537
    0x102070b0d0e0c0a0302010e12030f130501031a01080619050d060507020607020309011706010c0b0a0501090e071a03040507090524090415050a0e01090b06011b1e0305 73
    0x30006102c2c0015001d881404150380c42c0c4032a8150440c0d405940e40b0640c22090341c200805103c24003101500b92004200710303264081407c01400204958008009460f85400e001400f603401e00001041039400321405540369a820403006034015105803841002c0f03100c910151502402282c00c481d6010101d080484100036194103d2481003c80d0381c20754440d5143e0090980c0d0700c0c004c900f2190b0100788030045400034030102e903403455400803051405019809a90300d41480e020402e0781c0b90301003a5100c4005210b4043c19000c0c0d00c2c10850300700004c14040340703000000417443d0307010f500d0358021110006c00b00d000d206040101c000a0280b01000300224204a039042c2d480d0001510003620410542c40d0362540c0b0718280d02d6581c425500080120302c0c5500448191000b400001c14800e2502d64403075925245000c2486510146403141c000c00340300b41000b10001d00255294250405040c0120041c10009a001d54507800c1c800381440e880b0100d42e0322403030140c038280204420403440002602e08000140 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 221733983 1250 221732733 221732741
    0x1e030301080d020313030602030a0902061306031a1c0204330501030501080d1103130608061c120302090307090c050909090f0a080d110406200105040f0209060102070b0d 74
    0x1c214008440c0c040c81e8101d0203036124058202200302210340c0c0c0d4000c2010580b560000c40e4402080007000070b60100719030001d8004c0d04107080040060603903490500280b5010b2085101042041d40343c00c0748626002c00280c2003035084600e00141c040d0100300310b4210b4071780340c11900c1c0e4450118a0010724581c080010101117041c503454414003c2c4840001480754000c1c071485050316403400140040b91595401955103600c00f903c4801d05210400c80c42e00503030150040700b000b0b40b5055071029100e05181d0b0030082c40b030303004042412030f010000b030461001903030b01085800d9203225400c0158503803c00b0741c0003a041032016441085240d08103c48400441d5000f8010101d03040101c071000300644504551941c0c850311071465001c0c41e44840440000308201802401e90508034100220b0500700260030087c8035006640141c000c2051201070b4550a08400390640d440419013008000e20300d01502c3d20300a00c403400380080c0c003602c444e10201e801a4420301110000e0300e201c21410b0303900c1001442840040c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 221735233 1250 221733983 221733989
    0x30812040b150105041e051f02070503010606020a0f03030e12040302040f0504020a06140408030d1b08060102150c070b010e090d0c0b0a0518010906090209010603020306211e030301 79
    0x7214140340020082da5a40021002040042e07403a18282130424262403030400300e42510541c070480c2c03a0000540340e950300d8680409203d00044080c01c6107203000000c0d28000042d000365200344d05005040c040e003507000404140307440d0040700ea42e04e649641e0030b00b80c00524010300b0841150141d5401c04905c2403e90b8010000c8901c2620100100c0304188001822540e055a00a50040416000300b250b58450a032840541c0c80000c5202d2505948128591075a0b0000c4450004035480b130400159082c6001c80700300c002c0c8082d0402d03003402e00d01030000275107c405031030207101c0c0d0303a8041e004580256120340981c0c1c04a98080c0302c1c0566940c596a0ba1034802d00b04903901c41c0188950099242d40d09e10901e20303810941e901604c00c10075602c0c4d84480074041d017002000d28465000804891002981c2402865001e9000d90700004084846005004001a0582142d800e0500400905c4101d0b2a144030a40c01c1400004c141d0040445181e41c041c10107440c00d10020b0085000d900075503001030048002c50403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 221736483 1250 221735233 221735243
    0x3070c120c02090a0b0a03060b03010e01061716080304060503070c0503310501140901020109050a0f02030610050121021e0d0f05040201020613060b12060f0709051c050703081204 78
    0x2140e502c4501400517160460303032298000c404c8600820001d032013900840c003030100c01000800e00880800b5410701310303050303503100740310fa0076001800c40d03c810b5050043c5002d500c3c0211420306030a003002034056032486144240e1040250010000b65464032584100220700d50040c00d89603641618404a51600940030520700001c03c44407000c20412001e003440720442e01d040c0c451421042ca10610341d455a0401d1034458150f540307035860748001a0044c03000003070b007511400d660b0a01011a005140c0761a10007000100b2181e6910820700c0241e811203c0420800c0c040c4038008541881400c00c00068000c01d0740e030b0f450302009100405202c00c40100500040006200c0802c80d0080071503c4030180c41090301d0280c0941c00c0349001c90789011400a04a0465010780404204a20280041905600f1a81030141203402540a02c0098400b0190041d0000b11a152a0f05807a0401c000548814001e1448070707042e10248801508100051200c00c00460300043c2583e02c2c0e001d010740c0c80280010450b401c0f55 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 221737733 1250 221736483 221736499
    0xe040b010906020a061d0601060f270308161205070215032a04080318030c010f080601031e050406090201021002040e010e04150504060218030703080a030203070c120c02 74
    0x406510030340344001210300e258001c0805000c10b868480003040000e01401c54040d605920141c6c078207041055a00802d400d03a40c501d6643c625540040c45403e02051240040d10b10f00300785c0c51406990341402c1d06603508484219640c6550030005000c028000d00020209141c0c00e0941c6195600302020308062402607072844802c0c01400c034203510301d10048903c01852060781e01041811100c2080c00710080e60f118017064902925407821a1440e00040340d2600605c004900e221400e00303060140900d400c03000e01304102c4c120b543c1c40005d46159402401c0b68105070b617501c0c106618101c43c1850012403040701c5401c219604250600702c001e0302c0445403d90140c4140c08245903240054401c44e800ca0f45008007861280c1d0a000c211051000060401d8030800205805800e80c00303080c5c45094002c0d4420040143d5445c001c081c6904082c05002d4587d00c40c2d000b100c020404103c0940459907000054980182d495a59003402e4400d4906043d010380b082c082c0341041000e040c0c100d010a81014003c40d105030b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 221738983 1250 221737733 221737751
    0x902210403020c03100203091c12110703030b0306060a1401200a03021501080d03090c03061802030705040e1f1b0f0201050609070c030e0301110d050f01080622051207030e04 76
    0x44e0301c010385005155500030001031700d02801c2c09c00e00d40300d021000d01c0c101024400001164054603803035041042004400100082010707014405d42001d02400d8016048a103004070001d030300d40200303114030204111485200180390384992601060b0381c54848084401860b61f01c0082d030354984440c0110302500c540d24018010b04103640c003282c100c83c4004024064018840380480160200e648200c0d407040c01d546011001486501030b8040380100340d4001c1c50390301442d004252804860b81e0007940664608990600321140204500301c05500710180102c500148190590041485031b012021141040701003040c03031a03203c1260b02c0480f20681c001e000c940c46030810001131200a960440118030b452014000003070041688100003840180000fa0307250403948039000c0c40d88940318081d40b4991301d0080000c0e68100c3da04541c094104d03c40100310301d03d00045120241480e0640074038241d40b46410700005c11004101c0408400b001116194a8003c00e14018140c8503401c080d86106d5400e100002c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 221740233 1250 221738983 221739013
    0x30b060619180f06020303061f090b03090f01020c061e370c050a11060f0c160203030721020a0b0a021b07030b2d010902210403020c03 59
    0xd191a14611494000360003040c160a641c003140310b221540c1c0c2400100b00c000b501c040305004240c003c01c4540c019654a00c4e014040080c0b48604151b403002020500118000c6680d00805031003d0350003503904c03195031392503000089260003188201c4a2036036000044082e4207480c04075140d4041ca030303c1c00440c09000703240030020390044400c0b140d040c0d05a030140c090601d084000010580702c3c544500c0c1c0034584024088144007529240c400c04404901c00007018013100381d01401e02d0109070480d801030100c0d810b180211003c9104054440200600d0114030403040c840c216002d080160350080842e65100303c00e00d010003200180c1c009200300030650041d0207a07064004554041495400f40d440c0646595066403040250070a1016103080000d02480b1f24202600300110006180641516120381c6400301f003040e400002d00d506881040d06240c0c00c4200001d4140015054030400080540c80744684800c40c203200305103412250b148030100040c40107154000c5030311704003c1001e500b56140500c1800003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 221741483 1250 221740233 221740237
    0x7170a0201050f07030c0f0b0603100e10021b030a0305060901050d052a090c0d0b0a0308041202300f01020f1e1324030908030403120b0415030b0606 65
    0x20190100d201000745014030100070300145801403003803c280305085100d880c1e004425110703010442c1c0c091b144006000c1c19103004c01a0544901e0307102c0c0d05000349081d80c40d03e507032a980c000129a8255801140c03503400c540e01f131071303410b544603c50404494445040b80c0e0020054a410b48141c0d009544020000c00c0c9410103428071018180c118000308180c1500c402c00012003a41601c841500c050705244400141d035079000c50a005e030455642c41c64072401001c144008890b10000c255100304800242000082c245409071411104016100c111152503030010030810100c41102210f4014a941b00898607603040386c020b80746007070b20403c44000c5903610400600701d200b11044100c1d8441f050021801110701c40791301c00c00381d0752440b0702d090900b4160103c4d2481e010858100440a00c102031038207420380d02d0703d5522100804a4941442042d03000e45841c8003500c00a80f001d400c0180846080c80f01e62055040480719141c090803c00030490745021003000a422400212044050080418190f28103c01 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 221742733 1250 221741483 221741503
    0xc010209010912030f1d04140402040e071a0307090923070509060f0c0106030512030a05090613142b08010519050105070f0804030c1d220503120106020717 68
    0x321076410b815095000e407401030641510301c1c0218020240c0018544490023813551492440c84489900c1c1428030420095404000c811001ca901c01002008801000100b40c1c0e048042d01a4050380c03034542c43c508813511141500072203040c9041c44058a800100100281c20151102c400d014813902d40507800c0750303c3e1007403901ca154001814010402a60f9130400200b00d4400380f00000601d0954982d80c00d4100450303508001008003010080105441081c0203a980c0b04046401906842c94001c0d60640c039603402c0080680990740070b80e80414442c3e01004a1008009449500c0c801481041045a240e608035860100020b081500006960810124000c42e5089144a070b000880c20100112910740000758281c5080c2244c0c03c161002c00e1805000b04081c2d4041d0f40101101d508007040c0305401814400d41c550310280840401078088508107511051034214113041d00e0101580c01d0051a40c0038007107a020b200c1d80044d00005100340c002802000300c881c542112811102010951525611014 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 221743983 1250 221742733 221742737
    0xf030c030506060f0d0603060903180f0302150a110604050d020c01080408120402030304030602180a1d04022817190804060503060a0b0a0e0f0427170c01020901091203 73
    0x4c018441c1ca004a580940641c602034000041c00660325140c00c002e03101c040700d041c2c000c505804c07802c030007018900b480c3d90041e1103a00ba602c42c1061850707020940c4000585464101843c0100744003107480e10030510802c541140b281212528280313030500545074542840c8240140c4070708033080c6041c0d4080c0d2403940c4541d0f00141c42d01d0601d4405000d01e0040a80100103d9040c003042001200080703040c400782c81d0b417104200400f124080b25905106003540980c2007080311000080c2800d80d0401514111540039030b050720041e103c200d60496207480c0441c024941c4a40b274942005c041208568402d00895040c00d007000c03111036a034550881c00b8030550111018040c0001000103110f514041d00c01560404006419860b00640d5644c13083c0158000303c11060005220850b014500e240660900c50540c0c000c030307003c10510042c41c1c0621803d40e0305a0f403182d07001f100d0725228424071402d034556166030000c42c84a035a80f24055035025000b58130088400340401c03080c10021601c10309001c15421020350503 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 221745233 1250 221743983 221743987
    0x20c0f0303030c0705150702160e190e070b2107090308040b0901020c10050d05010b090a050f21062505121f06030614090408030708040804050405070f030c03050606 72
    0x440d000d8501d540c0304500030f171003a108820b0369800c0b404c48020160710450065014041404060104a40d0340059a0200698088000c2403114460098885441d8606c400c640010388111002c074440c181003c2c0d5100f4240100c02013a801020700700406020440c0d83e8078442c04140b0782e502442903500301107c0c0401b41c0b881605000074042c1038510300051014900c1401201c00c404095000920840120644000000c00100d0020306801039809000d000d07002c41003020741030400c40d0003c1a140d4245100300b0344200c205011000c070310f80b200345003107442e040d40c10f1902420300c1c03000c603000c2c0e038a11081d24004404400c0c0740e840c150070700c407116200c40c00000556906141200d040c410b071100144c05003c88050740100000c2402d041595501d5000070202900c0c00f00b401880c2c0003002c80c400e0380a61445005140304410080043c00f81d404890b800b802d207040074402c44d100ca00340501c01d409243c00050704140b80c030061100c0c00741c028044041144140d40d080c044800200c3c412030a40c2d5040c0d400941010303007 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 221746483 1250 221745233 221745241
    0x924070b040f080d0222050112090c050a140102150402130b060d06030605100816030f1b082b020c0112091e03030c020312040b040f0b0412020c0f030303 67
    0x180c81075006800303062160076120307043d201c140c03031075210006680c4a15800201001d207050b41900145e115071958110401c3c4a01d001c001922a442158100005560312140c140400416040380c60140001401c40c1400c0b0f511103141c071414000b589125400361107400303021000032400e10b803a148229400307081480541c61166105028000088510f540b1400c01d2128851807030040c4254001580035400118160a04108030b4a00e1001500310450540000071452c4804101494010460358010000c100e48500c13070400301d005d811800183d20070118800303800100c01d18000b03004581d0b8a031000121210045541c4c460500b5241e00300791001580061250080e43e602070a405225040d00310004100b410441d0b1303c404035602d00040e403003560280d088881003410742c91312031074214840a0009625050341c4a131411244280180024a03480d030201c0014100000c1840c3d02c5189a4130010112240c146031801d0400d43d000038114200600c0303070107000c00b007514100c0321a000005000d4051031440e11 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 221747733 1250 221746483 221746493
    0x70f0c0506033c070c020f010203070515091207080d0606110a02101404090509071710020903030405041e050604200c010b030d0807020706080f0c090a0503060c092407 73
    0x1503d0302e4440c0711442405800060061100c410744211565a112a00301c8442c1c8104582c3c1000c0c8451581194000d11155000480000c0c1c222004601d00d282d5883c41d595101c0014a0004050024240c000d400305603502040941406804009202c0c001484034548600007100c030110144552441584400500c2e4003508200c400000da02d0708600d0404485540100e503d4034980c45a404803145a07525000c00040613800c2c801c85000d050b03004511030000f2083d011150707488a10501d00700c03e075540090402c07403c1ea01042150014680503000703010b8100c0429180740700010f644080c0000c28107060010710301c0c1c901841034480a814003050b07802d11252503c041240c50300156660500c0d596140c400b808955410002450040503981d03c04195142007040241068510b901060600a80d0f00500628150180c0c1142d4007480d00480e054841402c0c0c4d00041812180740d1141d50580281414010051202e80082241c12801e60b02c000c4500041503e284920003181409030943d201800710400040b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 221748983 1250 221747733 221747791
    0x60706051308180909010e03030f091606210c02120928030201200705060d15090501081905070303030504150c0818010b0d26070f0c050603 61
    0x40205820480441c607a07544103001070780300b591000520124803400c02001d24000700c1d07560740071001000900c201d8882081e286d549010281810b01c000c0c1400000400f40241042011000303402184026201e598036600900700d04c140c55808035940040d2118146966128040c1d00d01c4c540d142d60050542a810120b516056007202c021554001c900c1301500b0301e02001c26425618aa2410039020540c1c0d00c0e600c00034103425030706c100c0c00c2c00d206440203540c0c81c0310002291b02811103009444080d600c0d0040c400e40c0006000321a02e4081c0ea6a0055007c0303120030031940243c1c1138411600c200c40c040c00f0b19420603d414140a03400403d290300c6010284002407007a0841d0760050700c0ba00741c1460304000440c03483c2c1507a44044a410003c0c0300c2174200404c00700c510b40c6016510304460b000700300811002d000701e220502000800342c001441415070010420740000300344920f8500d48601c585461803441c2058500224400940e022405140041024035094044074003500c107541c8468410451114148210 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 221750233 1250 221748983 221748991
    0xc090a0b0a020708120904052a031506070b06010e0a0308030613181a0c040e131515050a0608060306070f02150a0504060606030b0d320d09060c0206070605 68
    0x180254140090b00040c00c00000745c0d102d01410f0110303240d000400a0204840c0300400300c4c0c058808801a04424100b01040301c01c0b4110304043e01c0355260b03035425110140b660006802d03500441c0c000740c248148606020b11078040c081c242d0350520f801c0110003c108040b0520700016013031a00030008583c56245c00c22959540544200c0302080180581c010030155001006c41a2880d080f0b038140e81d1080c07003c1d00f20580d8000080f540c50390a01d8100b1502c0307113090034018031514000700100c548800f0b0000c079000255407800c030071704180440c1c2c11000812042d14030503c20a4050400c100300861601e001e015810b1240401400400d681e60318414115075203d400c1805100307501804098140081c00307000003602c640c00421010402c2c3c1410f141100c00c58000da03001c401003500c0c15604000955901009261031500440c1c80d504102e8402c2030901c0038081c46400b120b107042443c2c111000d8001c00b0034585070080d940c2c1c4613001055030b41c0d03005558503100c8150080d0711a00c208100000036030943e10450704 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 221751483 1250 221750233 221750237
    0x1a0405100b0c0304060e010f0815120105010f0302030f0d08040813030611040602100b0102032b0603030e120a0b070804080c0604080d180b040209070c0503210c090a0b0a 74
    0x203416626000c00340541d1003841840702507040003800f4000f00d5008005201444170038a000300c1980540c10006000041c01703004d11183d124440000c0b00c3c16a5600c0c10501a094050000c002e6540e480442520a07042480f08034064007400020340f20850300451080b0040780135490300c8103180c0e1185e8a20079260320003418030700e9680c00031801101092080c400c80d0103208030175886d00e50f42c0d4103090b8082d01c0c01c0c1c01008006529410006040b1a0f6640802030b81c40540c1c1c0440343c40140303a03404030340010421401035941070907489c3c40400010305910400c00120120169042ca8103c144142c602d612040c900344003510820541020808441c0700c0c09001d42d03c0790044e90002d08109100140c14100b0b2001e80742500c048802083c14084562184280b919075040403030356901c070280740d0380c801e048403000500180c0b203900510002403009000d884403c000381e9018007525030310076500d0310084850311001a02884910180000340b81c0c2c14880c412184c90100080003010070911700058001c0310b0340f2092800c41 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 221752733 1250 221751483 221751511
    0x4080304020f0d1a041104091709060405120a1109070804030815100207030507080c13020a020708070902031b0f0904050406241419060c03020a1e151a0405 68
    0x2001c207210b2201105240540c40c2c40c04180d04103418600340000d941b10a45210b24903094100e00041c9030032201490004800d603505843c1c600c01c0d80050040c4c0519808290000d01061140042e48000308540995030721a001c01c800841d405400e00240207000c84418000c96008000701d03011900515485070300c031b21108a02003401508002107941c8032486404200540c0c003900040c4100701d001d104400191601038020008115040d00161b40106440b0361200c010380d0010703001d0300380307482031005d1009040c1070000c031200c156032202410700940c01242c1c6500c1d034612040b402026a500e00b0101ca44c0d071010303000d036181814410808c1000904001d041252020780c4e03440300c0c5820075280740d2242440c01000c1d40a080365803801c2070107201000c0c40048244036030411491511008041c400740d03010b8800501d000d102480252800707034030704450844090900014001082d10042848401d14040c1c0c3c401c51104000c02000e1490100f5102c00355112110f10500f40e507125411704042c0d0096030b03c8204041040 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 221753983 1250 221752733 221752759
    0x2010f08040204020f0703030b0922030804020d05010e0a03020705060301050f040b040e010e01021c09020307170c210d0804110f0402070b150109060801030213020a021606081e04080304020f 83
    0x811b544586d104a010070b442e000d42c40042c0c43c0c82840c4c031303600200c0b8291941d511081d10500358501140340c10001c084c00901008a8199241d40c486d0806c075030752010081101d88000014581da45200030011001807042c0303003003c5003a041c00d030181c0781220b00141c030340304a1200c05020003000d07003210800103030000c2d0b5900300007071018804d010f01d03410301d4452000141d84801550b049540140000c03a800c2855003010004030058800264220403a02021585102000c8080449080c10400304081750b019507000c04610031080800c06940d4034050807411200b84209101d019907803550101d4024201c50441d040d0102141001d220418040100400041c540b0049542d601c4421405940548800307200074a842a0380d42c00032078a002822090400514640c0f550380011070b2041c8082046000c0c0c0d801003544842e00d03001f000102c0382602c482203500300e00c0d0f03201d0100400501c400c69120410006c46e42501040500145581c0c1c01207402c4202c6600e1507550b5000d010318010348850140c1c000700b040c8508 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 221755233 1250 221753983 221754007
    0x3180d08120a02030a060812030109090507031209090501240f0203040504110301090b011d04022802150109021309050705041d01151d21100219030902010f0804020402 73
    0x480c80761440e818016124201801d484040746c1154000c52080d40c02500c01c0f800001d456016281101c1104d18041040c019034608241030850903440100203a084403104010b040d0051102829940ca03004208200e83e610303024420304200e040b040c82d42c449122000503155610407120780781d00380f405004903854180d44401280880d5200200302e1007603032001c0014054012540a414641c21091070b0105a582e482d07004500392a440080080c80b40354001001c030081c0c0b0503030061a070040e6060300006a101c0b680b042c080d4803a441911a2411894501c1c0003149a030124400c0c1e0781c0c1a100180e0011001c0e0801681000900d0b01070301c00d1041c000184400500c00c00c60420a6403024220b9a45d080ca07545005074500350524507005080521a40d2070065000d40e5140c00c015550000031104145002e107c0c0c03800c00312014030f594891020f030155481c03090300000160000c0180310040c07200d0541070025250100c00f1600da0301c400a00145c0142000a42c4c12300c1240340795017003400200014030b465005d03801 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 221756483 1250 221755233 221755267
    0xb010c1b1701230f0121080f0309160807350d020f010203070507060906060b0a0e010e0906060a05030a1b0c05060601080105030319180e0105100203180d08 68
    0x1401c0034581d11100c0f8074404444111561005145899020010b8200075056400c4d118050241c00701ea02d16185a10b075071801560789402106400c40390f055544c12071000d04c08441d034000c0756030503000d02c11143c0c1d4400305030344801321804960844018100290074541c03080d80120303c01054011b29070b011804a0440c0c10160480f0398002040c0c002031000001060780030303042c00c10384040682540d00c18010084065082000c41e4200e0350300c1040003031100392615004004082940080540e01d201003089001f10740c00040020841c2c0003600c0e452407141c1034504002e05150216002900714000340008440700f406503001e9074000c10241404101c070740201d00e545408000710105240003800301c80500b82401003d100448d081b40e02032a20401641c1404042a135078490f007001500c4800c080148400441d10440e01341c0c02001d40d0344000007045136100b01010309040d0a005292095001241031a0610b00000c101e80e1400824070340410400c01c00d03001c1001d16019103805032464841000a071900c914175180e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 221757733 1250 221756483 221756519
    0x7020d02030706020a1b2102030f060a051f08030910090e040503030406050123150f0c0109030e0907020c0907270e090f03030c070f0f050102070b06040b010c1b 70
    0x402803103008007500346030322041e0012048840e04095100c00f405561203201c91306040d0480100705520355887c500c00319141c8801c000d8580b4050083d4000d1000140c460340005001d15141d1003040c516030b160114119041607540b04000c0d183d801000070f121a81040e0312559003076240c50801c0440d0b0755591900311440c420495048906400000c01c0004000240c0304903805030034048107160b15640b0321802c40207030200c0301001070310507080800e41c807c14000c2002203540410182d84401d403119800d148142c040d14a400c0d04034040b40300010070740f2150424144481c8244080c0d0300500051040405028407510060715917001c01c181c104100e50098164000c0c1c030f00c10b038041849588103502e4410404000917016100700b1b1144c000710005076000c0800419070f03400c440b4001685030f940185250140d0748001a81005040c0601c441030b19044c420198082c09585000d603140010503603030a003c001c1250100910107000c980180b400401141d10090204016007108481c081c0b550344074206100c0340311041c6 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 221758983 1250 221757733 221757737
    0xb04121a0f09071202010e0120030a0509030727020310030611070311120a1d04150614041508130209090a03090b120601050c2b170403080c07020d02030706 68
    0x8003030190400040049000404e4040f00c3c02da20140a540000d191040e0400c1544c100009080c0c40c01c0805800d03c191038141c07a4030300841c0c0d03490700314100140280c2c1288401c02d00c01c0c090800300154500c42003c0c04030303040b805051014481c3c284240c411001f07400291407080800c085140100000c1c0d03003441200080190300000d2501d6500c0b900d0014a51969514064900c4c0c11800e1400e001c503c24805445420000742003e00c01102a00c03422030141d041800c82076070007424800701da03030402c520306411410b0700e0b20740c3c0d681e0000d400c0703c222580807442284103510403054003410702e4103502d11070007005410980c0101e081c0013640064000841ca400c00f500e03980c49640217904500201a00801001e00401801d03d40302e090201c400191400401e00520160501c01c0c005101c461100c0c0a02c803c0ca581d0305008ac985d2079651003600501010a0b150b0889004560750002d0007204107640c44045105542c507641d021400c2e82c0310540c00509400400e02240c025400d0250b030b03030069800340800409807002d9 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 221760233 1250 221758983 221759011
    0x1903050c06010f0905070e0105190c0b070504031b14040b181609060809060a0e07030b010305030d0507022b090803070614071106040f0f08030f04020102010b01090b04121a 75
    0x713100002c40d04c010f408842804800c915400c3c5a90300b280c10b558040203a001951040c0c80100c0c401c3d6944803025000030f2071406602c04004425821101803c1900c2c02000001c07210004200c1070740c0300e000280146608408900006002407410303410500035401c0c09003074002c0e800781450218090250a6607961482e45c408402401404d5100203030000400c002d01d04800c071410716101c001d4840c5400b40c140792100b2b403916030a0600c2101001408000c40d0710400381c95807507941c0d041040e107a80110012150381420040410000d41c40001d0680a42c04111805004075200c9608120f80d20704003c01032090100030940042c007080305001501085000344004a41030540c240440e4003290300a03c08003c1c8000d028510755040c5002900ca98025071000c5640000041800c09000720f200c002d0000f010f013a400030400c0805410345500a01035403003078009204284045005440c0f5012901a43e5486d4105000800c050a4103480140c143d03070107003d8001c80c460358005034941c0751908907852040750b550 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 221761483 1250 221760233 221760239
    0x90507030e01151503090803010302040c0c170705010c090b1206010e1e04050711030f03071403040f0302070512190f05030408070f0b1c021308061003050615031903050c06010f 77
    0x21200c0103008084c1d403900700650380f180e40e1500d004c0d001c18000640a113595031460080a801580b042c01c5803900441c6551000e0b1840480bc625940b003110f040b80d645d400d003840d0046482c018840c400a90f130380d0b11181405c0c605a02c12980b00c4c0314008169038104a6281b411200f0798564103031000d0007a00c4004c501d2020203516043c07000b0340d103000c0c1014007001070003140789845042c0402520507120456030107690720707210000120340907043c80601c10f1181c0000014442044400c61903504840c1c841d4082e51512640d030800c1025007140d07030300144141d8100d000224440b0031540c40c10000d8910540c0c1c03c911851558a42c5d13403954100d5000040c8941c012401401244c80030010a002040800c41c05403903c1c503030b8144d401355800511489018950040741e48120303482c8400e03040001c2d0500b0000c032402464181d21100e81e4469034801030b16030303000c0d240c0030480810500002814480010703006003658408485101c0100e02d410805404014040c00301303020380081402524003c2040c04a511a9142 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 221762589 1106 221761483 221761499
    0x2070513060e010e010617040b011401120f02040513110d02090d2001030b0307030b040b09100f05160507020d14030d05041209120c090507030e0115 65
    0x2440b4400492084407040c030382c42c121401503446070640c0c203c900742e030308406406981c003070401d2001000520100c1400d038054010301206241c40e944c41050600d002c4111044101f8011b543c51700018100036910f08448000d6134000300c444204501511700805141502c07403110b014088075004034462085943d0b565040d005141c02c82d011036882900e01195045140c0100004d6021030300d009103e024a0a0000302e030415a41c0c400740803401901c0b02d48481c40c24520007008040144280301e014120b000c054040c000c100174010b6000b00315424014002102d250990505108202c024406040513a48416040c904250400a0040c8122581c07580b07a0641c4a1116006e100b01d042206020800c03081c448407156030182907079080700c22a160302203035418060340e190241c40d00e40e0310301c41482000c0d100c0d80003681240c21400d000600e01d007010b03005402e44404130908620042c0d59002003008070 = true := by decide +kernel

theorem cover : BRFrame.Cov 221582733 221762589 := by
  have h0 := BRFrame.cov_init 221582733
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221582733 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 221582733 ≤ n) (h2 : n < 221762589) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
