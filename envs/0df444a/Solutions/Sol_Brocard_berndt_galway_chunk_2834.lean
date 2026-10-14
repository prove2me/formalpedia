-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2834
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:52:49.078317+00:00
-- url     : https://prove2.me/submissions/6159f23c-26d4-42f6-9d09-e1a21a946ea7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 509532374 ≤ n < 509712230 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 509533624 1250 509532374 509532389
    0x3130603020c0c030c030d030f1b0210051e04020f010c0b100302041a0a0e0a020d021b011a030c06070201022404031101020a0806061b070801050105130207050c09061c030507031101021201 82
    0x440040320450a2740e4810280c1000207440d1480c1400c03240c50003501c801101d801504c1c807521300004565400c813041346c1d1480000d07030843c03011b04a4445800b0031000e2112075444a04100a0803202d1380001c024612580c00f0301e41d8480d6410700903003548108001d0341d0005052911818180c1c000e4244e03071b511842400c084410324032344081c1035210000c2c4030000e4418614030505940c00001c20a104115240e081c41c3d404403c0e0000700403942c0310003517440b2030840c00c9004640c1984881d109440500d0210700134000c0610500445011701580d40100f031b00d04100d41c11064110b100070381007006268021400b00000c00000300210329140081c08007604400e009401a4014640420400c810315142c4030103c80701046c2500f110392403641c4142c09800b8001c00d010741e43c040c00c59000f0350740155040340240da01943d4824090104c0320400000d021045070000c00007944119039554014006030304480c5261214065540d159a81c9141d00300a80100e500d00c4070300241d68030401c1050b503c11141c0b001c0c0303410744500 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 509534874 1250 509533624 509533631
    0x20309061911070e0412050306030d050c070915030c0608041a1803120a0c0203040302030a111f021b0d21260402150705100504020303130603020c0c030c030d03 70
    0x45030303085440c81007144202d90b062054180c00b062204031010b40921441c8907001d11b80c0e110890800407612400180e810300d40581c44405018056070080025182c07030012402142c1406940e40409400e8940b0100c04640c5111903020074014010703001c42d500f0261805080c90308090526036181c800c0c84016540e10308002100d100403901410540c44440480c074030f1501140e448203030f025110f0102140996504040900d03068030000707540d00100035101202c0e0000d0141c1100c0300540c841540004000e1246a48150032500b4085100c40c060050200c0001c42e900405100e0a9101c3c42030307684019500040c0309901d1403000c0c41c002420413a0708802e48071401c540b8031445900040030340741514403c517091101c0c10b840742c0c084002c81080094511840c0211554000e111392840a034000344104c01c1d02030041d420180104040c0d0032241c100d241c01c01d03c094100c901d050220820890340f1203a54100e140000d400046101110300200a001030404e002ca01508490400400003503540e10320025070000d2544 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 509536124 1250 509534874 509534917
    0x507080103080313020904050d0e010e0604090e01020405061c0c03060e0606091f0e011701082e050c2101060906030b01030e060108071e060c0311010f0f020d060602030906 75
    0x8120b0062080d10b90190994061f401c062410319102c0c0d450000c05800185003c0c5030568a621803a000004004068041c0d8542030414a15002070b10b6910302090b400c0d9000c1000041c140c9400006100c0703940e40c88480030b5041c0d8280710030303001d50f002e112144e410076080c04820303c11010046070541d000001203940981d2101c0c0800071902c96003030f80c0310b002c1c06100c5580c424040e658001d0340721460b400c42641d42800c4c0c59004140e501400f1000c1c05600140c0e80304000c0b840d030b40c02030383c072425050b016907454039020040d01201141c00d98004480d2241d2005001c07803c1c148800400d5103207c010505116110140e42c109040100710f48845c0c03064504054603040b49400a034001c8e48442c500580c0e96040d07074060341c0c42d446210703502c000520aa21881400c0d511115000c200c0c60462400c1e50826583c440c110078150f01c040302c001200c00c0446805550701c840820700254603100d080c01c071001c40c1c0800350b00da840c410f401404450145d48004199002045501c10b26550740301114508165449042101314 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 509537374 1250 509536124 509536141
    0x506070f140f1c090606090f020c0a060908270f1e010806040e070b0304030e270606190f020d021626030406020c033a0509040f020d06050405070801030803 68
    0x405502e580e03c3d03441c5000c5001d400d004107600820281c9a5245040c0907011407180440201d10800c11050300c6a0001c0d6003440001d1101d80080500342d010f2410300e824902c080101c44140501c0300c80712411b00302000034500480c20002c034440410482224203281c80b841d403c201101c510103105901d810041c00200103062940e43d6404210303080710301011034102c9074640061410b40d910030303038069007c6a040c0313540c60013a00d4170b01050040e801c07800d42d07030341e07102d24150041c1428210080d19060340710009004142c008045180d2400310314107565180000b007a2800b6002e03003000c22801c806811500040300a41c0381142205c001c10881e03540c4026045003200c041d07a060b048440c0d840f80a4030740d0100107000540a039001034a940649804c50944003028542c0c06a101100703084c40c001c0c0401d0f09008600c0002601040500d00c1c0340c4840c5c10614038020644002400321010300c070202009550108049000c5c02007841752201030071041d1030030010750811101c05441804148001042ca4600100007101394 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 509538624 1250 509537374 509537407
    0x501270b0711091503030d05040303110a021c0305011d0c0c0d080f06100813060f06120b0901020903070b1602041d0105060904030516021c0506070f140f 67
    0x24800e440322980c85070340c60300e0102c00c4407480d158414810051a00410140b4400182100b2034240c010005e5242c400840030041c05003000900580038035694400c0350850300320000050886207202da001d810804142240402d041c000c6e029880101460b2a00600c8048036140e034441b010781d6a140d0001403a0740303c400d43c018a100d4064070649500031600500f4000342c000b08000c0c0182d8401c10040002d80c0c94400b84803c4407030707ca83c0ca5002900c0b010209694010745003681d010540280808107400b20782402c900d0a803000d40d400240e41c00007009500b4244049444001d0700080c0030ba000703500c0c1c0000a40001e03914040f40c0104c0340703a040c00048402030442c004020184a5502400600c04260200d181c800c3c02d02c0b400c1e800d030741d4035401d05c000282c040c6428404a44600e902d911518201030071421004d80b41e070060001260000010b81d0f210118460440000903414401c0000304428648444014905800c0f54014001e101411040407244180d850685640215811741c054854050031242c60317a1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 509539874 1250 509538624 509538629
    0x7030e030712020f06070c0819051e0a0f0302071a0c0d0e030315030c0109062304030b060120030d0f02041701061a04050906040509120309010f15050127 67
    0x40107102c0700c07000016008030b0b0020340d4800000c182c40203607803400e50694000d160000024075290080245003000b11904841004112041c0360803820045124169040340c0c9143d1480d8245120120700364005580c4403507210120705461500358208046980c2d4400d00714520041294441200000184200c44450aa030182006110b003480050307821703154103440368820b4551013008504108104018100003800d00090705041c0d690201c601d00d0300030708403941c9070311500d28559411200089445076001d240944043c60060b5000b65050810400140601e450305812076202d058866000703840e2040481511900040c1d110089002c460151141d4002c1c801c980000754240d0042070348451403001580144241d50400c90304003683c00401e0303c001c449000b03038072880c0d50128181e0001074003030509810054001d850300b0704031100c2c50002650b805541e001200c01c07104e0f9039514503049405e800345000f010100700504480b03451540c01c00000070a003e01040c501c21140706848a800e68000c241d0201000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 509541124 1250 509539874 509539883
    0x9090f041103061018060b03070305070504050301320106050717071e0c06020105090a030507062013050a0302010c0210020c060c03071a010602150403140f0703110109020907030e0307 80
    0x200b034600f61025001c1c4c588940502c9000800302c3d62039500c2014248075800c10b0700c6a4510040c15655418002c40183c1801801c16003002010322002843d61424056004002990150a5070101c00080d2004103460500040c000b08003285004002d0b803038004013200c3c1241d03000146901d0310855a0181c41d036030b01c5000c00042c151380d11014400d2000c581903121152a62040007100e454641c2d0303c0d0b049080e070f03006a59a40aa401a00510000078082c2c002440350910524011071000c080304201c02000907164804550100c0005100c040750120302c091501400080740d201541c0ca0958000034070800d0045402070144e0301180450410718007c1240080d114801041d8580d01c940400407142c917500403890484d800301544a013640d43c401704e00081d90680303d2035801032882c007803250038505002d40054025010310400301c4401d8bc510030f21f00000d01d032020103003c5103507030780030316107401000300a00d00110310041c1d250a60b42c4005130340703004006402ca4140e180114040440c17281250461094100090 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 509542374 1250 509541124 509541133
    0x7050f04021305010f0311210f040c0b070f120f17100306020f090924040509030f1e0304030c29060f06040503160311060a05030106031505030102120405100209090f041103 75
    0x4923a650098042c4080444045a20701c2c01d48460b450541809800d89004000703041044090000c013043c01d0141c1615070059103000c11400850302ca50408480140321240001c0d4104614028907800c807465004c0303290300501524080c030301407001c1613040d151800000c0965400041030415240c01c40300396010080000c0c648100c1d8105010917148c001c603000280345848003c015100b0fa5484c2c02e101d2a03200311200d001461a0060540140566601c884c2551400e1b982c20329160500c00c902e0b03400f441c401c44c031030b48071000c078846a820000381c00040c440c0f20820310090764503507940042c6500350341600302409a40d000d0640e10700c0d1000428034081c58000381c0c1c1510690f9a02802c0c092810881e40440740a04042e112070ba0710318041c426a4451a80c23510081a41040100041c520a9100003015941038841d241c2c400d07140e10009099a220310118a40c182c080360a0005000e01440a0720100b140709030214500b45400001c980c0d1460002d12010790003001000180c00c0c094500d41640c1345200060658 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 509543624 1250 509542374 509542387
    0xa030e04020d0f0e0c0a05032a042003060301150623160b01030b06010804020121110a1e050a0210050a06170303150301140115110f07050f04021305010f0311 69
    0x116a40c1c1d03005910f241c426a8041b80001d2907040124030344e4443d8111002d121018900c08644034800040c1e440c41035007080c0c0c2d07140410b100d0b081008000110640c00c0c03960303030b0752814988109400d4070788065045058a080003000c105840c1c10030040241c920f107111864010007202c170140001401498803207042460500004002c00c098130704001d069910039019007816803038132401160011030440317009010502c1140700c07080c0b0070310768800079014020b03e4001191000010a6003403064220b4981d02022505410b4549200750400404001c1c855240c94102c1c01c1481200c4001e40e10031915242d0310b012075a9a0204a000500780c0100024222070022940d90307211801c1e035556203510448081c0e1903140b0a94a540c60703443c0601502600300d4403c40c8a5441d079003018100700068206aa00c002400101c5140b84540c48043c400d12021109003805403100c18540018442c55100c1c03100d040344544e104214100061798425940c0042e81c10a02c2d22207994507001ca42a0006d00e101e2a0100c020b81d00483c10 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 509544874 1250 509543624 509543651
    0x110315061002011e1e020708030f040f1e12110601180605090108030405090c0a1d01030b030a0303320c0a05040f03080a030b061801030b13020d06050901080a030e04020d0f 75
    0x1062440c2c4c1c5408290809001c942d25440c00c900a10400238000340c02000411002701700c5050303041c1c0242c000d200c5180e0b0002640e607851a048041c0c00e00001c0244109514010b1004608402100c002141400040d603242c50b400c1603100d41d414040c61a0300d01e40c004e402d0013810004e511007006090003511400055031036152083e41c0350480d00c0340520070480f11001654000071030040d0342038584035840b01c46900c201c00440140b0320791496205410156252018120744d5000c01070106414001e8030001003d41d0940188a80c0380b084500481d2150345902e442d280c04050440301e00c0d032241400f9240e030346805118000f00e480d48956441040006000030001c0240a1320f040200440c040d1038508101d21050031060103c1801070002c500d188440590910081d9402504965188034000300700000c010740b05180802281c0215a580c40103a07603c0e9810f12185c24003404080c00b4003543c1c4010003000c1110398000b00105031000409005940110b00740601000c00e400c889001c0200e1442840100c80d003101 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 509546124 1250 509544874 509544881
    0xa03090215090a0b0a020a060209010c050102070c08011d250e0406050901050f0105010c02040b1908030304021302070c060c0c030803010b0306010207060509060703050708090306040b0103110315061002011e 90
    0x40b468811190b0510002d108a954001c4a00e010a99001b4022035482512807400035008404601d042c411024540400214280300411401d07108015403841c0500302245542110a121401241400c440c03114480c174203000503118800d61b2a06080b51241da07595400241b420610358400c2aa404d600c070144020040c403500400c0c480da040034000c0041e0350f0788280c1e420701000c1c2885858042900450b4203009410300c0c1e04a8040c1c00790161803414201d08069401c1580e8025034030181c001d07000407044c08114604a41500c100500c14401541003e46a80b900c000b00702c4103100c0d81d024000c3e00038845041001c00c821120085030081d403903e80381d6070341e18aa0905a40101e0780f80340180140354000c00c10074083d10503180d47c0d9901a1429080280340d90301540c03194092002035a1106060044840e1076800300030052080f840380303485195652542c038106940030030900109110b6000060aa504c0d00321740443c030b9500c640f003111304841e40c8203e8a820380c010108455442e2188120440041c02450142c2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 509547374 1250 509546124 509546137
    0x3210613022106091306021b0f070501110c060f0a0e04020d05040308070206040804061b02100302040602240708041a0a0c0e0114030c0c030c0105070815190504020a03090215 76
    0x2142c05815038500e010014500780464940800c03d00148003076001c0340c0f60754060019051210642808441c44001c410f18040800c0c00105140e4010101400340396409109400368688003c010100b0007802000500e03540513840d05d2000101c004261011220311039a00c2c906068000740c01150780b4148090400050b00c0c00b1074041c1c022a8101000c100418400109a40b149800020741405c1a043c04000ca0b4a000030304400301c44c003413018070403d000d82d80c0e000b12050f01450a840040c4c0c0c642c60410b02a0420395070044858418a503c5a6400c00702c0c2c503202c1191303201d505031900326121b030344615180c42c4101c0e6400710b50302c4101a070703010081000002d5002c020046100d480d40510407449000441d00500e8070040540d280c3c0081c03001c00d14001e4002c000c0c0540348035050981c3c0c14054400801400c54030200c9201c00041d0707606060211030764601310111440e003002d0762020382c44100130383c01e403552031070900c40d0034003a550010303402400d42c2c1b0940c402c2c48078650081080325039258040310343c1890341006 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 509548624 1250 509547374 509547427
    0x207090f060f05060735130603050c07050c01080c070b131e02031005090f0f010f05221104061e09050702060403021b030a080f0a090501020321061302 66
    0x125404909880d2000503a04210361207a4181391420005d82d611100c0098400000c9503030b110b29518107050b6038410041c008415550b040c8400340351238040e0050640d8800391126140309402c101c07a17000300781d01180c201503100c002e0070000d2043d09e9034056520706104190014115121203418490a50300484008e14414090b02000c4580c103d401003010164041d0040258140d1007440c03004844942900101c4e0700980e544203032046022994002428040300700c0c0c850380507035500c00c041034161103503225650300080c0d550240c4481e810044003400c21044000005007501184524101c0c1b2580e45130440740c0601301d01c400200d5040c6154249408030202805000185402c00d0000341c1d00e90f01c000744140c4141d030103034014201038120036090000c04181d00e15075501800f076100f4820120310050014040400301c00c070460340c0e5590f241c0c80107000c487e25030001c9045400410000c2c0e09104c2d42c5206401d54aa0004c1c10b9005803070f5000058143d200008000c480340b400132543d40c00c05160418010b6030b80011 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 509549874 1250 509548624 509548649
    0x32a0b18030115090b1503090a0515010b030a0237080c0c07030206070f020607230604150b1804060504150b03030307140702041a030d02061b09010207090f06 69
    0x80c04209030a031881c807030b0408681800090108444000c80e0411203240710044d00f181a44404405000c0644d030084034040e4496100c0803400c41001400c210044100040c10b03170044655041010410140c8405018883c0303882d001710b111120340c81039008484018410850031030ba503c1c0c42954482d07503a407584000601089418000520340200b40c0100d480c1804098080d110041c20f607402c01c10b154003c0076081e00c000c1c03c4030020b000140c9a0364010005507000390622905e9490070041e01c501c29805200c000310641004040c0b00004850000c1c00c0c085200d414000329100040364089600da8861244c00309004426505020901c0b400c1d0748107a0049000c0d40011844e61051a801c10954070710808094159104000080c0150b20500c1019600072510000d00e00d4144c5640006e010380c0c110401800700e5030441300c1250700b45c0c641040035244008090000d4251441c000700c1128080c4c15001d81c05400348030014001e4141d078401d1080d8070180644801c02c011030b4040c1140c1c00c0080402d4019102204003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 509551124 1250 509549874 509549917
    0x60507050d0509220522170a140c0a0b01061e0f020a0b04121103130509040f0f150c0906020a1b0e13021908061906050a08030c16050a032a0b 62
    0xa08825106440d03803c01008280309107013554042c07207079104658860400c00396011841c030802c4420700504075060710b41e0041c038884214cc208040000c0e0103034400401d004545820340b4080d0b40070340c00d17a034007000242000011550300c03900517800c2480c1190001c1541507000104010080200ea41440b03c1510b6a44c22036955100900555244940c030725007034036401074002c02c000c41c1c5481440e80c0e034040d1003012512200b041c1c5070344030740185103076100840e41d0002c010701d802c085845910408071704d09078a02c0d00d0120540b40c07900c060b441c0c000511001d05080e1070094010119070501d00020002e08044403175144070b10300b03201ca45c800d05840c10360072031007055049100040c010228802005036a85000030741043c2d124031036000250035802541d1000e00340c8400c00001e55a8900018100420214001d140d032000817020560030300c00c1080b07180160458551081c07250b915101c0e41403041d40d50181c0d400030002c40c101030f609032100365220391004c3c3c1c40c1c000c4c0303002c1100c8260501610f9200f0005c440510350700d0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 509552374 1250 509551124 509551171
    0xa181e1d06060634020a080c0411040522020f04060f080108070e130c0e1603050f010806040807080717070605090f331f060507050d05092205 62
    0x704161030801240c25a64039601032075218a04c00107091071400028103241410b9000c240d5440c0180e010b54117a0308103c500b46da0909080c054901da42000164a51415003014006080d4960b5040760f0190035545010b003080380f03010390741220903460903210105d0b100ca607141801002e1111b0030940b80d0001d5141c60000400b00c1c0001444019507846102e100e04a80d901c01801e1107a5131203c500340ca002e44a01e00001d824140e003180b0900545441611200140c000400030b029120064401914210f5031801007107980c10100c1e002d600079070b003c02d8480d601c0c01207041c94041c0e03020b0748030081c09151003980e141c003141d00e03410011319440b8418881800166105c040da10340700c11075990003400c16046404204410050000d400c2d5161149520f0465101110495401c5035202151a4a13200002083c04c103051a007407010680140814608a4909050703030b59055103640c10070745d00d0300901c200032542c0380d001d40c0d42d600300010540107400c0c104c0e00c1403001d41030807002c1c2c04c0507158491021382c0e80c02c0d203c5808 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 509553624 1250 509552374 509552377
    0x8060108070902090307030222060305010b010912020f010e190e0402100302030402180702010618051f060f08040f060c030b01030b0409021c1b060f09050a181e1d060606 74
    0x110003400386c004545550207002c100c0854400030020a0400c1c407a4003d00003070742c451a400f650180000040708643e100c009811690203400040e92086450007240059440b0b88010364034040070b182944131070b85c02c5030110b2401100460189466541014082520040381c0f4180e0710890084595080c1252041d10580c120720080d07070007a4000110150030103215a0385d101c03494003d28248000603d1641d90003c2c152110301c2c816500300400e403914140f0012141301c1d01d40300214200008001d261615144000c1c0034050800005414803100000103410700c46403401c4507108540000301031006500c85070b0001d0003840c220b00050b010900e0f150a00d007040c10148583d00da4580d01505212002d2500d0181d140b40d00b107107050845a90000300a441c60035580300741120024110740d180d11a0401d403110001c0c1c042d842c2a04568024414200c040141411000034845c0ea1450385a0000f603000440720124102c5d000b0380c0c05c014056050032500a00071603001044441042e1103c16143c00c1e45580c42000f109 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 509554874 1250 509553624 509553637
    0x8010e0408120c0c07060804021002012715110304030305100f1a0d1508150714130302030d120608071a0a0c0210030c021506130e070e0108060108070902 67
    0x15100c240800800c40c01040c032840d4000d184080f42900f4410f05200003407030000d20741c00060010300075909100c00c41c144000e02c80041c0c06140024486824809010940404000b0300b80420b0b140c006244800e0018843c61002181c080d41d5040c424003040039001d07546680250b0f8210000b9260400090701c0e8003c1350016400d44200150b641103c600d089401160b80c101f600784644031590401c469251060315116074070ba010510804c0e00c4080c1d14012203d428103a0464444503481c3c50f0030700b000b01c40c0b07030700110300d40c072100380c9803900e40c5c8031200e000400c6119075954000035098881d2444102106802101c056002c0907195403d10040352159206922081c0070f219200c40a1800003001c0b80b20507120024004081091134101014420780c2c00103480510070355442404650703142c44184050b03070b0503c99021107074034010361011641000c40120b42c08140c02050b0302d0380e50740d440381111045c80040c80701c5002043e0090b80b480455031240f03003494542c0804c1c40707504540c4c0b180ca0f9002031403168500a9031407 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 509556124 1250 509554874 509554883
    0x2010b1302130e010311030f010b031903021509102304020111120a08040303050a051302011103090607081b06010b12100302370b042d0806040308010e04 67
    0x10311200085810010350050144001410345109001c10340003022a41c00d0f0080d400f5034091440c0410704010705041004071584400799034100844898503480000301c9282c030032001e800e080c110b228242000c030300700040c6440e1450094035a5040c0714105400041204082248580420210b25040d8586030b041d00040d0708401d0710b49182002034090760003803006895a0800e0000d652001260807806c00c50781c0c0c0a42c1e50301d80455214400d10080c15414883d00703604c2141c0c80c104108c1030411920103c41030540f8a0000e04003c448103d50305251401e0054483c3c581c005800c2c561a00c0f8503140010607500b040342d280d00c0407004155800c455420000303005040f40c2100e51107900e04201846203991004000f88000d0140c0d8054000200607100c0e00c41e0a03014294034204000c000d2460074032880400c100b10304021842c50203882c1800050b000b48111000c0f40c1e4044492101c5260b2140d895101082003030711003110b1007442c440052600000320700c880c4240e02c070350340d0217203a6a210400f400c0d0480f400e880151 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 509557374 1250 509556124 509556139
    0x120070c0902030c040308030a2a120f02160c0e0a11030106050a0302120114030106050a14010309060b030304080f06010602190b10090f0f060b18090c070203032802010b 74
    0x2100c1c107080c1e0700541e00403943e1803e891030981c880d140c4001a510541c0d4607100c07070b643d4614141d02c03a00407100003064020004000d42c2c041100080c02021194175100b602607181c3c1e251280307806049aa07040300d0900b0010425412040c0340c07820306030f219480e144540110304c0c28420004d0302c0d000a0b4072580c501601480d512500310307420b0900c2183c158204184c10000c1c903030300308400d00d0303480b2065010f0f034000c040c80e69800790b00c40c120000b49425030744d0315400035009081d0709400784000c44c5003281c49062120f00386030010f240101401d004001e002801c1159815010002d07010034a00030226250400c250300b80c0459082e40d03616601260340b0603151201503c80c0c8c0b00340301c0401c0011480040603030403140b00c1120340c4400b0346a443c194221004100c00512466841208550f030f54094003820000380042203c81d411b00d1403440081040c980050b400e80e1050b908400024410b0b0032510941e11002d402400302c0342c4810280b80303503080e0a5210b1030000804c941c90300e40c0d6455107105000341011b8840c040c1244 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 509558624 1250 509557374 509557379
    0x30705091303020a1b1409150409020406211e080426010e010609060618031719030609060e240f040908030a1d07060f0509120120070c 59
    0x1d41e480440c050210b04602510b101c050100f504108010030440b49200010300301032825818501c114540c01da250b010702113500c00c01040c545c4000803000c10080644022500044501c0014010013036900999030341d10f41c411100460301078829014201d5803040740c648840c0b035092000403010100f144002009480d040100780304030248106043d1800e43c2483c600c640b10385203109407d0a40769917007007540c501c1c0e641c1d030780400201209014a40c000c00407402c0009c8a90401880c80da585150f33030002514100d407442ca030244880c0d000b022207c103109480500d03415001c0b081c9006020340391500c82c0f503452500b0b0071408039508012510140c0120b110221804020380b40c0c0d400038403030b036108400b440d80c0100c49051610403501c6500410350410320a42143d076480c5410b400d020111000850a6148a544c50f81d45803c82c0710300007540c809846084c00c014260411b0094110350910424040d56002a0811055000b2100541201509400040f03802440300804ca000700c1590180b20005082c0c1a42607104 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 509559874 1250 509558624 509558641
    0x503030c030f0702040f0c020606030d0e061909050d140c151215131e060b0703050d061d07030c0503070516020d02101709071404021803010c0509030c03070509 70
    0x4003c3c66102420225800054905030b0f070444181d04102000b50b0826000c00c00c0c0341c0f81c184160501000203080c0003142c404100d01050690007001007117039000e1075074407910118900501a41000703240c001c24a54078180e684c40c2c044400541058034046034442c04c9204030300303840c0c0380c0030300d0380d03070f440008081030a001c90040265014540685000b0000700380880400f480e85404030341120070f0115100100d11028140440c0c01d0040810041004503450200709100c0c2540798400c8903092034042c0740417a22030840a8010380144000c2d409182100c1d4080d035541000807a030002ca500c1281161000c01003c8010351081c1c94900c07040b1031420008004001c00c22643c401000241071050024155600e03010550b4042040014419500d10104551210b5400c0003d9105100c3d58001e1480300940000c0e460305222081c0441e8404000c1e22542e004691003c050b0440b0005804040c1c009000303112180d08a038002d0040e40c08005194004c0c0034a010081d05410006a042c2c200c400103818035426603683d646 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 509561124 1250 509559874 509559877
    0xf0804020d0212030c0613030207060c0602040905010303030b0f18010b0a27150e030601170a060603110f0906060304230a0302010606080108011b0534020a0503030c030f 74
    0x22644212000201e0000da03c1d1260b60400c516900c0004542c2c038003240c2c0d107151070260020030320001140b6030303600000000d5002c41c000d4100c8041c2d0400c181100d11900e01600a400b580d0000c454552a0000000905500d41c0004000b07543c1520384500da15000300030b0200d0800744280c42044106200010003c503503100340108205c03019403030164451600070009140d05080c4041000d240107048100344180c5580070440007541d9158100368514400d19804652540814031808001c85000d00f0048482c40341407101c01442a4803d208001c03144d164a0688000c800004c68140a0801c0413413601d19424030318800c60090900800d041d04603a00c0c0e07aa41004800da0a94580300c0d0046203000151384207040003041202c611a80000c9036050420030001d1031004140e1001c3c2150b81844159094845864042c1c0c00f13200b6207182c0241d0351199840d15505001c039100c081c485404450091403001102c1480740d415051003183c005420710f40c2c2c3d104040c0c0e01c0c0280c1c1c980700c44541041189201014000c0c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 509562374 1250 509561124 509561131
    0x4080d090f0807020415180515030d080702010501090209010207051201020403080f07121b030c02060f0403030806310c030b090a05040501053709081c0e0d0f08 70
    0x10000c2115019a681d0a40c000c103001c204865104003c150241140703418020165184001003e6402007840c000454114110301b000d940a50ba6441010a4041c0340d41f104140000f0f40207401c03266600a0800300508007242100c0c03260065103080c0001c2440780490003107400004050340200312540c245410050392a034240c81c02401903508010000005080c0700280c00f82e40d00403505262a8401303400d1802d804113070495860204641c01c0c1c1e00c8c3c00603041054016105507090701d01190b04403001c2c804500b003407068444014030a070002c01d00104266011031610712407a020766146040c50207001003810014142d0340c140c801c1c08014140201e561069a008102c815040c1c03501240041d002c40214000400503a240520303503455004003c01c2c08030901a998011000000b00031540c9500c40c1c0340d0400003000087d1200280551985114042003500002c0403640c0000796941c2d1030356030342d03202485281450301821140d42801016400d00d1404940c00c40c90414684911368035a07903c1d80c04848112009 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 509563624 1250 509562374 509562397
    0x12051e091905030d05090303071d010309050102031003020a120201050a0810050604061d090f070c02010c0803010905101e060309030302130603150b090307090e100504080706060902120408 82
    0x200680071001c0d44038261011018040c1010710750b14038002c881c00c001c0d40c0c070041c45000355920801c2030000855008180107130500118828028103800c24004030050152081f008d0025800401800000d00003400280c00301d903c2202c0040f141c1b0b5507240a01c81d00417091001a0101c0d506105038505e0398002c444243c0e10074450600403080d261500c0005525401c1900901d0020f41d03842d46440c0410200c02c40c4040840d800c403100702075803410003118014090010030030001c02001002035030440e4054604040d00d0340c0e0115840d80c032036847c0d0071050000d000403140f056060318220350020300e810071140e0000d0001e5001d10100e400c60b0620b0800d802034441580c3c21020950b0030010312821041c40301d1382034041d20780340c2c0d40810506480099142c10306442c0e004102c0b0710750108000429a5000200d1404071024200003081001e04000941d0910540c11152410705040008000030415400000c20809101d4681006203d803201e0441040f401420022414030005001140108004101034841036602 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 509564874 1250 509563624 509563633
    0x1306050319120806220c2a0227040f0203060f04080306270703140109060605030411060f0c01290d03110f070b0d0b12061506190f12051e09 61
    0x1c50340624030401c0030000c17000c0c2c1c003540d40c01c040441c10b520440760060041c5003002d811101c400c03028040c0d108030496100900c204a98040c0e8140904064000e940c40c02640c42d07805450b140600b80620ba032074030201e04a06c039014850001d032614030f40307040c4503000e141c0013101103086a4503d0144018414011075144030000d448100c0304685c41c4102405110300c0183e500407621080784140c0c0c80d0054030682001c1036880c10f0490500403d41d006c41a25032290700700240b10750410f0294041221403181c031a041480010006520010201c150402d551640711840b84a060042c0c03030600c0c9031407a541c02d480c198000540c01c80e00000c6403080e5000c03c2016412802e403420b9074400d120451401e54540e125015094000c6450314a0805610500d0810340c0196100031480310000000c80c3c44a10060100e40d424200715041900ca803603000a03a0328080003500c0364440d1341081b00c0d01500541c0126403d400040c0030b4103002080028034047e4501515448030814004440441900b042c0c42001340450001e100c1c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 509566124 1250 509564874 509564899
    0x723101d0a0510051222030311300106090b070b0432070e0c0306101211030105040e010c120b0402091c0203070806060306040f060b1306050319120806 66
    0x324240f0b60440559180c0720740c0d070354886041003480501002040240281c049146c08030040240142207503010fa1b142c80d00084400c031950510042d4041e9804c50840c448000c0300443e03203903032100b4560302d081a40b0070305418a0780c0d171140304940c1c0c00194040c01000c075800f40080000030300c5074958180c00c0340c440c48406550545a0b80c1c033003914000300d1440f07609208801d2111203a00700a10400001d8480c90468240a1820039000001840060f00c00c902815104e40b280c6203080c4250021340148545000501007104131410b1080b07550006c0c0a024403452405821400ca200b0500c54015860a10340f581540c0cbd03000d115000004254603107043d80c0182c0c0030005000140d035400c0681d0440c0407200b000b54040030040c018141740c444150442c81c003583c041d10070f0111680e03000404036070103944010840e2100d03411b03190901c040e1007580036058000344001d090803ca0082c60b000b450640d10160104c80c030003200e4188110038445404030103012406510800030802d0b01c41c42c3d584c1d0f44070030042c01c18150030a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 509567374 1250 509566124 509566129
    0xc240c030302120a051603091101110a0507030b0703050705120c0f07060609020315011106130c080f060402010f021902061b0307150b01030b09071107080723101d0a05 73
    0x201c08403405032081e5034840800010f40200d640341b107512a0940fa08224101040d507035a5581001a00f803070781401a080d40d00c840800c41002580b00d00c540c40000d5171001550380c94496281030081e07905402107418940010000c511030384c1502c40040810400e0b13001034442c00c041c00309562058100b0300d40c80000708070f9180800e865005550041c4000100182c2c0c81c0b61801d2041103950b940f414040c1041003046010710711010020344a0307005540c1083c001624a43d80c50000101d0170a50b005195500801204c0f140850340030032024482c5000380c903a000b0464110f00108d0b15601a001032905000c0d400d90808058100316000d04402c01c0b20203501d021582c0c0000040d451500201c0040326900078400f03400b074810300e1500804002e42400e00b02801241042000140d0208008200104000340d0300c0b041d803c0398404000c200b00400481e010f85240988551020b501c86881a4403240440445d030000d4100d800c000c03c0c95510281c241e9a0125030a5803500000390038078041d40070a900800d8002d002c115036 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 509568624 1250 509567374 509567407
    0x3030f04080a02090c0f030103030509040b040603060b1f0f0804140109080406031103060d020d051509070e010f0503030429040e04120806010e04020d090f030c0c240c030302 76
    0x704624801881c0da2011441004101c501c02800300d0301a00c0c00348014624480da1130103076410b403a4942811510790040c000440e00410a03800310030f41c0700b0304001c0c0c00000c2c407003c1e40c0070003072071282610704c0b11213903180384407091403d00d40b0034050000880c0f078805199002c1c032803009c07a60028450690316141c40c0b501d40c05c460a44601c128140c44100b0009001c00c050b43c1c06104120b4100c05140c6c0382030a41c030301900003900741000c040000e800b501c05410504104070b01481084000080485c1c011400d040031051150b8030251070041c403030310800c10341c00821082c0e003c10a0344201c03240240218985414000100c4150801c01c1001844000d01589099030100c180c005d00081c040340060380203030b0b00d0542031649a41c960001c0c14400e21092400380400c69a0203040e80c0c0d0f500105542c00b5a54007040b41c4044002e0400700300c06400c01201d04113020070158007a1215442d5405000050359080d141d2807084401800d40c484400b240400c440d405486501542b00860228020300b00181000c03062003048070786 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 509569874 1250 509568624 509568629
    0x5040b0409060e0907030819050702030d020706020c0f0306041b08060a0209010905090702071406120a0b03010606020d2709020706060303080921032203020109020109060804031d03030f04 82
    0x405444102c00e1110b00803050001e54080a458020b000183c90754440f00460311500c643c00b5204246203900c500a2401081212040c0781d0150440303103e4905810000d40303414141c0107400050050010803211494140340300c00e21600b00802038074072501d0750f9807402c5000346401429440c024403c00d00181a1a051104504c88e50100b180540d0390007441000406401254220070705c0713889100284400a80c0c00100501038451142e1040101c49040002800078002d0544c40a42448840204558030b02950460300311100280c2c02402415107494081c0c1e151103842c250319000500000c0600302d050846440a41100000c0300c00003489500c82086100341c3e4040c0e9001d458140d01c6a104008069022030031590144d100c0c005080c0300184800c21514a441220041108060100104a0601a050944010072400009502d62011915010b800b0f000300010a83c00309400703010010f10306001c0e00215200d103030b1584c0d400d1924200758003c101001c411543c100e40501c03050140754006200a00103001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 509571124 1250 509569874 509569889
    0xb1b070f14040c140a0e030c010309050618070801090501200f071e0f053007022106070804120c0201050909070c050d020709050a09030c0f060216080d0b0306060a1505040b04 76
    0x100000701d5000e0514101002030f0f401c1c1014a0400f0700c00210303330081892038210390180300d00505450300c5102603140040f603400101c815468000303650b081000551101030b003071404101d65031003414500e0040d0018050700c0b18070703290500304108410001d8559100052805088a81d440500f205500c803020307a6583e02e0811900d0360f21000e44d108440521030f860b030300310f20240001d1140c491044090f843c1c0c5d40c062000002d0050300a010100030721000e541041800c009000e0440e2032910b400f410040c40a81c1c1603a003075a114600c44201c0382c1041c441c0c2e283d000c103142c041c0c481601c0d20f4403100c203000c51180014200d00c20840860303400b800084040c802100e80c0d4900e5801040b181d0700b8040c0e1341003140d0019101010079071501c62a00000f03500509400c60254005210380048451802c10b07802070f01c110a00644011b5004090204022004024018038940d2200820a10b50000203042c0d1307959050b1615648a0841402007200224000c203001c5140d05c1440c140d401c040c2d660452000640098101d941d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 509572374 1250 509571124 509571137
    0x406140c030a09030605091614060c010f09140102091c050316030806010e220504031806170609040312051504020c012a0903080a090b1b070f14040c140a 67
    0x1085c45480e000f1907401814042c060100d5850000c2c40c12400c0c0450f1180c1650744050202c1740d072195990409460118480200a0100240240000d4003c14221904036140001c442d04003440c0031051080c0c036160304001d8074038600030003407172068480c10313042c014115401d100801640c0003030707034502e040300028600c05d440312680c07420320b04000b41001c141d41c5142400390b664070700070603021034101c13202040c410400d40d40000e654036103044c12140d036041408038004440700e10a001130050340c0155800900703e0116000f500b6521900100003c0103000e0310003600259482d80746078503034206540910703082080b034a002d4203c9601c003808203050341c21684421005035501d0000d1000356080c540d03031105800300581084055075400c140600b0700c60144c00b0190881030045078125095000d26541000342540e0341c4d503e500c1d10080545000488080c010b0fa0046009040000610b01150242a400e540980070b80d001076540c140f0510006101240105042040d280340f014045034184c40109541072071a603405 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 509573624 1250 509572374 509572379
    0x7020307051009301d0906060f041d1b0a020a020f1f030605031002190c060b060f07050f010e100209030115080d0206060306060d0b06010207030215091509060406140c030a09 76
    0xe024101030030f42142c0c5e800c41c11520f02070640c1e9040600750744000304aa60395190307100d403421054a80141d400c2104203904001c030340c1c0014072800e201a0b20a0400e46042e4100c91a41088504103020b00c070ce0071800341e406544d414005141c000c80100d00060040c010481030000c8a0319031498040c0c215402c40800d41c2c458081c400f6040c18044144002011407083d8070b000e4003560b15407040c2d002c7c921400c003000504448a0204401d682201d9a103080c014401900e81038520040005580000411900ca10030001020031210041c080e09145080c000040c101c2c0170049000b0f01c0295202c0300a1950655031002020160650001d4500c003a00604004010341055441c0c00392a1103005442d4038820b502c15000c1118aa4a14041c2d1003802d521a02d039203490b468401c0103078035102040c0c200030b5002c8054110340d40c560500d0b030003507c13a280d001c94601c440d03254001540034040c401c04441903080392080000b40901e6001c0c42c1d004a154503040240c9241c04900e060306400c5d80c010010480006560300da08 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 509574874 1250 509573624 509573627
    0x3180213092f0d03020304030b090f06010b0d0b0406060806010513090e010b0a141c030215070e040b090f0a0c090b130504110c1e01092102060702030705100930 70
    0x140300c039465090b42c40300c9810f00c850720007941c4c134019884000c1c0b01140100c0000c0e00d549052018804207032800c0c04480003543c4405440c007840d01701c0091207008500d0310f003056601e803809004040446400b910754269584030b8600449460340882422701000801003c009140e090038401c602d541c254480001036010705040c2001281d81d01030703205005100c6a502c2c035510a559103090481c0b40c65684010008903142442d0036402c08580d04079103000a070ba28402c005495402c42110883e52500f140c00b0003c0740b44401c1004180b0304103803041c0103060000b0b4000380f2548040d9100c1d5030f00c000a824003801031a40c0f4a0f42c0300480d80024254000640b40c0d032000c004070704041c021003a403480901d4040e03050207244c45c1c04542d03440030900080b000188540c209030b1f0308102984881402034020a81854034007a080d00d2081490f40c58a03608014402e11001558030b520100946003450381c014003070460441112042000340190034000d9910340c410b4001c16201540803150980d0b009490046817601034241c060 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 509576124 1250 509574874 509574953
    0x30305010605180120030d061403031c0515030f010c120c050a030f02091503090d020102030c040e04150509010b041b020304060513030209010e04060c0318021309 71
    0x118005000e024400c0100540303081001426000c001c3c60003101d88550b0b20703000c0d0b172a0b49a100b0380c1d40d4140000130f03e00c020542241c02c1881a921046031003100403039488241552481044002020305846035203410000c04907402807a040341c0740b00c08c1a1042c11440e03000909241e90251074540d140c0d5034105802e1050341001a00004007003607034080204010740c48000d06144104ea00440c105a9618207219180d4259030640d450390030090686504194040000b0155a00a550ba0415481600e018095040c41402124814030580b64a41e060518004042401880c0070f4412200d00303455401c401d2001d1a0342c8036403845007103c00c1c004100540001d0901c001c9480804070f0040c004403214600c0c42c4250000100c0e0111425445c02507918488030401d240045030f0703600020b62207031808000282d00d00700307040b40c3d0f030140d4091002000740f00d90144080d811078511101d0019445400200303d0094179102110010300310741d4500103c0ca461450ba1041d0031f20402c003e080315544000520300451540c4441c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 509577374 1250 509576124 509576129
    0x41d060c0a1101050f2a2209111b070302031623060301181b0203070b011d0a020313020405070914010216090207020d08040305010f050c0307170a090506011203030501 73
    0x300000d051282c0c140146a10040801411a180007081c03540f017088080310a40c1c880c41c4960082e140c1f40c1d212000c01d00c0311905011011001000e10001c00d8500782c620071504200f002d121030f6441e2803034005448000c2141e810305142e050040c2c0780000007503201802501046250540c40305006418003007100000c0e6081d507050030702c064200100a0268907800116410342d88070305c01c003d0484800b1100302c400342481c1802c888001b440c0d18000303208a90004047c16046100741644460f583c1c039250011862400080308403032b40c0c100c002c0821003ca095900850b0001851001944011034980105058800a03952403001410300d00c8200040b10a20405100e0705509201030054105c2142d00441031809a000c0c0c4208998001a1103085641c1e048451000d00c1d4001c100d1070b161562810468000c01b024203140b040a4100030000300c0402d4494100c80c402d4039140c0742c0300145075042528070307041c00d030040030007400c1551241c1d5030010420070440b0600030a450159108191640e24004003070f2801a07 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 509578624 1250 509577374 509577407
    0x302040c0e090609060d0f081206010f0f12290301050a0207030e19050d030503010e0109020c151f0e060f0904021e060d0f020a02010e0c030c041d060c0a 67
    0x31140544969203000503250040f00440d0042c4042d01e5050002d0604102c620004000c6296500c0c0d540400400202800c0e841848840312143c0b99116801901c0242041c96410b0024149074031200585014207002c071980403624000140164000c11200909201d003000b0030f625110000308000c2c2490240517103a07004040c0e403410350a002180da0040c00344552002c0045c403490f106504094080141410395000f401d0050144100e46100d0801820b1170f4003c1c0141a802c0c0001c80021602000324003c40c1e4102c040d460080000c855061484007007180c01916900d401d00800b03005500d100344229800c005401042c09403141420700e10100311619101552150080c0d4a02c42044003603550300d4103400d1128440848008a6026580080c080b0320814005041062600210b20420b20b40c680c0904820056a002045816a2041c1c1d541e84c1780c24442c40799a01d50b20100401c0c245042a4100c00303204034600065161101510915604112044a84000714040070030280d0240741d000c00310341010300e02c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 509579874 1250 509578624 509578637
    0x60e18011e0b03010e03160f02030f01051303080f071d040b130f05060a122003010c0c111518030319020a020126010303050903160b0301061119260a090302040c 70
    0x41c87d00c5100b203030b40215400b404000b1108012000d40d10b090040c3e0000d0002607000f00001d183c05a00350b141d4401c04101503002607808000140c95100c20100d11340a44401e071140422829195403200c800c1d149585200d03041629030310140031544413104200d0303050001c241c010481070428510141210802007019100310809182000020b0b41e050408540b42d802260700000006602c0b595014408190881030b0150718000d403078000140e1007420600c0c81c910800380c0d0101400c107181003244200d040d40e00035841c0c9408203c040b403052600102d1080034880541981d050001e00124801603006400c40440960417a44190341103603071000c0000c044140c010000480d100d05240700c400403020500004007480790000b8a40c03580d42d02000000b205041660094901030b03240c0035885800e030400c4c440e00c004580d081c0104500001c3c0444c410011001950460000c10b0f41520351b99080c0303130200b510420540050742c1c0c101d003809840c0c0c01880349030303010b0321003852243c80d51040c4001c8601c841165400c200c01c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 509581124 1250 509579874 509579887
    0x20c1002040f171504080a030b01020114160207050307080303070806010f2735030412021c12051c050105030c090a0e0102040305011e060e18011e0b03010e03 69
    0x100036070b0207446100b207101100b0301a105800c0d24202e440200d880e0044e410310100010000010014049181c040d0340a000300b0440c1070040e826110001c901d00d10b83e1010000040580a61000c40ca02c00c2034184101da900c9561600442d04203191074000b980306420000400580c203810107034280d044003080c64082d5089030781032801408060740380000c1c0480c00d030905031030440c0b1040c40c2160f0090000f0328042481082d4054001c080703035062440341140b1504a10980c48114008404d4074111010b0042000d8170040c96400c1040c015414500512949001740f0f1100100e0b19241d0343d0710a00d06561101640c0324681c1078640b0509101d4410303180e6180c10040184150346005c10400752003441030348e860700c5039210910780001410342c0c044581d500350310214000007030002c150440d2141a20f50250440b190f1559440070007503e006000d4003103094845804641d000680d24100755100a061f40000340f809003e414904000302c5120b40740044585a10b609182440c1c28031a801a0704c4010f0000c40c40c105 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 509582374 1250 509581124 509581139
    0x3061312050319140703240504020904020c0a0308092e020d0e1f05130302060408032e050111070501021c030b03030d050f0c03040206070209040f0c0603020c100204 72
    0x5031460085000c0010120104503480c0c00d00c8076002d54110001400e101a4210340001c0d240d5103411140600001e0030b00200c1450401d41e00b11040380700c1140c19400150500b0902030001950104010310f80095007001100010b00c402d00c01005d41a00c40c1d5641d240500308055030929001501022410810000c514412340c4580705004106010202a0150f00d404101c0c40c40401000d07400c0214040740501d00140b00b880386120200c0c814003000c40030030052610386040b0300d1261820100d004025074401c10100340070591107809907034403e41003c0c142032000e1302c00c01c0b918030460002200d0090b02c07201e002c013400300d5a000310800340070702100c0e002004020314200000f0750716a4040071540ca101c564a16401c0d20510a40101c64800c2d005400c40e40e0754807044021000405048a4000401c5040b402003236920040c039080382d0045030002c050034100081602040121400600300b100d80c01d9200c0222400581c4900600f40241115140140c8612a5550242c02c0269120161402c544100000d00c80b11 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 509583624 1250 509582374 509582393
    0x301091b081608040305160303050108100905060609060a0f0303030f0e0303060109050609030106091a030c030f0705090a09050a03080a060515031902090a1202010e0402160609150903020a02030613 86
    0x2c000d14580301001d926641025115881001c034a070800781c2c0c6101c000018190903400c09070403610000100e0303070014100455441180d010400080190304110086030441c5082540c66800980060030801c0d100da0301c074290516400f841d8000c17000310f034590040c0d612100040c403c0d114900d800c00040c41c5985003010009010312030501030a03200301c2d404035110480d40c9096000300007400d4412410400b81421641c0002c05003201441181f0034070501c403550025042c0030800168003040c0c400101109030805081105a80000b404840020f650301c40d00d001081c820000740c10700c14042d4985c0d0b2203d0500d00601000e44441d60031440c0202414138811540c2d070448800c481c0c1c0000c124040746882c43c01d0a01ca04043d201e00310388141e02c04600c0c000071071039208c1c1c11503e450003403007601c804620040200502c0141d0181465030380c4242090303402840490110380110000724481c43c1e22120344008450441b007110003102c0103030300680c40307042c07804111b023030410200785c2000b000941c0c00c41d80d5509985a404c807 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 509584874 1250 509583624 509583661
    0x607050109150b03100c0e030f160b0406140706020d020301030b070e040513020603060a030f0c0906080c060a0c0303090213090c120506042d06020315010810091806020301091b08 78
    0x49541d0b14a901c01d014428000340716611030023001e5a02080d005819141e5608920072052039801d0181c000181e40030020007240d04441a0741c072420003440d1010981540b80e04180e02c141e460507000c20040061b02c0c4944000d601079481945144194241801d00400e04000c489456015524090a02c00b9140745641e4004186504035903143d40c90751107101040c00d01200b0341c0018451200304c03016104100140c0c41d00c8055503c4440c04220550b40c880b21140d0b076400b62451242c201204015400b107040c80b0f183c5010540f806400d02007800d000300e0340401c824060204503601910741d00c0350350304104100040860010307c2c24008101150300142c440303d854801c0030740006d008071030100187c03140030144001c0f80080e011112a064581445041c107001030350084070001d904400d1000c42710710560207410918051024a01e00501e900d080482c408000e1040c08003140c590b41c40d6081c201c000a030580000c5028005414003c1920070110039440380310b000e40700d00c90701806402020842c2e10b2010b074004844 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 509586124 1250 509584874 509584903
    0x50d05041814221502030601020f07050f011b1a09010c0e060301090203130c0305011406190521030c0f0d26070c02040e060105030d0c020d110f0607050109150b03 71
    0x200004500c5400c3c110745040b00c014807404103c00d092220012540c0030f584038220a0b02034841c0040390008940d210349481c02040d44c0440c420f094584654400e1443c291561000144201002c0b01034456114101809440b01d0100d0749104c20809403003428000d08164020f2800c1041401c01c1040004480c3d01050007a10780e00d940c0840040c00b0300310180c4180894580040103c032280c1d4a80c2090350207007005860328404001c5140101d50103007041880d000f038040009101031045ca04281c2000440d0b514511000303000301c1c0600c1215004001807005108070b41700d50000305042004400d03400d0070300010341001c809001d902d401d01900c01d25800c001c0392080c510800e14840076030300c411007030741e01000e0810301a4110303181484a243d83e45d80014000d058079800c13001c035851801c403200100c400100248009411000c12040300c00081c3c0300d5254162a01002014041c0c00d05075400858126040700c03c050b1f0b4180e450b2404c000a114081c20301304000600c2c5241032040000c0e250120356684103002d031a00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 509587374 1250 509586124 509586151
    0xc0603060305121305090408040509180d2d0e130c210609060e100b0f0a0c020a0e0f0412020c0f09060123040501030b060a0c0209090307050d05041814 66
    0x707081390155405001e4400101080032504140c02c284d41680c0150049600134000440850301d0b0b00d0303500d80c8880351607401000801e600c1290b05400c440d24038445588400d41e0300c1140d560074004050303241d0103002d00f810355580b0311800c0140f010090390f45d484081601c4034a1501c1c840007580342e07000f5107040a50344009050f030030000c0d80d6111b101c000e01480e8000d04c0b0051034458049503011a000c0c115010380c0613031405406850f2100a54039180c400c10701c803120030030006c0100a4034180210283e10b0598001040300c02c0da0365992954900d8000c0c115480c45038408810200b0007007021101d010f0903c10014402410f12810075004904079250081071144503002e64400501140e00c03030803003240544c59220802c0704c104651008244250010302400d8040b0307040a50203a540d080c0302054a0f11040c0ca651070900b03151580d000d01450f00380240c100c200e240000c10400012417010010501c032844180d80355507a0303e2a101c81d1400780c02c01c0c1350200045034107000030b9200064bc5141040e80042c02e450111 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 509588624 1250 509587374 509587387
    0x3080313060501090209100206061c0204090f0f140d12091103070305100b0d021c0c0b0c0309040c05070c0303050c072d06091d15090f040c060306030512 67
    0x25080c10610000003011103003003900100c1e9500c025000303007501840960304c44941c51400c040590302c84400311189030f002405200840703401e0f80098521701550303001400000f24138166855821000581e0f02055409240f004007840400440340b540000c001c9040001c2d2841146444004100303000300e1560740d6407991199900424040d00514807214890b006044813030807540c0303103040394580d25525050604107107840c0d003c0306d0350309103100c1a182050340113240c04602401540702c4440701d040741c4019a03007400c0110010460800c00c0c4020011122034030015521030102a0401080e00c0300d100aa0381004802d0041100144040c4038040643c0e40c03504084c2c0e1283e040450b4940303805c0d0145e001014503414a0426640c10007900b103000d00700b603c01c440314043c1907201c400a94014000d4410b916072882d140341800d0540c080c9200311500b100760000010140300c0b50b42c0026080803010ba40c80580005207405100c02c02c550b58007500020a85070406010803803030b68541c81d0301c900900100c0011200c001404c0d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 509589874 1250 509588624 509588641
    0x10305060111011505090901111911070608010905060f01020a02040b150f04030c080109030903060f090602031f0806090309040905121c0b0402040308040b0d290103110310030803 78
    0x80b00300300304003200200000c140d480c01c81c0300d03550101d109480c0940c001101041600d201030280e50303121010360380484d141c41e481481084206408807680801c00c241500e0f90800e48809001e000010112179540d4800c03035040802403030441c0c1c07001d44818440c420b200556100d030390b000b04540d2a40341d011200040c44c0e000500104480520302c0c400c3e096140300020f4201c0c02c12121601910a40c2c0c0a500d208010549445402b0700301e518128014020441c1d0910800004400390040c044c502450107021848490369910752041c6e80068840c0c04104041001204030900030501c040014403400004015505082140ae52680f041a643e42c0c040c60301c582c8044d0612000300a620042e00300b160031203513942481401d0503100c1031a4250303c06c3e15401c00400055916090094400f981e0304405894030b01440d040c43d244142d81308407001545036485901240c0c103075010f245034998812100500d00c12009600000504945070b126003c1842c040c2441402280c000c1d00d940b40c0c0a6a1744081c950b07541c2e44070201d2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 509591124 1250 509589874 509589887
    0x30c010f030f0f020313151a0603040302010b060310030614010b040b0f0408100e0d050a080c090f180615041206051807060207031208042d020a090b19030c050103050601 74
    0x4400b143d00e000100f4001d1040180f064200302c80d0094060860848076a4080e0050340e00309440d40d0803411108010b11400d00e000703001950018464000028040e16210200c0c200c1d80044034149000c0b1421402041480807501807540c0175006100316440d0366050081060785800fa600410318610f41c0407540b03c2100e004881124040c00500c1c088580036008034042c84041c0c401c891a41c004d9000d03182c80c0f0404c240c010025a1480d90582e1174211503645d4548080c410354004520541d0301c451540f507100302da5210100400704400748480003280c14a060014807144218003c0d02c0c111090040004000440c00600c402a003168032090200d6681c4038401da502c0e001c400304082c000309000720360000450540000352041102c0c4610b14415821600070015940309500729406400d020880130012078000d141d60341035400d9aa1072440c540b030101c05401203401c19407107801015a40d955a0740500481c500301b00240c9445420b8420000344030308550b82e03090b41c424207100d01da05047d142c1c1c000c2402c9a02960 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 509592374 1250 509591124 509591141
    0x9020d09200a0e070512071b0302151b1e090603011404060509090606010f02070f0b030a0b241312080901080708010f050d15060602030304050c030c010f030f 69
    0x503180a24007080035818042003180006203204804014002542c240316554203482001503448150403c00d07070240300082c0706c2004010b082049088240982c5540c2070144403002c10780070ba4014992000c0c0c2340050507103204050004010212700407651804142810110340300c2101c0710703000110b00852005c9080943c02010840303540300401100129006403201c400d010082c0c01143d05100303481ea03501c18044000c00540d0301c2c81003a0085400181c141d4020110506101070510441e0641550759134181c0048000d0340104501c0800017083c4200040e0500032422554000c992055200d00c808240d0026104140c5010f0705844001c2030400e20003028580000c0200400d03402912040030914142e42690312600c48603020405042c0407816251041030140d050310410130244100600300030400401c2d0700103100032070302c550f20a604501c0e038a60500a240043c03001750000e603282c3c00e10f490710030b084c09500c1d070034a0b0080d8000c0c0c2c00c550b441c0e0380c40142d488134050907003000100d03205401080360184c11140c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 509593624 1250 509592374 509592383
    0x9080d0504050d120b06190927050105150a18151115162a0f020307060f050406030b060706052403060402060a1808070e040b0f07080109020d09 63
    0x210030841400b0011402508101c4255a0403a0000c402c643c441d08407452900070076002a010711070b61900081c07210b0340b07201c81042420080c00c034079914000444400f000201b4151400044590f025070340200340519800340004440046010a650200c04c915000700c61840c5c1c1042046d131443c4803090f2031440341001a014005c1e0f2968141c0031a0b102610070000321052503602d02c103010305140b01d4081d00c810507016403440b41502d040028001802c81e5034aa500d801c0480100c2c007003290b00d00860a0910260600748505126040d003140b43c0100b6040132125072203503003403008400d0f1516156601404407010768801d41000140e0021480104840d0302411200802c01407404061282046400744650204002a00510117120440043c551584415100250450402e020903440a80030300c0c41614000020402c1450650381c4084079440c00107140d200d000080d108005000c14440d004c1200c540c85020384100c01c1031820705241c01405004144901c200103580814101103c40e1b29410140945400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 509594874 1250 509593624 509593631
    0x14150a080712030e010c020f0906030c0415090c020303160810080f0f01050a060e0114120a0b010e0a020a08041202030f220501020601060c060509030f070602071a01050a0909080d 78
    0x299402103000c0b9600600503000f180d04080001e21030b41c4030306160110307107078050905c04013201204240081100c3c040c000c00e030b1500410038110070070348681c0320364222400d0401d0300000441c9440410403c86803045107103001c44d00300304200302a40c00d0402d2050403400c5c40c0e20b008881c070f42e183c039200302c0400a29045100240603805403003100c80c00c00910b40700302c1080840208225104c3e00144012141548039180d2587c100c0302c01042502c17404002c101c08004040e00b01e00780101e0480d03d103418482c0901c0100d43c0c42500c0d8005000206050340c98560144915008500d040087c2901074154103000300010400794001300061509403080c070a95640c0c640e0010896107481c1c16000b0302200e9941008044420046010005200c0d8800103030a0b0480710305031074180c081c1005803150009004000c01030748452100b000071402c000c131080001e1403098080e060060300e50100f440e24080307001c0c1108021140c40d54030320041c0603582c3c442d403152046a0b0300403030020707041003a072604100500608114001c4a4034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 509596124 1250 509594874 509594879
    0x607140307060c03090218010f0902130b0c15010e060f0607031206080c010e0907050909070c081602040b090c0a11011401030506040209070918020d090606180e0114150a0807 76
    0x130180c010303507112442214001d21302001d4500142000e03500b403080d15182c00700b0917410000444141d0040112080700d55040c0c89117519101058042d038010300070f0000c25848640440210741e40c1c40121409071811182e09000e5003412000146003510003828103215650000700c020805028016940e000540ca200c00d0064a5032181403540f1240560f02d014003040c159024103406d032403d801400e200d02026191a41018114000d02c114140004c103180b00b88a91101441c004c662128040c2039820b01c04440d44a041035030307105100175101c03402c0205000d0800f40b400d11400f040900c062b41e025882d40e15003540140790582c43c0c180988100021070490300304010010042c04400300b00d0611490080e920520581c8880c0e0007199659240d219250000482002010782001c1c0368008090100d8016404590124507441c1c00d07040742e40c154070041c0c0c0020b0000c110f03032450040e07000e54402009010000c00a40c100d200c25001c4410f8010040c0e110312000d24801640ba60740d0b482008041c0c4544401c0702e0700c264 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 509597374 1250 509596124 509596127
    0x30106204308150402030604170d02030408030612030a140d1107050c03061303091a07140109030f09030b06060903010908030702010b0f0406080a0b0a0e0307030201060e070309020607140307060c 85
    0xa40501409542d03009940800b0b030043c541018440c0142e6000d402031400b50f90315180d10740741484900b002a060202003126008014850028600036400341400300d40d20304102d810403aa45503903041c3c948807500240300180d03e10350010011600c104901d000155629207110010000700ba120b0039000c240000400d0307203014800c0005044040030010760445a1540302c640c202c1002c250310040080c00504001b9082c0516060307214000d2a0301d4446484500304401540d40e01400c1541c1d40c104440f5a64492800c02415482007101c00041114141070a001e41551100074603080c005101601612000802d170405031400d6010b11561a08860303c5500c0741085076009000e003000303070b0700c10703200368113500b140c000380e25242c400d14045070302040051001c144640c1c3c41c110380300f0340109110f40d00d075074502c038a00e00d26605200401006100c0e500004410b070410075881c0301300b08080c0405082500d403556a00c010b80740c210407110090340140c4144494640d0501c520700e1842040801051241001070b07002d1001e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 509598624 1250 509597374 509597503
    0xa08010f02070c06080123180a050916060f1b060e060a0f06050f04090501200d27080d020412060501140d0b0c131a03010620 55
    0xc600c0b601818051569810045174840002e000384d0b03c41c54000644907890f00c0c56410384d2410311801804000054540014034545144203e0709046881e07140c030100b00d201803041c0907640b0b0300c900800c0b902601606051000f0202850510b0510038000c411101d0b1403904030303550a580741d05900080902c0a00c0403071402030388682c0107440320080c45003400c042d000c540080d4000c0d20290b0718050245072070b109191040001410f0484001d942d555070310620848081071b0002d49032a40f54000001c1e96444610910000481e5404490403028103a800c00303226041d604200f0391030350b207904403ca082d1954030600404000b0301c580c1c0d02c0040304020126100d010401329070845812100d44800304900b10303121034244a001c40c0082001031200011800040b1002414806000080540394100c401c46031101c0780c40a2448800582100d0500c0c00310040040c950720a0f031000c407440c036068803410301340c1c00260010b41c0c0d20843c5004602d103410442c101d40403280345064001044044049420b128001c000070202c10303 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 509599874 1250 509598624 509598637
    0xb090f181f030b1623030f07050705010e06090c01080417070302070b1206011403100605180a090e070503120f0d0209040c0c05010e0a230a02150c0105070c080d05060a08010f02 77
    0x80740070000d17412005800140c5068050020761265460344d070787c8800d05100300400609120501c0420b110400200d8070034407480c504028a80004e10380360a010708994a070880090320103042012403020040011202402101c14a4070401c0081d1101e0151a003a4140003075504140f0a0740710214950040e442c00078903450041c0000e072101c1c3d14a0040490703030072503480b044031050b0303015444010420070907120344020701402d034040c140b004410b200800062081c0896601c40000a600c03060340d0b00031110300744030101c0280400c4000301000d4080f404900154000c900c001e45001c0c50204480c2e0242c00250101d400c540c030b000307008001500e1100005421038207000c0c000d88043d8030f4600d0580c01c40742d00003803c43c0301c00d03049092450010104503444c4d135000b0100c0c0c3e08141c45e0060320510780051707c07240016900800326141c490788503903483c09840e08440c0020300d0f8204120144401001052944084461912040c00f0101e5103580e42c81c041401c0d50700341d921440c8150320340030036880c05c106a680035060 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 509601124 1250 509599874 509599877
    0x30302070209040309030b07050f12060111030409090b06060418050702010b091611071406130503191101020a080d05060d151e0b0a180908040b090f181f030b16 70
    0x201521600001c803270a0040351054090366004000004d2a085619482c1d41d000c00d051400e0031007400c01180030350440d00b041d4450b1440326110048241002044003400c8d6201006031540b41c00c0c5858040c120143c0e541401001c1441075483d8085582c19100b90019414600040c101d40340034100f1202c10508000700ba0623a134002041c3c0a2076894408002c10f181049032602400c4450000b580410401a9030012450f88064032403014005120f8409106003504c0b002d0304407540880c2ea20a0502e100e244160514860441d041801442c00180d40441aa0b0701079159041c005001e039200408260302180400014001e001c186100080c0070926800c80b04a00b903d0300c7e610306c40d500c1c038001250103803140300321496800401d1840034440b100c11020144c071540141040030425845075151141c0540c020780082480c900300081d05060b03414a20103241d0a110140ca030390034008440803030503003240d00162218040c92140204035082440c07503110b0750051a0403d44104403410201041091694941c2d500d50 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 509602374 1250 509601124 509601143
    0x15020a09031a0103051f0f180201090909080403060e0a02030106091b0305090715140304060f0606050306090a1a03100902030114090a110a080d0801030308060f0303120403030207020904030903 84
    0x50b946a01d210300b981203d40c010000c0540c05240d40c102c43ca0040840e829900103030782c0b4801c0c3c52080280d8050640c0c1e002e5084000391014016000040581030343c3e401101203e420000b8010001700b14400700d0b02141d4010000091217050805d03800d0a00d6802c5401070742c15800d105000c41c01c0041d80c0e100c031180c4441800182d400c000b1040040d819900201e0b03044499802c060020040783c90780805004d1400310720b10300001d428044581d03101642c1c0003a90240c1704656680c050100381200c1d0310441c0301030300031818440c0c15803601000080c003100004105901c055260315000b0303201411070090f130300034840040c103980d00060003003503003001080c1c9004140d200750b083c0303c0000c0030b10b925805003d00035011000500388480164030f945102c014103682035600700003c044002440b107001d01c134148070410079544078612540740d030400501011024200070310442040d8804c3c01b13595000812a090010004075404c00c5640341d0900350700a000b802800f03504942030b04100010107500a40e036805480c490340811 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 509603624 1250 509602374 509602403
    0x609140705190305060a05060103150b030118051501110c060d0e0d03020c1e07240210062102040b0901080a0c060206060108150a03020406060207170c01081315020a0903 74
    0x400702c0300740d510000c0e01c10780185011804242d01600059070200d03043c100400c5110205c2001d20031f650782a0700c0f4980841002c001442046846080700c1d1282da4105014490b17410202c00349034207085001a880c1c1489140700843c401010140040180c04200501c015116924044a04080e112040807080da90290f001e1a070040c502174400e44051254250060080041e5000e044902d40c0c00303002e003100c10f44a04000042c1281031103a21b050503003914002c035000c0d034990080180ca00352414203403034030b12410f0442c14011443d0481c5280f600d02805074a5060b085010300100c0d00901e020300c1d6454004a100002007003c18000559040341c41c070661142603030790b68400f82240c40d50019509207000034010004142c000390020013010f400d080081254074078a80d07960000d002c84009500031000341c1c2200300c0802ca9409025410f00000c0040ba0140c1200149400020f103001c0004101c1c811a010082800040c800c030303100c1c140c040c408481c00455540007480d60290a6440300c0c44121010121100700 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 509604874 1250 509603624 509603659
    0x3090f1e060601180801090f020f040b010e04111902010c0f08060109030f051f0f0e070f0317070c0603090b060d0506040308310212071a070609140705 66
    0x848003a61000094a900e4445100448900c1054038200c04056007075100404c2040013031083c03258813441a04500362941c0b072441841104050b00c03940d50f11543c9030281003015a40c101080c2171000c00200c5001800800612400440c1c0c003400c602d041e050040c1ca00b80f809850b80541c0050100c854580314420600d40303c0ca002c0718560340c2110a140001c000142c20000075942c0340104401e1740c49101030315805400c031154030503180750b8011544001519041d401083c03402d0742c4100348215402001801076241070002d81c044401291000420300d002c80080416658841410341d107a11364040d40003160a07a0321000103018203101c280599030012244040340d0070b40741c0f00e0258070500d80e024001d0052540c4584090f40c04038402010b24403a100c0100000411951042c2c0801e04002c4420081c561075656005000b10344d411503c8900903a0301414082c0b110700e000f0a50f0800141d501c41c41595610711a1800d00e01800780d0070001424403080000c61400420089440c0c003c0d80c40a451900100c00007018 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 509606124 1250 509604874 509604913
    0x6010603060b1c0906090f031d010e0d020603060316090c0e040c0c03110c12060a0506040506130915020f03070305070e0a120c08030a05071202030909070c0c030803090f 74
    0x1904a03040300862400c42401c3c001c2e410981c00180900e10010307000f1800e84072102c100811820403400248141d1040004801074007100794521020310303280d0342c0c1c2030850307000c075400c00003000d400382c411360020000410980e000c0005a03280c500c175000007111103680380c20a80c041c0c080c18460901103080c4505c12101410548501c55100907180d584c151580c0da0b81c3c6040d07030300c0500720382c2051490044800310b80b42034442254040c640b102d1080200703658076010b41d003071741142e0303024042c180320320300f0041440203580c0e903240000050761280303200003844091890400410f40321401c0906a2500108281c00b0300104140590b00c91155920309005c81d50310340c01c040314540301700c1741e0107940b007002d01ca402c3c0140744801056440c214031614070401c0341900c610040d480c541010b6421000603d001651108002500581200c0c1e11018002181003403910000111b0724079004191030100810786605006202c07007410118010354110dc03845680e0300342004981c1c0c0303500900c82441d44620403000100c80080c543e15 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 509607374 1250 509606124 509606137
    0xa06020c33130f2004020f04170a03051209032221121103090a080a0c1706040b070216090c02072c060d050303070201020702130504020325080a0506010603060b 70
    0x1403003141d000880f03542e840c1c081c981d0808801043c4d03d0903a800a41500c0340e00c000c080044140100c3d83e122860b10070444102040401d00c2000b036005601d1040000390054195441104c50902c1140142d0311440d01070300d03500540413990b09900b0240065071003a84d26803010303426103079503503400c94050418080c10402000c08030b000410b02c40d00e00690380006449080c55071030103001300c42a603107000c0ca4100098070510f800e410200390f50300403c0040342005020f14461004140207482e40300342119400d05031f0380714080104082d1100395150001003030b0f03510a00c24035a0f007070307c1d800c40c025200d521030003484000c01c0e64020000c05442500c0d030114008220442503150075a014401301c07000141070b504610007910140c125500400c0c00b41c280070000368140040d600c9500c8a50005803511614010800c0c8018036403281c040e050701e0001804003688010942c144103180507000b41c1840902e02e841c4091455169020340054044e0621030000c005022441604840d407960302801019100c0912407203910580 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 509608624 1250 509607374 509607383
    0x10614070611090406050324090c0306161106090a0201030f0b1f020615060d0c0e15031f0302180414070801052e1206020409060e04050715020a06020c3313 68
    0xc050001c031052380c103205502c442e6450981d2103603400d031700100b8907002041d1060300042d0154880322001940c86950882c0c4085541e00401c02d42c10038101041e211090288080d04054452920880117625500440c402c07990190072072407440e81c0300700400e219441982070030f00140116004142031002145481d00c480c0e00040200307150114002884004040b21880720003070145100a10780d41e0740d100018001c101140d9042e00707560740b50803070060740c9203500110070359008a48014140056140e0b0400017681c0541e070181c101c0c8c0c540b90344c1004142202000007a5001e0300c15003001003240401034010074010007000d0072111040100d01200c4030740913450040c005c14a142e4110400c52030b40c01604d8003503807a0155500600e00750300c4403440001d079041d0340c0041e042034620005020030010100020001400d160100c44100d8840e40300003500e60381160070141034a2f4020030007050000c030038030000307822654100b02011148583c0c88078007404108642201c0d04004001c0c002408114000b182556040e0311 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 509609874 1250 509608624 509608663
    0x51501050a270f02120412050403210c050102130911090619030b36090714060909070207030b0a0203040203030a0c081635030106140706110904060503 66
    0x1480c81c8018070180920000281e5450f01020407454600348014409408107031070085440c5010706010448102d980e8015082000030842003010400c00454001d45244456500c0c400326420b040c1100c401c0c0c0ca4040c007174003a5200290b20709001010100810031500020b60038440609400c40a070204c3c083c3da00c5442d0800c10030414044c00001c8181c00e200103c01c1400c00003400740d80c170000300b802c08a81c1d404000801000c2c0160604160450090f41507010301408204c02900e480c0c0b01071511498244902070f6070381c075075050b01201552078006550490030060803e081034601018001d55811252009507148001600400c5181246000300d910440d0060300440c5884039002040b603601061540980b240301c4107100e0a660040318034070003511180034039007001640702c2000b8105034001429000300c0c81411806001c4848d42045420b032411510941000c0c00c101074160580902e40c03250100c014942c501c1c0101d0380d5640b4280c0c02c00f03005484400e40d41001410740791000d00d0f54a0741c3c51050903012040 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 509611124 1250 509609874 509609909
    0x1807030f0303230103050a060b060a0e0f0f090406050f0105060c0303040b061c0c050f042c150a0203041e151d0102070b090f060609010308070c12051501050a 69
    0x41d40081156000010b40340d4442d802000d800d04010f03900381c008072007a40156814405001242c0035a0016a008030f840524011040801404d05240a51407900070811030070b5a8640c0c0e661200c43c941da5640140440d441440c1031b01e41003008040444505050054041c00801d49007004000d03a2103070b00c10034004500d0350319203485520a058008100c030354054400310f40301e0900c2002c41c401807182441209052400c03418042000516036615000c54050352501600459011100d03c00c1243c000660241c0114400840e82035030809101c0d40b40c10507107000f524280807160364254003c6100303038018400c0b0359012654141124406070b00c41c0010303250442450150000c852950300400c00260241c030b05500001d400b41c071107400c1ea00444416a1280c0100003000510b403401d0141e42a804d40c0a00505083d103449d1000440801c0103010241210314041280c50030031115501d200c0180035003ca001032027440c41d1070060307a61210240d051005d106854000601410005156001c1d181d07414000c290000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 509612374 1250 509611124 509611127
    0xc0504050d082205031e010f0e03091003270f0515070906050a0801090c0c021306061b260409060b0301080d021b01050717040608040506090a0b040311011b05031807030f03 75
    0x1002802214003c1d56102c10020040a507803050000c274140c00000b45440c2d07003040041151007000d2a030b018091500300300e1040110b00b999111404030010001c0c0303003030103101d0b0b5082000743c0f5a0003c4000b0014800d103516581d00300100110036100c0c403015514880751986521048849000d041c0140012a0101c40144403580c441d8002c801c0050b503a2404070b40100450300010034079510440302101995850324140f2503150b102c41401d041c410b05100e6802140071a54505c001c0daa4280305164002c01c207811001d0030b414038a01181c0c003c0102200c01e000c3c0d0740d10348443c941180e10a01c117180d4940303d00105004010300100703004422403034020030001d03c45540740043d1900e60003104111540790b1680d41ca01039a03480390010f031019102079510f540d6146030502e441171070694007070207000340750740301e06010f00010f40241041e40c0e205505184c80f1600070314540f041c902404a0f050849924600305a81e554140c1c1d0020296100d0011258000460030610054a07240c075618040a4410201c42c3d00020119 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 509613624 1250 509612374 509612413
    0x1180213170a0b04060203060a080703050c0d03050f07060f1404030806060307120e0f0d0c050307080706020c0f0c09070e01050405040903050c06070c0b0f15040c0504050d08220503 79
    0x50807000d0603100403021681d200000c0803800c840455040758048184002e604003981d00001805009004045040c00d60311481e680d0382050070700c1b0b40b1900c8c00c403074803200300340c0300e00151030b51081c148001540740c55003860308102920f0b0076544a907441c0c1c0f400700701500d8085a850350600454142e00c881c0c00c2034407000c00b400402e81c0000c214001340280882041d02400305441100c500c44e0845001e030117040a5903503503905140c40002c0300d00800418560160124002008841c4032952010701caa5a40b10b03a0302c0c0c5000a4060282046610f000e000010b02c1e00c404045505026200120f039410f844e982d50318015111804981c06140c00501c0c20321003442036042c654841c5071080d00904000d8145036051501da8540403040315444005010b8400314410007082c45d0f04150400b00c182c0700f20340340d0301d0b20420f8001a81500c840943c8184e0f02c910103152410b0003282181e01510001c4d14400c0301d5101410220b1071540310103403c1008003004501035084007450b10b8400107032503000b030180280320666000030806 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 509614874 1250 509613624 509613659
    0xf050c09010f0e0a03061b020703050d18030c0305010203041a090a020904150504121d09070f0c0813050a080705061b0708100501080d1107091109060403080301180213 73
    0x2071000249910381d8994900305141d0045200c0d800c00700d10307c850001240c2001001c086118255403003880d00380006a0f0229034100c4002c090310740407200c100020302840062800c1d61010305010340c0c0740e001006110b07064008610650284558003800710413420011981c1c14202c030b840010742c100803030040041c074003006243c0d0401e0051044400185500030143c04580c001d45d0102d540704010304809070840d40056105140d81c0038001034411115540003c144407030001440c0e80d00704841c1044910215002c0d0704620070b56a0001c0800d5186d954582c09200b0b1358100c1c2c082c2d20700c00d0366898000101c0c14000141c00e8141c5101800b15810300d010007004d68000034181c52080850b0280034000308030f280f000c00c0603c1201103207420200311940340080e01342c10074031096060300c100001641418209034000034100100c8a002c000000c442c52224070100d0303640a034200c0c041c0c1c00303d400074000080c000018042d6040c0d401c0302030904180d41240410b801281301e007078980d54140f40c110700100112915420041007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 509616124 1250 509614874 509614877
    0x91a0603061c02030f012004050312030c0c100f06050306100b1b1f1404260d050a0b030d02030a0905090a0212040302100501050d0f06050a0207081c0f050c09010f 71
    0x24080b640c0041d00f00040300c031018540c1da5484203100302c00c1550005c429040040013081078a45400d110100c1d4841e2108001441c0c202c20000202e0074241e03585080364004071f0f100b8190740b800c00c0c0d0b03180b1a0000d0078900459185141c200040440c0c945404a8441e020f103642070030704202540f41029941841d0452002c80d801d88141001c007001e001001d0082c02c2030885c08041e00c401801407808040c048480c00d01000c9101b03203a040802c0300080345040c8003501b10031841000c80501d4114a450304551080c1000c81142505103018030842044941108801d00800c5056640e10301440e0012642da00030091800e002a4010380e04000c1030800440290b00680e407054058030340320f039a00310071081c03c10036241200168085c00148645d02164403549014113011981e406030b020181c0c9442620001c0404040c00385503903035002c40c1b070000281e811100c0036940401d0181e2600880e032500c40e03080010030311031030400b8100740560744806c4203403091600c529015640542000c11840044413140220a8801c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 509617374 1250 509616124 509616169
    0xf01050a0f05042c03030f0a02180f040b18041205030c1801091a07060b10141b06040b040c0501020129150c070302120a0c170a1b091a060306 62
    0x101303500f030741c80081c914403001c0c400542d0f480c240b4040d0400307070f510024480c102040c0306004910b0300c81d2801c4000390122070101d540100401d0303000001001050744030045ca40c015007010340741014070340588061344200e0092210485001901609690910003203400302d1103d181000468032000270304140440d9000189045074101b40c46d00058800040081c500e0324150801098581c2084040c3c014001c010f603080d00d0407607000203107200251000020400e2a15180004511646100ca02c4060b1000c09201102142c1e10381c10503007059281c1081c260303030035103403060705580108003035005000d10b403000c1d910404003d02050f007070f810003e10314001102c007550100720021103000d07280a05001d80300700e00c545070107094003d14501c10400d01c0b007506601401c803134001d990308002143e4119080d2084601904a0f00b00945d46020b8990410b002d81c60004c0c0031655141c0c6031508480381d85030340026900c8504040210040e0919450741d11070900160341d52001c0c0070030000302ca500344011002c490500410f1502c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 509618624 1250 509617374 509617421
    0xc061204080708120708040510110412150f2703052b1118010c021503131202100612050d140403080403080c160b0307140702040509060f01050a0f0504 66
    0x15021504d051710030f000010300e040c00303100900205000701d604040c0710000801007039408041d001c0d070324080c910900d00c141a89220703100c02d018042d60340c0082084065010007000013038988ca00000c204254501c6d840c1818030301e000401d0946c04140f422580c3c0c1541f261030615002c0d00c1d140c5181e04069000090510154040000c042580d003e441c0700b6183c1010215101c080254000e541010814840c82c10421031071300c030304056282c07000207015030000303000310715600e035224032400c03480d410310050050a403040003034000201039010402c2080e100101d1414040c0e035a079603003161603c0450442c068840d4004444100459000b101c0c01c190b2440304540180c1490342e40d807600f101640196005031803503500040c072068041c0080c040301390020105410300c01c40b1400d12200100c10701004001e442072110740c10091070036040314825030360443e50041c0140003d00e4884840b40d1100001d4640c402c0550742d18002240514040c0b0450007614010300200e4001443c050401c00900303100f00080c482c000130800c0f031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 509619874 1250 509618624 509618647
    0xc0c100207140f0d02160f182405031608030909060a2c06060a090e040c030206160c092f1210060e01020a0c05090403030608070906080c061204080708 66
    0x3001c0f0800f031840d0180844400501c0041d0030240320190f602c3d111513010380103001c4105503003248002d4440c0c1ca80f1704480050001306603001012031220890504540f0902c2c180504030344092401986c509a007580c00751003a5600d54618806c0038000c20711941c20034842031481e401c01a013602c0c4d10160003000310380c050f03035600c654142c20301032078200740c840c880d2224000f2003100d14207100607001102580e03030358a0550300300001806201d20740281c544c0c3d95030b40404a41809040300c0d13584043e640050100c0e543d00c007103000302300d140741542e070007190780e83c000c54400603a081c041c0c802c49819086c040da05840e422465000030100c2c82480c1d122608151044c064420003810780c004c0c0320300c17076030203003000541d0141040c9010381903000200300141190301c070200c3c0f800020f4201418004440056684010940381d51900358050300c1075410039089072090300c1c1d0015503840c403500148115945d580507520003207042010300c032061182c5a08800241c130f107140410700044d50300004290081c0541e40307003401d21008008 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 509621124 1250 509619874 509619883
    0x30703151503090b011e03081b011109040f0603111207030f0b07110c180a020c010c09140d0b0705070f0615061e0806100201021e030a050c0c10020714 66
    0xc1e101c00103580c8281c44420000c2880075035000d042d5801c90001005682040155640300a010003842040042000c82c02c0ca02201c04290014540e40300070300c075003504000310b030009800441c291441503082c640f80d04091010762142c48181ea40200d00c05d90000840c106105554990288078003240c0305460000003c1043c20001c9040e8620444c01c0b20800c1c00c21110080502c14081c43c05181c45d0401d40060303040303548008100ca40382c81074000004440d43c07048031a10003806081070031000c6500b020400341c3c0159000020000352841c40c2e02d0300c0d100d08000d40c180800b402c1e0340b0b14000c11440898001c207118a001304064070ba0540718507000d0302401d07590341d80c00c400d442078141d400b00c84100182c1c050000e43e40148032000b040c2294840c112040c0c800c0740001b440190060f1a007402041c080241500e014800e4040f00c0601c010742001506003044038403000740c154801c83d13240900038a004041400d002ca03450440c0c031450071010080c08580000300301c0600039030000c401110940d8486c840707142c1c284820321 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 509622374 1250 509621124 509621159
    0x41508060a14071b11041107050a150b01120504020402160501051b0c1902120d050301051f08070315030b0106020f0c0f0a0612020c07080604030e0d0803070315 70
    0x500200c2d0140c1c0c09070310004088400b40c180000c3c054036110140e10b2a00c640c0703554014039040400ba65200300f425002ca070060400140ea0101e200e0005000700038002c0c002043d900440c41103015100055035940d481007194109a003023800526106509000040c00350041d41d005070005200610b0000064050f074441c071490f0380200c0d002d03515042008041c0602802002d081400080320310310302070842d0540c42e01d8800361000200e0010501d09507000b9901d510070b0048400d031503075084680710081020060000d80003445107502c54609841070b80300d40c2c000005c1420000c04152201e41d8030361101d480640207004520500c050303504003a94000701007a0702800c40c1d40204402d070081e000c034648108000c0d0813303000ca081503008030200b0000c0031980d180c514a001c12540c09240c80f0301c01e80f1030158107002a01c01c500c0c650b2803610611341c010600400200300b05010310710945034a40c0800001e000d02c03c16580700080035189240c148002810280280c04c040c0d000c0d074040d44c005800781d40351600303291002d103140e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 509623624 1250 509622374 509622391
    0x30d0905010b0a0807030b0105011d0409052d0c03030a050304030f050c0a0803010801050a0506030723040207030e0102240114060c07030605012c041b0f060e01141804150806 76
    0x8810021f000d849051a409000c0a2a110601c40c05082501c40094803407251103008582d00d00821701444024051841d0074005c100d03c0c851003030341d000f5941b0400302c404c00540d14140114000d50744140740000480d00700310401e0b06c0b61401d5039501d0f1026184a0700d65900d81d01400802c0007010111801030190004d100e104a08080d1a17505241c0138508681d0f0040c0b465000e82d1600741404459580018060105c4204100150843c05800b0810710b40a9403207403001e42240c001f0540c8810550401d9060750310071000e90071110004a4a00c0ba088c1c1280540c5070307002c1c08441c0714018082c1180601c005400d180000d400d040c42c03e040355900514020f104ea1060f01c050390348100504c0303443c05203c1d01e043d0441c1040540803a50139500d01a858062025100400200d5010300e000f45054241030000010800c080d546480650786580190807003030071441540c001041e1140d503402c100424400d482c0d070590350a10b0400b054032480103100003070040f0314451504210140300000c515000f0441c1901c01c0c800d1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 509624874 1250 509623624 509623633
    0x1801080a12021f02090103060e010306020304021f050a0f0507020d120f03090201090e061f270806190f02040f03020414060117041a010b0c0601050f03030d0905010b0a08 74
    0xd8100840c001c01030101c04800c64100c1d0110403c81042405040200aa5a100140c0e5034000c0d41c016001041c41b43c0c802204141e0010000080c400d0941c003641c880c50095501d00c040034034002000c41c0c901c9107000325001040091202c11036451240300300844031011810329501e420003980014042000c0f620013101c17502166583c405c10305074042c0c0d09400310481b40c10240a115116070002e8031507207a5010b5022444140d0000554580c2d40e0711800503d00d80c07a958400e40394540005c0184020b01307121703c500660401e0180c0e0803544107207214244c04c440b14803010b8a60313074445e8450f042d10a80e0a5038a03000b42c41c1c84404401100c81d1b0f0380300400042c44940b10309080c5614500c1170009a41c015135092000784810320800401d641c201040c071950b203003003c030f160003190703200d16180072500341c28403201a18800600000c540d108569000b0082508040200c8400740e81c3d03601000000c0381d03121f40b281c0e00754002703010140c90048e058215400c502e110300f0003ca040103481c0080340c185d8519070b00400440d0702 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 509626124 1250 509624874 509624893
    0xb030406023709080a080c1c08070f0507110d0215030109090309081c0807020f100506121b04020a0908060702031c020a02060606090f15090a0f030209070e180108 71
    0x80740b2100740c8014205091481d034080c501074010352100c9461001610b00d00d40010002149042480400081d6003014446030412001040061102000300c5944004c01c51405681520a018100b990742e241c0d0f00030300304080303028944207011080e00d0b907403000c036002080560450100f40000c406036018107447c481c005204403960600504c1d55556907c540490b8001086d00c0b00700490881c8000340c0039869003414070140d266848200d1600201c3c3c04c0003145405405c90403500001d640e00003a00500c011906c503401100300b1014a5243d0608011040f103140c052204807000713040c5500070700410190360428400f015660381850b401d0403412180007005070000103400c2070788008100040c1c40240340c80400c504000358040040d40d0340002070200e81c41204080780c1c0e003900f5641c8075603d14030f149000c1c04c0e501d044000f0b5242d4240c160050503490740306402217800410030071803100c0f045040701d40062081c040e0780c88031401615540c490253c006e411100f41c1c8500510700242081d00da0090a0360301c001d003107940 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 509627374 1250 509626124 509626207
    0x20d050408090a120503090108090a08040f14010f0f030f150e0a0510060206070e150a080919051908040302032e050705030a050a0b120708010c0804020108010b03040602 74
    0x900e908680641c1081c0d1903144e011480000075105000030070309003003600351a0380c52031600e4041d4000c0001c19030341e000a000300c7d03007080e4148040125480300415051854108006590312071a980d4590000350130de052420285100f50440e10b42040c0130180050080c0c5015000034080c240c40c0c00201e84400c415051105100a500c030b032a521031120010219407905108000351035540c06408030041040441c01111950380b00082e0f00c00c00900c0c0300c2e2907035603044004005020180122648015070240ea41601901e184c4000c0d00452940d104002c0e18400c4003075400301d0f0070440600300513a08001c1c00d01000c80185c504208020400102d601840d020900000041480400500054075218208400d01c00c000c1c1c0c1010039a9007003074410202191558902d42020002c04e108110507a0060302030001440759103020500c00c05647c034000081c13202c44907042c2c058038200400d4500030300086000380108950040380b000395401c18440c038005813409041c0422a0710810f15011640070b0b4001c002408000300 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 509628624 1250 509627374 509627389
    0x1d04020d0e0c0906270c130602060907150207060c0c0803070f0b011a04060c0203151e09010615111507110d11060a2318070905042301020d05040809 65
    0x4404460700300041968140360b01e85e410b0301441d2400024541d0012480b003c83c0a0b06650502c0d001c40560076500d907844000039912202a0303410403690080c2c00c000304120304e101c041450f1486094004003030962a001d003c940c0d19040140c10b88401c0c0201c5000310f00790005100900364a40242d4a001002c896800e20109002c010b03072150b070044540581440000e0328240a6030100c4031107081c184a070780b499001007401c015a50024071400e00c0c40d00c04006038691468511601d080900e1000401c594510092500701d880390f0180500007000000c1d9607510b144550201f45c6004d0101d001d0340c0b004c561140a030314911000f9220351000c240d00c5554002c2c003000070000e2079004400d40c80c100d51040c80380000c2e80e482c0c01000d00551161610744c000c0d00c3c2c0c0c0e510500b01182e484074614071500014a414440c213000201c210504030381d03901031150001440340250181900032074119421014440075401008140c110b0502e070f40c19195028010f0803905c2500744030b50b5115500031400165241920000c02c6a00c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 509629874 1250 509628624 509628631
    0xf030e0715020c060c0d14181c02040f1d070302150307090f0e06330c0f0a141908092e030e12070309090b06040314030a020c0609011d04020d0e0c09 65
    0x43c4e0010f00100d0030760000103801621503a000d27902c8003018455950224030000d0141c5020790814107110300d0910101043c1d00c08802d4003044101016400444042c05444940500c0040d511205d0b80e00010f8902007000d0045400000600f4840da9142d543d1f1211203800384540d002e408100f0740a03041080c14204402503100080c00854203828040041000b1501c105c450695480c07450b00200d40c0800c1d03040108141010543c440049403a6030006140100b1a0707070030880251501d001d8880b045c00340d2091100644040c992186201e401c0404030802d0240e8040811510001200ea058084540611a03250540950070b80e943c00b007040070000325035514004000f0b103a2200c0100c10405280800d601411500541c1c01d006404180d207040c1c60b0010b14140a0f03500040c00c603419510104000c80c000100031f054440c800e40136648610700d1641040400d01940c480c0780d000c80d9580303140e55030108800c02d10040700b510040c03005040203903244644045a152001509007540200b0b0000c1d41490980c400c10351 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 509631124 1250 509629874 509629907
    0xb310302030d0305010b0a1416050a0219050102030a0c03030213080303043e030a020405010b040f050303030705030604050604060819150605060708030a14040c060f030e0715020c060c0d 81
    0x7031940341512a1081c3d00c00c7d42c0050041050230107015120740c0026044856071411400b24804100e00d60500c542c4502100c1403ca215841d050007880e10000030380310010072200142c01450401e0503031036040e075801c403d80c02c0c00c03410158204184141c3c0d8101100000103080c00703000860f101d29241c54400a82c100030b20041044034070806080c20b8408100c1c2c1c00c440da0b004000842c0324004400d8020034585115500025885030400001285405481c070103001158108502020019a210145500e030302c0f082d01d084000550070400214581404c3d0005030708020007070400501d4a0383c43c1105410040311070016200b03400200501814000075628903032100c5880141044254a01000244107100b64807009250403408400a5266903a992140c00400c1603607800709094902480e0a5090b030b17100780201c00202c3d1002c1a4100b01d98405d1280c40c5000ba040c13402014140e045c1941024282c448501c0c1314114841c03600d40301180e488480107005c3c1c0e896500c1c002c010700340720390030040c1486840c01e04080 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 509632374 1250 509631124 509631131
    0x30601180f1a04090203090f100605090f06031c180515090d0515010303050702090106050313080d06091e0e191509060e06060f06130b310302030d03 65
    0x10070412140001012a092401050080407101641016030b00459100001551001c020031100c0100880c084c40b18031240401e903828038460500203421120f5034000c0c2600b050b00c200000d0071600c4010170540c3c20030002022a848c0071451302d210314844003424204d1002070b4100c159022490b510a100402400e021102c12040249a00100d0104d0195524040c4180c040114440900609014241407040990b8520300e0a40e12401d024149901c0b050040380a4003c0400000c2c1c0c15101d007060f20b018404200d400700500010740c07035400141d0003941c44412015540c4400054480262081103030360304886400010702500a00102c0c100c600e1102c1c152415006512007442d5080000c01d039040607980300f6408038100280d8140e250091220340001445140760090b40110520f000944a1003114120b61035002a40f0040034440b15000d0684a031485100744442404000d000c03002420000c00e62011809e408044111a405c010040d07010075145e45100310014003e5081c00c0c004030010b0100c609050 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 509633624 1250 509632374 509632379
    0x9030312021c05061f0c021509010509040c030626060108010c0f1206170105040b010b0405010e010e0d0c12051c080609040201021006080309191a1605011103060118 72
    0x10080411100c486a1066030b030b4000100b0075a50182060105032109403440424624400c0292164511b184246e00c500c0c01030200807032000f0040d0403564512010303034605084c60041024440600010106c01040c140c541c84049003a07030b02c050000100c840c50900230203060700d40344140d900380712040e001030001c2c1e410259580d000c4c3d900104a01280100ca107000c1c0315800225020390002c0c00075410690407801085d6a01d00280030540205014901803406104942d0342c40f402602c1e988100d10580d400f0903552103080081d0340c0a450f4034500301502600c800c004d00ca5aaa074400082400e400003202500d64400b5101800810032415210041e2104a010f4040200314080c0c00404011f129910849400000a0459209120707440b0510b50ba00070612085490b0900b00e83c0300e03003004400702c0c000c004003581321080c5400d01c1400d10484a8040c8030b461018103d4444444030752102c1c4400d00a007090780c003503d000890034841c94038040c222002e03580d10307400d00030001004036409280c280e5030104a20000e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 509634874 1250 509633624 509633647
    0x1d0304060207270204030b15030715180b040305030403030f0801060e062a060105010f050f030109150f060206071b0507140d1a060a0602060f0c0d0216030903031202 72
    0x7010306803110041c1c20342c080303207843e0b01d818003041d00c0e01600054035002190000410507818100c5000301c407004001800017500710706055440901d8400d481500016254038045180603221100440ba041c2c0c0c1414403240e110b01800d4080d5009600449071070780001802c0003850352144039071130309800501d0951419407611600070540f21405a0080c0305810000c0e0241a080805440c460000980c80300420245420300c00c0070b490f804e0900c00e26010402d10620300c030010780300b4000ca4a480803200c04803815039090658420041102c0c940089080c2e02004004c6200c00c103480390f88000b0420340c1d000f4112841d20210040488514050110100c011040c251000900c0840c04109407101d01e4508041040300b41d000810f54420280c0c090004010100c801740070b0002404040c0c812241594101040c0b48d4500c401c13aa5050221003014884005901107040c0200c03020003007a108115404c05414140b00489460180303a18135012808502456420010582c01c1015024407100c2d41c0c10441c00c20b03103403075036 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 509636124 1250 509634874 509634883
    0x40c110307021e04090609060c171f1701020315060c0312072001090203060610050307030504021302040602030c010609231338060a15020a151d03040602 67
    0x40203200c3e401c1c0c5141c590380c40c2c0a01030002c3d40484018400e10008803d81859401003a468600750b8042d403c041024100c00d0040403021040c0e09191103410ac0f40d03544540c00944041225450110307500c0300440000c121642004c03092a01d07074402c00050307403402c06200c480e454a0380da1800078001c1906010000d52648040296a004640119541c016079101d8004907003e40c120303684207141509581c9007d0715680d055000c21a968400c2d03080303c0c80c0d51601c03020001502099800d10740050b6040001500c1c1c180f01c1e400c104e40003880601610145050482003109a800c40c3e081040164408103101ca40a41d01b4041c80e002420398441c2000b00142441000f954402608a1080b104900b03c2c042001d07200580c8401031003e03000722610f212a408201010042c86101c2c110303806100308201c07907080901802d80141e00a94000340b1207014240b9003841c0e0040c40c0b11804140040d8010071044001140241c2d14005684203541000101044d5546c81440c80c41c40c644a500c003158814401442010b03000103 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 509637374 1250 509636124 509636137
    0x20708150601230c010608011a06070f1e0f020108180607053403120204150c0302100c080925060302250c23090402040e07080f070302040c1103 63
    0x60042022a84204110340300c8814121600700d0f060f00045030031803042c06510240541d0020302c001e01c50016160000108401c00c1c40020741d0043d8204008000583c245100300030700e074031401491000400e00b56840c1c6001841c10403d840340c0201c285800d0856034403034000d40d400400103d04180e61942003580c50340d00c40000f4036200610000240640710080c80318120044061013000d01c2d042005c82c490340c220102c00308d0408501007038003c041059100d12034020303101642c6003c542d503242ca200c901400c40c0c1c02203101c041074042d03001303180281c040b0340b03847d0080d00c060301d0381601d07205003e0400104661800c00b810301c1d4001e540000541078103100134484456411500c2501d070168440700c024242160740d03042d07846441d50400901000e041000100c0b020708048400d400e400d100b40c105461011811449401d0300d0560001c248070000b00185071941c00340e50340d501414112003c454841c0c5c0e00070315140080380d92803030036070158104004628160188202c1000700e4039080200310343d2070501d6a6030b4014503 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 509638624 1250 509637374 509637377
    0x606170a0f0b07090302220e06070c02090604060504050f01060207120b0a0507090b0414090c04180f0608100203220201020703120c06060b03090706030203011503090809061207020708150601 83
    0x60b0041401c15119200700e00107903800903d541e0610003018180941815400120280c1c0f60130607a405014010120b03403644280781a031161700c4681c401c0c2e4204000e4100082ca681d503c00e58520000c90980c54510a461050f6041e00080c0c49a504204010b40b07000369580c022a0140707100c0309402c001444004610744c11603c05030002c14651036100094030b0660690b00822002000440c0010b81003550100051007a501641c4c00e121a403513503010317403880e8400d07401780e00d540901002905e0f0045183d0f92059110301c2074001c0020741a03443c0c0c404981007a440d120200c0c89039401000b80406265820a040c554003564003841d00d482906500103921440c45101c0501100c007082d6002d50b020380604000010144e0000d02000016201c0074000d10582003903032480c1d000d118861300440c2480c001d10840c0d045e03400003402a4090109014210b000d4651140101c800c82c0c6d0511808199455510180c04480c040720003078103041c03401c03100c0249042c9144d0701c20042517018002d017030700340d19901c40c185401040a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 509639874 1250 509638624 509638643
    0x60327121116181d071a070f080a09080115090f06080d140f030a0c0e01090f0b09010309050a06021c0902010c03050a0507050a0b09010f060509150d0f0606170a0f 71
    0x80340c42d980081140c4920b604041e443c1d0b03a0180f02d603950100b0032201b03030b800c2c10001140c0c05000d480145a0383c0504000288000030480822003c280700e00d0141c49421140e28202c0321a82d120081d817030a4a8180c1d080103860a40f400050242102a004440c5d08a40c41c00080100901d0665150303640d043c6900c4000500050b85044c80121004108840c121000c00084503030b02e05001d003c41000702041060440010f618400d8640103600c00e08070307a000caa1030409102c14090502c0c2d07008443e603102c0c001d8641450766403c20440080c0c824030503900911700442006031210700c4910000102000c000120100741c1c542102000144e030004444483d043c1c040c0b92440d141c41e10301801390f801e407194400c00340051050302071501c204060084068440e00b00d140c020b019400703244690b04161540e81c05085d44c008521400140401c0385070310000e9a0120083c83c50788071400540b621580036000f41010707078074140c9540050220041000700001c001481c0030007000156000c4e254840607114006004140418 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 509641124 1250 509639874 509639909
    0x11040e0712090c03140c300601090b03010b010f0203120601090806040605041e020f060a1701060306150c08120408040503030d0902040c110601060327121116 69
    0x10608140d11801c00e0a00300308842182c0d400e01d0800c502d11480210350201c1c0303400e44102c140c40f002c2030f0101c880c68090841c80c04820348250707480704c1140d8544d00800e00398650012034080325007005580e00a2400500000d030407010801414207440da515851410b114824400001882d4000100e03660482003804000b200c0d122180102d030070030348540c0302003964400c501c10300082c407881c1c2d8403141c0203521854040701603003014804601c4000f40104081d6100d0329140001d102070419500401e000b03105850310700b44080d002840c8074030260007a0041800296105818088544020381e9124040540d050034101c69229a481d581c851041c40c003046013a00c881e83c042010007602a003914090500102600d454540e00c85036140100500c000030380c85181008140c5070440d002d4082800b1660103100a1700f26682040803d80162101d0f04120025007050101c0f91201c03140d0440c80031040307100e03161203e21004d4910004104460030b000c81009074220808804415a009984504580603030302d62203050359 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 509642374 1250 509641124 509641127
    0xa0c062418090807050d0207090b030304140d0602031303080f01240306030c08010209041d0c09070207030b040803070305070f080a1508012f03010b271807090911040e07 74
    0x14906000503c03038a0040790390130400c080031908040302c074002c7d4200d80b04035580d044450141d9034400765840c1c1540040000788001030004604a40208000e0f00e0501c91600981c2c03484101c1c0e104a400c6191201d65410050415601c502d016800000300c60020f00c65505100d105042480460400b0900c0080710b00303404c07299802a0010030085070030003008014660744800e524082e600816046200d00c0c0392003000d91621195001f0b01045036078010050030030400c02800e1006010028104000f5449004000400681e00c005001d101d41d00c105000c0c1d0320307420042409425990041c0c0300e03000707101524000300c0603a640300c24040c0c1d20804000c0040b588803903e800e080d00058181e003118681e5400c02410905258a12010000c26443e1605a000c046010700090559001c00e0140c0c3d26002c20400c8480501c040c0700c0d2080c02000d4400d445500300d00814000a200e82c2d028030300f01444d003000b00c000c1050303598022004400400400100340a0402c0000d1500d40e07604c82c50007852018080000860340c000d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 509643624 1250 509642374 509642381
    0x15040b100b1c0c200d0306091116080d0c02030a0e040531061d15070906080a140403020c01080a0e0a060c051e0c06071d040c140a0c062418 61
    0x19800c0042160344605103503001c94954106140300c0002c80e05046000078500464030600c040c060742c07084141c0c02c102540c402c500320035100703a2b0b00342c82451003030000100f03a1003244207603490000150015030342c6007143c01000c2c1031403918203040344c8580c1c90101045560081d80da88008100b20701c141c10b407164175011009500300300e10300d04003910242c5410082d620b605500724030a42c00d800304000b107521401d12600000300c026408c90740100000c406040410440e0b001d11095a00803000d01c401141803580103501005020f1f0444040c4c0c0181d1016812143e2540c0201195400c94120031050011894103a8055900c100c880401000742e80d0f90354910464a02c10000c1c0c4407034150040d4404056524101c1040043d04200c080c0b541c40d010310400300301f085004000718031041034030740d1302d4070083d0800004001c01000195508014054034400e0b12264400ba00300600c0080c1d0b80c3d880c1c1c040140100d0829408807060170000c44422a50208140c03038031943c030b1a0301022a03042e030744150088107145a442014 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 509644874 1250 509643624 509643647
    0x902011809051807060504122d0606080102031005090604320106230c011e091502090619110706031d280515040b100b1c0c 54
    0x10342408000400c0d49101c90b0096030091140b040c150500100540f82a5114081d920419022500801040050241da50696400c6c14011030701d1042107001582444000e0f550800c00440d109540704200c0108003113407142c1d0307002d000320100840c04d500e4203074810701100d5500e00035140b0800b00d00001404030307a195080011512143c0c3c400c40b419010010311303a0f40317004003e03141c040309404040010418074032590b0340101c1e11440c24003040c0030400008050304540c2c007003119031403155203035102441d0340940c410b2045041240c8080000d64100c0609222500c04615403035035002c1c900400400d11507076902000d60f10402b03c00600e030312024801e0320060b20b07150f0100685900c58001c280340051001e4240d030250090210b82d0311140c110f200300c10303100340e15513807001d6101d0301300f141119038043e241e40c240121243c0244580e04444400d20407410303c2c0d007080c404841c00c40340d1080c074070100006440d41d590800c0003803081140c600d04007051711290041c000595003965940f0b950311a1002d49891080d080300c40c2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 509646124 1250 509644874 509644907
    0x40902040b04030215133503040510030b030c06090a0305060c0307200709020a2001020403050114100506130b030f0108190b0c03060109180c081b070303090201 70
    0x1922980c6080d00750864000d80b10580c81003520300b010140c02d0403d6411514003200400f501d050301402c12102c3d043d44001101041d40300038142071191075940e1400001e0364200000d500a54482c0d1a10701008000060020144101803e02880c03056a80b400102d2001000701121055140c00417580410608481e5600c098010f2244209201141d140000198002d0341540c0d143c1081852200707111080407402101e04050740c0c0401700800c110071450380078040040b401e10f050905c502c0e603110310b1403c1072403000c450002030354002810400c1120074404e0110001c0c0c03460840b24a481d0540300c200e2201014410075001d480c0000301c1c0710504510a000201822040004a49038104041e40c800c0d200d03824061119a1b1066603100e0801100d40b00e04000045c0c2e20500464545d522141a000142c00280900341880a004c1004c1120428043c025103001c5120000285203800108020591070300070b00541d925200441c40c09008280030802c4036206038060030040707103030381181c40104e9000f20b05941d00355 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 509647374 1250 509646124 509646127
    0x5041703010e0105090c071a1f06111c0c060f020702040606030b040e030309101805060103140606100c0209060f15091f0c0b0910020a110613050601120602040902 71
    0x14a900801d00d420f41a124141c07100d22040c0c3d500d81d084600d03803180b20405008001d0009100320083c8890010580c0029520502ca42c26500209070743d0815038143c0012012400480040c4241c1404001c50305600c0f580446031030b40c03003050040180c5102610407003e020704e030302c584041c03c0290490701104c0c0d90f954040c004114455580300018000c001100e0071a102c1d5041a0203184116400820380e405199010b02410310004030111000041c40503030b442070381003004480ca410206105100da98000c5024007581d07250007407020356103424150010022403190002c0c681d0382043c95400071190f00150360545000107152140301c00103002c6000c103080c103984001c402c01c803000060701e500043c0ca810741043c2c41582206a81c884440002d00b200c02d03071075000440b0100c00c1804607212005990304074640c101540c030b0005805150800342c0c0c0c015000e42000c907803020241000d080d401c201a47c1d01000c080360f410381c43d031810764070140c444006100d01d00312001c008214009021840d412100100080c17402107 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 509648624 1250 509647374 509647379
    0x170a06030b0c07060b010c08040b09130c020d2304050904060209041508010b1e090403110a05150603030c06010b180303190320040909030c0204021206030d02011e0504170301 76
    0x307810340c3c0d01000c801c071519030400c215078905500801c07002031515800854a030401341000c4680c42540c115800d159030045200130642201001c40c86607851640312940a04940003a02202602100c02d051540e500d44810b00c0803540d61100700300644d015140200c48204180d2181c1c100300c0040e005a040b90f55206103008500740002c0d110384045021114010024041102514200300d045410180600031181c04840313400071902c1c000c00c01c0d0340e000b440790403c024805040301c044ca1800402c4003040301c069100e80b80c0c8140740c45004602d40d80c4110128003e42c60201c0e401003864840d0030601c10a40c1c10076001ca2071800c1d8101c40740c0d009012000c058200c81e218080e6500c1c0c850300144075128040460700c1d1070541604102408001c541030305410031240c0c0303010700e07201a8100801d000c0e0000e504008245504070016a5540003d0800c2150340032440746a081100400d420b10000705400c0d0156031500102450b450721301104d070200d46035007403000a010ba4480c2850020520000c001400e02240000007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 509649874 1250 509648624 509648641
    0xe0402040b0a091a0909150c070f080a090f0b1c050403140703021f02030103030c1103150a0905010606020309030a1113053d18060905010b0c0c0d03170a06030b 70
    0x20300da403c000c221078841c82c1e40c46004c20280c6400c0c03085003440319400d0303802c0008c445402800040c00c840303105070f40c009484101c0342c40b02803083e000400720000203111103100700701040c51124114058450955410310788400300000d03031980032504060f03200c890b88070f90014003454010b500343d4906040841302640c2d20b060350303d4002e480300052096070503c100d007082d2591240940e07100740c07410303240e00d0b40b074298107820b09444214002c069080e4040d4140308400085003444d00d090540340c01104001c10105803400c003464500c0c20758100350002400c5503c20f000c21520b581d000210341c1121600f0450301d981400603823000c905146010407e01e001e841c14107050207826942d80b0100c100050940c4d0b850b07108d0b80c2c1114480d82e8034011500314160107840d85042404012284a00030a00b4015a0f0f80020110380d0f81150900380d60099012022030b207804201440b041c082400580388000c0102c4070030030007880542e0007a01e1200c3c0200c00f1204a00c1003000070b1000005136100601541e00407803030704d8070751074160075 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 509651124 1250 509649874 509649911
    0x9050102042601090c1e260c090415020c0102210702060f190509160e010602161508040201261504022b0f02040e0402090c040e0402040b0a09 62
    0x907010b2a1990016001508210601c00e1440465011103c0391a00d4502407812041c1803048517822840c3d01c0620700001c140b480050300001c811005138288504c1e500c41c48403c0e0070801101100da0156558004100015592350030110600c05a0100182c4590308148440e00a01a805019032819046070240c0a21100e80110a1103180f10754201c0d48507943d240c003e807205a509071100c5d024480c0e86102c402039458a034000c1544840c1580441d404100c494254424001456200c1c820380e884240c01880310503414014a80720603651111204030501d0b20fa000030300d001d4111080b4040101e041c001c10210780c4200141c00180035074010610240104810303454500e0070a44041481e000c40d4490b070102800c03c0d0080c0c41182d40b140e10705900c000c00200e0500c4003615110202c1102603078908d224082c00005201900c05401000054440d9161034814480400303400b410b400c00d596000d00081001301d10550b485a0702c03590648000c2103100001001c16014945500101900c504001c40300d40034203480301 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 509652374 1250 509651124 509651159
    0x9012102131d10080c0625060603110607031e021f0609050703091527050609010c03060e040609021f17060f030a1424090106061b030c05010905010204 66
    0x600c90b04544440150403540780da603108161164109110a000d14a8214082c124a020681c0084010920f00c5000ca901c017080240c01c403800c503a83c1c0c0b024818420a03010b40410750b8400c0c0d813200e01e84001c5460146c1501c421144d040864843d4602d00040c143c4241702e840200f60f03150010902004c50501030002800349c5000c1c02e1181881c100024031414071a0050741026604442401c2c2400c1405044002400d00842440c00c000a0304105480794003000c41103400e41809036000c0e00c000c0c01c1040e8401d0035101003138031460030541015018424001c001d200150001c3d130120700010380000e144040b8603003441c00807011014804020324105038541002c003944500c0154410b401c60396071150308020f0359240c0703a0545070705507020341c1403000000c49040d94116441041400c8901074080c5402040b04802040d00c5008072588a01c24000e4500c000d0003490064025410090a40e8085141000c1000e260510103000c008000301440103210081d446800190341180082d56596200c107074004c1c9606590 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 509653624 1250 509652374 509652419
    0xf0303030e1501030602030709081002071b1a0a02010f061403010c14041505070206070309051203041a03060d020d0602030621061b0c0a0b100b0901210213 68
    0x1c055012a0901080c40e0b50345a10400711012980d007991510030080d00010000000c0c04241c04000c03c0c0510100603907003542d6001200540d03540d5032440d090903904089510144400d460201c18001c81d0703480450380c0c0050066401d06da0715004417076400c03405868444a0303d5802c600d0000d010459004141c00c0c140319080940003031140b03001d02d000031600e903050100000000001440700b0300c100c840ca40020111030b03200380f405d1030600101da0001441944440011400308004900070800740c2041440c4d80c200c0d88150019604113031611044212103680e0300780c0d1450f000b600000044071580c4011000d80e41940103402603080d0469450a00001d40c019600b240c82407003548440a83c50141481d2102ca40340c25001504084c0c444040e80c00700e40c85100c0345149060010b100e4000f080b5010002d02c0303a854011046d1920505285170080d400c2491900045a009001c00c88021340c5d90f08010104202030541881044020300481e03000000c0c05143d11038000c90078403c0b800110284451841100c000e002d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 509654874 1250 509653624 509653631
    0x105180c06161217251805010509060904023c0703030b06040b0d0609240506070317040506040303050c1206010c06020417060a060509010303020a0b0402030c0a0e25120f060e010f030303 81
    0x1081c141c0303104000c0c2d91481d400d40c006c0c440c207100740d51040c0003601000d4800b40226080c220030034000340598120702c1030301c2600e01805003d42203a00411052220715040410b80f07940b00d41300040f200589216004003c0e040c1034a0f0200307000a45c03140030440f0000c0c285400b03d50349600301000b02401404003403246840b50b0f405c140f01d91009144c2c0c5124003400d6584041d10400c0145000148040b6410082099040c0007481410800030080c030003a80b485148a4000b80200d40303041d250180c105c8001804680c26202c050200210960908524076040380003403c009114954601d0407401a00c100c0e045400184200d80c824200080000707003c0d4007580c080c032002d01415407194284103000380e0074480a03006920030145403021850f880b119540003030019054441c4480076101090341101681d000a40040c0d95600704514404001703403403000403030200c200300d0500040c00401003c01e035003941341c40c0704199640518507043c00294800d400506044504004560b541d003012042d06100380701c00e801207400c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 509656124 1250 509654874 509654941
    0x90503180f0a210606060503010e07031808070f15150815070f020c04060f17010e0c01141b0610060503010b070816050105180c06161217 60
    0x203040c40d010200800c080e0603800c0303840c039002c40035000110802c0d481d543c20402e100000049a0301e4002c00703001c2e02c515140d01da542c0d4940741400f410010014201c1080515010101d408817100c080d070a000c40d40c22504094031015281003811840c048020300906400c25007104c2c2c14850340d280c114512003c201c2c007a00b1481307640d603541035440303c920b8501c2400040404001615050117a0b8480340312032004e2048803103000ba09408030301200c40035000403030200e0181c1c4040141140544003140ca05101ca8024091441c40e80407256580000340d02041c1030284041030301041d000c1c07103c191001c0402403422803421000d5021019100c003400d885102d01301c0ba54400104401c0d0045088904130f41525038094a440300e00d85500d03445820085c1c543c50541005600f41001c2402402887d010349220782c110960b10802c0c60f0042d150881481c4e096026202c140011000d5840031034012541641080c41001650b00700c1c80101e8510b0f8515440000e2720310f40d8014020301003400c940884152144084112201d03c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 509657374 1250 509656124 509656129
    0x9020c24071d2115010b030109050108011b210203010b07030f091a070201050d05091f090809060c01020c06040317100b07032d020a0c0f05090f060a030609050318 71
    0x110840d090035040480210341440245000f4658990000c030314055402109004c000007165060170303030000c400b80c00040300500603400c1621800380101500c1000f0488005441004403650761164249414030412440d0644000c2d501d80e00c645103111001811562584c4603103800c1c24a03005101c040d03001520059208151a000e60005000d61340e209048030141580b03400003113995440160124100310b424000c5100000306800303118090050a400351110301d909800740b0000281c1707010200840c0b82084031382d00c082510017080340c1e01c0f80f1043c0c440725651314002d091640648200d40541c4107501c200307810081415800b80320806443c6c000142044192111082c143c50080c081c01a58541801003002d00006070003111045841c0c1640b160b0f100918604080c0541c03088852070700040540c0104192008002c1ca03810000c0180c244e0130385621015081c0008101251340040040160102b4800420306595448921900860744841c0500c102d103803519010341c40390001407044401401141e0302c15840d2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 509658624 1250 509657374 509657417
    0x1210527210c03121f140f01030c1d04090209160813021c021f050c06010b0a0c02120f0703080d05131518020a030303050f1006050409020c2407 63
    0x1441d01d0b01c0214103000c0d600001c00408800904420310044940c180c440003109550302c000000c4c001101040c2254160905012000540c0c01101d8101480c0c00800c240950b044810034072044240c507480802d6503081000b250040c00d0282000c0c1d403205410080001031240da01074082c40340c1f51661205026180c041101c1180340703185000951144510b201320041c0e000c040301983c42280001d01c074800c0711040390041800003070000900340024100086840d8200000c004182c014200800700900d8201440401000c8000d1094000e00c141e24003018900f80010400c400c04d01c100305c070010703030315a80c0d606c1c90b050903168401c3c2c9030b820b4440c6c2004001049070604015200e00c264005208441004a080d60366001b403102400001c410880d11a10303c015880746a441c1c0c01451003a2000245420700b2800f242011000601004404413003510600141d61b100c4c00340c2c1c00325101d00c0c402603201e24900c50b1041c10b199030300c28001114400424074540c1603602c801d011740550700f1a254000e030510381501c250f01380d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 509659874 1250 509658624 509658637
    0x30706020a0f0e0a050405270f011505030607081317030105010e0103050402010e190b0f090f030d32160b0703150e071407050604030e0121052721 64
    0x81c81074020401414990013141d031001c1c0da40055815030140d9040a8442c1240150340e00956100c0c1c0070307800c0d506d1000d218201c2f0350001d0154600e0124a000b000175a5940f0003000f00003040300c1c3d040400c0c1c4032016100d171026030030340c030919500b66081d550304c038241950824030800f4002045040003114075400ba2040a0246406a5a801c40e400288007800001c1e41421540c150a107242080000d00d440410050040d012030200307101d40d5210610108044492150952842600140c0c10402e4890308450491040c3c2100901402c0d00105020251640b129682c140c1d08000000581e000380010309901c0301c100c043c800d81051503070b41c50b440001c40407a40403204410904590070000d000303544140409035800007141c60722050314905a0110561a082280119490b41c071076006d11081540210302c2c400c80104c20700e0108410045103008000e000e01d203420080c0000c0d550408a14011030044080c144402c880c00685403400c024203c40e559840d1060100c00120000031648400000d40404c8414 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 509661124 1250 509659874 509659879
    0x60c0507151e090801060603060905090c01091406090d050d110c0a170a1e0c0603090206070308060f0907021b0402040f031403040f0b09010201050f040507140111030706020a0f0e 78
    0x8810450a000c80c0b4030900e0500c181050000c164000070305000240594400360515540105800780780003001804d856014026802a410070480c00310582d0f4800070b03480448105810400f180c125000100740940300f00700b07400b42c0080d4889014006c0c8000040d1340d0b8004d646940e5370008154850380c40a80f03c0501194480d803041c00c9810030071814800a400200d90440a820f480e801946546d800b41c908080c00d100c00f400b0a00b0501c0301c1d05100458640000810017400c00780044540c03540021030310b01c0742c2c0c48000d040c00646400324071103072503062014624400141211f481c1c1c0c1062400696141c0180701c6c089910207035a0703441b000a0815000b550300f140d01c2452217070300c00c500310b503074041e500581c0080000b001d01c0144030004512012405d2070b00103000300500c4036034401d240400203003940d20041900096075005002c4c0700001c1d00008945049480d004604a801e41440300125441045480c00400512003c6401d0703007401082e500500440c0d030b071612142e071883c004403000e071800b0024059599 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 509662374 1250 509661124 509661137
    0x307050a0b07020102101805070b040503070e0a021b0c0a170307020409050313140103060b030621010e0604060605090601180306021b0f0f12070c03021513060c050715 73
    0x840754841e00094040380384140159100820550454000c403044844c1c0d0700c082e4044913018401b800340a110040103401d4480c107240c03030a810f05010a9843d8010f1150f182d6410001d00000e0080c65264141c840303600200607004500b02205a51995401440b03500900c640e081c0040040c15030705003c003801c2c0b10341c1e004018504001c0c641c1c00b0080204a005001d5580307020810801c151090300a0b00d0700050040152082c19001209000400312400e5400a0040b048100b041c0990b41c0d403800144641f8411404024006100c1c3d40d60300f5016144212440065100e50070070700c01081301c1504540203444041e5012005c3e42d4404004441921454150418007001da2000b400811459001030103010004008810790b465045180307490900480e0020160781c00c6243d071325050800500030100c1280c80000c00c01d06008040e214000c4030502e500c4024801c0079503807940c42c1c1888881c3c0503640142c0c6210013803002103582e0390300036180541e2820200d90600842c0808100f4803401c400c07401514615036101c4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 509663624 1250 509662374 509662379
    0x4030f0b090c09010b0a12050613090c0f06030504050c01020304061709160e0f0a0b1518222007061a060a03021206031212071b03110c0307050a 63
    0x50034140141500351580100d038a4001c003500c500041a00030a0101c00305170f85d8240e04800101074800300f260030840c203030410041c1700c180d039210b4000180323040b9401d400045140d2545060f03080070503d940808600000030300001403480c0c01d540214440c41c005c10654043d000d050740120380342c0c03041c1d00034000400c081c09c0181d520381c0c0740a9aa141c0c03000c00030341103489500c08240c0c1280c02424640c003030740111068000700003010300c148560640001070320000340038180c1c440e40020f0001203800001e50303511102084a6440d1700d00c103946584100c101500142d102524094494a01103035492480c0740141800100b17030312600010704403000a40d440c00f4460400a0035070314038001d4020142c0d1281c840d01c0c0010058101d41d984d034001e00a0040c0e03900d005a64400302d04040711002401400c01d4403c1e080141c0c12000c8965a00c2111070240000c6640161569880b50668142150911280e80903800f14008410103402c080403c1d40c0044d0082251100c68100040568a111a02400f500300400d28002c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 509664874 1250 509663624 509663633
    0xe06010f0f120b2710240b04051203191112071e02041e02131202031b060706060602030901080a09211101023403050301121703070906031104030f 64
    0x52024511601c1d4441020f0035907040003460500d98114581c5806d58a800d8080c60080700c4c000d1100e1600301720907911000d4581403c0e00524091071091360b00440401020300d08881003401100e200c2102d021070001004908240100406000540f4911504c90f18081c1d00404828405490790309600c8410700d0f8280c041a5104055081d0b0054201d030800e03104c092601003c20b04196448500410762001a1541142030500c002c4911607800003081100000902e409070b01e000c140b0341061300404407454040c802100210702d040c0f09048026101d10f25007440418203030350200c0100780001003660781010340d455051404c1c0c00c0380c519010007032a101309505078810300d00c2d903030880303400910407401c01968101c0058101826070380030182e0780403c03054030307038201c1803070042008680352446180013001c503c580c45680103000b40c441802144410000c8410303031000c00c2651940140c0c070402050100e9141c0c02c2040c8d01030000003050082002003403c20f070380441210300c21816a005c803500590a0001d40000761503 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 509666124 1250 509664874 509664901
    0x14100617060409082703010c03270201091206020a020c040b01020d0309050304181d0c0a03060e0715030c0206010b09010c08090402040801090503180102210a030e06010f0f120b 77
    0x100700c803002d40504c00151100170960054200d085e020440a10061403442054212039020f00124245480d2070364001c51141d0584503801d80c441035503251407c800b000e000503070718201c1581c0594500c0c8940307145c1204000341a0040d058413100758003201c60100040c0d00b04816280c4424103580164890380342841060303c13a0b00504000c5000ba015a440c003a110042e1050011103800d5407000d150711203840619101480d15035886008240b0b01604031104500c3c00274201c5050b03848041e1140b030f00d0f03c65841580300c040c041d0744002d0805882e5222803c01000340a4081c01100c007542000d4082e1314000200b0028202c04c0f00e500103030594440010707003003650f15141316420070102c1c030381c00c10b42c28040452410024403980620a008500454880c26520780b000c0c103102c01c00c2c070650704640000a190702100044113104440342400341540d0346403141001d00320001e10300000d00d41040d11075035000281c1d1039151015842030350100000c6d490325903140d0700d04846d4a00c000e000109011519800255103100450 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 509667374 1250 509666124 509666141
    0x308190306170c0102060901020304081912090b090115052d1305091608030904020a121407110601081c020a0f080319151502010b04141006170604 64
    0xa0015101c1c0e1603800300202890a103909208a030721907490150340d503804021840d40640c9080083d483c40c9840c1c0c1e203056280c001c5a13900f000d00c40c81c41c0c0180b12481d0146118412400c0d000c1c80801c21000c59050a4140c0b40e0b00313942c002d00c1c55203001c0f42209004e00c000b54450035200041c0158521022903004950301d0b0108000400080400e09000780840c0e440142d1280034041c441c0001c509400c003000040d0a202e00c0307001d600b030b08092503002000b0190011090b1480c611040b68016200c00c0c083c24159008213400195501a1340341400b04102c070340c01003418502508096444101005c240ea98141e0380311001c1c00b4800071580203409040c1e1500320020200761400e8141f0580300c040e4419a0703070105203607001c0811070b030349403002c81040507201d801d420310888102e80b40710038882041501454800422107015408100c0207080c074049545000b50440421030402400811130000084940c00c80107030700351194150034052100028006215038a0b05868a040307400c01e20441c0c581e141000000c10001 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 509668624 1250 509667374 509667377
    0x60703023c060702010e1c050715020c0f0c100203090f031f0e0d03061202010804020609061611030102190528030b03070f1202010806040f110c060a06030819 69
    0x200d0401d40da160368050401048092000410030740c1480c100c040c5c00c2d2046120610300551000000840002036185425043c140b2402c00e550780b54a0350402c0002c0700c2d403550480f54224000205401f594400144000702d45004100b500c924444507410403080700ca0902c4050010307801881078031010701e0a14081280090020112a400052803405000001c64a5072250000c0d85d656010005c80304140418900a2800e00c0c080110b6810b1001011240c800443c002c0d0401400c84002411511030302c8c101d40b010000105281e0311841204a1803c01c404402030071140c62045c480c99002e01e003014000e452020b60001c0040d90007909030740046401d90492850248031030a1300c80f81d50f4000e080c086010b072401e0190368021460410000a240c60492030341c4c4440750319800c115040280300c3e80c03442d451030315036424640108640c96523000034026124100c00c91100c0c601d0503130b20841e194901001480c50140c0081514070b90f40d2401d01500c00c807041c903c0080c10a0408018412000a980007000039402d0f45 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 509669874 1250 509668624 509668693
    0x307021e060f09120d0504150203041212020c19061d101412070e030f0d1e02011413031b0c060804020103090606180f110702010507051018060b06070302 67
    0x150780e41da030320b44600300c440c605c081103001400f480110b80c05450303140c07040c040c2d0005614007803920f44071101c80003000c1c5014281c01c0401e140044040e01c00d100328000d11000074844801d622211000703030303410346c1d1b141304100225005082820841e40314014000d0141d01c0109001d6032100101e10540e05018034a011280f159400c00c50048400e42d5014001d000f000c0580d1515082e010407814185418103c400b03040841e1b01001034480074039805001d94000c0c007400c621441424150f01c00c1a4003400c600c1030194041c848440400841050301a800f07600d49019680d00c01d104081080350034400c000c0004044c0054400000c02c0c0700d901d010320b0600d5001481803400082c8081603442c4c0b881114140d401c008010aa03011002d8003070600d0340030340107a480315440200050341000d81d1700c3c0c07003d1184c000000e0500c40c0200b201403d1000c140070b0640312030000341c01441003020140c0540700300079115004681092074910030038064289030040d54801076260b00186042d4481a00360b4981d91624843c83c103007840c8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 509671124 1250 509669874 509669899
    0xa0509130609090b0f04020d0204110442090b03100506070b1611061603090803280c05390604201302030c0412050307021e060f09 57
    0x249114040040c4140b402c0000e5030002440c00401d22000640a04a4802450284009682c80220710304003654100d0700001d0940820629003014007480d40080030740e1041056200e1021950b145002401c1001c1d03540940c1c0c80320451035041c480c0d91040f000000103104100900c14410401e005540024101009418040c1d440740000c2041d84002030172a4048408003c0c805035589040c801003550400342000309101e290383c2481a55900020700000c01e40e418214044c1c1901d020f544080c44503508002c8283d56403800c84042e4600b4800d0303030850800c10340c0305400d0340481e00c00c5201c0d0110303010050707482e545464040080c24020510040310810560084e142d13500e420030841d10f1b803805403020b8001a207554a410f00303003100351180d4004103804000c0d80c0c00c80888240d035494075060303c41e84c90b420010f0300e1b0b0b1a034110740d00300e9020740d422165003011066046801d000001000d040180d00c2140c404070b004019802081c006c998444400740c000740148803001104408501420324840701600c14180c000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 509672374 1250 509671124 509671159
    0x9010b0714011514030d0504050d15020906071a0a06030c0501111606030c11010c020601060804030203070b0f09060901110913021309020403120e0f04020a1806050c0c12030a0509 78
    0x2510f0f903000850081544000c08030504040c020322200d03c5640c141181010f1400b40495030301081c40c0d070014116001480d08031310703202040d4166900104050030480e107405051406a0205070030500501201018000243c40c5060343d0081e001502c1c1c0c0400b043c04801e24110055480004100342d4081902070101109007401021a801d4002c140607a40407500d000060400b0b00b0a0300301e403003842c10503410500c122500707680001d034032411112341d8501440c0c01c3d81c85040481c02d501540000814400c803510a00440c01050034400b8001e0604ca010307100d45031586040c8a00300c845045000e07070002030901442c0003070310b0404102da009032001e50025107003070050881084404d100d0380050744101e82c003180610034003864046010f0311003554280300b070300d020224002a0000d855401220f1159800007460304100d8800c2040c0c26000d54451401ca4030382e03849000252060f04004411201c0d40700f0100214076914289481c0104081e07180003035407620711007180441c2c0a5000b0100035801040140f110144c2c903 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 509673624 1250 509672374 509672411
    0x6030c031002030601110a050703080f070501140411040c020715031d011d06130b1e0a0f1a0108190b03030301030c030204051302061b19081809010b071401 68
    0x140e668a41c01a90791400782d0000d010b0565a40040c1e4490b44013000c880001140000e030b80066a0b0083c0c12035888890801c0d85100e07034421080024115424250a20402c500b4000c0450090f0700c5008112522043c0301c09000c100d0303070702c0300a40300103034454201000010940100c0756207901c064640400d5162000300f181102444024180c00180c0d5a040d02c101c02d80f05400f202414204454068012428803020308003080312403800251601115902040110900f08001e203180c841003d40040107141c220450740092640c103c1c828041d5040600d0b46801401031403016046150584544c10240c036441c0c000385c80d442c070082440b503829540307902c50092643d08001450007144150300640c952419032040c071080e5400601002180381c2c0e45080040160303580c1064039080111650001c00803251039450520f407106007185a040c4081c4026680244039101e0020040c6214800c280a01c1c0d0f6010070501c90b400d0002d02c20b00540580034090304000031440c0c0d1005100c0303100307200081400040c0320f4021080c0d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 509674874 1250 509673624 509673643
    0x3100c090305251401020c12250810150f03151a210106052205060a03051203040303090803010b07050c0906031f020f36100806030c03 59
    0x214401090070420444100b24102e0a0b03032498800504403090502020b0455845009984001001d03144d81e0075981d20800041c46502802005048614516010142c55000e4030201c00d001c1d80d4612440e1800b0840f440c0c1c64402c40b041c090041c080410340882c004d0080580b0003140004a00848002503080c0703d40c90124003850040e110303120500540000315040b50070038000302c104140e8010200d585e59560071024001035000343c0540080d8503417004100d00524054101a605c0741c6d015a058a1119a1205464152100800400c20360300c82e00100040e00c400c0c0e01c40102140e124101920140c5800c4c405140c10500ca405c0105130302156560f0480c8980003600148001800801c0d4007043c00b20801910541c20010f9030b070a4505d040c01c4012985503540b280000703150010051034201a00d10960459855120717a080580c2c65400f02d00c40110110300252350304511490303961141b050b000b8071016480303484800a0400e242141080425a00102d0060400c2d0349801104021455501d0074400c4545 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 509676124 1250 509674874 509674877
    0x1101090308061c0c170d030605010c0b040302010e01060b0d0e1b270a141e0a021317010605010906091212090e0403020a05060705041220131407050c1b03100c 69
    0xa1920400c181e00c1c0070004c1b5006020036040c1903040045980010b9007410740c07608550702403080d6807541010f074003414106c040204030307618001000a55100318409401051a009010b00540f0b503040c03d00741c1d80d00f0110b40141d244041c00c5403000507a24001c50030042100c0c01c4040c20b03d6480c502c8442440721a41242c86043e15034440400390701d1b410400001660001c10240445600c5a1420290303521000041c00c0310005980056800140c0d002c0f801d201004000803000e5a501c0514050010b000c1d10a0384170341c502050010b00046201800303521101c00782c1e48199055004001940c807000381e07060401401e60144000e5820106003141680c1d801c0d48541d0003a00240741030020b9141c00e40c64800014402c07070130018140f00901456400606110400c0d4100c007040490842d002c030b49014051810400590003908681c46100a800c15086a8026407912030b48003007035a1000b0707042e038645c03043c0d0a10304241e80011881c0c2181c10b4080843c1001c07444003500311400c440d080041f40c0e040711001000c140 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 509677374 1250 509676124 509676149
    0x120604111c1101090503070b09091503030d0903030908041d07020102030c0d05090c0d12020106050f0a05010c0507030c09290603220b01151101090308061c0c 69
    0x500900300541030311984141e585514200441585030054061001c0090282c982080000c00503071042c0d43d10406400c0090998060a981e4160030312a41c1c00501c106000b4180c03c0d000480705840300c0344415203440b014029502d08121103446000a14044400302d00b4140d5070003070400450100b101800c0500840401d080300c4040088088440b424003c04c017004680c010400c1040a4088030b040d0740140c501a4070100702d0f03490b154149414800e55421464101c0003ca0b0643c0900014000d2103d1142d06034000300701da01c3e21801032115032030b601005c00c1d03000304000b102000554490000d4220f180d0142040c1c4411035129502c0012001c4203a010130046600d135000301c055424048030080b40d84900c14084404050503201141c0c65020051408903e81040010f150160500603031800700684d00000c007604540e16050600384c03008004d10310740001078104070070258a100522540850a805071030389105d030b940c1d238002c11040380f08103141400008103180d01203000070f910401d07001c0504940760041 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 509678624 1250 509677374 509677381
    0xb01030b2a030a0e07050a05041d030315181b0a031d01021c090f080901020f06040c0e010e0708011e1802120f011a0d1b0801032306011707051206 64
    0x10041c1e039444500140d0f00c0d04018000c21503071f9550b0f49410304545068a01246620a540d040200441089040c0c25103000000400031140c43c402030320414124201d448890428a00c4ca04008460003229541641c0400174185500444010b019000001c498a00400d40c0e0518900562188091451180490b900441c0c603103e612811002d0f903215480303030441080022002e4940240d0400b02002c00b404151b070000d8814a2a4402d005d1004425000000c40e10b4a0801e4030b03201c52a0510383c0b094440c446c181e540080b0f1441d1701060158041d07200e65584046c280d00b0219942007400300c0d09404894550101400920102544100840741c0c0021500503180c01140000390062040202101a4154204010300102d8030041c5514022a80c100085071181001520100200380c0902a204400b500411014226501154a90590744180810031442810784101001030301101040300071038014a00500c04036982251364146020003c0446101035507500c08940941c8100303042101581282040 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 509679874 1250 509678624 509678641
    0xf050703060c030e0a060e03070b0106050c1614040c20070e16120207061503110a0911070f080f280f0507080a110f011a030102070b01030b2a03 63
    0x200d42802e40d05041c28444001d940004e03a4441d0b80807030700140030603916030046072030039400c00a444156a203c1c1c101d10503940c403245d010741a80c003d0081d140c07862251031040c0e685024414601e004032001c2c407a000025204040801010341030b0b000c41d56041080341c0d81986c5d095412881030407a880d41c00c801400180d03052110440034584018800c00d2410031050603030707c500354084042d0100b00e521000050322210a4580080a851440c0c80c0400c0850114808001d02038004043c40c4d030424200d54052501da6030303c80440a0f0742c000d0140010340c0c20280440404501540d5040202d42d01c0303401d08614183c07500e800c004250300300004440600c1c010300810300a526000800080340381107410541c15044052200801520078040004c00e0301401041b01c0543e240500d800004030340b011400e5951a030307690942d0038020042c0358402c186000b07150b09544041d060600c00c03240d00c4c0342c00100c8545075a0960307c1750000300c0307009002c03010b07005200074101840100701d564035042c608998285990702d080c0b5801 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 509681124 1250 509679874 509679881
    0xb131419020406090b01020c0d15020403030f02010f110315240301050a0b0f0301090b0111010c0228020d030f170f01030c05030609100509010f060b0904050906010b040608040f0f05070306 82
    0xc100c0c24545850101300b0283c1c7c0000307582410350021103a603c0100054a061400784401070000c01e0110b0012401004041c2c1104504890220700d5000700080720038421b076042518040c0104004003042080450540d104800191250000141000d03004007401244180c80f003100940704002e02c0c10100050142c0e29210101000820751240714606050040c02d1b0701d541440306110308030103581c0d00c01e0709243e141d00544000000e03440c031000800c02001800c030065203441096640a80d40d030340070210800b0071001800901d0341c1c560081d00c488814081642c0a54094464031401c000b48080302c1040241021401c4050f0303c216041c0560880b503501d50f2501c0e903441a05038020070301c01c0d0000002c014100000041c20303c0a1101c0c0e11000c5255140c1c0c901c0f039401001c1c0c0c900c10008035070070200301080c11000e40c1c4c02800e155a054408110b070340c1d1a0740f00d00c0c0c1c0b1190300b8061043e00b404100800c01040d48501e41440c1c100d130240481043ca00c10710703a0307034200007a0b48080c11a05d43e0003503802081800107620 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 509682374 1250 509681124 509681129
    0x5060a05041a010e0c131707030b060a08030702060a140309070e13050a060b06160c08100207050d03050a020d02030a1d1c35150604030b131419020406 66
    0x2500e103042e035410903004080300600144050100c107004202c58a41c00b82842e400e81c010001e1803020841040003070005602d800700341c0019202c0404000105400c0c1c1400750000c412030741e000000c0c5081c4520342c0e080044d90b6005501c07101c10402c0c0d500e01190159040c10080d40185a118010500c142c03409560500d8400000d05118058001c00740300c201144c0081101d0034a55846071001413040d460400180181c0142d0080c0b130204101603910360300b0032081c5810813082c3da03103803403c40710f4203403048030240d00b40d01c80c0c0080100280c020811080f2400e0294010340e80100a0a4015081c114407503860380c1280c00c01c444105a1a17165003103c0d030800300d17040da0701500b08110710103800c0101228540702c00400403540b4001c2044007003010810f92149081e62040d420014070303c240c440000001440c0c90a4009079401c18134901c40340c003801001e1410000712000c8a6003e81204e2540d81e8000b0004804024110207a0348298400301c1e0400780c2c00300b40316408180545085c403501440080c01440704a0b440368 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 509683624 1250 509682374 509682413
    0x31f060201110d020705010603080c01060801050f072703120e1c110105090f0a080c18190216020904050601170109080d0203060102030415021c181a0705060a0504 71
    0x14400d50440c0c4a042103c002d041d0800000d40d840c000d61900f54010309159002070f10603a13011505050301081900000104e4071700b40000c0c003645d02c68081d101143c840030b039686804500709510300c2c10000c04000565201e00055030421200c15034a40700c080c500e0580c1240400045c0e03020480f4070481c546046d41c448542c002003120340382301c0096621106041424540705051040100700594595a0350740c071030b074560308058030461440e0b540d600c68590781c10700701075851721501000da40d202c016031180c1a500c0c070030061148141d1903c56000c09020081d8080d41c00200702441c0f071100f0b40007680382c0300c80c0580034500c500005c10803503161402413040c400704c0460404482c0d041c41d1084001c00d04039415a02801018180140c0d00e40b26100140e141d07200e07513407001c50301c0c0400500ba0560309401158004031019000c130b28038500c00314420210796038484103149050603604c019041c03140041352006280c0c940d0301c82c02100d1505405031519031400004654204040c0d446904110403c0009000d007003c0c04040f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 509684874 1250 509683624 509683631
    0x2705150d02150d021c0c0c0b0703090809090414160608060f04060512030a0810051e041e020d0605010207032d0605190c0e030c091803031f060201 64
    0x11400680e0024125034003034841d02c4084404080d02104034100e0321120510300c000c654131013001c1030b2070f460198481c007254041031a1414840c0082d02600c5986c00c001e0b03208100343e00c02e90ba07540040d0020b240b0760328140c5a2542c244050459902c624000e1400344d402503807080c0e802002a2042443c0503858902c54900b100200030820005801181c241e0308010112060030724054240d020078002c08484d8002a84001010748000c0ae40f00301000500389028290345840050382c0c0d2074451000b0714040e226550b04030078817800030004000b420907591000a00184049505c2000384c3c6a1040c201c4045284410305600042c060380741401885450300030a801e0000c0c0059601d5034450282d84c0640c1142202c0010814941c051011540709000c16080c1e80646c04203c2801c040341120b081400d00c0d06c445800702d152500000703625010b0220240f00800050041060913004010f20400344401b40410004402e04034230b00c002c400007071014621903100c500161018413040c0407011402c1442768825010740e4503 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 509686124 1250 509684874 509684911
    0x111905040f2105010606050a03050a0203060d060b041508010605030c040903020607050307120f05010608090619021323150a05041a0c0604080306030708061510092705 73
    0x1001c6000c001222004015046400241d4240d42078070940c106009106500c3c01d080424016000800f0300340c60041941c0c1080565605803841c012440181e524590101c18203501c0742c0020000c0e0054509084090400304041c100d130f00180c1001d240e69007141c40581d4507510103210718101003061142c0040d044a09201414103a10080d44502d0050028810400000005071101c3c1c0a11420804145490010400a09400d040d01c004040078080d56000071264804180009000038601b0b0040701c43e042c004024040c0d8041c440000d6010340c222081ca81e800c9040017510041d4038120b96841110710b007000e4400881201005201e80c0d42e0011401c1480c01032149421065102081e901540c8450141511180442d4248140e50240f5451000f50384103501c200310400400c100a10702582056044500315130319114041d848000490300303805a00c0d15010404054a001c680b40b001034141414480d5000d0348030008642010f00b0a800d0300000504994000d5203094148100390f40880c4090031000440b4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 509687374 1250 509686124 509686139
    0xc0406020c09190b031203011805010603022b1113090b0303071a0a0e1905010b0d0f060506180a0c09060c020d150e030d240605070b07030603020411190504 68
    0x10300c2000043c58642d6901241c034054904021040b0545860303000710b40c40f0740c0d40d250b10207601b00900f55032241007420500000b4202f4001d001741c480d08180c0b4006000f44407640c14010151000c120182e510494444006590940e0058002c0441d104240884a00e060404100d0b4042d504089a000c2c002d50007000001e0209546e44904010a44040f0200406840301d05810029148030340c5403000901403546103141031101007201c104101e10800003030201c28444410410744030400360b40603000410040c0c3d900000781c4580c0c04030785c1c800310080010940d20800304d00110340140850b061030b0f1080e03460388002c00242d00089036500400d0207280c15265012030f9404030300c0744c3d4000350b0000c04441c4e1681c1000c805100c50b400c0007804004503c100c903160407006029402518002c50501d004101900e090500d01d05004816410345e030711600e9030b030f16110301980c030340c1943c410060500003090341d19200440181d0751406010700c440080450603403134983c20040c8412aa50710703c0c940d41485000c101c00c009c800f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 509688624 1250 509687374 509687401
    0xb0a031109010b13060c11090f16020d1d0409080c06011a1c050a0b22060806070c14030c01110d0f0b011b030e120304030515010b120712050c0406020c09 67
    0x41700da91400c0e02c03c0c82441d150100782240e482a0050f4003940131810400510b0403503445610507544030107000c1083c5151503050b615105010a050001008044a428215012070301c0765403100c03024200081036023540d1500d0400c2d8112005150464110b040100b00310700003a070380048a980411000380c541f06a10601000c10441c0200c3c0012980c1c42d0030001c0c4400800742c1c8016032004014054464940d05000000020111140200c004525052001c0b0b24054000303901031046545446d4145501141d8440444280b940000c51800d4841080501c250302c3e000c0c058507015100300700035280c403450020f01440075110009005c0300072a2501038a900540c0c0d00c46030305242000d011400070000041401c1c1158050780d94882079410041545649c13168180c0007000f0400c4a0061040d614401c04046600100c40d10138441c0508a80050020484e4004240071807500320440f4280207410491403e80078042e900100d0301400b9000b400b00d42045459014070540800840c06c585a800e60b18102d00b9040c0c44 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 509689874 1250 509688624 509688629
    0x30d1104080609010627092126010302060f0c070909030e010c030c060513020a150e0a12151b210b01050d050a2301030515011d07030b0a031109010b13 66
    0x1400c010106d075265419982c0001812500f040090090844020386404003142e59095100021103144560364000c228140707522428803513403220b501d04c1e4659020000150442c542c2c440c92070004000300c07460311a0802400005040c00c1e003011900b0b1080c0e0038060603024000c510103045c460020305100002e5442030700c9034200c9030700840020707540d11000d418040c950038205000b504880700c0740001c03917100006040308030984e00a0380c3e030003c98103049050141000b600e02c240800303401d81241810014030200c561003218003841c0350000381284000e2200c00d01c4900140c02002148190a498100307200f2004906071040003e40c0901c203180000000030007611489000c5000d466a800104000c0d204a0b00f2100310305c10004203a4005840c25071203040b50100038030084a861158a907040808011440002d04039007121424010b810010b030004400382200400385001c050390303142100da065940c40c4800300958060140c262020401c042030122500b8113030485000c0c41d60a02070a42400355800d6075005 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 509691124 1250 509689874 509689919
    0x4031e05090108090c030a0303050402040612050d2106060c12050405100c17220e040201080a0b040e10020a031d0309121513200108011502030d11040806090106 70
    0xa00c2c1d44080d00d682c10301c420011504e1b894003035098003400741075058014501490003200c081090544d40c0003d442d001e03c604000038402c3e0016a01c1209407400b852032081044205a400300351031080742d8170704080703170303003582000000c96150b00b804424400b10401e640300c00313085800c050307180c241130100180008100b51001c200b000b440b04004802c10852100407148458118a106e4a07070145520103c140e002c59003004103d02c4192000080e503446291a0502072901a1190001515003800744c074094035460121913005510345c904101003460400a10b80c1d5086076010068890000550040c2a14005a8200900b19000007001c482c90340c0030085a608000440301c0f280f29403072443e1403038200381d040d084c2c4850344802d140422603002c5958a4a243c03e62042c50400e494035590040640c15000c24030b445d074002650740d00103211145540c2703142c0c400c01c6084d0044074140015480c144040c0c8000c1740c50a49102d1011404000f41c410801c41c2070b400c05061030091218600f0215840780441442d000401d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 509692374 1250 509691124 509691137
    0xd0f0501032003030d0e0f0d030c0e060304050c0d05030a02160302030c040c170a0b100203070b06090c1b03040317070b070f050403050313180b09370504031e050901 72
    0x31003940d0208105c420040c1c0751541440f52400707480313115071103a4003100445064003c1c0c00460100070702c00c0c460f16199042985411402d41c0d00e080c00c0c85050b400c020030464040c4100c9000030007564880707030008245172040004555075555014000d08011805141042c1ca030b60303c10080c80140d4001c640703403010310302c01d540004250b0b0070326200715004140d0403070544032032103040240139410302c0c66006501344020980b4195403521f100342c0200d0752485000e2000d001c0504010110b666454a8101e05070010031a402d510700b01644203080038003180504550a100b503000080400401c0250590305584026691199003401c0b42034641d540c822100030300503400c01071111548901c060140e4280c0300a141c110080302e4a076154400d0541e6022518000c0024424694004488070b84007406a04c1c0c60f00d1015000380d00031384480042d030b100311010000750f00510080141c6400180755000a20b0754500c061440400c207400e05040245c9251101c12551013501c0c2410010068503401030111603104e5801c0c82d240 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 509693624 1250 509692374 509692433
    0x524090f0c07170405031b100c031232010b0a270801020c010b030d090501210e0d030e0d08040209071418120c0a150c02030a06020d0f050103 62
    0x203026a101d0b40303000412a10b41c1c001c0000075810042c000d041510802c0d001c07100c0f0508140001080b0b00720b5030418552140100d588c01903094415440000481d119040c1410030982400d800000e440c61703020040c1100c40045941c104032260280c40801c1180509020071640d41000d124104511440300c0502c1442820036011002c0b183d2110031030182e48250042100803920b070300026020798031201c1c0301c81d480c0d0b0814109075524500032484004920243e1102d5403403d161500645811b0195240c00010042a407903160862400b4054900407000d80e0001e0b2042154140002c2c044400c012102c9a265000b030000302503498005265030b410580480d812034660703442100880310391000b58420296000086142482d100207168010203064007120300988812210391440c1ea101c4044246030f5012a041e002007000d401e540a21240498092500c070903542900e0300030038584584418210b9103c0d900040a00d1a04210b204080307040316980c1c014040c0d0752441d00da01a80c0381c85807000360b02d0302341e0f0b010f80c5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 509694874 1250 509693624 509693641
    0x609050129070209162706230304050f0d022109032d1203090a0311121204030806041401050f0316031a09030f1c0209040f0524090f 58
    0x6440b60305034014401600c52402c4c44440c0c0345000c4c1c0c180ca032008079203071350030818483c614511070f409010030340d075100380c03d00e850101d08a0b095000d480c1c040800c030103c804881100c11911009601c5680100020810b10300d2808410389011404680300045402a50082032101810501a514061a480b9090b16800d40d400001d04241041d0410710540203460104202d58881a2030030460411010a94913054109901d1018510007182d00404903042071301508002401201c0c00400c164004040700c912030500783c1d903410180c0c0030001c0d920b0b0404c03c0c0b9040000f0903170311021055010000352800c1c040d40d16560700081c160081801100e02c1011860148000381c1c40400200b61490700148030610815070720300b4116400840c0c40c100c1c50b800b40311070000400080f000011030384c0d402c85012040349000c0041c104541381c1c40800c40d2125070142c08000d030881c80da03540e001e03c03e80e0707800c0700f40005213038248424400d00d4054000c207004100f0102006140c0c8580d00d01d041e141d401581c42c2200e0910395500c00a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 509696124 1250 509694874 509694877
    0x90f091505190e10050108040b07140c2b020a150b0d0b061e0d0b130204050a0b030c0a0501020309190f0b1b011406010e0310020c030d0609050129 64
    0x1c829040030b10151500000602804501d044486503248aa0582c403400454165034182d80a00303408906104041800100c2d01c2502d90351003401ca04e0140b203038503290000e00d96583d0191a00c02c0c00c551220f00d440422035410000c80c501070064940d070b401c03507000e83d02c0b019444820b0781034041c03c03544130001c000302085c440781c201d0204460b00605030840440603140080c0c60007015541d0704d000e00754a00c000c00c1203180e260418a120003000300b20900e4034842d0364686c0e0080400401c80c4100607406402c8600684aa0050f58003c165852000c54803201c14030525241c1303e005084544264580c002c208003503600841280d2002c882652181025450b07072540c4c8284d082958000702c2c540c60498400100c8659140107061065000d540c15200804030400050a131180030205030030106043c00400c515600412000c4104080230341992001600344454101700d82201c5440c141c5508006120450f10395248282030160080c02804c000e107505144140c1d074100c5d2030250814512801c0e15440e0b003500c0e140700 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 509697374 1250 509696124 509696129
    0x901181a030d0f02070b04050f061e120105092a0a09050d030302030402180405030415110703060b010f0311030711070906120201030f140406050a0e07030b0106080106090f0915 77
    0x14100e0b005034010010003002c0300c612003800700c01401000404510035909008407012030700002e28400c2c0004080040011796400032071452019921400003d4151410300c3c003401528000880c407421641c541424800318600080982c000000b90040c0e2101e28204c0d0303110b8400c00c51080c045140c54000c0d507071040e242e9400a41140b03a0024400c2c5a040800d40d0540040d440780e4825211198120701c60b0540d41c3c07408038240c500800301d40050000b84114203420144aa03039185c0c5292504043d07803042e201a04104083e0010740e03156494490820b01543c000384250100c040c1440c00300031800044950120703074003000e80144100103480c03240780c0b200b082c10031140002d4060b9100c03c109a91391018200d806d00c081610407800309042c68102d01c5441950701ca40000c5d40a044100000e56a03955140b000415000b0810742406641e50070f403082e84001004500080c51050b00f00418a5060003405061b000c0164403480c100151500244060b142c01e05550b000c8030000380c0003060452600b070000e1040116034 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 509698624 1250 509697374 509697379
    0x50606091f030608070320030d0e060a0c08030a0c090503030c1005070e130608010f0e0303040201140c16030b0a20070f140c010e0f0d1e12050c0105060901181a 70
    0x70000071085c0803031907441e1405042c0701e008107c291a0000140b58641605404440118080e00756100640c142100100f14462072442e1200d4090065a04d1407030540090302c01841d0030341d44502085005400031030a030041c2408600540c100002000710540e02e44039500740900356078486010942e42400754101001c440c20050070b0114a20a510a441c01064144075480096003086005203c440341d40c420550035000c40c0026603e1561250015901c10303a409580425522040011250420301806444030003081c5c00c84128a07940b650501c0c907200e2178054003e03d1442c1c500801401050540d440480746d01d088100141d4582c400d60500c2d4000116180001d003500711400801c6141c000041441508010240c0b1914451350310340c024040101101000e85400c030600046800102e0700001c42c000c070701d00950740031044442c05651607000b021f001d45442c0000c503001181c50030041c003082c05001d074400c0c0c0684d20003d0661520010154025510391680d485554400101500501070f0a4100c04030001 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 509699874 1250 509698624 509698633
    0x9040f020d05070c0b0f070504230a0807080606190509070201020c030301090c170f070e040f020c1501150203040506070f0f08041a0f040b0a021005010e040204050606091f030608 78
    0x1080143c410b1309208011034006481d6400541c0c0500d060384050b01891080c3d5a00e0704290500c1c0702c1f101000b11000d003007086040700209001c80d0307544601011000c0c050702c0c00648186407500c066070785002005420745204441e00c054520600380c012510000b112400c6400d03075050b03210840d041e4028401c041d40e038410f60000100210f02c20013940c010212003d92035072000742d0200f202ca0285d018420644d12810f0000300c031400b103040350784503140030101510b0007440001c0740200112284100d0788195280c440a400c407441c2c0e1600c4100070040c1e18010030304520f42c1d140102031014000d48070b00c00c1e07001d107070b224040110b43d000a01c840c2181020040e640110030180c0d00c0d00700c0c200000c1c02c0d080b41c403d43c204110700800d0012440804000d4514103840c0070307a003071b05050505540d00e10380c2c0c02c40d04002003144580c100f003500c1c8040a0003118020b204031001450241890f005000c141ea10040219004802c100708418140c1c41d410b04004c107068000d001c03006010104c013070440160609a0000c1036501c107 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 509701124 1250 509699874 509699881
    0x60b1804060902090702010c17150a080609073017071104180b0c070203160b0a030609090b06191205031b060103080f13120609050c03010b0609040f020d05 68
    0x18942d1254a0300c5008403101d40a42e90b58840403030070b03280d01d0200d035400228405a0038070989005603140d40c005007d00d4040802c1da08010101d41078458035441080c542c0d00020510003207040030f00240004d494880406a070b023221018200d03228800301680040c0441c10f207465641171102d2042405985995041c102d581d400050401c103d0b181e90710b6004ca4880c03458100c1e076000861707444403902c0403141c0c0201210071035550032440038903a4000ea0707c02c1e0b80500078000d1602101c08494a1400174111a404140d29040c8104e40141298410781245002c58541050200461242c489556210908480001d0302002c1c5903e03104050441d40d02202002d0040702c800d0381044800300c05031103050002c100c1c510450620159095440900b8403016001c50820080b48082d016914000c00c0703a800c42c040c4203542c06580340722514149500c5142911816030b1906080308002d010312464490803400c800a002e042e22080c001540c2d84690000d081c42107665001204501c60541c050702c614212542d0704015510707 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 509702374 1250 509701124 509701133
    0x110a060603050604060606050c0a0609110603040c060801090203010b04050f0307080106060f0314061f2f101e1a0409060209120607021b0d0209040c090f020c0a060b1804 74
    0xc01c0e0703001c413261800c114000c10103508c5641a600100000c100800641743c054980b5130040403122030a8400d0500d8190003040c6844403170081d03000c1c600c1201c0302e034685450000300400030711060700a015030310300400041040070040804d40e000c0d5101100c140d5803421880c00003e10705901540045103070b50802c00d000400c036400084000303410b102614184406a01e5074004403890904880081e4084000040d84400c176910b5210a20075488a007009581c4210498100c03041c8501c003031030352000c0e00e41c0c3c10000d0b6429805000c0f0005c2c2d841410f02c140881140309010b03c4982c0c0000710360040c01c640d1141810024140f41254400703012001c0d0041260144074202000a580a4107419000d120302c901405189480040d00310b00c0bd9000d83c0c0502234074041a9038000d2401e91151405034846105045030002d660f84107405400760f0310510181d011945000100800e464a040ca9100c1c2284180324107082048082190811154030100008100c9584000680c0c00c083d244d0708500c086103184100010030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 509703624 1250 509702374 509702383
    0x70f0303060503011505061e0c011119080f040201050c0a0b0a0509160303020303040b0604140702010b041d0a08030711061602060a050105180403050903100504060e0a02060a110a06060305 82
    0x200c02c10740c001e01c1648018000801c0b01151445040c1d0086420011401c0c070203180c2110000320344121022500c0c140343d0030021400e480d0b60070125150044005070150483c0f4a110904464503801e0034105001d191100034514121030040c4042d0501400007071803a0481010700c1581c00c403d9000880e9806414416017100c0245002c9682c01c0c2e90b403051a8004481c45d02e415168030499501d41c1c000d41c695619683c40040c0000054102600180c9400c00d245140100e0740d105031083c0010b60001030b01889150411042c6c90948040340c0614103d07c81d2030700d281e40702041442e08203821101807696500e0304641110500e8401240303141d41e02801c030510802402c50100446981c4031344d82110525104c284251044600a1050700d0340600780c030b1100e0803c0c00d45500c072150300c28000c3c1061030070405540d01203401c18074048074401c0c00c103581d01f08100c10031034184581001401e01f800280484441a40802c4551003032103030150030300414044800400000b000f40c3c05249034071000a01105a507454002c3d42c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 509704874 1250 509703624 509703629
    0x3110c071d09120c010b1c0c0b1c02030402180c0c120406080403030c0c06020301090b0a29030a0905100c170c18010e0a121401020903061b070f030306 66
    0x35050086841035141c00301c0c007040d01400d11900035086a0300081121821980b01c0f0302156015500c030000c103c116655a46040107011075840c000b08030000c01e103000c141020ba5a00840e4030f001007030180182c12901590220030440485a0061ba6030320b0f1800090b03600300e54501c103c031140c42d900c810000f50300304503005851104160701c03c4403d40b045c2c0294811440c0500c3c018400040d50305070001d00420300c070b60010f5544042d0350600482c039060b03680b188c00030b03a03100341c1041360005d49580f505009400c0c4840c2010003400c51120704110040d1031140c5e00c9044407913407103400b0440d20100c0480c0c007440155000d181c96a0380201240c1d00b034000c140c80e00d009000702c510840b021403c1d4800c15402000080ca01e035105250988900d803825581e03070b04603c800d41e460013607181041a500c1410b2441d88844460038040d203140f505103415921035203494030840d0850402d0103a5039006120b4200103072000220513801c05d440442410010341080400440c500a0b258007811070140c1c50f218205154065215405 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 509706124 1250 509704874 509704889
    0x26030d0615030c0212030703021908071701030b0604110f070b060a15081902040915213c03030f05010503030f071103070b07030905180c07030c0303110c07 68
    0x8001801c910290100c5811000901c05604200d80440305080808020356200b48142070045c108280400c3d928100c448801c0c94101145a150074130400755004003d003032407980c0300041c840e01d40d0f043d42d0302c0100b90070020f041d55000d40c1e21030f204c071080c00c0000010340303a451826241d13907619400281002080c035401600e4490040380070320808280a2000c1c0f02070046411651034021164075510032810555601412015482c0e60130321000c10180303054000c4c2d030403800c03001c80e001130110b040c0540c07403000034000044400d10b05401c2c03800c1c1c000607e1aa0300d40c030780c031b005102250329083c6664510b04202140d4240080d00080c9103095442019011b1b030115580c01c910650810840c0e0300c45042c1503983c814007070f401100000c10302c0750710002035640c210041c06a0b8042d040d204c0b4155545603500427508204000c4012a0130a5000e00c840e041650030300e120a4001c04103001c16003810152103e0601c0f84d02c00281c1008034511448040c14000d40001d0100d4200798030103946c0c0c0b030051060315121406406441c1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 509707374 1250 509706124 509706149
    0x60a02030f0f040803150415120c060f20120708190f020c060d09020604180b01030c170703140108030c060c070c0e040c05061b0f150126030d06 63
    0x102c00510300d4422600c03890780b0410312031440c0c540842c030113501da004548159010340c59503020f0080c00c0346001d420008002d11030008401640030700d8807000040b4180c100380304001002c021018410352082107003407040441907000c1c800000e00d00610341888000c400f418019000064040c0c2006040380042c003078403002c182c01c00810300203da011244404205003000059120b40c407115032790f141800c0100a491740030540020310041079408100030350031a500004004a110031180001e40340313401006082c0000340307020041c5005c00807010304000850b92800008164001c0000c100301e00a178810010190740350400710440d0303034420601c1e946c0d900c01d6400340068001c403400305102c0c10039141900c0040b81e0014481d4109070030129030740c0c2c000304000d0050300e10701345420001880341c84840080205031035004a40601c1c00c02034034120300c2c00d00c04008488850340712410120503100003011081c1500c11207002c0d00c0c2403021072903045020720074a04042400f800001440505004540d20000842d4141c10005 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 509708624 1250 509707374 509707381
    0x12020102010b03010e1e0a120e0319020105030c211005030c01020c0604030204090c0e13030e0609090a0b0409051c23090409141b01180b1204050708060a02030f 70
    0x5030998458a401c2032886d44075080b8001186030524102540c2a0031008651080d942c6803549004100f101e6000008200c8184941d8001d00b400e0084030035008840756000302c41d0320b0780e0340002c28611004103010603888000c00c02078000c61415030310400b2001240c3d28039003282001409030342c4601080c485d06201c1c2c482c00c17002c03510b01d5002040040f07c088002b041c5a04252954013408040c2c69a454111010701c0c01800c00b01d0710640e03080940f402250040d01144500700d1928028040341c81c641f0980348900c1c1c09206075000c0b50390740000568481c00c80d00000c1650009440407601400400c0300040c1140103001e440200d043c04903103c183c0942e102d43ea40762400c036400c0078444015010382c4c02c0100d02041000f0300c0e201c5082c00e030000601d05100b03200006100000a5846082240440e90803400d0241c080011070f040da8011580c0c810610700302c05907180e8915140707451104d0721038075100240392081000010180001800018020101103003174419a10303044590100a610859a41d0031034a642c0021 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 509709874 1250 509708624 509708629
    0x181103010e0106051e0105070c060e03010b040504020f010c0507051011070504052203090315050a0b040510030311070504020408030c0607020a0222060b2a0a02030a02060f1312020102010b 82
    0x80b0707411250082d04000300340d80c6515940e14003284a40c5200d0500008001d200300240e2034049c2e0744000e0500c1e954003084c03100500100350955200d00f102c2c910ac1e5090100703000140c0d480382c807012008042401c144000001c1441c00d203041924651259230300c116044540002250800c185031001c40349881692502a280c0040004586c0140d40b4000040385008060060400d01c2e0540d002c01406410410011650b0760388036525103003420160190315071203c051042040071341c01480540603044a0034410352a040c030903d61000d103140b001038200812f00100300d109260500600001d400040e10030344d520785c0c403004995900e6000380441c0d1168468007000030340c810710100d02000102e500a000c45c2c40c0d80b43c180701e149200140202402e004a584520003d840a840001420003842d44c1c2e005800c80d405040142180c1d00382e4068040f0030381c11616a050059501081c8480c07910380c100ca5081d1034403c00e82e4241c040b802181c50400084460b103002040440b59045c604000038803d0b07000744803d5500c80107 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 509711124 1250 509709874 509709881
    0x40b07060615050a050711090703020705011b0e1c020d0b1605040303050406140c1507020d0804020907050a02030c0d021c11070501030507020c0415050405010b0a170604181103010e01 80
    0x2092070010f44280020345400780304000424050380100080c0c0c0c1d41540e000001000113000b90307280d001107640000c4c2d10082003c28000c181c1604045500542c03040c01003a0090070020b40301c0c2d4030511805840e85a1280e031104d07180760003010f60b0041c1c003800c10400381d45001c004004007034482400821032482d41301405d9106600312000c0c5d0398140c1e221401c0c00d180130402d60b11078040c142082040c103018040072800c520304000c0c0c440f48804103d100d090905101001a003003490040c81d120030070900b44e04001c00341e02c0d8003d0a640141191a105980d1003e0282c04c90071806900041600c4d4066015500d4010307a00041400c0806031301404c1c45400ba0243c1c00a660305c0b00c1412801c4250b0300724000400030b943c040e50000c0d03840501801946c00300c3c0c101d400010210382c10000b100e926504070100c01c2c403080c18140310707182c058100315090514081e60388101501c0c0c0200402c00303a103881050030008015481e1a0030a0340c1081150f0218001287d507441d02c08000c00240301d005010790318201400071100710500 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 509712230 1106 509711124 509711159
    0x30406090b010906050d0b040602091c02011425020f0d0c1503020f040b030a0209150304031d0f060304210503071211030f1308040b070606 61
    0x141034529070206801c40d86002c0e280003828003080c1c1314848240c0c1800d4015846d46010394441c5400d5000e0302c62503140316000240d0b014181c0b40b80801c0707986009a14400d032a0b0803841510401c0c0406176020703286607418a040985000b0341c25100d03031035004030b2043c0090081d01c0c81c40140c07008561900c80c52101280e81100c90faa0030004400c081c0300c001c110f4072680c41c041d464075440303403481c400701c1c051405170303500300400040854040e0300c141e4100c45c880d00014040c008603462091986c82c190b001200c003035010645c45450341030010b000001c0d001b03c90030020809110302c2e203d5424408181c000030422a01300d01c45034440300550304081341640c0359000302e513a400d540e803600c044014030014440d41c0f458811410912107004000200040d030383c0c4101d0703090484c000d85d40c8540082100c800d107000060065600024081b40c1644240028504c15009010038042140c0e20305030400c0c0e401a16 = true := by decide +kernel

theorem cover : BRFrame.Cov 509532374 509712230 := by
  have h0 := BRFrame.cov_init 509532374
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509532374 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 509532374 ≤ n) (h2 : n < 509712230) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
