-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5272
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:19:14.979089+00:00
-- url     : https://prove2.me/submissions/5ea2a4b7-9a25-4e01-bf84-adba4a3b452f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 948021582 ≤ n < 948201438 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 948022832 1250 948021582 948021637
    0xf03050f0a050c1b150109140a090618081b012d0212160f0518060702010c02150d05010b0405031e0f060403050a0825030b28030b09010c05 61
    0x201c004143c051340ca030740400d442034000c60300d0f00c080c0203200b9000d00502c400003a8590b540e02034540a004140b00a0802c2c1e01c0341510380d4050711001d50180c174501d40328000041118445c0402520480c0501162500d404660302c003041c2d00e40c4184400d041c01d81c1000d0320030741a400901c11441c40031070101540c03a2402480585a00a030145407070000c1d18140980030840400c182c0c8207460b007008074a40d030744100c00010080a9840307014560030555411810b071408001400d04000800343e043c01410084602161507000031040c0c0c0d5810b04401203808086901a81c1c0703602800f80b54017400b0340340c000500703150800c00883d5440c00e4200b0780d608901110105456401d6043c000e1461000303800066410724601070030050b20660045000b6070020b465031000440e00c4240b09115041c02d01d41c0402d011150301c102c00d0032400ba1441100c0c1a90102d12401c60b0701459000403c11001007031030403101c10300a461800c1030400d84000070007500150741041100b1400c181d119048542c0388003074400c00c0320089a40c0301c05 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 948024082 1250 948022832 948022837
    0x5060a06080121020310021b1506120f060a02090414090a0209131a04030927150b1b0d0801060e091503011a21120a180f060f03050f0a050c 61
    0x181d0180503042d40b25140c60340d00d400030403031035807101c40300c07841111303100623140d40c50845020030f51803038103943d0106045242c0388140c12a4440d0b424206c0b2894614041e40070f040c96000d85290b004075500040f82c03401401d090251000300c03183c608001d55203203000540e15031a254005002807241300b0220001d690103c004000c41a45a001400b804240c0034184003500d034030320203450075004690305e51000580041003071030b4060308900605410f803100115100d040302400382d6010075007410003003007030108000300c9400140600c07006203034140c2121080c1c5110907040880c005050010802801d0051101a412445070030082505580c413144540d07520f903d018030300788405051641942490046400c05003d42510480d540301264140b0703d04000c03807a05802d0048100141c0ca15400c034048014041003030801410032824541401c0302a0804964031240780c40140c0c01040d50030303661032400e10402e5800b03c80c3e41e82c01000303800c080001e070806038100c01d1190b100400b04a40c454031400022607a0401005 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 948025332 1250 948024082 948024149
    0x6100215071e0e040605060f0d09050c0d050703020a08010216030c0c03060c0c02030c0306070c020603060a0e07080a050109110715200702030609010506010f0f02030c030d0b0405060a060801 83
    0x1808003140d4003000001e01e400440f80101c1d100728148400070079586000c004442c0b8245080d01c613940340000702c10302c1002600d00780505880a0151320b140c00b1880c0c88101c1103a03611407050001c3c11800e0300750b104200703032006250071800d1160f1050000d00c140121001007003a81030780505042540044c0340c580b0f901d0200007500001d2042d41001c600000064200442d240c0c07292080b019900d10283c120145640e4020841e10000024084030040003d824280003c5800010150442e4461622540e81208034103080d00c0d0b40b80001c80c424100054990184102030250104110502881e0030001c0504480e001d2200080c28036004040740c091000000d40c40151040001810008520102d1000e80c12a8000c17200c117900034007441000070300361403040c4260351260314141c4459903017500d040340481d80c070322800b201101580b1081280002039041000600344405c0e4100700490b042c840388081c002a0340f40504068003846411800b4003803a5007002c038490540e004008404000a000b5444041c00e003101c50 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 948026582 1250 948025332 948025367
    0x1b060609010618150906020c0306060307350309090a0504080306131e02091005040b0412051906091e03080103060b060715050423030403020114090303180102060610021507 75
    0x1004e0a138415004881681214019001c0d1481802050706041d205d4004681c05507160304181c1c0c0510a034480d0b01030010f00355460340d0070024101c011a550750f000320041c0d19000700681c401318541d240340c50051240c80c1e1004074054240300300e040540c3c1d941000d00028200c148181902d89000b03095140a50148030608201d400d009825440300401400a40c00b4844103806031152074034a002c0d00380140c0458048860145110349003500e04144480811590b150403140c902410b0994400510740c1d10700620b000303005120002d10030069280561100030400309219120b9901c042600119070400e00071811250450000320701c008040c40041e95902c40c02d0401000080d041641c0141c80e0402d80c0030902c21441108000c8200741c080019654100001e102001603038001c11080c0019481a0801c0c102c20f050441064104842280003e04540144030031440d14402d56030a920a0740c1d04201868000c00240c0300c4141c03003c0d070603c00a45a20303070406120410381c800c1c400308004a2107440d40c0069151604d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 948027832 1250 948026582 948026609
    0x90509060f1b091339030209011407060b180a0606030b010c110109080723090c040b0a05090607060c1d1c14070e0a05090106061710030c09021b060609010618 69
    0x1480c08103507400820181728050094511400c03010760092003103c10100050b10b80300b43c00418075003c8415584144802c40302651030319406200c0342c4903800c03003401340000342c05401100e02d0704802078070444a890748050205400c100317240720566000702080108640000c00020f401c48681c0050742e2003c400d40c071a01d05c42c030030040002030354601d2002d4a081511001e81e11544050368200700804507000380c4100483c00c50810040000d520828014600580c0c141050b904041c0160001080c075041a50140c80d01c984500d20005210350000403498204051510350303041680d10800b10780b51508003080c0070110040c000b05031007444400b04403490540e43d03041c1102c0b40c40f40c440d02d0020500388203036a100602e0342404041484040103000c0e07a82a6485952a203c0488000c00c1100703000e60050035001b8101c1c100000071010032421a005c50107802100c10160b40c50590a240c01c124908005601846800090621219a0f43e480c50720b4110745040c58280410751800d41c0d01c8815559a0340000001c1c20603 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 948029082 1250 948027832 948027881
    0x2404060e07091d071d191104061e120906090f061b05031620070905160903021503220506010501140a0e04050907090509060f1b0913 58
    0x140c0c11034101410060360b0f0392110b0000b072103110b90324507503805a518500c2079008109903003e0650407a81d48513101d203031000e0741c0d0140c0c944040200c403909424070000100024041c000c868121080c8000554039000c03a03184400301030401054032404150a0501a407100511801d000e0b2a0700320011070703a00f1045000192040e443e1a400038480083d1112415081064600905010b801a41c1c07081c0b2110060388401408804c00f140e00820b50b0802d00f0010621201e01d000c44401002003001605076182e000426040c11a4180b0310710095041313070b50400102010520058803400415040480c8040581d920790301c94011301441d400c51000000500b00c003040c5a0030a0110021741c5a04075102a01d482c1502540408501818404d002080010499669100d03000b418264401540202c80d04159500c07651078409550030380344150703044149640b0480030b00c0380b5600402e050320b420190302d003000950b03101103802c4007400e405a0703181980300701c64075210300c004142c19402810311a4400c0150303414100c0b5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 948030332 1250 948029082 948029099
    0x60a0c062f0c0d050a1103131e03050c040b06041d0703050f0f041101020f010906140c040617040606050901150806121b0424060e032404060e07 63
    0x110030307948030300280180450008440900007141d030049281c2d405419401554401503074030b079000d03903180010800c210845014100f03061000d80b801d200c0c400c95440100740b8140c2600c1040ca0143c068448110450030200002140001d078148650816078001c9600003170300d40050028062035100c1070080b9100d41140d102d5000f02c0e00042d100311000d441c02c0080362220003103a0f60f0640d04492014140220002280210f252a1500c2250020500c12200248040c0d141d940c2503078408002281c3c265203450702080c480030301d01074907540441c03904070507410949040c1c40109800170101c110260000b0360ba021500b800309541003d0043d10b4068009212940d40ba42042c50544070740440e000003a400d00c0c0400c2c05454801200100748103040c1c01031000b200820042c142c0d2403035511900b40d01c641d4071307070b6050711400701d00003064902454800800184c914240e0050458407500125501c42d40207a10f02140c1342c11600c840c5820640b002141e05107507981c5181450081044512000851180d03000000f9040c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 948031582 1250 948030332 948030371
    0x1407030305250f1e050d020702030109060e0709050c030c1e0d0c0e010f1716020f100506030609010203040507210f11010e04020403050c010323130606080615060a0c06 73
    0x4959038807103021318400703038080c004c2000d00b4240001541c10000314170185481e0300900b400c0c2c0d000400005140b1025a1900100c50303220401c280d07142c202c071008021541ca20b210b0150700003141c5048034650302c4c100c4002c0e0500d1140c8840d581d4031003417a800304000943c141c800d540e0314041c0d82d84c040007000c420301c00180c01000300682c018006030540410303070500c0d8440d80072140f400494003000091a00c0396220390000c2c0c8840d600160851044c0d1101c032030803880810004060b44e40c0ea83c000035890411009050803d040140f030410240c0c010020300000543c0018460300300e8560410701c4038051072005219000080e040001380ca02107814205005200c8414200c604010f0244c0303501d40781c40000300a000681c0103602c0040c240b50091303421030307415500036001340210a401d040d00580c0044000002080d010301507c00c502204520f9292004011a61244101619034030b0001d06035850104070300c401c6001c0340891940951004038411a195000d0b820312007105034003140a01118030b40c4a08010140c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 948032832 1250 948031582 948031607
    0x91b0b04030b0105030c130e0c090f040c120c0326070515090a11190305150a27030e031e01020c0d050901081803040302101e140703030525 61
    0x1102c040005040d1600090429003c640500003980d07003e104400e42c80203200c0020145464001e02c065811242d44903406d0314458440c82010303200a0900c0c1c00c200811808582001c620827802003400d00200701092602005c8a611107180508071544030040d4008054102e0007813490100403032800b0070010040f440383c0d0005d0f4108a03510b403075510311044a03541d203081000600000105401440305050100d0701403010030314400b0701e480180d507e1355254640700007003880104100c80102030000580050081d01122018440e640503d0701c6080441d1072900003c040040510201d1201401c3d5518107002e0803c060310b160740355040181100300514007039032007010486102e0084d0408450050300803001d8034140d1206951b200255501c00030001c0b0444171000c0900c0d1144024800040140d9501c0c0e0b4501c0c2d00d00466980c041c04080c001001e40c0d0354944100810b0a0050200514946d103080409a071402d6402d468049001d41713500420404450000a4020394092044200c118868000b46c110409 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 948034082 1250 948032832 948032843
    0x52e0302270601050f1b071703030403031401150f0c061503050c03010606081902040b030c070213051644010812070f03052a1005040206030a091b0b0403 67
    0x2580da5000c01101d0f0341c803451040f0720344864203001c034400ba0111b800e00e40c4440030010084070300c0503403262403052541c03000120300c030400c1d40008100030401d0b515001c1c2c0c02c4001c2d05105800c03c40c1d41402d81c1044a081684c01d05002c00c40f501c251150b629200e000c141410700c2d0054003c01c00d04181c00c009a901410324001540c50b4880c0c561103299600301403054004071111a44c520340790351640d0418111441400102602054003440042040d04a01d40158011031902c42200d5a0341d800d0702c10f10084509510320307401554500400c0100c103150b00004034085050f01d2428044548541d1100b00000107090f40500c2403e03803580811107003440c4108642d00c1c0b9104890720502c40eaa860081907030b94200d032041c040516109006802c0011494415402020f2182c2000da080410920406150401c200d10710b1200707022800341c15440c00e100b4011004074440221040c0324a28054000c1401d41c40003403c60305917203640d45040b20900c0403005103814000220f5007812840d9a0f9140c04412682143c0401d860 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 948035332 1250 948034082 948034159
    0xf0608030405041802280b041d0a0912080c0d090606031109071b0f14071a0c0606130b03030309010b09010e0702060412110d050c0d03052e0302 63
    0x20030741e500725403000d0400c2c2c0c0104046125035000c200d400010015071380050180e0450b0b080440d51801c001c01030310181081112700440594180114901414042d2104200c0b519202c00d181c046058032f600350f50303c0fa2441c141803c007038442400144561040d488444811464030301d18000308074045d00410f0469000b10b009115506006040021007442074900b50045114542d600c01c445024111580800d80034220b0f074640320445403940850350380254001c2c44644c101c0740d001d00c06003402086500880c2003803150141811a0f13094115a1040040d00003842010004030034058494103410802c0f4200001d000c1d030f80c80f410040300322806442e60311492442042c3c603400220b100791240c445a0311401059000b844291030302c1e01c49480310758002c03c4003010418648110322030030b90300b00a01c0b01c00000365624159680110700c0400d052014103031282d001c043c10031040c448102c403020740c1e8100e803003074252040624401360094400062220303400250804801007201c482e0995410305004d01114000c1c0d08170303 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 948036582 1250 948035332 948035351
    0xd0302011b111506010509062a07081b030708010c02240403090b0c0a02041d011a0a03021c0c0b030a0f0e060a020a0207031406041b06210f060803040504 67
    0x21042da4080d418000194080030b0361900b1501d10345a810b40045041c1030180c50141042d022403204e500c01c04661000d100c0f09081c4035240f84500080480b61070303820014010150501c84c1c580c0c0c40e80318409079241025041c24260302280d6090254100504482000704882d0b862104080d4030742510032129010001643c003a00b420040001003144510303410b030b07154402c007402c0581e408030b903400c82c09241d55944110110400183c590b48540c0100c2c04d01501da001140c40c800c05c0450035200d107030104411549492031100b04684038181c2000c01d8a40c120388411103500e1030048544d010003086405044071544000009494940c40011030054401100c00d10092048010301019941c0c0d0010114180d40401c00040da20602507010701810252071042c2c40c41e1540c0e03900e03820300307a440f0143c000401d40c015005110400086006e54140c40000102e120700b06850110081d080503403003c04654001640e100010303181c011903200c840384107038110040107100e45400701541c0c3d0782c000380100b5000e00e24201040c03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 948037832 1250 948036582 948036587
    0x150f26030715051f060504051201060509040308061815040c180311030328030c1701090c09050d0303060801060b090603010b130b0a050a0f0e06031807050d0302011b 72
    0x180d039180d81001c940c82030716840b03480d40c1000b410010a02c0b40880e03503041185400c0512044480b00600e069590300e902c441c02d100400605000c07580601c08160714002c07080041f512041d20350f81e44160181030a0311a035030b414004c1002c07021315883c55002c000f8040c08002c6501d0a5140402500206880030080c0091400041c1d8590084641e148010f41c2c0d66281000000c41c90030500d421040d000d42607a050070070040d0106003c03420034441103140902000c10820395a41403003aa1b0240c80140b0b0011f4401070350005c11009001c040c001c214202d521214608644c074003c0d1102c400071701d00030703100ba15401c006083c000e004140e01e00a607070340ea50070902c0008070400d1110a42e034120070000c0030301d40755034646266800341d90700040322039103800c24529000406001c0007010344001d10094441983c0d07000346100051510348625004010f1180298020000351100c406499011009030f1818200d604900b501c1c91030008982d0000b075102800b60707103020800d80d043d0001002500f00c040c155180d40d840b40c0e0107 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 948039082 1250 948037832 948037837
    0x200108040b180705060414040b04060b0307030e1509030a1e0207050d02030c0a06110c0d0b0403050a03060b0309010e06010806061503130b01030609230709150f2603 72
    0xd0326207118500800c5000c80c10240034055500e040707044071003503542c41c0041140c9821030351104110a2a04d40d07400014100387c01101460741080394200003160600210409030301011741400c04065843c40c903842c3d138460403c503e62103580344240c003d01c42d140c01c0e10081d43c0c0380d1090070300b040020100c0014500035542a20803000454490700606421030909007804110504200143e0380f41c0718400110b000c1d92034200c41c000c09001c55543d85c0004121078040300d840d007003030411000d00402c05000c11102280c500c44419822590500d000c9a4400c20100100c002e091203400c0075440d210000240260300e407055022400000400c800c2d28100d80e13036520080d0b11184c040780c54076000700c44280d0b00103041614000455201296035107403014404152940310305044260000ca481e0f43e5a4400c0400340011020820316030350180010070086c59105e120301da1a0039181c81a95101a01c50f040d840d910b21700d0040c114040e20410321211440c50340c0c1c01078080c0168a5008609646410302e000d0080010003004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 948040332 1250 948039082 948039091
    0xc0f070c05041a031b01170f09190f0803090c0307180b03071202040e10050403051b03090a170a0b04080702012714010309060e0f121c0e0316200108 65
    0x18080a105445d021008440e0140c003040c104138116480e10030005451030101d00074040007062210b0b61800c40e5020340303800c0501e84840c030852000020a00010000203c026042c0d52006d40745d0380341d846400c1d08518054011001a606028818000c03c40c00c65141007040c4010810009002107210a0241503c0d00e07018010b88504150541000d005030401d41c10004529480100b264000c0c201c422501045600c1030750304034009000092078201c1c9103402c640d2040043c0410014616000e10307200001d55a034070754400e00840f035504007207281c041c150a00c180c00245410881904403850940f84c08102a03200c86000c80c0803820b90482c80c2c1c680400c80c0c81d0364101c802000100e20341345041c0301108902a22102c0540e04050300c0305615800244c05005140158000314010b00c0c0e004000c0c0d40050a042d11929850082e0b20217001c09089403000a021680c10840d114000400700c0042418034210b1240c1d14078450b5605400c0e103007c081050039203040d2065140100b1100052181074011101201c00380c4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 948041582 1250 948040332 948040339
    0x1209050307020d08130b0a2019031e080402040606030507020a08070524040b010e0c04050402072603070e010e06031501020a021e010e031903080c0f070c05041a 70
    0x4a10018200f4110f20300000740605045814130f041c400840c0052503482c3c05c80489408040380403803040d600040c04410609031654942c07520b0101c442c4169130b4200315902c00345860000b41312601070500035501c0c3c003814813500307000c452820300700040581b107010281c4089014900e04600020242d12901c03946021b8411980a08114000d603202c440180d08522416a40d41c05490300101c4113200c1e07038014450030000c582c0054200d1400342492070004405900110b401409502002902803840084406484c02101c0050700c40540382021107500f10380c07800c03104802a0b0011204071107481003026501c074071780702d0b03455144c12412400115034600d500c000440c1c000c0c03c1400407420120000c140300c03d0415040c4111039650b1035680000d10601a1100e410700da95a96910204082d6885101d49400c0701040d0000c1c4010303100c1824000c1c1241301c14001404008004c008910341c800c10008843d1642c0003442d602d91540c50a04005550845074880e20388038518018100045600c203120b01002440c004 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 948042832 1250 948041582 948041587
    0x210050c0f03041110030e010b0a050609040e10020408011d010c080f071707050301061106010302090a021e0d05060f0d0b010e0703020d050f07080106051312020f0405040b0712090503 80
    0x10000766603000948200d46451901800160355102da0207844110202c50360f001c111b0380f6070250486c0c2101c11401e0f5a41c01918162000d01c21a1034020468269081c00d0703a00080761644000c00b80d050103511a04010a00d00020f400110725905401500007241140004080301c0240002c0901725124030000304003080d1142d00045030809440d90484d4000c0407810500340c601d04440124004032801c89800f000b246012005010181c0d000c40e43c501034000600040455505507000034410380c800800202003183c000400c21b0b2031200380465001c2618520000301d8a4482803148000174180c2250f8060061080003029822840c00b20007000e09076410440403102079003404aa103410742d40080c086420b02d9001c10118100481c2481441c0c170031082000341100398140301100034294041039000c0760400c4400d11149181a561452070012941e030111100007104540c808240e08408044100d035216242100300420300170102925446203540761360748182d1014490010040b50000c0360050300c7c07030340107 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 948044082 1250 948042832 948042847
    0x15010f030f02040204090c121125030c0f05010903030b27150607080418020c03221d06010e01090f0308071407031a1003020f010806011e05040302010210050c 69
    0x30900407280050f1015103400e44501c042003d54a100c101c0100150285880d01884282807107400f030410b500716895450711104540660091440302029828542d4200c81001010700484600c8400c41c0d01411000c080c40346814464002c06a840c0241d010904100c454803191800c2458004160030000d012186445d12610066005034014004080b83c11501c10440242d0380762409420b66034416001c66030307194145a0400038007240c40500200c07460043c4604880c1900204c01d039502d034084407644408003600080c107060218210741c00742401c2d1203130452460100c0000d1000d00c1c402d040031b880303134019003805c1001180d41e0300880c0320318161542d80c0201440041e81c00c030004c11001d4007401001410681d00300e1264117203809544111100f030002d0b08010740307050040c4200e075841800e2030401e1001038910b4000c9249040016011810040d88400091090f8000e0f042e018049164000c040c0c81426603140c094815401400264007512491600c20b0141215005141c07207040c000e416942403520 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 948045332 1250 948044082 948044093
    0x20d0305011d1803191707210204030f06050402040b030a0206040b0a0c060c0c020306070e030a0605060d0b01031b051504060c080d0c1206050402071113091e0515010f03 74
    0x700580300b12400f4008440d10102100c0410280010303102c00c080c4058011710300c45016048915018080c000706010700200300c002c580101c8064a9071050303000c03005005060051840082c412500000e140070b0342c018240050203240e900c094130a034030a841c1040084e914404044d5a0000810001c0d40314208000600c4400030340c901808100ca018100280c12001c1070780c0c2d50003078800f000700140c0043c0c21136201d8001d626042000c603400103650300f0040f170361103605030100340c90300f80c00d0780d001d803075140c41d0000b00d030607504e50102d4040610b800440002c20740d610703440d0440f034418035440d001c03240c549640780c045050704d4207100d02600310400c000c040d0303e02840d020041e60040d062203429034001d6020721107114074407901c0c0641045140f02d903031119982804072000b0070480340c1c607406c40782c00f451042c000c410005064445007244890101c43c00710720309043c096424081c21100358010000032a40c0140346200020f644c1c621022131091007612401c0c0d580340040400e00e102440b034113405030407001c41040880c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 948046582 1250 948045332 948045389
    0x60801181202121605070509070509040203060a0504090b0403030e0c030307020f0f33120a0536391f05031915030303020f0d050c0a020d030501 63
    0x100140180d40c40e41c0e00f0003800080c0341d040107a4034414030520b5840d62007004030600c0f08501601080f55006104e05011400400600546090030b00813507001002c10384591b02d0101d03080041030001c100340076011042c40c5c000d006139000d036021004642032108288400401050b6160300d03101c054001c40c20841207808200060500b43e00180d00000400100c00c0c40740c8a060000c3d1034040d076004d088050b0840d4000e0192242e101041c6c6e4290706070203100b45002d41012101c0e064108264a01c00b18480c0c4841d40754040c40720107400704445540032410b082954940e5804103c80c10200c00040d80d48100341d40940303009045084e50080c3c0d02480000081d45031042e02110381c0c00441000e403100400060650040c0b80c0e2310654064a40490004010400015440c80c070139001000203807024001052180c000984009035808000c007495008101c84a503120b01c07105581e001c3c0d403008414845801d02c441c035852950302038806040140102809940c20a010740580c81c1207901c1c0060031550075101240604000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 948047832 1250 948046582 948046613
    0x8120a2a0e0f1c0311160b0a030218040e012408060f0c0c030307091503110f0903010207020409030f0908010603170703020f120306040c1e0e01020f0703110406080118 73
    0x51050140e0019040c0f60107180080c840c429200d258010f01c591030b100345030a0240c082010084c96030142800165100801d5400501c00b509002d41c8400041429840070b50301e5a201c41e4000f80b030403081c0300f0382e20340c15048030300008032031074000712040300c182c500c0d56281e6980d004000080c0e0204000c95580d00d2413411860340092034240b1903060403020504e440c10355006035590720004009200a00c0340880d10110791120b56002d0400304000041c6040c0340c039046c080c91065250031007010601f10300a460a404890060381d004100700041580c5240c007a120303585200c080e00004488001c04111801c0c14400d24054a0300981e41c5405908002c51401455106410450850041105a003c0718008111f2101c25400741059141c50346032103000e200841e441030200100f0000700c20714500343e81c40e1800442c008074815280091411141c40c0050b403420344080d01c0d032030703481c810010000309200c10340c0b040401100c42154140440c55584200c070342030f80c4e0144480030aa5544545110000700c1c0c0002da00d041 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 948049082 1250 948047832 948047839
    0x402130614071a0105150306030c010f14030117010b0109180b06070f05060603010c0207030b060910030c060903120804050d031a031522050303011208120a2a0e0f 71
    0x8102d090740d0f502000c3c1890550714412002c10000500007841c1a2404d2034003240e10340090b80c01d51510100080d50b030300380c03074080c581840480408848a18442d051107154184039202c010364959460512040c004140d00e11221954640640e03080190b100746000d0003198141020394074003180b2042440010003140020380e40c003540411403800010000e1490282050040001d0059468040c09150a4030101d401450443d085400144002400c01c0b814981160081d502c100780c0f6078683c0241c1d190404c1581003c1d210442d071603030000d40140d0004505058911801c164880d02554400c180c0d0b02c104141c40080143e00854144031460788070394010417040c0c8a140780b003420141380e40042400c01e0258041c044a0300c7c0d6007020080c240d00060130741d01c400081150240c441401685071140c6074001805034200c00c2c80b00e02010750512915178140c03017011000c0301c5150000d0030010340c6503000384404807000d109400d0b41080c2c03071250281e031031a4080e07051a507152060011048020050390a000d5014543d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 948050332 1250 948049082 948049087
    0xa08090d0f0503090406090b0a091a0a0e0106021002070b0604090c050a09200f030403081015090e070908030f0d021c0b1201050105130b0d12020115050402130614 71
    0x4500c1d200e030381c00034590190000c1c50340c8201c0300091000355110b41d04280403e504252115103143c80b111141e4084507007200d400106403140b8a1201511440800c0c4941d10078030f08900850030680460f8014100c49241e02103807103c00c2c20910300c80a0307000d100301c00380070041c010000442c9400c1c240c20110410740700e00c0f040d50040e910b030400034540740d000390421640c00356030b501040c0c1d0704451540e94081d00450030014500300f10600c2c2101c2c01d2880001c00c024100071010010820b0400c100200d42c0152091614843d010002e906004246010910403001d003180154003003801700d8051450302e070a848241c4060751501d6848801d06034550301404041028980c01c011860b00c0e01d146c08601440c41d0321030703040440c00b03052000c1001100a034080d9158416407400004214541d50a0a07000c5109501038005c148092202c0005004141d01700b17018086c0071010090712440c50741076002e8081d030000c11080e121900d8451090104a01985080012922a0382c40a0282c1c0b401180804008110f207040c251 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 948051582 1250 948050332 948050359
    0x913020d14010219030b0607062003190b0616080a0c060e0c030c10020a060f1103270a0c122a080111070816020301020c0d17010501110a0809 62
    0x111040c0c28401d800903030741d6010409082c14409034030341003100741051605210380c403400e40004605220b0503100604003591496001621a0301c220390440071405011070a845e4982400f101c080b02c0b15826034007440c68501000b4420a207024402d8420b14020401c030061500758580d1000c009a1004102c0802e10030b03a00c88403000150780c0c0c064440b4a01c00080644600705808041c140741241c0d400a09218031400540c5408041d40054203c1d9900c1c1c1045022030354043d030003120002040708800041032080004100b03d016070b003000c80a410900a07018020f082da003250791803604c03001448030040c460510004200145e02c4104901c00355603000d00705900b9805140480e03800070116082342e08046104010382040100002e110b904280e000d4950345610708407241d40c4048140c0f00355001a49165000c50504040d5142541642e1116200c40103e0b501c109100102403d56045401b0540e280441c0300004a820351041c105a18003440c800c0c0101b40c440395580e01e0403429085070014640100a001c0950b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 948052832 1250 948051582 948051593
    0x20d0501020c03160b1303140304060209060408031e03012304060e0414010c0801050a0b0a09031b090b0301090308130611030403090611060403050a0c05030f030a290913020d 76
    0x10132100400c41c00c400c001031000c1c900582c07040d500401d640c10780d40c217032141200032a400800c0340c010000381240301503490b034852800f08000e00454a04940007500450082440c01c000802088511458180d03810703c1c4101e038440103407130300c0709000ba01c1c2d0100c5942617181d000b00c0c026100031a0200014404900d0b15200d0714001008001202d080da800316505400909640087c4a81060000d103417030400c01941c101404181010300c98411a54403042c0065070440040c403c946240145900800c002a0405150f10403010f201540c040e4400b002e18002c2182e2a6280520680b01c1c51a0b02d62500d2900e6a100da0103c01e00e00c0c4d44d80b0b8143c8206440d41543c480d00c024031310007184a28402e444129100d03092580060886c98441100b06681d030041050002080e001000d9550300c0070103103021401d50b001850040e00310301801510280c03d21012040c00031004d101d4110014901c0708658202080c1d2003a5180c0c1c041d00c0d1180241a0802c680c000801c4030700c841780703c159603d14005819032080f041a540c40 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 948054082 1250 948052832 948052837
    0x308042606040f0209100f1a120a0e1213060302030c0c0304060c0c050904172a0102040e1608060f1c030206010f17030d020a091701020702010e01080f04020d0501020c03 74
    0x3299486540c1c9200004c43c50701c4030300b01d6003115800f50321016540c101510504800d48a004a42e140e0754081c5002d4290001c01d81103610300d0540940907019414402c514a02800611125008038000c01032166000c0b07561500b03440010390200f0b1404a801d00e0180d094000707500c090b00480e1901c008010f4a00002010401840240302c15520403000c010035042c00c10003035649800031340c4269414000d0001065650020251b403014109585663b80480304507100720961926041003001c2d41050000031100381980030b0011110080c005003080d9452454078540111800940320228042d10301045643c1403050f07503d200c6000c041c01c20040d8011861301c4544081240c0c1c0e0072001a844400184942e07100f0040303100c0185440300c0300701d4250850034402d948900036030810842e402da0116072010700a205040e540018165480320122540c03042c1010340c042c2d4018003050707010410030303182d4201a5200e01e0401d8898040c908907185143c540d03a00704083c0b00e20741502a503c5640900202c080c10314240700 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 948055332 1250 948054082 948054091
    0xa02270f220b06040b0f03061609090608030c0106090b10110a02130f0c021c050c07030803090307170412060e1203011701061e1e08101409070308042606 67
    0x1402542c80c501a003c0100f07880c03122016034020308410082c00c0340e60310f000510940200c00320120402c010800340d4120f032000300079400205030b141404070004a201d00400105660f1107590001c1c4a40c640b241c2d100015120080d00c501d4021400200c0713801a01d20071a21000ac40418400b03984120f10340b6000a803070240d10703134005000e140d6566840341409400c4c1c841c0300a64210380c0050030245800180c0d0050030000341e0342d08018020005078041d0381910500140010f1684480c186441c1d051003484d4a5883d040a01e04a8020001c0300122180e03140e40400c0d01c0441e45220002d079072040c825550000608103800d1703002900d10503428164942100c1070041e5000c1d10044c1c0180d0131900c0c03d50b00140c2510416800030001d94401500c007650b034010303100c030041030728110041000c008a81c04d00c2d204c402c81e8654010006401081401c1040e1082508000c0c55901d041c0c000e14a039849005120340c0344c00d640d11000703220170810441009105034504208103c091005500082c81307a02211a500b800c8c0c00b103d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 948056582 1250 948055332 948055343
    0x90e010608160206010608060607060212090102070b011e05210f1f09080304081303060c201f0c0c0203070b0901020123070503130204020c0a02270f22 66
    0x402c20440080072900601101e01920041105524224016000c442c001e0f12240c0070f0392001466a0030b020b2690100c515510341003908000c5864408880d500035044400101c480c4074006000080c800c070f00c03e040c2c4c03a03031308040f0155895451800c81007080203130942c00c0207160011403d101101541c42403000c01c1140e0b0822018140c2c5861001041050007880a2400140c1340340840b5240402c1824003600c0c0e0155001c5012640c0d032903280d0300300400040aa00003420f0034100302560700b100b58000000113071621405411203041040e096401d88960031741c20b40a002100d402128100315005821409900d146410800034000054012a08040072500034042c1c0d1180010500607550f424840d9030f6840030b10003044103585404170b00c4a20604005002402040404000318032118114400002001d5006008640c0c850303c60a800d80c55480b41d0390268461240180803183d03807039440300000c0f80c002c40300b40b0344c80055175004900c41c5060406801c070001107004505031101094071100b6502c01e1800380 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 948057832 1250 948056582 948056597
    0x10813031218120c03020d020d0507020d0c1214071d06010c061e020417060106050a030c0e0a03050a02040f02160f050a0203070803030912040308040b0d09170c06091c0f090e0106 78
    0x506006e8036100c8050f06070f40866002c483d4084180368840181c5803460f40c11500c1d001603004078103140c10203c0c11608548100006140c4060030401a200d003400181c6e10401a2800d6070755484013090385000d900c1410143c4e5240c07800140345588070b00c03042203070507120f1500040d46040004081c0c502d035070a1020003000300ea000074140300034402090907030311341010344006140542c10400c00501070f000d1441038905058440300d003098124000c15021044040150595880f207940e41007169940d00b40c41000e0340154a0320f4000360b40340560b030084840300c3c0c0c42490030348450f8055649440543c248200d094859000351038420300180d034144003060050641e00021900d03400c110203076609002c0315200c0300580302810070042000488030b005031002c442c62202403a0300e034035031614190007800c035050300200300e0030130189a00c201401a8000d00300c090500421681203660b0860b245903224004800d0406811201005c041c070319200e101c08205511035841d2002d0281e07a85c151078003038000e0a0f003000b80401c544 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 948059082 1250 948057832 948057857
    0x10315025e0801090f030507030e030a060b090f0103032c0301020f120114010906030c051c020418090809240c0a020916140c0c0d0501090201081303121812 68
    0x306034003000d40350200007008040441d5455001740f4594820042c280078000c5502d90505014035540e05803900082c0c140d0781a18082c0c40e18000070301d14921414070981c4031201182d02c0f2100c034540c0c1c41c181c0354541c5901803020090502c07024200d1458840318441d826102d11001c0130380b030a0000c0c1420440810701161100d411b2001e07802c80907170507007050003d001c0c200c90702100f40ea4000c005004a4989050000f142c01041404843c07900c1a000d003a0340c50b03003440d002000046003950050080703812070110012401d0b024140541907400290000c0c00d59541808011f101c0c0c40c0529400103100d080d85081e920600c0b148022075203d401c0190350480c544c202050401c01d608050f401540d202c09205034007070400000180160014071581c8100f0b10700c00c07011070b491009010821402e1000320b001001c6408002d403618055000c1c2006000c02c03030000340c1c898081540d80309600f10400c6d409a141c1c6a152080340d15241000c01007c8a400c0e992100700200c0c04600814040b207102e90700c0e81100d980d6034402141 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 948060332 1250 948059082 948059257
    0x609020909061c15060b160302060714040510020c09040b0a1d031e0405060f0c010e07080d0c02010c020d05210c070b030406090501050f01031502 64
    0x400800a41c01a22669060aa00c80c0f002040503030300c80d030169001120003d0800c0300030041c4865000080800000941030460305d00c4503030011009403082d801c68117603980d140750448200340600894039260030300f8001400940740c203141010905415104848850b070000001035486501030b00d050b0b400603150020b0004549041c0502c00400b0102020483c84840300c11485960b1300c10b004001206006040e401d0358401d41c05000c480040c1402003100b82c650048048034282d84d844025a2042c41d1301e40811900c441e0300105218044507a00c0000c6c14980403601e0060701c0207500e9440c02c038100107200c1b08010043e544c907554a045075005000904190103100c4194405c462070070450003501c0c0d01403011300050500002d002080e110b80c2824240c49440710f140020113030840000c0140b0650070013003040320386419440891704980c00755103102d03600c00da265071010413032140d03618501d00103408a00603042c4181c100c0080b900040c0c0e0b1402a40241654104610422421003890103e00e5030041e02c19510700 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 948061582 1250 948060332 948060349
    0xb0607200618040b0a05030d030f0501050307050a0612110a031a1f03020d14040311070b040b030705070201020a06061806211b03170d0e0607090302011d0406090209 72
    0x2030040d656a482e20507101089001001d0100c5003a01c40c0391180544074044e296100380600400000e800c50706542006880503001d41900f201d0034508601d0100009114030b030001c0c11500312000908140901800d042c0201d58400c03c0c9010b03d410991540d030006e4001030280e00070142c240c00c50b0b03000a51032007416072940a1032580c4031814450400c080d012184080e0701d0100310a00559170a005a480140c43e003c0e8028003100410000b003880a001000141030304410b941042d244850140c03000151103400c02c0350640903d0003000e961040034000070b08203900550003801c5040c01401143e44104141d0b440e04190350040e00b24401381078448a550002c0c0441303004400241101301040751000d1046100545500c101070f0700948a10a01000c1664001025140c44c01071500040484d810800b85103d085060784071641e1005442c1c034100e100f4080d5031011810301d01420142d92010242d80c61600115090501302d0120000c084105800000351390303e1344a1400140842c0002688500c000c0c01046040c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 948062832 1250 948061582 948061643
    0x1180321030507171e090708010506101d01050912100c050909040818030607110d0305071b06060918060f02120703050903070b07020f010605010327060b0607 69
    0x500b0001807007005030b04480b1881c40c6440e02d0340c1034142940c401340b48113101c8115040000b880c245140500007007105c00700300380c425501e00324020300554540c1c3c030611440340101c142c0d02c00042c0c0031a20084c040c02c6800c4c0940c0080c60145855070078040c2c03160014200e440d82c000c0905040c1e00030100032034509601e0040a101d8621070815174104242240030410481c4024001000d841c400a0000551100000c0820f402140a012210315103000c0030040c04c0617012200b0400315101e900c3c0400511440307070160a100714803981d08d41d000e402851085a803e49a030280480c0c08940303408010a00c8492485003074001003a4008034200d20200c3e0416100715098078000c6150140104003078103041c5c95040d207041c0c2000080c54001071390342d80c50014a080d4020020000c14124491003409609030703001603600b04101e40c441c02000030503903d07001581103030380c540700102180702d40d410036020384142d40d04000e20b960302a00300414001c186c10001582d0b5404110b084602958945800140314a42628000c20 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 948064082 1250 948062832 948062837
    0x2100206040b06270a06030606030503041406090d032f0a02211c0909090609021804021003090212010c02030c1011030408090102010b033304020f0f01180321 69
    0x140c001c240804000c00c2c4d500f1154044440741c0001c01c1c4180d60f50f6000130001c580040040040640301d29140791a90300c40d10503a0170100c1c064002602c14030382042201c0205400811344003409041e640c043d150304100139656000d560701700a041c07001340c14080170640e00b01390800c054041c60040d4410800403100d90495801c0803142061210003407400060040c00042c801540d08402d030701841700c229240603240d0003d181240c1011030550030403241d03820150060b442159142c2c00c00500c4000d00945240407140030350700840b184002c44e4568020703400560b040d0f001030040c81100410b240c420b400e50b6148000040140c1c03000034040e0980106100c0f0112403400a4006d00c9030702c0220070b1505407404040c03c068103014000400800e540c2c003d6204500400380941a103c4c02c1201034000030010001c0c2002d1608c405003c907094a541d8520b008080c42a5401402080c0c1c0001000512811404804425042c80540c10320801445459614840150f2144602092001d142680d01c800700314104860400d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 948065332 1250 948064082 948064099
    0x501090914011406221502030702090c0d140c09090603070f031104020d0e25030201080c21130615030308061306092309190b060d02100206040b06 64
    0x10416501807181c1100c1a102c041c28030390944a00007100c0c0c0c4030351041e4000810542c1c017503166a40710002c54608803990400036910400840000380e840b841303400c500071b6102c00440002880d81d4401009055605a00c0e080010449240000040312400568442d031070400d010031321060300e1424444560307105805030054000d051401240f40031080e601d010007840041d81d15540286911540c0c180c4229110a007400d016810403000520b40301c2486819206100c4c04d0347d01920840d41329040e40e00300b100d1381039542000982d24440d81c0540b41c0c01030220f440e030300e0f00400c1c1e000d441050520071940c0900003130380001a020348a49044021902038820080f03100c40c18135010800f207078200b20690350140c019140b05000100d40f0700d5034401005150041030300d441c0307000c02e01c0120b6100101c000c1030415000c01d2901403a21904201540c1d0031444035283c004001d118605000103540300320345030304a030018000306050b0011380e0000b0342034034846c86a240168000f400300001d0020a9229a4008006540103070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 948066582 1250 948065332 948065351
    0x3100506091507021f030e100c0e04181a2a070209060f1c060e011a010f05120a020711090403121a09100303080f1006030e0c0d05030405010909 63
    0x914100941c20300b40300c045404100541551210310002000a20503009100d030070a060364040c1c010807005a07a003c45202c2c401050b98400740c60711440e0070070032468490300b016503820410000038144800c5512200a1100d9071a00001d200800f95140ca0010036102e120910b4250110402000f07070010f6425000c6172545c41801049411044819040e01a181b440013560303000d022a01c1d81c1c0001c00c000d500001000b103c116410a602081c0c01c40501c2403106004007005105564265242c0f0b0030301c404c41c4800420f0012003903000316415403d42166007001410000c0c0c50101c000b0038007040702e00703444241c1c00240c83d00070400d42c20408050654100c45034403041c14541c074010301d1111985c4c8c0100c0c4d81d95503400320014400c050035010640500042030f40c00149400d102d480410b03000c6110031408076000c000483d510b03c0389000558815445a00e84000d01c520f0079004502900010a0007540c50182800d8551a0b071180d004913a00180030703c005583e10b6180070001004800582c0c04540c11714940352004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 948067832 1250 948066582 948066589
    0x20408060717070503040828020c01030e0d1b1e0c05120c090604020403141c1407060906020c01022206050702010e09040828020d0c0327090e030310050609 68
    0xc580003c0145040e030b84a540718034154280c1e110f02c4828000b0b141d43c2d41c0c203128081c0d0170408112025480ca90030b407000200c1060064066440781c103540412908030340311102000348a011a107043c020311511420400e115611880d041076519400c5030820111041c02030140310082c03840b0740c000d02c01680c0440c120500c0c036262a44030f0301804200d030b110b09140808030780c039503445030141c40140d600810f505024100b41400c10365600c03a10741c8410400003c820501064500a018150500c110124154030b007406aa07603c0c4014101c0042c21038034103600380801c0c52007160074400343c441d6060380313820107446150420072100750008907444241008000c2000f540141d81c4681c0092a642090320700124940396480c244200d03006003070003d80301c0c0c000a85a2080e0106d100e101416a0440742c0035216000c1101d41c00720303003a4251180140100f4001c2008014815908680c00c0e00ca0f03c3c051980035425481e801028159900314010500b02c0d8808401d2020054500416200800045803180c1c40d19440302d000c07 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 948069082 1250 948067832 948067877
    0x1b01110c01062c06090c0c10020714070b0304120c0b0f0709170309011b0f2003060103030c0b041406100e06090907031709190e060d02060d0e0f100204080607 69
    0x35140a040085d0105201e012400251741481c4120001e451000c00000400380094001240c2641e041c015040c0c030b20110400810a401603c08402c4007910350b07956a120100450701c1c1408040400c1850300d619400314103500c00c0503010b088081c1920701c649c201b40c00000c1681826800c482190b0350100c819264a80c4000111481e2803002c0c20000a000201000c0c00c0e4900c0c0075400c040d001e4262086440100294540108050b22240030100090700c18601070654a0f14240070050124404c0311360b98003ca01d03161003480d802845401700880c24030001404130709100c42614540c442107103010301481103a41e46010075a20800503220307001c00d4907040000c15a03e40c0310303100141800301c10410100c840703c0d03010111000004060000d40c0501d82580d00103c42e04524494420708125010119046191206001c108580c0080000d0304200c41e0a45020051107052000141480340320340d06a018a0103201005501c1451800140c6aa1601c00c0d032030300302200100008200700000840100ca01c600140 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 948070332 1250 948069082 948069091
    0x5120c04090e2a0a08010c0c0510020f0d050c09040f05060f03011b0c0812090a060c020a0b04020609011209050303060a0f0305060c0f09032a0111031b01110c01062c 72
    0x48a00090100c004130307546421503086040b0719428003026180b0190001700c0209003034464800c603403820041791f80300000c900582c01548001c90080100d55844c03c403a80001e60031940d8242074514004100000070120b03084001d0300501a900c0b00704101491410010415580d40300f40c009010580c40c021900f01c0307d255440441c002d000b414810f060511130103000352801078250804480300c5044c1101c40c00d6030b6621428048031018103040c0c10801d05803000c100071528660024001641740c4070b540c200a03030741c1c00c590000c50402c0038203000e003d80e200c042e01450080c64001c8000d581d6a040c070900b80191101142c00010a03540f03000d40030000150b0028045034420301401c010303070302e80d1010100e8004511034050f98a9142c071a00c0110651101c1d1105038040600f41046000030b02c206540c01950b80100c0c03c0c20310312854000340880002c85910602d0031200c22180c800001e801003d136100c00c500d58200e4115842607a54410090241c0c9001101840303000b100c1803001e140311040b86001c0d01c2000d20081 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 948071582 1250 948070332 948070393
    0xb190c170a0b030f06040615060e042a05040e0c07030c11040902060f0316110c0402030604091b030507062c12010501170c18061005120c04090e 63
    0x100080e510341207560000c009210300400b0740303610740040c90741a660b4420589096a6140c80e1a280030324040c0950b003200c0c102d828688442034140411402c00000b0003400070924404c02001490000d012020080703100c01c4071107a100c0c0c54485040922040c0f180c480105581004201000183c0100e9004030013030300243c0c0c1c00425413010594003004a8050700314081c0013500325102107a01d1115010807005588106540c1d41a00c145540d0300c542200c60107048400e2a0b0b10380c00c414000312440c20140c004517801031018002180d01003140d9150603403080348c4185840d518003945014401c2080c00e0040d000140001e20700003003400b8290f400c0e0b500100d0701c10303a4882100034020303402c1d80035120130f113420591080c40c000800071507035201a14a10b0518110b00e9250a01402d950003801c1d103000004e4100c40c00032a040200584d5450080c4a00c6d0f02071fa100a5040c800c0038418417061005059030540704114001c10305455030300c1c2411000c03d4800c45001500c0c1030b0001000019901803502c400b07040b03000044c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 948072832 1250 948071582 948071627
    0x16121110090f0b09030702090a020d0b04090b070507051213080f010c0801120204090f03030b0315160810030f20061c05060f0d0f0b07080106020c01051e070b190c 71
    0x44c01c083c5140315229000b0b400250034010440c141e42d880e8054408215440002c2c09001c009604110132500511402441250240081402c20b440340c000303002c03010b1085044a440d00d4028101d105260030140703110140955a03002400700100c20302c05402c008082c1030090025036440c0101401441c8140110490812261641c5065654540009002640000400031410300c1c504004000d4120750700000e01031720400503080c81c3d082d22a0600d910072001c04030074035940355514004860401000e007107600c01d43c110003408000f0544104165a65070b201c0c0100d06400000e1254551040c03248540603442100103200c4403803000070340d201840d5060304800380010710f41d036404005803d4902404409810080c1000800104403080d043c9107080b50040c83d03100015521850200d510101c00d00400c2c0043e000181c900d041540210050800b203191064405e0802c9202e82042c2025040a401a0707840002035050040c107854820f101040380c01407002c1480b0b4607008100243c0309242c640b00514052088 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 948074082 1250 948072832 948072841
    0x803041e0e040b06040c02073b0703020a02100903120f061d1e100e0903041a0901030c020705061204060906060b0a0305060a03021516121110090f0b 65
    0x1100500e4040c005129180c4210304050030140902d240494509000d00c0c6440d1409400b9400018480101e400c6a004a81c0b0038001d1003e00080c07200f1010400c3c0f40e0310341c1d00303041c0400c0751401508901c034400e550750050303c44880c08002480c00d0188040381c40b0b0700d4501020000401e83c056210500c004044d0804038071030400018240041c02654441458030680c083c1d001d4882c010032600fa0700444020b403810040a165281c2e1004618050b600300c2411036440504100100a10148a51041607001940e0400350f0f00d00c0c5980b1040480700088000c060b0005a07402c1d81d45c3c142c0705201454185d4170042031014244030109400384070301c801a01c0c00004003000a000c1001e15080030b4555076011200340328051b07440c040c9200c0c64008440450100e070030f080000701c903400d15003032150450707400415516103a030300313483c0d00402c0b64460555807241c2801c114000002c2456505c203a14181125620602406440940c0c0f034200004400034030955414022640301250b480c4520001d00b64122101c445103494 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 948075332 1250 948074082 948074129
    0x7051c0909091b1502061e010e040f02040213260709020f09130b01080c1e090f0405010f0f080f0c220510030209010e06011d0a05030a141501080304 65
    0x412004441e003000c1410f808140344203032504480c000e0003d5000c840ea66160300e098402401708181c1c0b0410303004020703801041001412080260801c0c050001c004008180c2c0e00810181e0703001566602180401010401c0074091500f500101003449a010012800401c080390303454542c5842035094194000c2651981c85030301c82c0031603c100c0001004076505181c042c4c00d003c042c0403680d1030980490562400078903080701201c00c407140560300c46004005a411408402c2c0960005184a5008284180ca00745035484511416005c2c18007400c00786065484c110141041c8200b6030071803080c9401c05c840c1002c0c01500061105202030044600032848000202d0001049400d04d4580c0d05807811f00c0e050006040c1e0075030702a02a40d0003a1070380401c3c2d81c1c0701d4114000c0440b003911b24600180c803e1085903414000c1503d001400700d401081d42c005c3c59510000a032900e825400140d901340141042d0350840f1700704204031000d017440701001c10200d624010406440c0d001b10300c54440e42031426080c1820307605 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 948076582 1250 948075332 948075353
    0xf090a0b041104150905010e01050a1d04060f021210231002030705031315170a0b01050405060c2d19030915080a0b040b0d020d0510020f07051c090909 66
    0x8050310132018507075440501001170942886004007190004c00007280ea0704068503080c054459a031801e5602010722a601d000d03030080100191015076a41c60a0b13815101c50340010170315983c0104280d045c03401d210580d4060b0540a0f4030030000b50000b040741d003d40e40f201d440044e81d40312003211407294076556003609038114822070800070103034000058041c5003c02d140003040f05844139080d020188590300b05068034840b448802d03c070401700c03002001410100442d080354241c1030040c5000c608141d039a50200c0c41c65080f07141980d880f40c03c1140b644a403000519490b824070b0300042200480c40c00c60f034402c65218400d4909007400d50040c0072400c414180611010b50052041100055100c1035801006108003010f07980e08280e5800e0040b130041078034290241c60490100204281d4409815500304034a1031024202140c80d800b80342d41c0b02d641400d05202900d1a0340900002940e24010303440d2580c280b440c40705e910727143c084140c00d00700190b5070b01845010a03182220000641403105040602c1110b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 948077832 1250 948076582 948076601
    0x62b050114040f0b010e01121b05191d010e010e090a0f11101106160c0209070e150307020c0108040f0b0106020c04060b19050f071a0f090a0b041104 65
    0x5221400d2000304916290707403c2e0520f004500d41091640c850006514000082c0b01d00044640190304d0800803030492510307056007da402c45400c6119664402251180d43d00c0c51520316000d0840d04104801d40480442c40010169070405902075810300b00c1c0c03200d410206005415180c003d00d00012001042049640001c40c0c2008039900c52a80500e0f0440b5194035588203140220011210010058090041313102d400703100c3c1014080d0707561200c0326020841c20719600c0d00e0402445041141c003680340e2040d882c1c01000181c2c0c8000300542c0502c2406050300502050340705c45881041000700c4a54081a545060142440c00003a20340305c5040c4210120b1400c0c40140c003032002800000383c41900000c000090b921301b65014800d0a5480c0c1d0020000c0c09901c02c220240300c04101c0540305244100020406008007a0541d400e0105540b10b140b00302850405000074408002c040c4010b03000619640380d0302102070001841c10150075900c0300200440a00024034644200303494050342e664130b030809040e0f03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 948079082 1250 948077832 948077861
    0x607080901021e012901020604062403120305100303050307050a0c060c110613030206040f1b060507150506010c15020d0f0b100212041a04170a0b062b0501 68
    0x1c1c2d00f50741050303078000c05030340d60103035a1000503c200000b030704240d10086205580c16000b405080e0780b0307601c9032406040d43d0f00100c51010544d01c007000c00e081914190031301440c01031803083e40000b0b420704082c044400141070b1a480c0e04a0000c204006a03111088075881186031504980382c1014aa0a99085001c0d4400519043c1814001d03114140d200c0f0031340804042e210100c40c4503494002540907001d941c440c025005070080d00005d03001c148000035170000144500500d00380c050540141070040150380c1c1004c00010000100c4105121115100b1243c5400f0710700204114202940064100075a14400500d584003da682c9504061164113a45e00030520310418031a130069281d08100505007642c2c00c074407032002c1e03030001c0d01058030004074800b0010303e2070301c400c1c58603080100c2600350014440320300004d14010080441c48002c4c07541c0b020b600d008110300500d407042c0f0071b2801d5803203000700070505401504c030085161290b4007400807000300c080d81c2c01d00b0152205a0b40c24010302519840384007055 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 948080332 1250 948079082 948079123
    0x10b030c13050d0506060414130311030906030115080a050c03160c05030a02012f0703110a020409121101050f0c21100f0603110304060e01150611010b0a0302060708090102 75
    0xb1302c03c022581521584d400c8034100000d81d10402d1a41c113007402540c00c2c5458006007120381001078007510442c015031003820700300c03400d080d00f5000084003544241c010f403c6040c280d8084641c9150072020302c68000c81c0b03841003801649041801c410b010b0100400c401c0f1400840c01011820a0103008511145a00310060305d42d5200c0199020303020345564038170441d0400500d130b2040103170181191884405290080447d14040464030f003101c1c00784070601185c0c0e242c06480721000059a03039100f105641c0d0b10600d2022240b0706008000340c44182da44c002120540d05140c20001c00051010401ea031020102c80c45946448908111a107699020714108041507446024001030340c0c1000740740c0c0f0482e5040c0c0c0780c00fa1896103500044080d02d403410840c10072103200f4004140041d489421801600c215000009001d0f40e141131300e000c03030310082c2c1d1040020868000311039614110a00814811040695000006038550360101d01c4510484401070501440810000c5240c0e2081c0510340e0f00d0300304100d03c0311 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 948081582 1250 948080332 948080359
    0x2503050c0c0109231906023103020411030403020a170715050a0c0c080306060313120f03060f03023f03041d19151d04050c030303010b030c1305 63
    0xa074915103510081458184e10840300141c1c000041c00d0300c4c50040300600e403120480c00783e5805000e500240115201800c076103032900c20304030302d24011030407009070055101121840c500610045034001c2c981d43e01c10141c20010000480d40005840411a03842111744004250301c1c0b132664000d0041280080c850b07540324225680700c0d603007600028015001440304010b004107900c000da410115282e801000304030140002400c9180200207180e00280301030b0250701c442003d6840c1091840c10808513004142c1140c1400e01031036042c4544c81c050014102100266421900051041507410501d5108209a02090f80841c00150424285c0348502880c00850550a024140d2260040e00402c8001c107108000000340304885501d03140244201400d0001023004418044003a00321740c448140d0801e074011000a006e2003113a0712408010003003010780510305180c44c1482c101f004007403161b4844d91040c4010b005a800010440350025402407034503689030041c404030004070704290300c01940106511900b1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 948082832 1250 948081582 948081593
    0xc030d0306030c05040c0f050f091215090c220b0301050103030503181f090201110d11122802070f0f0806091209040e010b0a03080a082503050c0c0109 66
    0x210980340f003045030020190700c44040c030044902e5182040c000514980c4860b05c813a00400c028840700307104015551400140d240800c1503d0030260406042d03500524035104800c24001c0c0c01354118103028080d1000b00551000541e07400c0d044041504c110300d4911002ca00000103604c15180020081c0c001c0c8410f60b034904020f000381c0c000f01c0c0c11000d442c180c400030500d0424042051041414140d00700881c2c00d655100140003800410700407410701160600c88401d149040185c0649001155201305000300c0000c03003035081c41441007109141c08424000d4030580c1e1000d01641c15104541451901c01c107241020072031920b422a444006080442c04001c540242d031381c00a17906461082080f105a5140c0000f900c4c0d540c81d01006026024005002820180c5850340003a12100d44110001c40c88540070070001d00c40c09442c3c5d1040300c450790300041d1000515001010654411120000084400008001d0300100040c42c81e032070301003654841c00148581c004d078050f44c2403010344000030003d140c600c0c44e05 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 948084082 1250 948082832 948082841
    0x9061206050301141f1d04240c03060e060604052e02010c090501021b131103190506090f0a090309121b050628020f160e01061b03110c030d03 62
    0x140c00001c51246012054154a10244000c403549145000c0600450300c0301b80d60b4402c40503204865001061240a404007141880075800307220911f0000b40b8080344d001d000c0e08840e601c1e4090a2a51250000c0200d039a641d407080d10100d41d8240c2e200241e080ca0b20380c001c0d0a408005081048010f10b038503c01a40c2541580022032143c51030b100c0c124102e071034400690b91081003006002116082d1004d8a130343e800d091902d0007200c4021000030418032140c0301c080100350000c407401c1896005803001c0c000d280d00c407801201d07003010041e15201079904014850400a00c0001c01084003184c440700000704051140d650310005180281d4040d00306800d03440c003442c9130505803510908400c142c5071b010446140034411250b03210303c1050b82d0030880b0901500a680c40c001100a1429401002410b1111450501c104885084016800d0320010b05201c030f01581d03400d040c0c004808021003200c608004012495100b9403098150a200010601e0700c80c0580c030340f01d101c1c0754450705401061400701c0202e415400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 948085332 1250 948084082 948084091
    0x7150c020405010b12070f02010f140f070f121505060403110301112a1c110f0c0d1401060f150305061005070b1003050d11010b010c030906120605030114 67
    0x41c103000c1640d8803040e605150281454814565a41002080343c841c050040d14113503904a000103d0b0310a44481220229448544d24105a110b0041000600c0041c0124a54401014242594000200980107142c4064a1090031b01a42c2d540d502c1c003a08904599181d004001c002c045503a9151039141060134690030301d6440e4004d42c20a402c441d00c00d03d0180965030111041203040380341e840c024042d05080c03c02e8444130925400b44003090350b0701d40c1d203402000940c0f088a880d814118401640100e160000314507150090360059420b0702d06c00c2e582d02e2000500f880c2c020198101011085d202c0500400099204842088842c80001111100803a03018010004c0341c400304181ea80c0e079001d0200240350310480c00001082045104009045210010340015070307030b0042d4164a88a584503032819046c02d081d44003240e85022031103440102405000800c05085c600009000741c542e030007610f84003440c040c030700038003c3c9004055101c007048d43c00100200340040081c800ca07402c43c0070b03440c0b9103001600d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 948086582 1250 948085332 948085339
    0x1e070c0201110a02030606280603020304031e02070902071b18180f0609050f15061c0215090103020c01060905090d05041d0402011214010e06031b1207150c02 69
    0x1820807041d49010a07003040d0315070094060040b0755187c0d01040301c100d207160100c490390044200048210ba0301d40003900b0107402c1c40e480040c2d503030601e414042d182108c45058072100154442c1e011102503030120b01041161641400540ca0390034510b019400c804144010314100c49444000080d0701c000319214406a018500d400c0000300102032613402e1501180c0c002600c0880920408800a82987d010300c0c0c0850080065465000c505030380c050a1087c606040303403a080468050201358030f00100f80c0d001245d0700704d40142500d50980d0206041c0d09550b08100200b40340850501e001d070340030b0380440b070030b00d0300c0c410007044182d440d032810400800041d180c1404c684200b0380c1002c0c0b03080c0900300301d409403402e5104810181405c1a02c090031000c00420880c1004012140130740b10030782c00c0c040c40c07851441e81104401550b0520121010341035000b0074191103507000c00030401004e0702410a0f41c1d044402600c020036a1074104c1601403400340283d000d809104025000705021381c0d402486041c0c1b082c801c4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 948087832 1250 948086582 948086597
    0x30e190306061403060c0c03160309031b050d06090519050312010b030705041503020f03090307060c08150d080717040f060203040f05101101061401080f010812031e070c0201 76
    0x1154a1800d069a2200c3d0b1500365015001103581d5200c514080c100180d00141228a41082490f100c00c19a141c614203d002c541c040100748100200140e4200c0402c100d441b885003070300c0c80d09000031841c48069102400c400c1c0c6d1011400103001c011f0003201c040040200710b00c2d24446991411a549030310440310b140042c85448000714000844d90102c90107034019503605403c00341054003044507256a03800e16800e056080117004c10001818024510a810000c0a152901800d0070b211065a8203540114100b066440420030700c42061041c440c501c0b807080e1007003e0900a94501014544182d4502411380d9204200e040e5801c1800c00050044c0c0b040c1c4400d03503c0040e0390302800d90380c80c003850240c0d82c000c2290000078801d5041c56000c3c884401c8961410010b91544800b90908441c810b420043c00480c075400d1026440d6040440c4079080365164a0a06056143c17038403d549947d420124142581000004152210400101c100b00880c1d000069011810030790000380002c112098201e0110315031 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 948089082 1250 948087832 948087839
    0x1140112090c0b0d06051f08150a0b0d1d011b021c0302280809120301080604030f0210060f0509070503070e120106030c09092607020409030e19030606 66
    0x6004088140d540007003014503490410300d9403c0107802120307081d0314459075242c0004590751280b29020600700b58101c8048107118041e8020503040004000c0d140040030041d00c00f00715150709403403900301c07a07001e0303085500c400e04c181c00003024020200c14250480c4010b1403024640a0662087c0060020115141c02c495000001070383c480081120f42c10440c148403030003184003070180e0020198000381c041190350b098840600d0080d001a03000715031000412410070403600784010041c0c004416040340c0414210342c5480c1c0003965996000b0402020001c4001d14070002c2c900810600701c0c841341194042c443c90303441d000c00390314141440c8100b034800d69443c0007103086603004001301c0740141020703600c0300703c8101d4150134005d8405500e443c4c00d50030365945e81d0001c0480c1612644101410341c9500108055003581088440030792814000809103a0b95030204070700310005000c8560469055401046001b503a040c2541c81080c44144542c204d94202c2c0d01d030083c0807110450800341c92151008102d920344 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 948090332 1250 948089082 948089117
    0x3140103080d1d030a0c0f0812042607020d0602040b160b070e0f190503010905060603010b01180e1b040803091203090109050112020c0d181d060f1206011401 69
    0x2100d1841c040e141c00c1040841e803091300c61801d11014031f0192081c0f204080065450380c03401e1740140810850b4071a00b009200c10011000c440003007812200300e5250b00c40258000c0346032584103050340240b04c1d1814508500c08c021944c0c05803002000e44111241e2038801c19034088910550740e900c112b035003120050020b0611802007500300c658100103050308101c1c0001a09107c2c0300c010307483c1c00304046140b10b00005425502400360300301c203e22510107041241460720a260a40301d00012043c1401100c80c60f80040315202d00f1804200c4e9400c0d54081c11a407206002240400025841040c40030300000713001c00c3c803007000001022840c10a440c641c146503e4034400e05c2d00c0b40109080d59000a02c003c100b0080e0750b1003003840151041319654010f244c010441d10503460950000c100d1000b00c0d00c0d40c901d201c0c00c901e880502000a00200c40b02d41d00c0c40544405c2260100d1006100a00c1008207105410658440310129200c4070071907801c903040795071076070b0503103040d49020180c0d5800180032500c82c910031b19 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 948091582 1250 948090332 948090371
    0x2304090f03141c0203040c0302040e2d060714162d02130906110d05010509090106031203020711090a051b070f12050c060c040306050c0c061603140103080d 68
    0x3c0c1d10ba008421261020f0000c0694009003040c2e80301c07020000d010000d652684140e00000628070020000d0310564043e9071072012440c0c40044907102070000c0040f803d040810400d521240c2440c000e00b1074203a00400301068007608411112103d00d1001d071000704200f2000260320070001e02455840b1820101001d00b10f039011460080d007084001c1e142000d18080e942210701e1641c85050042130000c0c203441c505e90150020743c056000c15032210010005030070036030314064201d00d89200900030a41592034021010b6851110007080580c0001e402c0140300009102809440d0020803201c000d050189541001d00780580700c10352010000d074201503a288d66076080303940e2541c0c07040c03a118194400352540b5001c10004060241401010000c420700380e60f0600109101d10302c02c080360b948450450a003c000c44600030001d0600950030071280c111034000241d51603215800c001240d4841ea5004ca0803000742160207c080d4a01c01d850f00003004124038000139000e4003400003802c020411014a4421140 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 948092832 1250 948091582 948091597
    0x307080403112508010203090d050a0909050a0203041e030c0b0c0403140606131503110a030b01030303020421200406080f0106080d030b0a0303030b06090a0e070201150506042304090f0314 82
    0x56009e60052900d013402907019001421050505080040c1c1c0d038840b40003034901c121800b4503007a5001080004200002d50520000340603d080007442a131140d171702400501c42c000002d0245090b44000816034031041086034041d640c00b4641c0007141d00240070b17650f0344140a0700c0f41846200c901c101280030a00500c2510f0300d812220400d0748080345140c42d0006501000041c150704001c00c0400800072031a6865034078002c501c6960011ba8640c40c110600813080c0c3d68403582c254403040c1600710004698002000700c600c1e80365183c100c90608075000024004c140503440441903003d580000c20741d0050640c04041114040810340748040c10f500780480c00c940e6001115540100052414004a0721a80c840d5180901c054040c518002e0110000ad9415040c0d502c807082418410042040407903080c010b85030040e02c2d8025078040103050100050b543d010386d000302020300c54002d450040004550f101c07100c1000e405001041041c01d9070070501092420302e042a0040b5000650fa4008000e400c011180b81 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 948094082 1250 948092832 948092851
    0x1e1513091412040611100e03040311040b090c09040e24090604080a0c0501061a09010e0f2d0a0803070b070801060206220209011e0b0f0307080403112508010203 70
    0x181400c0010a41c2c0d1060034020300c02c0740c1c6c81040041107000c1517501c00c800c010700301e0900071a1698910302c1e0080c0300030000760306140900c2c1000c80e800456101c0000c2a134002d41c4254085231550342000204005203099189007003584221a0029908505040340c080c0b00981e94044540950351462020394508041e03500034a40e00b41041407086092040f00d817510314a00c500300114807156a0035041d0070b800c00d282005010b4110002c0c0c89001981c001c40003801801e001d49a0ba50100350700c0000507822504003224a00100d4101d801588202c12180c003045000c0c001001c8101c01c40e22001c00325500d403c01e000440b0403910280c00f2540342401203402c4c50480302545d000b810315030780d066101219444600d001c4202c46070052030b500016a10064014040d000c91100840b01c20014003054104050039030000308482c9007000302401044070b00c0107c951005072400e20314034584480c90100e82490083c0b142826600a1221903102d441c01c4490460b0700e90000240b0440042d107031140c45080784030a541c030020 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 948095332 1250 948094082 948094087
    0xc0f060b01030c0302032203021219030b040c0e061803070305060a0e0a0b1909211d0d0f0809031c1707050304150b06040f0f0e1e1513091412 62
    0x3c4007aa4031f030140285103e4130607110440c030502030445554100c02c0301c04251100104503808070135814800ca101e550004c031020702c030a0b0700b100703800b3740b6255041640c0c6005074000a090304c940900c80c04d29108078407007d0304485580d40d03a4100707a07444202c1a03810780c21190411030081c10038a40020f00144068000d034501205488030312180d6503c0c4042e62020110b241c48002a1011aa1500103240c1c0c80403101c03540034032000e00c00001050f42d41818400002d01e4514442c0c1a06a100c4860785411564401c0b1951901c4010b810002d00d103008040c90258588110388000b40034040f0403561040c80d4079552294814030803240c032484407004048802c0c40c0040c0c010b100140200b0321080451802206808000a2007031190020403400e50054008447c81041d00030100412200c40340c1180050100402c280a107052910140096492a0140417850f007802008903040d99100002c480c08143e005002e070803282880c01441d009020044001d580005600c04422885a00030403100e1144010305142071 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 948096582 1250 948095332 948095371
    0x20a05010533010c06021803060f0106020d0c0206190207170604153318063503120906060f031e0a0b0403020307050d03020a090b0a0c0f060b01030c030203 68
    0x400b1011490040341c10081c8a0403100c02040092001f84030791800b101810452070030b150245450141c016200c83d0450790905d00400c0400da02040d504031041c2e561a003140c15401a00004902c1c0c0250343c40044d82e45c903071081200c00c45400041c40000c590681294020540103130340543d44132001100d0140c900041c00030303410504840343e40b001048200f1105103030349406154202d4036400c6140b80c00072000b00e80241c400d008103090025241c40e070b403c07000e000f84480b80c1040304402c12001071018400350301d0300804007011000010b4810001c50300f200402c03a901c400d5072156003610801b068902d400c09000304c070081182414039000590f042000500100807040c11104540c8115040c50481c002c80d00550001c00001003468a182d030285009500640d1110314905203981400c3e0340744444024140f04200f10211960040d0304841200e00150b40d07640c0300d500c180710645040c52082002004825440c80c00f10410400750b0245172007550030380c2c040080d5038030110250220b200c285c400180c034030403034070340c21 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 948097832 1250 948096582 948096661
    0x1502010e0706210e01020d0b0306131205040b0d090201120c09060509040e07140f100c02010c032a03080c07020d1b0b070f050d05030f0a0c020f030a020a050105 70
    0xd0f400c030b104680f50428801801560081101d01002c5110107030b03500080c0c445400341e100d0051118014045028103084e0900e0560702000211010000b064442c50950990803c2c0c0540255401058850b80d140d5449441c129070600420184604034042503110700c1030101100a03114815038880952175500d0900c1c100481541d0b990002801b0365803094550070302c080104414401a402401c903a61074882c21144d62042040e1110a1040035000c2c00c0d012224800299121017101d032090b80a0815001c0788201d41130456800031986124594082d8400384965000030010007a00d20754004d565841e4151075480005450344641d140c06503001c41072950641c041580f4480f031903060074074180740c3c0c5a000d03070741c000c100e4068000304011f640c0440440c0000080c4902400004260140351615514529080d04000c0e00310102415184100c1e50380c1070210340f000d00801900d1411801842102e8845460356030095075a051520300b200c03294204804903110b40505003090650b1038108141542000d0402c201 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 948099082 1250 948097832 948097847
    0x40506060c0a0302010f06080f0601060503070306090603030e0a060203040b250605040803040521032a0c07080712020f06130e0406290102030301050f0f030102131502010e0706 77
    0x45a0300840800041c0a402810041c200b00940f090b00045000c05440300264102c2c4d07050707400300c8050f4224100d5104c5010005c240d09040d00c0180c1001600c13a12004000c034021300107600540d601c545484004800d042e003122000341421011200c801407152540d03000c070f072240640d1046241030340317040c04100b1720511004420107249040501c0309840d9905920303281c050340d50a6070b06460302003000040c801400802d000d0040c0201030043c0c2c0042c01401125886c4842c8001881803134840d01071800103604402e032920304c0444615403401240c075203010041c903030f4807082103108146031841001400030702d0500310000301c00c02c983c004000d101d5001030071003405581d50040c10380e803842c10b000c1240812508501d0f800b40f8081e5000321000111400903a03415000341d0314201c01ca0441c00c24074110f580d41689c0c0002240d054550542c0c1180304d154400d80407400d40c05400c030007554554000b041e000740c1744003201c0e50388003144c0444000340c4440c052280c060b0300321034000e4041c0381c1a070090b550a01165024007103 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 948100332 1250 948099082 948099091
    0xb0f010230070b010b0403200a09022203060b1915050c07080f0a060c1701090b0d0b0901090c0512060a05131b0305060a0e0304210c0611070e0c03060405 67
    0x11503140c20480c0c1c3e20014192426001a1941500400c1c203005000024148400d00204400c01c480700007110f00c009041c0030440c1c031500e03910680018040c1c100c0c201d01d0240313800c8203080c1940e10302c015413686041409484c2451055005020307002040180c0d0000c400210300302c80d02d118190140c010180f800311501c0d40500603038210380c880c1340c07400696803404001e43c80715410800c01070705010b4544c3c6085019110801c480c88108500c5400e18020100e011000904583c002c207400220310ba07401000c1010715281c08402303040202000d0401c2907048042d001030b0b0400c0d22501a8080c002d03114801c100c3e030590000c203014400d5120b0b0001445421099020b25004251640884042007680e900c1c2c12400442080801ea9907854030010010483c0030040d00f80c00140c182c03002d006100e041040b9650b81c0c017440c40781c1e030200300d1214100714411590801840d24290000303034070080903441d17100192003070b5002207410300c0e40e22481c6400030385104412040e074022081c0f80d900728070355101c450402018110141 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 948101582 1250 948100332 948100423
    0x20f0103090c0e330111010e1f110c06070320030a020a0305060102010b0d03230309280f06050601090b1902010501080706050a0c03030b130b0f0102 65
    0x3540e80045240c621207680142102c925150103440c0c42200e1410007600202c070204c22244102119000eaa00f240081e1203200007071030700e10707840e4049105441c0505003407002c0244600420001d5114201e44824a00c11524904001d100098005000a80920800c85404116007001d0007260840e8070940185582000042480407121070401640752554000c1c0d502c081c0d0160b0004001c000d030354060080c2944850300740000c10844a10201041c200c011a00c8001d08208205003e9000f003071464a03034660940e0b180300e0003a00c81c40c080681a90340c84503c29142001d05a0313281252700702c02c1100c82003d03025400f10145000071400c3c0d0341c01000d4140500b00c2814061101400b10790f0b002240701900440003070040c583c80348040c2c0c1c0b10181c211003060300f08420b0b41d00011018407038a50418200e42d2800260b250515501c4c2807401c0c100c000705120354000f036204140c000600d83ca050a50052000c80c002207920950b2a20f88000590f41c3d1420b541d09100f03d40780302c40081070a04401102d110300720a50310b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 948102832 1250 948101582 948101591
    0x9323a1247270c030f060406210302070803040b04050102100b0f060a11060c0d0c0c0215030615040b07150506180a02070602070b04110109062f1005040308060402090d020f0103 77
    0x70156408044084850f8603004101108000c12080e20b248140e812031410b64082082c141880300302030f00c80c40ca02030b0182a200508200b102094400c0014100070460303003064a0316940c50310748410a507481441000d00521075184850b00b101d03098490901c0c0c104004020a100910460500c45a40c00c02c0e64401c00703020031014075145281d0103100c214440c401c6002d505544514040c6a0b80413541c0c07481002c0c0421035405081d02c010b0301ca01ca404402501404081b41e1a0f665900000783c2d24180300a0f5070103c9240440c001421890340009400c0041c86007030562014240340c08042c0031103804480d902e520042070b5138280b404071650b1621680003651010f001d80352a8464944074143c1e440410704941c84000441080305221340d059901c038100000340391241c1c0b1149030400080240217050092160701c00382d40e03c84a2075112910099500d8064002074541e0903842e01044401400c00b2201500451000302c009540c51606100301c841f900f0000b4100d00c014a500d40a002c01c1d01d201034401418141d45 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 948104082 1250 948102832 948102889
    0x333070504150302090612010e07050c0a020d11181b16170d060f14030f0303040b09070e040303020a0e0609030703030309323a1247 58
    0x5400060250100007c200300032540740007003200391100300030240c2042280c00e10410003a07590206541d10f0485d0129420107518100341000b070440c0329008025640130001001a1050f80f1014800da0702ca8000c00c0305807000600e0841d1a981c20b8480e84511400600100062000042c42c0e62036200d50001850301040c204410521044125070b080d0300580c1e8009845401000001030418440d010003000390098803022003000300300d9940e808082c100400c11032603040080c038200302c20401e05006025400003801e00c0e052a0401500942c4803940c0140010303aa24588103d90900780219108203030080d000300b10b070030720350f440482c024880134508840d030002c0d000400518a030018050a403c41910000d54101202c9040642c07400360800c10010b9031100075030450101020300000c907002a12a070302d44540b2a401100d040f111100441a0604803505d4483c4819500720180b4150800414120b419607040b80345015804080008410015072408000d140500a081c612091002101e8422201e0850083d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 948105332 1250 948104082 948104089
    0x30c0c06050916080717010902090610050903160303030b090601080a15180c121815020d05280e0d030c0903200103061e060e030c033307050415030209 66
    0xf81c1c07044c0300d0340c0d0054200380503500076860002c1703550341464001c1261b1061076000c150420070040600b442094020000b25a09008800311210084010150b5001c1003204138141c0031503e40c0d0005030000391400748516402d00340420440e014a00c16100c0103c1e03940c40d011494054000800c0183d1114070441c00025200110780f0701600ea001d802c6400b1078101402c8070010031f100d0381c0c07000451801c1c0c1001c3c0f180d44104040031001c0c000640143c44200f20380e075000c901074041d00c144c0d48200f80c21440d280404c010010b4070001181d9918001e50b0b0281a1708101a200c025145800703001001ea1308600c4540e010340340a86d01ca150021082d0600d0131380c0b036580c0c0c0c032021180b403c25040602040342e03284010000b0741e4580302d03010190800d6450581500d8914000c003030001c80502545040c0802100080991f507420460903110304001400c80d150008a811540206020b020724010b1111025640d44045001d0682c0c1c140b02e1210740d95564205071820341c1c0c80c1c600004c032424030707001d250382000901c06545 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 948106582 1250 948105332 948105373
    0x60e0109150b015a2a05010b031b06190e0a03030e04050a0e030316030605030102040b090f03030a2a0c0801090218100e090c0402040806041101030c0c060509 69
    0x301c0d8041ca40c001e08006070107100303609051403000c1d043c500d442c04c005880c08010b000e20004c0d03502a1802d01040c2000110718010428048000e54075a4841100301040000540040d444400c06905483d5007a000c000240ba06440c0c1c40b04103540b01005128143c18440320000a204845003454440741a210450200d006103015400a0b00041c20901c071000700e90a01b80542d60f08130800f09002c0002112115a182d03c030300000e02380d65400c0100308110180d881c0310390048009880c004008540c0c031559420200c000d0380c00010703414050300c0c00701c0044106e441c001c402d0310640101c81d190402160f043c18080060103c011218a2440e4550080c1101040a400c54400a00508000064405601d004104c01c100d0303003602c011031801a144c2007046910010000d0380880704500c08e10b400c0c03a10360600550038100c0a90303000c0d0304148003050014482c4000144a03001c0c500a00ca071020f0002c043d0f0044003034448800c066004211401500720004078194000740c3d00c5900541039813411030400c4400004013 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 948107832 1250 948106582 948106637
    0xe0a18030f0801060503060a0303051c0e070f0e01080d120e030a081f061202090a1d040c120308040b0c090a06050a0f0203180d050a0609060603060e0109150b01 70
    0x1e4204220924140e0b0020308042c00340c1141d0600b1400c601d061400203e9960090000404121012880c51138552001b03400c1c202d0000c0d0404140304542c03206000694134040b070f12590031400004c2c0320007e04641800c45150607120b80b0740160100c982010800d8a038003040302c41c090307401d50340e580001c002050b05101800894038a5614500281400c0090140d5689a4811500c4640340303034204105064010410951062031030001503112070480d000111804915840590390400380c410748032164080300b9120748034a209003543c4038001c0e00c50408006649010310b0040104800402103404524251a20755100b06804056450310414401240d00034200741d01c401d000c603402080740801150007404091820b03910b80300950618100b100c000c200340501450550082d0600c40990050140c00d000c160342ea181c0001c0103220540d014540318004102c01d11095a203181317007694894041d40d041c000c41c41e9580d00407042480340160b0038044002444000c003040d041c0001d014103880b1044a0031400ca10f031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 948109082 1250 948107832 948107837
    0x140f0306010f0e010c0b180f01051006050c07031709060d0501150c030c0b0c070b1003060b0a030f20030d2105060d06020c010b0a121412040e0a1803 65
    0x128240354001402031496804442c0c1030116400d1210101d0741e0290702e010009800042d106040e4880a4038088100c800100c105030601a90341d440c0e6100c50150404e9000301c5803071041001c1c01c3e64801045a440c010802c0c03007085d03600002d8003000490320701c07000721203021701c0e8104092510410100103065507100785840c6140790340301c80040011404e526017244c110000c80c2852102d01015980090002083e003100a00500018000c00c3c50a00c440d81901c020560003c0620802e00b002150a40000750a00c0203d4146050100c11500c0d402c08040541c112540481d80e0345500d6450f80d1030396064101e450064940640514541c02c10346c1e07003004a089044800e0301d8056540c0d41c007265100c1c06540040c1004a40d500306800e008458641081205045030024001a22207032807240c800e0240c0f10b40101daa901101c00d000104000d120400f4502c0514882e40d55080050803c00d80c9984440c0c1e280c500c0100042c062004028061480c41d98035407110f600c00380040e4081814009622207400000e05070700 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 948110332 1250 948109082 948109087
    0x9062502030c0103020f12130602031305062511100218042901120608060c030a0f060b090622060305040c061409302d030415140f 57
    0x30340c1410b001c0342c0c102500a01c4d095240508030340c1d50000522400fa01c01da409100d000c00114050100810000c03683e5000d5000e42d40c2c2c1c100a00d50082868503080150360300d01550700481d090381050002c100103400b2207804c19490901e50f02040d2001e0103038200a1905004a1582007000603491000303010458003408100705600b045020300084a0392050a100054100d0000310790601200e21004034902003480d000304020b65141e081006000c807940084458801e203801e01c10585600740186209510f044410440542010703094030541e60b4903c10450954000c1000d01d07500d051a4005000612000400f0703048100f41c1c0d880210103801c10ba0081000980d0780c02803000b04000c041c2c04400414007890040e4003000e603000301c4d40040c490304022a204440c915041d051040350240c181c01e0340009981450126001c46e030703000c2d440e4503501e80c580c0280d08050840c4110074040d40d0701c041c0c08801d550015401d181c28a01211211182201840140a25008055949404913004080c00d4090740c103181d4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 948111582 1250 948110332 948110407
    0x170103030914040213050904030c0602120103170304030e0f0315090307140604150b04180605070201050603010c0903021e0312040e060411070609231b1002030a050906 73
    0x16003a168144042e48100e0041000603840181c00c0c0700e03102582c108039a00882c54445140a48040d0003040b002000d180c004102d4645070448180c0d4035048074002c0800c030303143c51151401d0004910013210010b01003016001c4003180350900c00e403001446100070f0b04407007800780d149038825407082d4120b451100c142e00000300941041008905440c18001c980020b15150505a442210740441c1c1c04c07002c07100c0390f40c0b844c01c8042559207400c0b80e5100e043d6400c07403070301400c41380c00c1c5100a090b0480304c200c055805c00c008198641014800c42c1402080d0342d550505090455081104980001030b03102203440422904a010390350907c060729800502c10315541d42c480c582842d2a4410500400c064402e034500420a204000c411085401c52036011000103008c00180c035241000020074100940110a44d840c094805003000030b00c6810306104005241d0f52103005801c001c441010f071040e000c0127800c10b002400350103000d03070054803103000c004020f9418036a8058602c1641080355401c3e42c4916215800c05 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 948112832 1250 948111582 948111599
    0xb03070906140603012402010b10050304030e030c06090621010f060909020307050a11010f021309051302061213080a080106030b030c1e04090f05030a0906020d080411011701030309 79
    0x6202c01c0c4240d62142c1990314041c044800c04202c07600f64201c28400010145046100394042e841d196001060a00748000901c00207259030411a401c8010989104582400d4500090b041a603010020702c40c81c50903011000f4402140c0002120140c449904501e9580d03045100c00198040c0c0100d0b4a520181449e00500800400040d44509a458410010305c00425402012500c0c6030b2900e00708290307803e00c40740c07a4030b0050680c20f1251001c5440810200d200d80320240050003142d8484d0018402611055540c0c07450003070307802c002540000c0c10447c040c9803212040074181c1c0040c4511000d1140401138407040c40c654071a4074100000b8400c1001801040d0305841001000c030380a0700117000551001b0702058100024100c602c656544205200c6141d503078076003120940982c09000003022103020300d0280d640781c0043c0f80003c082146200089459440003402081303001140d0341d12b008c5903d07280c8070032040c610008401410840d045440d41005595005028001d5100e5640d1800081c64110f04 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 948114082 1250 948112832 948112859
    0x1a04080604060507020d0305010e0114031f060f0512061f03050703060b1e01080403050f041208042c0a050c0906031801150807030b0702010b180a0c110616030b03070906 74
    0x89007d05261200601c2511440c1e400e041c15140c000c40c00c4002d540f0164000781c40c0441c186511540f602d05040c0000842410b41c00c078600320f8000a030003014031916181002003c101c404004501a4011400280c0120030403c88014500e02d56408110301600c0c3c0e00c0c0c00341010226081a034115131074080c10300c401c3c01e0401c2020f01312200d840389a40400314880c002040740c2d0010700060100040858034910a540e000c08a03002440702c81c201107200c0131140b5015413140c1082c41a54501004202822141b02340c2c3c1200402d01400c501040c01145e450002070230003080040e107c04040c0c2c07003c2c00700400356103a91008600440308140c01d0302021042000b4a07094401c0401081400c0c1a00c3c0b10800104800040f0002030741e5000010849079565110201d00600c500b0201c80c0c0e00000004407000c08442ca01282401480f508005210104c0b401c9001d0714980b80140d42c9540c40d1340054005544078039804c1c036001a4103000e15011070b40d071f080100024a0510190080d1102542d601420007045081c0fa4a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 948115332 1250 948114082 948114103
    0x306040309290a0e371d1909060f0b0906060c0c01050304020414010f080d02160b03090c060d06060e030c0a032018010e0703090c1a0408060406050702 66
    0x500e10b412200c510641c0e03a02d0040788109414050290f0701400c0a680d180b00b50002c1d100f0303040c06490380c00701e030000e03a42c03891511044a81c107000c144000410030149010300354803c0d94480791b00744029200c0b020b4540d800c1d0f0441507200101603480b02981c0008215010310305003e4212500800e664011908200080e0405005284500002c001c4002601004a103806460100b428455140d644900204005d0036000c510301580324010300012490040340c815032030554291a00f05c85103000001010381e03a800200c038a04d619000700c04010820401d2150065900416440c00d42c0d040004010200d00990441d03840c0f154480d0b114001400855840300c0341c0c8081c2c40c8103c000341300c0d00349210041a10b016840c00083c0c4105001003807800461a18400f1800c647c1000d403609814841c0d0398410075000301e0030b00401e242c01100d5008070f14914403d016807111250002508400e052038035a03107881c4401c10f01800f02004c1c905020004002c0428485603100c4ca004940114080ca0b0040c0300a0800d1020b01 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 948116582 1250 948115332 948115379
    0x180c010905220b040c0c0c090c0509060a1e09080d02063c1302090702060906220204020c030304110612040201030902060c030a112a0418020306040309 66
    0x10051556480c0d410410310b48080070307540c40701c240810360001800c3c0c2e407541142c10a08013034041d580c1a9018142240c0c2d04d00401c500b814107030300c91040d03030103965a00c4503240001e1014031000c0404c9c5080c5004001c04007407424514040380f071490660030b60607076000540300800c005001c10404071009102c205c02442003407000c1d001514008d82030325140c000c41c8801d011b04069950100ba0352105400005001c07000c0c3c00c03241413662402100c0c90502008080c0120b000e8070524021405860000030701038014200f003800f802c420f569011603100c0702489031002400d007031402510000075856a1000300795200d034a10240d036491405082c01e80311030419140140c042e83c800c00280d405601030b40380c01c1381c000c0d030709283c0842c0e00b41d054000998980100d140c864854000065518100ba80245000c512000030000f603034081054040c80078101017108001c1c0c07040907600d80c2800c1051401e0f510403611181d042c3c3d103125070140150042480d1210845080700400c07001081070041942a0f61600d071084a00c5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 948117832 1250 948116582 948116597
    0x61e170d050d09081228060e24060c150606070201091403030f031e01061806140d0e071a0a05040504050a0e0d02150a020412140114180c01 61
    0x3503801005441461580c0d00c03201d40d5880504100a511000c48440c1000c0390720040b81ca040020480201c0e100e41c1040080b800391b04100c000d8044d03020b02580c401c9882120000c142503481c030b4803c410313441030650b82d8152489500300d0300710b040e95401c01034406214000020481c0a02e00b04400c01aa5400b40040e881038ae070600c2401c0040c0ea10900100aa4090303c9030ac00f180e43d50310000c07034607500890120000306400482040360340036403102000c01382501c0b00301000a0340d03652603040d01c49a6105e078481207510080c40302486418080c4840c0c2403e81703c180103452519011308101411a1003100d800d006a0304911001c01ca5003682560300d1412203071001b80706117012481c4102a06610407441954083d54840d4000f40080e103d95015404d500541c100340c2d401c401001400945620401000d13407424070108021400100e514405d0701c003a1f40241519240c104159250340340720306464140c2041a41d00d43e11412000306520100d503011b1414600c01c00304482010305098140030720b0041c4541007090384c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 948119082 1250 948117832 948117853
    0x5010e0106030b0402120111040b0a020c04060f090b06070b070806030f030a080109050601050c01060e0604060e13081c0f050103030f051903110d020c030405040e210d061e17 76
    0x8240f1255001079048665010050404003018090300d04a410b141481001150014082129800070411068941d0980301c40c81a8041004200c030094007800c1c01140040b03105000300809684085015040202124100010f958440b40d0707000b02110f017440002c0c1514140900c50504100c00408040d45c04095410000d8042004081031414402c4124058071480442c01c9a4014011502d90705a44030007882825121062010461002ea0304180202c0c942103000942e03680c00c820207400f802e8108401540f03a41e05845541068100d4903080640c0039140301000c1c81030341c26100b030092540420b0808a9103601d0f40c24050540c0010465440a10a041045e1040c0808800c2c60903441081405c0c0080e60407003541050015000c0c001042402500c0051890345004001001d8400c48034103c60078044602d006019039220b050400304401c108120050710040126510f01920084000f50000074005035242c204601c0c03880c882c0c3c070f6500d64100002c410702101c1a0a034900c1c0320091450000d00c10b0214 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 948120332 1250 948119082 948119093
    0xb1c1b020c13112205040b2227030e04050405030d0e160314060c0702090c070204090c14010e0108060d0321110a0216230d081605010e010603 62
    0xc5004507244034221001c0314802d00d0440c2d6000521202030b00800a071070340319002001c400c0c00a01c50704501038070003001c400541840c2501803091500302c09003e01d07014045a0350b03407210303c400c051420b858550710707895440113102440c0095800e0090200020300c1442c40d46c1005045500046e02e41b81c021400c190821000c00c0340081200c030a1707181400c00240c520b50f403070000e0703040c0340c0d01010b1948181e8600360000180407401103545581c0c4410720a0ba00c4580314042d201c6154418100000d421110250000700780307c4070603018001c220700142000c42c1c800c09558900a0b0141c6c107401a04440100380201c00e40c0707591004029103006002e08004240d8180480056001005242c001b020061100881c0780300b01100e08800b09400078140081c412150101c985420307a0f003003480b61000611482c03100360803c4c00e2052828044032000142c0c005221a25034032400c0c8004100402a0410900a1500d0019a6480c010460340140c0c00d5070404025803403601c00d003540d00603010810ba0b6814258240b001c40d0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 948121582 1250 948120332 948120343
    0x30d0609150510030b04020a05070c051002060c160c23011701140d1406190c080f0a1d03041e030c050418050f1005070f0c060e070b1c1b02 61
    0xb1000c403160034a200780280f044014207002c1d20b103d03030410b00100c1d0415140f50400301904040d40314805166000c2d8844041c0401a102025003000591041010800b40c540b6900180101e26820100900c001360356241c0401655181c1d1001040032903080f02d000b0b41e401c500c800006401070900e000002c454242c52021510841030160760800150700c03c8281243c1e490014104100e80d100c00d02e003040d11074054403251500f0007160b000e0302c181881e011248101240d840360b004002c2903030715042140d469940500c104240002c0c00c40034859070ba080140e11110001c010481e10081204c01565160b041c2684003081242d58110940701c0c0c04111000e1001440d070500440503182c0c1510002501144131805e40d001070912200a0702034007400700302074448031000c10030b0725000412000c184074503210090100e48681d107080a9400050f10041d403000080e805400003a0100d01c40c0003152500c1d074560b039540c45940e100c005007481c40340484e02104400442401010f6580e42c1040112614445510001e510354 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 948122832 1250 948121582 948121589
    0x2061b0a111218030f1507030902150903060108030f0415090e090115050f0306040f03091e2111240d060918080d021c0207110102301c050405030d060915 67
    0x1146d442c001741c069403107135000500362a00140306100072040c00141e07040541c40720742441d000303014100c004902071a0010441d42c040f651501c0c15450180341c00e0807150483d000103184820047c0c1e8081c0040c1c0d41256005039070090701c2d100b0001480040702601c0440d15040c0754000d074000c00c045240741d01540c0d00480c4140e84150055803e0040a40500e030488169216030001d6020a5146501610644080b450a010744520b03c445000c10f0610003803010901c018050001c0121241c2400320801e41009020b5504800e0220b80c481c040e83c0c402c0f560400c0d2030708007008400c5074640d603a41c1000403040900032201000311000300341c0b012890075241d40d451841810740c85c24820303400007000311a018404445448051031208210b468900500c0c2c9001c040c03058515042c0107100b000d000180310a40c1d0350080d054202c1c8200d0148064458601210007030704501c50000c5000c00c1c111071540d44c07030040c0c06854031a600c0b58001d182d40300452080c46084802540240c902070b07280607902d080b4284074440c00070a5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 948124082 1250 948122832 948122863
    0x703050309121209120306062b020a0c1b0803121902030c1b0105010f121406070e0108010e06030a1e061a0f0102061b0a111218030f 58
    0x229652007000da45403001034460148401e10000340c03000e54070107000076940280d01d030405450002d000e401d143c0e03155001c25a42e0580c0a5070070031498071000307a5200000310208840e00300ca13650f5100d01010500300e8001d05d40d1000403030107038003224081050420101041c015a59054040b080c10080740a6072030050f08040d03050301c0360140c04aa002c01c03080c5501089900711440c20755503494500444840360300001c10388464248040e6041c50008410b00a160598494051400210385000415080d407441c00106131340d41410899003130440f84041c48110300c83d48264842c11a90b80000b4001480004164000040c140c24070081c440e555070041002c01e030807500b00b903c0d10b0001c00c80442c10049030046840c005d04c050300d04140d108212015001c2d9903180d8404445000c0c010002000683e11004d040315104001108107404c1a80c8040b9500502004045860560811034044070058038004042c18032228101c2d002c16103496484800b10380d8552180141d001c0c1c490b90b100180f03059500c0c15461a485803 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 948125332 1250 948124082 948124087
    0x806040b040b0613050907060e0d03080402010e010c050708010605010e18063a1202010207110402070c2607151e02030f0423030105040305070b101505120f0c070305 72
    0xd1592414000901101d00d554108240e003465006647d1322005840740300040b84400d03030b0702d49291408441201c0c0c240d401d922250042e6445034011180000c4060f5024103005440442001240d001c100c40700150480400016030207040200250600901e40700310b51240c00c070951011041c819079000c15410080685458181d1010440680c190419410310131000034042030703c5500140a45503c3c01c00c0b41c1c0035034a039441208010004038280c0c80384510181401141103040030080c24694010f240380c038000d40e485141f01c2c0e21340c100402c5036a40100300c50800100118841c0040f58103000e540001d140300c0d4a1424103903890710000d880036a0803400141c0300d4030020003030034075907000340111011901c20661044c0c0c1c8640b66000342e80804900c0085c00066198800300840030b040502c83d090207039415071078550410056648000e80103500405891569040d0130000030190081d440012003603119031602e54841401422440c1c1d1024010518500d001d40c078018071940a40d14801c95039104e41600d01140e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 948126582 1250 948125332 948125341
    0x80d140906030708040308090d0912060b040203040f0309050906090718030b0c0a030509060601081f03050a0f02030c0d170c010e0d0507170a05310801020c070806040b040b 75
    0x9519019420085800410000400056a9201d0381c0140708610030303100d210b1240c0b210341246646d01c10344842c080100da2800300a100e804607501ca449183c80c8a110013003134a88180004c10300b681c0064904854005810030703030404041c0c110f2450000340c00151044c440929100f800146200c1000c0c01c2c140a02a00c0c0c201442425a800c243c94061900b000b103290072030030700c0503044140d540540100400079250a01241901c030001c51100d0059905a40307500041e00c414058099041000548014110f00b0b8100000043c2e024131440e9442805003200360f10340b00150043c1810000c1c2d200c1c015124040d83c0d00f20b1070028556134102d101d46418000c0580d22190714a08641c01450160340c50b0b100c9115000d107010f0702541c00001840c140740309080c0708006022015020308103010300c3c000740021490a000031a03c442070071021f4003103480d4010350f50940b0708040d940060704000941021a2994000440c00418001000400002d04140008002900e01034840d802c224102820080c405010303440030a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 948127832 1250 948126582 948126617
    0x2607151d2b050c010504210504080703030509030a060f0617030901021b0a09110c19030203030c03100e1501031506091203090b1306081006021507050d02040311090a06080d 75
    0x403409011404020000c50400741010009002c00780c441108505414149407481842030089d00c1c101d0b1801e0300203081c124110360701500d0741c1d001005403036058450304001c4004204036000f102d1031144030382c0300061054201151080009500700d40e40c4410340c805c20840f4090799000494505c02198152403403010140b000001d40001d9403544400141c40c1401900100c1a548100401240352100c00b103e03808444070b00e0210001d2144400078026030400d00000714180070f09001158005500321240c3c2d64a6142d210007038840600b030714801c203c200f414031494160b582503c5018103c5164003481801c040c03030880e000f0320000c1c19010701401c0c00c1101c0403e204141c0521100006005483d40280e1071701040a85180c5060080c850600000c0b290000310792001540803000060b03a03035540c01342c11200021618080b0010000c0e16540800604110080780c00c1898806000910300c03410034040759201c00b108211582d2809441d81200b0341c6000410070406400241c0100e0b190342c5401d056000c0821134410 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 948129082 1250 948127832 948127837
    0x1602102f1020070302071706010305100507170408030702101803140c120c160b07080306010e10030c020c03030f09090903070b0406020306120a2607151d2b05 69
    0xe0040160109001c004c0540101c0d005080d102e921a040070306200d0182695a145006e100c00390807504181ca01c020702d404141c000f141d0211403828080d00e203da540c8036540d001e805c2144c0071760300f05c08041b00788004036606100603035500414180602070711100040c85007074a555144000c043c002032040c0b00001c81d4180c8161808403000c501510030980901c000b000d25940003001c24201c500172065440000030b600c074660019100004c0740749080a000b66540d210907400030300040d0501a01c01e40c1100507035610460700e44141150b68000c181c15009c1070b8007030721384075548400520940050164171003665014040d10086442117502c0c0002d522a100c0320b50461240348000b42405002400b0030040c0403580d0020341c0108010313100f611802c02c404089588910315045d0040154000c56075060020802c1d03410380007007455100b121403034529103a85800f6154a40100002501c1d21062132440262840341640382c4503000c04040e22100d1540c0d110300581c3e82100d03081c06c0d183c60650403820000f0348508103 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 948130332 1250 948129082 948129131
    0x905060c0a140f091804050a020d02040e010501150908060c09150d050a140c12010b090a170a0302070509010e0c1b03070f02030709090c09021602102f10 67
    0x2820795642902c604201580d01881c80b442c010050b0441d46200c03c121000c0d01703882690040e014143c040156402c01402c2240c0b03800980e4841d0f2959100101c404083c400e00b4024916004c401d440700c0d960400184ca042d50b580d02c69001d9400c001c0c03c00071850000f404840f01d04104540d0000015024030030752a2a005288900c00810b16023810044148000d070702900c6a96050751902280d940c890401070014840d4402d00000c070301143d0010400080400c0103400003c8004150340f8459454080f00000750750115007449059010100340720915805000c0440503010a851480d500c0d0304089002c1c14825003d400801c460a0000d031602c0d04202c0e01411444101064042d0390395030005040c040c05255441d041a4400d01880c503001070300100078411050010303032025038200010b103040c42e50300082d0480420322200c80d0100d0752000c0107903036482c8510007042960701e604500301c0c00503102200481c40b03036a28030720a00141c50618248200042c41031040c590300700300498400407645d080441103d4291 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 948131582 1250 948130332 948130367
    0x60c1209121218080a11010207081203040c06050406020d0f02070324061e1e050406081b040504021c030903152a090b0304110a0b0405040506040905060c0a 68
    0x107202000540b45005001104640d1000032010a60290150301c00c600c1c410241d0761361185580700009183c1d20b003202085003050069601d0540d80e00101c5080901d000c603140d041c0500041000200a01c032865140540914604181482d0030710f003010f503590031000d0030041401400070043c131082c0d01c00c11660000c4c40d4403400c58125240c2900b00c00c01ba0380c26005041c0029820600040380346a108003140985848513203840c0440c0d85070002d25102e0b03a00040c601238103240c443c41c01040d0398a60340100320040c100c0000811052010f140a54a40000652020f2040d81442309000150703076214007070720f110480043c05c020020784d41d00c2c0665100c0020307030000344208001d060604003140281d1088558103603414406214412031440340c01d8590038010302c84040341c0600070074000b88103080090342c0c1c01440f610780350110405000020700a05526405040003800006007800581858080c20750081c80641d01170040c0306a580d1000e842e120000c064003001c00300460381d049001d21031302c040380c406554103 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 948132832 1250 948131582 948131609
    0xf041505030a0b01021b040207030e090c04060807020a1502090409210201150b0a080c040b0f0706060b1c180b1003050f0303040c0909170307080109060f060c1209 71
    0x141000380040d081220900402860111089802c0d4004070b20385c4002c81081190b0300f0084401000c2200030f4010305c2040c1d0420026007140c2000d600c40c00d05580c000c003083d050498580d4a0807800800a20000f0724034030441d002032041800065540d010003e0301c603600c24002d07846905c00008035000745103910002c0c0008034528101c40280180040c40b039000740b450b80c000d02041d540400c05040a946500c00d00c4414a001c124142019114040103500701101c3e084162400fa0b40362072490315500120640c0424520000e08401048814072a130f03001015010105420b10105c3d0810708100300404a045440a0700c80a03854061640f844244072225440034040e07416060580c841041c0c007209000482d21880760354543c443c406800001d0b60700c6142d012206007080c508000030400540940b003001c4848102002800a0805203900590f01c80d518603a55800c580d80b4190301c10003030300c9283d0321040014482d55010301170b1592003400920303641c1c0c01c070001f41100e20803120211105030455005000940c2507 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 948134082 1250 948132832 948132869
    0x6040906020c011515020106060503160315030b0709050a0b0901030e39010201020702130903090302060703030203092503060203100b030405030c010e1501170a0c06020106180c140f04 80
    0x64030700c5a05551000b07170b9001101c240303c0410390882c1c070729005840101d1401d10000d0b420910300c40c0c0b450341000407032502090704003440540c2140c0170600d42045450a81120400c020142d0103460741008110841c2c1003140a417070a40b0741078061052025080c100358507040f0207080e000c4108541a0340318807004210013103088400401c51211400e107400c0071038000270040c050303203507105000b41c440c0791360000e02a4421100402c2480b00510381d052048081c030080c1140000541d5440028040881c002c2e01d0150f0f603440d0118a880c2001311401041603210360100c0e40d0440c401c0800940300540303a002c980107035640c60b03121440d900142d503507001c10385c0d0900000402007044030100c080c041c046000f03002844a40701c10460b65032112000b0500c00101e0f0f10a00040202066521445917034000c00d10644003030344c1050702e80120340d0b185900284090303912001d0810a51146081034400602100010040300c47c0202000f042e5288450410103000004600580b103030050710200e800402c0010902100000c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 948135332 1250 948134082 948134111
    0x204051e07020d0e040b0906100c06090c03030206100303020717010f09080915040503150a0e01090c06091d011e0f030302060411040e1f181103070b0c0606040906020c01 74
    0x8010f002600000c0c0c00305654091820580101d40b0036078401080c1c004d81d5a501c80a010000700c40702e200354100300c18500c1940101e510b601c40e01caa5503000b12110503840b400c50601a00c4c0c02c60142481110300c0400c401003011944c003040740f40070759020000034486c05d031800703200340e024001040301e01480307a160003804403c02000b00020f00520341c00ba107050720801d40000e4401c6081c080d40c49125010b400c200340e510039070645100c682d6488000b038000010000980e05800c1d08590740201c08680d007216641062025070740018648001f040307114100c1c0d04800000134424242305e01031040451100050001c20741c00f5050842040103000394503101f5115036920b090007541ca446c1690151401d042c1100b6005190509008881707509461000401d100b03051140c2c54030240900b0080d80300e01ca652100e0340f0741d99240000c900f8511034050020030414441490826042010661044900c81810081c0d8501948081401544031a08560009080605080c240c006e48501841e8080311f518080c1d42068a04 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 948136582 1250 948135332 948135343
    0x200705031c02091002030c0604231c09080d020d140d090b010e0105191202010e0310020301050a050a05030a0321020a02100b030d1b0206071a0405010c050408100203130c03050307051501050d0204051e0702 89
    0x52a8cd100c035821590f940170700d034554502e5407051006800040000f42c3c0da034010404c04ca004e0002c00015890a1407865146040755031050040780c820354010010488094907031041d1f401341004a50000c845030304201d410940a0301480740c6400c100c098007110301035a02400b04811000301c0542500d05403403030740400304000d5000340aaa0b2068451640200342e500300f40d0811801d80d80060300800078180d180d20203444135003c021200c4d1841006100c85103921140380058119141d41c2d03001010440104009a4251209004001c0c020f51040d2002003025034840c528802800383d0341d000508020302c50010404c5d91082d4800509800c3c8500ca101081d40b01480456200714010002003005035400c90b4105c2d10b901c6584911030440e880700c184040300d001c0f50b03401150042e4414040b400030709640d65414070a13445960054405410105004d02440402d1211515202600c03010032a2981000c000810f074882c1c03000b01a020300c4c0c1d40d00000d584201078194005002e1100f0101396130340d24058100a40c3c0342d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 948137832 1250 948136582 948136633
    0x50d0b041104020c0624010f03050a0905120c1014180f031201060e0306070f110a0c08030406120902010c03030b132a0201200705031c02091002030c060423 68
    0x61b4050101e1000414010449540c2c01c14141e5800300f0b100d804240031006400c01504042250b582c400043d000104100a044244510042c015890b40145c02000c1d050000c000e01c6216620308240301018090040070f40241d001891243c19000d507140c1c03118042c130340307141803014a01c0c0e44400160034500240700c100043c101c403801e0b514000b160944009050f124a425a1944041942040d003050381318010002c01c041c145400313045584404681e140c0c00c07074150b200c0c0d200035000c1d00000f5081c06060307807009200c00c194a6071101801600120360001300301d0b0b1082140507081565828601c0310030741d03c40c24410003000260009001c0749810101d56010b5800c041c001400e0884296008c00d81c0c0ba0040c040c0001e048903001120f4082c881007003102c052540440c0080b917150200308106101c401c04440d54440c0c0302d007072410040e10f40042000b0311030120510311351181590300510601300c41300000201c0740d601562040301c224800141e0132031484a0846030701801424060043d00e2841e2408485610009 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 948139082 1250 948137832 948137851
    0x1e120c2e1503020f06130509060303070c03060f050108160b03060a181a01020c0108041b030c0906080111070818120a03171e070f200a02090f01050d0b041104020c06 72
    0x50302024020030046101e01d16114001c20751100d4208010b08e0b201524981c007440c040c00741c0386028101c0d82c40e0000d05041d80c00c103c0f151655000d14427007554240c03144501520b5403400418042c0b800c002484440b004a10940f0040180000004c3c0142c07122558100200024035030307024141c0303200b158035020f0084e0701c035000300041c1d484030407081039840002c00f417010320380684642046441e252510500c00c901c4070041c00451129481c004005000700788120000c0003100800983c50b414060801e096840740a0219100702c000d00c181008034690f407045030030301c100c1d0802d124545200180800c4000076003a14915403401101c050006041e04020300c000d4641c018a01c00c503440e52066440f03030303542d43d070f0140c200c501c8588036000031000360050403000007030035240c20400c011800d080310b14200c1810404c074010298120100300c10450030030000d002e8019408050888140d0306150100307601111450000d045c014940000c01c06101072072000a01e0070754083e206540c3c1d0120380c412070360b55401c00d55604e02c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 948140332 1250 948139082 948139099
    0xd080f1e0a080a050112140a021915030c09060810180b01031506210e070f150e030c0d030c06060303051b010c05031501111e120c2e150302 61
    0x8000f00e207110b803906075840483c0400245600d91140d21102c0030000c508441481840110303005a0f4a54240400e00141e03100b882020300d06091440c8071000202d0504400e1505141702010003540008140c1c0a44d120761a2a8005507201a40880c03c50329644c403c012092802001707104c0f816a40d0441340c500f91080e20103200c40b8081850078401030079940b04141c0080c00e18000c441a140c11118003c50483c9090f0010070000066810701d0f0401a40d41e020030041124094100080c6c021192010b2540c0d0050070541491085003001c070b900c9000182645104081702042a4101809014034031035003a040136081114986910b00034019030301a0328030748100180480450392101050158040c7d41100e950b68905548034062813004034011020f03180d0610018000d07104114008004058420a0700c540061141c00c18040c0c15040440503904c1440e00b400070020244141c1c0c00003500d0344501c0b94211403100140c0d40d140c01d07140618030607034090340160a0840002c040740030100701c003007030360b000f200d40c04c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 948141582 1250 948140332 948140341
    0x60f04051f0812120612070b0712020309030c130905030309030705070f0303021902040221070e04090c2c13060c1b0605101706011d060d080f1e0a08 65
    0x250749020100d80f07074040d03410401c00280d01c1c41e40c0300e5800d80c0108000d48140401e1306169050707810101290002e0242c402c022640006000d10908003208030707500d500207503240500020103c0d0322606465141402100080b916120741412a44540c095a810100b907075140d0400e0149191243d2102d0425585840790800100d500503280e90341e00d00b242d5054004000003001000c62502c0f40005400a0f64001da00344424540d1203041e00c281260100000840140c5103881000070740143d520300b2403180031b81e150041340c00005101031482015a01c6002040307440200011380f680200841144400c05440360106101401d440e9521680740d89104550038000ca6050a900300d0340031a8090100140600032450380c0c1c003203803550340100c0c1c100c2980f07084803c0158031039046a1320304200030000c411035400306004020710f0044544140c426415080050864200307040041d104503c07409024ac5030380d0002414209a001c1c007011035580745008150201c2c1034200c1d005041070343d04000880000b003800400042e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 948142832 1250 948141582 948141599
    0x70e01090608070608040206041503091a07050706090c05040e0a200d1b0b03130b0112020906010503310b0a060b0a050f09060301150912030f08060f04051f 68
    0x80c0160388031400100b4403186040401c5a1408004e80140e0304100104408280d2b55640402c1244126550f1000300d02408a40f400c40580b40c2040b6080303000020301d4043c040c907154840104d541d89500101c0100300c105040c00d01c902c0311400c0e644159481071409120502084012501013041030103260007101e90315201c0d43c038580d041141c0c00d400c5d40c03044684034a080002d00d90003a951041a800c0360071780808d504d4040e82e107015130050715810700c0360700340c0481481000301e20700420f405062150400030b405c0056902240c005100076008070f05014010000854540c15200c0800805000344034408160440804254040c841d1440955034100b4101c001072980480d400381008860031154502e00d00b00704410f0480d40c64000748000d510501c0e040008030803a54031040036501030051400c11000401c131840c0c01620704910f41d0700c00c900c500114004000440d401c020700c210280201d00f041002e0750f9840d400a2030b40c1c1e107c0e07050960305c079141006101000c6030b0090203e649040c01e68881c0380301d54442c420b0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 948144082 1250 948142832 948142841
    0x612030c0d050f1201081b1504030305031b03160e01020604030804061523040b03060c070210030f0f090203190b0a0b0411120f0f040f1103030c0708070e0109 69
    0x148840d4000c1441c501e035148a5001011007414100d803540c180310044030856142c040a0780302e074910794014800803500c5110541c100410600c03c4031103000007104900882401e002e64400035040c404c001c00060090303030b14070100f038050ba0280b0301e160381d0340e29003414820803c6104420140018444080503025940006201c50107103801d07846081d465555503442c00d0181100300603443c030340d4104c44400540e01c003c8102d27800040016180c07524400e031000382440201c034081c07484e1610076440401405903403510355088621881d01950303d088010901138096014200b14406010101d02e020824010040c0317030341c0401203051084060b24820340301810280c000d42668070307016004410f0350000c40da11055984c4041c0030500040c00108540903901d4001c0c11f10b41015250710369041c0d2400070060b5140c00c0060090788280075101784c1040f41070980300d451044114002c010041803c1d503080681c1d581e020020355020308441c50468101513150188252104414841c1c15004003145c030000c00d003c5d40034000c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 948145332 1250 948144082 948144097
    0xa060519050c030f0405191524150302090a0603020d0b040e030a0315050909151b0f0c0705091504050f07022a0901090c020f0a350c06061203 62
    0x302a0a5803511641240200c84c041d004940310721403815200d20301d01c121206a00c903140554078824405400d1070b850340541c0c07015008458003441d0310031300c009104000c204040580704c04e03022040a1101c10a02580203125184072207504c44800c0380009140340d416001011f028030000400d020b03441c0d6210500066840101518010750004d10140002900c240d00c20003140465006400c200c50f40d860103d2941801aa2014195040f070301c0400c21145c080c141690304040c00d02e4201900e10804158030680e07000310b17422a1590354000a160b11011000c104420207403100600400490a0030070364007105040c24910310740260b0038400014650409041e036a40f00e001d054018000740c80f038100101c81e4070082c01c984540c82c0c0c0040140c15565031942102680600010000080ca104001202900d440f42142c459251680017070b82d840009002d004d4045d4a0100700d000d1a06e0240842c01c00c42d101c03800b010700a000c448000701d0364a6080314001a000c2c012602501e210b10b0300f401d100121910380c46502c5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 948146582 1250 948145332 948145351
    0x31721010501020c2b0804050d0501092f010f120e0705030d1d060304170a030f1b021b011b05030a081e1b0d240f0f050d03020304080a06051905 63
    0x180f120b682d42c090044400c5c1a00c2040c16600e0281c0300d20001c0c6e00d0184d8184e050351103a54944510040100e603620030307903517038218202c01500d1804284d86401904440501141000722125410f40d0707143c0203080c1c580d2240740e0380b0010322024510311a80c0e9540c04e0350340b0500f84a8800d403204202100c2c000c0b41085410051130f40000d645603c3c000038403030150700141085481901841440c089014004050414400541d5010446441102c6035200385d644c00071209841e41c17451580e80351041e030001802d002e9080007001c02c6050000440060300c2c141c9581901080b801469211001048804801840c1c000c1881c0c0722511952030f80301d0b20200c40d4001d042c081032140858030102d0f28600c000081c4000c4080e001100c1c51030074002412140a60710602c0c100140c003050b10540c011160040d864036000350089840140d444e910f09111424a5051481460b01031500c1c41e00c03a00603d442482110b001d032102d07000b1686440c1d85072030b21100501c0211421b20380000d11070f00b0054801c0171406218080c00c043c0c1c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 948147832 1250 948146582 948146629
    0x21026091e0a062003101a0f07060515031906060608130f0c031e020310020a09033f030b0402040b0904050601121a1c030207031721010501020c 63
    0xa43c0d0b20030061002903000c201d15000700800070007184058004610a1030300880726044036142c02e0010422150f14400210f41d0001440181d8031140e1003000e0b101c0c060342000002c5991307141c82440c120502c45c21090503030940100d1900040c8050607006a1074064811101040007950381c030012982010159040a101140c111504000c01c084900d445e118500427070b11088040e0f503940c0d6000f51543c0d0440d8800240d034040f16501c007949018050b81c00324806c0d4110640c07426070703408001403060900b80002030226010000c0103211602a40c0004190380381c0004011b00290440002c00c00c200ca28044400002c1c10040b01540b00d0606000343e908498024048a04002c0c0c0d80d003c000250078018101e9041002e0081c03a01300c1c20503980944202140582900c40e400401170050000030380c5c142d8280c0888100700107a02000a90001d00350b0104c0741c1001107048a1400000c450000c3d21030a4103c2606100d60080640d020003800d080d0b90481c0c03002d80848054405400c01d100d40c85400b03441d41000c0d002030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 948149082 1250 948147832 948147853
    0x2090315101206110403060b040c080c040b0a0207050d1109180a0b070309050d030209040609110901050703120218091e1b09040e0601141c021026091e 66
    0x14081c0c002c164854140404c070800306521200c1030750003550059071010340303c1c0c0f00f4101c01c1c2400d10450f01242c1103450590440e1a02d411003081501c114030030146130101c002058000070b8400d00004015250041803140500c8144c104801d200e880c2952451017591036038040303000301a0005e103c18034101d21201070509143c207510b034240041c2d4001d081e201416215404140014014812000c2e50240c40d00c0041e00d9009402c107110485000b40c000140592900142165182e01c8c2d80590302c0510782440c115644031100e1404451030882042a51070b21b90022903841016610760b40210b00001081d03c00c0501d69595240010b00e51070101c1c2c0c0340784000d003540d001c05c00140d018540e40600300210210305282c00842004901140c41d540c501071801d8020000510248030100b0038050315150403140c4141e001e20310b02201b481075040030300007880b84100d0f20703a14032030500035823000000040c00701d42102b8420000395040300c40441250002c240340941903d0302150904040382c0c00045282900904101b0355 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 948150332 1250 948149082 948149099
    0x130e180f0d0e041107030f0806030307020d06020306011407080418020712181e080d020706082811090306061c0b090f07060f090e01060f12090203060702010209031510 73
    0x80030306259401c00c1e00c0b20f8001c2d203103900c80002405c081d4400c0d0740b0b002c0d00c48810a0300902e0a0300c00380c0818400e0301708201040160f55030100e18007000341c00c104016a25107a0030300503108403900c24400c140354400480e1490510840d0000380c000c6481000f10b10003415190411201284140f82c0010104840264699082c41c0700708940800c14401003414840390b43c5600d08110089020100c0c00c9000c00384103014400356038180b0030480c0c10b040d98001480e44500301500034101000c010080d200124820004240846800036840c2c100c0c14594802c010385c5a0040910300f181c2d0088101d1400b1b8451940881c03950b042440c20980400c45909643d4880000b6548081c4240c41c0a05000c4c0c0074410804030050803041840711800400c0070b03407101d0031300c7c2403642070280241d0b003564002246101854010001c160700300100c800a00b19a140c18480343c0a4500604018116800d000c0e4151095000708284180c0550080940d02e134100e00300d8554000c0110a003000680844080100035040d100401c500036 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 948151582 1250 948150332 948150347
    0x40308070f050f060901020c0111030124120f0906200a1b050d020a0b01080f060a020904092406050409050c060f0403050d0816020102031614130e180f0d 67
    0xd11034015268104050000c00c4e2078501d0a9070b45050a075400503e81040003002d1090300743d40d04003140f8143c00c542c9840b500c01564002c06443e2841d502c16000541d04191180c10000d8400124130010080c1a1498003628004c0c400d96404840791440c3c01020014004011401c3c224084161000c516080600e401240e90049100c4ca00c01c201d40b40c8a150000240180201c00320007801d6801800302a0417801c00054403881a80140040d40104104007030341003001c20040c0d44042075590240e80c0c1c180d1140410010405143d01905010381107245440140c030100354462843d040c0b000c2804aa9200d6041108541031004010421380c4007140005003400c183c03016129800c042d0031000c0c1010b650b41c80d203038240300b240981040003444441c1000f0b03103281600c0341d40d48844c035244000c42c150324041c0d002e6002c0c1807080c0040000d003c010b061844900c0d820030125079881042401c1141c0302236680004640100060f20060400a105e40062040c810005030b40b07916415400010409413021900c15685070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 948152832 1250 948151582 948151613
    0x2103132102061812010b0918032704020d0b10020106080303060d0f0f030f0f0c0519020a0914040606120302070611010609050112050d030e030714030c07120308090304030807 76
    0x243c42c103094003900c560302c400303240d01c402e001180042003082c04182048840c0c04000c2541c40741a13034441306c103a00300d00000252403c0b422450340042614400d000c40c00c207000c000c000850b600c035000050005908820781c00050b68080d05807455440c00c001510b09900fa06e0381030017200ca5a600510005007a0b15002c8403035404d903400b44a5030443e400e0300d92202041421424410307030105221480341304080d42d004c221900c4c60107031440c0200d500d91306a03a40c00d88540c0320203003040314032128012034002d40d03443e40c000900600c46407404012040710100300091106003201c2c02d0315404c3c6800070000d4104244881c081c0455410782c05440c007603043c440180d80320409241c0510f003039965200041000015441014040c2142502c040e0055400b0f141c600e01d041c4c40e14508504143c2010011480043c0010a42d0096a40704030010508220340307510340d1030750003041402940c0d44640c500c0056000b1000e4003d0350094060b641c0c103005603482c0c01141d6624416031000400202040140c003000c2a205d503c3c20145 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 948154082 1250 948152832 948152857
    0x51206040f0212010e01120b0402040218090a0b010806031203070f031b0c02120a1e020112051806100b0703120f1a0a081f0b210313210206 61
    0x11150742110701c002c036048000700c03400700fa1280c00180040320b0241c0d001030041c080c0203aa4030050a85c0e40d00c0c1c200c409806000240035540100b104070101e030100422106021024210101c1c601c0c044212102829030090143d0100341e00001007032180c1400b00c0e00800861201c00068555164040c0440e46101c500c00c01d84201541d070310070b507804007000440894800c0d803984e030352911240f02070040054101740004403903182e501c0840c44a000036010b07140801085882504071490234024001030301c1e01c1c1e0b403c511440241d440c202c01c000003200355040300b00c20400203604581c210f0740c5000903032506003158055110490f0041c8400400248561480340c0009403816010810520010b20340d4169003c119a83c25400041c400454544c10000c0f860001004018010008135411802c44500f5480d459038050085031207000821607611120203040c0088009051018512600d4100f0b6489800c1410480e41c502c00e10301d030001e452080211034280c05819203140c420106025400c110540d4007007200b0102 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 948155332 1250 948154082 948154091
    0x30a1107030501240b1801050906040e0112120206010e010509191a0f01032f0c1e010506090603150403021207060f11070b01090b01031407050c120a05120604 69
    0x141c1c04e008100102002c000c401e56a110321000d0364000651503000b10112400512150750a6140c0a4280b12406028203000383c0c0d486191000c01c8062050b82c1040300402807060000401c0700420144c070b640b55021b2001c04007030480820040b62111000e119a0009801c1400103000d2450410016174110507103032030880d090714002002400f5101a0a14506041b0803a90100302ca030820400507203a0010902c1d0810090600a003800350312210444c81c1d803010060150b00010000c811401c031070020740031208035943d0002d19003043d08003032a01d00c00b03051a9402e01000c10b0082c02d0070f1800ca070162600402500c3d0591103140d11884500c40140140c00f107105610982c4003000b060f10042a145014000120b5484103812a080c1510440d45040585440800004003c5000e000d15241900d041c164041a6009074900490192100000c911010070340c900601c102c2a400500030201200380070260758551107400f060104030300a03c1c144030013140040000e02580c08002c0480ca0340100010720008 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 948156582 1250 948155332 948155339
    0x30507090b030a12080405060f0c1c090f0f1104020703141305041a0901360b06030a141302011e03090b07020303090f0606061c09210905030102030603030a1107 70
    0x14080d03213214030150104941500f800203020080c0182548240084d48051241c20840132503004c510440c081c0c01c2e4910740001c0015182d2807180c021648850300700c007004443d43c0441c1030041d041724110300304071103400c2ca5407443c07001c90400d402a2001e10350103481d0400076601e5003403032751801da100c2803001034024103c0102282d5595644180d0040c3c100e1500c041210300100000e02c0110501a00300100100d508440c028902001005a603084861080f61075104e02050805402408200120903803000d00881000540c400c1c83d4401e090b070b01c1016104001545035942c04140d01542c1c0700f0040d001503100308070011101090011101d0007440d911300000d000c40a07860300948079070183e07000c02c0143c200000303000700745000300711059440b40c0f540701038280750801074000340306489030f500e2141c2c03441404000441e601405601c0448542c0c0c00c04417103e80b4481d401405002c01c41c08071000c101090f942140800c1c40d003814400d50784290400790041d03203010403808040e621803040310082c001511a044011 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 948157832 1250 948156582 948156593
    0x30a0b070e03101e020403170c0312010602060601030b190323030c010b0f1c020d060e0a0302070306150b0d0513050a060209150906030a0f06050616020901060306030507090b030a 78
    0x1103c0c20718103040020201c20700b01c0d03000044070f8205902440c2500600c03007800402c03800009090752645c03940c803403a5204140076456040d4050b09001c2100703212000000203407581c011560500c9180300340d07002c00855546074108010190b104030914545100a803040c80040c40031007845800c100381c0b4071101129040504c0d21861540103040c111680d944900003101941840015000018421102c02e01c00540405106120409482e00030344601c0d07d2083e0201440384030342c444101808510700740e80b01400c0c039003006590380311300d03100440320380d407030304000d101803030700701221b19082e0380403408110f161001c3c1c90641000b5050180c04001c07102044440c40000440402060764150300c103503c056250407040d80ac00c6031f5580d00c00c0c0041500f0800300701c0140655203200c100e03030340704501c04000990554403801e4480200102d400c8142c201d40c00141c3e03c0b90840103000303640d807914422689004240e03220700e001c50945003644801001a8003422043c8003200380ba400030f1141e440d0207400c680a500321754948 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 948159082 1250 948157832 948157843
    0x216032301182009010b0f0f0412050d09080601080c121507080a0507020a12030903020a2a0906051c0501110403080903010b010e0109060c0206071506050a08010b030a0b070e03 77
    0x40360808030309040b00191a2003c03800982c0c045084544039003640c903240003900345104000148a21440000f80d0301e007405a05000d45001e054161103160010a040c900389a4a00d1000b004c02c1c08500c003103400007000040090800c0c140c1d00c402e0041c0180036010350500c10018024640c2c8105800303540c0e1030010154102e02494890103050b91107100c2810800042800c55401034013034000c6402000300710001c00c10000c81c030040c00007140303000282d5450701c2c14200d0174145039400042c921100102c0300c00180c0056881c681e00204041d0149801c5559004100122021482500c0d004000007400745c5076103d02040344110742d03000e10000f08200c640202051201c3d030098104640318580401c11240c141424464688641020b0a0041820400c07400191803000d007403040703804214806828004640340e030030a441c7c9940d4403200440c8000300c00030b501c83c00b9010a02402e030168403046000070f10100140200b410b0b0240180140c80e0040c41ca4071021354801c0000c3c98070b014000c0030401040c198034100316 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 948160332 1250 948159082 948159131
    0x1612020604020a0f03050303010b03060d150222030515190921030515100e03060f09011104060f0f0c14010b03010f06510216032301 58
    0x18024a1801d481005a00942508250070040980e8000d1000907000001c60707042d6501c503841e0544035640c8500041c180d200d40342d801001c0410b455501341030041aa00a011072005070320b61003048541a00314045144501c2c800941075501c8884980d0080700c05015045d00a1016181c1840d4008090510070655422079401c82e40708c4445a0300c1c62203190f00c00d008540104d841e14082c0b00604010361000c500b0880500c1a922422800510800360350180410840481d0007400769070f82c0e8601030000b000710b00c404941d554003e500340301c0043c000406400440f000d80d035854039413525806c140c2c5021217020550b4016107040c0603202c410000495100ca25030100c9422000022441d03c001100341400d44e14007001c003050b1203051100521500c40713855101c04040c0c070041c810405209085c10409500b04202c07681546c684040c078012a600c14404050040c0e104190f021591170301e800060100780011f003032101a224200c040c551048040c1804de10340d150400440000c6408000c00400e04050701c41b460 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 948161582 1250 948160332 948160337
    0x2070305070f1b0b09131d1b03101b080a0b0a080d02120405010207031103010f020c100e120415090b0c100f020c0705061620010e0d02030c061612 64
    0xd09403d62400c00c0b01d4400140500c02d800134104040c1402244060001460061341e058541049000d650000100030704913400306022190001c000e40345407100300341d40202c0c41e8001d016504200501c88454040d5090074201e52102c0303641d10002440855180c04083d00c030079a407580710f0807402242d642d44480c5e40301400041c00984510039a01e007010786031015649183d2401081403004003ca6a0003041442c1102e4218140c03000c036502104c000707401450090740c10280e01e1302c01700e21030710000340c0002e542c10000c608410030444607613002c0f00a0340e6080070241030154010100310a2260b020320030704085541880e030804200742502c86003011f8840d000110fa8111f10303406860324000030690343c0186001d8800c0b0303110440c0381c8400d0010b41501c07280e1901800e0300890f000207501d03d98840103a4440300b03042d0085406018003940140703004c0340f0300210024500080d1088000306c1940760a03214821082e9008008150704040c80052202c29000142c40d4060b8a04140d1203102149048813090240f00191303 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 948162832 1250 948161582 948161603
    0x80708040b0f090f091902221d070201050f0c1c0f390f110319030507050306030c270a060303110a05032706071b080c06030a02070305070f 61
    0x3d1051140f107982c8180528804c00c2e40b4414401000c15000c2440001048500003581e11510b04450140e440400d1503166040f2254210000701c041c505514072410071503903280000203482d5990700301e081e54000e85020040c100901b000c149160400c5009143c0c04121011391184210341b5010001141d04400082c4142e940751003072816507505283d041101c45035103404480c0d005011513100d803802204071035100e09001c9061140400c490203070b800341941c5d04440e011282c4c1c5030002c0061542c40c1203401c2480300801d0800b0f000c1803a450045c000c2c0c82c490307103014008280d000e000604000b0101d1000c0c01c0c0040c0614a078585e88803c0f00881e105500c54618003a0200302c0d20b146140051004c4020480d811264001440c86400100c000c001c1f16842c40c141c404c2805240b02c06004409401c801101c000e500040008081081050101a40040c02c1d585100a81229659050952584854840aa48051f040002520001e01c0303a0150504600030319100e800d190b1305503104100b488910030b041d103420340c0da03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 948164082 1250 948162832 948162847
    0xc06091110030e0307020603150d0f0302010b0607030c0210031e2309070303110c04141f0b0d021303020414220309050907020a05030a18050a05030604080708040b0f 72
    0x2040c4007048200301c514003085020164510f894580c0074080000f072054000001054060507440700b0082800c100811885400846103070a402c16400480d0840140d401c105414210f49011415102ca42d6055142e0302d401307078010750030070841991101c02c65041c19658030398025070b01119540c1310341e080e5143d02d0006080c0f04515540c1e074004814281c40103d8a01581004400741010815008403541070400304e000b4500c0500c0e0300c1c00c00b01c0d0b000c02181c01070f14003510350300701e40101d126041c018540103845004000d000310480019602e0340c020b2009071001003042c51300e07007031080d07000b45040c0c00382e051200c211545035800182a0703081e00748035003840340640050100b140303940900c4114103000040c030040788100c1d540e0080d00c0340382d2a21410348038426a100283e40c2a0003403184106141d4424241d0b6a81c403100c1c80080c1030382e0582034804a00320040500032845003491500401540e200900502503690b5554500c1c4440d4400c0504503403c80c014400020544081c0000e04450076030109050340302c451 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 948165332 1250 948164082 948164089
    0x51f060e0603070f0b0f0c031612080403050a0e012a02090109061505030a0b0a06030c0e06120c16050105070806130b090406020d2304050d02070f060f0c060911 70
    0x10142615210760040030f02000203520290541e4101ca084801d480e403210b00c540e8080c1901c2c002c80e03080f11114000011070304640072601d1601800c4620403d40040540441d410886040c1801c440003030104500300f20303480481e409044503880800d41498028058204000341541c0100419544e02000010122003411132514622040c09802802001c03c4503a00d01010300b806140d007005240140007000011075403901c80794000100b100d40103840c1d40e03540ca5982c030000300140121084000014030140844081e8a04002140c2442941c840c0804880e00c901ea42d242c104c1e032101d1180c0100a691444080001d00c023806003d104e0b08003034455001924001c400d1040701458101c88014552a2040c2201c250ba52104041d0300250000300041c1c981201082a000030024008104a00c0d01a069860040341003c60b40d079108038441c50540e6564549240c09a90700c0040e802071000d246085041402100d00c101c01e2981400107910b04121100348545461045808503801602c6004941001485904 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 948166582 1250 948165332 948165359
    0xc1305060d0522030909230907080f01020c1032060307050d0f030806061b03041806030b070c02040618020a020c060f0a030902040b03010e0607080105040902060313051f06 75
    0xb820f41d500b2584020180d603004103071003401d003d0080c039540e48094088a80184101051092141410301a01414420b5103280d0300c4500d442425500c2c8100d0511114101041c000c1d00e414694030002045244004807140010b80b4200c01406100240961700c0302c2240544003151100808000c0c103a00e0301e007400c01c00d0605203582038120a00400d016003000001070808420003000640501e84561030361202c00019045204420405815001010201c8150078010004100302c0704003540640c00b0f4035030049000152a42440064a09840e11000030b414034045c101c0c00801a200400c0052015140c0d000c08050380750700705481c0c0e507107076010443c08003807501044047c0502d9421038501c0d0916081c2100c01100d8403801040c1001c05803a01c0c800811902e950f040752852074001002444070030416194541c0d505812504040000c882e20000200740c206442041002da8008d40f04034030b155980030244208400200c0c04840c03920a02103400c2c1c81d0f000c05000659019600788011070443d14021014100c0c0c0c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 948167832 1250 948166582 948166621
    0x1719090905070c080a0e011e050a1b0f0b0405031306031b0201111c110c030913110306060304140d05030a0f0e0c040917070c0e18060c1305060d05 64
    0x80203560b80c3c01080d08202900d034a0a01d9140c0b200c1405d0412004841982010218500c40e09009882886140d04030740035200313061242d95046401c289040c007420303800407001c00191420401c10201c1021920041082d43e0280c0540d0450745000546521441c0a00c0164008400681e43e4010701c81d0101d001ca0070104e642180c1d00c0240210100440da1034041e206403d811510344459a950b10941d2825410004203805c203940300644600084104030b440791700c080d954500c070750300040f0308940006641c440d10b410000000f00207030455443c40280b191980c406041984c21460f031a08485440000f0000709040209a03900d907910380c100100090203070781f40e4400200480e400c01041e42600b103400a0081e000d450229004144203506040c010104044500d82c1080c3d0340000801274280004040740701c1c1190202d001001081d40d64400303118030000140c040c4481b603003140012501000900014103486406000700b04841581e82001607516400b624500c440c0c52b0f12001001341c12001c481102c141d4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 948169082 1250 948167832 948167837
    0x1509031b060411040515060409021315050406050a051207030c0206060301090b1303141803070e09150a0f060e0a0c111c03110406030f0509070f03171909090507 70
    0xd400d042c3e50324843c0c20000303030149004683d01c0700020600e2010314441c0c0020040941407a945503200c3c44101c1c0a940304600b500c02114010380c0001e8070180c0210201000b51541d82c03464105401c0080813200d640c0305041c0281009000d000300f0f00d0302d160210342c2d03e0040c45583c03400680401070b110080d0402d80024011480b907413400200c940448d002246040d4080c020f0040c00b0005c0b01c85250654500030780e020341464041d008100541800c0c001410100c10703240c220101c480d030035079070001a560b8004c201c1c2c0410064004288120711582986506038006104200104103500c1041c1008105c0708281c0c45101020031740c805016440d0124070820610085c0392401d030540c46100070410b03950706c40700e0228465620f0400c9030302900c940310b60b0007001c0841e00024916511666100014050310381071000010207441c10001c540360500c0040c2c20b10031145020400d44006195440c0d2148040c1030140044403840708002a04603003e00307140c1000080c1c5a0f4a68555076801c0141d82c80c100c95000307041806 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 948170332 1250 948169082 948169093
    0x130203090106090e03090d1703010e18030a090e100308030a150807080309101205011202030607020d0e01030e010e06040b0f10050f1224180a020a171509031b 69
    0x130588008400c540703404005030b030400545102840d00385d414480c80b140080c004040480041085601406001c0c040e226200283c0300e14144400103540360310a89a0030004138800300d10400c0307400130340100240c1c0101310074044030020b0707501d880e01c6040d03a02c1140e856441030754032003c1101030510500254058400301008080c5142403c3d400c1c0c1d500c2c4200010f051150304034400d05c0e041e2034401e2241c480d0b4444030000600455940d400b8a107950030b00142c040340b00340200130000b0306252001501d0b040f41d00095640d19030590301000194001d005210460030107540714941c08958540c208045030141d44201410035032860013040c5c5e01c4800ea030141940103d082c031460100801c1d038450003460b00a41e800c841c4d401d141c0140e003031102d14011142c03041050300090002c074000106061712180d44200d00c02c0c01c401d5402c0e40460440d903201c22240f40f000303601503c042d80c18040c4203155503120000700c12041c01c4840d003440900450202c840200c43c8840c1c00e0b0300001c0c02003d01003401306141e8502e0400401840d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 948171582 1250 948170332 948170351
    0x1151103070f0b0c0705070f1818140703140c040c090e040303020d09061d0c0a0303020319140c010e0c04050105130504111008010e01060e010804031b0213020309010609 74
    0x10342c650007542d070262102d00300748041401100d03480112505180e0020484488554894481060b40030a20840c0c6081d1152200c02e141c81c0c0c003030f01610b0940c2e50300c044035411046407070780c50801c03a15010020483d1031242100205c0080c00500407501c449030301d20024408907848004110940d0341140300e4008000c02d090042005411462000390040d9240c1009600d880140c80440700400303050b0005400107003410720046006424500c440030400c1340c50143c83c1c50f131161800380401c0101e0340c0702c000d0043c2d0041164494000d256003009019110503c1c0802c002c143c04403032000c00e50091469103503581d6446601e454505000c1010f0303c0308800980d400d1065624000004000900517046282169107078030001d01080713805014820080030003070407a040d0500a01c0000c0c240700d024040c0c2100c0b4214000080307610341c010b00f20050f0340c0c02e050b5100c0410381c0d074a47d0202c0d4140416a5081c0c90308080c0741c022001a62412101162035401c803500607100e10b0036545240c29110264040821b41c0d24199000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 948172832 1250 948171582 948171593
    0x13062703050d0f170a0b01080105090903070215040509010602030417061b0702180718080f060402100c050d11061005030c011115090105010815191d060115110307 71
    0xb0003602030304100e45040c3c2c501030213480001064100c005914421410004041000d40c005041d1030340030b80c2c4101131b030ba80ba6000d01480e0302c0252003198140e80706201550046c5004554440201c44c15000e041c20325640d40c0120b1040382d070a0700508090303000407406002c6056100a1601199061340c020300040c00c02c90f10108195030a180c0c0407002640001d4a4019034807983e04060350f05401d88207449003494620340041030b0016010804000e2090044000b5811100040b4500182c07070341409000c10361a103508010300108120501c0040c1310107031000300e0114005001c504ae440400c5d85a840107450000c0f961818860b004080c40302c040880740707081c0980d40300040e420441010a0818246500c4a080600d10340201000d034000030f41d006c1020000950300c190440b5040341d600d8021070390440d41c81040014000340032200306280841c058108910720f2000e0b044403039446260f0490000c2480400784990808000343c0010b1000b824440d000800107a0001c607480c1071800100141d0308060341960389 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 948174082 1250 948172832 948172843
    0x40917033111090a09140102041e08060c130902040e040b281104080106030f1704140d080f07120f170f1008030c011410080303040f03051306270305 65
    0x200d02404030b60001131800d100b640c1c401d114080e00261541100131543c110f0a020b91310a00440801041c1903204444c0360fa41484001c0c292a0b54001510482e6a108400c17170f0290400b680001c0f548107000c4001070130020718401403015161500f140221450303d0300700050341c21b2004d051407214038404211030500100d411400281074801c1c2d00d0200740d000340307010f98940d2406150000c0301d1551800c2c90003c02c014000c00d2004482d441a9000711014009201c8216140182d1180d458001c4c0d035440029850300d84620100919841000d80758101481c160303000c1c0081d0054141201c1c6410a06020b14070107030003109012000507240740100609440080342d10703040c00064181c0d048141e940c000700b10f503403811840312005800e0900440c1c4d05ca11550720140e002e084110000c8008840d5a00820750200c141c0c1034100541d40c840e00190b01e140c460b9500d141d090810701d4000d4040040038040414540d01034050900100030954560b0701803c3c1100790401705070403001504001d034110a40420014801049 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 948175332 1250 948174082 948174113
    0x1323010c02120f030d05100501050a03090f120c0203062a070c0302030a080406110a030f0e0a090510090b040207030c0318080d090e100501020c0409170331 68
    0xc10400340012840410301c0c0305080c031001c00c4103000c3d900304094044000809032103200c0d195031003400241c80d41c81d030804458555002d16400190300f0062091034a000e500000f460764854a03006401031102d8440d442204114940e0344000b4142003d4501949000c101c41a00310802100c120114a0f0518030482c0c510b103e010201c000c0100450000305128215035000b0041d0f4020701501e40e1107141d45006517196105003d9074001c102d51954420081d040000c210740150f5042e00d50707803000c0c400340701c003a05e0100d030305801e0070782c4402c0c00c003008074003600b05014542c040c0c112003100344222030a0035900c40683e03400e000140d00a42c03043c04140003081d8004042d0401035050b00b0134070107a21181c0c181140c90b107490381201031316206550317076808007036405107038102100e00700c07500045141c0b11606141c054035003500c19140140e0041e00341c00424505640481703041480351840e410a000010035070001c1e5041110541c1c502140c0205140c0d2008904c00e4050146000380507070510394910fa950710050110015 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 948176582 1250 948175332 948175337
    0x80601090b061216120902010e09090c120309010f020a110f1c0f0204110c120f041d04061d100f0f020d1a1e060903030f0a0203132301 59
    0x41c404452912030904989940502e61081640c0b4a003600840f01c8440c2d030a101e220005642000c484a400c0307051182c0084681d05079143c90140588008018800c00c019005400314041d0041d2000b869556200382e400000340c00002c2e40c1c86c0c0700002c0001d072081c024049200255000380111200107446000015110401118211040d02010012820642190000e25650085440540b00341b00085e4091048203108407010321241d052028441010302800c41010415441503140c2110740010707801503c1101300612703200e800c1070b99440702160349a50000501d400b0407180002d10041c80031601034035844544440c0744101800600c0c81c801d58440c03014940001c0d01d69244104a8428226005045490b0000b44299180c801032584030000f880303c8200d410145468124a00380c60034210002601030300c008081c0c48145c3c40b80014000103a001c0719a00d6818002080240049818000540f80e10303040d90340156140c605e00d200c0b070403002c001600f0921880c0ca007000301c16075100d50b04480003607a40003071 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 948177832 1250 948176582 948176591
    0x1e03110313380105040c02030a0c110a09021216090b03040303090f0501020901020f12160c090510080c01020a120c03030f05090c041118010f0504080304090204090b01030608060109 79
    0x5050032050402d0300101e9100300d0006104075445a1442400060400101032140c2526642c40003003008850381513130f5a20141c0c00920003c180b41c3d0048213147d1041340190fa880411940150001d426480c881d081a03042c50341c0400c0c402c00c0000e00034136a9a204080c0c410700428800004e03009814003c2da4410045100400400101007610941141080c140c0c030583c040d0f003030880d61038040e01030340051080700e0043c03080b8120139441c000e00003103411900592000c81c620b842140c0b01402082100032000ba240740e0130001e00015000c115102d403500c80c000030320141c1601410203281c2030505400301c01a0b81103502681203000416004070741407034021000d003040c0c0080d50440c98141c02620042c2900244180742208100c003000010414030701d8240304075008c03c180314145429a8150040566103c0e402051150800701540540c603c01c207200c4050030800e0401f40d0f42c028180c03555000f5040200006c1e00454100540030560251070170100b002d090a0103894200781c0e580c0c1c0c0d9114140f15100819448 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 948179082 1250 948177832 948177871
    0x1119180b1918140301150e16110f010c0914010801151112090a0501050408060c090117010f03110301140601030b0f040f0b011103120402010305251e031103 68
    0x8100c51065801d0840380c4400803555003c3d20f02406043c3c040340f6000f5402c000d1414410b0500b02110b8064a20040c1d01c417256450344007820410800070310308a820721030016090400001d0400184003d01020710000c200e0035a82440184505020340c04840d0702540d80040031031507038000c402103043d100102c0005c0748036a09013100329826040c0c110aa140f41c01280c40081f8034824104c01400c5c5075005a4a00c083d50399150011201442284a410340a4210002040035180c064004000030707801403400700d100440e01d044005a4100a91100c103442d15580720400070428010042d1400c0b02045008009909a403000d0240043e00246540d04059560f04680f90750380c7c444400325103244001d8030801c40100031705a000014445140564049040c42c85c0c90050130000204648504084007800c810326101d42d0b005502074000940b5221141c00b8901d1120101c4904403441001c1d1546503035451311400c00c800c0e1481030f442106000c00205800c044000e8000080d03c01200e80000c401840d01e0a04200b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 948180332 1250 948179082 948179087
    0x20a0306031e03140f07171309020403150c0e22090c210c0e060d0f0336030f021206090d02010c08061809011119180b19 53
    0x100d03a08000c154100300e0004070000b021140015104030301c42d860781c2c20103089580c140c001900414040307a9403c80f08101080000380748040000e0201302c403080060505d1529200b10030a90781c5034200b840c080780d0204007003041c0200c1c107010a0003503403184070411180a10640080c8031580b1940c1060040c02d1029040e010540c000e103071441c40041c14041041100c1c101c1c6003a2a0160b442d21449a002003c0c0c0116040c0e00000305c03d02000c940d021655803000c5140416241000400a04083d880b00d0fa0500700800f0410400038090120f20030395451015080748850081081315580e865078141c11180f01c1280c842110510240c2502c1d00321035a401f00341d26610001e00803400e0042e01840d9030107220207009103c0b4001500c6445415240c009212494000000319004042103514a80c400150301070061242072118001e50030031045800481c0640c1100760b0b240a541c401e1001c50480c820400c0501d11141d402602c09444034010000c4003d040c1c0340c41d0005d2154060f070010040e0b8415103c2d42001e0060 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 948181582 1250 948180332 948180341
    0x5060c0703060c02010926030718050a0306020301052403060607020d151b0305070503220f0b0a060b160615080a03050a030f051006030c14030f011d01140103020a03 72
    0x41c0d1110307080c000d50303148043c002d02030541300c0811a0031000702c0749040311810303e9000d009007060f40000c150b030460356204011544400b4080d401c3c10b00b4011382a0101d4591200d0506901071409a140544d0325450310003444041c4825a001c4006101048190344100201201b03d0b0b40000c0c003103942c40d86038003003800025000035141e04000c0030381c03a05126000103042d9982000d403095160b1103408240754458101602901c9040710f840d00001c0c0e041002440c2848885070881c034030300244115500c040c044d90f440502002e5561826518091008208001ea68190285001601005d0406420a10148a484142454800c00801e41c0e80c0703d05107840b0b1074840401402c001c00100040392040f600608020b001940030303200c0000041c0c05c005c81504840e51a00859006408240070010002c3c03a181d8124001d00042c030318a400c000c4840d81e0402002d81210107076014a108201c004503551504001e045801c49848115a001030034100412094101c0b16088146c080282000769566203440021030060 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 948182832 1250 948181582 948181589
    0x60613030b15190e0903030907031b05030a140c0105040f0308071109040f0b0a050112031808030f090406050d0f060b0a0306050405010b2b0f1505010b07032705060c07 73
    0x3c1d80d14207074901c0320390703441c03240790300b111001114621207845100d00107440340b0045921803466802400100300040d040c51019810307507003101e0350b041c7e00b640344c500082c1003400151069400420b144050485001e09000320318041209091180c6424a13002c48000248094403002d41110f4004c40c4a000f4003c4c0d49a1524424270001c2100d00245414a41407051107200703003041d1103d0080c0c2c1d00107190018107100300c0741a104413900b070f10b40d820141d13035049910011001c4000070403c3e0240000643c00d07420400360012081005005840b50840401d120886509a110b90302c1100f0305a9100d01003880c1d642000d0140c1c1e00804040341c00c003401004641039000d80c1d403000f01000c1c5400300300320034054103502510081408503a0074078021400344ca0300700304260140c03401e68180c500411003400a0f0207140f0724000300740f1070b15031104006450a0307581c4c00c55000340d00a00341900b000660074100341d40107080c01e0034035000e41d00303100305080da0281c4a14007000500901d030080c1c034005100740c0b0704c040401424009 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 948184082 1250 948182832 948182839
    0x1e040e0d21022512050f0f0d1401140910030b070f02070b0406050d1a0306010501030e010e011103010312051602011110050411030c06030603300c06010608060613030b15 74
    0x50031843c01a016007410310440588155041c0d02c89840b02611450840301c003601400301150602e07201611006141d4400007075805416500c990105242651142460003014043c0c1550801307040703101481154036000b8a41d443c2d290304124140001203030103a06903040045854034a02208480d14160316101c5640c01480a5440c0450001007842d40b00006090900340908140f000c000115098002706038041c40c01035150704031100502c050f5200c0c0d800384803040c101e40b00205400f802411040d003164000c90072900b40000001c018014002a21541c8411442e01e241c55403411000c42001e07142030041c041c00074100304804610000d604000c004c0350710000c0f00e0344420481801c007840c1c807a800303400c6009060f02038080c40141c400d4516000d42940e1150742d014020b840b0401d070415a0554140780110060461580c4140c94520890501c0c040d005c0d01100328000c0540d541000405040d4060041299100d050108100d21075141c5a50401044030341c0924021801c8c1c03140000401519118840d1030b80 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 948185332 1250 948184082 948184117
    0x6020c01140f0a0e0312160906050c0706120908070507061b0309120303111303120c2307030b0103060b0a0e15010c21020307060b03010902011b030e1e040e0d2102 71
    0x809042e151500d40810301a51107500c5189d603142c1d8150780d90300039940800301035044603c1c100076242c040c5c46100c155a0341840002039200c072650b60b105040d04a20001d80362540b1225082c8600750700b24004280070425010400c962502650f4014200c520600a0001d0180744003018410140a0b811000c1100060032009888042501040444200721320043d141074035104502c00d00c8c03c0c040e006100c1215003200e0602e00c160741002d100401000c90b08115025482035000000100d1403002100d0b0180d403203600d01050410102c130810540d82009c2c2c000307050710a059000d00181c4e20340048282c030140070030f007012488650982000d01e0420410a001400c00e038661100f5100d150380800102101e600c2480200222660103060600700d07006450020301295848400c04403c8620b0f20550041c14032914203e030f0710b40610800300d403994900c01602c1e252400368900340641c40c5002d0060014007038102c2d00403c1303144500940103090101e00c0360092200e2031881240c45001409070110f803015240d180d00d5a0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 948186582 1250 948185332 948185341
    0x100b1f1e080402010906050c0d030908090405011206060e190e01270b0c09030619090203010f0f1a06030712090515040b24040e15010306020c01140f0a0e0312 69
    0x40000700112000c0303000034030302c031008180b43d4007460989460410b2900100410300c1c1c0c640c01070300200b0f4a040141d0744840d080c4034200040d552030290728040c0504051403000082a0714003002a03803d260002c1c0c0410049504100c601c0c50b00c11201004001e0034600403030300f901c240441c00d004002c3e0840810000d01000d10f5101d83c490795903110142c40344110b80782d00782941c80e80e441c500b450150b50000c0350b054210398042180380c1e100c14240010303400d03403130702c0026080c040782d00003400c413000203921004080d150540312503102214030071600f14107221100703407022444000016150344002400340080c089501406000c8550607800800c40e594088100c0340e80c0c88443c00f0102e818101210221110220071001071400c80c051040722402000c20800140c64500700c900304405051a8042c8015034410b0840000d00d55403081305d102c0c02180120030050342c45004060b55801d40721204600c545824514003800007440508a20300e43c080d40c0301c0d000082240c14400020308621480b410000350125100a10 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 948187832 1250 948186582 948186587
    0x803180f131d10092a08030307090f051e0103020d060509040b0a0621032607090f1202061801030219020f060105122109030a03090503100b1f1e 63
    0xc41102142c04115040600c49204000c140e40301200300a004800103000d036241500302c405102540200c0c1490b0504468a5054031461908201c1e80080091503414003000144840e00c1c4503400340c02d0580343c1055150b04078038454880003003440c10303c0c1015400210254060120741c0a80043c060040452085082605120410b00d20582d6403a0000381707000303c001070702540c40c10300444030b0708503403008007070a01a0384041e80c100101c03030a804800700705c01405860007101440ca240c4908140e1700e900c403499052280e030b14806001604410b81011400c403c40016903150f1007a070f8038464014880d2904480d060004074040c2c007070700d0003c0c84905101040743c0d030340d0380d004908424100700354000c40e100760382c2c1c850402c01001c840312403051243e00203032204907403100b158a0030a5000c920034001b07860a182032011900d44134003140c080d80000d92002d01800140740c1480100c820305442c0c0000d00401c0012000141c004d408003101c008004041030080b00303441e02500402c604040e50f110000002000007801 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 948189082 1250 948187832 948187871
    0x70f0f0e1c11040f18031b14060711030a02211303031d0a15030207060e100e0705041b050a09090510060f020a030813030c06060305160803180f13 64
    0x100c511813800c109055070b10301050b104170328582c5240305500c114066181c0f03090b51180358000c914120084031030880008501c10b503a0b94031180e40044000c084a15004000a105800401050417540c00c10000218015800030b510740400c8041201c1d41082880343c4644801440b50001400560081900c00018180c0007850359200c4c01440010b00c1c0c00201c000c0811101c0d4001e40911a29000b0306128400300300c0c4268080c1080f82e100c3c0c80001100645c4403039003440d29801c0c05000e0000c540701c0064510031203080c44500e0041c8002d990a110303814118000786a0846095801c41c2003090200b14058064401e0620000034602090208414149440340046c2c1c07581a004581c04039910508800c529803001500101e4690190359603052921460320000e80d03005c0000d02502040300a19084001c140c080c4640d40040d881500209410100e5070400003030744c003240e0b00c8111030341c100f400402c8020100f84046090a80201d07411415a08080c0008240200120424030b880c1d02e05205000901d80c60b402 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 948190332 1250 948189082 948189113
    0x5070b0907030512270609090103061a1c03030c050f030406020403140a020d350306210d030209010302071e03120603020f090402010c0210030c08070f0f0e1c 69
    0x140c1304101240d4500d45040d1140b0b259a0103010304410024001a07100300c2d0001132001c00030705443c6007000140014a0400d0280c0041e110307560f80364038400318128046001040d601056070341101081c0344155001d198034503040084c040c903894840304070125204008691400c2e01441d03841e80c80741441d08140c0c001b90000d000442c0e4038258508080d007941c0001404580b404c1c1e004102044610480c1ea074080150307421005915803640d400700b80c072212608607000309032040c000e9012984a19111040010710042c1c0703411102512081000c03030048034030219100c2ca141075242800350396901000c0c0128000c0c4141c40b80500b4043d10448040702110034031940038000c6000340d4078404003801e04891082103441c1413100035401001c00303441d245141800354580f540640141881e58900b40d80c1c0e008101070b000005891800a0783e070303100011546e6084100d00b038001c5800d141440070828400b0000c3c0100356420245024404104801e41d0035a035004000010503a0f6103219075407440052030100440d400440 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 948191582 1250 948190332 948190343
    0x6121202070b040522020c070b0c0d03020918090c150307020606150d0e072103030e030702012c030f0f010615020601053a05010506010c02031c05070b090703 69
    0x30161000c6043d10161403005050722840c40442016030100d100303600340e024601d50248804404001e09021341001440180e102e95642c0740a500e095040101444e690b500349403062054081070b440e9a200e25000d240400314101c1715849440c1c013240341c260268596940035002d03984a02e1909561009180a5004c40d02110003548a0900300420784060a0088000c1c0e0000d000790a40516036422016080d90340c0c00035500f516480d500215100c80c8040d42d1088503e40404c456001c140d450300c42c40c4400c1d400c40014608050466000a24406400da01160700146603014150700d07010240364210803e0008080714000300c202041140c584100464464507546480740006e000000d05007940712103129540500b180780e00348020840c1d01c900740c40000840c081d1030301284911080e07903c059102007410b0301805080d44158500142501c600410040c10810200840401a1000502c002001203411015100384a903400d045429002d1300300080c1c48134000341e082c0904014041980c1c5d060328040c4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 948192832 1250 948191582 948191593
    0x804150b060a0f030c021b040908040f03030507031d0d112101061e0803030a020a050708070c03120c0b06092805010302030606010503071d0a09050702060601180e0114010306121202 79
    0x454143d880751102140d002c10303600c407541c071f440441ca401d81c40048554460541d490429413076213050207049101d600200c0c0070a0000403480c05040d0090030350b41c0a40101c0700c0e8031400c0c002000114004541040d0020814031008001c0b0304a0758910380d507441c0c240d03441c8000503600e405141030304c0d000e01103600c101c18200403440012a0217104452010040d03030302c0840211b103540c5074101102c4c0254040074640f0208481030060304006062000105610380c003c0c0400210a0f0035802c2c51a400000040c20506011180c041000081c01e42e034a20b50340107004441034000c0d691103d0908034044038003040058000080554050310b1049544402c0c180c90003581100c8069a802006448034441a80d03183d000c0707107030b086c0d0b440d0245900c601110211540602030007000c50769101c605050700e00648040006d40c016404012080d6442102182c003138444584001c031075031400d04801540c80040c0504613040c48111080607042c1d00a8000c04010241094601240a802e003000100101d103602910b0050081 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 948194082 1250 948192832 948192851
    0xd0306050909030c1b0a0e0c040303030f020a0219020402090628020f0304090b19060e0f010912020424300b0f040f0c0603090201030e0105070804150b060a0f03 70
    0x1082e120300c100708900810303403021320745c00d40c980c11208038000b9030340480b0418020038103800c1b010700c00f4056032808121079213860942c540a03042d0303602d01101400c0c00b03205010b034002440c2e0000d0102d20201010140c2c081ca5016400410003921405c08002d42240c8009411184481801c0e0940c81000c0c265040a4071010b180d40200d0b00c8501a030100805a4003e000078450010346620811402100900d512011120b10349030021640c2c1d9035220002191220b041501c0c141400c20b14500d0850003480d007003112908103074880c0c54042801e54064040c075034a11301034201d1442589951101c0302c10304240305034140d440c0c600060300e05410f2950903030016040b116000c00218a4142140651f001d4110752440c1c0d41c408895540c01002803041c4c03038a03108000d60340d0100b041c40c035500000e02110740c1c0114181c1c0090002405840071540380004a0303140804000031f00317911000c0c850304103a0160901041c6410000040098048a500281c2c8844001240c074109a0000c2c80c40040020503202440311030380 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 948195332 1250 948194082 948194101
    0x17131806050d080a020705090a0b0f0108010308250c03050607090605040b0909090a060e0d090609032003030408061006030506090405060103063b12030c07020415080d03060509 77
    0xc252242075046400310009500056009010301035254961040b40d12159075000001c4031201c041c2c50349030482c1d5807040405070500b01402c0c2c4d042c440d0400e00302b0105552441d0345d0700507030744180801e000e0b03c41c5040140580315070401d1404480c040c1c100f05141060380d1a07040c1075860304800e441b12408554030a0000900c1409401a10111130f00c0304c04280c1044d42203428008a0076006004000758060000b800380090003a120f03c2664581807801049800310020000e8107030148c5801400500441450400006003c0b0107141d001e00342080c40529901018030119285014940202d0b1440c024101081454143c2000040440309156810f0281751212414400302c0d9000741e0300501290000703401480030814503045010140b151013941040a4021a0b0b0b07200c0c02e1004d40c10b541541b8400e00d00f0102d041c0d000300811040760042030170381451400c1540308000c081c410010700901450f2140e240b820b8207100510f8000c020981d9000342c84100b00b6a000040040c01c0e14000c1d14401c070011800704185c080b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 948196582 1250 948195332 948195341
    0x3160912080d020304060f15030201120e0316080405130f0510081b06041a27240706020c0c100207050d080c010f14040623040f171318 59
    0x160071001082c6084503003000340c00030798802002540d4090302c44583d90701007245071050000d07600c0840c01c00f800c1c05046100050a080001d480005014100001500d190030044100c130300300d070f40e19a92003d000ca03491611104074080c2c7c3e0701295103c8902024207401000d0798000000d25898000c1c10085903884480607100d0f00741034001c0100315071000070300e01c010542c000c05515490350001e040a043c195940580180944e000302c0382c4007003030700116072070080800b051296140340c0a002c0c0d10040c844942c0d07020582d48401e4003a0419201740251210008040b810b080f501020780048003907540c0c002d00d00e49556188a810507443c001c0340000380301c240351840400d0f114191140248240007a081170388403443c80781c07c115030308a590b540c1d4140d0031410500900c22120703512518446808145011300f40340d401c0300e520242104403840c890320070040420781c080600b40d000c0d03440f4a80d0b407031001550410b00301c6030005032070b41007540f8000250090106c0307140d4915000c0b00c040d5400d084010504070910001c0d01c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 948197832 1250 948196582 948196619
    0x6040317010b0301061b05012f0c19151a010e041e09110a0909020a14010e010809011b09051002190303090213090b15091b0a020a0206031609 62
    0x91003d10050144902c54080b02480c00c00d9100128824242030300c5082c2103680390762010380000c1401c00d040c0e0041107031500c80c05c0c00521000360303a410020303c02d0141c0d840d06482c442201f880b40185500c8010494954400056512455000c111030614483c11032002d004102000d0b01264414210401c03500d05400b55940d1b2564501d100107c01140d061828003400c81000115a0300300c0030108042940c952140420007448501c002188551042c01030002c42096a08211038008600700e5500c16a60061042600d4260a103030603001507590001840c01003c0310302088020080b1588004003042d4046654400d90701e080350201200b10000c0420b13a501e200445c02c441d0307090140300b00708010074041c2c0e02001c1050f0018040d0095039011078a40d0702201d0081d582100d12030880c0301031000c1030005891f00350700417000703942910301402e02070000e0200c40e2811001c00800d80c400203040b01141d20038810340860741e50281113140c60381800050300038450481310142c00000d9403802e00041c1d44404807814001e0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 948199082 1250 948197832 948197849
    0xf0807230a060e0307080712091719030903020303070b070201050606160b04080f040e091204050117150a080f010f110f0d2a090b0306010e041805010e0604031701 71
    0x44050358680b0050312007140c0041290105100d98004143caa200400c00140704032001d25103507a81681c00f904c0850213030041c000ca00e52501080120380d20014140800c0070000c5a41100045585412540c1e6042c580000750140030101e43c0f2020458242480d500410980d0000d00490303032410140303d1140285148610104800340d110303404101c04e040f00c1e9800030f0150407141e1402c4074601c46200703164410780c812503503141220304210f00355005014007000200c001d90454580f0b464100002c01d581009900e181c0c0314102c04011408208100c52040b500b03800c05092006540c0d0781d0401d65840b4044035030703850200d50a041d00ca980503036491007480f00f01d002a101e4241046580d030031807011b6411030400324008a60307508401558625108900300a85202c052002c82c031240304a0060000301c20350300c201400c0c0414402c0c400d10f603810020102900d541a00c000078520200341400400c0c20341228050425468698401080d500100380d1510071806030f250021806014030000320311240c24461030a0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 948200332 1250 948199082 948199093
    0x40b220506360d02092e0608061905120c0a06051b0316081b060f06030f06070503010b07020f09010306021e0f030609250807090f0f06050307020a0f080723 68
    0x51809580c000e4006d13403044550b40118408030f00c080804a003d001c0c1d501c2d040d0600750100302803a481f07000c3ca43c0c841400c1c3d8a031440c02085083c05c01e03054055019143c070500b096407034506400c10400580e0004034000b4004280d11b80d6842d03029200360300c0a8601d41503540140500008280000100c9014481d52180d80c80b034251152541c18031900000070500100c201109401c0303241400f041454040c04a901690905082c4201014a0300030355034190322058100d581004121034021083d03a045540e40e401c0b05580754080c0c03001410b2451108190355104600f140040b040c0308082e030180007054104014042c07001d07040c00e0000c100b4028030754011030307860080000031120704201120b290820500000818501c81040455501a011494020010b0800c8041210a070742c090b80cc40e0080c91a13404540d8010309090140807010014003950080c040b0000c007103600c06208101102010707801000c0502d0003480c0340343c811490b0703110b60800c1d00c00202c903520740c2912070b408500c0d400d6410003050040a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 948201438 1106 948200332 948200359
    0x105071a07021b010c0b0138030603070501090e010501050d0608010f0e06070315030b0c0c07080d03050106030c2102040b0f030615040b22050636 64
    0x24100300d05d006400010681038003c00e41540c2514520350740c1516a100c0044840700905015850014040780310340f80f01c1800c20155016007000c400307451215a49800446480d42e00340075040e6056440401003110792b001d80001e00d0325400c01d0001042c4107030742e0b00c1820b00b110700d0904084400d030b8550000c170103204018010300764810041c0c2010003040061008601084002d400000d28000c82d00010800400700441030f03501414118040364807060f112603035680c0b034182001b02e00300824100000405c035039010303008089030307609280d6541c0c0120f074404015030150300080c0c809049032a403c000106041c0144802040e1032440d2105561b524107100061040200202c20407030000c00c0148020320070821601c04850040c84e00c18402d11320012000c00941d2042c2e0309a0102e0750114000070701d00180c0d4101108801c00501c200c40c408580d04203160b4465121200000c10355000710540c8840 = true := by decide +kernel

theorem cover : BRFrame.Cov 948021582 948201438 := by
  have h0 := BRFrame.cov_init 948021582
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948021582 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 948021582 ≤ n) (h2 : n < 948201438) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
