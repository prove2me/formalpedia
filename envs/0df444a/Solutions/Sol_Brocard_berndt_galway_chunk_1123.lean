-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1123
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:20:16.968431+00:00
-- url     : https://prove2.me/submissions/94747b0a-ef4c-4a04-9a2d-dbd2f42d1ca1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 201798561 ≤ n < 201978417 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 201799811 1250 201798561 201798593
    0x40203040c090f02090109050330070b070305272d070b03010e0c031902030603031902010c0e01090e0a18120201050105010908150c030702070518100b031003 69
    0x11095841c0c0e030301c901010581e8243c4010184560303001070002515a0040001006054150000c150107214540503200451805d002c00032410011a810000c546117501118400d680c404500c1d40c10b42003c00c0003401030a02580c0ea2500380e58a41090b400c50408071315081a10a80d03400149440150210300c0000981c1000f4101c401489400a81010f544200200f4004028103280030f65a0b61403c1840254000050100301c0c41910800c05c0c0000281c84480414140b09055801070740c0343c4404000900d10f1084084842010300090410b130b0324540c041d401000490314540300c0f0b0814130041c3d4011208409a40030b003c04400c0c0e1100407132500e01c542e5222485088030301e006001700b40301d552074a14061098480c20ba005039141c100500072560b00560501c000d1170407100600100440328581820440d004007581ea0040c070210010349018400c0200343c00805018000c1c503003c5020508a10094100b15060204008055000980a040b1700c045034420310328000080034031401c541c0c0d507040407950240 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 201801061 1250 201799811 201799823
    0x4120804090c0c05060c0a02190803070905030604030903060b04021c0603030201061403030421050f0706030c090b030a0519090803010905180d0c080d0f0c020d09050a03030e041808070b0a15030204020304 89
    0x484660040c05624a1289c11400b4055407130b205d02d005840108002c242381c001134003035040b4506000019401a207a03c0c25a5030005011a041420b071011a0090007690040c0c00b003103001824406502c841035001009880c00780d030017441030a86504103e0440032b01c031002d4a40551041004116000c2684461000d007580029a1070710700e44551500c5140c131000071892105a0440d1030100320341a014800c0803d0607249d070800f018200d28001c22250180402070000f031203036480d040066084d258480c10f14040e0f8052071030030460203141e828207142d680c20900800c40c0e0140b0b09004903c507a9800c0e68207100040c2408010070782d581c0840760844840240910444907231800b07005494149440b8014040101401d220014680300c01031802441c010a0581e4ae006100d03940030300740000c4d110082d0f0581540d4242c10003442451024010500900c9407640800c8401c04c01442d42c03080003281c90042585601038802000746866141034201100d4076500102c1c110305440004100508042c0c01035540300340270350 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 201802311 1250 201801061 201801073
    0x15020903030a1205010e040804231306031106041401050c011404060b0f0a0605031f080726070b090906060c0703030833041104120804090c0c05060c0a02 67
    0x401092650b0050210030010030440309151103081501d100b60f600503d40403406140908003500e41040f81d10950040d8030029800300c4980501034203140000c41c000d00040d010f0852001031901e104002e15032800100c5001c00314041da17400701c0c5030000a580590b0703a11039001c6000e034800c40c01543c181e44000440160741d500c40010001001000c1c0c00140314600030440415825005010013020540310000e00340300d411100d00500085070b100302a00d50100540c502031490000818180c200c030768095101010038401c1020105000f10040000c40070116081d050f00100c40140840c0ea1300c1700102c0c09015103404050080701524986255541c1d00401d014008514000c1e41c2d02181d41803034101d80007940807503d6241409960340d180800a104800b14121280154a0420900c07000091200c00148681d845243c22403c450403c4110740003000035050850080b031040c9020341da103400a20410202500d00340e044810607020b0b02c21074403c43c1d400307805042645c0e00c8402000030b0f90890365250b0110710600b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 201803561 1250 201802311 201802327
    0xf0f14032a07210b040809010305180d031104170c01021e060406050c190207031419080708130609030317070e0d060b030a050a021e01140c190609051005060d1502 71
    0x420318040c0030f140506c420f2591861b10200150650703c014201b52a642c0d0103ca12040341c00e00400c8900034521146004280c40c403242004400074000c0703401a648460f01c249190b50400800036000442d06001c0e003e481411003410b20510308800e8a03400d010498010000040000b0620740c0107235480440701c12190708252901c2840c2c001e18600d1842d00015a01462060080c0703c00c0b0828088441c2002c0010400c40a080110301d03001c40d10550000d05010010403100100705071003050b030b0041c0d49003600c00c01e0140d84c0d4080c020081c0d00984000d90209400d107223440c5103100840c440c2e40c41404652981315503803a546040c003200c0803c6110a440c420b079283c0f1044000d42e03041c4100d060345c5000380020420040d04d1300402100055480b4a8202844000303444105640c00401c00c8074142640c072841f9469038500d09105082030341d011f10085080d100310711000200305481d4032245980d40a40122011650460700a5084407000c0d100355030303c101003200b5040020f4140d407108603c0b20358071030050b08155007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 201804811 1250 201803561 201803573
    0x60412080a121409120903070b0d0b030105040308101a031914160e0303070b130809093c060d0807020904060b0907080103030c0f0f14032a0721 63
    0x944a41030111801c240c24130850481c01c001501500300e143c10031502c0d22512400203642c4007041c2c4074481403c3d20115801c1002080e40c2d01c80c00c100728004d002400f2502c0c241c0b60082c100441141c0508488084100100305001c55000c180407078244103080510f03544580801881c800030340d00c5807190706502c0d012140000340707151001c24025006410700307030034410111001070100d5031342081c0039000742d20900c10000415110b01040d500120280f01c005058403050070714954070312404212a8002d070204040c807841040104041030f001d17080c403280b12002d6980500d41e0240c1341080140c49003110692022802e20700e0b02c0016907020a104844691602c003095010510344101100e041d22115511041c0b0071490034030b45e8074550f02941e14501211a9030541d5405000d00509020161100d02d80440c2c610410079060444612141c0202000c0d8120300c01d048641c0d80c0342d20001c0d1249401001d401c0b01283c0007481c01c052104003181d00c0103407500e41d05244642130101c401c94007449005043e01654004100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 201806061 1250 201804811 201804821
    0x40b040f020609191403011b030c090915031208040c140109170f01140c1c020403020d14011505010210020a03110d06050102241b04080f0105010e0105060412080a12 72
    0xb2400c0135a00d200c03481d040076510004040c245c2a80a80d0410841140e0100920440601c142c4541030000d44e10b400c891080704d10b0043c0b900040c00b0b0724030300f5100807007403a504c0e11200c1c12070b0701c5a90100c045140642c0100c5850200f0b0350003c21402641d20f081c0320a41d4809503051540006140005c500d90792810b08268044e1035880071005d50704540c1000d0000c4400b03008482c01102c1120b501c038602d050500d026074080c890158012038032200604101e0304c810441d01103a005540040c006441900d039400c0503c115600f140c0c00342000c0d072030300c080c48001020f1103200b2000c0f03a0058018086c038400c1003003040c0295215044003000c25641c1c403c2b08800310079234009014214038003c0c000071454103240000e85401c04210319101c00ca401580400c0703040030a50015548503502002e8000517004c00b00c4600064011600f20403001c1c001c8040002c14950f05602950481700b091a500d54241d0343e40c030910010388180d000e440d18043ea040110008500c07560000c0c40c031240705251102400021148440c1224 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 201807311 1250 201806061 201806089
    0x1802040c02240f07050c0d080405010f0c02010b041406031b0d0f080703020d05120106110c060d0905010b0f0d03050c0f0706030501080105062b0203030909090102070515040b040f020609 81
    0x3403000b0090050790f80c00e2618241d4402003d05005180c080100b202c15625207140d03504074100030f14140003800f0440300390001d081c00181520244110700c82040702074042d281995030240035030320b482d00100300b4013071403c002d6000d0710014010700640d5a02124001100d240300f01c1c00c81e0050000d0381c2c0c000024001040c11200640502d84142d1924a249402801d20481c45e4242080103000c0c403d10840d0341c50211046d045960604100441010450129080045081c03c9580c000f41c01306224003000ba558108144a61050000300301a041c403100300704c090410700c802d084e0001c140950890000b401000103040c41030212040b18401d00c464210281340281c1d5070040340000f91210010050710609014440d085401110140c4880750380d00680c03860840c840c2c8081d1001403141180906544051048405005025040e10014a04001c526010390710290044a030f0f4400c04d0342c0c0814081020700f1441c025540008178001c2625a40c42d21203002110400c1070740d00210400c019621540c4ea031a40541c1c02c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 201808561 1250 201807311 201807373
    0xa09020d05060c03060907030516050d0f0e0601080d050423030a050a03031b02010507080f0c0c01020f04050a0501080f0c070c0503010515040c020a03051e070c03050604151802040c02 80
    0x64986002031004006d0040c0c0340c182854201020b100c0031040b403100c42d5a041d0200d18081e600c817a0365500c40006003014071030804055142c1042584045400720701c4074142c0c0c00c1002103a01d400c0074032200322060f10861085075100304203146503208403180944c205c009040b000302200c2080d407440c0c603000d04140e8540d2045000c241e59520024410a1070380c02c4d000313888150700080000345018480a824103100034000c03844280e660000680464215060700c51021080000b1501c82800c40c1d00a401c590042c00345c0b910030684440300103510341c490180d1a02c180e41a502c45081902c808a4501c4981c106c01021a03c20b102c510004c50151002d202c1c162140303001900590f518200f1106100031241c0c10300d40c8030b045401003100b000101c0c1d002004c0f2900b1300b00200ca20b02d805501400310310501d0188041c024031300c0c05140d8001051100000300c0c00d0041c0c1c050085080e02c3c210740c4d9401801c441c9043ca1f40e907052000240780781d01510f407590103d80b200d101401503d4448004140c0c2d541c00341c5034074503101c1b10 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 201809811 1250 201808561 201808567
    0xa1407020a03030b0a120201030504141509010e070f0b07020a031703251d120715080601020105041709150d020c07150e2b0605090d0c02090a09020d05060c 68
    0x2410341c0f6000e0a540301c42d00780c13000041c41c0d04150210705041c41221000c0e05043e02c500119040001a421501c41c0e41842829188141181c0e0807110420380259405012982072a0110a00103804501302044030420741d001c54000740390200704e00d09038000d2603050360b1007001c584001000c41c00304045441c1d05440c0b52403050380c900d03240004034075040d039207280d48101030700580641072842d0b006920f07603010841043c0903598890405000404030400d500007952035001c2e8200001d4460345c1a11418210896900c4002c5203039a8180120300321802220042d000e00300c5500780b013101c051210300500c50000b029200010340d0b5886601d0b001540d12a40c80840115800298028030640500400b4085e214009903041e0801d22010010685041460058030601180420104184a0181c0d0141000700c0160350705240006040140c01407000b1500c094050160295110320507201e0018125138550041541030540c542070310031401003000c0002241c00c40f140350710000200303071704025880c03040081072403140e9 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 201811061 1250 201809811 201809813
    0x1d01030317040302120702040605060f120a050c0909070e03010e070906090908070605091c0e04050c0a090b0309010e0307050109030e010809120a1b03030603030e030d020c06030a1407020a 82
    0x100c40041400714088401042030100190f408225090480c03103024001e92985001d000060003400d00c1d501807a03016100183c2500108604400380c4011000e58010315035680d2141c0c80c020940301c0445901001040401003080d9a08d4003c050681041a81c0f03001020038a400c0046421580d03440321070401540040c5041002085074094032014001c0d080c0203000101d4070b90395101c0b003405845030040240c2e80307440000e40f0b007000400910801d4002d44660040d40005800044c0800750102311060049062400113229112880212410f0741c0d250390350280014900005c0140581000c1d21013160b954880c16142e28416040015004503809540006604080b0340b501500005008801c58140403000080142081d400701b0000c894a58201c4000d075500303440c0348120340300011001a0348040031000304043c18550b042d0701140599100c0e446a0f4103003110300e005c00d940c0b1140f4098540060f40f03c07103070341c00c810b0901d4005990032410340500404c3d4055071001019130702c24101c0e035030001a486094598 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 201812311 1250 201811061 201811067
    0x609140906011401050f0c030903070303031b0c020603130204062d290702150403060902010306080f03041a0c03032811040905070c1718031902090901061d010303 71
    0x9004201c00301c020300030f0195090002c2c0603801151200c00400e1004140c0448520060040b156682c81c01407c1d107400f55224a80580200750f0713100f0440020602c07241c0545411b0051446035202900108114210341d500702061500880e40c090890300161140000160401d00e4071038401c600b44403001c0709030621203185030041108480e40c480282d9056035050886503015520b2440865000c2c030000c55078030000e9001064004d040305503000100d58000600000340710079540640701040c0300366000c0c8411a0380d1071181c0d070b540130ba0340310381c503065041004100300b07000c3c84540b040c03010358030300741c800d4240700f40594a541103400c1100e003040c0c0c2e00c2100b10180d040c110744c401e05060440004100f0011005034848244040c040d50258040090b598004211902d018800d6210001e6000e00c1d64008144c00300c00135820f58200300c456100c54a10b0041d004c0c0945000b25a820f07142c00843c01c0c5e510305101c0b5800300301039184041d00f0f500320395603200004158883d084046a1a60f0109182c14825501d1440e0003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 201813561 1250 201812311 201812323
    0x3020405180607051b0a0809060304080c03131707360912180308030c0a050d0e0d03060f120206071b080a020906030a030905010305060612010e04021203041203030f06091409 76
    0x44200c5e41c02c010940d00002c4c02c00c0d410f0305d41d416401c1d583c0c281c6aa4070351274141864450144580000e11000c01e010079420f5a20740c403001643e2041210803403072252581919902c3c107881c0140c0c0440c801d80426603a070320b48024284014501040301c00344894200702024011210316003015190300710840070400c00103800c01d82550303100d01c80c070010041c030a03d151900d1503103000c042c01d81c1c1800c40c40014002c3e003861003402510701401407500200540b24944509079a680b100001240105c0d080c5240064007008035004034088511400758417810303180c0c513400c00c0195440241c0440307007a1100b010901054000d131406d03001901000005181101c003030300402c1404200102924881e078882000f000001e03600600c1c4401300c90b42801e0200d105d80780d00c4001080d42c0a60442001d80c0b0800c2800020b203414601443c500075402510714000c01c1003818022030f200d100d24010911010a00c40c00c01d000a8440e6005100340400400b002501c682c0390000d40c825910300e24a1000c22003101800d01010744014040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 201814811 1250 201813561 201813607
    0xb130510020f0606060a0c15090605070302090f13020403080c1513080703201005150114041e05090703020c0c030f0d05030901090506160207050411040302040518060705 74
    0x81c0072241c0c800900a555201c0141003900941c1d02286c0614654010074505240e240e01c0905038049801c00c40b41c460083c48a08020b86800b410100403031107090003803003150b02d0030310090b01102102d0004070600c09070714007801003039046507420400000030501202c09401034404a0000c2c01005001042c840c844840c01783c2100903617100b0b10120000219000101d0311144d515003000c403004058058a01481a42c11550202c5030095a00194441095501c42c1c1c0c403405034000c244588000d4500115580c84030f4481c084961402000240079145105076080c00e8580d001c5150703100e80b600c03072011444000040d2460008250049040320848005120101900310250010800b050000b4510b5540320605070318003051000010100b10002000e40051502580020480d146030414207403110140e84894000401800b4075200071130b1500d8540180b0b601e00e40850750181c2001d00395000c000040601800c0c0d121002403141c14491080750a005032031081c4107640b5001e40799070024480d22207810708112 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 201816061 1250 201814811 201814813
    0x603091c180b12040b0613020f04081506010206011703090301020a030204030210140417010209040e24041703070c0b0103050313080705031002070c080f03030a141603020c01060b13051002 82
    0x20219048000c118030641d4085e40010042c105600e841000c108189500c900c11854a0700004003d0301040e03d010040003142c0540007150782d03032240c41c10a80e041d6031041e5109801a04082c004000301002d410707500e4010707807590041e00c0c42c050824000a08a078030440001c00800d8000c10100b040d40342c540504081411a82840c400307003914000c001142d13105900410000c3c4c0b8084180b2042c405c800d5040d180c10441c046c00400681c242c40096a9680c0486010828481628429141d007290382541050003664441c080c0403d890070307002d901106410090000040100120300d0801150102e280980250b0256004d03554500881c003d009101c6a942c1107180e099008420400842c1c4002034510a00d4000040058440900f81381042182c001544100012f10030919803d503881008030045001c1c0b050401c08001c0f0705440c0d01201500706088501c072031506140080b8443c1c05001e0f40060500300c494200008615071a0751801c0704e40d8021090401c08491041000d01007414002c0c505100421280 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 201817311 1250 201816061 201816067
    0x50405040c030206030c0f070c090608030c1b060f0a030501050301150f0510030b030708010c021c0e0910080706050c07060201140a0207080904050903090102061005010203090603091c180b 82
    0x34403a003070904020b1000a00540b00000080c40d042c494900b030383c0369620000032850795084281001c3c94100100e008822049161001c0011807130341c000b044403000d0481d04050301c0464130140c1d000070761100001c01290040c1c01000381c031a484104100030071450020b910006440d5040500345821617608a40b41900c2c910000c8090010501e0b03441d43c042107860886501c0840901640110050002218940e4142c0301d181d401240c2d034a01034111050100e9141d0856582d28000e203022020003c502810301d010460010b4081d20604168503120750040c8500b00800d80c4542d1180001c1c0350050b15400040001e10119501484050a2104200400051000b0b110328003401100300c01080c00940302c82e40103903001940008210f015810340c0c0c2c5441d070081c0300b0040c0b890290241f0b6101c4d0f0004d02024018000d042c000b0704a2881e018074075041d148180d0095082c2039109060140c1c650010b800d07500311b0720a61141c14840300201204040f46415035840503807803c4009005112081d80d034002402400c814 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 201818561 1250 201817311 201817313
    0xa081806010f0e0c04260c0a12060b030a0506090a0c1e050d05010b044b1e0504050307020a1d070507140d09170601230a080f011505040504 61
    0x211030001e003a1040e43d000003c25444880b0402d040744a01d6208039101550111080f0381d100c4254041d1040c1a000c03810b540404489204102007020309000b03940400da04200ba800216609070321207198480090203c5010211607100d05280020480e4607001c1503000305140810445158007101c0105000049665100501180300342c04103c40c0c0a41406418081800000d104094004185410000e4402c211025254400c1c004580c01d20080c088045169010f58105000c0c50050b058022090a4805414040d1800c103101800061a603001882020008d0078490000ca00c5020300503407042c0000e42d6514418818407910140e19400080301c41440c2184500d03420300e545d100c2ea801155490840d540f40c0c00c62400480c0015080c03419400c51180c000c10b031203032942280030034003a14805014080414001c00c070941e86c400b424003502c81903100800340c0280250b40340b141641400002003032560f40300d1b200c541107450040101c40d038111581d1281596644c128401500001518060350107100381c1c601 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 201819811 1250 201818561 201818579
    0x1031401030303090503070602031e06010e0109090c053010031a07030608060708040c050607021806120d080709090b0306041410020703020a1b03031e090b0a08180601 73
    0x1407201030709240c0c03a90411800c00c8020301c00c8800699004800315224203086101b103070b4800701088203c0600307000c24040303501580160342e041e00009059403800d14090802c90400d024082c01d100c40400e2201c144000019541c111350098111252410580d810813040800700080c40740c050048032902450a5080c004101c0c04101409808030034155680c0039203a0481c00c5004210300e52041409024120500c1942580515494082c6014a44000e083c6071140c042110700d100c0c1410007075101c0000304030b00c0c030700c0c03200700c1211548144018070520810501c0c101c00da05141c0301079080000200c01404115030b5541055803500074040020301000700c800d03c40701181c0e88410140c07000d03100e04000e0042c0c9880500c10000f09503460b1140c6801d540740c001e03e10707005e0b50350f54080030700b151141059000712050008c8001c109003140e8040d9500101104000080c0c5c40300c080c00001501006401c02010072034080c007030000e0001c0c088d2641c400a05192080c092910204c04034a00a505d80200d8010000952 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 201821061 1250 201819811 201819851
    0xc06010b07050c1002160506130501030e010605090f040c0b1603030b1f05040e010b1201050d080906040f140a0e07030c0201060f030f030908030a17040201020a0f060501140103 77
    0x15042003403941c6654034100b0078500780c0c6926a01da032061030a0041220594081000c40107000914504c0c0245915202006450300a554005264608000c03040040791f10903000300816074081c0300000303519911003010503103407181240d00003000d607400c2d4284001c00401509a100800114450030305050340c0245881050500c03103405000c00d9103980e0341071f401d40d0364060131042480d6405900d220f00440c1f0072001c4c0468010388610044080c0b42c600000302009003500715510826040c800d9540c40c1c7c03c0200b08100606e111005427002d000900201e161600c0c1c5800400c05003e07910030340c825281c607141017076040704503481c0040d002c3c1100c00000c01139160b030841d000d0340181c014100410301c80b540c450102e00401313480d840b9017801c010348a00001070020007418226401d000b55100d2000d141c88088031a031f240f24032800b0344001503101400e040f80406642b41140c100384144140e4040c9682c0d5200c44154a01c015002c0e1076095484004104044440c080a18820000e00b420301c001c045050000003511 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 201822311 1250 201821061 201821069
    0x1509030a05030a09140d110d09030c05100210050f011703090d020108090c130c080f0415020f1912050604060e0610020102040314060f0106090510031e09150b060c0601 73
    0x190304c3c0c052040401c10300141005030205040d048500b0404400030040030641c1030005071110340204941d0101c4180301d214400162a046524604481d2400060007441016442c080d8218028140700151440003401201d00a20b0080b111380341a50425000700d403006402c0249401c02e6004000c3c8800f0b607112090301f40310f0140c090801e00356550321601e1903801c1c00c2c00105040d40c0004644041000d29819a020242502043c0d851414981c2d030007080350b180110544001d85030040135545ea104600440c6c00500192016800c1e0600f490301080300c603200d0181d00c07544000402c00c0f07900d03805110a8140301c2c0961080040360280710a5150440c4a00030020240480e07006890001807809442d0003501110002c5034440c0740b1140d000d030504180c40e1903040999051001135080000001c07194811803084044e0382c801001071130040c10300c61040c1d0041c65140414050701540c5040030280c607005220300c803066800342c4031b01c165000c2003045e940112400103030010b01c6180c0600481c1c01c60f134000203880b4191 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 201823561 1250 201822311 201822331
    0x10b0301080d3203010914040c031e0b0103030806031006050d02011209080a1d03061504020c0c060c100f09030e01050a0203040f090b120a03020c0f0d0605091509030a0503 75
    0x801c0c1c400c1c0760f954902c0030209501202c07024240f103c018a02400c004604aa41d90b6804001d85111aa041400401c06840c05800e000c0d0704001403012800741d0f42c2c1d01c504081700719400c00b9140003c2e502c0100c1032030240e00c150b002c20b44a1040007154182403000000030f41c0c0181080104500304000225011040c10010341004a0084c60b41c1d03440c500c5502c201d610b80d401c0340d907aa8903001c1000b80141240408074840c000010041c01c2d00410b0300707001848501a110295a030b0b1b01d8000d985003404000e4100d08010b2440388109420302109072100002000b01e4662040079103c461106484041558031030011580d940e40340000000c0070031340c80900c0d0181c03450240b1705a039817038000f000102c0c590300440c0c106c015101d058070400240075660780e100c00000103050703078990b4500411030600f5854010f41c8d40050090307040000c90100528000c02203000700c20000b00301703280b02c104c940c076288111081140d20502075440200c1c0c8412940034131240b140d02000c200c00540ca000c0f03203500c000300540800351100e808 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 201824811 1250 201823561 201823577
    0xf1003060c050c2415120303010f03051c02060a02030c120708070306080609070504051911090108150109090b01120905030c0c06030106121e1401060e0d0b010b1b1b0306010b0301080d 80
    0x1d580c3c075101c0c200360913540746d070440343c42e561111014078000c001840100ca00e440760f810a010b40d21120b445c1e221010415801801c016694600f140020b503200801008070305a013005035590041c02604d0b028052800c07076844880034070300610003600320383c090b401121b8150301000c200030341c0440009007002911801e85010515494a4003482031011003144400d00c0c80342044040c1040d90b0346800505030b541826641c5070136603100d8820058040382c000d0801c9001030804001030003800c6103034111410a41040c50b003442d032801c050503001e080313070201c0300d0440d001c0d040020069440c850820101a0b0b00c0d1041303e0581c959450940c001d03101c1540091014a6a6150350315560482007d800701e0240d0420700f032043c00b0703d50f19000c407154904424010a8041604034034000c2040c107010500380d4400d98044154080d40c2d0814810308905d410407031000107005003d82118410080074096041060803240c41e003004080900101800e00c807058000c688103040600041107100e4000541100c550110704240350 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 201826061 1250 201824811 201824851
    0x8030702060d0e060c070203100c0c020f0a081b030d0302091018240237020604050402070b0711060601121a150a110c0105030f1003060c050c24 63
    0x20141c0f1044408052900400040055000c690002000000e1003202036070f9078016511400300440d10b440c1280400a1020030404006040c4001160340006005044502d607a54501c0381c08d04e440b070310b100e007094602c40990352105281420004144940300500b015414448000045040da0b4240c0100504101000084842d5200b41c2d80d02c81001c1c10030100048070040c44a007640c668144440c0415005200b0a40d1400c102140e00301220121a145140b4041e80c0c04103821601904150383c1c000e0f43c3c0300e0f008000006040e0707101c1c030042c00903d20902e03801042e40b4000e036000c3d00350b40426030764058682140301001481d81c0d200070b1103825131010040000c0c280948880c0d403614181c01c2642d10750090008604284119443e0001d400c035800a41e658400c06201590800d44a4801e5a062408100140040742c2e170742d14424881030f4000481031080141954035151881540c2040000b00003103400050f40c20342c19034003849040a121104109943e200d2030039030f501c2114201c0108541412807400310008 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 201827311 1250 201826061 201826087
    0x510120603021f0e010305090c010f05190e1f081801140903030a060b13030308090307050d0519030504020a090507030b06040801060816080c01032d0606180803070206 73
    0x40619000392165401122048110404250302c943d59800318a600f2034202a66103e40205842464804007606400071f40000542d00f0200707100070003045c0001800401000d412000e40050740c2d40303455486656a0015409002041031000d00d80c202484c0f240703c254000c01d404c00000354000040e0b5401c111494040840280144400c0d680058422080c10500c1507108000020394050261610108121a0f540c030030009103200e01032002d00d8000c408032007003000c680142007169001c0b28440a4a180228940c0c1d01d9003040a06049070001c01d074080b5a5100d06440c2e000d02072503070071503030404205504064001810480251040d84000b5440c2c40014011314840e402c4024103ca0240032140c0300c4c0d0b101d02c0098041e2002d8001c00480348250780c03000003c103000d050818100c41d01c40c0041d102001700d4000440150488110703210510700201650040440c1c0006c490120405405000894506028008200e00700f601c031002c03a81c5030329a009202032076011086a08940e81100c0d02503a810f01c0301410 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 201828561 1250 201827311 201827321
    0x1b150b030109110307060318020906030a02030304030602040608070906021c2a06050f1003030c030509090a1a060406050d05061c03090e0f040309050f010c0b10050a0e01051012 77
    0x115010750900100d1800c00908100c0d00e844000c04400b9215102e4a5507000c80842e081c0f171200084040085d50b0100c05400c102c00740e580c000201500303071003c010040c4c0203c2c2c81d59006900444582c0c1d800201008080d40c85001907401c15100c2c50940c1c94a4605a0000e580c0e400404060b00b55200410307155045e82d004040c0621400407840150341205130303050600aa2484010083e02d800d810140017030405a1345c1c0307040b1b51190341c2d84403204101c60305688045860411100c421000c1c05401c204011055540450306880391084500c0410540045840a205444452500c03030080e20107020600c07015070050140c0b07070145a901070019480d980c1000233051100c10a000b0603120548210500c14580e004c0c045d1003e480c0c54a0b099441074070b40c2c1283c0300200e4006c80e00a400202d0281c000e11041c9042e480c031591070001403400c0117400442d40c40f803184030141925400b180744103942041241e41800000fa000030500c00d283c0c049558905004101280404400303e01040106012500456026030003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 201829811 1250 201828561 201828581
    0xa020f0607090f0b030f040f1401290f061e040302040e2d1207031e0e0a0501110d0810030c030f02010801051903031202040504050c0a09061b15 63
    0x11140c003824503400c0640074207150f0044040380201d0740c0c0003103080d60200c3c3c1240d0240c0f190101c000321554450b180c0304164286410200c80465100002211040d824040d2440d6124003000001c0e0f070358840271541c04c1c2a25284052805205100504046c5a540c10180d5903200d51445881c3d032080304444c07109685103d03940000390302c58030f00300c449404000005a10706090200703507040304048015407014504801151180d42c0f4a030b100c0c0c2819640710b4412400b40420070f1080c00d2080f102c1ea484540c5001450040c0d25a030001055030120540510b08500080e000304230a00308881580d180030482512403040303010300002c2c4010f0001040c1030b040034400040085070810111842c40703440c0e14050f48003d4502005a0016040c034001044038600201180d0f0000c0c050f4681c81009441c580d0280c441c03481d03e1600140c025802e201c0003441d511140507446c8100151201c00703035100b450300300c01740c41c00340c0766000300c0108211081c0d1744403c00d101d00031044840e6081130003c1c02e0140c0b0072098401920034446 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 201831061 1250 201829811 201829813
    0x31e06130c1817010b030a08091c1a09120c0a0f0302071a030108010c0f02031804110706060504150305070303050c031b0604230304060302030618010b180a15050a020f 73
    0x11001800d9a03402d4040014007283c807000b03001400e94002056903c0c4e0781840e029005450401c80214645006d007800f00030f1005034140c008500760240c07034012060f01d10400d10180c0300c0040d81042601c00007800714405410070040c96034184078022400c20b41d41c00b50349000404512840380c000d0181802001014010007401544603a1998050f00c25049a042841079120035070900404ac40c0e96030040040c0f401c419540e500079070504115100005207840c3c0300010700c1e001a910410a10401d2800c002010460b0143c10042016441e244c00c2c4011900402d1141f19000300c805406d200054001c2a0380c02101d070180b420544a0342c0722242c4500314030440040040c080780d4262092180c0c03502288280c400c6003e0b550f94504402100c00c1841038001c03115022085400c10407003840381e035000342d02960f00107001805286000398105514241e02100781c001004044002c079100c4900d1904c0c0715250058a400c1c0c610003600d81c80c0294413074141c0d0701a02414288a004504540d41c240f007044802d0f04009144 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 201832311 1250 201831061 201831107
    0x6020d09080c0d0f050403020915010c061a03061005090403080403050d0207030c0b0f100603020c3309010b010f08070302120705030105100305090a0f05071505031e06130c 75
    0x8050543d90300c000a6540000ca58101d0805142c0e40c001c1c2c1c2600c00b126000761880403196560b14000405100302411a41840000089900460460304c1030b5140c2e43d2680351705520450800040501e0b00c10000d043c80b10012040000340280c1d00e0b5400030307940280c0c0c1401c019000f80c40310300d0107880c240110f03104d2910072840400d000092540c07080000c10080d00603801101030707445080c000d52003c0b404644a80500030b040390f0810206101c0d500420075079000d041542c18a050030f00b00741e05841c44410503500080c0e04503012008204104090503000800030001704030b55a00703a40040e00182e218451803060100c2c00001485880c007d404640c0202d003960200c12191404610103005a00203016003406500140c4909000d58020f104e603a0041c000780b001403a18100c03a41d03d00304201e4541c6801c071150b000301400000d45082801e09a014056143c880d00c4c1c40b07152941c85503507540348a0307403500750743c88441082c0400340e1121502a000a21880800314071040f061005968452840408198004845d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 201833561 1250 201832311 201832327
    0x304020d080705060f0c0909270307080406080108030705060c071109040308070e241326150411040e010204080304030821190f0b04050c120702120706020d0908 70
    0x420113a209120740000803100d51940507101542e070150a100b950015a2140401d0030740b4004100104051040c400c580201c12401a643d07003150400d10f4112541703180440c05225094001d0417031750151400b600210b00380082c0d41c80d025903e0b000502485604c0b0340000c0c0001c14040c81581d80000c40700094040552801e0034900103119034401c4900400242000c5580c2c0600c2c90001d1a90005a01c08840c40341d100c4027044c0c01090503808140c600000c00141400001c0c080164000c120140101200911015080e8080c40381031401015200900011074400c00c00000d100041c00060a08141e0340040c020000044160091003660070544051101140010410805800805600300003070070344240f51310b01d44907000400c001070702c8042105110106198182c0c00a51091041203c4e6180100f140030740d02c030205080307540580d142c1c0f42c0714500044c1c507000d14820390180c503001403003880201030900c1d80c400c9201c0b4600503608001c20307035030300014040c04102454100e1842c1ea900708583c07550724405 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 201834811 1250 201833561 201833563
    0x50d030c02010305070521061206010608010e0a1104090203090a050712031205090307080304030203040f0308030403031506080601030902150a08011701020c0312090a0b0c3103080304020d080705 85
    0x1040310490002c3e061034005452a403040f010786049000c40034100c1c9960419074155151924000c0c0340903040b030201c1c4204c0007400c44c10401140208655240d80307070594100551416881002000c034000c26080c254040010f01518003100c04440980c2001612501c9450b0194144000014003402134425030b0310104248540810360704403644030340c80e4040484000c1000005030340e81250a10031a4209100790008103c0c401c00850313020707100b4030549143c40d8540b00e08003800805508141c2e10200040100300426405100f48641c0c141c00a26130802d0611344400201034a0008108074109a1a03041d040219206d1203001132034001c800100d0340d210f00000c000205071030401d10800000c2c00300481c4550b400e230818400c0b95190203004001e5484d0071208011600d030400e025156004030301c41e1103003c80100340002030040c0500d2000780f00c95541c1295500c0e002c0c05c510807250300c0001b9482c468001542030581d1054004881e8041c0c41c1da5140c1c2d44500002d800c5100008018040d03042c00103001e000c00c50 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 201836061 1250 201834811 201834827
    0x6130509010c23070609020d17190e24040806090307060b06031003030318050d0c0212151602010b0d0501060602070608132015040302031b011202030907050d03 70
    0x12483da03034a440701c000002181041c4030301102102c1561000c00c000c0780420703034980004442600240030f040c010855070342c442d14170580c00a040728014001007841c50130360902c14a6440204200c1c07170030407602da0059000034282008110f05e842c07036000104400403a020b289040d81c0041c10741e0016034039245000c50f441a10703503125403000c07941d0900e0490044070300c1c07415200f902e02950340083da801880d411035400340d0091000c4103502c808219003c00d9040003603410000d400c00e40210f591809480035280c410704c408400d03d43d45201c2643c11840c50b44401c0403001c0902a800069a100104010007054082c1d0040409014280c0c124500e8051001481015080313001100d9056003155a0b040d43d50108883c3c00805441d00c07480c1a200d00c2e00140071500c0c3e1216048000b881942d41c0f41400000b10000b49031b010010950407405d407010608105510b018000c28401d0750689409925548010000810394a2850b01e6002c0301940480403e030010300c100420005844058144003041e405410060404c031 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 201837311 1250 201836061 201836081
    0x118030207150206010806010902090f13020d0b060406050f1b0f030c2529030114090109090b0c071b03060204150f210906050c0a0f0c0312050613050901 67
    0x1002c40540404520b00c0014039904845012000d4a00303a42400d0a4030041c0d40124a210b41c4080c1026042810365900d90404e01d041500200069a8101c4000144207580400c60080c1c41070b002400304005441e00001140c50b600805801c0f50340d244000c058961091301030901c07540d400d228602401440304800801042c4c0130703941500b210b044100000448030a010f00442000303c800c10b0410030002c0c0d114402010300740d600040d03540150300c103034619025443d0304264050340740301603103000400c4c0718244451a10302500590700180300c0b000c00ae03110649400c1c0e01615004500300c00080c140240045101c0700310051460040d94140e072a6203041c02c2e0301a410900940041940b80a6844903aa004413141d000f01841c548880c094135485001288072402c5140e107000140341c54211810004000d881420700c940d01008000c0d890f034602d414018801ca407020003003810320002002420210790020348410000c3c240140c081010b50301c11000c20941700301e28000b800c9050424052103032450341904251540 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 201838561 1250 201837311 201837329
    0xf070510020702031506040f050703060515090d08030402120a05010203070815210f0a060903020d170a0c0c060509070806150109090b04150303090302010e0f210118030207 75
    0x6080080400e000724450714000030742c1544698114009030b020340d40001d50200b001003000132103c0c4018410403c0e10400c4a544c00040d9503200280f02030300c0c0003002d0100d410469019141081c1c8404003094460329401c0000d011a43d02100150456032400b803104504540d410968114a9151501030301039042915400d011510580c00a852800301c034100d10803000700203080c0410714082121001280510000c8850381c0c0c0904000c4080b0800c08101041d032642c0b042c0c0f0000344450b200d040090601c01c1c9904651b0411013601c00d11072240d1040a0319603001070101b400050105452002580d00004610008260314208020080c00030b0000c0383c3c0c0401c0f103180c542541c4c11940c4444014400d0205c43d41428003140d4900070512009003a80d010320307c2e090000d4000200800a080c240310659502e0f40101c0009101c2c820500865034449212414040e050303480d00051000100001c84219040107808040360100c021040710039025000092000140c220f06015510541002520b40b44180115845 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 201839811 1250 201838561 201838573
    0xb040609050a090b010e0f1219060f0204061d1305010e0f07030b130e2401030618020d11030109150905010605030d0206040f03020a081b01180c050f13020f0705 70
    0x48107031a004411413800141c3d91411841510020031680c4036000f41c0c1e10b074210030b25007204100190300f00300d8024110711025280c10310a026141030b1040d00c4440b070014204500501080200d00e8011550f1407034403842d0200b6000616000b40480c1888030b045203d004c2da5414100000345000c000340e896400307480100a48201e55940020540039075422107d05034002440c0c0b088030020070000ea01c51140105c150041e01c0b41485c010101a40e401e0721204a14040d01c0501d0041042020b40e125816074010b00e40a003030f042400503000940d8011240d18068100c03601d01d02000c100b50b802303500600f122984000a030300c1c000b500c0013850005200701b400c01c5910750300e0003001040910300020101c00301d9185030300502160381d442c4d0b100c0002c5403000404505601c50f803819030000442e280003600c642a92a001002d50a04004145003990005004000e582c0c0c040002000410044502c0e6001e552054480422180c02c0b18040ba1070a0007000d8a5050b00e440400d811240b40c80720790041c6800d03801902100c00c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 201841061 1250 201839811 201839819
    0x1140109050603070e06040905041a0a0905030703050703030e010c020c15031b070c0305030d050703060b0a080c03101809020f0109080304090f18030e011107030c05060f040b040609050a 81
    0x5080800d4000c0541c4000c0030700000e00c40d648540200c0c1c05910000d80308900386070307882e1a01e5080d258107440c03c03500598000c0855100510411380da99019041030300030b00041803141c4600f070300c8ac400c500b0f000d01005400204041414040e4014203031000300f550003000007012951000307494100501640e8843c2104940280754031300c0d00e1041e28014001c219083c03030031041c042240302c0c059010f02022680c01206500000100b58144040d00d468101c0072000301d4039140048009003156081e070015880300c04144040c100c115404a03030f5560140c00d28032031036034035100e180405003030b031401c1c0e80881450004610302c40c40394146c6030131140c120b903c01d4405580f08000c5100641e44038081e03000d8149164802c0c40108100e0045400c105c103420340308040001c044041d03040d0540e2041d00f00381e0a401060200300042d01c50b50344240765509110b201d0019110b11801c554503408142b81c20300c1201d204042c0810703008000d03403a07030b81100c00911122041555981d510301000d0305051031885801d1041e10741c098005 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 201842311 1250 201841061 201841067
    0xb030f0c090702120306041808030f090616120f0b0a170d020c010f03051306020706020a02150c09041e15090506010507110925020f0609010204050307050d170d05011401 74
    0x404c00760b2114000b505554030314050000030040602d13500d41c240c1074483c0400116001d080118041d025000302c52a07203250101c81140b03406030103006900880541286203d80a41c07220141d101d00101c1c88021543c00003001d004806403041c1c600403030b4082e0f00300e1800540100304030000c801920000090303403841030100d441070b41c0301c01d129034240d4045070340100b0000c81e03144240d00ca80ea01c50404450740460201503200c110403a0442c010855186a0029992089139010401c2441c64940d407140f01426150140500d1540c0c000d100344507008513154190047c40128213000102c095070241810044190f4030350264007030026038821502064908008904030f548100c045030501500103414901005404003400f9801400610f001d01c203404240d281c04440f02c0c0320b540e0f00d80c41c000c540d000305a50705001d011981442c030301410740b4159a204001c20803031620042040300480c0c00c1241d40c1000095030381049842c1000f420310340c42000c40c000522254161141c0e20150585030802d040c0040301084c04015 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 201843561 1250 201842311 201842323
    0xa090807030c17121c0506030d0e0409060e0f07030308070512071b021206190501030506152205010609050d0c0510020102090301110912160e06040b030f0c090702 71
    0x500400e082c058180901d8191038030010344844410111400080311a5002e600c41c1c01008040071480f6802c01c031099205281c2c0112500070600710081d01804884110103070582401d80d44041c050364580c2c03040002e0201341e07408002c0b050140c100f51120040c0704c0c25401e80702c802501040380401c510b50003145035184074070300392031000034a01d54091894882d2242a180c1010440c050041e4814110002006868909005044625403402040d081c00c1c091260606c0100302007075542c9083c40d200040021540018500e608050310400c2d04241c1183d4a0120340d1040b004421590050911110440c003180e290380028100c400661310710800301d4507a0f0411040186960029020a208a2042c4802c0c905180652003a12040c000107150219800200382540d5103041c0e280480314010520b040e10b400c02c05051440c144404c4082e144854036118580080407090081140ca0480782000400d19266a84107003420540181194134a1102850f05550b0700c441041c1c2601444892020452003400020701c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 201844811 1250 201843561 201843563
    0x604061508161d042a05100f0e040b030304050402090d080c070602071203021506030c0d15060501050406050301150314040501020a2703020f0a0e0112030f020a080909040c08030f0a09080703 83
    0x80f01c18440105c501900300e903151640c4038003074950280c400044d680d50b48403103208504540c0c1c0314000200a0001d010b08581d000b5000c013030096040039961135090740c001c0308030707010b1310f80c2200e00513152141035020a1030722500600047c94031800082140c2c3c2c01030006402c0381100c066608860744183c4402c000c0c04006050080240580c2c0165507140003001028842540410098211901d80905200054a22214260544120440d800e10045400d458013944000e44000c4c20300d64982442c0060085c401d10051280f03850220340140b503074940704d2003500103100781411600303003001500f0075040c1a4001d60251540346d01080d01c0789404140c84000b0a1a01c6403001540031000900f4556000e115054403070281d02c0e948004210408036001d0101c901b0180a4400070765032810403800d514001c0c06000d140c035409000c0d9405a90351900242d100f0048804540003641c5048170741d169450441c280200e103402c441782d103000108441b0b122403103201c05802c030610f150740c88010750307035490489549440007808 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 201846061 1250 201844811 201844823
    0x906050d05040201270602070e0c070b07030b152d0a030207150c0206073009030309351206010c020109030606060504030201031d0604061508161d04 65
    0x880c012100300340d10081c0d200c2c0c010b040800d412451a283c0311081400640540820301c810b403418000c003941040810301900c018a0310590500304124541128041e814004182001380030001d01d83e140b081d00000980b2001524020b0785900041001c04a80c000c1c1038a5400040c0340e800100138450b0061200100d80103552900707152000510040f001781d804807905135410244420710031501c0a5901c160420207200e0344c06402c0034140808001d0001c216150041058440b040d036414032600c0c0b16404040c208414180001d540b5820f280c20782c06050017210103086610b10380e04a550b0469518401c1e0007100c0002820505103144802c40c0086002d01c8070816600c814400026219500904002802c01d0050620100c0700759290b45a9043d1400c9810041c009000824200f0441d601350254815100c100200d681d07058119500d413503a104001403020301055100e0444e5060345001c2882400600070740c0c130546420865920040003544090f02c2000110403800c6039100741c0b105204416405654801c2c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 201847311 1250 201846061 201846067
    0x91101021b060a0306031e0212030c0d0f09051002060910090302060a0903181503150303020d0c0309150903050f01020a090311041404050606131e0e010b090106020709050601090605 79
    0x140c01d0001d035800446640d030906031745610200200325400b242c14028084030f114480420101d01c18404414003180c13150b0031540c020310075044010000b00e20780106104601d0a8003c44852030402c0754040f0043d400a600070040800c101c10f0140e01042d41c80c4500042c00441d0a046440c2170303404100e9001c0800a00141c0264001c1000118181c20080911340680380810342c800264002440c030355007a511545034030040990790310680382c060160100d4503801d07201c10b00000385142c4020351184210a440010414201c070401c0400d4052130b2020003a2050044a0046240340300b006880d140d0540401c6d00c9900c200301900025280c14021203050b00c42680d20b040b4094a0759644c11030180098281c0c5504c00d4039180a15400c2c40b0300b244a510030f40c0038600404607801c041050018081e40c01e6614a9102c0c101042080041c40300e8810300503103145c0c45e070002982c040f4164504d00401d400803660b03a015940100006910354002540d9040c0c0c0c1c0b107101e0410040d21403600640d4895154403502010030000c3c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 201848561 1250 201847311 201847363
    0x207060605090c0f13090e07090f090c051c151d0a0c06050c010207051002030f1b03071b050609070f060807080406110904050403030f0f020304020d022407030309110102 74
    0x50001e03148045d02d03039503400c1c049034440c00414169007142841796080e5003c090100700c0b240c400d0040300040c0000040401c0001403545504030b41c1d49103030041d14010722080111141d05c0708650540e0310810b4000c060100541c02c4000380310040d00745480080c1c483c401c1d5000710a80550080341b0207035190b611040d10480c8034034081d4169495000841c10764078955083c0302d40b2011440a0144120800000b1401680c030700d0b11801031808840007511402d4a2000e081c1c4001646065008407904081e080c00c2031a00c40002540350000801e0000d0300512502800041c00f81003c1c2c0000e029055030740c071003032014445807607000445428108445007000a00d0040c00300b4080b443e2a40030260b070941c0f009025240840700740103c0c0540c0c4d002c0e101100025600d01012424081d51b10400c03418150b484030030741c0342d401c040d0000b036001d0090031401f0784034840410280107045606082191a500344400b21600e440b110300f006401011482001d49070794440709481c0741950f1003c58000c10f521a101410700c4140380d4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 201849811 1250 201848561 201848587
    0x1b03060a0303180b0c0c01031127150403050606010e0603130807060e010c090501090b04050f0f0609030d1d09090607140d020d0207140601050109090905010216060207060605090c 78
    0x8400000783c0a924a07060110745801d40100400988035000e0013080c020179154001000c035100c12500c60b002003014001d0355042c03038051150141440c0c800305a000d003a600b040014014002c002480701e200039001400208208000c600144941d034243c9801280c0d0700440d0900401384022030700054007030300080c2c2c1d010000da22000541542802180002070b941d10024a10382100c01c54001100482c0158500300320a6030701c042440082c0840b42d0a40b42854640008642c000350344810441c070070304510046424548131201541c0240100a00702c40e03003018580f101600c0c0c15080000040a01000d400700c0c03500703041803120350b40120f485400408aa6441600440d110848940070081090081240d45080042e6002403d950f02c1c0014006907034109626007208141000b082e9a01603421640040280e6078001642d0360890303251140118811845141546c02427144682d0401d0000034052a00281f00c100d60140c48014400d48007001503d44410030012101c1d0101c1c2c48860102041058110f0500 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 201851061 1250 201849811 201849827
    0x9050310141518090109020a06020a05070504061a03060402090607081c0203010e1602070f080c030f010605031e070504050a060e0901050606090f0d020a08031905070c0504180b0c031b03060a0303 85
    0x1340140c00083d10415a600048809001d540030a0050344680c04480c24043d040c05140c000b000c04481c00c0006a16003d0300403103c41001486146041011000600d07580343c0d50100e805a00b0f0040c50141c1d0740d940303071900b1001600031440820302e03220f0800641620745144e10843e8181d6050a0f03c47c07005946d0329102c400d41000d42007040013140907050001810400080344000070f4040307840503101d02c081d000e05241c94078014645080c504c2e0305040c010040c545011a98440c2a03a1042c4509a0321607101596032504441e40d100c140c0081c605000c02803010150340c065400e032402c2401485032903d0b01440142030715420364040d40d100104104034002e80c81c103880029023506000d454043e0101d21500000d07207002059004c1007050b0000030360000d102250071768000240d5540c0c00d00b20304080454075044400d8a0078001d00740a280d45082400c65442e50300368102c1401da00c07030700301b0400307140ca0020030609410a80700701401c00d21140c030501e1990310303500c00e5a11502018003003811061a50301e085403004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 201852311 1250 201851061 201851071
    0x609040209040e07230105041a07080c100903170402010f0e030111030103110108070c03050a080a06080d090501020f07030308130305070803040602180105090d1209050310141518 78
    0x155a150001c503107032402c0c0070400003804910b1110035160441c0d4114000040c842038140d04000e400c010034408035a00071050211417030b03410882d80d110300f03062510006520a060171100c080c800d4046d4611041c0d6580c00c0363b6031252013540c9000355941e481344c02150040003610300a0101c1d4503050000e1000d8441d600340c0031503500040002c9420a452402d80a2551080c0c0083c0c680d5004102d6403a11940c009076140d400108501d49034005001d0703610014058040c0411035010400d812001c0740448580f43c0207400274040942c16243c1503014020044c10004140c8120307030250080004141d20740c0000318040701140d0701602c81c9000d175554428840e60342c01103c242101403290070f1110002090450000d144220b2080c580140e403180c8460801880e03070050740d5107134100541040345100584a0f03803141c0643c0c9a22409072070302000b035400e081c4c809031419080741d43c05215206179a160741e0844d4000c103294035042d10840480d52203801040048403200c00c141c40d0880c80740c80d10241c0380c9007505295a441 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 201853561 1250 201852311 201852319
    0xc01080406241d010305150702030403200315010f0603020705012d0f0c120506030f120a0305010f030f08070c18050106021b030606041e091209090b0609040209 70
    0x222440003418411120510000000d40408082c140240a01d00c907040408aa8000000f00c46600d035a9560f40e4401c14000c010b0702078040c20740802e60288c001c00988024550120000c01070b00110104d8078076100c004c0380194801d2149a004401c100710348405541641c0c0c02c00c07000d400d0306003006020380195201900c1107030720359600c2c211445504440b4007070340c803800c2036079121b0701035101d40003107002c16220980d1824007001e00d08424109090f4005140300042d00102c240425244c1d23464000038104602c0101a1f0028040d10346080c4200c4450001000072140f6902c0400450746c0300c2c1e14000c609121400b009001034608111203011401020107001150b204001d0460000e8030303802d0b102c07410645070051051164503900140308494040c4802c10141003c5100046900c45100c001b941d02c5070040e001a005658036910500e0703141451030340500d40c14144c0414400d41d41c00d0f01e041c070201c20344a00c4002c0020083d210101e40c80246004040140e200149018200040d181c1048020742c084c0021582c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 201854811 1250 201853561 201853571
    0x9060d053301060f12150324062709020607020402031b1603030f0212010902031b030c031005100c03050d020c010e161a04030f020d050f1c030c020c01080406 69
    0x605030007008103000c3c1000da614400560302400018000c031500000b551280741c02e00215000b9242e00c0e8406070100c1c0c2d00819001d00c0c5103140a5001c580e1084901038000c81703410510041101d03443c54002401c1d480c41c003543c404080800c082c1e6002118805240254490b02c104502800b5181ca40c01940c0c014004200710035500745640350308121903003d16101e010181c0081000000c1c16014031030682c0c0c0021222055150503502e03814170101c40c40501a90881d0380e40880491446070003039000c580d0030b0190108840d5242009121111903410807222840700107000100883d1604007180c2c40d42704880b40fa2900032802206640558450300300b9603d8040442d8244400d8801c64801d00a00d044c0c04511000342030b49048642e41d0510361009504041121085a0504100c480034107007210201e903040100a500e0171a54800201c3c940780b1308002800d0340c4074000c0303464001940440d40040c0c1122000f44648000c606080c298160b0701d1004108000d83c00464142805500660743c607540944101c00000e6 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 201856061 1250 201854811 201854893
    0xa0b0301151706010902280e04110318010e0d0305222001080c04030308040f0807080a08070e2b0b091e0109080a140706060b0909060d05 60
    0x4007000855000404039180502160b809103000c0c0b00040c0540000c2009600d071001c9038004181c0c148440401408540d03007440c61b044002d129201d02d42400000a005001201d802c4030402c40c5500140c800104400b0b01c000c0f4038490350414800c807441c4008070b00280610780305074a01a8000c1400824012010804203103050f482c3e0b4200c07904c5c10859104012072601d141c8820855030030194159101c60600c00d99400340b02240403068144c0702140d9161804101d45e685516003042d00390307000307a8018000b04004c03464404101880d0060141c1032500d80d242c040c15900c1c0d45045410140f100851508107005030301075041c10806054a00340074801300318107804a16030342d1750b107102407004a5a042007500000c1950819140b00c840180c80d503e4a20000c2c08050429100c8110902c40d000d044001d02c58016038016071395044e0019a0081c3d03402c030a080000c1e550b00d290b03801d150317880380704040d200d42064400a40d05207001461441c2d1960850300400601070343d00b034a0341c0b6520307040d10382249250340142055 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 201857311 1250 201856061 201856091
    0x60c1605011b030e0d1b06060b0310050312090a120203030912011508060c04062a06090312050f0402040f022503110d0203090f0406050303030f010f0510080a0b0301 72
    0x260b44520b00c2180b041079a1500d500041c00c9420709010b10081d900071883c4010300540c040440e01c00d40042220030b024010440c90030380001d00c2a03a200800d00c42000c410410b558658290300411240280c051303941c04992142c0c3e6550900c1142102580840000303010301461800000c03003500f5602c0901141e180070241400036070003040200303172683e90b030b9151340060500b0807080350703503200610389a00140524180a00242000d005500880701003000b40d920400a030340940f4001c1000107030040c140c258101c3c031402d01c10040c280041d0160013083c40e02d180f03001c0211042c8901881505110185052031715250708200c05411803510b00e00d580e81d001e0200360a00c2140c841e18040701c00d00082e0280d13400e030f80783c030f0050101c0e289906080881e4211032031801d100703078011007201e000040840e440581000d040b00010700070f00d6160442d030b030140f0001c02005112000c64841905840070000403109003070ba954200690782c54120040c1002400f84030101c0c85200b6607400212035000020001310f40c05401800171 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 201858561 1250 201857311 201857321
    0x5040e040609060f1e0f0b060705060906070c050309011805060d0e010e0c0a0905040201090e07120609060609060503040c0302190e0a06060e01052101150e0d020102060c160501 77
    0x15501c01c0e9850020500700003051094049a16540030103101541c00c1c4d42050700d00c2c600516100c400706894407155905880c07150b01001010000400c01134507119141000c50b965007049800d100c0d58418400031444003401030000c1103140358864001c40c6803420280c011030700e00c006070091400100d420700303000c01c056031a08064034010031400300000d0720041ca03407021390035a03011850420304c40c0c001d40c20314502600c80744408400d40ea01d403000495503464a2004903912040d40d8080100740c0d03901340900208a501040f49018003109020512065498500c0c1204544041c45014003007850000100001d40c014005550702c40c0c01952101d0303580c4d98a401080300e100c0d501c8000c0544012543d010312450b1901740d03610f5000303550340004014680c20100042c04580380815118140100400c581e4030074132580e0f104070101141c1544207802540e542d428040c0c400c09001e01100418888000c02c1100e04059030000c0700650141d0042440c1d8440300a04a12544003580104610040f10004000f0400c24010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 201859811 1250 201858561 201858563
    0x6100c06060503011a01080f010311091b03040c0302030c0a0513111b01060513021201090216050a05010e0c040207050d0806061909090608010b09160207030b041202060718120305040e04 81
    0x58903c0c03680f07170580010204074000b010010380c280c05070010300201d071003ca42c2075031030355055032070302c002d5210220101a8031014600d0b22442101c004100802c02801c20320410880c0e1096003102c10082d026020020b00d900c45019042e003104080c100d24500201c950091010020030b450482d04d041d807201c1c0e001013400d45011140c007040e074580e8010441070404881b401c0080c0c04551085003000020001c0f40b2483c034041c0300d400701c2190042103514221a00c03070b01f20711800740c0c00301c21690001c00514010703001c1e180303480d0512101d000703e0400350482c4c01c09000f200d0700c0350350002c040c12003a248403200f07440c11640a0059904001c080c458007d1545c01070382010450180c549a11205c3c6281085c20f8080c0c50b91030300a0521a410b1100148464440c00f0100760482a4441000d0030450646000c071710b015510f43c0082c090400c401e041c801400303544100d40f124014603034241c0e55159103000c3d0036150002030311440c2c81017040d102c40c100659031919443c001c03000d00c240b600a203050790350600d542c0f1040b001c5d18 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 201861061 1250 201859811 201859841
    0x3090209010b040e0133120f0606030509010c05030115020f0a080d0b04020f0a0e040e0102070f0b09030a021903210b030d022d0c031c02100506100c0606050301 70
    0xa0180314100b104c1c0341041c01042c07601c1c160413200c0d0b11100c089001186c44241e030106e40f44007810b07499400740200702070841c0507c107040c10040c01d521150760901400d80c510801c40802e00e4000415038030300042c064070349198202d840c4e2900c1c50346410718440024902c01d404070f085001b13036105002880d00c01d0010180107401400280d4581000c05a101c00b00d038854140c0610079403042100748481c80c00b40c0d058030640101c90a2030103031140009c2c040b60140210b42080040355100155280401441452200c0c02c94055100c0108640e03804400c680e4a100c3c400128016074045444030f0101301c4001c1034100c0641c446c2c0f1340741a807040159654410000d0b00c01034044955243c6141c050603040c05c11805c443ca103030038402070180241d100e10719030703c11442c52400b020341c1a06426140c40500100941c69000101404495a660219421401d0781249200369001402404440f0310b5081c41030041602425009151089010241b0320645050341c3c1f0320800c583d03d98540d000002d160350284180610900404 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 201862311 1250 201861061 201861067
    0x91f050f0d0b16020607090513180507080307050124032301020406030b0111070f0513090f1a0c030402030c0418060e0d02010e030f0301090c0c0512120106020d0c02060a03090209010b 80
    0x3070f0003c0c1c01c2c818000d003503004001d0521420890380d034030a000c03070310708036622140040c80904c02400e9141c84020064054454420718000061021f40000240300c000e0244000304444008a01d254004512164107203030f008491035070034804508889968200c60a00b010b50340d50b8542c10219007400d907003140c2c0c40117000c65038448a801507560407a0000b1a038a144001501d00d4508049a40c0b101004a008a50003000303d11100c811120255105004841d041510a409d000c542e2903c0070030361400140c0003000c0645440030072603400c0700d002541d004a0380180504107004040c2c1c05e1100a1405100030382d51355280141c604042032462040140280004002e85090a080800a801e5614801000d80310764010408400c6c618040402d80c1d042d18010240840c0b08100d030b22040300c1041c070030440030f0414000d0601582118203420014900411b551113603040d20780c0d82c1d00381a43c135146200f10000201e1048001e160040c60b03d08000c0c42f114400d0300740002d28082980100f10028001d81200141034000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 201863561 1250 201862311 201862351
    0xc0304030b1e0f090a12020c09090733081b030411030c0604050f0f04020c15070e041811060d090f1407031713090218091f050f0d0b 58
    0x49600e1a80c0322980da0a010b00c0ea06002d0119940c81700081c0014050340a8012541d400303030320034010405801c4000340401c001d41040030590780c0700d0754036106810501810f0501c0c24402c442d07001c40291540694070700680e00703044100c400d80e03450000815000180d11551421152041400e000e0350141e405603498400d414018418180307403501c0d20020901c25502400b007041030795034103c1201c182c0d16054845085c0f030500c2c0f00104020b4051030106030114020464210041c441400c182c0d84680e485a68030b4030404524400e200445e000d00054002c1c4103004001d000c0818250307400598100009482c15182c050010f031800c040328210082203030b507110705d0b26401062000c0048801900111100a0401c082c81d60f520b0040c22074014100001003e8046450101010324581c070310020100d240c1c0540d55101600d012101c404000c0c2c010318440c034003e0006c50600224a000842c2d0102c1c1c92110300315160a11040180da00d40520b80d2030780c000c0c8840c5415001510180c0c110303008180d5031070640c24101701 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 201864811 1250 201863561 201863611
    0x9090c0c02210610230301020f12152b031701060512090c061204030e1c0b15031009050c15070c141c06090c03030801080d02030c120c0304030b 63
    0xc0130b4000c40e6005a007860500031018680f0034003e0108010010751156001400800d002e80503581c0d41084444003c605640c544904a41c524400e131034000618000399440b008010b200b00c0700352201d0041102140b0054109030000749014241802401c0501016a11921401c80c00e103098101200103200450307002c0010890380304481d004039240c0050440030001e01e0204440303000311a00742c0c3c4105e0b40403000c903007414007031007400d0110070b00541031440c032201d00c480d5051110014101111344103a8a4000380712034071410802441014014082e00c0080c5c01410b1031030113011070010540310381c003403000154415618400d108403410040c26049841d0081c0d8142000c171001e05500c0408184032040302c0c62030076520082541c8114180400c1311041e01001d080610041100707410003807610104800110505811058032412905d20104482031140c14400880e01c90103003010310340b52a40501c51541ca40508040504060807010044ce81030558a07158040c5581c1d0507980403484204034410035840c004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 201866061 1250 201864811 201864823
    0x909010204320405100308030a1b0e030a031101060b0d050108010606050f04060c08040306020a020609060a091e05120f0c1209010c020d030504080a0c210309090c0c0221 74
    0x910482c2002039145610045031001d410200c1244034641d2040040e01ea40c40c2485081c01071600b05da00e65469140c90031141d00144103c0d1085809042d8130301031544028840e2020840b183e1014001c0c6c000c04446903015180650030200b8041255200d1001064071407841007d80070210203010049501e5142c000c1543c21215290062002c00c10104081c00005c05d40070103d8049600e9840d001804600303070b01f85510680240d80000780b10310b000041500d41154009003d5001e04a03c0e801d440c0a034850000f8001120344001c001407201442034468012240c00580d1910b61600a00c180c403a1007605c82d034030302c05960010069205c0c001700800d40011150041154007514141020202d00e006002c1002a00702c1c4d00f6504000d1107454210480010544520180c0d0300900b4403008491580e0545c0c540003807812058010300c2c81400c0340e01c00a040c0b1017521035076000b0041d003540f60203000500304020900074000501c101030900861812a90058407000003101d4051041c411940559108116160a185c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 201867311 1250 201866061 201866099
    0xf121f02070503040b070f0c0603050604050603030309150a020d0617060108070e0a090302160909020405060a03080304080d09020607060f0b04110415020709050f010501020607110604200909010204 86
    0xe20500c05500003590000c111030035112640c4905444542c5450520490758842000801c400044540001c2094150b0803043c01f5000450f070600c419952181410360700c6c00708880c0c0ca8099402031515106031500402c503d070300b1800d40c20000d86031501040f80070b0203990040c0d10025071a0b405107a203a540200078004580901a843d0103040400c2c60300b40c10150383c0c240074100a801e16510710b91001014001c10818014654819401c000315039030748103000c001c01c0c584500303a005a00f4070002545034540b000784041601e502250050854890381c958600503005111020801580c40b0840303400b603504c1c4c002800e80144500000f04908801c421050300b5034000061050080741084005c4e04222540c40a0381c06580c0d4078401c0030204140348801701c1c68030200b0f92294452910b01814411420100070409050365000e80864050b03454050045a0070200000400302a8001401103000038282500c9010b800303d00c6000c100003c558000083d605a005540400c6141e500090800000381c10b04290300043e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 201868561 1250 201867311 201867373
    0x3250305070e090a0f0e030405120307020915220f0e0c01230909090d09061d0d080d0e0601050a05010c0c210507030312050c030108030d05060f12 64
    0x6080100d00034250154070b00744184a203260038001126280d540c0c0c00800c0340e11307101c2418000c039595881615100d62080c06007900841850401c4491041c000046030b0840d540030300880e0031641d41e921040e086000d02c003180d5600035140c550300322040701d603010442c07064098864002001c0800d500b40780102c4040f0070651f005604681c584201d80c0c0e8101030708407082c041c540480c400400c0708142d2600c0ea8841d070400c85900c1036203d418000380c00000076540a000400e915074000f00360300c580b030548641e07003003070b0380c0c0540c0d40e1960604080714109100400a840e201f11241070419840c0f550310004c3d50100070080400b940018010000c0389480c4072901c000f4042800c100d5201e5551391144071026410f4028101d460103034800141a555085107941c498079017001c2512002510380c0b40040ca44500a040484504d00705808039000da484203040f40d040b0744925004503d04803014202201500d001456940d00108010b8001000e80703074440e82c0804c1c03040c070101422803408000d840d9000210042c45030704030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 201869811 1250 201868561 201868571
    0x30f0309051e09070c020a050d0308060a0b0f04031104060b030c0310050a14040b030f07080f06220609050a1b060201050c07020108012102060406050c0f0c06270303032503 75
    0x26034403080f40e00c03a007000d00d0346000c050409160000c6103c3c13407010f61245030040c0020300c5c14402d040c2d02407401405424101c03101005543d8807006111140030780c000450045401300000c00001f962407903612800074015001103038440d40c40651210366001204c180c01c00900010820030301d5441500c00a000d0b220031181c040c0d445041038100c00680b0915120a406a81c1d00c04401069a13810803008200013030040840704942d40303074481152074854145405100c0e101c2c480100c0c0f1145148154901c000c01103c0d02c190f000c0a558a4071000f4041c044070035940d40c0501c0c0300c0800806c80303480d00d00900764076100504a02d9132514100908492005203241e82d241e109110000043c0e070f10044048c111070300c50721601c443c07100b0418070000310b01e01d043c4000d5111800180000c0d605810201802184001c14141c40c0107189221815032541c0c1302103101680200204072514244502054030203d50030f0b4082c8944020000320b0101c0d1840d40191080303d00c240400f6040d030b4104a101268140041c1d6a02e07062003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 201871061 1250 201869811 201869869
    0x140c1605030d090302012f16020907030903020d020a110d0312060306020429041403070801020c010911010503090d08070c020301090506010806061c0609020f100924050904020304020a030f030905 85
    0x1f950906295400105140025207201c1c0303100321100d2183c80c1500104022014100700b0b1000d00188800c0d0780850250140790590364040e400801d08054442d0007189480d4900203100030481482d0b4030040071424482d00d4801131000f05024440d0802440c858100145e4544c285400d44907507001440444410030307400c2e0000400300043c0300560b01114283d0290062100344100003030305140300e580048003258400316000740c081381c05410500495011729890640503502400464079880101c03a40c4030540e03c208803100c62588502c0487d0b07440455454200d00380001c6600090946404240c20f03035950313100c003005201c141c90501c126500050112458040180044030100e030042070000d0181c013565845100206648540d2881402c04e02c0040040c6445c5103900d5000e80000594041e00d4507400c0304d194800199121427828a5444019455160804100038204806548000c7c8102d070040c8145034004001900e00e512007a2161203a220700c40460706201c140101030402c1d03803018200d40003012a82c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 201872311 1250 201871061 201871121
    0x300405030a08090a050603040c090609020c0c190f0815090304030f0803150603040818031609090507090518100903050304030e0f0909010902011101140c1605030d09030201 75
    0x41010781e07120b0280c9880b02e450000085020034107a000d5034118000108100800403504404c2d41030b00c400c0c0d00208003907030712000154220700070b808010960764003521081140b4900142181c001000c0317008848001c0da00c480902e054203c4540c00f5030650350040c201440310100d80c280d9160320403100001981404d10f580c41d800110b02c0d60342d074003400111340000820540140f41c41b48065105c00903141035580c1c01c1a14000d03016601c0348059420140b06070392a40b003030380340c00715000c40d000038550398100e24103023098801401040380d403000301c076903208403100007900700510b002d5648240302d1485030312003024181349500c1c14004001c2000394200c2c50300443d9400281c203c03007038941080e0145440b41040e071040011860051880301380c685d200440c01c041044481054000d2842c0718400c4e40c038204607119403140a0300780d139111041c1d0956400c003000081c810140103805480030f044403029200034016162546d0b811584152424000f41d41c482032198141078090142c803050100120280302900c00c01641d038 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 201873561 1250 201872311 201872323
    0x703030b0d0c0b0304140d120509060103080f0c01020d0e06090d02030702030d05160c0f05010e0415121e0b0f060603070e040f020c030d0609110a090e0406060830040503 74
    0xe0f41050380c0400440c0500404100451a0078040300456140000303001d4080c0841008002c0003e20030f0801000810350300c00411014100c85c4d200c1e00103030422042d4403120340c1a412151540c1c40541d03007400b601ca0444020302403841d40c100c009000d8a0300d41003110180c0e0a1403541c00030392040d035104020b6103006880002e070202c841103440c0b801c251a41050109004200c0b58140040c04006141d0f602080104101b010042191000d80340c610b2840300d032406100942d04040311100704a81c0300354040003000c0d9407200e10823159105804031603031209030044111400d8100744060350250803400400020400d540c01c6280c22200444080d400c43ca008a0001d00300003c480d42540030325196050340e01045825010303510100c2c01c0500740ca483d08005200403004000c244201c001c2a41403500040c100501d810403a040026140d03a10210103060442203604c180b0041c1c0700b00c503c59912000090041c3c002d000e941c03825005410403107440702480c01d86811500c0e518224403d100700810007000155800210b03 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 201874811 1250 201873561 201873569
    0x90b0a0305060103091209140102010e150a240806010909150c050f04030b0f0a150e040812090109230727110309120906040909050703080c030703030b0d0c 68
    0x45102d03503540004801500301000d004102c0c0807039240c0c000c41580c109581e44c00381e0300b40c80c00c10440c0034802d0004909a42510307160070b10030341000a002c0058850b01c6a05940600b13445408107038501c03100e0425120100c1c01580e0404851044001d008180d014002d41d070061509003030511000000d6101c01e108001c0b02c42c1c045824a07506d490884000e8040c5d001e413540d10061144143e1541d55900384032900c00c10481d40485400e11800025015210a00c200c1e6900e02d01100c030300f031109090444260180c43d02030010346440205101c8101018681c6d1316440c403c015000000c07c0c11511450402112180e1380c01e1b61040c2c40104000a074550b070009140c0044406006952030b1b000000c0d1400c030105600014841c42c01070400000030103001540000b580188030302c1045901c0b80511282803401801490300da82e47c051810003003000006010f400801c00315010720261a001c5950baa2038808540c46040d0052054202252a10602d6014428044030407800d842400c08000c859554101015013401 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 201876061 1250 201874811 201874817
    0x81c0311040b0c010605090a09050c06030403170c0904060b180103090510020f09040518070909030e0d020f09010e0703060e060a030f0302031902030403141c1d03060f010302040507090b0a 82
    0x40c4000b403ea409400440050078050441011801d0400c002006002006000c1c2c5187c0300f000e04a800504081d0201c0b0b1089416542d80240c00e1441c041d05615820302400039000403500b84028220b90303031140300d00c00c024103070114001d80e18800712907131620800c03800054034145441c02d0072640100310081695803080e2102c1d1801640c031300c0c0340481418140104070742550007601e80b500300441e8101c070003026501503c0040032200b010366104038a400f0355104813402030003da03441070020080d040810020385150300c01010b402d1010568400310f0340400090780000c22465a2100784605542c1602c908400740c6a0b2110010081c40c041c07010540d80b078054440203050802a2000e981414400e10aa4410b20301c403a0800c1d040b11020319009503a03070424041034446142c26280304240c0500051104030107050112408607148142800359041090160031212804080201c0240c0c6e42d41030106503c612425003c9a1a950640c011b00c4201c680051580003840007100061100b20840b4090302e410400e240303 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 201877311 1250 201876061 201876067
    0xa0b030709090f15050910063501090b030a1e020a0f09050402150405030a0210091502340306050c1306050c15060a0501050c07080601081c0311040b 65
    0x3110703145040d038810b8041c0c03454100082d40500850300f08252040c1070075407443c8010340391010041552425584c0400111072504100075442c0120060f0b0070720b407030344d03100b0510f00404061400f480c001501c480141d095445001072001905601c109403081006800503c07503510283e482001c00048600c001d410f1000d8440c800302107603110030413400a4492180c5440c041c41d44c80301c00c1400740c802600c040b44102c441079004c5540d40110020354049030300050040a003004503400388400c62403c415424104552641d011866584440c0800184078041d4000c20321040c03404aa01064440c1041001001c04e80d0020801403104103e544419a83c0041d00050345444940c00546148a1201140c05d505c2002c0c000207170752600305c070180403100c0c114420340307517480d4081c0452411010304940c01903224122030402c0c0010b5110300c020300030356002d40003250b440584504c0d40d03e1030003600342e126444076402a81d96905607600c0486002215000341000e108081c50310240240e14001c0b07024a40c0c00c0320001c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 201878561 1250 201877311 201877321
    0x31403100e0a0207140f100b130c030b0301020a09140303030c0301150309020a18053303010b0a0b0306030d090f0501031e140610080105032817030f090307020a0b03 72
    0x15412283c6540d8021401003003030004810070390f1180100c604401d8a801000000b8132041c0c0f060081000c080230081c41c81c2552440a1010750082c44681c4409040665a888218454409200800003a4441c3d00d88005080c644030301d0300f00414181707400e035001b80c00600c248401046580305890640d0800c1d20101024400403e040340204480c0c030005c3d5015003880000240c9281081c540c1c0911003444106003d1a03840c1a285861421286500354204400145562489241c80030280100d40010300110b1066008400201c420b00c258100035408a000803d01860b841e0821a0391140880380c101103103590f191000d54803201d861071043e00d061584070070380b22100052180031940e050000c080c0802c0002c500694060106c081290b403180503e8601c0c1c5080800c0d0b002d00c1440e4100d400040040408282000a2003440728039040c1083c1d40d010007200040c00554454511074428001003403480e168680744c40070310b10503480034001c050290010803580300275842d140b0b0b00c40141c2d103004003025a252a2 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 201879811 1250 201878561 201878581
    0xe090109090f06060906051521060d080304210801060206040b0a020c0115090e070308040911120103080706060f150f090f230307060503040609030c080c0a031403100e 73
    0xc100c40201010b1610b000402c03405d44661095041d940c0503070740c449001c5500200e4141d05d00c2040070240412001e04400c02010300071500c929070221000d88410f4140300290344a584540080d20100d40581c050112100c0030701e4160302d148402030346480e080440d945410b03c081d4a41e0340141c80540440740040004d450000306404403100410213800801100718840001d000a0055018940c002c41c101a20080303801e40c000f41d58020740790840101c61401e841c261080c1c1c01803102e2540c90882c5441800030000e6180401d29480c0207601540c000d40d40c0d100ca41c40c000f012185240c00550500070080d0040c80102c0d00b10b542e4240f003002c4c4d420413161000c0640703803d95003880d01d1b6000c020141c00402011540600b00c007880b54440e041c0c0ca92032200241001d041585500d040c5c09031100050303040c00006e01088064001a01d124041e0030f00900352441c03038440442d1a40124400314083e4000603a1404040c3d10520101c1c0700155005805d0440c1031080c00c20071390b99018425420344244190202e100512 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 201881061 1250 201879811 201879833
    0x30f07170f1321020601050306070f08040510020c0303010e131104090201021e07030b0906280b0402030c0316030e03030606130e010f0f1e0501110307150b0a05010e09010909 76
    0x1402c449002d43e01c0388500300000c0c01490120903200140943d500001e0340b400e0008030180039031020f440340400c000f4410030171503002078014010380e4140300d088190104001c241c40286400e0ba1031802642e07803581800014440c1520280c0701c644640f0070031401c000440c03045c0c0041c1817010300440e000300350241c81d400102e1510004508550880c240104000006000020f44900710b80c440c08800b602c994842d201c060f119541291408001c503030203a040d85400604030003005480059030b80004000a900c00404c1c1203800c00c841d0b0601489000044c40003000c400c02c41e24000900c0f40c9003d1080101488003240c80b030002034001400b40c84049650301240c4207070314032800a0f010002c0c101c001580c3d01c60844d24010110f10540c003103c10341c02004998032504101031801002100f0410b000c50b490a00115402701c602c181d012039600080c0044000148060041003051620a002180c040742607001c11185220644c0300506000e81e240d52010661600a40c01e41100c0f000400090320029904204c0c1c0c00340 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 201882311 1250 201881061 201881063
    0x703021302120106030501180203040c140d050319030614210a0b091b010f0206040f060608060a090203010605010513030b180a030c060c050304051b0411070503030f07170f13 76
    0x503540380004031341070f0792642c0801d0403211804000106c02a900b41d03680c04910080c1c5001e80801c091610074041010801c0d001c000b8090041c043c07269070640d0381c40d19411074000c03031a00694072003142c000300e190550500680e405489800b0780705201945000000c0c040031209180003c42801c020004d00515030b0034815410b035541c06c015820514600b52108071b46494210b1050003540c90300c005a0141d552040306807103911b40c0e040e00109955142c2e61150410a00c003100d0448505403901d0010803118828070500380500c000389008264604a031042600f901c080343c112904001c0180310ba070852007105002101181d030070032002c0384e01d9100c0e880340d40f03000008802001d14520484c84820101980b03c440319107201e008040070400f05803032100458540c0320580c1d0161855110182400b20391b0030a00a041c001a4000d00001d030b03403480000030086036000f00005482640001c02042900100b807011540c0c03003d224a031401d825100252801e0308064040c00c2c0e20066035075a0005a40c08000c83c0c010f0120b6 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 201883561 1250 201882311 201882337
    0x4050c0d060f06120302060f04081b03030a0c020c01020d180506070b041e08030f0a060312200c010516060f02070b062e0e01020307020411030f1005030703021302 71
    0x245a0608090340030700b80804120501034544200003c4412003020440301c801d5265000d414151a549280003d0520140094400180030040e11070500540c4d40920b842000d98030295440e0310b09101c0c0c1c1422070b0074504010007550081c607901d034004e0781d010034861038100341410103500010307940d0a40240034042d9048160003101c0014020705002580000300c1c850f40c40740002c00c0040442e04d6907511502d00c1b042c001003010400f4404190b80c8110200900e80c081200a00003600c15540e4580c5036441c615008a44049110b00c0c40c0c1101e4400a6400140d404a207400103150003403224000030480e01c50a9090f180382c9003192030400030050340d40c000c40c903a1520303104255222441c9017084649400c0903102c0601c41c0019003c00070b0300d41d000300780117007090301380540c0d500b080c40d52600127407216808140700b03a04600007003100c5030040c1e032148070308007d629060304029100d00d001c281203403029101a1010303414103103a042c01c201c60f0341d0000e22042034076816141080001a000ba110000e03001e19100c401007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 201884811 1250 201883561 201883579
    0x8071a0f040f080f0a0b15060c01050a0203060a090b0904030807110f01020901030c0f1d010203040302130b01030e0f03030c090409020d0311060a1104151106010909050607032304050c 80
    0xb451a0b024607800a94480c64141d6040c514000d082030707070f110024140205071101600004001006250a184111001070000d13403038220750340710b80c0b4210350f421164480020f602000340710300c50800c0b81c0b859000d05100c03107040000c00c204c040021030002000b40001c0800100c500000c068600c940340001c0c55002c03800843e40380459491240d0b010b900981b0001f4000b91504880a410612550343c002080c0d4468079200700380a210700d0702041c2c1e00c0505150505501c4201300001c0141c481f01004d040304403080d80c0c00982007003070200040c1a244002000e1303003260720481d40800d5120003c022680c00405944107030340e036103030010003103405402069000795110705040c91403018190004941c800c0d04071810b00390b4041c1c0d60b90992003003c440000c48038a242d0001400203008008561101d07601c1815641000e240614505090a160600036000303400000c1c0c41c3d0b100780040010400c21107801180c0350400303205440b01c0070308543c491380d0703884034078503940c0c2e96000403c082c42170030301130b0f29113184000d410006 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 201886061 1250 201884811 201884819
    0x30206190201060f0f09050705030c0a0c1103070b0301031b0b0a08090703080c100f062108040b041d01080316061a060d0b09130b0c03150405010f14090108071a0f04 72
    0x560b0b011718462411400d061a0025226034401c0e001c403445900c904249600b0810f00b014101c40480440340229000c180c0039050a820340e904100484c024445824001e13620b60661a0aa420022031601d00030041d43d00c1ca81441100421000c0d0340f00c0c12441d151041940e43c0e901122890840f0540c03000c1c0c18403030001280d10420f040801e47c0e5030715642156052140c40100800070045458a100d6050640000500c000034440910300f84071104d401a40501d041a480c0c2808801550040c1d03c0707407842208030410001e403010800340c0240100f00c541c020f5400c0503081510801c5600c80d0450091a060b52085446120f1102c00c60b400f0891001414a5880d10810842d400080c12107040261007100000001400030705d48041c01d4690303640c840d0040301d2503111021140420f42018103a20f0011401400a403460340741d51042500805100c0c05009e070302480d00c4c0401407000010005113003c1c0002e04010721090000080b007908840c080174514003292000140d00a01e0301803002198444500060006 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 201887311 1250 201886061 201886079
    0x20f03130311060106020c060a030b030d0c02030706090e0a020903010e010c050c0106082d12070602030438060d060905010603052a131131030206190201060f 69
    0xa00512980710101d01c2c100226080e81d8403102403003a040181c2c412802c5081c51705003070003e0040300410782004034403030001130000717405c00202e05081e01c00a03500c102c01005515080203440300820306030078070170b40c00307400c0c10741100081e08014180b002258001034201d505450940c1316448bc098018000c104080112100420640c007410718072819600780100840c107104042a107010920f030856188200e02484584150703204189035060105004900104814003168802064280d1040000681e2072404d441d1080c80540d02042d00010500d0740001c0ca050044075100840b00d0075840250032095940c0d0000140040d030b860440102050f00340b001c00d6040103015002642034a12038400d4072900e420345030b00300004203104084034180c03407110605801d16080401031140030703255404000c0703051440c0e8030040c07840703070b0000389070100d8000e0349044019403160a800803491043e01005480310245581c00240302402010000f089014a404010810b18001d41c0440b0003403581c4460084c1e820b41d182d82107 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 201888561 1250 201887311 201887341
    0x210403020f30061518070315151404080a02040f0b121011070b0a09020102030403020a060806031218040b061204030519090515030a0f0509030d060b091012020f03 71
    0x8641144182c5000c0b1340381140c9070b20002c00c911009080860b40c6071082c881d5400c5d032040601408281560b03041b460400030210f4645002910524071411070340e058406008140800000851880003002e00090054410116038444240c1d01102c010803181480141c0b40001d107460b09800d0742c01580041809022440811480420050a00f00f0003c00c80d01d441d56000e00c1c030038104000c114511120000b207500d0050340c802507a0790300610440307040980f00c3d4041000e04040d07800c154041020107003080210303e01000f000c00c02da2140d58502e418055814010320b50f1a0900000d50300c101d8440c68191656140c00781600c80d640418541e00c2d40c60700f001e007405021a48807442101a65925058820481c0d000300c007408102c0c2d501604419650400c41011000c40c1c0010706400841c070707102e06508809030f209000d0580146c0c00d407405141da40d030f02c0310510b1040303071203542c0060f0007407005004d9000140c0e1116480724141e021401c141440046041d2040000e1142c1020b100080102100388030036810150341c1c2d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 201889811 1250 201888561 201888649
    0x1110c070302031b010e060a0c0605310305030712270308070e0d12020a060903030515042a090b1306090b030f010605090a0806040506040203210403020f 67
    0x40d540034080201c1c01300001003c4040c02d130b01060062103002c40c141450070081c4000c40e12490a4005455103644544c203403070064400c030321019035000b1540c200003003500e08a01d640c40c1c1e4190078030b08500035030717006065404010060750600c1000c6003442944081a0040300c00054050b0601320142e0445201d00d89a840740d1506800060f00030001481f118020045a82803142c010500194544541e81d003c1c0d40c140b91040314000c5029440c500c07400500d0501428421a10940300403c642c40c0c00c030a8540d1542079140100c0c40307141021b10b80d0342204c1064405100720440c81c420981000c4030410203588101f42d991000f80f161000281e400a940b02c2c0f524a9003c2e90f5107940ca5a9507503942e080c40b0407060009035048441d044000004102403402000100701a03032000d0130484074540d55a01c03442c01c00c0c0c41207800f640c041d00180204001c41c9824011843c03880e113241000680707902d800c030740740307043e406a40002805440d8058200e0744668440a240c0d603554a1144c2d40c210b82044442c1500a110031149 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 201891061 1250 201889811 201889813
    0x509060105060708071e2001261303140d05010f121e060b041505031507090b0901120513030e0f03120f120103030507050c03071505030901110c07030203 67
    0x8000301d46841c0c0361040b103850b81c0e08014903600b441c0060b11400740c890a1324980e0403580d0f9004104400181c21078a00d4a034800303426501fa00d8920401c0000740c0006211100110345203180c08000c1e59030301f928003007941c010081d02c80c0c1e605114418601030740c174943e500704500340d00000492202c0340003450360030a074140c883c0c0769501c607803a40d5156050011400d4880f0700420008442c403c10640c80303010303a00700c032500b401402701090296541c4042403c681040111341c0b10411030a0307041c481c6003010017400b034036000d17420410b243c207140c0030100404075481801040000b14002400c00110303880352440c04520070342218200424109480d64102c1550212412000b00b6000c4503084610300d8610072200d82c00c4006006051045c60f2070244a580d03510152402d20a0101401102d040201c092900c90286100ba00ca240c1d0b184421b00f0010301c0c15050059040c840c1d44442070038001100040c1404010400500f0841c0d22078a503130000ca80980080c84030388c0c128201c08108a18074100004400c001c4074000d43c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 201892311 1250 201891061 201891073
    0x3020f030304020a03081e0d02090f0607020a2d090b09060d0b070c02011e020106030b09010519050406020d0c0906090602070f2606040807060b0303090906010305090c0a0305010509 79
    0x51401500c9000c1210302a520025400c001c2010401c1c86005041e42020215108031100aa6030750203400d4110610300791400398082100003190410721f80c40c0380605011070302c0324188031150b8000751511200740940d030301d11128a4811111084058821440c0741c65070411703d5007107a00ca10000700240107000e5031070f200d0b07000000480e44600b002d4031168505038010000300016640e0720b41c155012520b80404904000c01e40441c1669a50303011095195480380e9400411403034958100030151040c040d03e640b86c42d034075200034800201d000c0509503d11a4810b94081000e82c0c49040c03100090150802c04122903061018092009a01502c40c0741604d650745c541550b0b560302d0307070710072a680ca0a50043c05542076004c0d10510801042014044010442d0400c501c4504011124141456025170b4210303000d01e0041109803c01c144c034000e030000300300142c00031800d120700d0b070001506960002d00882d06050340c9001140e14900288490400e1160103010000e4690703691400e24000c02e0b00320340c000c02034000d507 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 201893561 1250 201892311 201892333
    0x81e1c02091311071e0201020c0907050403060203090f01200d200c1f0204080a080f0c030d0c020d1b0f020604050402180f0405010302060406140d0e010b1003050c040902030408091c0302 81
    0x11031700c2c82c1550182d004000e400c40b0700003800402c43c8040c10340000d002c002d010000000d600c900040d440365040e40c004e024031181224003a82590b1001c0350794018500c0b600c101082c105285000d40701d48554110b0702003244601002c40340041480030001d0741150200040c1c4860303c0300c0c0041d0420303042c0c03000a0594240022001d4084c202c3c0030342d0003200081d402540760310380811408401780c4001001c403c0001d02e03000d80419002c0c40c59101c80c03000c03108642c03501c1104518a40501003040d040c5994100440d01201c0d1414054404003c60307070003008482c1602d01001552a00c409a5001d01005031046645504881480c099450f40210141c410303140148d040a050074103005d894102c80c1d000d0100e509081c24001c0c196091064049519030915003400121101c92017400342031103141d03466000203100303000d1800f803011580104102400f450f041078140303d880c01170713101160304980c200f490068032030b150b03461320b49514401c6201055005143d0f92540341d41c4060070364618600343c400d800f2140700c0407103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 201894811 1250 201893561 201893603
    0x417010c2307030507020f063403050418060f0803130f050604030201260709030209101410031808120f060d030e010318081e1c0209131107 61
    0x2603841c1d01e03092540902072800040d00803406070080c0c5100906052071400341c2c0020a10035005203441c03114401202070440c10b03504080c03640c4002d01c1040918500c40807035544004d01244100d01c00e0400d01d24461100702c50140c5c00780c1c03225001e4000d00700d50f40103565035401402d61b2600b22141ca2641c0ca4150b0000284da003000744000000c0b0340c0c0181800703013820b10303580046d511880c2040075081d03c0c0c90001c1e0003164203140d08800500c91403072030300e07000b020034154010f020300031740c0051040000c140301901c1442001101800450385103011205844130368070101044001d401c82c070b80c20b102c00080e1003a44070104400800a4004080c01d104507181d0780e9103c22000d078040d0000e803085508906000340b500040303841803181c1641c0c0041810040740d00702c401200300201c3c0341004810b45d8a00340c00b1079108a50201c0e500d4184400007072070b1000d824000250b0495031441300c1000000030041d3b0001d484115502e800c4000d00304880ca030001041a240604010401075100f00070880d07000e41c2230001e101284d10b03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 201896061 1250 201894811 201894857
    0xa0213060f0923040c12032102030f01030b0a0e07090c0e1c11040612031701060c02030c09071404060c0b0c040605090d210e030705060324060417010c 66
    0x414408820f000300c046049446841d40054015980c031001032402060551300805d013250f039244030313a0f10400c8252101c0e19110108003081035445846d40100140110406107908050540382c00540e02980c0d502c401550200a02c41490200381c50b010740800081c4a0b801ca034401e130a1001991a40d941607d0b0800400600d407a524099140b8090305030b4490010455a5800302c0c0c00c080007030400504c6c039450712140400c2c1c0034126000c90004207101410368034000e0410142d8010680c07420680b45180603640002c0c3c4819204680e00c0c085d8074100c00142240344a015011040d02e0502c95080e070b1141c0380c0d00000c0c43c1110304003040c1c4e94650b5100115104156500c111412520300350359840c184035181f01040b1400585072000d46003e01c2c2e410032180c107003401402034076541046071901200c000c1518180350400f10968020780c824071092041000505040e0714204034030585050002d1307012541400641c86018582003031594001922248501c100705510000950859843e40d9021220388000041c80700 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 201897311 1250 201896061 201896081
    0x1a190602100207020609041b09050402040f060c0f0c0b0403030201110909040602090f06030a061d01060f0f02010e10050103140604030f0e010e0909010b0909030f03070f020a0213060f09 81
    0x2034000710004100360216070180c43c0c03080c4018800e1789400031540c00201907601d441c00940d8002401c5104412441e0494400b0000b0001a1000e60034945040319091205689100d00410f00c07040d800e4002c100001d9400c0814880c3e4018040c070380390342d1200c1c2100e400d9000750204a001d036103468032200c203100402090314024640104102e11640d0f40366641400307500305400441c1c10105203001000e060340c8820280d80704c2c8050000001c0d03094501403129031107ca140542690044161006000355a4070445648600c03040d030a050072000e2040c1d5040f030040c008804e44007614055140d5504001d8450707081b90303040fa8042c814036070b03090f03240c50303082501c8007811f039001000706402c2d0191003446070043c0070502c9940014100007440b42c5000010440021b42200c600c0301c00d035500c00118045140482021760044c84500c003c5081100080d51800d0324030003e0040030a1090f624902e0090510801803403040d680d028001440c003404001ba0440a80894003880c400c00820100204501c8a43d2154000788 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 201898561 1250 201897311 201897313
    0x3020705061b0d0c03020c010b06180103020309030403060f09060b030114070305071709070602070806040b01050904080f1201090b100903080306030c150910110d08090f011a190602 79
    0x35200c9460059901010710460102e02000b8020301043c0e0b0454441c4040c4020b1585000d40c2c0c500e000d80095084a000340c403203910030081840019540c030941315803854001e0082c200180c0e00d0306d510040e42d1942c0a6903000030115070411640c4056424160081210148509014000300a8040415081c3d4200329101343c56003240d80700140182e44203421a0390048090308210701590f4240d4950301d914401141e07031248031f50107a0803c008450341084900f00400940c40030b840130f400d0542d240040040c0600c2070510503245013010405120544048800c0010000341c403a554080880c10b881540c0800d110304008a8502640d9180c01e0a01030480036003e000703656507088643c01c43e581e4100c030340c102810250b05440790b80714100e141d8840350382c500600215865482e440c1c0107404c0801c00d50300d0b00b03041c3c03060802164200c056200440040d041e00b159100c1c0c1006440341d50303241d50355031402c1d841304140d00d60f640c01c001100c6040d041042507513040c03400a23910f028100344950003012120140384140001 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 201899811 1250 201898561 201898573
    0x30609130602131d070f0206070c0804121b05041b030f09020303040605030f1003080906030405012a021e0c01081306020d050f091203160315030501021903020705 71
    0x4109034411540e0203a2098000505150440c650039082c200706030003990101070707a100c501010415090149602c19218a4152071080074034000070744400f4054443c4d424080c88500300c1040211080581c1d0189c100c800070900210040e0034a203181c118150f540f442d0040e52400d000c00c3c5800c05e805201d8901d9085040c0c8801507540c840218018400118140d00d002ea5940b051801070350240002c0009003001d07681c0700d48905007201050303848140980341c40c174101e0400b42d0801c002080041030340e803510000c440b911307140d40d0303103042c0b09002d0400407401c04402c286101c02002c280005400145104c950388e4201d81003a1030760481c11034580701c88030380c01c1071329885404004190b601c22400282e001145402030503000405903100d00598100b5040100140d071034100300280b40010000305130b4020f6030360f8020a0010350b032111803d0a0301c409810100009aa4491428240d000e9006604c00301142042180c801b075070f9040c01c44c000e400910071110501d03200741401810314840c0c000e8034181e507041006401 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 201901061 1250 201899811 201899821
    0x1c030c032418060b2a07030309030807080c0f030d060f21080c0a030c0b090303040f0605100b07050106030c12111003091505070906050a020714030f0d020a03080c030609 74
    0x1415411020b00301d480b6a25524007280b40f26000014200319010319020000d4851480070455040b140f001700b01c07009601c110f6003000442d41c085841009c40350481d030351a0307444059041005035445103248001091084d03883e4100d83c80000001800003070a104800c010480d212100d4103e4a2690700c19400c00030b0b040c400713040540c0801d40d010701800780700e60096807510102441c507070309040030150706401041c1144485000d0003044c1102661029100b00030710b14600d400e0b5220028020b8104000d407032542c1d5003000505041c4030303141d078002a004144040c2c1e21803038140340290103451b00b4007086804e0908442c0000d10380345080014804c0b2603200c0b1051780c1e05e4038104140420741000c400300c0030400d0746414000d0b0115440e1050765442036150710010030301d46000f20014154011941c008030421804000c1d05010b20f601190a605941c040c1e003110480c580007800091406440e0740c0c0070b1000707003e40b0312550300300b5030001608080e00e4441d454524442d55401c2c244440c2c0e00049a0711368000034407030001a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 201902311 1250 201901061 201901079
    0x80705060417010b0a0608010302090604021c09110d05060a0c0516030c060b040204030f060605011806030b0a0806071805010314010b030612060112060b0f03070510021c030c0324 78
    0x510582016400001c0d030503c1349000a010166592002000c15200310050041d0300b04a640e080e4020804e03074095191550060300341e507524280031421540d15540e124510f0130000c4031003000071140e100a010307210300400790412680b1002c06543d03101c1d00f98900840405a00c2c06001503519210140030884620031850700c090368010500e07041220990f41e140d82c4034402d40d03110f20142001c1c600408580e812051a0320300b0404454940d0412818444500c100d8140c100021504000f0b842840c600401c080044001042c80e005668111f420140102020000c01642c0904004100540800254002c40e540e42c01501112003a05c80c02c2c429403030800040c045040e003030008681003c40600848420038505001c0d9040950a0704140c0d0803a404552076018800c141c0101c2d80445811071784041800c82d81000280d660805108860142030069501024a8024000a0f558014000c2c1d101c0b600d1558100080080a1f03060134103021900d4450341d406034000b101e0558080d00e14021484868600b0300c0450 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 201903561 1250 201902311 201902339
    0x10e061b070b0a020d05070e04050601020601050609040c0509091f0f0b040306050c070f05100b04050f0a05070c060204060801050111010c170901022503031b08010b0306010c020d0308060306010807050604 89
    0x200c840c04d80030000020350303080d41e101c0e1038460010713590742c514155202010402a00d01c040c0c2554110b5000d0380041c002580e41100b200e2a031482100e0000d810344400400ba1024081c0055a0364041c140c0c1d010030108961a00c0103030740d0f550220000074011500c440c0c41100042090180c0050b03002d083c4002c0c00001c440e41c0c400f6402288508246040c010340f030fa14600d00c09801d4000712040e810014100a0221940c00b507858115011a024402850550007441c02038a0007028500a1921107002c194118000c07031000c0d4030950080419592a9100c0d140074085100c00e100b11400105038242c0141d1120040c07140b84400701c8659540c500054a502c1030740880b00340a890390150b95420482c1c0c000b0320320000c0d660b0030346814003915180d41203c2070401408840e0140200b503030f0a03060494010441b03601c00f1701070381900e9010a0340c40d269111035004907202c100c80704000390810700c01c40c5030100341600040c0c010300c9044110100d40b1684e0300c40c040c41e03845118501c12a6040142480140190403240c451 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 201904811 1250 201903561 201903571
    0x609030308040303180209090f100608033408130504020304050c10110109030e0a060203040308040902071a01030b0a05070e010e090402030a061811030a0308010b070c050a0602010e061b070b 83
    0x408417409540703030001386200c10181c07404600c1e540000d603242c40d40b000034014102051000b08003004258903081c02e080d168031414811003100d85a040c02d40ca00d85c0c500140d0304451540d03031720401c4584886807030a01d00c1503100d05d0b00c0c00300c03442188600141c645010b00813030b1300c00d944c01700141056210f94428022419049400f120a1041c003180003403100d40b0904c10180303058080d5a602220b82068000d10100c0380f0140c02c80c10442d003040005101103150760045800b2501002e00c01a035441c25820701224854006400380c074440311180000050000444020703005208152040100352501c0340b0a0302d08241407010b09010684e05503c0200314941050310503400350001d01600d80843c8296129400c40e1741c1114008011420151a241400529412007030300c4c007000c0c1c00804090041e500c028016a00512591101510015050007004a1400313a04018900a040155025100c000203406403a583c0f088483c04e101d104001800848600c2144140c04600102c0c2890f0505c66114045a0400186 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 201906061 1250 201904811 201904841
    0x4030207090b030a030e1c140a030e060406080412030608030f04060f03051006050901020f010f05090d0801030308060424180e010204050f04110c0d02070f0e0603060a15050307120209010609030308040303 89
    0x114400403071900e0448c4d102c009150306c00b4082e042514500a451459410f91079806008140300501000e500540c0c40343d0402c3d080a490030110301902001c40140206410100b540d00000c510600d94a006c03901030410f86181d0b490304048036000550071401c0b20750031203428848076000d86040181e9030091000709a280c0062040e41c140c0741c1c0c060462401d45003100d804500031680c80c0c0c2007260503c8140401d02d03142c1c0643c03502d8030366035146460082c0482000341030303144900d0342d800289000100c4c201c1021801c2104041090384555501c0c81d2862204180610034040d509150036881403a0061007290291a0024110701603e1503810034030004140d2542c3c1c1c0903004c242000040348000d420098002440744aa00514401d402d22a01c6a14100070f0380c0500000b000a40070321050b80d4010480a40c449100400000c050100c00b440ca080b0311416030169405014181c80170415420011002901c54001d807121001c50760703100003c94145446100160001d9982d102050010307100c1e4100c1c20010000c55 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 201907311 1250 201906061 201906109
    0x1303110f030a060c050f1c0605060c07031e050d020f0f032d12010b0903010b0109150e0102010219030b0a0501020a12050328150614040e1e04030207090b030a030e 71
    0x12180500541c031080c030200710b03400f0044207c45c010809004407070140c4001c0d01c40c103080686454495a0f1181d070340c0401010305000301d0342806803040d10511900c4240d000400c40b6024210340002070740725840361b20307040144c1c0510490794810400000485007040440100c2c0e007001101d83c00700c94080c5040ca40c0075040c500c810071038540724180340c0d06454044c052100c24285d07100303002e504150841d640c44101e039060000c01d0030100001d84190f1a082e04c0310900b8103003c0c15603210500100c0c0240f02c3c81e0b2003800d00ca042e002820746a19850350055040030002c3d28038003046c03500d80c0c0042e43c0d200c0440600904015035500c0485160380706102554002c02c44802140c030032000c520000f000000d42d03844d0414507640d9000181c0a0140d00f100c00c0703004014504041e8142a010100c0d45000c0c40303540106000c401810700802c492120800e2801448400c0000c90400c80c18186002911003055124903e07e0504000d40c1c94403e14000c10007a80b915030585500031684030500903c9110b1041603c4640090341c00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 201908561 1250 201907311 201907327
    0x31f050f0a090f060b0c100b0418020105030601171819080405060c01090501020f180a0303020714010e0306071806050f03060d030e0915101103030402241303110f030a060c05 76
    0x210300900450380000c1c000d0485031403881c80b0a411110308c0d80159119509040f0350032010714038040d126a1003602071078030f80e5880c0d0b075040050303541c00204500016105c100d04200002000f8142415404035248001d4482da4524403c0310300c00d94130201e1001e0207004040000f013226207010030081c602c83c0d05100010030000e0301c03034682c02d089810001d015442c075000022029100034411200d010010741c11540c0d50011820341e10000c1d5a0441805254916507400d010030b0000d80c001d98801c0c0c0000c0c0000d08550203481d100c40700502440103110b40c0c410384110b85002190150060f002c0c2d5050020190140c1e0542d40c0e030808210300b103c0c8845054050014800080115807101d0301c2c8207105003210400c07a482c2c00030740c40c140000c00c071003040c90b1700030044d0000a01c41c58060102c1202d4000b50122000e034101a400d0020105618030201c0d0310520340b00014040d44104040f410701c900301c9010f0322450351007502c0394080c03000f000c0c8109448c0f0b0340b581200d4103c80001c1c80700d90103210108002e1424034109804 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 201909811 1250 201908561 201908579
    0x20a0c091508070b03012c010303081503060a02072f060702040204150207050f0117040807022e0e090f04030c051011180a0501090b0a1202031f050f0a090f06 69
    0xd0360700400d15822000005100c4602021071f4075801d0340009402e10b005a80d12040443c400106000047c10800c20a0114000304190900d00c00500c80c0101941e060f41030042c0024007c0d0b1000b02c0456402503020134440c03541104c0705441d0303291032040e0744400e0064440001c004490303000034401c9900035030a02c0041000301d1000c280d0812080709400404141d4100410402c4c802e0200720094100702c01c00c4c02105c41c010216500c41d8106501201c1e06489030407500c0001d5000c0c10248100d2001d5420450560000d5445207040001981ca610380210f042d00b00800d20125000440d0f036840b40080e05c10101d40024464085031100364080e00c16504804a8100954141e5226401c164070030320020903054a14034100d410039052260458054041a2820300080e250313040510949520140110364084e80134002d90241e60030502403002190342e0b18184103841c5c00f600e040c2070320030300304031600070040386c941440c0508041d420001010103000d14948043c1001402d11005800c4055031518800103100360 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 201911061 1250 201909811 201909823
    0x10f0f3c0305061b030c0919030209270601050906010e0f040e0d02100515060c0304050301110705060709051f020708030406200c011202032a040f0501020a0c091508 72
    0x840b84024003110304004200350803012510f440f50364000010010700220003400003c55107104416144036021591b01c40401810310310551001e50080b1882d8100b02c2d01c1700c40c40b992900998510655080a0740d084540280d40c0c45007401003035080061030f00403c07003640c090500303040715040c000c00300e002668205012070180d46205201900c158041c9200c2d541d000d405000b513091900000c10200b0091070a252200c031401e030f080d10664044c45001540e034542400c140110740c0a0034010b00207110f1480800c22a005943c0001c0c01550740340a107001041c603052090340d510003255001045402d43c210620f44100501f000c181018055100c3c040340041e02c00d42c24006400206069201d0100b00205418108100303002e00318010500c0d002070000060903078210681500d4030b0a023820041c1c0346d0780c1d55080000200d540c0d4803460718840140c40980c40c4101514014000d480000310580d5425584500580e69180030800c01860014100c13424440342c0059401000442e00a602d00c2c2001542c894406041c02 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 201912311 1250 201911061 201911063
    0x3020d090f0b070210050f041103070e010f0f052202030a02090a0b0d18120503040c080f011d0a020901090513150603020f1002060a0c030b18010f0f3c03 67
    0x54003080208668042c410315520f00780480e002c1c05540780c81f02840107464001400201130201207881180161410000000a843d801b0070203040c075611003c2900700c5c41600d1040140c500d544100128280c14400c0980207510094540e241800d00401e07404000b030340004042c210321344c2c2d00b03210082072507030798011110040000c03003071199640d4011702600041c0c0d1007409182079410900301e55175002484a5440e042c40791401d2401603140d817540c0c0380041c030081d51a408429148902459a000d107041035002c407060581000546500403041d03c8541d4a40e446000c02030750001441300100003030801500300fa640b00040000541754201c1695444242482071a00b404055079107030414000c50820a00c180725076078048800000d05020710034025503d800c02400141c0e1551140d801906090194004681d02c56004106400c026003084264107026024811840b401200301c070005064101d200c015000d8a903801c901710100c003017452480c000c613100c0c0d040601440d0540c030048501c003003110036008091 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 201913561 1250 201912311 201912323
    0xe010f1103070305070b160c06050402060409060608160207080c060d0e1501090b0409210201110a0302070c1a04120302240105040e0f03090d0510090b010501020d020c010801050103020d090f 83
    0x85c00b00c034100860881e000502e00e00454890740c0021a540381c111100e0324005071300c20070110b0305d03135118404150b8500135a44000c03015410070a0218400ea08904054031801050602402e1050406812655070603148111440c2c2d03000001c0c1c42c015818410010041d03c11215000f0501001001036185441400207448104c45038080042c4107210650003103505401e4111420711550a158840c0d03810071b0280002c80044810607c0907140d01e034003c1d0082700101002062030350b11203801150160196000b44402c485540421754082403858a1180500810300c50802c1107040c20309200a014001c403400c0701c1a0158460603001c0701800c40c0d040c4c1c40142004400c81001201d5140605110998480c2143c000c41c40e001180808007141d4000300342c130941c00b000c403110a510042410000d04200c5014940d1001034203000c003002c00e04c1200c1c44168101c80c2c1c03c0c2e00700c41004d01441d00c22621703015103810351400160010300420032503200390041d2003415200d000005000100e942d50030501d841001c0308980d8 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 201914811 1250 201913561 201913567
    0x911011815022b0203090f0d060501090f151a0f040b0309070312020102071a0a0605030f1b0d20042d060f050306040b0a150303030605150a0e010f1103070305 69
    0x8084400c460720b502c0c40c0c8030181d820f2045907481000394680c002d540d000f9002c4c264254003040e440d510714058071010b41c5c22030800c10055131241401d01c003500101c10100601820010200030700f5280e030001c4012103000c01082003c04103201d00b800b28a82c40840c10003020b0700d080c400801c0c285030020085001e889039a005003c114076624011804980e059900c9041da4030600c40074012501516003c8030316514100c540440d961040c1c1484000c0c150740e000b8581520a006070301d15490300014070790300b0820b10040f9004001d03c00b0702c00c011184d100890b000300201144040711a000d0886408404502002403000c0341280c00004c0d107040c0f42c80b950034418a03a182d0851074440d107298610a0034087c000c10941e82403c1da0404021030341e60b11020380b0050441d1155000500016019071060f07004207402411441d140d903403410010007805150007034500c40e0141e00c030b071110703400003034000c0344e003011341a84401d048000c1d0300f001510200a180c2c00d101c1071040c2005d5106041805100406039944282c44e4291 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 201916061 1250 201914811 201914833
    0x402040509090601080d031109190801060e100e01060c080d14040f0c0f0506120406181b140a030209070e0907030f060b07030522030b0a0c030b04091101181502 70
    0x21a182021b80e058091503e801d45036250100c0800840c0c685a0003079981d000d000782c1040346016901406c1c0c0c0448025464840c01055110030000080e001cae60441817a21070340780c0c4503039410b0001d0100b032096502040b4004c5800340000c206002910104019600014000300101140012404d08075401c5880c40c00440c0400200101c02000c800074091000c60007004074145800719043e44210340d0f0030424001000005810440c42d90850100311551022600910000c3d10b41850181c0b03104900c5100400c0040000c20035440b0042c400e111440001c0c0017080303e45c61a001d0002d01388015054008200c851803c041c4542c41c0d03a0022170242c81c09a41c000f410251900b841d030103c40c020b81040790032207410020040420f80c481c0503541e20030a908818281e50f202c100611100c1007455000418249091b010840503900740c0e4424004281d03a07860070311414010004000480710004002440000e022103184c80c554400d09402e408480000032407500c19894080d400304142c0000c0038000160f00c240d200c29 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 201917311 1250 201916061 201916063
    0x40b09011a010207090905071e061202031306020307121e0e03040305060708090f1002040e0609042001020328090503030f0a030203070e0d05011d0708030301090b040204050909060108 80
    0x1c8905200d600c44140905114000035200c1d582442003108503a21113480c0b03000e0020900c00c4400400131038000d141400388120000307038811040d10840003c5407840446a07640652802181d114002c0c0c5044003014500e03a60300c14009400c06007040d4200024454440e445c3c5445200c0e481d5884101174016501c80c2c44480d800c402d441000381009030580085c0010030001b100010b0030340e009038081c14980510740e5203407603140c5480542d003038858140c4180203244003043d40503801081500d1403080030100c01c0e641c1d003051209081040e1001850a0514405201c0c008240c40c8030013000c080500c152440c10580303521248840f40110300142601b5003019180070740369000a1a403000741029400365003009541100180c25008520124040c50740010005203003074414410791000a0004107100c03690300745070600900a182c0550b4503565010014143d207241d042c005051022280004001c51940c1c3c00c2050f82c40c041c2c560544480d401030307024031012416950300c0b030140e44160aa800108200c0d80740000c45 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 201918561 1250 201917311 201917321
    0x504060603020a2012030c07050106060c11040e030f04080c090a050603060411010c0204061508180a15021908150f09060906030a170a0201060e0606160503070b040b0901 74
    0x3091600c10441035110716002a08000130780341e0100c030444d0200d0300944c80380c10403c020402c07018a40340001000409006600a0030440d40500000c0141c2501c43c1c005803111200003074080c0482c030410381c680e030003481d2540020944912a2040e2400e00f80803070503181c10b90700a0342010401e50400d41c4050700508184c0e500b40c4e0b001c2c44091080c0120300300000403070b4454401501c0070300310381c5a5a481c0a5507034007580001c0a10340c2d0280c402c01013140e559600c2c1c65014070002c0c18030001080b490102d091001d070409441f10500d07418026281840055031040804141e884c06000c4640d028888000080300320240c4503400c01c60742d11800c0c90343c5000c5e4910224925031002c5035104e494034206034101c0b0b4945030300b55680290150f0310300d40316032140070010b8034246104400424227103032b00c3c81c9018a00c00810251a2180051300203001c0103444665180810b207084964541050081c814202413001c0d04407940d208a001d07606403460b04901c3c1d01d6454801030210340641f11080000c0500a030790b4424400c6c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 201919811 1250 201918561 201918569
    0x702070801231f03080c03070813030201020d090315150906060e090f0f041106070507030c140a151427090f0f010605030601020c180a0e06280603060c0306050406 71
    0x40a6007111010700e480c0003484513400003501c1c0c11400300350107002610400880e00096008111582c45040c0000710318158031481c04124018050030180010701402590801c0960f54080f01410303000f54000c417050010500340024001d100301c111000980c491007840b030000034100c9903a4840d0000760300b2090100c8240060400b01091005c0d8003003101400010005581155100031407940a00e00900050181d008110001e011405141c40c00020084110502001c5684580840007143d142c00100400840e051141959408412801c5031203184524480c0302c00170750003100141800c840a1200054580015181080c07500c0d901d60225076141600341950b00601000351100c0d2440c210111000814041c4074074018820040081801e581c02440b902022800140041c100013941482030f0380f484000341d0f5010802840c02912100401000c55254401c074240309500d01c407011090982c400c0001c10410344865103595940200000d0258064403035070b18410780c1d01045140c200400c0100310381581e44 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 201921061 1250 201919811 201919831
    0x17010c17100e07030b190302010207060311030a05060d0b191802030c0f01050405120304090e0c09010b0d0f022a01020a0903030509040b03070b0d0506030a03090905070207080123 78
    0x4201d84107880c0c072010015034460010062480c1c8031010300f540a008003108440e48404001c5411424514201281c1e0440303000740c1c21035000c01d13910b00b400d030201e48046a0448035210200002600c02d00280c0060350440006401102c194800752a2110040d00544500c1ca00d8807118141250070310300b5004003039040421181108280056030300007944c541300030140c3e500642c065240380146030300820907100100742c090540c65a6030001c01d541c4e51203520902440945c00d290141d81c440030724001882c8000c90b0b001401d040166424040c07501941e40040b52903010707581d190300c02c0c4900501c0a0015280e0f8560741d0740c02e04044001e0010324810000c480c9006843c50384144542074110381e1003085042242d4040c01c00076650a00f01020a028100c1b061103283c06121703450340001c0c600004c400900e00c2e90000d8004001c44e849444c10152640031303100c806000180c840506018140095210a8000301c40d40100c4d410300e80d8416100d03007900c81d18071280e4030701e000030fa80c401d20071030110340010b6005200c84 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 201922311 1250 201921061 201921107
    0xb0105030622060302040c09030512030f07050c010b0a1d0f07020309130e030c07051906050901050c010f0c02071d0108070317040b13050a090905060f06040617010c 72
    0x1c00031429200d100d600121040c2889206945142159400200038580280051001000c168000b510045841c4405c41d1184100b5240344031442110050b0b1740625042c502d4512240c403500000c49540c0c03c150030a41055681c2d10b929691039a68141d42d40c02818500d401000c6041d042d420682400c0d001051208516920400c100b00594080308440700c11904407104000c0f00c02c14001e80005211001c04074189201c001440241d1840000b00b020480b18203d41401482c0c102034050500b21b41c407403280b07102194003031000042541c0144d01901360080443c0001420f945020304946c140c80c000700310500035800c0190306005201a100f071070b40e141c841a02000300c09503d842c0c00c89030760340c40e42e1001404002028060300e41359406501250b005100f000e00c0c070b40c2c680c1170000c10b60b11805003d101c0d540c440c04046100251a581a0080841003600200070b000681c0e1900340ca0940e4880040c10923500c99078410700845d840d43c100c440c61100341c070302000002d003101c112580500105416400c50708403004807 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 201923561 1250 201922311 201922321
    0x210080405060f0c0c0a05031806040602030412060908270303070c1503090507090b011209080a140903010204060509030601050d020d06020a0e040f0f0606030501060c0b04020d0b090a060b010503 85
    0x41c0d20740c00035006800520107035600190800b0034005d07060344000034002d92296030280303e4000003403c074901c041d054519105071504104801c034892407141c08056002030004020483c0b9660108010a004d01000300f21901e0903518440598045406001e03a50140303915000e01a441203400072090741c042c0d00071490080746440b81100103003503104009081000e420b44241446c4a600602da4244d446001c0700c45607a11101140e0141c82990241e60000d000b45c60003030910103250040c10001500030440d1498800c41c03000071200000c4028040d00345110401660305641c80920040000b02299500c150f124019602010700b4404185d0041c0d100d4070804800101507900e46103178100581c0c0c80040141c1e02c0d0300114099500341c407010506540140361948140c5010041c1c0c0081c0401221004100100390b00c58505a040720000e0181c200060f034140d0700c0100140c0610301c032036005070000b4007000314111aa524823448250803640b550b966000341001500308242400b40c02c252001c00d003449400c500c0c0c5 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 201924811 1250 201923561 201923563
    0x8070302040b1b0c0306070f08060604060f120e190c05060a0e10030e0a03090914090d031a04181205090f090718060503100807050a030201080702030d06030605040210080405 76
    0x42e03a00390040d01ca95020700f03141140c0e020800ca08400d0b501405031802c6103440340c2c0241c6250154490f10011901640c002031051421008a8007610a00e0719800000354150600b141e154250b01090040c0b41e50743c0071030f02e14842040002648041a035600f840306640b2600d48256500b01d43d0384400c0c00740205010004d01280c2000c0d5241203010b007550456001e649850040b0090060f1403582c050394003074040742c1c07002d0541c00150b102c15609910400d00c80000c0036802c459400c0340458005442e50401000c110f81c2a1090f002948580c008504d05101050f5042c0003130708843c11850740480c2030018141010801180b504114801c19103418402d040566600c003180003e948804c0b13240c8603115940010300c0503400350090140d1070f110602d180e4134443d00e9000c0038001c1e40c82910003196000b090351000a841e1400503d007015558042e01c0111190720310303401544c40c05000382180c804e600060041c00c605080c2842070100541c0038010119403400e09005020881501d1442e41042159960801000c140 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 201926061 1250 201924811 201924817
    0x10b06030c090109090905010c1116050f150f0304030905030607080109150b0a020d1806020c040504082203030e0108150d060f0c0801080f070315050a09080f070308070302040b 77
    0x30241d0480c0c0e441d10b900300100c42ea440d254018030822464511385000340f040540c000e40402409494500c0b0300c180300a24542d89001d01c1d020304401e400da800040c095030030305901c5040951000340c40b00190403440c00503005590000140b02201c2107001c000c00c41450307402118100203040542c0030709464189000700070002c0005000311540f0a031645020100100f09a516900902105400c1030300d40303100400007900c1d00016640f1100159030002c68140c0352403805003000c01c4510b5074000346030b42450807044c4400340400030400d40d030005080c44270160800101302c00924002e01c030790400c99250700710301d000741141c809070301094100f000710b5040260000c102d816008400604403500c0400350400d01d00040074102011030fa001c070310304100e880e00100b508802814140c40c8500b06550560b00344100c8207580d04414031010b0b201b0303444e400495030301146640c006a000f0350b10004c00b140460043d11004070a602c101801c0703807241f0340020010207050b840502560041d445280c2513281c00c0c5002d1b81c041640c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 201927311 1250 201926061 201926071
    0x1e05190903020c060a0201021c0c0203070212030915030106110304271b0c02040b040b0f27040c06020c0d050705010f0e09040602040302090109090201020d081503060405010b12010b0603 81
    0x5540d000000d040c1070003040800c102120080c40036a0390040218028041d4100d0b0904585404452003882181400d41c007501e070000352242d0003581051400d408114482d01c000791411810302003004540c0c020340300ca83d1107411014483c0c1507559254505400140b0b2000d10072a542c0c15a0028441408150080030101c000e9100ca860031100520800301c54000501140d0034204603c1280c0c6140180c40d900000c034100e0250007110104000300c91101400255246504003562091612409207001d2401c0c03500356682002808607150041c002d43c400795a005025a004c0ea02e0034038102c1c0801c11030303a040000c1c0c0c03840744040e141c038911043d00c0d80da003c0d40c5802c10302806050000d244101554030784180504041410002c0645401c0c0c102800e046000b54041d0105074000c003c50000801d4508881c01400500d941c10f0340188070210100328100c3e010746c0080e01c00c100601000c41c88200c15034080000c80c8c0114001c1e000011149001c0c000c1004400043d4040e05540e410315040500c690b480c1000e81e5808 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 201928561 1250 201927311 201927361
    0x10060609060e130510080c03030c07120c0308070f0b360c0303190206070507030504140f130f05070903150f021306020115050603010e0402130b060408011e05 69
    0x5100b02d00001855201d140304103041044c680804c2220750030f0141c00103400c0362098002d079049103079604145526449024010005039200302020096950401c0881718a2402007284016a540300d0340c88030301c2a032200b10103076641202c42100c1002c0c40340000e40d5503001111035916403810300b81503448401071070110450b2800030b04d01034640070240300309000c03000e044803005003965a119a08107440034980b0085015800502c503c2000821550199003140c81c01c6402d03484013402e091a200551007111104400a40c020211513865411a144c0e80760203294001000d0010a409500c3c920030812250300808042c10004649020004a246600d9860450110314004514150494400400b900c81d40100300600203041c8400101c050741940100b5401c10070b61080c4c03609aa80c0c10401001740401e014a140302e6510340003003401482c0841020300300d0010f030710f00442d4030807196002850503082a44042c0c050794542016441c0c8081c400c0361010050f818860400103030074501000c48500201803004841 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 201929811 1250 201928561 201928577
    0xb1602060f18010c050309010606090506030c090f1c050d0e13330f0603050712020a02071a13150c0b04050f030409020d2f1b07060305010303021006060906 68
    0x240759016003070b400394510074800034040905180f000034036541c01203030410303030951030b10b8800b1440c584107005032021600f004041508585031406014200d030b00581000380d20182500486810ba1640ca043c5201c04000c5808208d00350010b040450030482d207580c00c00308000310100740e41304540d00e005042d00300c22140000003c00484002001c812404104040084401c4040d40d41c404000c1100c00b403000d8805200241c90a507581e84002c0d400c1d24810303a5100041584c0001103001241540c0c060700c003c0581e0b10440340551740d1484020780c0a21403070341101480c400014400c0052101280e038000402c415007100c0714400345514000c101e181c61400050200c000580400c040c803a0400225140d40c5110302070313a565030382d80c40c2042c000b94401d000c101c58141c02e01046011904e00e005c200d070510401d088890500506602007003050b42d00c80c02c111004142d44200301001c0135810021a804ad19080c1c600154035411402d019140c01121480e00d11110b0034071909101039648006820110341e100d09020003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 201931061 1250 201929811 201929821
    0x8280603060b100f110309030f03070201180b120a1b0e03071d0c07052104140303030f01060e0303040306060f0e010f0f03030302160f0b190c05031302030a020a030b040b1602060f 78
    0x104511611a1295240c0f14003903a03d175603049e01000800c0c0f07641c400d0301c81c0c0400151100c0d44a4064030070344070301861f81605001140c800013091403551f07442503072105c00046241c00741c80804440700d499500d4500040c3e10700b0400401d4241045600007030503200d6a02c0d07003005048a41c2104004004004a01c4201c0201d1030004001c010081e000002001101c0d02003c50b1080c4001100c5410030310808000c007550380c00b168142d09000c02203a00460a000d40003006d6801c190003a0764011003652207540620040200201240a40c0304a4024041003015120907a1500c410303c0d41a0006030440046c0521202040003040000c00c000c80c12254103003405038a80ca04c14040d0710b0700c040801000ba00c10040d520b0700c28100455040071502c42c0105031210441122110350b9a0110340501a202011542c00c0001c20203864035909a6a1464402401c682d0104020ba000c50700700036460703204445041c8440d0a000c20840600b032010f501c03906202c6484403003854240000e6030342c100035020740342d40d101401c0400c1c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 201932311 1250 201931061 201931063
    0x10302070209250507120305060111030c06010314010b0a0608060105070204110705100c05070605040206041716080c091306091e05060c1908280603060b100f11 70
    0x210312a40040c8a04500d162102c0e0b00c591007481c04508801003582090480151805202a0f426854002d55104483c8002c104150020080079100ea414043c104040d45a003030400c01c010212021094082d04895141d4549644640090240c509150b41010a003c1242e16415500011a911450301c400e40f41ca8000040e210381c03003502c03800f80d002030030400744840c842e08030b13001440c0081c451801c07035021000383c0303015000300e0b007141901d8000604100004404265150007082d0085d000030000c902d01940c91039400001c80100340541410b400c17805c03c06080f0207030544664020803000d000350000c0000c1c0000100a00001850001c0b00011446084c06002c000d5100b01416540420700030800240c6503400244094103002c119098404d5000045031142c51105035405601000b400b03219000c00054181c410140080c501d5070502c00920500d42200d0808805040380d803108480015003e04506165040c0c0d04090211401002103168049510387d00c903010742c10042089c0340001084510102d52 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 201933561 1250 201932311 201932317
    0xb010f0804033506181504060b030702150108030f040b0313061415040902090105090601050c0303040303050103120c050d080c090a1e12120302131205061914040f02010302 75
    0x1d00340c042810f5448004902c83e84583c0303408144000d42c454072a6550504203c00100894080a0f681080b18041106040e1900d00b084406c40e0040010400701e032180451383c0f10342c00445002d40140e001030082e524040c1e4401091303000d400c84101a51030848032900e000d000348510b2041c4040c1801c000001602c0381c0110b151003101641c492400d00112601e0f0009903e5850140d903d64010341c0300510143c1030b441d080c46025007040c0c4c05440740010760702e080d04200242030b009002c00d0610204000250a2040a000961003107200e03480001c3c8550560a016003065141010030003030103076070990940800c1c0001201d0907502460b14040340c02e40d89514511400380242c005064210300044800f0070705d565a902411190001c494551109e035565030110101040d40301c0f0041c1c142d2904041818915200350020322607410040914091280e80710f80600d41c2ca42c84804c142c40c1e0f80c010b00300b4811020700344901201c104070035040074130149128101e070310304000001d40000c202821000350241164020303010b0b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 201934811 1250 201933561 201933587
    0x711010f0306210c06020a150c0311030f07020705091e0601050c01020d05180a0807060213050907030b0103050703020a1706040f0c0c0606060c0c0302060c0a0b070f020708010b010f080403 82
    0x410f0b0903582d0000418100700103004021074030614505004501c1601c0007501124958006460300c00b613900b0380d80c82d00d00420008620340200f54480182150404400c0000e40c0140c94600200c0d18515184c11b000381400c101d500040d1184200c0c034180520002c40081000e11040381c41a02885515540c0042c0d1303683c8140098002c55500100e1074070040c032107a50040b4410311540c4140d030781d204e1524070380c5a169488208014406e850a2204501040d0160b02411001301e08209200384141c07594009103200e4803c80710500040d40302c95001060796810b000361500714540341070079418074900b1700c4007801803103a40ec01e03c00320305403650000300326035600d801894005005900401850050140080c45001c0f00102501e01d68100800005c1e054450400303c40e9058006003905c003254256802c10a07154805034400f42d640c414880c0d01d80c0031030f0a4402a500515494507a6070005007001006030400016620030003082e45010f9801c284c60340c010802100280e150314111307180d41da41c0d10b42540c0078283d0181d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 201936061 1250 201934811 201934829
    0x4060e0109140a14030717220b180d08090d03020c100e0a0605030114010804081902011e0605061b031b07031a1611070b130302090c0711010f0306 64
    0x96490b68074020400c100000d005162990780d00004940b074680d01d2141140040c461101042c110f1007100c50345011700032641e048000008034000c2c090030080508500e400500600d24000b821444201c2101c01441080e50b0544091003005070644624003640112000a4092401d5040c034500300340c800d0202c2141d924004041c00c0030100144e0f4018001b00c0d00046683c0181e00352100840c9860144003920304071460f09040001c001c2014004441482d0040c0048440c039400b4803034003041c58070100c40c040c0c1c00c0760700d50700006140078111841a140d25400345001c0714185407040510450b100e090441c2d420203010211403080007956036146140d44100c860030549400000c410300302040d408210003040303a0003204814480038002d00c920170716210654481c0c00302101c0030145100180191501581140b244e01990700d019610004120341c1d074030a07558040881d46101007801103141c94508030303402402c00d6048034141903503170380c030809406180e07030300703d418800044206608035109400c82c0000c0e001d030b04 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 201937311 1250 201936061 201936083
    0x30c070803180f0f03090411162402040e0c030606090307060e03061005090f0405160b09040608010b03071208041203050c0706030509070501050315090702030409050c030106050304060e0109 83
    0x2850220707002001d4902c010b80c0c0c2c092007040801c21800000d10700c42d440c0324580a1803500f03104d0300400005040c5400c1c0e03515a11011310049803401d02004039601038a00901088186138900e440c40f114180107042804031031881481b003405460840c2d12103d91000320329103181c0d5a40c80ea800002c046004110003980e2512480344040b5140340e02555103442090300360220f4120340c0720020721200440d0613004481c0c10900100c00100300d00c15540800381c21038080d809594170307109005a2a04084002e41081c0c0d005280090141424201442644001c083c181d00800004280e000040d454440c0f600c19034003403c01003c04031040c000220211002840035440312080800b40745009080b40d0001c4101c910180190080000c0c507074042d005444c41514110040e00c0200c0c08d0138019240c1c4c1d00302404419110442c0903407986241c480b0900c0d14050b015a40045456a14010003442900e80c0104440003181040c4010490302d41c0010a503600700f58000004640c100600100b14010310000f100500003a1041d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 201938561 1250 201937311 201937321
    0x1713060903120516081806040602010e2515050d2c010c05030a0e0a02151317060a091407090203190216020d1e03020601060e0f0f0402030c070803 64
    0x2014008040703074461400c1c0003104051560a665602401e10b020b007058240c4103d4100040003040182004180da1039091a5007002802154894000e0341050000d0f0f03540e00c0c0d805003505401c102d00c0b090541070400800c00c1d0444c01e00e04110308902d5100741d84080d500c500c0144402c40c06074090710590305603030800f007005005400d902c14921204030700110260300640410740715808180250360350600c280d15081d2464a81e000003400900d51041c044080740105443d810042c4d5864000060350b01d41c1ca20302503100e1142440e41d459240003980014250400c02c500444804030119140d9405841610005090022800e02c0c10310080c050320b04054501400f940030070200c0655028500560101c0c20003143c2c41c0e00720305004100c6c810301180216481c00c42c0e02c00d00043c50540c00703400c0c07484d200da15128110610203020414110203050220090381008005102155221010810160301140c01031103078a00a400700703800c0c2101c460650701541d000000100800740c0113044031a040d600ca0602523492400b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 201939811 1250 201938561 201938567
    0x40305040812090f040c140a0306050307030803070810062f06240303040503190215070302280209070f18030c0e010602070e0c0c0705100c02010e1507171306 69
    0x2c0303c4564810f500c60114201541010701c903501695005444140000790201c001e4007898202e44039510405494080c041040d403070a0091200840c030601c1c03003c0c0ca9003080c1c0405003801c107008048002d880785184007004010f0f4071503204050a0108011440b4801ca07050030131412140521120095104000030b01c0044030101c000844c0380c800c10f058040551101c0c1c010551288501e104d800d41c15403080e40000c0741444548007030214244000c00000b031030185041c1110075908040f00590160308044641c0e0a9000702e1884038411400c1e201040c101d01450b41e0019003003101c09041901000f440d40703416825a2700854456204140d41800210016075038501100000086c1c001c80280640050001070790500002c6d00d0303800d03200d130b5400e5142c1640d510300c0f44080c40d40040c80c100544d8442c40000152a48039140e00481584d0f40c0e82d1840001c0038240005001c0d403094004540c002c035840c2a0034280c801011080c0d442d01540b000180703110540d000e03404101c500031019440c041144a0100103161a0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 201941061 1250 201939811 201939817
    0x10020c0a0803191110090b01031a07050a030e0c09011205070b030603071a0405090c09030d02060403021c030b031903080a0504030c1104020d150f05190e040305040812 73
    0xc8900c10005529603a12545074000c0800c1940303c00b0482480c40900c60003036035900c1c000b01d0000d046524240107410080203842074600240c4805040791f006000b4880202000b01030301c5042480b451080c108158000e01030b1041d60400000c042e030381c01e0307113004040c010321130000403080c000d04680d21540c442030981a030200f4082e040301d180c841d01000050001e0780400740ca129a4005001e41022860141882c81184e4103411803a001401040041081c0e601c808089000c0d40610040310384500c0c0180c149460803ca03481c1200030341d44a9003c0000182c2c0c00542850707542c0c0034111102c212540782e4000c1e4007800010301029414003814210090504450756201c107880d000b9590f90b040ca4032090480006c46e28107540c0a000105c660120750040b54100340c1d4040603080117040189404006030300601255800c0460003d103c0d0f4403801008a10010503e2102a150031a02c0600d420307003440b064514000a8031418444a602e880000d00303150069040d98010710101e0309440c0040e4280b00c4840030743c0c3c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 201942311 1250 201941061 201941083
    0x608130f0308090114060307060f02100609050a0b010c050a240e010f0b01110c100e03010f15090c08060f010903080c0d020d05030f04061d01060f0302030d080408271002 74
    0x9031a0aa901c4448106800140c6c001c80e00034015040c07040c20308101312414002c0c1241e0034107621600004103410f079460711510f0014840c1708400269404d20b0301d01442a55000024241082103c1d07064030003041780850081103140d40180101c0090100b244610381028200040c40c000d82d242140901103084190001035040380c1e200800c00030740720800019a203421141c03030203800715402500386001904000c0c11b1210341c10461308001544650003000242540d0a1540d040c11040d2940c5200300000d05d00034a100c040d14942d1400c1c0185109114010301c188801400030348640d801514550441e400740d81d264000d560080d01c5641c0c2e41d00f9844c0102e07620f2807002205e030014030402c59141095441401643e01444c5118103002c41070310f55071110300142650300c02103103112039000c411000c110070921030b2034024004840d001403081e285004041c1024584540041400184802c100002d44148111014135010803038130401e84510301000031158410042c1e81c0d070040804591488030b1600050100825 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 201943561 1250 201942311 201942313
    0xb030f041403070602071b0b04120501090210050903011a01230903240604020f0d020d060b0301090e0111210405121204020909010902090a1112070302040501180f0608130f030809 78
    0x160740d420f1b05020f901f044500c50101024400e00060000400340100c0714001c60145001082d1141c9980002d107100781c000349404081240060301815500b002c2c001d90181802440040c00c203140000d0010340b00640c0c1c030b02200c50b800c07181084030b5001c510003002d88a04001c050103d42802706042024880e0148080300c1255019441000039080d00d001d000b15590345424111090610111070030711340194010000c404141c0c0d0b203c06011896184500285000b08404d42c1c1c041610f0140c0d00101d82120003550b0160801d001c104844540b60384c1020503401c0e40c5400b14441103035507542c2d003030050074045941c0d0011310b80d00000801c010041000c0b0911405a8000c50381240d9540b101c840341800c890311800300079001070b8220f0002d40147d10ba03a0041515800008440d440e15203880c2e030001440a08666880100f5030205007400156440b012038501ca504000040b00028180740030743c55050380c1d900c41e8508202c844800034503290000014185440c0d03100940c01007032051450003600c00c075030441d002102 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 201944811 1250 201943561 201943583
    0x17070314040810020f070b04082203020a05010f05040803040902090f1c110406030f08040306110705060c090105040b12071b111201090b0a0902031002040b030f04140307060207 77
    0x1a400c040000c64045400030702c010600380d0380d0035a404000c1d402c509200d1440b0803050244c0000300d00c0d0703220218451032098408036661651300305084c0200300000101c0d0b030701c1006068107100584440c04850107541c030900f81002523481800c070407991407003240c1020100d40400714000171440181d4015014080c8102d4401c50310f21150f60a0110421030751107401500e0103954895030200703c4110342d00380c0040c4060700200e01d8944940318040c10784070040e8100d400b000005000c10a001c06803040d8028a0600c1c02c45034540292521030030341d00d6802414401403108001380c0741c00240c0c0240e00b2600103100c4155903544030b2079009654044680304a90380c001044942c103a407040398099141311926140e0045038004c588002c2001d020741d003009407001035005d42d43c40e0281c002044600425034480c60b68100c0200d65407000c0c0c41807504040c048869154a14018481400031903014001c1e80c1c0d011010804d480c010340d469040510801004100386049030000007011024000709400400487c0c0c0508402c041d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 201946061 1250 201944811 201944837
    0xa140102010c031103040303090201030e0a0309090c020a02031b01031808030a0605030606010504090e1e100612031e0212030702160b040e0f040c0b0415020606011107060c020d170703 80
    0x55401e84c422100841100300005030000e130084c0e015050b040c1c010302d00026440c558113640c0e4982419044141c001c82c81d400400c100d04000e5014002c400b1041d4400342840e1401d41c0d000c2656500e20315a10004502551041403081c8d10035030115620040200d03d000945089041a000d2540195203940400e42440000324003030800144090241406030b480f00d01d01480c0c2840c0384020081c881c0e600307049014000c14141072840d0316001600100c846c0007d41207004141c407000b412528035900051005940440300d001107504440201c2911001d09200030944082000c102d00f00241e1103e0b4403400c071004800c0c40041c41d0b00295140c1d82400c01516800704a07110115103104d401944291100c4284c240c001940790808481c2c51504030744079458a2510503180c0001c00f1407900b1a4012998100c800031011040503410400389401c40420300700a543c2a103030303429083d21855036000703410511070a84801411501c0d060140028142c011480344124080f080700c5144030380c4404d0b001e034001002511684 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 201947311 1250 201946061 201946067
    0x150f0f0c030c110619020d050103062304020105030c0304060e0d050306040b030a05060c0a09170102090406050108060915030a02270105010906020d0e0a0e1003060509030c120f07020a140102010c 85
    0x41c0c0040e00000b0001c07981c0b404402c08250070176107041401d81e070302403080308080081d41c01814080c600c1000f010034981400700380102600c80c480c601108800c8250309020150f600113085030380000d0380c102c1191b0380f6600c60802c000a083d0307030282642984120180718002580c01405140121800c5030144007030741c0b1140c01c0503520044101c1c0036100d0b40064001c28840490f61004042031420381c01d11071021542d500348107070b0060844003200541d940001c2c0c041e14a282c41d126480241200b42024129420b01001282c61080000e00e40090300006006944c26541c0c10454094165402840050514462261801800e40e461401490808004000f084640c028503c0702d054611030350051250201480044880c0c1ca64424180e400101e80341001c1454207481c03503160322034504d200c5400341c0245146040811910001c1808100750010f1004e46e03080000811121107072091103240b0340e114035206074003103494855850003c0d8490302c032000004480c58801548002e66600f40c00801481242005c15 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 201948561 1250 201947311 201947327
    0x1a070801060c0c230f041a0423010602030703020d03020a020c0108150a03060207060509030f07032703050d08240d020f0301061d0f010608041b03050f0f1002120103150f0f0c030c 78
    0x524940441f81c201d03208a420694084800f034801604e80381c00f082561040d5403035001003038009a00580002030707440141501006141d40254240c98110f14203804170000941b1007105003145810041c24201080814480144401c40110b00a00c01505a03a40e8902007009500c160740c00c0b1145820003000aa0340c0c9004000e41e1640603d644940e440c04820365130842e4200c1e8110346185942c40d0582c0441c80045411121102440c03281c8020299000c2c0d840300641540e800134003c0080d00300010341c2c0c101d84001035240c1c0e54201e000742d0f040d4494101c1c038030010742e0400207082d48903003540ca00072002500303600704004001544010051020141ca400115810180c024056180401c03440f401250000b0440071140162241c074550182b9015282e503900340c01c01c2d45203811803c0c2070740075200c400c40400040c096018100e00b520001c610709000d42c81d03103c0880074140320207401883c2407081500641c0e243d400c0950460001c0000300403850792085c040005103505081407000078903041c055008107005880d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 201949811 1250 201948561 201948581
    0xe03030f04030f061b030207110901060525021327080f0f13140a090e10020309030408010603080a090e0403090b03090a060504080301031a070801060c0c230f04 70
    0x10440c07405040d41c8030100c2207900c80e942100c1407682d900d0300b036890584410200030f40720155640541c0e54507490401d541142c0190303034068416203050004202c004d400c001121941e113655078030403124040071501d1244042d20310b00041d410003135850542c5040501c590040c4034021800210f800a205900051098100120002046481d0070007081c403090040c1005080c140c6610000945008c6661501c040041400d0780501c5203e2600c0f41110841c0c546190f44101503c018101089610744454203960780e0310118811020595000011a010100500454014116100c0280482c50303403071500c0080d80d0b000f440f12000044a201000c2900018107040b1030050b500340d55440000c83c00d00d0020f171800d0780041c003490245d1007442c0c070f0708001900d1401074074816400341400740d0320fa62460401080b0491036603000c00e04103290200300701003250070840c81d038103660300f42ca00724000140c1c03468248643d000c0c44d04811a030340412102884115000480c0d402d0041c010394201e03008001140c1031005903405080 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 201951061 1250 201949811 201949837
    0xc082508070506130b0d050f0601031505042c07060e2e0917030309010e01180f030207030602120412050307050d0b0a0905010e040605090c09041407080d09060e0303 72
    0x1c02961503c04054504007120b010608000d0f1381e5440f40d02c0f8107a00c41304e41c01c0301060301e900800c03140649100350103078011020708061006010510100c1c038041c00f180210391145c0d07580c40301180b601e170f5410b0307140d10b11038040700c40700540c4100001200d81c1c0e10810311840340041c2c030744000c3e20400d0030300010124120b8184860140503d010100850f0b840703009002c190200310300c01c0e000007110344481ca66800700f00341c0000a0b60340c03410800c40b05800d48440b070140000c3c9a0401a01c2d0f203204813408503101c102a0050580f0f8015000c40c40c04030f00701390755684081c24890010072109100d403540340742c042c044d45c4101c0c240010076080e007070305407001c0c0000ca58040c0850b405004400c3c400c2411340207414503c3c4011314101101d900c54807040112842a004591000c1565007003000b0040c0900c04d25070080b88150013080401104000035542d00c0000b00020511440c0180c600041102004803102501240341503601325900c0032001420255148610760001c1d200c0038041c11541404011a561651104 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 201952311 1250 201951061 201951073
    0xa0b0d03090e070e10030603020a2411030c0a121101090b0c070206070b070206180304050607080901030207051e070f120807080c01021612031a04050604090c082508 72
    0x5290992215402000041480313404500e4036000e9076800c0c182e24000026480000f00b550030360040c02003e110036040820b03014803c800c0c141c0160f600e07000407a90f00c070043c90040000c4541521030380c154000c0000c1c010191041c10001070400100e0700c2504120714040c0d6888a06800e0060010700340c032080360700a0548180200800c210030750110050041038000340066113804640d6075000e040368000c0711000b005821030424422904603801140f012180c422008504050825001400501c11040d00a1200c0030006080c80141d000f1b40680c1c00158020b801d0310081440c5e48400c48220500040201041c0980d030320104521004060a10a503420704540130392180007541c503164550300075803003500d0418041c80f100034104401d0000740000c0d030f4174011300e40303403c0a5494140da1607080b40d0343e10b90505023020401a40546044099501c881e0222808680c9031501c01c00b01e40100390ba94005072000d00c0d8084040b401001c000f50707824456003201c04004401102c640c20100584c0725010f030701d41c1500301c4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 201953561 1250 201952311 201952319
    0x402010f020a02090a0501060f1103041214010203190e010c0c0b040201030914010b030705010806030604060b040e0102040303030e0601080708030a031a09012340020a0203030a0b0d0309 81
    0x2888001060300311600490794020010703000a0013403081210070640507030305c070801404030360b601c1908484158414205000600c0384000b04980301c0c00fa50042c0c918840191551105008814a180000700008402199a424110120800c4031001a0b0450b14241810101e0305003c0051191400004140d51201140805981c0b02e0913105400b410581c101911004908041040010060082c9440c100002108828201498200540740e44180e0502850104115003030720f0201c0d0150b4403e034003441c002047c085640c0040c0050000072100d0b20158070101e404810903030141e106504052940044540c00d80e81d03031015941c1c1d048035020f214030030b400c00c1c070031100014040d030805180c81c00b8079106000038806410202c2d1800000741d10614041259401e40c985804610f40200b003803080603208a846240c691101115003c441e00c0c1240c000a800407102520f04140c0004034840854031b8015562131a40201c025a0303070300150f514030b040b58500740c1c0300740341c500c0c000d00c40390b072031070f9042d125803500602d8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 201954811 1250 201953561 201953567
    0x3020112020c030a02150a05041e0302070e07020c090a091e060e0105040b01260304050114070602070b0105090c090d120201140c0a0f0801030c0512070306060906060f0e09040201 78
    0x48180480c0419400b400300d9091410148050b0180400c5a0b0041c000c00c6e21100c5805400500503000c0d100441c0b82c242404040340302c1c11a00c5070310300004c25800386076200c1d40c5003c907d0950b40b41d01c0300e98040595010b000b081d55010070b00c03180c440011074041606032a0162010304894074468010142041c039210f0241031149000c2d18a0b006014260024248100b4079442d400c0d5001181c1c200c900940c408014804908004084600d8045044d0b8190038424007020040c2e50f40700302d004041c103008401902251122402085501842c0d000c0c20075900c412451500040c913100038046c0341d10510140c0d00180740310210109030740d15010b0040440032842d81c00d8881a41da00d19902110085548030b03a080387c004001e0042090080f24a62145540d40030107140062820996060b8001080849001040401c1c041c14044042e81c00c1180c4542200302c0c4011458a00101036100404c4141403000005488484d5480b10084544a440e12506054405012200207101d8589503900040c11400700340036500c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 201956061 1250 201954811 201954827
    0x108010c1805040c14030c0306040f0b0907051b070b07050f0a03050a0813050613030e030c090a020309030415050a08070e0d062c1608060408030703050c070804030f0228030201 77
    0x360b81e080143c0341d8080545e0110b1558800c03240310312841000814002d0320706151040e0500401d00340710412282142c140021110040034050700304000d800b0642c03403010118405030411001c190703070489035196514048580340740c0020700c0641c4c407406511700c03c10480c0c8010811898050745940d5a0b403614030607500036107540c40041e100780302179800c101c9402c0000d01c6c00c200e03c1d4040c1040b142c0b6107814089078600101085001c4141b14000e81000c0e89100b01901c030f01e240d0756080400c0c40000f40c2c03281d80b040c03140c6280d030083d903000d4044440340542e6200310303030f4204004098504c42c0d640e4840035695500000d488800000350b11a0304013424039a0800882c2c0d155201c00d000c00808427102010722500d0140c1541c000c241446894103420212402c01c5007092287c3c1c140051000c4800f4064030301e001d4845210600004107500113054503807001420f210b0404c400c4a01e481d500440c0141c81d661a401d080c0100c14100604074015100c120582c80b145a040b0341407200707680345009000c10103045a0044510390 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 201957311 1250 201956061 201956081
    0x30210020d09140a110301060f030f111005040609060e0d0303020a031401090605040e071a031e010312030509011e09030509090a020702010801150c30080108010c180504 74
    0x1503440d04401c00051401414440740340c5150000e25038040d103418051010300500184606c81e07898035004011401407441071030112a00850b088084840c80d0621011070000075041d80d90150042008983c5143c12901030800e03181107076141c441c2e1503261001640c821100d18112948843d00d840b8400000f07209400620710343d030203031a003c105864001d52115680c4002c2c0c0109030601d45840050149040521030b0305001c100c5c68001b4a01c0518299001c407504141d0f8110920002e0008001014019000300c0d20b0303d04515021b0510166a4034246550156481d00304800043d0070300020606010741401030394808055040300303200c180c2710404c100700145001c02085007409001d00041c80b0940d1060710300da1080d50302c00070159031000248001420014140c21640300e08504051084485a100709802c0307040707a0000c0410455082584500030751001c0050f01c115100c6103210483c40e4544c0030040d01c1c100c81e0104c0092011243c6d4a206447d0364480310b00c50726601c84896020845460180c012014203 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 201958561 1250 201957311 201957337
    0x60c02090a090c0803030115030213050913140c090f060a05010f1704060b04200301050603061309030f030b030f10022208030307180b0304060903021212041208010303021002 76
    0x300303443da4a400e54141d1030382c02411a600301100400201801c440f60100740441b601d41107142000b5400312010080460041078010b1a0100005240d503000c66002e690060b0410f80c3ea4600b845419519951106540f4a050082c05120003050a034045c031400680924402824080c40c035040c40c004541d94490010414101b108012010b9131030b01c4259040f90149000e0040800c405507032106000035151040e110510f00c00c00a05010754466103001500d040d1b5904440c690340d6501d0b0300001035400d00321250a500c040d132500e03212200b0160041c0c4501042203454406015290001080545039408201c0c000c1061b00000740840c1c4411340d65004110300c0c1c1c0180e0071031840d010f20845075002d111141c0c00400440d03200100b8411610f400c000414860203c00403074100346410074901e42d0050002a100078102d6403151019000c0500030b11403c82c401d201c3c0300e2015140d001030300c9460710869040c0e030152920320074440d4071900036100d410028180c0307030103400415459102c0340001000358032568680c036030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 201959811 1250 201958561 201958571
    0x408030708181f0309081e0c0706051911031e07020315010b07020103020d110c100e160320040e0a0b150102072c04080405030c030c030c010e0607060c0306080f0601060c02090a 77
    0x5800044520020f40b8a031500f06500d412523802032610b001125000201800014050000d00e1102020020f4000d420740c540b0201c00e2440b0102c070392640c040d400c6000c40701a900c00d00604d4150b0040080c2408a0080f02291520f120600c200991018217024000312030200700803100c099406900284a01c03441a500084c402c00d00c0d03a54080b0a40094400b031900340c000300700070f01c48003082d030262050f01c484c0700c00a85040042c024004034404c03000d120003030064141c0d04080d01c541116600958022502902c02e1258200584116486501443e81150b200d80c0c14404115085428008003a23a030f18103030020000030b82045540d10960300c045041a01000310300f0703074050401103402031540c043c80c401c100c101d85983c1000200740c2040c0c0a49003140c01b0340d0281841c0c8484d55400181007812403400c3c2855106a515440498141d1041120107090141000000320141d40e055122800b1100e0403401d035440c5190420f6069180d520a21074003001800e1201c201002d80b80c200c02c0c40e074210f1644000055 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 201961061 1250 201959811 201959827
    0x141e210906070807200a080f06040212010b0907050d0c030203040b0a0b030a140c011b0221071e06030c23030a09050d03060f15081303050408030708181f030908 70
    0x80161684050f007407049560060306403080c20046e0210b00075040702c001504540b80d11080190791003600402c080e2050100c600740c48032703079142944185108100640349852900e0030080c0900103034404440c1001d62890501445c00c01c80c401d01c01e8a0040790b001005c040341e500c40145c110080d1480e4140c0a905001d1074505900003002d075a00500415039000103400444255000501807141c850004160300d0502c5044400603a14095500a441645900c80440021804003217142108035000043d002ca01c100d81e4684d40071030702c1c0c0f524040300c00680c1e00303000380003443e901160314003140b56001c4401c00c050348129011706c0109000d150301120310b074000070b000c3d1b125440f00c80c0b41417101c0c5103460100c1d03034415040c818004d50701c00c11000340a003c20390440400780400300401c0c03208010118443d801c000300680c41050b11903411a00200b04050031280c4402031030030206900d91220110340c03200c074452605041d01c0e08003c0c00c00101000d140400700c16825001000394080c0802440454040e002004445 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 201962311 1250 201961061 201961073
    0x120c0c031c0501031104050103021f02010e10050114010504060504030f0f0c15080f070e0d02030709021909050a0b0904090c0503060a0911060c0613141e210906070807 73
    0x1080d41d41075503101003841d52550403c2c0040340400700c20709000e175080c20014805a11130415401500d0100d400b9180706804a0008a0042c080003401824038094010694402c11442e04201e059461010b403001800c410b5400644562249100f0b20340071031410700040000c2002105400481401910700d5020030b0465901c1e1400d4030000d401c00c6142d14214102c444a20340e120240c558801070323504480540d810b180a01070800c2c0d41c0043c24600c02c425403c4003030b0031900c05101c0741d002402000400d54503500c034200c00c0c2416a03041c19078400010f074064030028062a05904820440d9129031b04c0c50301e01601d500c2808003820840c1425650162103240008482d00c0803c20395210308090a00000e01d80034500d4245040c4111803030040c8515003e1044060070340e0702103030f02500072030004249500407025251400d100034500f40444c1c10380c05803940c0c0300725030700c0320800301c0a8a40003201540c0c41e0406d0100d101d60400c0400700c407000354040911821080f07080c05401040d902c1c0c0100c24490401c0a10f81c3c480b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 201963561 1250 201962311 201962347
    0x30406060b030a0e1009080405150906030a061e30020a060906030b06040b0406030504210e01080f15040509160b070221060604020d09060c180902120c0c03 68
    0x1c0500b41c1d42c10451138800c2041c0702000c500401c0580920440b00203071510815070145000b52881000b507000b0304a42c0c4000c600440d9071031000588075586914118251713000a017014481c513048000f440b4000b0041d090310045150a481c00c00f5054401c0c284c1c0140198484142c107207180c1441401040240c001d81c2d124401840180800d50b240944141040001815601d02150039801618284018009100c1038002e030780a94007a40750005581c4d84905050740e1281c0401c2c941c07801c11203a003080700d0802c5d0b40075000b00303078030602030700c0704580340c0c032103a40314482480c2c1201c962035005403038a812001440c003608600c2c0c01496602c2150701c200d4170361211404440d460344c4410140712001a1038003c6062103076814043d440c0c202460510180700600c0300b900c85c00002d0805110359400901120b0044490340020755164010314200590202d100740901951529080c800f01c000c40c0c0e20000031404014000c8600b8520b00c80c05070596910345001a100a800444403200d041c04184074180c20840d10703042c5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 201964811 1250 201963561 201963571
    0x60c0a090e2707060c060903020c06030f010501031802100f020c2d06070305121e040506060102120316140705011506110102040f0b0903011401061701050321030406060b03 75
    0x1c005540c9040302c01000111205001820700d58000c100c04010881c0c00402050585400100210ba400c1d11403604030700308040048034542c0803401100b440340a030070f42c0141c0b5058400c2a24108041c2103601c00d00c41d00c2c0b11810074000d50252519400300c0b0503a110b0b40f40d0744451099401142c90305004d010000341c98140d90040d1820100340c070f0b41c4141c3e64181804000f544001d0564440d03160100a86005102c0c0c451411489403400c550030114000c00c8c6041200340c482d032a400c0c0c80d50320b141814507125481e140e091311703030710b00500c1003c4142d404000c00c0307011a801750600300341c8110446d4441500b5642051940609a44071400f4880040840d5080c041d8210f00180444040c0c80141010005007081000c07191100355688140400c1c805040d80c0400c0d282940c01d14658a51252504800a8050205c401d22025980b00b4100001601c68004030398050744410852203032003586e00c03802030545e2000014001e4542c0b958001c00a400080100d00a40d00540916000325a054036201c001c0015030007990 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 201966061 1250 201964811 201964831
    0x70302130b010e0a0302060a110a05010c09030506071e033813050705030a0911030d0206100905040203030403140a060c020a120203031b1305030709050105120609060c0a090e 76
    0x10300c0c078005603400b068200100604603507202d18035055402040c054010b80c001c07881805005514100c2100c400c104062031142c0c03220007807240d002d01ca070b03004100d0f982d140320840d80703440703404081503100340030b94211800214140ca5801c040301400c507084006c0c00541240010f604568402840118540d604500c4100c401140c0030310580400000d02c044102c83c8000d5140442c078180c203002c10716034800110b81e00b180b100200804d1400441c1800a41d4040d0012440d43c90322a007014a04c11680200d0543c0c8200700c000302ea40070483d40e031040c06058030400c0318002e505410070002440019802c424080c4210441d078112030303540041d940c1d080202c401000101000d40c1c050072204003000320600800d0341c60082031025600354100010030a0500350407088640c0c1507440070a030f450085100d10f00bc2c900910004046501c00f039a100405002403801b801040e009409500445101c10000a0224001d001500042c801ca030faa550708021585c0054846000300051000001f80f4004908481805021010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 201967311 1250 201966061 201966071
    0xa0903080705030403020606010c08090402030f01050406050103020c0703021009120609020301050705070f030806031002040f0f09052806090f0203090c01020706020703031103040905010f090b0303071502090307030213 95
    0x414040c00045004003401d0401800300704020000c0e5000c00c070990810b17020300b0480c100c19071500c0c14600c41d0107181091a009031020040049901d40c14103458129102a90200708413903e4000441c1070b442042d001c5d100c43c1d40442c40410044c206117502c204407926500e0084086912140e065403100033301d01060b2002a10b03003c06105501c0c0030711600e6008040c505240e8604001a07443c9400c0340341d07280c806401c2c084040300282c00e64405108017040040c1c1d100c400c5580701d44800320303c0c80c80880ca0007803464002e030124011441e0403c034072500d4020900e03090074140822842080403108001c0701d04031010103499040c0041c1ca100a80a80300c0d2030340c002c003800341e201c2c5809001140b800d100380951134115404101c00308401500420b410342903070341501c1c2c4200c1e04e1300e1003210249540705580c0051202440d22000040c803a40020b9607109407895048180302001050041503943d006210303000d48944007560112816007655402802000c0b13002d425940200e43d00c0e0005a9921000c417441d4900036150 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 201968561 1250 201967311 201967313
    0xb130c03050609150f0c1e031e0a0905061306060b040312030e070b090103020c0c031e10020a020c010c03031b05030a0605180c07020a0f0914060103020a020d12090b0a09 74
    0x18440c0c009143e540d000341300014581014146001880904003ca55000003d00803507031811181e1660302422102d06960b613079007040800740e941040001240514000320070086507100d48103006010403590400000c0c41d480d1101c1d8446106810003000440f103240c0e486400007030b000c140e0f002400065000d055441041c08840901400740c510340f03405000c00d1f030000d007000e020f0180c001d000e54194040130310780162280f051554491420b84c100008035410300c1407491025083c04440001d0340b00e101d0110580d0780d48104131b500402030340201074011001d60006a8854a554850580702110034040e16012a40000034120190f041e0340c05650307400060000010040004002d0040100900c01552418141c10885028605500e4003030b10303a42c50b00500041180541d516868074202520080f0000780c255503903050441c0050412030000f000841090700040c0c902d600074800c2e00d222100d2600580f4140244410031109407005851248030340750350382c01c0c0c10003041c00d0380320729840f420300400b0020301030b945 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 201969811 1250 201968561 201968563
    0x19060218010e0a061b061107050c01050c06060f150a030606090f0503031b011d15010f050919110406180e061c060902040513020405010b0a0203070b130c03050609 71
    0xe500d000350306000e05845001d260b51500c0c0d0030b08003221550b28011410781c4e4910301100c9240410f601c060051401d001d40490351021040080c0041403247c1c080303031081448180192542c1c01114042c501c0d94000b00002002c40c100600495000f03800201444c0c117454480000030b010b40c0018101ca80001da44103018041d041d04280c450003c1c00340801c00709401440c3c080007c0c2e40b407041590004904a140094440c5c50000750440407000c040c042c501c1c441d1f60290000d1503603030301d842c40c000004c0070000d44c000908252540c41c02d005032070b4007a00440d030a80d95403000300c8850745d01728488000c2c81e0341d82060841006140c40500041d000e030f99581c440035600a10100c0c4e140318140c02032130408220b142841f01c0b96039080c40c450003074000e1014030308282c11582822b20040c55442d102a400c1070404042185034401d41900c03002c843e100711820071490b600e070a2600164050004c40c800580d00420500000c100d40700038440d0721490500010071821625aa2010a868241d0086480d544040103000134400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 201971061 1250 201969811 201969847
    0x20a0e01090506130909050a0c060c2a030b13020306011503060e010605070201120b0904080c0f060103030e061b0a050303040c140f0637030f020705100c02190602 71
    0x80701d26504001e810044d00701d4003241d505c04c20b8181a0b4800d680b008106090003400c2900c2c1d003000001007259520725028103060405401100e4018040701c58000d60312011081c10701d080350100302c4055250460351000c2c8482d0015000101a40b103241d40324006076010444c01c4d010b800e80706a0701440d5100240d0103010b0f600326820140740c006281e030050001c80d500c02c0a23610015024a428018014800003010041c89843c2003181c010321440108800e0045100082000c403003d80d04541c080182c141c01c0f02e0301d0b00001e02009002422000074250309241500203405110600b1441a400e6901d014503d0b10b0620251400c407060f4201008000600400641080050082e401c2c00c404070a09c01c400129643c40c43c9c0540c0780300300d1001c1801c1c0811518044205010f035822818a4203400030410f840c031604404401e00340c0001c0c10b01290701490040d500a031080035501c10024460300000c2c04500000e000113228140840c489c00e40e80e000300d10507052034845614020300c2d0040c1e5401c41e030300c08400645 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 201972311 1250 201971061 201971069
    0x903010b0409110f060f0307050310060503060310050c04120b040b060d120c03201f0207030509040b040b100306030c0b030603100b0a12032a0b2404020a0e0109 70
    0x1440d00c42c55101040521000a403007040440b85612100d60802c0090b030503004280d46580c0c402004410070200d150040c0045006100c43c0c403298a80c2a81d030402202c003032108903401d41e0580c03c22038603074850391100c0d017009800005200e156420a46c0f18100215014018041030754090403170000d02051180c114000e40d04040f080d1307080c007480800c1ea1030b5283c000d480346d4101410070964899801c01d141c030500103900740907001c40500c01c080382c1d80c220f4195120344070111064a00c552806903426940f9034800c1300c1142d0f52588403141082c1902e8200001000c0222001380c000c4d80322440c05502d640d0b041117000c011240d82c0c50004255046082c01580c03107410741c2110144210800500680b9503001851f9001031855080c00300d40300c00036101040003504640d006198000840400c1410503130003050500b01100c0355000d0304403200510541210140b4896005464000e1850102e045000164808041c81c6664020000b000b00881c011904903446224150300081103202180250369100130040014 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 201973561 1250 201972311 201972319
    0xc0a0f0608010b07020a12050c040c0f021e011103040b0a0501060c0807120c2f040c0e010f02011113090b0f03100902030a020607030503090609160b0904200903010b 72
    0x105090090207000c642040c000c004009401044010442d50703600d10f030001921a05101d20301000c030364a0510b588011520b0014030460500c1e0041e04124403802241901c00d144e0b900070072401000307030f000c0d0440e00e94031080481c1554a0745c0101140c3c0c09000020740c01203106000c401d4403480c00100d0402220b4041e003105040051241510020079140010b541559070001690102c3c1c14180740c0070741300c040007140024050003040ca0311032200b03114610301010300040c5a40c00c4a100c000281000221119003031510007052070a1480055540314214669800000340000a0040030503184c4a00c907400c80d11101906140c100c43c1405005408e00850000f00d000303903110488006080006074840c1c0e0018845813040d60b82e00d000c1019550100080102941c024040c00d54540007030500903c00da0003140d05103034a10801e404240c07031010002d000484000d03000f1020881d5070502c03440491a501507021720f544a52241e0004940b15a54068003e014207034002041c0d541d44040145801e40c2d0420303501c1481 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 201974811 1250 201973561 201973589
    0x81e03180f0d14070b07020f1501080303070c1703010f0513050f0417071505010314060106022e18020319020f0f010219050d021912030e0c0d03020c0a 66
    0x41c000c0c000035456503014040c28410041649403011903003d0003020005480f4203410350500c401c07950041101070080344040c0c2600c1c403001c00200a4480000284106c0246a05c2000010b031190312801000c11200d02c0f4110b012200040712004140e1798200780c0012581d0525410200190b24100d48070300c0711000281d9082c04203152126518501d440300400c0501121018540200c00e101da15048035861503100b450ba51140020f080a0030041009010072601c040030442880031a43c00010b18034120303031942e80142503242030341c8a0b0a00b042c4140c80e01c02c00d8141d55504116042d00a40100c240c0244170061416030501140101440e0100e20701d800480300c0407090540c0090b848032a10200720320800e50380c5c1c2080b0b401c4030340101c0c50f0622055010800030902c0d040c2908114000c00c5504080141da070845021010101108030035810040c401403089811110510301c0074060741040d080c0030010001e8070000d4404801182100e048004114010b8008406003100c510308881220040e06201211081c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 201976061 1250 201974811 201974833
    0x90a0605041e0e15040e01060308091005070519031e020307060605010509280e01030506090c03010b061204050703140d030e0f0307030c060e010f02030a0c020127081e0318 75
    0x1c4041c3c0a00104202e50f546180c4102d50b40b52500702a860414880080000300da6908106035a900002d24040c81001484140a0420310a9082c0c4103402c0d00705000d054000001040c141d405180301100f1400c2c4520b1501070141c5050441c00c520504181e0b401850b81c80e5603529001c003c8034940e800041c10b002050050300c860f40c942c00420584600c2d03200c08004911a40c01d00000540081c0c2e1040d030003822540004820400003203085802740f04854100c51a0002e4201010b080e60304070826640c20040510520218410369510182c015000d00300743c84030b82e9100e840e0355a581c546080d50220030751081441c603000035814810f40c62800150740c00b4200c1c422800300025140d00c100b080180420000c0d0030350005100c4183d000301c0c01c8031400b00080050360442c07110b0074065003040360b240c501203141041040c80b460040c041c40c106079034146a00c21030140500c95101e40324219030740595402c8020b0015001c10901d044280000302c40041e48c8035100c0c5014400d07142050200b003540e00301c580103440c1090b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 201977311 1250 201976061 201976079
    0xb0f040504080d020703030e0703081e070b0402061b0109080c0f1c0809031c0603060b0f0901060302030c07050307051b0a06050306101e1d1002071a090a0605041e 71
    0x8510a03c10480035a59404030b08007100505111940790034a405622800410403800100400714103002c81c0400c0464100920010103e01848401034510f007221400100140b9020300101542ca0607800070082e101c031000381c250708484140e081100d4a030340c000380440c24000704000800e40d4017100342c010215603202e031807080001d070a240d06c0b4409211031080410202c0c00309000b0f80381e06062a005001e035030300800c00d0082c00340c45107100580300e1903d400c503c2019400c21103014410b00300050154251a4a0200e04070002c0d4001400002028404e00c00c03140010310a2004180c1240180000c020b0b9443c0c07c0d02441a6140c076203d154030400585404000c0c3c945c206090b2540154121a080f040e4a81444141ca0f0b1409091011020040c101c25030203a15070003401c807070154003800085012308444201407101d00284881e6400259100030702c00c000480c0c2c0107512443c00c0e211804c0745801c0500001c00701e0024a403030f41007a008079030042001e00800d500c00c1d0020fa00d00c03540f01d07128240c80d85040e0f420 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 201978417 1106 201977311 201977317
    0x2010507080106110312040516030507030c0b090a1a1201081507141602060706140115090f06050901020f07060201061a030106020c061e07060b0f04050408 68
    0x490702512491300302100040344c0f00114035084503d07881a88203440140111040d206002a14a40b00c0a5148540065110303600910ae51030451400180d52229a007102880c01300500c10b0314070560b01d4251000880b1446040c0c030300803948c183e030603100790f1181061160303c405a60b000001c044100082d240c0c101c0c82d65444180140d19801002c4030940300440c0c214642c02d00c188001004d6503420803000164602c0108007501d400090340c0d80000740c07402203880f07000e074030544001000300c110000290500a00e081c54801c80e00760074001884e904000a008140c00c2080128208603036034001c10a054500e250a8100d0300d28550700c0c48028084d11841c0600305417029204041358107210590f040d00e041e00c201782c014200040490043c4030054000601c401c8003000c0c12906030340b403952a00300505080c3e010303800205450320311909005c003956040a00601491030a010440401c04407825 = true := by decide +kernel

theorem cover : BRFrame.Cov 201798561 201978417 := by
  have h0 := BRFrame.cov_init 201798561
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201798561 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 201798561 ≤ n) (h2 : n < 201978417) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
