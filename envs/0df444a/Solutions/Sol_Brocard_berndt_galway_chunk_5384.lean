-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5384
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:41:38.316797+00:00
-- url     : https://prove2.me/submissions/544b7906-73e8-4f09-80fa-0a04b52b77ed

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 968165467 ≤ n < 968345323 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 968166717 1250 968165467 968165479
    0x60c020319180e0c1207090807030b060103110c0105060108090a0f12020c121606050a0c02090a021e04090c032901140c0a171806030a090203010606020a0302010b010806 74
    0x800c0004480241c80052540c02c003540081d8089104520200c00b640710341c1104500fa900c9003240c4c50741c0e590280f4007034140390601500d650b062200034004500715090300d410250f5a44287c4031240120000c00100340b605010410108200480c1001034100c140903c400741e0715004907132682c03180d003500d8140540c0d000380702500d041c280c0310010f003c500c01e1890850b0980180d5100304140400300e5900b01400044c001d030b980110359100014450840c0801c09401700f894054200100f52030b016021400340500039200f05145c1d800590f5403581501100da010350076000c0d012005000300e4000f0815006801001c40c183d04081c403d0b926144688110880c0c91910401c0e04030300b820206103105c034110b2080d0481c0c10451400440c5507581c0c4c1c90750040c08003400050003010301a4981c2000d03a5070070124002c8541c0002c0c02c010604020b5503809810041c04000caa0f925500c0c4c80760060f4000070607403080300035050b5080040000b213503900450107d01d00c0b402900240b1201403d48011180c41600b140c6595000c4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 968167967 1250 968166717 968166757
    0x303050a0c090e22031112070807060e100204120624061202120403080f160f05090105120106050417030310030b090307020415181b261003060c0203 65
    0x290018240364100780320f084c80480400c080804071400c450300050550118000c03c82c1c01d811440200003007050010601d002500b480340710f60f1081550b2051120281025841d5182e104c002c1e10240540b5069040080d82190303241e03507402d05908031801c03081c015501d0602d0a09401d0900f02648001e083c15412081e800d4038103800c2c48002d840f101d00100e40e075404940e0906c4424081c19440c0e00300d80c042ca000340c9441c141803500ea00604030000000f0203428100d082e05030035106083c0c200b9012682a10103060042e102c3c0e8801c001240e545c0224a2408010a405400010000e41050003442901c500191a503281c0010150103603a80c4401d1703a2501e0354244025040000c42c1c46600025088404101540c0c07400700d403500000d083d11440f03051290074035003003c000c106400800110000183d1005002c0c00140603960018009400c4502d507101402200c4034944520040c0e102000451701d001288034400c0e0820b00c001030460100c60000702c603180d1801d00c881000b540008180c0b50700c81d2907400310f05c24131 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 968169217 1250 968167967 968167979
    0x30c1803061e02030a020403060b010507021003050c07051e010b121f02091906030e0d020712061b05040602100506061b0709090305070b010909050709090507120f0303050a0c09 77
    0x500010410b1201d20440803010030303a42d021030000b5401410350600150300c49040d400c2240440e4050400141440030811100e40181c440e0b484510b0821911309000416968150a40303260b88900200140a8021660074192050b114800d8884003130303100001300440201501400304400c0d5075680403201ea07101b204540c051441010150b03d1010611801500b03040f410310114400b480060758002060201c0b040a104095241c4164018022120002d110084015001035202c0c0814010101103415040d84d913010f01000da0031074543d075110807400e20806420084001c25503041801003c00500880d0a80a0214094020b40303000e0f100040c0358600e00010301c0d0244003929205c02604074940501d00c000034412510b4031818407124001e4a80907a11500d40c40c00702031111050300100503451a01c00044080b500010350081a580350031070024800000f424100d14001441c0d100914502240000340300b0001030748005101240f003900c0602880d19600004001d5a0b07440004a001541c4030f03c0030061 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 968170467 1250 968169217 968169221
    0x15030503031506130b0316090b1e0918040c090903050301060e180702010b091803071202030409051008060a0c080c090a05090703140c0313021017070807030c180306 72
    0xc4200401d031a2404800c001c406101c213101d035202c41903610010040280603942c54030005078030403d502d000c420340d03030400c4060169401540d50032000816890400b40341032404400f2605810070080942c05481c040d00f0524010600407201200d0528031035400191100d114028401c41c15407603280c00c1c0c2980e0910384119040141040c40c1540300300001d0254280c2c501015660380219640d600205400300b4a07003c1c452400400340661740c044001011900e003080003c0f050b1254107511243c60141c0118a040c12844d50085402242c0340b14580010f10141141080f855000c840b102d8064802582d118100718003110305c1d20581d00b010401400c0060100c0807070900401c83c80310006c2000f1384140c1c0300d4000c01c94540301125081e020940ea01d04510281c40000c503502c1c0c0c0114128945032941c0352420306011440c10440009004000300310902c0c40c085d000d5010f8141001060074010303894546600020940301003a100400400c2c601031200f08502d1064545088040a000c0f0a030805481d555031600 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 968171717 1250 968170467 968170501
    0x1060510111c020c1e0a050a1a030c0705061314061005060d11130512070810021308010e0d0906090f03020904050c130902040b0f010e040911030a0f061503050303 71
    0x441c064003122050b40c0c0d8807402c8080031520344070455080d8031500c05c18040c0303a8109800c0350740b24180e640010800031854100080400ca50000c0300c0e902c940760700204200a00400d14000c182d030044000b0400c040604c1c8400c500140d01030410300b00100e906000081d100c1d101560240c2204100a40502690920354028032442e400950001100c030040000300200303410081000c000904080004c000500c0c0c001110862140c00b00c0141c0000340c03034030341002d40d100f904880e00c002d40e0b40c020400244805013070105074028548180207000d42c0c042600e13000c1d1964170311015180850003000c40800d000303208400349802d6544c121800f40001e800c42d020030070301150080044815214481a0b0080c0740c0710350322203248510800c4004202106184108001c0c0c0b0054060140140c00040f03030004143c1e0300c1034403011600c0d410760380001d0002c0f107400c0240a41c0d8141c0c0c0303000e0f003602c01c04100c00c08000340b4104500c2454022001040100041504600d05402c0d5220250003a4424804079440302500f2507003031 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 968172967 1250 968171717 968171773
    0xa020f150c120405100212100602121606020918100801050910181a0403030609020a1b051501121a040302031c0e060f192d09140106051011 61
    0xb0300010001d41500d07050740c0c40480c3c03c0c0e58041030501404007144c04508c0e544064000c07400940401104098804824000c500e02c1c00301da605420b41502c203005055040707034a03022003c1c1000c02281480c252034075460f0010b9595a0300340400303000c0000e40090621515000704074035409403c0e11a003c40d001c502420300b01150509090100d981c1c040056a000c81d0741c01e18071441542c110051505040203002c5440a030b00030300c02280100a01007506500c16840c4160444108241c2c6001200b41003191414040307007054213102000000101da4284d0390004256518810314101e980301c2110200e802e00c4400a8070300030b001d64014130100d280e0080c600c02503000480701290015810200c1c0140034580141602c0601d0b01c04504400d1003402d01c1170b07031283e43d01c6030b032884000d100d00e00c0c2840d1902c04103445007074400c140e242e50342c032034898014080c0c0000802070741050b40117640300b6010029030b008104a102d10b620840549241203070842c091503203040d40304c1003840500b443c002030a04c0d419002d4840400b00c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 968174217 1250 968172967 968172973
    0x3050f0d0b3a110406060e090708090a080c100c110d0908070b090d080d0f0c030c170702010e0a200a03030813060618050a151206150b0a020f150c120405 67
    0x40501600c13107219000041040d51780b40c0c41800402801d0010f6104040c1805c02040011020040c201c4800100c8500c9503a00441c09690b800355250b1075400e1081e00440125400d0402d04d4403c01c1c2c0d5844104c003028980c020090f104c82e0003200740c1c292070300c0103030780f05c1e00d80c068101d008100f0168142c08003a110ba140080d108002003609540c56120a80c008842d190300c9983d5100810359409040c4a030001001c80c45c1003c005802d40b010020b0302c80301162070907030600400303c2c0018820620039004400340080020882e01c5820003441d03d5880c107c203445a600200300a24018026442d1100d5980103c0360591240c9811346c0310101342030410080050140c81007904d80784001210703240c000100c540c003212500300140314200510420290741089040010704442c111041c04100d1a090018020640c0280e000400c0900c51098008036901907210555060010801c14181c1d40c021815130010010071003a104140d045084507042c0c002c00361540d407650a014050004d403852101d145641040c010021 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 968175467 1250 968174217 968174243
    0x409060603050d0f080132010516030e090a02040f0308070f020607032c10030902030f0328030606050406031518060603060506030402100c03050f0d0b3a 67
    0x6440e2502164807940c0380007960401c2c070008250345c003c1c681405405a00d0f061281c549240103003445520310146080b0500382c03075040c1c14820341c0c0141d088a0808030846240500c8a4490401a100f503e5841c022406103003481c0006584810394802c136030668001c80030314844541941c807584205d4201c1402260100c0d400303a45480507a40d900042c081f0a4407907580e600040350f401180b41840700380c1c401c95070303c42c8050405202450383c9190007152010158075001401c6002400001d103080c1680099100e2800002400ca000e0803034003111407001480100516000002900110201c0340244106e500042c014401800740c2c501c243c0140281141342c0300e04c001440c2d00c41000e50b00964060b0009141da41c0d8512040200720b03050b0152000422044400b6411442c25401280002200a02881c00c100000014908240c0120700381c0b0341000401000075180d4401140004c018144010064852040a440c4e0380e00360b61075800002c3c98510214070200720340ca2408041112111241d8200c4001c908451 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 968176717 1250 968175467 968175473
    0x30515130f0311010615020d020a110f0301110a030c0f0207030506281b03060f050a12031b1b0b160303021605030f0301030b130c03020f13140106020f030403110409060603 75
    0x1400d40501b500b2050b46003000025400a8a044885680715082d03421107a01903001c81d44c8903030800c01112040c0c1c0c1c280040702501000a00500104406880c0d070302c400301d48003062a80c503510900aa02150b26001070f4282c0c2d54005070780d02c00f0244030050550303020340002101402c5003401c5100c90000c00720b00c0c4c40070b01d0000c2e11100c1926041c01d00060040381140b008800305034980503a8008041c0400450034072800d00010411040f41c81c043c4442d615240e01000081601c5404480b0b40c0d4400800d54030b820070b0440c0744c0309503c0b1211411846032032031860404100e8141041c203d84003600c810003c560000314554042d4041e4020600f43d03503112140c0e4244002180003440204803203405051903035920760440c44c1001401502404043c104803001103800d001501c80c0000e072007940c5d0116507810281c1002c400260700c6101d41c0c0e0703001d204a800e1900003070b1120040c0700c5c2d4606036512902a20781000e1f1f0040e0095490040c0d2102078081e01c1c01880002441c202507010307880c410300518000c10007035100c0e2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 968177967 1250 968176717 968176721
    0x1217070209090f10020f04050441070314060f010e030717061302100806040603081c1121060a080102070b0f07031503060b01121104030515130f031101 66
    0xa5400c50b840e04032120b0300c000d444040c004c4520100900c00d0840c100500d004100752540200c2c080c05000f030382c3e1904410000c400f8894105c6446c14030a480c0f40e407102590100e405100498420001b1604c110343c04100724074000c0c002d100c3e004480200428056440310100704501020041c041e0500c80140940161902d06000c4400a000c034900d500d0f2180940b040e00700d01d440750090201c02c0e00100346c1010030060b644d4221045900b0007905c0c001042c3e0725030384000f4008016a40c402071035403e0008616100500012054104c080b1402080060900d90307043c2020520842441054038940320f00c5410842201d2840c9581011001e82135841c4203071500750a43c03ca911861068400c070b0210710400c07102600f2620200c3d03200d541842e0074080036101c0221103004c800030b03000003424503480382865006079101b02c044900c1c0203031000041c40700b0042c04c010030741164006d01065a1390301450703100308951030310100124012110400c805410048a444d0b0360013110000808408000f055001c1c4800e6001c24 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 968179217 1250 968177967 968177971
    0xd050903180d021309140118050c030a0c0e0a141303030c09030b1602030d020c0312010b16031407200a050f1302160c140f09040302151005062109071217070209 70
    0x41410704482680b681411850000c8001c2b64510a91103506c0f008001901020403008130b50031008144165220b141200f0040c044070000303006201040001c225088840c400c02c00c041c14040c3d10200406005a20f086030400c0040c00040d041308009804503000c0c01055070b070441035003024419203042c0348522407008140c0e801514217070741b02d51000c2071800c0f64281418545004151450300301e407800756030120400340e03250500006070a1000301054082c2031a6000202d4444070740c00301050b51038007042c2d07031000070b00d4160a02980c01005404004212400d0040340b2802100000b0300000002550b001a079019501041000c2a64034600f81410300264280c00c2000240c00c040c640c149101880300c0a010040343c1c54409107100f090002c3c1804040f9070017007520491030682030b00d0210680c1c2d510321440180e1400354040c80e0000300c00102c10b00c131200149005004100d0281c134903901502c0700300d54655560b91030b00401822072111a4094000b4000c1c4603080d201e0380814032002c0c184459500080e0b044401 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 968180467 1250 968179217 968179241
    0x10e061809100e0c1207050711030609010606030f20070507050607050f01050c07020f091f0305060133050a200c090601030614010e060d050903180d0213091401 70
    0x4110090201e600d43d0706200ea800f0201c003611604085410311880055400a03002100303000c40041d0340403d0000c1107414034000304024080320a02d040038508140241400c1c0700d040c00003482e2185002d40030300e10f4040d1682d0481009000f810b444098000440143e2110307108803180c0c80754502c002215243c08003e00800c501550148c10310300030003030103142911b000604480300c6103402c01651005a07500381d118100030100356617108184d5610a2034030704d80274510142404243c10480c00000308080014002c2c142c40380011100d0b00400c41c4c0d0024801c080c014400700c1241d06510301c40c400220312680250140e1000c51030888041003040e007240c2660b800210360740c4c030a500491400344140c1802c581454000d41c1c286000c11419150411001640c07502c000140c1c1000510081c2003916502c0350107659000fa5440c1c4104628100005090307500e9000c1001102680041150120689041191465850f401034809004e41c26500d039424000c1c0041401280c042a9007514101c810300d00344903800c91481 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 968181717 1250 968180467 968180491
    0x150519080604030c031701030314092806020c06090114030a0b0607030804050129040b1206100509130312020705031201030b010513020f04090203180114071d010e061809 74
    0x4c2c40d08000700b5a07401c000d520024251400010400a5404001d4100c2c82d0850103905031a047da1000080c03c038103898040c02c000501083c0c5498904000c081220225000c42e000c560b00d9990f040103206680c0070302e001290228083d843c0300d00f01410305000441c0e0011520000103218042070000808030f4110b87c01c1600010306000402080000910070303894030b41608902c440550b90681400296440c812101c140100c0d2030b1140403d1030784503d20900700c159041d0066500b9450304141c0b03840f4410517445600c0c0705420341c50110307801134840c07000c150100c1e4040d0346074030a41c502d59014502070351202d1003c6423203100c200180c500d5140c1c40900c144c040c500c6100c007102c06525060030844800b0480180301c0843d44104805c5000e030b11311108860880d85c6143c17000da1203a80e10050f01d046903541c80e0400080d5400c1c511450b0b2042015403c052247c5103584848140da6240007400502090b03240e0f4603804101e610100c280585402806032480c14407200000286000b000c012403a00c0105442c000e00e103203 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 968182967 1250 968181717 968181737
    0xa080a0908011b1409060309010510060f020616050f0a030e071a0d1107290f0601080f0a0213140f040e120c0a02040207031706030115051908060403 65
    0x6501905103001000950000d101006201c004007400c80c0c103952240052000e81c03e03120103c4003000c0c081d03074828500200340c2620780c0707003d504c41c5000c0d1004071810301c0000d10741ca00102d9400e00803014503034410782a40c02030141d03135591120000c25215011480f02401400e0140c65001c0c548030001703100d05105030350080350700b1800a0b4201c2c035203006504619164400d4200e200741d54000c1800343d034486580c42c207010903a1400841490410b20568202801800d200040910400417484000c0100f00c0c4600c84c40302281c0d90000e0112a0b2a8152a02070004039100c0100c0c2c9000b940d15011a0098540c8070700602c0c000103405400b4007190940d00c050340071003059000030200c0c90030088a5030300040a540500044514492190300e03040041c84074500400040741c0c01960400800054400720b40c040c0c01150381ea1a142000350008041d802826503103040a00020800c1c203040c0541d100c81e4040f8100b4003802c0d41040108036202d200d500da010f41034604c1000018440304204002030003940681c44102c500 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 968184217 1250 968182967 968182987
    0xe1e1302030f072d0504060f080d0e0a0e06040e0105070e03120f03011205010b130222140409020f090408220b0418020d060b0405100c050607031d0a08 66
    0x6248102c455506400201c0308100319003100c2c0f0b10314080c0a030758501c80d146080b1400034011014a0b03030411a0001c6c601138005c600741d4038040c004810384000b0b008840d4400c0a040080f1402c92000322940d400c1601d0f10420405074011280380d58010030000d001041048401c0c0c1d102d8210380b02119070800085120445140034202030100c10030088002d00d0381c40c40c1003008051142248410311814090440105040d02480001c1d4010a813070b48e0001c000d2080c44651408400c0a5008110103020078520410340c501048130715030364841111503c0e5070104004c90b12404010090000510581e003000c1060b03030f00a842d03558200303e54404d511175404c550b10341c4c4150368100700346010341c1f09400c1036003902c1c94184440178020050320103c07105c140f8040101c0c001c0b0030302a00607001c0c64484506050418102050700407094020340241d80b425a400006410050001c5500c65082e480c0079200303400010104549500c260048007001d200b1210704001300a40100c8140703440c000681c19114604082030380060 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 968185467 1250 968184217 968184223
    0x507110d0b0412030e121207020f061f1e0501080a1d0f120301030b0c131e06020c01030903050405060304020604080f0f1b03060f0907090f150501020a0b010e1e130203 73
    0xc0e42400700010520004c440c6d00328034291003811100d00d200103440c00007402d128400c028400c0380326900c209803625800c0490300e001041402000c5000362103c0c2c010089a582d000c0c8004150b10034005283d0524603241100640360700c0009024203129903103682c006c500044100241e08a50f05803400203014180305008110b0621031501d03030700034020a08000410205958078001500701c4111004250743d001c1d414185d000c051003940c08840c0c03001e0b10a881031010741140e045542156202e400f0f903070300e21080380d0044040720b030031000c0100814010300082c401420100051039116101074240c0f8600350b1a4400b02d46011042c0394200556808203030215541117041c00280102e8180341d01510341503081c040007a449020090950903040c2980c030000781c0c2000c003008048000c084807001040494080c29001d009481020f5051302d01014420001506510003d1400e821075002103100318640d080940303049081e000a0000440652446c0c44034402c0b04d0f0000f101070080c03d0600c2c1c0f00b4072501c082c0c814142 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 968186717 1250 968185467 968185481
    0xc030a02150a110307030c03090c120209090327060403050f070f0f030b040204090204200a0314101503090506070c050c300f060702071a0a0507110d0b041203 69
    0x40843c01c000386107510b90441c1081c1d0340c202405003400704107000c1c3c0c0d440842c018529080c02811085648034001039504200001059070341c02a45c000500c3e51b265210195240700e000708020b000004180c9030f02a540014a6501c140d10004080ca440c0c607689031111441c0080c081d07050b101c6a0080308041020030003007030b076410007000c0c0744400040f0030b490341d207508506444c010b1000e8010b584031000d02d011507139503902c207032011403072800d100800e00d90303501909130340360020002c1d10042841c10010551101c0e40103019403003181ca140301000360f207081014049100c0c4100782d0703450a050700c070020440041c0341404014480d05003940e0780940c101c0c4506003075140100e8a211240038001c0c110002aa1041c1d8481d1810820b0300d4a0360041c00c10001c0c000c0c079150403010011130b1940d019020610071340da580403480400b142d144817110003902c0850083c0c091640700b02648480842c0d010007030781002480c08400c00d802c1040080581040b00017039241c1c0019001c0444084076009400e03030203142c1068042c4100c607 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 968187967 1250 968186717 968186731
    0x4050411040513090f080a18030b0117161205071d06101110020306060405030a08091014121005060304141006030c0b07060207022e0e13110c030a0215 66
    0x2c0a0425140c40d10420031400d19800b03401c1b1383c2c0c00550503100c1c0340200492101040603030352041116a503400d15811f00b220a005d10303a00f00381448441c400c0044006009030080e01080425840545000300c02100b4129406e0700311458009c121300002c0c0009a841c419081c02e11000714a000340c5007203002c02a049503040c50207010312005038801000000c0c0088c4c821000b400f502c10040e5039482d0800010441d0003154070040d0b062003401e880e4402c00c60070b81d0140c84010030545001846103c000b6054035a110340640f0f20240313000500012800340c0700da02c9400e4002d03507840c9000410a440c1e10206034580e20172501078034003e80d005004444011308100b01548415500810404103045a551a984010510441a200c40d0116106052190a9044403003869009094120f90a8000101c880c800a6002c0203080c2003052000c068495000f00d0038804602c00040c0444014031000070030714011304801a0382074014109102d2a030030300c44200004c0200e42d01c15001480b0400d01d20f5003500100000030144 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 968189217 1250 968187967 968187971
    0x5031507050d0b040b030a0c030215041a0310090c0e01021c020717011b08190231080d18080f031902240406051509070c0804050411040513 61
    0x440c00c0d07401002d486200c000307140c021600703540d0440001d003e0040b030210780c1d6050050203501c0081140d0102840c0459109486003103400e1400541c405090186101759036101d40b001500014401051009540c804640c55000c0c841940b00d0790b900c02200c0c5c5841604002c2245180d40d10215a01004092100a04041122414062000020b40310031482c45403070300244964101402400c400e410070010b902050381344101d5010602001000c5050580303e900b151143d2101100014241d402212001c400e504443e070040c0c011780407000707101c582e80290191009283c6901141c200014030150032a0b1005030340e442d09200101c40107482c0d06800c0d0740075042a034005c80c4100102d100200655407902004501c100305c0b07152042050b802c03c980700a1080615600500d100042400c130b6001500440c010301c2c1c01c04c003582d20000c861107036080e581041540041d40c4800110074611900040b408584529040c80c14240e0303980204040d04c40c65420890700e0326001c1024400d03810035004001c0d5035400c001e41 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 968190467 1250 968189217 968189221
    0xa0b120703111903050303070903140a050d05070204091a0a0617070303050c120d090b09060709050f030c040912080601090b030f0601030912020f060117030d0509160e01050315 77
    0x1d00c1030181600b0b906980038a41d4010008a01180418000c00840d00031042c0c0382d4910b03003540010907881d40c80c081201c90340405520240303800f00c001a0f541d0b01720303440b000514640d80a0f10082d11700c1e8100b488200da00030b8450300c802c000590141002c54005c407400c101700e18581050300d49402500c00701d803c005078002c043e00c103d00e05c00d200003492400b20303a05820101c0e034660744c00440a082c8101c84011000e03111b000140d00d1036148182d1310031061b031b501074040c2e0a595211503040319259401554640d0001e01510010300c000e15012802d2100100010300701c078200a05a004070301a1a825441912403c610b020301c0b0340580e400c00105540700b102483c080101c1810314003168000e00000d00a00640000d04c00007d5031640258000301c0030720b801a01382c00f81c01c1d01040c802580d03540400f106035401d008140000a1040148104076200402140558100f0840d1413000006080040c0100c840e84254496030b07175040017989882c005010b05038120704040d8100000d01d032174145003014084c800c0305200c00b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 968191717 1250 968190467 968190473
    0x30f011424060d0b0d050604030810150e1c0b091b01080a09020d0b0108010e160f06080c090904050706110c010c110f1201020d23040b0a140a0b120703 66
    0x98114070000201d503a90744801d0388102da04010180d400c81d0783d4109a0807040030b01403050000e9002e11451080d607030800f49036034007141d00c41e001d0028412070314010006510400e06074000c15040003859000790901d42d00c035004044403201071115100c00c0c0c5a0032203034130601c03c03840400e01c20070710064001022950302001030300000306080030083c80561640d5a68901200310754600c0d02c0a48440d41044014101e540c540c020240204400c484010032803140c031155602c40541c8550403001c4462445000048610704842620109001005034a580741c081210280c3c503551003404501460003100101281814075902038040000c10a000c1083c1c0d12185000f04142c2e071200002c0301d0300d03900c1010720a060a1044c0400e00c00000380f12000d034000f081e1500113504881c154081c1c400711040322414816400c040e08020200f544000d00020103404d410005004610300a90280d0414076840000415007403411920007032a10644103424802d031110b80010301880c0402d80749504070501405069a285595 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 968192967 1250 968191717 968191771
    0x40b0603010e07140f0a080f090a0312150510050903060c0315040903050c01050a020a1403060d11031e030a0914090601110c030106030b100605030c03060f0f030f0114 73
    0x9000e9810000e81d10340c0c00d0100c030010002d40d44042405040307140c0b240400c04003e0440325041b41c441003100d220788d0010300094800254140310ba80c1546904820708580801c600c003a02c040011130700300c130308407403400281034841c500030980115545d96065180c100e075400301801c2400282c61107a4031401030050190302017100354180d0300000c007110700196030b50103440e056400d8020301000f440f5551808042084125090b0001c1c40d00082c9036441814490100c50704480e540810303921181c001c02401150800034804030b03141c440308400102200e02008490150320030010104010344007030b800c0482c18540d45500314a4020242c05013402808505900303001040011000414590400490b11240d80314940c0501a01100902c081c0080c08003030307201e080502545005654100d01800c2a010000302c0e00e1060b01540e0195200440b179914645075401001281444518580c1c0d02a0100d001c410301540c081213080280240a00041400e8a00c1d411b1201042c100070003400d4001c204000107001c0350008 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 968194217 1250 968192967 968192971
    0x6110a051e0f121617030a0506040605040905060609090c0913120c030e04051909052a100c1b080f0c010212120a020c0f030c010c1d01050a0c17040302040b0603010e 72
    0x1600a080200c0b01800e003a400c4840c21581e03205c4014000040c45039040c91a080103200d440241c40901101380c0d11818002111120031019084e900280e022540c580f070f00050305034210a070030080f5240c028101000038075401040e203282082d1a00801c2c3c9804128540d280300090b0810780c1840390819070241c6000d440440b840082a10940c0d83e100082c000000000d000000d035a00c4050800029085150103540d40ca03140840445981280c10348080310051210000004440035042c00c2c092103000e4001c3d24000d0000f0421200a00c9100300b100080c03034600b20100042c41000024040b000c00c500380c1a0801c00114103440c1150080d021004511035010100c0e0b607141005084400c042e074803001140024025184907003214080d850700748805080000280800c203c481d00200451411b1100a503010180d4107204c400301038002c010b900040d030040c40640804041828003074003404e02580d840c07101c0701006680441101c0b0200c2c0c18404d42c10640714060341c0b11019103d035455541000c5130103a6100d00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 968195467 1250 968194217 968194237
    0xc05030a051f0b0d1a060915090409031d010905060f160503070c051e09160c0b01030b100b041d1b040e1b120106110a051e0f12 56
    0x40707101003910800c54488480d0010b40700300c24404090380320b500300b28441d4880502014500e0510030390360044442121111500000180041d240c2100c42060041e1042000b00a00030900180610040c40c2c840b40510903690348242e4880000380501c108010159881014103810480021028000c688408045940701110340100f03540740e191081a514814280600c003c04a00012482d00d0803c2046590082540d4080300e009080c1505051003d210010340003865a10400f201c010948415529071050503680003458848000c02c0b20361a121701c03c8038207900031580c04511200708000e252584450b08050020742d00103a142c1850038032905100c410b40d0022404e89a000c0b0040303900340c6458000c1000000c8c0001c140764442d5550100c0488543d01141c200b10080c1180c00640424142803084070a40d9001c1342c4245e2860342014000c540309600c03903e000e1480d201e00019080460010001808844201190381c40103001481560b0704004a912115400f540003e4a400241322842e003030b0343c4c0c4444 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 968196717 1250 968195467 968195471
    0x80604140417131806060e030609100c141606050115090e15131a12100f1e09060e030304031e18060305091203010506040e06040f06180f0c05030a 64
    0x1910040007503104155070b000903501540000b804028003131a410582c200e4117603494038456481200c0c10305844106c2100c0c01e030b105800980c100342d083c00b00c1e40e1210343c81d04403e20b0600d110754542d854848259200d40c1c151891030820f0050202008185e0156034050702c45929a1407104d22540d001908480407030003091303e03a407990320010342d010800000201001000400005440b4009440d4400a00780ca103501c290345100394400c21040d05020100e4203425985a00403ca10b00300202164020302d541c2c3c02415030152225428110558401030b4218180e14010002450a84c14940001228412418018240c10901c10040440d0700900110364101000001e005400751145080310400303a01c0c1c8440c1501c01c0030b17110200d6083d9140d400f4a205020001c2269520581450014501d000034410a03a100104100602c001c646010350310740c1212011300041030031b00e0b001d40100140c07016500040e000264050014140b2091405a0b01d030321965032204100404c12502c0c010003e00c0001c0c90800256 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 968197967 1250 968196717 968196727
    0x15060f0c02060c101107060506090c0f0d0906020d0e150609130f080310080f0703120e0109051c0c0b0306031b0f102304050306060d080403060c080604140417 69
    0x141c0504c1240291130040f101042000f50550420805070000e0600b5540c4610f4500090f00c0c03810018949030244080c01c85c0c0c14100241480c25111540c0f092108a80790b0382c442c5003050000b016030000c0c03d00103103030384008101c100040804911b0142c0c58404950811103840c2886059180c0f100701c2e503000300c2c240c0600381000d0498204460709841214006020590010030460a440351a1214041d036213540c050710558065405900d03a50b100d240805804400d003c48440b25141c0100d05460f050a0181082d10046940b44002403002d64625220f040c40880c1090030010001002100030103414680c50181c02d40c00c050010070340d640c250b001c0d040d4610760600000d90059481c40b24082c000c1c00300034124214211260340003800203e80070b020f680c1800702d0f41c10740c046120075142510141c9e54007900624490783d40c3c02c10440ca0340742c040030554007000b0810000c40070400c5c600504944107420b80f600301c000d08108050004079800d60000941d001c86041c00c1c072000460800350f0050048250600c0c541725 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 968199217 1250 968197967 968197987
    0x10f0b0d1203051b070803040b0105192303010f060905070c08120c0702060d0606110c030c060f040b0d0c3509280b0105010e0303071511070615060f0c0206 68
    0x4d0705801c41041102200420600c04000522000f5881948604031490450341e0340c03c10b01c100d24020f0380341c0c030f079070303040784140a01030071401c000c00c2540c0349900030103810b00b010050013103030031522516106224143c543c103060000383c4041c01019040891460708525208486d26519602d010310240e402c004850b250104180388080c00a452041d42c006003025601e800c00e1f003281006208510500c80030414604000c501c0c90401b1444044554010b400780450080316801c001580c0c0c4690540100a107052001290520300c80001d0b00d910700780300c40001400040e1380070181860049070020044500030312440350b04a10b183c02c07404402000301040c4110750719410030f060f04125075881e44a501c0c0800c1c03103c0040c4040810300e09408036015001c00e59883e620340004485440060100c1a0181d108004450000304541c04502103480000f10000c0e800c44401440321250b03005010540b189900c4011645805411011180060032a820500c180c0c0451900141450b600380101078031442d030114002100e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 968200467 1250 968199217 968199241
    0x9030b09010b060d09061d030409050c070506070c0312061a0901111903090902070c150c0c0f030506070206241302160b10082d060702010f0b0d120305 66
    0x11a04024401601d031070a48030084014036060600f5035201d42080110380300c424007840c42c0e4008807c440080c51410b4144820340000c3e181c00b8001d0303100300da810040b08001c1002802000d0040380a80d5403591100260706008144110349400702c45290320f40304040103986a54001140450106142c0940701e07070b05d420050712941d01d11f100c801e410f8043d0004411140a542d40700c0303c5507610a4030703000c1d0155201c000400403070080300d000818141c448181880030f1014150650400160751400f400c0c0b80f0360907503c101c1100c010794001c5e0f250610b180406d101300607050000a5011200b031005141505d05428240044000c0c02540380100250402d20205525007103042c80380e201c2c0d212030642d969100c0e000c0c210120700c108002540c291100002040206040d0f41e06030301182c40c0240181040c5640b03c1044030070740b580c8100c24404010401007a40400d80a010701880f504094000180c40c04900410348261390180c00d60610504031440d007140010705003060f902e0741c100c0343e250014640c0d64900205c81 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 968201717 1250 968200467 968200481
    0x10b0a140d03140c0d0207090f0204033207030501020a08090303092d060c040503120c03043b090705010c0209130302070e01080c040b040207230c121605060a09030b0901 74
    0x52500036050174406058000410b1400c55011400c20001d4145441040c01203000f00d0000500c0d049003e0041c0112000e02e0100300c0164202100402c8084000344003945020308a07031080740c59035004103c400031a03402c80308042e0720603070707500240d440c0d40790070510755440f41142c60044011201e440980b40040803104240c00300d000c1c103041254001d080c4002d81c209250400d02c52244684184480550401921026204c2e05d1a0b901c000314242030902c8075485503100d1044039042c0540c80301400b01034100c408a000d54507400c0d9003190240601300711000c90300300b44558100a046c0107032410b1810044c1c4800c10010382c40740c0d5643d403404a0203110b2030200c0c10188954440f511030110a400465150008180303843c0d5650f01711402c00581c03103400284800d90160003005001070320429402803443c28046d0b40c1018403242d080a4404c08240d800003c0c00001c1031107028032055200407080c09080f03030b0354000003015140454489051800d050300041c5000742e140801803d800c16803010418001094010302 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 968202967 1250 968201717 968201737
    0xf0c15012c150613140339040906140903180607050a0f0b0f33150f07050105060a080a150908030106050703020c010801031e23010b0a140d0314 63
    0x41c0c4e41d84451a00c00004009409120b07960100a4400c5400349000240054121a000d185400f0b18014000c2000e4286003030824001403540700c0c14a0b502582d4610039030340141d209000029821180c0040c5480da00f030001c140031800e03401005070410390281901c51580a2004603440b541c0c4e5041da29001d4103180b00301d140184000b41052204080000321440244615a40c4021a031103580c0c202c8590391402c81941c00c070651411140344211400c111030089420880f0285c40c1403003048429090000b65482803000c5e969540010a095040003000e000b803e810000488115200d03078100391a031520f5100701d00307004020024511520310101c030560040f4030400e0b0070541c0c403500c0750307540c4401500c60b5108141c120018081c0642840381e40d0302495a490507a50003030030700700308507840745010050f81603000030a4036040c440c4000d0714800360300141070101d1540d90100204d0000c05110501c41c5100c91600a000c0140020071600310b1510781d8034220b1b9480c1e4240c5881e87c0c00b19688000d284e4588180321001c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 968204217 1250 968202967 968202979
    0xf090f091d060f070815010903350a030b0603040812040f0f08090405010905092d161406070305030a02030709030f0f0215040303090b0f0f0c15012c15 66
    0x414661403458003d4441c10303581d29440e459a46010800c0c000c070321084102408140d440c1c6050006c0345a041d88648243c6a001401c0304400c24000720b002c0785000c14221036024880040c01c10309141c0e250040c0c042c80001900c0c800c1c21801c2c0f0350b9541e519405001c00c0070640100c1072001a09000c6020b03035450800d0b402c09852980ca1003581455141c0b98804c1440e01e015905100000401c07203214801c0610614821000c3c01041c10b480585083c2c40d86012008c9040220f00c0b403000301088800d109400e258041ca422900302e007454140c00f03401042400c11400d102e01d0041c001480400d42180489610100f24840140e4070b903105103054a101c0c0700317600b01505070901c0c4400c68040111540c0030f03449a81c02220700e0b070903401420181069a00c02c1d40001400600d451100300074002100020f07000440c1410a11030810040702149a007540089400c041c996104160901400c83d2803800c190141c8502d6480d140c0b0300c082c2141d407490141d031310351840180c01c0b5840c000a02c450820043c1c121214001040c1c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 968205467 1250 968204217 968204221
    0x31203060e0115050702010f020c19150801050d03050903120d1415010e04200a0914030105040825060e07060201060905270c041103070f090f091d06 65
    0x800500080c0601c5209404460000c9000c42000101d000d09202594030b2a10b4000f1503801180d50b4004200ca21081d03120300c2d0074100241da00c6c01c00400841400600401c443d5240042000000700f002c018102480041001030203c0d07241d81c0b031110030007601404d12542e201500c1000c60719002d00100020001ca90100740c00002084917081181d001b540f0810104caa52542080b0148051421080c0e90219211030642e10090a0503042195080700c15600200349100c141e40843c00c0b0f83c4807220700c5e00000c008603801d04c20800c940000c49500c0c40141c000f00450b1a00b5510444284142d01c004c0c5e151609c480d401554810f8030080d0041455400700c020b10000b0410b01000e41d48880e14011507001d94244100801c501c0d60a20409225020307100faa11040d5080500c1d540381043c1440103070b40030740515018000c00740c80f940212242c1e210300504c0a0b50300d18008600800380c01f080b06010003007017208803080000c141400012030a451600e10006046942c01000540c1c12104203244034082c05043c00b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 968206717 1250 968205467 968205503
    0xd050c04140a0e1305010e0a0308042a0302060c030c070f060905030a0b04080f041a07060e030a021209040216060609061e09021b0114060f010212090d0302010603 71
    0x40a802160215090032034290700900030020b01a0160080100910080b000100b203211000c003220034032400b820000641241d0002e02c030717003024103141058002c034200c2c0d024031003001042c8903051500710148074045440302d000503240c0700f4030321203210107403043c800810f082d1b000703075414811540f03216407910848540d03d58518445030f0b00440c0d031003024040303901e5182c0000c0038180072030000d220b103502c11803003000c0395119900c54101ea00200c508101584051201050506420b402000031400004d200b075105c040c07503c0c01d04107491103041d0305a0746400910298043d507800041c048900c071034113043c9a4030350004c9000b00e0300a02a00e142c508450050382e0610081c460783e03900c5002034031000c1109014180c0c5a00130780fa14107020480341c0d45100721032001000070044ea5030152100941000501c00800d406041580c02d4591944101c48000d0350b180a00c01203180c0b040000c10403181c20300151548204101841e0000e00507170b83d41c28003421902da40030003054802e510080c05164880d07800140705045a03 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 968207967 1250 968206717 968206741
    0x1d060d06060509090c0405070e0607080a030204031e0c141f02190c0e06030a12031a090c0a0207090b0616050c09070807080112080301050f130f0e0c040905150c0d05 72
    0xa505540a11f1500740441c0000c2c0c4030b0214403410000141c1101c0c60090a40d5400c1c60544c014141c00003015420b200100c00140d002107011031160b00e07551140710140e01800c180e0f81c00351042d0700050303c810004025800580701d251a013201c040064201c002d41c0e43c0208401c0e0700300320380d1940661520b0070210021040246200102d000d448034640721810741c0d0303100300030b0640d1003500e62005080c1c280c40d420f0303100d5001e03c603401114009020003100c3c0e94013650140400d5503608183e4a802208402080082285604004034001001c1c8404280592041580800c0e89031290010701000030400e4800700041c00340401041c240100042d012841a15011400908140781500d59000040c82d080000484101404d807800405410a08040c556480d0100308400070f1070300c4841e540c10882d85510061090300c1d600c2045105c144a10000c1145110392070854107042d0f504441600ca5454601e46401040002501c01c1070203403016200d94ac15200c1640304811805001080040c41c0e003480c042140358030b118 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 968209217 1250 968207967 968207983
    0x61b06180f010608070b0a12090f0b0a1109060a0306030b070f0908070e0c09010e040e030d0606030203040c050d0f1b05010f08310b1f1d060d0606050909 67
    0x60059070550300c191000306090b43c2107449204e0310b0781e200c83e000303010048503400200710001d03035404e08810780c080802c840816250800c1065034000c0f651020751060000e00c44513180c6c48080000208054503016011813128043e40e44031034001c62001ca035164040f40260700c000091604008803200c0c41c5402c010080000d0621549500024400e8000141140c000141358003940c210006036400c5980f142000d829903080042c2690401604801e915459155841403402031711040000c1d5582e00010450201075070103580c4510201031040080201040142e07440d030064a00455403015081c207141442d8056031003180029264203a04e000c0100c2c0c071031000e040d034402c9820a807941d40c0341c0e070381400003030700c0c0502e0440d601c01c0840202c11008912611180c60310310224040c001c88810004662161a00240b041380d06450107003804000f48611080b1202440c014580e40c2c607040d00880390b070020700d245c0e1a006400b0340d0003900c1040302c500c10000c0b00d03046000a0f20015210810a00c0d11900b4560348001e0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 968210467 1250 968209217 968209261
    0x110c1e04060e040f06020304061e06030b150d080d09150603210f080408040810020d110406090608070903021002010c080c0301140607051516091d010302061b06 70
    0x140c801c000640d0041c280c03400340b02e2500a01d10303400807186034a986000e540300a000712401c81d600d0000703030703001d07210130159002d06040350380d00040e003504510f80445201006452820550480d401c010417035500d002c400602c050380690032940b907040300d9501c440548440400101802150f054459840406038400310880b8003c60410440e40700403807a0f9042400b4198010000605010900c4185806002d48641051045816500c5c003980d03a80c2007414075958a0b0308480031900015009981074060003542000200407122034646883d011000d002c0c07500503c120710500c483d50002030340300d5002e454104004c54015100b03080c00e00b00c10000a00916a0b0480308002c107503030f82d02081da004031080c00c1d641610500b0b408403041d080d0302e000f00700b00750300301e05800c480f50320441521040b003034200381406001d4000754004031704403001402e010f445403a07150011328801d28280626040580c0400d121030450303405030341c3c3c13559541c41c04c8011000c20303c0140601405100d51014003160000001800b00e10301a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 968211717 1250 968210467 968210471
    0x209060316080c0a12051008190b1b1902010603020a061e181413020c01050403110307121101020c0703081803193002060105040c020d0f110c1e04 64
    0x10710807102c4003d9000e100140400140c50300c40300e60842c9034951011340c10412020b07513400782c40d46d02c0c02814502a0b65480656003100780c0c601000400c4542102c09401c82030b0410200c041c1c083c40f6565100b01d0007200f0341c2e001005800304681034120b00039407100c4051600a0644c01c00c843c0c0340c080292018550070002c2c02004c49121080503424840c110011055402510140d50185094075040682800d411307041e51003100e21504016144241c402007072061500000440c2501d00360601402136103120b40c001c0c209d0b4008100b043c000910206100480c410103050200c40513041140960080c054041c9602c014800d0306008014090b4240140286a03d02e242560002c41c10301c0906448160a100354150208685a80400a059810040070594290b02c0c94041200d440313000e1000300b400c0143c00070168001400502c49424180074100740c16071640010304110380090b40081503e46100720850821800329200c98011400340b084420700100248017035101411b0540c0140a10017000b41148070fa4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 968212967 1250 968211717 968211721
    0x60b3702030a081521031303050a0308010806040503030105040908040909060509011104060e0906190603060e0a020a0f0f1404061d10210f021b0c0909070504020d020906031608 77
    0x200c0030001d48240304d44054040c5042d01d9241c0c4107085408040c2c00300394420300084c0f01c40c010780c09442850360002c5004030014142000b281c00c010f089500103030048005a0021020803001c0342c800003c980c111001a0303000a0342048504090010f80619007180318882d06181c3c840c41441348540040e40242131200080010011034080031074036105502c00c2c40081058200c03501014584001f41645c00315028050740c0980a40d84000300d40080e05401203400700b543c603281880701c20181000d1660014840300118a028031510001d000f04030a16605006c001403034440381d07070441c0f0036034140752100c0141c12407a49032601d03288060104524225500d40d4124110400801c61408030007034424040ca64852014841811800c00f03104038450080070132a64840c05000c9130302d20144020169105d05110844901c005115440d050240a400c0c0314400c942580920039144401724022003100c10131500181d4481801441c100640515222240d12400200400818a0f04030f80f6603c200c0c0c0e103540c0c4840c000d03 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 968214217 1250 968212967 968212981
    0x1d040501090b070c0204060e061311090a031a101d041b0f21170c010b030a11040f0605210c0411040f081f0914010501090608010f060b3702030a08 64
    0x1230904131035160b4400f030429242210700d51150300400501c14070b1680103140058503000319104000aa00c111601c403034055100501840e02c0c0807054000700100080307650146465110f00340080e500c640f800440000348082402c02110a0f41740d03113012202d210805c0b070107a941c2c1c4841251603043c45090809141d540c1d040711200c8081c010a080c995011106062451100061b26403640018403003040540d03a84d000ca400c82d9804100c4141880e01c81d000a4001c0c094101c01c0c4410381e6a400880b40220b41031031820b0150b40d5600346118074070b1070310703440780350001c8041d0314054a00b0b0b0189941b66003051402040788903400d070023401013040d81c22020000796400d40c0c070064a0785d61804140461020050786209600c600308036042b078000c0790300548814604650110105007102c1c03082c1c1c000c10f020b6641e28800c201130b80082c020031456903840c074400c0002900d800c0e1250024070642c80710820280326039007529814041c80106955000540503d03658800c3d5155020390f90364080d40001011403041c200107804 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 968215467 1250 968214217 968214239
    0x20c010c020f06010905091501152d080c07150507081003030801030f14010507030f0c0e01080a050402031c1d1e0d0507050613030204060506041d040501090b070c020406 74
    0x8202ca4500040c8566842d0500c5d0400402020b08100300500a9015002529031401c06907406007512001d002c2020000302005801c80b400307452101035980c0002c403280940541c400003000603030541d0900e00100d60380d0040a000c4d9114a0000134421003d0500c491131644040c0d04c00e5204462648884ae05500e41c0751803000e06800501c8010f000802d600010b20011300c0381550031000b036218110004180000c44055400c0d1402251403800103542e07000c1083c2e02a409004611081d40c95040ca00501e18900c000240980401004040308545a1010504540b02044598800f40c1641e408401074404210001c0080c0505061300a00c0340884441384460b06c1c201f550f480d0043c11a09210b040c0040407420320240e47c240b01c01c2551380d030003140d10016040d1659801007690003040041c0c89081ca04610400c400c5500c0354001e00e006080601090180c100d420103d50307408602050b0006450384e9034500140074000d40ca20050034014182c040c4841a504440d0304089540300319002d20140340c44041c0104 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 968216717 1250 968215467 968215483
    0xa0b060c0712200d15020d0c0806010e01050a020c0105130807060c0b06030c060d0b030a060c0203040914091e10140105120f0309010c11090103240908070206030c1c020c010c02 77
    0xa440213413000c609002440b40950103800341e45502c001760828920807022005c84030b00070341500200321103508000780c56030f00c5841c50503071040900f4182d04210310514000d5848800c800c0381414032170001610490a41c014802e00b00914000d802c0343d01041d11103000030450038941d54100c403031660712800b01d1000c0c580824540c2050340043d22039410545105068400780550000803a0180111411500402c80d103010311b510003422600103658507450300c06480200c1d43c840354940c02504088090050303240d00880c07181c90300300c494071103030340959940003840d801c0144c090900b00410707280070801e40d04402c0505291f41201c4040301d07038005003603d590100b6140e580040101c02c13150402c224070300f082e60050400c0680c0314001d00d841c15144c046000450038482c0c2c280c00a84046010402400004042c41008940c00000400030700185c0e603a035070750780c0ca40d0003210340080c850540400003a00c0a0280c1060b6408018824502400c240710816804000c1d0302c40804420301c0d500700301c1c002c41c4841c00000ca1403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 968217967 1250 968216717 968216719
    0x602160812160f050706030617161a0c0303160e04090c05090a060b04080a11011d040915020a23120a0c09030f2909060a0b060c071220 59
    0x54509154039503009401c00c2c1d8030744110b0301c011852000d480415020440c903c05040c4d41d440003c4c1041c03c05003600b1300100c00500211190344002c001c900ca22480c002070800f15040c90f114210382c00c403440811280390050703018003140e503c000300070000004441c1200c1c4480001c140c6504840341e41010500c4182c900c4480701403ca060710b14403c00c8641030024416501c500c806600080c1562030b1a46580c1d90b034440d600040640e03020a0040052000c1008100c6408100b420440404501c511410040b0b10601456a05c11950344281406005191002e80d80d0709140c03441c00c6503603242d0220058606540b460140740c1741c00c22030f1000000c04032850304840d06610050300088440d0780e480c51140282800e504a04204450712100000003103009120100c0940308403440d0050305074601c44030b002e40c3c829200403daa0041c540030304c1500c18010901c82e800844580340482c024440340042070380e91042d050307201c03818401c0f62070004040b44800003908119104803400b0440301c254412125000040103201 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 968219217 1250 968217967 968218003
    0x902090f040305091e10180e060a0e0a0f091416051e0f030304120b060406060503220507080a0b060303090f010c150f0c0f021b0f01120606021608 64
    0x31311600e450010204164a140680e40041c00a0008254440044480b00010450310300001d0390003c040300804015061641aa03066840c00100065803185c55100344821081c00c040802c016070b4041e000380d0540e41d4107210604c1992005d1903d01c00703160100c2003012290082c002e0107c0c0174100c505009003120307070007404407250031030303040302400800140e61003070303900c119415201e107090b03101400038000504404660724041030541c204400c1c0610003c02d064442e80c50104140001d5801401b980c3d0009070200b003114803150b12407154010107089039030141c40e51291036000500c0f1031000941c090080e11454180e89586c4131542031555038018440410751050240d1651240d9500c5860707580d40250203104040f0f20f07442036035080800c5544542c1c115906030b48031b54400180c140c1084459040714003520040002151703503110854100070081e001c900c0f4800403a004507803a0700c0b442ca030009405406800300152699454084e507245101c102e150401a800700b030000d07010101080d041500d014007520 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 968220467 1250 968219217 968219227
    0x1d010510030e0d0f1218050f01060f0b09131a01090807050916050d0c050a080105030d0903080d06030b090709140903041a0705010905010507021603050c310902090f040305 75
    0x3c151a1620764800581c01c1000450100c91544e07181d0040d9002d00700c54950068804030346041450405282003030340700c01681003032020401c510310104448100d440c00c840c801e88600b0800e0000b50504e0502c40b103116101c1c108410305100464211042c890304000b40c039001c480a80d1001c80d41d8903501c0f14480d61351701c080311400180c4c0120351408010034075440b9140c01460310502c0074045007114419180140020004615219903a0704130250502400c0101d004145d0703200c0c0c5140044c5a0039190000500d02200800c401e106601c054200b48043e592141c6650080c0c6071410b407041c0c1c0c1380c40f2445a405000e041004200202d0314100c6810300429561000e18035203402c244d03400103005040050280040d9041200c500410001c0c4a0101d480780718038004912410404002440c00d020116024807d4090520400c00241e00140001d240c000c2554100b044000103a55024500b1001c5201c41c441c40080082c0c41c20b8040991249411610850704043e0036200c0100103890301d4400ca03001400300c1c1d03003040 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 968221717 1250 968220467 968220493
    0x60b04090e01020c061509070302040b0304121139011202070f0804030807060605040b010e0d0c0504050915160806040506150a021509120405090406061d010510030e 72
    0x1035245600380c20025240440c4a421305107000403c840c030401520741501d980c01030b0f203480314a03aa0080c46925041d0b0402d82070500c1e24109201c054001441901c0305050000303107a008068018855881b40155019000c04000c028125165070b1084c1c02c0440003500c0980d070741030500c1001c0f41c2c2008103950b1111104182d003e048029403007074230181d42a03441c0405000000f03100710000c3c80a140301d58000f03625202c1d5031610f44140c4844d41c01861103075080004100741030768004151032610b03804850391020b85502e401d09048040c05038009a03002801e1204110040c8800540701030302150b206c400075003d40c1c0311984640103414401c4540d00098040003c20a44c2c0360541201c3c0d004000209800c501402035030310010150b05c804180c50258002c41203c604980801c6071480d40015100050441d0b1404010560582e101d02e0040354410000c40703003c5803d00c0748030303030014000d03003210100c5040c604500320381181d003c00244a001e2090348895041d80d010f600c40e00888001300e04c250020f1404410f608 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 968222967 1250 968221717 968221721
    0x3122f0304180b030307030e010e0906030606130e030a2114060904061404030f1404030b0414100609050133120209090a05090d090320010e030f0610050301060b0409 72
    0xc402034403150f101c90340988150b0341400100005482911000c29105515001601044d01e407030860b441000d4280c10090691000702c1c03c82e0b402607041703a41c41440035600881500804aa000303200f04c42c440400c03440411130304060a45034a0020030702e425030003e00c581120054605040d0400c2c040003103100402c0644c06c000c01a203070814802e1001148424507002c8000c1c0d10070301111300354002181c9406010740e540e00070595080100c581746c212072800e4195143e407400c10380b018100420007881e00900600400701801100096140707690140089550f0b0040d52000d81001e018224411015500200c8501260030f40d034006501c103511281c0c0c1d01082040155503000d409a080d140e003a0302005503041c1e070303a241c00100303210b03001c039190020349418006650f0307142443c6901110b007800061401800401c4010f080305007103a00e50340340345810242200040301d10201004006800d8495407141001607400407032090b109226001c004815503946404060a0311401d10072130746829400c11050202c0081a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 968224217 1250 968222967 968222999
    0x70b220f0e1f3308060a090e0303180708100c140702010f0c08040911030a180203030403060e15090d1112090d0f021002061506070c050603060a03122f0304 68
    0x40032108194001c0f101044a00c0c48500e10104001034101040200c1454039440380006481c84401c108140c1041d03001e04e80d524480070b000380c0d0000440d0003641f100100c040107904050030b981c400765440c4501d18603400010381005a0500b021030780c541c8102d1030451441c000e81d005190146d480082800d0305103810764800a0380103041e070703030050208000315402007580280d808007880d143e00550780b0702d003080640040340c00d0070320302c40403d507000c2814001695000080c1e5064030b4100740d00040000440c40d105150090504c103840d900b5071200c0400c46480780116501014803850348034402c0b0300d1300304182e040d201c40e6a078003070404090091040c000f260400d5400116501e2145034141910400c80d00012000c6425401c0800180c2c44001008560132485000210404042d9005400c0144a0f51200d003a95083c0c001c6a0040001100140240c6d403a0440c41008540000505090300703000b180c001d0108002c0805e40104180c84415490403401080580880000043c059805c0c6410580350451210750 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 968225467 1250 968224217 968224259
    0xb040516111c110105010b040b221a0705011d1c0c141612020d03030506040f05180717030904051008070602060f011205070b220f0e1f 59
    0x245000307140210384021428000b8803541c1e00c4168403006074060807800d4a4050700892400f89044c0001c000d4a0151303002d49100e1101c082d00180c2c0c41b01141d51007000040c0c640d000707c000201200b100c4024080d584020540d0a020f81c000744107408039407110545001c52086070100c05c1c0d0001580140790041e10b800c210040c0e001385001e2445269a80342e10801d00402c4044075115000f51641c05e42841c0681d4010000704580c1748104050242e9400240300c00645503006030a0644030f0700042c501c2e0756983e108683c00f0448040c104079134100903240300c0041e443d4040c405400c1c0320b5540085858103106101c0b0005410140042d480c1a200c08140005404007920514507001200300c0400d04010a028440c00741945500038070880c500302c0480d503076602060748900d0740807000f07600100102d03002140c81401e50340b24106907a9124000e02c52001417440341508000804402180860004640406441200c881007050f0700c1640741c1c2c252600a8644454400000724903010082065040c42c010720100300e40 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 968226717 1250 968225467 968225473
    0x9050604060e0a0b0a05180703080a0804110918010c03090c21020a0b031501031103060910050607111201050f15030102120a0b041407020318040626010b04051611 71
    0x3ca56507640c0c40340400d94080f8607660b200d00400160701c0514820342200c2604000800b1503d146482d071000a205500806081284c1140041c081c4520b407800d0b049807007006002c0d84041c1c03410440f0000400885400e8410765400c048000078054882d025040c04150004a40b0318610300e002d03002e4107000140c02a8008080c001400100540d454045e00c80c002d0818a070190f58034900b000840f02005407444259040c03504e85641d03045000c50b10400d413940700c0010340d41c0350510748440800d508410040d41c0500d44c011400655602002054400c0e44110030007a60050a410b0120130001e081e10002c42da0342e200480fa0308002089240c020668022504002c2c000610b01703000960080075145045171074105d955282c80346116a0b05092040b4200300418800b00c480c94206614025140e1255010300301a602644c404d11f02140e4660707200d0001460ac40024040e1036000c50030075426210b42888402e059440c10002c2d42c120706050150621030641c4690016842444540c1600d1900507135200140c270744 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 968227967 1250 968226717 968226733
    0x170c03060121110411040e06030d0507260d020408070e040b06060f0909041202160609090e0c0409050604170901050304020108220309050a0609080607031d011a0a0909050604060e 78
    0x240351071040303808008030307040c3d0b45d1703510390034442050301811005d4642406076105181d18000c899000003903d00d243e03401501e40d5040240441e8201309800c042030341844210f0000348681f000c200e2a4010409c982021040d107400e60b50b610108110000c00b101e02510b0f80c60302200250251815034000c006270f204c82c840e25410072810f040801e8003440d04403405c452481800c414070001c680c04000c50f40b41402250800e6444074203000000b4601031162051100c910b458905042c41d182d03050103801303c1c40d0405401000307100300398100b0503030f68002a2010b85071042002d042044400b00002240d040a20603103501e491600c80b82c0c01155910002803000d0b40c01840c6580c2d1400f58100e03245451185402a654001c140e0700380030400444200c1c50740014140b1100b00c5080200700c1010449035400300460800044003406512910745030360100001c3c43c0103511b440d1100c51540c01c4c0300c4080c010100c05a43e5404610740b100d40300c904803a00c1e980c020f000c680c841e800080008025400481000250a080d2207000c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 968229217 1250 968227967 968227969
    0x5010e0a0914070e191502070302031b0108010f030f030c060905011805010b0613030b07030608030d0c02070605090102150a0b0a0605071a07140f13170c0306012111 72
    0x403101e1260280403064240144007269500c20b40c0c104c41100121202d0621003d02500b240c409201c070701c81c0842e11807007101842c8060340280803190007140c015054136102078a91240b403070b07248400c107081400304503440004240e036140005540300796540190b51040360703032903600c09440d9000c180404503402910380120744d0009000303005000440003140d065104102140c50b18600b55070550780024000d01090044045403200b203800b0808603500450100303031079101c00800300c002d00041c4d000b810701840002030f02d2030f8012842d800340b04200665800c1d200290740314a4211414880c4044150041c0d020448107290403a0140790703142c2010800200090100d000d1011030503001040d0b0104000c00d201066810a1080404c4580300010380010003503039901e40030340081d00c068500c1178024035103100400d2101010500d982182c5a5125a00c80c12041655030038070008120000d5240442c54041c481c061001418001002c605846e2404518440301c00382070001402d0401c20316058032603103000d071a01300306 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 968230467 1250 968229217 968229221
    0x5130b04091407080c0f2a071503061a130e0c090117010317210c2214061818160f0203030a0e0109020306010b040f050f060405010e0a09 60
    0x30440008042141151203003200b0410700010200020301c078140c0708205440c007503442240c00182c0d241c038a00f0f859102c40401400c0c44420049441d804409030388241c080343e140061020708807509003e0710240003180d1b080072001d88125101d15002c0f0320140d0300543c00200880040e0590842d00c010404140303596200518505105541c0201e00c00c10001e402056940c0c0a5902c0c0041402c05003440e042c7d51456407141008444094002000300000c600c1d8200ea03901c0511003000c9901c0510a1a850304002200c030703640758403641c002e141c14900180d040f180d00340080001e10480d0700c01c008090021031907000703001040c1d1103080c80c100a4024601912411b41e540c51a000d0070b201382d182603000030f10300012038002005418401c041072082d4010303c48a50341d400001c80703034042083c200100303040078104000ca0240c564074100940c140614030000c41c1c5804003401170000c88100b0317054410318698a40a1212419012040c1900000104000c0c8140d5000d603400d0508880d0140c180c494050341c60a5000c1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 968231717 1250 968230467 968230469
    0x10e0919090b010801060803090a09180501020d053c070309170c151902250b07020607030b061605030f0403030f03110a1e02030f071b08070506030705130b04 69
    0x405603140300c014021312009100c0c010107020100015460701a803c0d0004140b070019224a2046030707250600301c200803c0b00c81000a025034804000d64646103178071406009403504030340e510750102400c2510321103080404603002c0c0d0340400f403651541403181c03960012070030302004161030b080c0340c0c5030300e280400104105404868491460341e05900c0da5000d03061a070403c0880d80c3c5919614407050180500d109a03102ca400d080d000b00c400c01079840082d146201008c100700b5409d000c000d515640240244400d907a00548204019400d03104241c2e00d501c1c0079012105c000e01d0040c0c000c0001d1203641000c8000c80040c81c01c0501171002c0340d0501118680204143e0300503041100021314021000c016a50103000b06090b0a222211042c1460103c40e001401c041e2080c1c0f5041c5040024148000a180240115070810070340c1c51130203a64400034100300c80b4540c3d0103c038880400d1030042000a0700c000c041840c10039a20020800e03890b542300c9200440381908400c1c0f4200075080c01c4180000c050b110440208 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 968232967 1250 968231717 968231723
    0xb070209060301110d0501050f090912090301110313060f060b0909180f10060e06090a0b131505120f120703111507080604052502031309020c0708010b010e091909 71
    0xc111b0f0741c181001d106402c080240f200307015a1001c428000300c60404100c00c0070901201c04140d450b00e0013403001a014000003040700c582c0940010502c00c4901440791161561030103040240102842000c144c0112030aa21421071b000350b003440b115810307280c080d2026404c01030341f45104c0c009407805451341e07040c0f0707602170103103400c680c444c5040c460b00714180d011b802c1c010300300442603c90364030b00031020880d480002041e1803030081e918544610700e42e80d403100c14400d000410b40708110729078002043c20321aa000b8060343c1e100c3c042c4107010001607900003850070781c4e001000b0060145a2041c100901564024600480c1807010b0079117035034640c0c102084030650312a03511507400050b040c020000f900048011f84402e014509050401c5010275220f03000078402c2450a083c14100040010100d0441c003501445641c048151040081c0c0d01030346801030407039000641c05450603140d54085d414229441149010b0102c0c0844080e2300c2d031403505a080e035500213941d41c1f050b1022070303a0b49240b40c101c0d0b020310422 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 968234217 1250 968232967 968232971
    0x50c030621061503011401090203011815030f0507030b041527030f03150311010f181401120c110106060c030210021e0a08010504150b070209060301110d 67
    0x804503191152140041440c48804040e14a007040d400d9520380742c00500400d65035100502510560b2800d40c03041013400074005500d5081e5854081e814007a42c002c1c0304007045c02c011650b505d41015000e1103041c400030b803040e1224080a19641c0c410304121007015040d00d13030380101100000419a9200d4141c810303880340200c91058494440310308121525026020f0721180c5401e103d00121610040200c60250107007060444094411401c0f409000d400308200500d40c8940030001c10800703008240c040c174104c240c0351f170320754101012011284546c0103241800c0c0306600f0041000070140c62000c50200e06818502294004020000d0034203031146800710000013186a510030b0000d41080c401c0d200940b4062a04c50078400c82900e00a50f5824846280007120f076000880741c04114120320160703a0640d011960030b40f00c0303500f018044d054103000d04c80c0074000e034103003c1c0800126074030000c0a000e86503038038582130410065400340002580d0082c541d94041d0750724041640680c146102a0040902c80c03440 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 968235467 1250 968234217 968234221
    0x3010306020423010e0d020f0301060303021501080c0a06030c0c1712010503030315010513080f070905010e01061704020f1309030e10090e0c040f0311030615150a050409050c03 77
    0x1842d81440381c0380001c0e40c129030182401c0f1581c0d0040c0070741107680301114020b24100150000841c0001101c1d50b041d455860803400000700358020034044d000124407000710310103a070384201c80e030788450140c00a154041c050724014050680a940501e03440d00311480e01c0009512a5611030210700c2611100407681540400c641e41040340a40c8014003603c400d4000d5070a5090071900c0c3c00080e14240c10a0313050102c0400c020181c0b959014044000740f903000c080f110300009031020305885081500507028140c3c1400c00101d1800c10820056040311744980c0c81c4070003003507181c0f904200102c0181c02240c1c412203111840485d40e03070303810301d00701d91620340940000c4010030383c500a000c803d000d0700224040d20359a0156141d5540000c1030300100e4051004503021030395210170681d49440f8a0300100d845580b03810780031007401091080d88040013010b404407541c61b10ba14080114030701001c07440c01e41c825621110100d8441c20703240a414080be450400320b08140d107400d07608050f01d01c12141c43e1a0300d07001000f = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 968236717 1250 968235467 968235479
    0x60801020f0903010e011103240411120702010b0109151e0f1218060509070e0403080708060d0f0305090102010b0d0501020903150c040905060d0f060501030b09160509130206030103060204 82
    0xc01c4851769402c0b031000700102c820622a84441c0e02000301484515401240411650340e48064600c030b41d05002032041103000c0d11446036001713582110302010203010380c900c0000d0840380140701b54401004147c4603200b07401c4c6000c106c442c0014003140c0f42c0c0100039420801040b501c8e40714070b04c3c803000400343e2146400d9410705540200340c0b54400c2c0070358030741508000c8900045602240c2001d942d9800c001e02040c65070311001e9040c80c0c1000c69005103a600c5103601088141503200411034041e600d80c2e0303100300c0640c80b141e04010580181c4040034044445250007407000a0090005220b000010700010a502c400c03030002400d248032000b000d0f40c4594001480300424030301400800a5070b002c8801c9200c1d14140245210014085c501680950a9980300880c0032681c4081e030100306941d1100d4018442400e8bc0b038040c000e804203101c2101c44d1403440012403c1c501d004920716000381c3c0804001c14100349020100881e2100c090b010b540d0074032804480360003685a074001580a54040c40016a480e46011 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 968237967 1250 968236717 968236721
    0x9040c0e190614090d050d050414010c080d0c030e0a0308041203090c030f031809150605160b18030c06070e04020906040902090112020a0c020301180209070f0201060801020f090301 79
    0x4164040345099520701881103580054120f030155050034800c0391250450000300701d45501d0700c0e070050201d100300122200c2c06640710004100ba28401101042e09940c90401505e80c280107140041200806005c900c0203510150b000d43d110200a290200c0c0c00c0c007004550905044010a050303000881000c200004d00c0702c0c0080e1003140d07001d0341c9010403408156032607050b65800d05020091071080610f20550074544541c1003945543e079000319102105940780c514400811000e0100d034651040d06000142440c02441a20304107403659001c85641c400316a070342840e040c00146008904900603c541c1000741e070802c06400102c0c1000000c104900703140d94098500050151114401c900400060180707844030001d9408031840c0283c00f50701c4441810050306e03114400c6103034001c0d8034030100340f00300982d600c03845a50360740340290020030004045503480740e444000020041e400140410105143d10310030440588002824400051169100e403005402d80e031107494584404107010a9003501450b00f8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 968239217 1250 968237967 968237989
    0x70e0109150e0709030321230601090b041403070902030c13151d01110a1209050f06030c030c0c0a051c0503090d050313061b170108061b09040c0e 64
    0xa042000b0301840c0c00b080040040129000003020460b051107200d149821003441c0304c03100004210140030383e0f04040703044142d41c620b103681e002242403503101158655000b0b02040703040da0700640c0418a024103203c085505000141d80140e0907102c3e909001031aa6003610185005809070000140e40d103044d400203814031300f505e40201a0404809021414850b045003194912804001c00303a44c141c0c0400005840b42e808e1000e00c91018058000030744204040440040c00f103c00e2a20741300342d106e846000303011041031680c4485420176820004104145180806903034001c118403505803510450742246410b001201c0c40417110755000c040b2069601074880d85007610340109107001801c40ca0503203800c5655803104070b10f180501400001140a0f50321042c4a903c0d110f40042d0180540360720b0541940a0f01810789050001404090200c410b0100c0c98524504840c00301000300b846441d41c501c0d120070b0140c0032020400b509020806605192914001c40d41e01d610242c6400c45044203200c107203d04880d01c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 968240467 1250 968239217 968239229
    0xc2a060207060819060b16260d0509120c06151804120207082509090f030e04140c0304050d0509102001061701230106030905070e010915 60
    0x200da05001c4680d111000c030303910078072100344601c01a5401341e008000b00307803a400c203080707002d0700181d05e02500740341518482d075a6119407071000140c0715000641802503007600c4180c81d0300d88108101005a05a03070841c40e00a040d00068541802c07024120201c540e0240111507040d4101c1420407100300d848941500032008103440f51041240017a086c1c06800343d00500c020b006110b105620200148200103000147c503010307088920040e02584444c2c292444c4a01010600c0020100811408924043c1180247e84440303582031890b110340d0203466207002c0b4a00d0580280c1d49580318a054600c00700603d00a88051610664a0030302d800c00700d04211840004d0350900170104112074158a0700c464042030000145005c0808220902100011b044107407246e0301070b0341c01d003000851101d40910801800007010002007203540060102c4900ca0044076848441280c900401000702030701075040700d01c1c4580328200b500c40b4203444454900e6101e400f0307007001c805180c1e15440d200204100700410005440 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 968241717 1250 968240467 968240473
    0x203030103021503100302040e0f01180c18020c010c0305070e010e033403050601050a09050106090909030c06240e0f070f02100c0206070906080603100b010c2a0602 72
    0x20564020032000074001180c061003c00c000b0010b200e1544004040000d554014424010035259140c01a030300c2101c41003d05255103410200460795106105602c02c0039401091407200d2440d28500801440308a400701c00042e40800000820040030310070100b62045644000a0714108540001c18444650110a06000e61107020540c15030300040d003030b915030040011840c1d407104004960f15040001070501c0500350290310000c003c00c680415124140e9400b6514152000c0d6100c0210080c1c0301e081c0b04510214544c001c060000e01d032641c00540c0c1d100c2c06030500b41c44040d4a6a00d1104039100f01c1388541d000c03204c2e0800d2406000040d0b0041000300b24200210034036081c1440c02220702800030b48490140a105000008241d009005042c0c0100e569002002100410311001e91900801c4544000160f0810300100d0300c0d50144101600500d00034006019800381c1d82520300003004485a0300d8103010301c4000d900000741c1211010009200c244405112600c010004c050a040e800d81004d001c2d50 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 968242967 1250 968241717 968241719
    0x15032313030815030a080d020708030907090b03060f0a050411030a1101030b0409030e10180303080601180e13060e100f0e060402060f0f09100c21090e0c12040c0e0702030301 76
    0x142c3d0029882417407a400c001002d903204907019001e4001e2183c08002009030300c001c0200004940041158800c0701c0c030114040c44945216401c25448140445040da9000c1d2500007140d06400c899100740d5025101d020109584da001000103850042c05110444441001004445803540e05000345040920169001c0c80902c60a54000d00b54014010125004901c4400c010245d18466888480c922074111a454141602c0341001005110115801400702c4c1c1e0b45814414030364080e00d40e800840d203601c0c01d4001c8546444211440c0c1990151055901c541c80e25000303000704070709200506900c4000c001c0041c1440c681580041aa240200c01c1700e8640c021104101c007585400c42114840300f01c201003945d948090034036060b824042c1880c603a401c06101024031504680040d00000440d003d05660651440048200c490b628680101303440000c40c4903400300180d61444007004d40001501011900701207140008500803031044505075581c0e4413040d0100702d00ca00a45a071034000043d0701c0598559 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 968244217 1250 968242967 968242969
    0xe07260a031e0c0b045703020a0303050301080106140a0b18062a061b031018060905100b1909051203030f0a0218010f020c1e040c03050115032313030815 67
    0x100c1215a614404180340e40c180070307024030711b608041c8061f40c0e0003072aa034000c540b40d003401851a0000d00414802c0d619004012842d0741141036001300b1a00b004095501305403c0c2040c1001c05c1d040340c07074400b010310640100c0c4504e960b130b140080c1c9040c60011f28441416049901401e035240344a00c00110280c01100601041542c2000c0e5001c1c1300601060059503500c51f850412101c0185910202c840c003403918842100c000e864100900719240b0200500803906c0309070f036440c1e80d820280306000940070100702040000e002901461028401420183d401540d00d4004ca04e035151103181131001500000204580c82c082c442d8021340020304404110b080500707000151a42c2603203040c1060621400c4000300401c244204240303001d0300c6020b80701501000c044440c50700c5070351080c070213688218100b00880950324401e11440381240d00544151100260300f24094008001c0022a05502c0c00211030744029004000c030312038001c65107540b02510406003801c008140d035070301a00c5500e51141c0e01c6401491 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 968245467 1250 968244217 968244323
    0x10920040c0c050616120905010204060e0102160509100b04080f0d1d010503101d06130e030906250807060507080421030e07260a031e0c0b04 62
    0xc0078115070a4851794040103881a0307000840c005558840a040c2044a0100030042d0081c10848009440b000c0860001500682c0c880c1a0340030106081510410f0070409880c10700d0840750803002070051400e825460b140c400c0f42941c01904100084e41c041510140040e074200003940c21320078140f07800d5407151070340110071081d03400642c001810820080003048020398603221030b10080281c10903640400e541245c00c02040d181c2190118440e0402c020600001c400303e0003001000543c80d80038524250a0a04003e9640c1200010707450b000144000b40090b0b9a07c445003900080c05440c1c20f5460700e145181c810140c5500400740401c0115100921000403214524042030360040c0004a0b00e0f04e0103154121300420001c8030001c200e02c0384200c0042c21f404040b07007000c003850001004020108551982503903c0c0780616000380020400261080c5401502982e50500c40c800c1c902b081d00940b043e103652859601c191420f44900c0131003110b1300315024130100e4141c110407000710801981503041403580c0c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 968246717 1250 968245467 968245471
    0xc030506150d060b0105120403021c050406050a0521100906120c1202040b03061008100501060f0c0302030f1308010c0f0212090f06040f081b0604060e03010920040c0c0506 75
    0x42103840c0c1042e40643d80c000e60544010007d4690f11394564509410000c2d6981c818410704100301041c12a07031715003144202d0444050703172896103480f032604a4481c402c581c00d07031003041000036014800741150008803084a03550b00403140d40d10901d1906040060080803221958040d201041800b00c01c0340000d8034107400c4400322200c1000080d108141400480c1c0a0264030101e250b01d80620803c005401101c0d003600000e079075021085030160301045d00703a00704443e428042c040108110811034155540b042101c14000c61092040d24105000360b650a50b107030300b0580307640c080b4018441060200c010244201d184411081c90446480542d034800a912009100d107400c0307903403000183c424159150034561100a1301c0c040c0909588179070314244180000407038040c91a585c0560003840c4401e40e107264442e1140b5400070501403811b8602503042c0d860070020f00c07000e030300b5540300c40d80540070581e4104a060440103c40442c01c80e10707024010032049858980b17a61081c0300010000c80e01085000604035 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 968247967 1250 968246717 968246723
    0x60b0306100f0b0d38011704110a08100c0f020c010f030e0a0506010b070203071a16140118030906091a0f09030313060206010605030c070308060f0d0c030506150d 71
    0x103683c03562000a01409440b25140858103844210030142034903040d117418030301c400039240e10a4407030390024004503954607400003101c000520b40d1020801140e117084110b010100c0041600c143c03642d031006268100306282c0003000e25513682d02c000b524456004034801102058601c00390900f40b2150001800382c085125021701015a9074007407030307800c0343c04010322240160800201c17001c541e03461014440c503a20041c002c90190003400301c001900060030005250000d00c0c3c0e0310645c10295a0300000e4010a03940400340c400c0e0f00f10a1141e05c00502c02c1c130400f61014000e0445030840c02190a0103460261141e01c22400c1003000c050822004d0051a082c20f0804041e6480369940c0f101c181c034485840c0941c0071416811701000910205034204a0718420440c1c82640a4031a90f0380c1c0d82a00b81d400d808100c5078900141d0b03040119400103482030b102c103a48035800030700c1c0071a21076262001c40d50100f003243e0101c03041100480248288182088004d91000c40000f101c111a8410f1000c550032508508000f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 968249217 1250 968247967 968247989
    0x70e0307080f2b031a0301020418110a1b050703020d1110080702030a03021e160b070507020f04050a0e120c1c0e06070309031e020f010c0521120103060b0306100f 71
    0x7410000403415170049102c000740255103a40d1a200310b080d501c2c58010486502c64603003000c040d81c10542c4419603214603800c1d102c48440e20503540e9040801e41c0010011181c030b0007444e5012005a8406807a040500e001e451140751061950050001654462200d44217103d0108100b0000c5c030380c0001150500c280c1c42c5005a101c4501401009101c6048907580c1c01004000c10310180c54502101d901c1c882c00c0c041d45041d0266119003905071801e10880c00041c4d00301e0326428881d0998102508165080701c14148002005020100300c68240003400c640d401c4420320000c2c40200400e0108412125140400781008840503010000b406002803074031070500501c00465584240745c09103804500443d01b1265920310340c4d07009040e500074640490b404900c9410064041680ca520444003c00c01544c04402040c00031041c0a2982040b23a0003c0e208809907003c1103075020b240c00e04400345000390710508010582101000416060102c0281151580c4d051f4107000c2007110405804901140c26007016 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 968250467 1250 968249217 968249231
    0xe090c03190606030b09010519180308041a09011e1e0507052715031524070c0807080a0f03051309090c0e060d0b01030803070e0307080f2b03 62
    0x12201c06002944d0000d80045080e10810500b000103401030786c0b090304109401d400d00f41d82d0341c084800315000704a0004c4d022081c03900540009000d644d40d140c009004070f4a086903039441111007800c8520894000409945446070240b09140081c440011071b45c05280900c051800300c40842c0e81d8907c401c1d4035101482d1204013182c0100d00038070403100f12244d00c8010a02221403000070420101c886080c007030085541c10360b5607104030130600959004141d0307158801c620100e0303001084851440b010710024407548003072080b00c21a000c1c07001801e00610074200005031383d01e0681018146015540010b0103600400b92450004001501340f152450f03060030b19544600f40c201040e0341d07900c1582c200c00c1c0841d140010030f01c1480506491401140d80030782180c81c40390389007814860181a400401072102086100500014115401540e440b11251610400206620300040d00e4000b05a0040e040740c2c101c039100204550062001c4c0e260b4107108003840408512260140c08503542081d440401c040d03035412 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 968251717 1250 968250467 968250473
    0x3020c0a0b0a170a060302030f070f0608060102030a0f02190f060b030f150709032f15040e0903070602030c040315020306130e0f010f0f0e01111c09061103010e090c0319 74
    0x100c41030240d50090121103940d10014844ac1e501e01d0180100c0001c840d151a000803a60300c40c0e22041e206074010b90155080c80e11407481901c13000140e242d10425805040b82c0c0001685c80500c80b030388541d0040000049424890034104101d03a661010790b80250045c0e1540303d4240e4001078100800c00c00c1508000899070340180841d1032079041e400c01800128501c0c2c41c21103504442120084041c11011a0340c2c0440d06002000b4070388500f808981300c01d000a01c01080ba411007801e0140d885103060040e81c1c40d00902e955000101e034021151031001d6840410309100f0711583d00807100040386001b10852650404800141c0c0c1e07204408400c4c0300c4c250b11155040da55060510522205400600092012101c6c0048520140c070308215014000f034640302c1810010801405081168503a094069207442482d200c108001011007580c804e015413030700c500600054983c404c1507041000310500640325414611111454400035180043c1948800d691207a203580200301c01d90442040e40040c640048185 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 968252967 1250 968251717 968251721
    0x5151305130b180a0f060f260a050f06070201050f04080307020316080904150f031b120b01030c05061e0c12030109060501022e0f0b0301020703020c0a0b0a170a 70
    0x10340c0c607402000c94901c0c0640001c0c504005800b9540c2e00344280040e41d582d10144081b69998800c0c5001c10601840801c5086d8103402a9688041d41700e002c06028400c070f2071220710b010740c20700003140d4941c0820000d41c080d9070244010398200302148000d100505001900321018000540040c2c04441c001001c03d40050082003120054064140066402400ea040803c076507004100043d0141d800c01c2c0552084060300c290603019662245030805d0381d0b5041d40c03590b2481c00749854202c2019200d0710b8000c40c0c00c1c0c00c102c42c4030b03443c01c0c480c140325603682d0304615042d2465051980042c0c0249d5042c0103c94200c0c400c072502c00b00528400e000c041d140d22505640e10301e440d9170728039110422040000086160422a0011400e948007a0201c8001c0c20311610307241c50140702c1c0600710826440318224407445c10039540180001c403496401c04224074414100080c226401401c1c2100540c2c01414100d1070f07414522000d90050029003555403d040c4c8802028182e403030b03a440d07900d103907529140026840508503 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 968254217 1250 968252967 968252981
    0x51c080903031006032a080103051009150902030c060f03190504050309010e0f040f0204080d080603030a030e030415030b0306180a0f0c0e07050301031707030c02060703091e0515130513 81
    0x20003050100c6c81107040041c02c1307100c082c041a41d0358000d100e0420a40d002030b015044015901441a07070103820038810700c02c0180031900040360f00d400b4103000c101a03962060080d180404440c04900e98078100741c0704410000e860016512241420001000301051011040d91101c020a0078605140c52a030704c006406013941180e0641d000345400f0340710344c500c84143d004e030050f2110311040f188403001c5840280c40c030240840b49182e01d0350080041c47c0083e486600180e10134082c040840307007015210880014488005d014000010f96220884422032504000c1c09401c0f41c5001d40361016030450202c07403a180e4182c01c0010300705007202048282049000e806084c0240a080c0c8454210700717202800802c16842807000340c5011000110180c3c6401c00001158034095041e100c0440b0204c079942841040e4000150607004d000c0c0e03410000811002031491074200d180b14108d050505402d2104004c011200c017165512500c009006007c2c0401c0980340d10401d6a070200c4e00000b0101c12801001c0182901d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 968255467 1250 968254217 968254271
    0x402040e0708060a090204050606040f0b0c0307020d060c1b0c06180510052d070611070b0114011412010e04140f0d030e010b0906100309051c08090303100603 69
    0xc0c1c802007101804e00782d0f0040c050140f00f150b040c016503c3e4481086854000c034003c013519a00300140c100b181e079a00d04000d100e401c0141c01943d0400000d038000070116015000166003075525180301082160780f040d202107507020064405403007610740d034907400d405424902824003403052441d4a001c2448482d10158000d040c001c054099144100303400a00d150012114044022021f2413000c1d07107080d0b10440c510984148110725405c01000c0d0b282c400107459907001c102c070300381810081480410389141c0014003030800d41104c000d410041c0400108000683d50002c10000001d02c0b46003078461007100d846044400e4440078020a8945d03060180c0d5000e407490741c1054a200e802d00d03a003041c001c003207803149808001c0d442c10004480b01c00a500e00340e41032245002d601079100b03c005022072130207040828000c10b181c58000f900365400e948e401e04d01007a0800586c80300c0c40300e9451410003030788040c2299000c10324101035410f50074030381c00f10480c64800d8021442403540381c1080040d40c26440c284242c0c0042 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 968256717 1250 968255467 968255473
    0xc2301030b120f0d020d11100c030f2f0a08040b090f031308010c03180b0403050405040e0f10020a08070c1a0a0e0c01030c090509060616030503101d0402040e0708 71
    0xf0100d03e41541c4000244000c03000d8010080001080d50042c810b480b031581200010b8405c00c001d20803080700803d40d0360743c48400e040c0d50f0350244104117024464160042d049030a4a03c42e00c1103490794185c040402c05446d240e8120410084040d1740d40042145e4100d5803190300c2c1074013034a442e44d15900703156a00302201183c1c80040b0702c4901e40e5998003020803c442448008000c0780549600072001c0c3d0315601500d03200c2c5030410054100042c0344c1a0541d5200c5d000c0d10380282400d48660014050702c1c035940160519602400b241c3c0200756080c0845030504190900852a107664400301a0607480300070000302c01c1c04440b1064006008403020f14241c4503000f07080500340c500d440d9903240000c0035881c007800010b2046001c0000954000e204101007102d0503161000303603c3c03410b0100044240c0c01003207960010800c3c4000140c544840400c40b094503c41c0d11180d4407807038080d001c2c0039648142e60102d40c002001603000b101d403e2804d282a60015010b42e804103d5081000f40c0d03920302205940001d039544 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 968257967 1250 968256717 968256733
    0x4050912070f06150f03081606060f0801050109020c0c091506070c140910050f01020114043c03200607020c03070602030909010b07021302030a02070c2301030b12 71
    0x11481c030640c1880944640d008108036080d11244d0a00506035001e003403041c0d070394040305101003402038020f89011039504070303201c0c107040580d5100016640c142d4011403180c2d101c03030001d1000e00000c1c000c503405031110110840c00c05103440d01d07903541c03191454a610b002c0c20840022070741c1040c10104039140120f020301b446a4030081451702c0303807140c0c41e2032141c03a10b8040b1440c1000d81c14941038418038064050560340d00805800e041c00c200c402035140b01c0e81d41c1036650703410202c901e020340c80d8092071086028071003107124280c001c80d00303c0080049840311100b06480f10749030301c203205d1130114502440b501445c0200300b0320700746d900c0f880d4004031030800f94103680310b14020006020f50004140c000b004c000e8065404456460788142e0b92409030710816580051103800501c015102c0700040c0088900081c24010203980e020b42d48001c90780185c42499525400049420070301046002c2e040041c6000d840207642c50410f0b03058a4001800d036007507181010f441c0c00b082d101960780c001c2161071800c40502565810 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 968259217 1250 968257967 968257973
    0x1512070b0a23120718030201080907090e06011e080703033605010318020306060907210b010e0603010b1e0c070605091c0b0c03190515010305010e150405091207 70
    0xd508902d8590010503074103c001020a0721440c1410304158402c0502ea500c1401d603401540d09072801031075030841d0711a80f180001c0070800390207030b1402d41103e0300c0a8011541407880c0d070144074800840e4031150070115072040000700310010380f0104880c6c0515040384c0e42c3c064803142219246541e010418144510584001071000050145c0100d60302624100300d00300d006c00048104104142c0060750503006180000e140741420003503513502014510780030104081c1031102d04104140708040f049000c0ea40d07103c80c2c00f0303540c01108862500b06d048900c03605640c0f60018060140c401c030f554401c0482d00f21102d00581801c40c0041e9402c510740d420544000c0b43c0c403148014802c0d00402e010074424841c51000010086000e08030a80050304980c2e040340a5807241c50344002540090800c2e02014505148244166818400c090160002042c1102070b000e40000050a4407810307081000030034081c2c07092000c01f0384907603d00990100103540116a50b5103c01020741050f4a464440e808100c00140320420 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 968260467 1250 968259217 968259287
    0xc0d080c010b01090f030b0406020c0316050f0a2003120409020d0b060313080705070504090305070312110301050d020a090914060901050606030a0e1608061512070b0a 73
    0x4900355050081040118400044031004c22a1040f0046490740000603c0480c06100103268494018000036141c2010324004030726590082048002c85402400401c080101c14000c01109800c032500030000d801c007a444100101e60040e40c007403804210319040049507101801048855100400000d071215501c01e000c5011754003e80d44807003442d1510144071650f00c3c1800a0b00d00400e00c85d43d44140c0411a59a52b02056200b2002515688141c010010b02a5114011a18028420355459840d5141c40c540a04100260702a0440190501205071410601c0e00252811203008036210180314070070b40003280030410036420420360981883c1c581b03c1840803a03101c003801034000a0440742c03aa601c0754101d81c01c030f0b50300341c1c3c550f54005010800721706d40d0340c0150071618128505606032403980740c5907881d50075503d049520407000c6030095000c02c1075480f540c1316001072001084d01c0d10141d590203000d215480d15264080d442d086d000204440105901c80c100200942e900e030b4005c2403403144035805c000c1c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 968261717 1250 968260467 968260477
    0x1d040608030c0d1b2a03060615110a080a1106010e04120207030305040e190f0903180b07291e0c0a080426070b0405150c040905090c0d08 60
    0xd036100d40c0d040015490b1040c2c0000301d4951500f190520413850707a41d120b40141640048a41a001c1d0035100703a107881e0441c1000d1030013148030302d00000300545082c001c000d824601c0401101489458a202034005034007094000b926980100701c940d07182104e074410b80e40410341e60590251407051000205024040d000400d0086001d045218a05a424101203a17502c24902005002440a100400c030f60398140c0b0307585401004440c1e0036168554500603a0b0116007d00c1204228580c4918400081c960401800c0d00e9441d004010440034038141440c1d07a49070300c0f0f90040144080c0215544612041c0c451110000340109051000c449081990124404040d0700c254011400c1d030140100d444451440d040703e413443c41c29102e0254582e25600c90b05c4070041d01407180094a10764480c3c4a0000c807901e801003841c0c500c10302001009050500380341345060100d094038001444e911041c07040d0205a10190743c01c40340050004070f03259035005030a505040044883c15040b8900f841e4400c00c10a41d880074107 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 968262967 1250 968261717 968261737
    0x40f0f0e0616090b16120201023f0c0c01090f060614090a0f09080a1211070b0f0403030902300c0105090f01030209060705010507020d0c0c05011d04060803 68
    0x2075041c2d1200426802036034100310410000c030b9404081003210018007005040100d03155091814004003a45604c804a0301303228219005035400907040409403140c80802010300c07031060384031041e5407450840300c605c080240102c0f0080e41c5401c00007104100c0d40d20498001c955134200074030038a100c510700504084c1d49014219256404c000b40414940310a1522840c0c080004100b44c5440d143c0305c0340c10000344100c035900c3c0505a01d40040c040440d03005401050408501d540e040c86c03440440341001c00302c3d00c0300c13090a031249104022240120f813070700012507004420359482d0002c1c2c1d140c507c0c0990040c001a64004c3d04030800b000400c4154001182c058013105001d03081c511021054004907844505444095000ca0020310240007503080c0043d45a03620b10045c100140384c000321000140254200c450102c2d91691602c00300482d055040c4080000188541060052442c95540b00b4484030391602480b410446004003058004183d03c180088090000c1e0040202c180c071101c1d1503490340e1142d0751034 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 968264217 1250 968262967 968262973
    0x60b0612041a0403081513061806051509010e03160816121a19020c0c042d020906070609110f0a030c15050705100e060c1215040f0f0e 59
    0x34030702c100c91250940d88a02c0d03055607290320950399440307248480401800b03215000303004400d8003061020703130744100d2002c1c001c507024080c3d0150070400044150381d040e03040680187c401c2d403c2101d00104000694411070001d00b043c0001095040105e80b0302210303041c0041c02e540404200282000010568080700003040c0800143e1644400030300b00506c0000754028418410403002144140100a52039008106420b00c5840c402201011106903000f507544085a60400c0805451a103003503c50102404850042c80c0c1e441504142d241c0ca03812075280380034402940000c0e1091295895004640c0110b601c403200300404507607414034104510b40b5022041c040c0b003d14070380700c40c0351400001d10030803240d0166090500c18140b07042e1b481c4800e501c07220b203001d00c807050254000094040c8014041110a141c0029040e0822071006181c03031400b41c440344203038104112411306d403800034a03055409180040705100400b6002c0c046001040c20102e42e040b20742c6003c1c1d5044200e9055040442e00c12560021 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 968265467 1250 968264217 968264243
    0x904110307080a1b02100f0f0e071e05061b030d09080d0b03010b1e03120c0a030305070503060105070b07020a061118040e0312040507030f141b09070507060b061204 72
    0x201307010f10740902e10720259125481034071542940d50070031004843c0035078020030410142c24560040d14012481e0905a80018605019083c2580380d00e00c81e000c581c3e174510748018900300c0402c6c07451040d44001000381c0c0d20140c54100705001001229040504003108002c006c00c103007020311940c1c01003200740400500b84180b40d0a5443c050044425a14005046450300032401940f455500030301c1300e00c40c0d098040d283d80501c0e1101032001510804e00404e0180500c08403d00d00202221001403d0105100c4103006001c09030368080c0c141d03003006500001310a01510307030050a81c138028401c3c100810107800c0c50134130314814941c1d070301030304040520030710582d20003039501d04000c00c0e940b1070507507414030794803d0058800c1004807550071504180075400b034950080d1030741c8400041c414400341c1550307c1d40c40740c0300141e4004070400030040313a01c0b103c0751081180b8010a00181045c84050002c808204002c40e10400b44109640101400d403401070615960b01100d0650a040c804225010b680c0c031343e48000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 968266717 1250 968265467 968265491
    0xf0212031e0d1b0f030b190617100b09101e020106050f0a05060904110f22051f030f0f021903111227010e010e0c060a0e060904110307080a 61
    0x700c0244545158440c103215071103004d0b04030010001c5041d09030780800408040503161444a007100040c4c04c61396144041d20f15450400742c44017102070171444041c040104104010b200ca00142c8508040440e0040d0f4440d040510855030074010000341071000c1c40d40c814468900b0b40540c0303c3c40c1110030544810b10b01c110a0b004000014940c0c0c4280354210004000ca00d0561601e58000c00c00308c801050481d0030f11030784800703001c0c1a0f04190040394a052210300300c0300d24100c100c5841001004216265401b810010044201d22803074804072005058566040088a07110f0350040c0c10010092682151205010803544a21803072440f083c0c40820b103450b0004060044d03000845000500c411305c003042540b54503061003d49400b0032110040c904040c62000c0a41d54280214000300949030000310f00881561200f60030565903c201c00c1c4035140070403103011051380002d07250384940c1040340d4464031120401c0100d0041d2041e0040e40c06030031000000c205c4840c0c0c2104504e40100030001c01040302c0aa484 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 968267967 1250 968266717 968266751
    0xa08030f0f0901020304120f020a0e280618020d0e03040b120901110c1b0303091c0203160b03090609010c080a090c152106030f0212031e0d 61
    0x820100c00344808004181e416910800140030103001803046034075042c0d650074001300d00c90400350115500c0c0682c803600019803804800810152804d001d2a040d64106100c04500d10007007000c00c61405001343c0d102500b1247c0a502c410018010144aa003025509490b030a00075403114084000361880d041250340300d0040001900c00742c0c4e511300081c515040c00394074854450400101144e0856480c1c1c0605204040d4441c0034113118030b88400107140018001d0005900200d507410554001e8bc4203129242c055030302c50240403c05e507540c0c0c00c00d54900300f80d400072a044c400c07005401602c0862810300052100c00c910015842141c80c41c040e13030044c4c0c0f40c4504542c01d80301150703034880001d2181804644202150f61103080d21074491032128210540d50000201150744404414000c1080c54000340d001c01507001007105101c407410800c00402d410340c2d07a900d1990503012400b9000f0300580501e564121010000c40d9072240e69040c544214900c5508000104d500c48129038049500b02032403004c401160f0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 968269217 1250 968267967 968267977
    0x1120203060c03041106160201030b010215010519050312030916030b04111207032004141612020c0d0f0309030e090c160b040c0f0803030103030f050c0105150a0803 72
    0x4014148075103a9810282043d040030f002603070928590080ca074816580c107130040c0007407400c400340101040300c91300000d011030701d03c108118159000703c03c11103611190521001d06640b03003280c410741c0440c56221400342d03403a82608820b415208441d0001d03614120348002d0f42c807844c0001d0403222a407001c4c540c500100038091200401c1361000b080401d001a1550441c001100006030100000c0000c0700300b003c0c41d0101c0f581c0107803a681c00e02460f40c2143d0b54480003071500c403101910103103c0d0109040d5002c9402c02700403d00c4e00c21854280d140c00101b882024142c4040d82949000e6480341c0d0800c0d012612000362001c00c0f8041900000c00140090282c007030100d2032601525025110000d01060103c000c000420300d2028080401c400e49085103505454404103020b0b1501d90342c50300c1d01e803820107850078041e04013841d0139a417820200600c40c0000f08580c10350340c0c1494220781d120340c0120107442c5070044100e1458a0350810041250300d10350160203505041c1c0c00c0313883d0803040303542c1d000d900d442e4421 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 968270467 1250 968269217 968269219
    0x609020405092809241b02010b0d0605100e10060306172e0207050616020a1709010909021803060f060102070b0c0304031b08010e032505010e060702010c0305011202 72
    0x418000c0116009070304c6088214010f02460300300008920744590f1350401104200c154580d1100600080d060003a1045061016800200003000a68000440c112881d00004019584520014803040030b03c40c8030500405200480300d4090400203445541c0300c8050003440002441c0010004007031320b0111005501480c8140600114868486002c154085518a07142c200c1d0313070080020310b402c94601c010180c55000f400545542d00b0109007150000700100004821540140040300102c3c280c10701d0788502d50400105156501814001610004029403115498a102003910110340b01c00e00421200d00784124142c2701e0b541e0f914032208121a006840031070041c0c0c02200144502e650a0008281855040040300e04040d034a544800c00710051025062a90000e00700030040b14409000d1038000e4404040510706080924040c1c030800200c1100700542caa81c4101201e041c4242940202d00c1100c0c080c041e0f0341c00e4030300703d01d019002e0482ca0f04900e00082c5462f000050719108100c50701d2555074 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 968271717 1250 968270467 968270521
    0xe0c0a1427010c0b130b0f060a0e07030605060714010f0e061302130f1b2c0613030507050f2403061906020a0b01090c090303030e030c01060902040509 66
    0x15640480720011064961141e061220303012450010500b24558144108955000f1040c60a41450010182c2e00042d09001c1d04184010a022a03682c0d11017254064402c101d280c81c90340e581e03c020032006002c01d80e1285400903400101e800910803024000403500071494000c1c401c511405a10100710b604050080c820f07034000001151640c1600c2d2000c1036a180001c3c18040c42c80c1c6d40c1811103085902245180618641d00c40f10654454000a541904250941410710007444490030542c10781003101c0d42d05071284d100308410a01030751000180c88100010010300001203440e403511940d1601e00c0e002d064410300320041f80680c207290641c0750f1100c6446071420800f443e500801440020f80001d80081d0303003c1d50403c0080c83c49000c0408001c02016244d00608401c00a801c080110ba40c040e004880c100e4181030004002da60410120011280c0c18a00002e5280a1004c00d50460064001e14070303080d404c084d40065a03003642c0c3c02030005d8550071075819480da1561355009440c0111100c000700a10 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 968272967 1250 968271717 968271757
    0x30709081b062a01020306040518100b011205040b09100b0109051c020d0524071b050718060f090605010c061e06080a060e1b12070e0c0a14 61
    0xc1440c0c00903004020f00f0300008085030300a8082c43d6081441002110380980d80032080101c0303450032303009240d0030003025054400083e2a201000d80c443d115004030038a681d48036920341040b070344204c0010001c40b11707881042000342014500000c00381c0058901d14264801c0c030300c42041c110034038403504c0d103c180b05031120038480d40341c5804c3c000520000e000940b003040a000314000541c5038524a5801c0300d00c510040c03c04c8100001c040c4600d10a0140011284407444040100d19508040303204094100140d80034109a044d150052500b00c0c03640006c030000810b6556000540d0941d0001c2080d41c00c0c04913540f8100751241c00e140c0499480e441514001204003260802090a907441051420142800e0720041c089201c04081524103a81c4450450392200c0c890703400f03000080c403a0703466004140c406401d0b102e04000b41c4442c10a041c18180d4469400d0008141004404001c030400604c41060450340380d1501c140d01240f20b41252880700b001c150f030301510403200d1100c401102d0301025018000d217940 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 968274217 1250 968272967 968272969
    0x10b162a0f1503050a060518090601062f0a1506030308130c0e0405010f0603080304060f06050609040b0316032a050a09181704080d0504080d0f0c080301030602030709081b 75
    0x2c0c2402400c80ca00302c507038501c1b000c507050b10390f10b072800031a2011021164031420301000c103038600081684010200100580380341800601050345460003412510a903460112410200381021803620000b051485100c10090b440741554111004480c0203031203540d010b0361a04c2c900445011213500081401440c41c0080c8440c007100c2e0702d1940c110303014200014a9146500400e011905035030815038440e4400310801041140a00038003030616010f0344280f00092030040071517440d00030056100c1c420390f101d1091660645041000e0211606040201eaa04655038180600039990320800061600c5079074900704000d52000b0b4200c0110398014101c15101807415005d0001090025010040c0346820150500803400440d0010780039a61041e01694683c60030512034a4028405021801c0c401d040c48204100b40c00440c903c40c00005038200000c08400300b20040b1160000104000d040280c04400401402401e81c080c40c49a8025107503114034075151811036640c2c4950340740c00d00700c07502c50b40e0052030340b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 968275467 1250 968274217 968274221
    0x1c1b0c0b130c081b0a05010c170d0e010516030b0a0608011202040222051c111e060706090b060f030a0320010c03151d010b162a0f1503 59
    0x24140910010103071561106045130510400c0c01c4400c42c1c50601d800e8100c0c01e46400c0d203007000245000d09003405140c0c4c1c15950317184a1000400e8001040b10301107811805140560407c00d4461035000082009281c00c05600150079042c41c40c070700c0000c0c5004550303525420240610740968001d0340710b40200d84e1030b1010a036007107031080300c003241c2040e0280440700154450b08516007070442045680c13200f1908210920141690740c0c01300c4107034000074950f40b00c0854510b0501c01218041a120811301000d2180700d0340c0e03040c20203030003260040000680c1809119250380602481807080c818034450b51118010040070541800d01d196242c0c024510180020b4000c00741900c80c1d10744880004800c0c00c8003000c10f0b003101c0c0e1404007c80485c1e00d83d0390980002021818141c01b803c055422184107054126500520003414040c14403107040000c1d072555450845039158030270541c4000c3c0d40c84640303211003004441e01d480c01d10003102c0090540d808130720445c1d0708800c08251411920101d04a51a0301c1c81140 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 968276717 1250 968275467 968275501
    0x1303060b0402132601020a14070609080c0618010501050934120e03040602030417160b1c051603021b150106080f04020d02010c06021c1b0c0b 62
    0x54415403c1121070048602c40c0045001010b0120b80203a84507904504c01c960004d0302d000b525980e9104100540145400081d05015004201c40302c9485040c1c80c17400c103008000d0054040c02c038040110750f0000d62040042c86a11a510065000d80400c033504109420703140d00f030169640c0700240100051560200c80c50b850b52929041081d00720b80c041130348213142c0300d40d0902e0384500000c6245041001c00070003070113a035030750140040085240c035250080094690280380110120141c040b00b0040d034199080140c0c00010103620000090290784a82401c0b441d4003000040d85225441c01907400107085900c102c6100d642d10045081c0081c0b44250201e00a50040058086e400d40e90034800710a10300c10400800e0040321000c2640f55941410350182015800034182280ca401034000c000058a48481d49240b4547c2800c21403074500c290300d442c2c0081c0c01100051620291254000c1c40c010140d600240380c0700401e21800b030000074080310200c8880c140d08d030018200040400c0810384034140b07a25021 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 968277967 1250 968276717 968276719
    0x50a020c071202031011070f0c0501020c181308040b0d021305011b0305161e05150907090f0b060307092912070309080309010b0109060f0c030e120f010608070504021303060b 76
    0x11307141001c48d40e00d42010b440b0a507420745400540c90000d11543d60104003600203036a00710341c8010070800002c0401401c070402458980303031808030b01c2c0e407008010071001520050200c40038400d40354015102d0310341c02134000c4240e054a64601030340024095005460260b5605400700300e0070306159641e1000c0c0c5040c0d0015000003488602c001021000c66031580c0b40c064182d5041c880d05e100421507082c46464407007d2451821421509401d10000711000603112044500e004404a2551244001540101010360445420880002c00c1180c06913001500000351510300034103418210f0750410104200590a41054100104000050415484c0e04211b540301242d4980890400c005540c0c11200760803d5482c04900d17074440c0048101981c015814101a01c1d06d45805640d1805d82c00000b40704200e450006800d112280340b10b03080b1515072503580300542481d41c048941c0da1000c1c03d00c2c54001d02140c03003601f13840d0041c0d0170301261518140c002c4505015000d0160465076040d6158031005003584c940b05 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 968279217 1250 968277967 968278001
    0x302031801180603090c05031501090c1707020606030f191412070311010b03010b1804020f09090a0c150203120a1e06030b0601182304050a020c0712020310 68
    0x42e01410311481008000d41020740d0302040c4400c070383c6000b048146007038111600c6030300000420702801404000e40e40c1140c603001d0703003c038442c14105001c1d50002110a500c0240022400070410030f140c0000d801c5029500c03d43c2200c109003240380c0460307128007154010180c220f84128499000c65405011406c2e15100340054074080c8410400f4030707090350b02000d030490203d4030148506000f0b0600f13103c3d00d84038550030790003030000031451000648080703035800c0c0701850300106101050664a8842400c00e20719005058003661b130814180107581c80105040840d4603a03404031000c20a094280e031302c140d58000c80d80045040c00100c040c2000713000c3c07004040c1d240b49a13841d0000e841700400f00d00f032024640891280002c0013811800c00302c0d580c000060542d41484031040060804184040302241140c4100011803410b032044c1c084102d1380c103540043c41e507000782071034240b002c141d80c282c2c020031200070428100c515441e1744218158200601141c040e505402030f0000703401c408049d401400300c0c0300c68800e41d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 968280467 1250 968279217 968279237
    0x1009051903050d020a030b100503010302090703020c0102090307141014040303270b0d050a0b280504020d0c0e010f02030a080a060b1801020105150d0602070314031f0f030302031801 79
    0x44004036000404601c000a49407444a807103070030207981404108c0342d1858614590347c1140c010401c00342003d000a030803d540000e0401550400398103940c0c2c072220040a540d13201d5616040c0810561028020901c07a0a6845411203854000c4020810700d86101010900b054a15242507856034003080c0c031540d1290818900b0460b40d40c0b01880343c00a005003400c0355807103100d0030348500122400204841c600a184c92428070071590349406a60b01c810007030145c020144011300503907102c24048d42c8440e40140c0045034020b4000c1d0070782c0241480329400d0743c40c103800121420046031070300b2038500e11601503001040140d0006d0300c1001e01680c0010031030340214905d40e4419180c50103500112000300040031007000301c0f240c4c0d031f820301036217810680400420702116040700000d04c0d940c52001d40144004e40c00507403c010076005080800c081c945540343c107522841c28502c500c411105100c0c0c01248508034150120341b0b017840c0501c12090b203415a00450a09440440d074a045d0304041d11614140440050 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 968281717 1250 968280467 968280487
    0x1101020708060c0706050709081c050c0106091406040c120905011503030f030605011110051005090103230303070c0b2505090a21080a1701060e03100905190305 70
    0x20b5014030f0010030034940c2c0380600c0c1041c02c200c410140a1800300719400804001e9500d001903440e01f2101512520b1100c02c1c0480d1090b83c1d944203003007000c0c201d135081c030100080340031842d40300f80c0042407a8440302c3d0180d82d031401004201d502e201541e2005c41c403618010010250341c1d50114200c1c1c4e1180c000040e036000891003842c181501c87d030044000074070800050100c2c3e40d06000b10001450f0a0901d001c19503c800056a1503110640b4841c03038150b030f1540001d14a40c94182030030020310010340b24007101d58603814150318809115078070f901c200b6040c0402008942001049910a00c115079440f0241e02460f62040f41810780505001d1450100d140508010526281703511114806034440a540300c11400c14413140c80c030f60f9032040f0402c404001c0c80c031f00c40e44010001601e0f0302d688003103015628141c020096070358100c158000302c0a901c01d000045045074001c0020700c04c4181c11000c890f11004804106003d5400040d00101143c000c403010b40e41a02c80074442401261003400c1160514503120 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 968282967 1250 968281717 968281723
    0x5090f0f060403170a0b04111b06041203090516080d0f051204150f140714030c0d150f0602010f0f0203360312180f0c0d111806011e020a1101020708 65
    0xd15a809940c00049c0d0b07885141c0b0202c0007030207045203080900309615280c0c8803060740300c9200d0f100b08141500c55030508200801409440342c114000c00d0f00120040d00c0e19405641c49800040c1a07001c10751203003991400c0390250055981000b2001e050410546d03c680d10308940040c011004040d1a403134600351000c0f1003c0d40151180b090781b1032700c0c510851818030706c000d04041c040780711018010b00c1001403100c28802d00c800c86100100044001c00d00301070030044510b442c0201e42c4030311300d40c50f181d42001c00e406e40e041d00501d9042c01086000c1c441c0c15851041c400c00c9100a48000504110349419001c0c0c00494112058070854040c40d4129000460000203082d5071100000034256411070342004a082900128038007100d000781c006100f0502400b41803607481200d081818864407013000e0000030800034080c810324050002e00442115010315194411015054403d0741c00700341740c1c007a04904081144c92114007018980c0c0284054103054582040340e41888030001c3c1107005d21903000c18401020 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 968284217 1250 968282967 968282981
    0xf082a06041b0330090503060a020702220207061109010509041a06040e220b010e1306140708010b09030705061b19050c040b010e09070309050105090f0f060403170a0b04 74
    0x10400e80c15482c041301c940013180c100d450742100500c6180e9100b071060340c40005502d80d1100084200598402040c0005980304202449502ca991006448d0181658450b0003405002d4400c10040c044007c80011042250007100259130010f0014001c0540504d400d8000e021000032100d00313096210440004601c1691050b0040300121039003d00307100c2500c0401d0400e5070f0441862802c1d480115180d591340704140d2041c0b148901c140750b9040495031071031901c0b0407175005541c000e0b4208091207900360301d4900390908542c01004500c4074030001400c0403242c011200400700007000303000881d00701810050360760000041c002008450414100c03083c80108115501c130031a892840c5002015860304901c1c0201d54481300c1c2c0a1400c048092500c0c0e41c0000039111401011983c1c00800d40e42c60380100e000340751440740544a507090500740130502d0001310301543c4071072518007600d03084516031a81c5c40e44ca201c280c80003400200100700c01e10f8140041e00980e5084200c8201c08240c1103850000102560303d0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 968285467 1250 968284217 968284253
    0xd0b0a0e0709060303080615040b1806030a0c030c0207030302062a0a0c290121050a0b070e060c0c060f04030605070f11010e0a0215070f082a06041b03 66
    0x150f80e03414014140c00141701c3d42d00040444210030400168116000940110312901062030000b040d1091400c00c60300390503000036000740500b61a40380c07031403515000c2e11070b120702413020a241c0500e4005241c404180c0c803058a4040d00140855111110842d081050307071000c0ea0f4100d1f03000e003040851351042100405100901c0d60301c2c604500342d01e04040361040040c041d80c0850503040003110030340030510381d251411209682074034804580e1046001c030384a0100c00300200140036008000d420007141030310315405082c403a644c0c1c080342d00b8408240800c9102c0d0303081c4c150040d4054401045286000401011820b00c07850081d81081d98a503101c00546100b84e4030100800c800444008405078841e49100c8061003000c024054181400003443c1c860100c140d029005145451040f506031900604a840b4554002c0030551070100c43c1c101210756400908000781c8444100701c042c0c40e00700704000e07100150400e801c0034100070740307c541c0c0e050113004174440d83e0301084918241c0000810412000c10181c510 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 968286717 1250 968285467 968285471
    0x31f030804080d1d0d0305071a041203140105120f07080f0c0103060312080a02040b0c010e0105060f031c02011e0e070e1e0c120915070c020d0b0a0e0709 67
    0x2c1003495aa00f0711400d19105020001d20382c40f5611490710200b03452100380415501a5020012414200c445100c2d0315806000c86000510f0700c088010b40317040161083d4002c140d000c01048990308220140c644c7d1074540a00300d880d550050001e80780c220140f410000845e4225038000c01c5500b030260620401c0e81c400585900701c003d511910304818007543c180c048003440d040040e2400c642e2981c108400c3e4151640400c448140040d5074002d03550304a0340034259005150b0380b18465001704172f0280190000407042542400701081290070300d0b65a640c2ca00788000c01602d10030f9250402c84d000400030341c40507401c5649582012560001000465122010b055008a4601c0310418070318500030721b50707200d1205060100200081c1406117000b017806049003481d022000d0300c4540d00c0040c0c9020740c18120f0794072859403090040b02d400004507602d807842d40210800c0907070340d01d0b2802da50f01c080f00300001e500090030000c80c070001440ca268840c1c0c410090000042c00c0a0103031000b502d840c4d5250400c1786019 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 968287967 1250 968286717 968286719
    0x30f250b16020f03040b0f131701060f0504090f030f12020a0c0b13080a030b1201050a0b1f05090108071101050408030714090a03060b12010c0c02150306090705031f030804 75
    0x1c0e03060040001d41c0405000442c681458002007851034400c540254107c00000714032040c200d001900b07031900424001500319810500c180809000b490b144c480d0826090003000c000616042c00d00890901e40d030051043c6001c0342d0140c5098903140c506030022820401d10100c0d0070b0030304038244003a000702c03540e40d6250480030805103001000240054400d400062119140c00b001035541070440703180240c01d14021804a030003902140708800c082e00b11103041d5080004200c0c00011990041181c89000c50740901c0076400c21482c4039448c050b032068240010400c00c007020b00340d4080d11406400c91407910f0b01c40701d69082e220015084610507074044480650000c24009420352001c40071100f400da0043c4186000c0c00080090070704021440010080c9444890600e0950340e40c1d0740041004001320000d004510034400000e0000c01800b200700d00c13030905c00c010302c54440c504400f541d204800c0035010344242d444450081e42ca90b04024074070340b04d81a0386210b02c5a04811401c205000318031403510140c40d2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 968289217 1250 968287967 968288011
    0x40c06030e0318010f0203040503030414031e0a0b06010e06030f010503240105130e03040b030405100b0906150405060d0b040c0305100902030919030c050f030f250b 72
    0x7072849801e40d26082e6005002414008000041d0003280007001d0802204500d10250107908600842e8051503260201250010380c0d02001c9070880f00c0900c080341900c20301c00c0080e04146801c440c0c2c0780a0394440d40070070417080001d0300701c483c0150007103014100001020b0300d4070f001480c141d00c11550110854460401000542410040002400c80b0818101c0f0312038400040300f4580c0b001441034510495480a00944002e03490344851041800035080c0d0f55581d840b680e80d60025841030f2411034140c460080001220112441140700368400200000f811742c0314541009000110001d00c00440b120420000410355550002803400100c284004181c0502010800049404030030526080c54140010440040e8030050800c0c160b62280700016101e03282c3c4030075075107018060580ca840907482c03480c007141410782081684d4000da1113182290360f403811000c046a160700400d015030000b08018080c0040c0401031a269003a4048844500ea901d0001501d03580c14150081d9089200c0d00114048000c0d8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 968290467 1250 968289217 968289221
    0x7020f0909030a03021602060324011419090b04080a020405011226070c0e0a0c031515020c3f03121315240503030708090315040c0603 59
    0x42550840301024a881c2004a050300e074802d0750080360030190300241c1c3e21064480512a00200c607000383c011a12890403010040000740300300b440380307410301034003002c060150300c03403030030603911a8003103000c80d0816180f4107501c240250241e1400040c00208540855000e078000090300040c1041001480858032070300510048480c10381084242d141d0110103a004100464044a90655501341d038030890340038140c7c5c43d0400c0c050340034018100d5404410019103004820310290080c0c106880c2081841c240950075000c0341c0900050340c445001040c0700f0000c10503040701d21500141a401030300e035a000c0794000605091140e41c220030803240c1c452658408a030008110b1264440d45411181148481100b05030342d0f030050a20302c4400040b1800082d0424031800d00c40300400b540046608883d41203039010502400911006a0740e5581640030540c0c00d11701001800c1c116000680550b00d000c84a40300d900c1d80364171511f500b0780c05203e04608041101880702c45984524010005500c11504007180201 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 968291717 1250 968290467 968290489
    0xc080a1107080403020d08132405070b041103031c0504050705010921021201050f040605060103060e06040e010209030a030905031b01051605070b0d020c010b010810090c03150801020702 81
    0x100c440c4091000354002510700341241d0940e40c045809101d031240c54074003440b1500c0340c5c2ca90140201aa424002901000d50b2080d80140a100b05025402d000004085501c0c0c040d4503c0541818070240c04a03001c82c01d401d00e603940c2c0642c0942a01c1c500003900d2010341e0407140001040c07445a40c0c132403c01050150501c0240040c0c0001d10300641c04500d84944c2c80941024103280b0441c01c90300c01c0f07c0c1011569901d002c022840a804000e000070315103d0183c2460076001c50702507070301500301000030741c5a601c40d120350001e40d082c02c1d0b050201501d03400c00340001440c001d954038040359420070451105640c200f21070980703d40b00755580d5141500341414142014200441d22500c155050030079074140e03811406944100e1041c000030207503100300e414070525004a0b6808031591280000b940c0001c0c0b80181c0060142c409100001d1007102c40c00b000440301902d00f250f044508032404d02003401810280d8001c2e02c0c100c5160302d0b0110b0202e01c40c400300a04000c0d1603000e4505030b0340c001003c2e07007181010201e8035 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 968292967 1250 968291717 968291741
    0x3004111f1d030f15100e070f1d01020a0f020d241109060d0e1213090b06040e0f09010b1003060305160f0603090c0b0d091e111002030d0c080a 62
    0x10804600d01207401e40d49103489130070b40c040d40d0012030000f50503091040c22200106503501440d4a10b00302040041c1c0003050704912400091490500c040803030818002018813108182e004001000b01501c1c0e50701514619201240e0040c48510700401140c808420141404001c0c0c882c100c48010103005d04085506401d00d45190032401d00c00001255605410f844005d42170741008548042da03694a02e0078915485c201c12000c01e0080340b08550b66010801da442900c41f800070800c0b4001d00c0c41c0400850780528802c2c2c0f840300c291980000c201020b0200143e41007048074001241c0400d402002a20f00d110154071710000030b41da2038080051100c1000081f1800b141420202041828000200d0407080940106020705445490342c108010b0300d01084030007009201440c6882f90801610f20018161100d402d6a02654040d10400c0116107010001d685aa00031803024000700b100b4113111081d00d0762603c59056010512030109002d00502031072041d40c10b04e5543e10010710303040f21b0b400115440342c5840c0d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 968294217 1250 968292967 968292973
    0x70b0c090d143c0f19030c05070305030a020f0c09040b07110d050901030c0206010b1e1b0615010c0b0402090c090319020a063209060a11190c03140c0d0303023004111f1d03 75
    0x50751840d2550700110303400039008141d02c0c20f50386c0d8415080c4d48001e41d0303015c1c0a0081c80744061408040364440003800c042d2000340d81c28000302d100300000b2644d501e4280141070280c142040003240400301070f003249003000400601903081c44402809901c030340081014100a6801440410500c209210228500c0a001b4282507440d034540d40c0b260040d81c940100002d01130102000800c024940b48816511100310040480d030300003501d0600040080d5898900320700400c10807001080b039038003401059952410100b034070285894150b16141c06030a400c04400e40305101080003c0980d08c600c0018000a0082e440b68640e22081030761745d0340b50510034134409120903c104407140000d0700d103400b5141103d81041c0c0b040001c0301d800c0c0305c19041c680c0440340c00e503202012800030030130160160050324540000c40800e6040d52404d03104c62003440c011060401d40312501c0800200011041040c0d04c921450207000381061040d00c104d03100c0e44901840180000ca4406114002c0703510410441c1c141900081e000703 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 968295467 1250 968294217 968294233
    0x604030311040303020a03080709050d1a09010b010f1421092109130e070305060403090501211e02030903070b0c090d143c0f19030c05070305030a020f 66
    0x100a407250031246d0024100050100424945441850030384090034000b003048006002134074103100c4848140411103045030300031001440e052010700c80c0007803549042e1503441c2d4807012100e044880265110480c038070554140b00302c00800c444000300504185481c04910303414280041d07010f01c4d00403000060b07618201c40c0d5070030f0900340c1d020800f5181c62060545c0c001c101e110007180c4200c05048800d818605a1041041c0041030201c00a80c0034007a031b00a0320b40b6000c06031114011503625094403147c000200001d05a203400300c0c2e9540c49036034082600360402c58070f54160307184002a80e0050710115011b502c007141c44d0050126510b05c00b9081110041c24501c0d1401c640c010070b03201c620149014204101d8887c1140c80003e0501c1246d5825084400c04041500c03148198000b040240311150780c20b04000c01c0402d0184d130001044118248880020910f01101c100c3c02c460304a10728004030b0802001280e903100003042085224060b41c0700380055074a41d241e09500134504251031a600d03145600c0480 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 968296717 1250 968295467 968295473
    0x5030108010f09153810020105070912051f0b0307060c0b010915030b070906031b1d010e060d050103021816030c1106240d030e090601090503070806040303110403 71
    0x60320040045500802c5e4510040b040d1100c071a1420216035003440c2e0070f841501e501c3c1041644d040c0751030b02111511881c0d840d51a0890883da011515000443c2c1c00310800d100b91260903040d0040e0610035402c50f00c8001c44407401c1d001000720300301000d11035621004101c0e664079083c040d0f000034012a20309108825031a0b142c82c440e6403030600c6418110390b910384100045040d000c858002440c0c0001c0300340007a08007080000c1004015214180009150143c142504000c91320044d42d14010740d5141c54140c2518651208420707034920b01c507030512100003103210307054a440c13010b0045820041c1e800184c542c075500501011132644030082c08a0760b1203008001380d030903a02040c404a04c00300d150004800c0fa400a098a0305d8000907400c180c1c0b84201c4041160303103961031f034440b82010004080c402400c50050140f00102d501242c00401180c65031590081505160401b2a48400305240c87c4420075510f8004c2820840e484d040700c001504503408010034944c140c02680c050302d00c40c0c803191b440c10349551 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 968297967 1250 968296717 968296733
    0xd020309060c07050a061106010b040e190e070803040911070210050f130311030c01030203091b03070306050f100506042d090c050d0b0907021f09050d05030108010f09 73
    0x8042540728000100e6104000c0302e0812004000e018064400210a030701c51401510407090044409810710030070002203048481079050394121030715180082d0054480c04070700610150640d55110100d03548005400d8100307030401200004004041c05581d40300d00345001303c0c0561341d801e0404d000c44c041c1007080d44c1c01a191000480f4516410b4074200c2e44501e40c40b009640b0724810358800ca401ca0003680008003d000600c40f100c05807000c01c43c100c0f2120440040190188c0c0012500404142c001910703a45440e4454000642103640080544800684954a040403501c0540d070a8030000c41190800003400c610ba02c8a00c00740904944003414103160090b03c0900c1c0c1d00c601401e00c4000010021418440d01c4484005c010b0a040e08042c0800140908010260b810469000369003c1c1490206202818226800750203501190b0150841031010407880000303000381c4440e1480315580c1c1c2c8030480802d07c103118000480f6403582c0c4043d80c0754523001d0101e0a41348059413183c50a45840601d200081b108 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 968299217 1250 968297967 968297977
    0x2e060f030b060904030912080a02061018020f040305151b130b1c0903020d0e0109080a02041e0e070e0105040c0801150201020f07050a0b0c0c030406031a041508010e0d0203 75
    0x2168210f03440d0380daa2404940094041e404010541141c254401c10000d111025100e001565821641c1a1303130703007000200711100c0520684400d42c240c5051080c3e0320340d207500182811800078004510306a543c0d52000d241101020602042000e02001e2040d0003803840900368400911043d541c3c2494044401012140100d1043c514030303e500066250321182e1922100c008140000307000c010b070000c1ca0030042d449410181c2440001106402a2455076002c0c0b285142a101d20f84c0041c030030b5000b1903007804010000d14440318001043d8800c41074000c081c0c0d020b10040c2e20745550161868900d030241d502c4045034103030821131040381064508074001c0c4e445444581116000307004880600c0740b10714260700920640303180614101c4005440c03800d118000899481c554450348002c070944d03940d03905c0c0455074081d2a204807420340041108000882c86504000c202050740c03002d43d4200404600000c4c21150b44160440c00c2c80740e05a820080900207100e01800d00d40c80b0030203040418206c480c020344a21803 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 968300467 1250 968299217 968299219
    0xf04050123060d0609150507020106050a030c091a1e09071e080c040f0f05090c0705070303050d0b130e061510081918140a1a0402032e060f030b06 64
    0x9003c3c01d542808034580200384075540050703030741c030500040c0e11020024000c222000400356090000000340342c2400e2901e002240d4000001c60b54482c2803501c400301034108050034000403014019000740d41e5580696208880d4a01d140560661004109203c00e1a400034044824420001049408000c16040c2801640d03500c0c40c040c00380d60b44e40c1440c11003500a94120481e02c8003400c00208003010301c800404260345088650521556400000c036880d80301c0d41d14003d0003034104d00020000a4024405022580040c141c04240d00640380007142c0f030a4a82081e0002d01e90321005c03d0480b0200500019030096080c0a03211141c6000d41c003c42d100c084600c020008014003040041d580c00c2c2880f01030740041c03042000a11541c1c0300810440d40c1c3c4d03050901c080c0d403c0a402428000118800645000060b034080082c19150102520852440030010410f903014041c2d102117590184c1c04011920031102280d14408400d80d402c3d0710a8100c46c4990080c402c600c1c3c00000038004a042d16092650000c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 968301717 1250 968300467 968300479
    0x60109020a1b030c1713151707020f0d120c030b090606090f03030a090305071d0112030216151403060609092d0a0f2f120f0405012306 59
    0x30365442c044a1612030740e0070103012000082c9001c44e024440d45c0040088901c0c5e80403049a0a4035a8214011740310409a42004561407160642d21100016419a400422401a0f89035510305054207030400006144c802c0c0083c103044404100e0f18100d200d101e0b01c581961404105103850313040411240400541614403031400442d001c40141c2c0c80c0707503145103071035009020b0f2902c80b0784003140980010100d010448550096140201c2d403420840020701c803034003048072000c0d041d91134510601086081c0d04019401c50240c0c021010003400744541000007800460420346c8000c000807001018484240d16000400ca010010304c03000356101004e403401030310129081310755510784c00403d0075111800ca0384c01a0660508140c87d64144207000d100d4891358001030140705c440340c504000022650204402c6442c5c03000d2032074404091190042540b04a42d01e5902030b032514010701d06043c00c00c001103529550400e54001003008103c003c0c0a01c0d0803010701001f000c0ca410b103d5058003004890010815400b90b0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 968302967 1250 968301717 968301767
    0x40314091806060f040807060905190303081b07030e01090b04060c022e0f030c050408061305030f12061201090c090e030417030306101b020103020c2d060109020a 71
    0x10f55102d0854400003203140002d41d44a07512801c06440320560720801010034002400041c1600b80305402010760564002c1070302d4110b0071a903046d04d5601000d030407621014200803001002d12566401052020f0003a112481000b45190004000b0a00c94021045848040c0710070800c46400450000d00c0680c1141c0507074100ca090482c145072030f4a070310b002d205d15003e5422038590042c0c01035a9401100b002d030340d0900c821520304074155414881c43c42624401e51021000640480b072000840c0c41c40c5100b8015246801060f00842c0c6207900f150107417010b1540c121040c82900d00d001c021307000380600104000c9c00849901d4440c081c02d0000c070701c29516000c2e22074062503001710082c42142c01600c40c1030403c0c3d994a03600b9020a540e07800440358507004020b04131966025038050008400443c0403030745107a540b00b035181e004401030b4004d56582161031042810303920a00307880c18010300710030135000c090000c0074441110035841c288041e44044015441009112030103644941105415072010085440d01 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 968304217 1250 968302967 968302969
    0x1403030a11131802071a160306030c0e090c122805060106050c0309030d05090127090b190e0609150d0204090201052118030c3403030206040314091806 66
    0x1074483c004000b4006c80a80c180900700c01c406801650052502440045510802da5010b40031100c00e4040980352076a4408200848000703c002181d014515601b554400085400400c40341d2807c3e0802e02544d8014015a5094090400440140d0800004000700f0303e070741b0744c81c0c250b01ca840c1801107408000c00003681c0e000d0004100111806000003508540c6419900340c1e000705150800d000203030019020a40d03c80112020701c8090038140b0840407004926440c2101c024002d0050180d06500541d14007200100013405c040d400004045440403080146004070420104040003030140014501412400055031258210044415419030340020144082e00050382c03103014441d10040803003004401c1c0403800d500c40341141c0c05040715440e00b8450300c10a040f030035124061488c844607030781c2c00100c81c801d00071962281c4210010707070790403194220140018108500840340d007064025034000c400340000c142c2e200f101c00d0019102c04c1030150415170301e0740000b40c803506100c1d0500001c4203580c0104600e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 968305467 1250 968304217 968304221
    0x1d060c040614210a1a090606090d0803090d020f0d08040f170a0e01020f0102090d15203a091401020406021b030102041d0903071403030a111318 63
    0x280040101800c81c80010107488030410442c11110080010304105000f2204070f00017000140d091401421900d81c1c0d034400302400b032290000c05520380d20090184426010401c210700643c0220651400351004032000350001e03182c4007880039486455806042410701d44d541c012a6150050380c403c0040c46101460b0400f00049000841000d0017598005283d0310704940049411401600070780985580066514a241c200d0080390b07042c03904018031040240028420b4280400200f840600019101c012590b8000720400501118070041d0703800100d60201d8200361400d081050443c4585242e07030381c4602c0c1c401c195003a1003500540340340d0b111003400b4100804810081030700e20844000f151150740e1414000d5840b000c65000d000c02403031403202c81400382018002c0b1f900392022480500c19480c5901c040942c100e038000c0a0311082e001c10b018010001d0034074150040384c0b02252000355280e0811081c80b2081711003041030300c0d0024000300299071090300038122403c00c68200c4194145240035007291200 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 968306717 1250 968305467 968305477
    0xd09050c04020315030c01050406021f090c0b0d0b030604080409020d20040911040b0405190305060106080f0702010c080a0e0703020901060207150c11060307020313091d060c040614 79
    0x54800e0000c020040010008518441e6410017241160741a8a01400540e502d124501035070006822016020b51a03510341545210903070150400054000308984030714140d500c040d004441907030700008040c0f541400c1801006000007003140542020308243d80c03503a846108a03c501b072005600401c41c40d50031801c1d03a108010410000c01d20740124500703400500c0c1c0c103038824064280c07050b141c0880303106920740000940381901c905294031441c0c44d06120402802c6400e41e02d03031460305810f03000080005001070240d00e00a04954960304014113206000506643d001810803046a1402c4500b01c11581e0050103950010180f481c0002c2080040b803085040c1601030300f001e504003051000005109030b00050b40d504a803403030013811502c2c1c0700c8080e00b2100c500303802c4006030802200c041e0801d110f01e004801990050014011079282943c01c1c1c1c0d140c40e401d0000e50002c21003030b80e180c803202104140d40c800c06501d150b150000d0241c038030302420f50b681c0c80c0c021401140108000380d858040100081400c0391 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 968307967 1250 968306717 968306719
    0xa0c030e06090d2f21030c0d09060e04091203110c030c33060103020d061701090309092901020c1e0f0603160f030b0409210c05030d09050c 61
    0x1007600401130414a642d04103032242489800d600d400076000543d5500306504480600405902070080100c010040154080701400d14074002080b09208501c810003401b901001c1c1d903241c00020500e03205001e0b2218000e0000c0034011828a800c0200003030440d041494201054140000d00349500d54211441e4013400040e407880344070018940c0b032040000619140300c2c2d82d80707a0000207181c010501e40e04805541d590040103200c041000700d425980260050107078640d01210006682d5921303071002c140014501b00842103030b59138a1441d424198082c0340d0a002c0d00341c040080c040d65007134015030710001100701d1003401c603200b6807128219660b02c2407112400c202d40003041e064a403103004140c21607034000301d054503100300c0d42c051000c12a03040c04c5041e0317413064002040036104402c80c0d035410380d0400500e440010815a9600a40f0f000340c1d0f0b10b20a440042d405071210210b080b03405203d104161518004560500600b89200000030790004204c401350125940c0202d030303090843ca0310a02d0042c540f6801 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 968309217 1250 968307967 968307979
    0x108070201060b0a030501031e03021c05130b0918060303091207050315010e1b03040201050c010615050c1009240f061401031404020a0519092f0a0c030e0609 69
    0x1d28145d41a008181079a00568150315080010250010301101e1000c000740560004a24448c486020b0f4118000d090404e081480c5481941d808107102c103041500101e941d804082000740e9030b41090400400100100903002d41d860400900083d942d024008042e031082d00d240422000c0b60f10240801c4004040150403208440755124081d410104240252002c04005400007010604400c48146a076070000401c5442c5440c0c58004503203d61010898041940d02ea11f00052074030861500112840641ea840545511001126a0601e04403215403496941090001404503903c801484407400d010160300a82e8802c1400c098060240d445d45074111a00e0104001420080030508080060090760208440c2003404840fa4800e0019103001e5006440040d05001c0d60030700300c03840004800fa215150814a80c3e62205400b600c0407051940305e400d210101d200c2c822080c225a680f4480360030200241002040e500007042610070b604042c0030458140c00502d09911094221540008003403c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 968310467 1250 968309217 968309227
    0x906071e0309060c05041d0c040317090d061d0619020715050c0d1b080f060a24030b010203270609030d0827120309011e2c0c0108070201060b 62
    0x809170032030300036120380402186082d5a400e050010018a0362146001c8a810b82c101400d589550b0b05400141c410080080402c20118596035942c0e040032a0440c402c40010a19241d5140360102040c022044514a9072021003403154410310643c1582054550701070040c0c40c2c18482c02c1c10042440710700c207003002c924a00010306c02c031a61110010054901d40c80024070000c030147d0ad00380b030800e0f240d400c00e01c001070008001c107203101c0c0e10a43c820380108000304000545070311404c042208102485400443d8844514100c3d40103405000f40f0020000074000345040c00a4907032117941c6d2440b60f41828030303015001d441c06d44442d0303111025a500c5250207000c584181d6031002010f0180d400c161902000c01841d801c141101c19802c07412032050034000c038044d106414001c4181b148580020300030350199500c405803184020140440c410305080d12480101d150104c40b21300105407040c0c140c03030882402202c0980540204001500e0492460030318088550f9502d003d0704a0050007075030018000401c00082e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 968311717 1250 968310467 968310491
    0x203091e09010f0e0106053a1a0a060807050f09042d0510081504051908030708010509100611120c250501021908040e1006080906071e030906 62
    0xb0510041e1003044140e2443c0c0d0f621080b05403280e000c1c401e0b100c10756902c084098080e0082c2c2840142c0481d0f401000c01c119800c0e856280c5003507802740b00c03030b0b04014200015441660314105450b540100450f04103901d641c0be007500014468420554070101c440750000d0160f445446a0703002c1d040c84030304415075042d04800c6448400014084102c1744800d1424040441e0400d4142c3c400c1008071141d003001018503400b800708a0001c480e00030000c0d5810300130200d483d08507401d00300581000c103220740051a901c0c90040d00140040304103810031400b41c07000004000c21204950b0b0302e03805032082810300042d00004081c44618200b90034203082103803500030030040d52070b410000ba0482e10744001c150060800641031030507802c16555110386030043c0e124495800c02500b2840350001c2c2e150051541a240a850301200d1461200c1030700c5645880342a5502045115032203c0c6080c1c0107a40c1c0c5000e0b210606104d03000401c15079a101c00318610034400c2c241201014001e500c04116241d000109001d4481262 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 968312967 1250 968311717 968311739
    0x170c040e10030804141201060503060a0c02070803070503120f010303050304080304080d090b101202130506012c1804050c091f030b040c0f0e0a0914190c05040603030203091e0901 78
    0x517a110b0040090704100340441e24107000e00001d6950290040910380c0d6040c002c407014100e40d04802056009080300821009070a0006212860241c402103075030b1002d8500500701c140008008001c03820040005000007544501143e800a400504150300c1e922a818404054803030555100341c1d0914000410040080c40c8200d64401c05101e010f003001659030f521103012008426100951001d60040210310061003030340555086a41803400642d000c41c00303801412202106284025a15510b92040c0814680745026690030f03606004400643d00301030341c4244d560704140d1030880c0b04040c1c030400101d8150116111805460442507004101039980c14801040b07901998103507112080d844012070f204004c440314801f20f40c2c0d11444a44140d0310000c080c0014400640c04039580014118980e211150030442241000d41c14101c0d228150020320703001c0548215580014090360030403c04102103900032040d103080310070030389030004030304121800318041d481c0446003254081218000070420928403 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 968314217 1250 968312967 968312999
    0x1b2b06080105150d150603081c06060c0818060f12010e0106080906070f050f030117010510180b0a081c02010e0105040f020111150c0a170c040e10030804 67
    0xc0008002c0d589403103010600ca0510401c0940d0800305841310f100001d04c410744005550010400c00041803a1a41d450130080c1d40315400307181c905600c06400b200c40070301e684560001484141000d91540107156070f010030701e0203032075400015034030b4020048200c7d880b1070007115010310a810003259281d05111400f0200c610078014a04030910070340002c00d80c240034161a9009289460082c40701d691a8103045030409004400082000340a020031004608114081c1d800f03030000c032150300f1503000b12100e900c0c00c51380e0003000c0d10310890134034100b0095001a1174520181d400300c2e140c08140c0c0d42c2054082458948a503002452510520304002c0f0b1001c7c0003030000d01088c4a5500030b0052002c2c0340919420b075001038402401c6d54076045500780c010341c0911201c80003040d00b9000d890780c0c640c50b000150b048440c101e522121207440010724070310960380600e00c1c011005a10000341564140a010581c060090b030103050307101c03803003440402c20042150405200035580004036030380c1c40c0d444000642c944044 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 968315467 1250 968314217 968314229
    0x91d0105010b0d1b14030406090618061802100311040f030503030412140d02070219090507110708030a0c05120706060303030b04050f0a0b010e031b09010b031b2b06 72
    0x41c116100f1104c80b481000d01401001982c1c41000d0720b1a0a1a01e40303081d40301a100b20350059580a0240014401e8090701403010064410b504000d80300b41040b8055980c4115001e21144a22004000503696005842c01d880300ca45000580d01e601c080703c152107071190f50410721403022040c1d000002c00000000441c0324511030b40264480310603080341a9800f1980c0c0c1421150090180800f560105483d4058040940002d14503e01403044461255100555800501469448104008005800103501e0f2440c5108800420b4494074100780a5100c5c00313030039800300402c540f11010b1010301804211182c114601c1c02c3d1025600c1809180c0140101111310044000c00d0030003023518032505e41403050340d100b00c1d070400d80440e07580d54405d0740c10b00400700020702c0c5060042a854800c0c003038900300b081c1e10023000068590010144074000700103007080168044542c12400704204410102907000c2e010501c005198420b0f111514400700004040144490804003e402040c40c001c040454000c40200d0320 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 968316717 1250 968315467 968315471
    0x2070e040f110603041a0604060b07050601091802030703020913050717060a230a020d0204090203090105130c0626090c0109090203010605090613090507050304050d03090c091d0105010b0d 82
    0x6405028460030b0b01040302c01400995900e4000c1b07001c2c0c2d42c91881c841e480000148005074007500c40380500e5054010250665403a400000180015030191059031124038203125100ca49072030350780c0041d42e100704a004c003c0c043c410050200e8cc032031040703030f1303441c0704103607108007540c03005510b0714004070314440c1c10041e4200d503100303900100c0c400c070701c5034450400951000b40c816404044060716180d400000640308022803030742048116038a0b002c901c09080a0a011000565a030402109040c05c3d01c0020f0700d88161139003038210141c00101101100350499001c0c2c01c019a40743c240662880d40c130a40c03000101e900440d00b10030011503040c0428a54113206098852004d010788907058402280001d004031004900c00704907034502440c01c10301401c0241d0404400004441e1910780708016903600752445d001040c004820302c002c01c1002e0140b006188594501000030000e2601c400c0750b007020901c110030000e940c1d07136403801918401400021800384044000d004079651005c81000f50350001d551a02618 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 968317967 1250 968316717 968316743
    0xe0f0105071419021e1609140103020108040510060617090d0e1509030a0c0302150909040305090310051f0f0e0a0c210b040b0102010507020a08030702070e040f 70
    0x502a401800c481c6612161040c10315440108012049075500d11810540c82005c1440015420000c240c40d804032003007014200300d12a0030b44018121082d9000741610504001ea5800c1100310003442604503502441d00c00c44a89441c1401030410400c001c100e0b40090a0507004507840d038000d030510340c03030095104034001c951743c82074041d98445060701c058500040c0c0c035041007412072800240810070000da00840358030301907000b80000d00e07001960500315042002c0c1c50303041041d0301d01104000201030a40c403031185429005000a056940018801014080040b41403c07681c3c4013000f9201d074400481000f0002801c04407605402d892140c40c03203100303100b0807400104544480c0c031070620807240c8610f074180254039051603100c081e0121260040402180340200581035429103010320141c00f04482c00148007507034605200543c0d0044551505580c1408180325a00794002509911150072811090b180e4440c0b24080342400307180c1e8003548110444000340014454041b0a4080c683c0c4510802c883d08 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 968319217 1250 968317967 968317981
    0x30306120102131517010801151a040b070309090903110d0c02150702121b010e012a14100213080a050d0f140c030c060108070b09060d0b040e0f0105 65
    0x40d100d600344110443c40c03040010009400020542d2007440640c0c200a40210145800305013000401d0388000720b180c0d15404401a5240c008002001600c500180a4840b810b4804c2044207485103210700c1c441e00f00000340720b100741032080721910b011308418801480802910304004007511101c044010140c003441400c8044640104250710a1950180030b098154281007501c0070107801060043c3d8100d48039052034500d40d4000e11140c40d031100004440c0301098010000100041e51107000c1a062004140c9041d074803444d44c6101201e4040464040520289149032030f0388080b01ca0a044030880c454002c1e4000644e602c2d030054920441c0c02020762a031542e0311001581d91781c0142c24058460703000003c031040054420410315034000704904240758014000f00d014100d56201d080070001c5070300301084c203c12080b414003890f4014000e000082605e2420700c13030f20035010300c01c01a0640c4150300c000384840d1400c0013038100040d0042d00074801c1222007a00742e113181e202c100303920542d012540f07010002140 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 968320467 1250 968319217 968319221
    0x809030d0809101d07030c0608060901210609020405160e0a0303080408160506040b0403020f07080c0f03010b060d0203040b0a05070807030b010e12010606120902030a12120e0303061201 81
    0x30641c0000001c14107009000f808000a08841c4115030400f014810b002c04034810400c02c2600451181c04001d0569103030210040c0540d502601c0c8502c01c2001718010032001204041101d9041701c5101d841202400c140740407002004406002500b0034181020403060940d030180c0031282400d540c03514401581c03c0c40401c52190218000200441e04100102c0d011841032000340c0440c0c002d8070f4940c01d194110303031240351a00b40c00304c40c21104104064204820903a044c42015041d04180005011890420300407a40319110380317034040d0041e40c0040c1c0001d050356094210758003002014140d282e65900000600300654411075096900d0000d4001064115129100325889036005542c2c030311041d110309500714040c142583c0d01c90704001d40500e16003500c0e611100b0624600308101c0000a03414944403000d400710400c0140f80e82d1161074046000c0158802244840700b55501519030005800410000d0701d0016014007001c80051401e0485211064008025070180008440d5400c80390305849009007 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 968321717 1250 968320467 968320471
    0x2090f151804110a1205010614011b08032e06020c010206040f0204050c09180a0e0f250b030a02090a14010c02040e100207060f05060a0e0f130c030809030d08 69
    0x108804074500010007180110310f42d2107242600400b18102c00795109040001040c103400240c0d41c50b55140000c006e012140010040c48010030f00700f006840d003145c0e480c203412465044029080c2c481c0000003811042d082408003000c1d2520401c4d130802080c0b4807101d909400414003500c40507100e038615100c041e41c000211941b02d9540701d800b18400404d640d0900028010161561107552030901100c00141e1381e00c0008440b400c82280319810754648050322001b5103107a03030700000e01c580107810350745880e08002c603c81d0307940004204401440019001040c045000035030000d410104084144042c50046400400303500da0102c88207002162540c04140401c0d02c03050440d40070940a040e000c00504041d0442d1646500600a0718030805c2d11001d184244da1012608688075a525001d6603d81e018500c0b5294100509403802d5414509200c10414400c43c0074115030710007400c100009c1d001122508100651560005049032602c1da6403030490140d030403080030340d44640a07800c1c50040700ea1050820034 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 968322967 1250 968321717 968321749
    0x8093d05010e16030b0d2004050601050403020f0a051906030c05090a180b060a0e0406080601082d2b0c0c210206040b04031202010905030304030f0c02090f15 69
    0x200d801d407692410503c2c40030000c1c2c41c000c241901d820001030036644210ba02284c0600a140c4095a000c0c11481c041400b001d84924511940c542014083c40ea44d00200703480c240c0b0341c103a400307602d041c03d5000050b010014940c041507110110002c0c4401c882c3c0f01c0d010070012900300e910180500c40110300d081d2034601030b400d0015005440084100b042e9081c101038058044451000000d0940300e92001c101c0c20342c0701005210210b2004460000d4034203084c4210f0004001c5c150140c5640e50400c1c000c261508140781042c100c2d0042009407024a01c9080541c0141e412030310121071014080c444c412410101c041c00c4010720401d0b141c80c0f1a000b9020b03c003203220060380250603840c1c090805402e070200094207140d8607034030fa804554802c0141c48650091015042500006031120b207140f9242038103200c42c200040071a4181000800060000416250890b9140c181501c0e100e03610b08085440003000c01d00030754845844020b200348110304008040c00303000c00c0b2031020001002da105110b01c00400c01000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 968324217 1250 968322967 968322989
    0xa03021605031c0c0f120f15050111060903030c0f0d06061d12060402280f03021f0c0b0a0f02030a15120b22020607051c0c1208093d0501 60
    0x24580c0601c2002d04600319022284000750b584060103147c4200c40714494041d40d050304450041c0019030b0400c0c8848101503000c03000f0080c0f8035114204540301c0c040a03010400130007000c101c4e603510340c02000c2907078860701b15004204070903507584100808a00c802440e03034100749074419400000342003030325983d890001200000e001e035445070790900c440b5401541c0c22541c0948000c05942c0c0c040414040c4600416494030704100341400c40c01000651010208005204800c42c20b500d0010750f00000304a44068000c402272280d960390a031450068900c941d801d80b1403901c00401c00c4090704407680504859a0074102c0d000380a17032031707010080703060a03180c2010384011031200000c1c0000c1034003847d000585140da000d0782244030455000c01e0b580c0d0055001155150003010020f00c21410052100600041a00d0429282202a01c404458400c0f02400f101000309820000300040e00c04c00c154a203510b8200c540020552920f44a14522040c041001d01c02401319000a0b0900e0b440d80112410ba5000c9425 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 968325467 1250 968324217 968324237
    0x510050a06121a10120c18050f070c061427031e0d0e030703021b10090b070606180209090112020a2c04150c020a11060a03021605031c0c 60
    0x62007003410401002100e020146880100e24224045e441d5000a44100203080c4203504042080f000032040c60300c098400741c542020883c8601080c40c0c0c00d5000300a60502d207510a00724140000a0074115404100001049062004001c1085036804501e00780d1a40301e17003c00c20001420792240b05a0302ca10803a06600041c0d9080703604040020109d191440e0000102c9a42c01250642107810002060b80560418960500240000d8001c601d0700417048500b10090480c080b4082d048a2450050387d0b81c94001044440c100001a80200081d0402102400103107081001c440c0103580240300044c0691039082c00001c88420140c24142c0c080c1e401090748411ba402c114150030340b051010002107010b4003903944610201540ca5415001e28005d50704044c48000250303040d4180c40461003900c046511084201d030200b04010000c28070b000c0c048490795950524030b0030031000703400b842042c1c0d41c2d90600302c0d010104000c0008014441b075240100e25010f4800c4003c1e0308821a0002110308021a0000c42c0c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 968326717 1250 968325467 968325503
    0x5150115090320040f061706090d021f0f0e1c02030909040209040c1505091c020901090c0309021203030406050121032303090607080901090305090d08070510050a0612 73
    0x40026031850f01800005030320180001940a03101168800d4102011b50014068180c40c1803207820f61106004c4004e1505080003000259030300c091400b89880c0d600914009240c141070b0703402c000455007030130b0340c04c1c09880710941d002500c0380c284e040c01d1051300400c0092800c48074008001c0d6150a88010400801551a40c0903c612402c00500842c0d246510ba030340842c0074080c55001860b400c6055403980c2c0c90340c2d880e109010300c12043c5e00c101002c0c5074202070802c0040e0b440c9021141900c00c10b2001007401c1e4060001500980240740c4000d50085034060101c2c0c40b0705000010350300c2140161401d0103143d0b0b80702c805441d500c1e505106044c15008100351800400c1c000d00c41c4052105e0301400601c80000c0e00c0601c044189c00c15207080382240c000e0400c4c08220790b48002413035042400c28000b0420b0690b1650040d016105034480381b4000c0c2d0b01c0e1150042800592030581d401a500700081d20302540362021803400508003114011412403400d040450b41c08c0113010b034180d0056110014480700c880740d503 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 968327967 1250 968326717 968326763
    0x60807230906090607030e03160308070f2301050901140702030703030b0f0a08010c110c0307140d08030f01090507030b01050406030203181902180403091809051501150903 75
    0x1074500e0304004100b0098840d622070328001d210042c041e176502504160348408050801540071414102c41101d62024004141510211152180c1c00003c1d01800802440c0c20200c4080c0030508040d0780944540050f400d040640000d0711401d0703001e008004110b000d502265007420182c415100581c41444005c000030b0081d031104160540081c101c80c101d5295800003507108003141c101c0c1405944403010800070316000f042000c002141e080c0607100d064144000301742c0e50a114814040f00000780d0701c02160989803007001c0c0c5034154119507015a00c0c0703890800018000021b03c90103c04501d0800003a2115100e13100e01000d030711050b90764501c3d1a18200c401c902940002c0d0008101030344481c1b0850900e2002c0248144c015503c08091b0300103692801007180c1905804e058000b40002d20b4100300c0002e508c0940182922504595050103e5218001400408010384020014402c02c1400121600881c0695049070068407075080c900c14900c00c11101c211042c4401041015081c005002c0e1000003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 968329217 1250 968327967 968327977
    0x70e010c050304150914030604201302070501060815010b0316030f0f061e0509010b0a05070b0103050703020a05030f120c010905100f050c040f06030507030e1606080723 74
    0x900100c03400c15440e000c0f21540c0707480004c4d40402194038040200300184020403400010781040300074204a01d81034480804034400c4000841800c0c400d08405501c80d600c41c0011782032383d02004000c54545c0c203d0b05c2c00c1c5000342028050130009119086141072009a25040c2605030782c0e103400941d0030f42c1c4035424425145002c0e0110001416140c1024040401507440f070352032003d44c14200422003d1400c0240e180c08112501030418210030f4050500031515015010742c1180c400c1da00300307682c951040c030048446000d980310050043d280480008244040040c010060707034000c461010312180e032203042580d140d03410101682c940d00800300c0d00040c550000c0103021259400c200105c0d0481060f0b0b10030782048a2040c410040b10341c0c504201d492a0810300c5290380c072901c69401a0300e8581007551035102c12071144207030000c0684030800264a20b20070f82118540c44213800c102d6010041301c20b5100c90f10f881c0e600558000424090005039903501c1500701c1c14424840a086800d04200c05d100031325560303c2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 968330467 1250 968329217 968329223
    0x70f1d10030f20100909050601050c03070b0702120c0303010602010c080609042a260d1b030e040513060c050307090e0406060f0807090605040203010510050d090803270105070e010c 79
    0x84120040c980fa2885021130b18216951044401418240000c04403000a410981080400c0c802003120590000494044a4001d003041e6815901c15000f05c1c60034080d024102180500401e0102da4460008051360603120590001e000c009c44885085039440d004544040c3d00000c000041000316007050b2085c40c1030612502112402d00c440a1101d4041c10603900c204240781068005000c030a102c030484101c8200c400000c3d003822055201e00510420052041c0c902c05000c00e1030340300c1050f010311082d10f034000014005000d18503117581d00c030300842d080c408192003c50500d51130203440d910401c12070348101500d07240c611950342030408580944e24010000c84113260b5480c8085074001034100520b005100c2e64000382015404c0040d8142035030340daa0b205900440c01070006200c29038072610014650201c52800540368000303421001c0180a0405028203120000004d01608140d07696600d5208403c040030105c040803011362043c202c600881c0c0480008a030b810700c101c2c40d0740c8104030621700031340 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 968331717 1250 968330467 968330513
    0x60c010b1e030c0906011e0315090501031506031211030706020d0e0d020a0302100e19051e1605010c0c091104050108010801020a20070f1d10030f 64
    0x100c8000724402207801c0d2403001841078141c07101d400c00d107010408404040826a464480b9041810000c0e294141030700c0c4101c0006001c04025103464465482091108907041100e103080c0c0da5202c0d80c0000784401c3c0410303229041c02c4040300941d401107008010171203900030001c64810011140c125a0442c010f07000c4001c90208000d0a4046491400078224100c0100c000007000407261200034906902c0580e03890664218901000201c2e4010680013036030480c880000c200380301c80002d09802c011409034907101d069414103c80c4103002000030400c00d4a01840e040381c039001c6030012221341e140d8075403c2003ca013400b000b0040c0141c3d44180d15002d4070a2181e8230994040380c45421417000d0b100790000800340074502160400c0190390003246280142900002185800a40103005000a205241c009000d01e1342c0c002150341010108400c800a104019411f100b50b41c035922851007038401c0000d440c03043c40c11040450340081d40c4034190011258072070b01954030030282e03980700c502c49013031500804d414030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 968332967 1250 968331717 968331731
    0x140603061005030907170303070908120301050418061d070518040609060e0318010e0f0904170c071815150809070e01060f09060809030a050f09030a0f05010f0209010e060c01 76
    0x7001c000c1046c001e02580c4010315100d1030511001884c48955620064007035005000c00e2000311404022241540c01c01d48010500c80c200400c0c0240e8014040c40061220f071501d00e601c3c1002c1c25440460611403111411f46080c0c86e51242044200c140c500749004020b22001e002c1000a10180c3c05a11074605c144e40105409a84603a25400c58110360022191080d4510700d0030010344c1d10000c40e01d8090011190080100070440108180c000003d200401101c8403401c0342d4200c4400f142503e034120015412180c00644540c80355144034000550315009a05048002810f004181520b40070780383c00c07505001a1000346103045980359005003203054940240c83d40400e10f22400380d030790380c040c28442d203504c00e0007a12001d000f020440c071a44004100038000b000e010366001d0210440c2c10000e003d1604a4440780781401d00c0d141c80c13244645450385885142542810064204000303030003135000740000c10108200c0307000f0700e060b0b02c1441899070000c1c002e04001141c81c5010005401408032900000840c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 968334217 1250 968332967 968332979
    0x80d0f1a101206120f15060f0302240409090c0e07020c15130e011e0602060105191d0f070503012405120103031d030730050a0309140603061005030907 66
    0x113540c141206849103034120303400300c05000030481c801120b0300f10036100b004031900c0c002c20785003101c4840c000248100d0742d40301500506010003400030b881d4069800c54a941d2039455000f4001000c10a0049a00648441d00080d640c07450386001d51041ca80c0350007500100d085e00c0c1c2000144200c1c0c2007032074501001805600003100300e03400305070050111113404804650401521000f40003624035860520030040c181400f119034081000f0b81101c00c1a101e5060f200350700c1c01040524525a00b00301010146860040031002010383e025000743c80b030340101c44007500c0301c00003103659210034003a108142040440c001c0c81542610216400c02c14a40380850a2a034500c401c40d40c5540c0030b90043d400922146071803d20340f01e01280d5010820070860081212034684080b28202c24109181ca10765031001c445200e02074904c0d4141594619403220590f2070051083ca0050300c1001a4000c0208000b250ba0000742c00f0300b060412a0301a001c02808c0250040207242c0403509075000820402c20b90184150010b20 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 968335467 1250 968334217 968334239
    0x1710082e1d0d09091a180604020d0203090307031107030b0114010309050d0c0215070309050f030304170f2823010f0609140606040e04050a080d0f1a101206 68
    0x22240d21542c624403841c4c41d01840f00d0075185450004081c0e140c0601040c0340b1030790341200f6592410014810403445581e0000081c0c02809110a1001c04600010030442c40881c040014496103102e5210b12040121201c2c005d0355803206400000e00c03a808517801840980b5403800d2035040c0e80c44c14500403445040c50758aa40c18660144100380200b540ca403030100442c50b04901e286016144001414289509a14000c0642030380d4410580600708510075054039440600c01c5902600b204040c0c4844041c0c0c1c4041d841d550823001408a645010310000b05054010304040020a03d1446c0c1c500701c00c071000317038688250813035500345c0c000c00308020310020b0300d8911028080e80042c0403d8031000518a03180442c8001031b83c0d42c60440541321140441004015070782c8205840c02e072085240c5034103003903031940b07011480d040d040123020b005040080786030580c0150a401c0700e40180b9044400b404007000c03160312072080ca82040442c0754030401260614040c544900094810f82c800d0340d801003001d0342c0d81c10384150 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 968336717 1250 968335467 968335483
    0x3060f0b0d0b10020604051e0309010c0204020d02072009100b0901030f0e1e010b031903030f0f0218010905150901170405070f08030a1209031710082e1d 67
    0x343e00444100310901034240907060040d80a042c8d8080741c1e80100c90900d4881c4524120603044c00141d0420388255166a8143e80708a58400d108554448450600c4c12200082184c0c1c005c00e2800141403190382d090100c3e0340b60280688045480d0340b00c0c14000130308010f801ca038039042d041541d10b000d83c03070143c9003e014020304c01e5501d0014106840c0c0307054491206900780d032201c410b035a06029206055840010b040155907030400d02c041032a20040ca4202c0240940003151840f00d424501101264038041d4018070700b0300d031a500141002c2e4840130041d80d60368160300c100c0c0d40c402d8803102d8540c5000c0081000301800c1005150410080c00d0303400c03210715040b1080e9002d844030f9002e000240901d0304403410150252103039400071401c104180600500a41005404101e1180ca480400007094020b9603401c1c80341071158903007c218500003014010002140c810b4012511410419000d000b1103880e00c4c0546048022003c041da0024a544038090f00d500d003000d01e010100c402251048000078010b2034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 968337967 1250 968336717 968336749
    0xe0d050f03040b190f05220506040305090303040b0c012c0706120609020d0b0f0a0b04030210120e0c011806090302060304020f060c030c060106050f1219020406020c1003060f0b0d0b 79
    0x42c09041841f00c010307029140f0017184102810002c0c10001107000065803c0c0d005501d40307410340d90f8841c07082c04207045004035403201c58102d1011801180505040d08816080b466881290840c00e44030441400320074030b280c1c1c0e141529000701809114682c0300701c001d8080280e0280010174036075a1821284100c0c0d0102454034a5036a680c1e500c000685054102495101c80c112404048030f030510341400154801e922009101d11007142009034600c0c020f000400e00e411030000f04110b00c103080c09230b50b03840d10546000741d800550710414260b1981805502c803015200c9a5440e03117591425642403101e2580050000d80e405030000c18400015a03925000b00030084094024507160b058902d405071030b001d4103821480502806200c1e040d00c01040f4401d8451400400c1481103840c0c681c085140100001401040c0802d80002408200c03e500010a110072100030b503074000c89000030030012800c850441c0112043d00d0001001000b40c040e0040182c24014010f100024140345107074005001c42460348190 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 968339217 1250 968337967 968337971
    0xf04030306420203030114031005010608040201080a15180605030307030512060607030c02040231080601050901050d0f051002070b0a1d0d0c030e090403030e0d050f03040b190f 77
    0x1001e00781c982526a100c104050030300b54030303032103050042e450340014010b240d035201d48030100140d00ea0b01040600300344400c1402c10815940c4414004248503011101680880d619030049050a40c02d0301c40c10f00080b042041c0024098100980072000c0c0d0002e803c5e000c95142c83c3c56006c105580d042c401040400c6c426168140c3e07440920b01c0d5424580c80080c891417240c4030034801c0c000031135003040340000c6c0540d0481d001a03442030018941c0b455480e0140d0085c010b0b0400918140c0032031000a00f10781030794008001c40d20341c1d81c1d803442000588802401459000214209554002440346110303e9140c2d21941c10740d282c214001010004030b030007e050a45803100c104040c400300c0ca00d60700c180000c0e40321341c20b9511419003405207455510200c0b00751a41c100070600c44128103152003040c09820001c4014580112810641401400703040c4074107148045005050584440d03600400841c0c00301c0d42d01c48000d034259900d40e2204414035030001d10060a11041107004c0c030500c2c40031f21500454440103000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 968340467 1250 968339217 968339279
    0x120f0e0109150c08030c0c07061d040e0a050a1b05030f21040b07080d0501050f09010b0903031c05011a03010e0a0c0306050d0b040b070c020f040f02070506040501060303021005010605030f04030306 86
    0x10313092238040d0310341c840c0045c0300e010446224070568400a20381c41a07020388010404040041c2c0c80c0e898040c0d550405019070280030300c44410412201030244c8034030305030305c603e480140d1650101919800c03240e2410f882580f1050701031007007034071000003440300904a9185506003541d482420005501580c01120038800018202c0603a203d00e206080c007420303060710755200070400702020030b07a0148180030340707200ca65000c00c01c248107680070811203844c510501d01450b0705640d699a140301911081c001e414080044001e426800d41d010810b030f0f4100c4070701040c0c42c04941c6407000c40314000c048a441c04d80c00c054031003a001c11342d0b46800222010300c601c900701c05e8001e46030a0400c3e01c0c11200190040041000800e00320380503030365903450340004640c200c400059204030650054000e10508100402d0780c0203900401043c440198000c030202d034041e4090302d1152900d00b8400044a1090081ca0080360701030000c11098924440c0303407940544a41000950b554841c1035600c5c0002d444102e0f490441600380c5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 968341717 1250 968340467 968340487
    0x1060803190c0b0112032307110f151305011b03081b03070c031106010614090402043b060604030b0907090501181113050607030e0904120f0e0109150c08030c 69
    0x140a00111120901591f6000e0300e9910620a0b072040038000741100240322050425a601c00b013907503403100380c002c16512440c2003140c2c100600d40c01c030110601e0044640080000c040d40a01030a885800c8030800d01402c1160a0368217462030034002e0484886540810041c40036021114000d6009560342d4980550740305c01490300030715031880c2d40241c5480b9040b6500411010f40c01c40b403e254007960341e8104a4071644120080f4000780100c0e4015214a80008640201915040c44004206000301d0303003000c0c10149841411280362080d948990070000410080001c156a20000c6402c114803c6c00d454480307903559218010340b40d0a0f00a01070300d105604030040000c04030f00c50b40140c29500807505080030103485c0800350712a001c1c03090350300803070000503030703401300340c45408400b000f01c0004004500c181402d00340b981480e0054051034007c2100c102101d500c80d40585220294154141e40b00c07665242050441480005a051007000744000c404060002176507280107180300d11088101c0b60f46800c0001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 968342967 1250 968341717 968341727
    0x40c03020711190b0c16030f02030d0c02010507170d09080c070f0308121f0b04140603090a03030c0302070b041a010f031203020a1e0f08010801060803190c0b011203 72
    0x3580318892800324100e030f210340d160140410f0494440810184d104c0d030240c0c2d00e007801c03c046a04054240280e050000c01000060440d049002d40203804a80b00b500100d002079400010035240130f408914107100c03100c005841000301041c901b40e80c0580605040300ca0444800b5120340300011218580b01107800300e11007030100a800003c05041040c01d0443e465500c3d10102e81c45541030790685141c1000014040c42d0b58002e03140c03031248214807802c0d2519a11394022030396030098000c244170800b842c00e0000c035034a066010b9a020b000201c002d040382481340d503000d0703000b0a02400010f0505400b4070241c80421007d0002c0341c8210b0080e501920f041581c070401042c0994140c01041c24540c14480a10108442044880c20f2550a050041c2c1e50f0300c503e0030988a0300c4400c0c4100d184158058080001d09a102094080007000c43e11074860f1640c92b038642c07e090b52010700442849a20610909640510750303010405074001f0750418401410264a900c10b01c51400d0b00143e007000c030b001c0c1074102056401 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 968344217 1250 968342967 968342993
    0x10e12240c1318060909032102070201141605030307030e1b210c04020c060117030a050a0315091a0909190f020f04021204051b0d0b040302072402160503060f0a0b040c030207 76
    0xa08c02c600d8070312075500192452903251252148694082414000c038000541034107080c40c1c020f02140d0301c91501600c010080e102d012031036040c500540340c0306204110002c1c41c4181760040101046a19801007092240703001100780118454402c140640c60347c0d450b2440203080f5455008050900ba60400401c001000c5e80211500640d9104114041c0c10543c0172058414811051030041950341089000d109d468240342c00c03d031145032500d00c0d50720800d01140121041440243c0c0c0075061070351500307601526005034803000d200482d001001c481c0040c00007054000c0c2c60f4401400b51800d0980714012404a0b00010392540c4102000014007051050401912500705881401ca10b0b400440070040b44d44400e562100412a103041c8010408240c000e00c40240030341960003400c0c510079140d00200244050981a2002500820080c01c2081030b01121500c00e5400160040c040c50729455210f80c48807070000c203081240f40d41d40c0400e2241d640d850142480d805855a000341e220740071030a003100f0307407101 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 968345323 1106 968344217 968344277
    0x3060708010302040c09032d0c033f050a0c051b1320070f060906061a0a020a02010e12240c131806090903 47
    0x44024998102c0740200c40c20302998500d582e042d140d503030080c0405003a00315400c2c001e0301401c491040c40c60300d0212044440200d0b031000e841e040001c070740c02d82044517003004510003080d07445003000d81840d01c0509901d40c1203240c86480317070b031880c011507503c01c14050107000b04074a5441400b80860600c03141e001029a40c583e90031444600e10f60840e40300710ba201c1c001203048845407504a10481000900c0d04811426103030803601d64080d15000307918200c1d08103407a4819180010b840d0701881440c03501c1250080b0715541001c15450b2640203800081383c01c00002d004900d00141d000401c1d09444d074080c01e01a411400d86000320f01e0030103a03002000c00a00c42c0610121142407015400d80a021074283c8840035602e032030140c4401481400300c1101c161500850602c000741e13640d8107101030008050000070b029690303000300401740c0781e00400960100e4081c942601c2d0344000403412440c1020 = true := by decide +kernel

theorem cover : BRFrame.Cov 968165467 968345323 := by
  have h0 := BRFrame.cov_init 968165467
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968165467 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 968165467 ≤ n) (h2 : n < 968345323) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
