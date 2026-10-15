-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5297
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:24:07.678202+00:00
-- url     : https://prove2.me/submissions/d7a0efa8-0aa7-4fbc-944b-ff7e52530278

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 952517985 ≤ n < 952697841 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 952519235 1250 952517985 952518001
    0x12120105010f0e030a02130906140709230904080c01050109020711040e100506010201020d1b02010509161206091527080d05041703070f02010b0108073023 68
    0x2034200300c2c0f280200a0400c0001c00c0d070030003c40d030417a45194040503803105000743c0411864031a111302c58120901c0e0950038070f486038005041884581028802d61414140e80240c01c821250316241e480741519130304095111814100c2180c050345201d01100c1d03081900210746c00c80d69401500502d845030f480a90201403120801050301c40301aa1460303242e000c243c0360216120700b5004180c101784180001450124240c0b082c41c1541c81c102450700210f0405c0b40304000301c0c0e40c24403c2130b0380903401401601480001070b0080050298038460390707800e00141c203485410320200e6444403810580c070840d842c0450307081034200f1000d07254652103440c02c0981c04410000c6602c2100a200e449540303d4111407402c030840300c0740c00062102074802e030f40d88503154140440388200e03200151700449041e04c0c0c0c0c001c0004405402400d4640701030000e41080001c1080c808202d40010301c078199502c10701c80c04e0800c4416400b1003e0141c0c1e00105841c00307142802c1c0003440c14841d0300303449140e6603c1182c0b40d03c50356441c400 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 952520485 1250 952519235 952519247
    0xa1e030209060909040201030b030d05180d02030d0c020315160e010e010c0b130203030408101a10080702010f0f06052803080a1b031d09010302010f1112120105010f 72
    0x1071503030040310070454042d0914044c41c61990040c41410006060080800821310f0070740039440f074078003160300050604071b9101204000340900c001240d848140c10043ea001c070341c941c0d02c032594040a01880e05c0c4030500315502446500c40000e0520240d9a09180c0351844003000400c071101000032801650081c9000d511440c0b00030003611741a120b404209a096a800d100741000405151204907004511001680d05000400082c42d018005140500702d001c40842114030384849030148c2c2080d100c2c42d10107a100d040c1018000d0307015080405540c0d590020aa02400360402c141c1c6160f1300e4826613010740c00540c0d207d2801d9400545001c0d130700050070a4001036004040881e01000e0010b00c80800020380b20000800d00c54555242070590000c0c402d00d0708040800d1520103d020929008940e0b0000084032400e440c1b1200c22111008a54907540001e8480c5010900c14000c001c0904500ca418140c10010301c040d2490112040b60307a0301070400c0340c1c00030520038081c60740002c0d240d044014205201e11 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 952521735 1250 952520485 952520497
    0xa1d0301090c270e060f0f01120b0c1201080303100e100506072604030b06041e0b0d0519050d110c010f090b070c08120c0715020c060a1e0302 62
    0x403040c12041d802c010418800590412000050000a0740c400d004420540504901040004c009144608060820301c1070310038000c000c03420754400100100207101c81e85406003512600415240030948030700d1128401841511200300040034090000540300c60000011803040c0340c032060320075500344c4903c042c00074207000744d94141810000700010b200e1443d1208c01031100380d20524100000300754400c0c1e014209690040e03541041300c03010600300113000a41c14112313403180381100e0400c00351a03001e00c141d0381050051130140c0016503800300c518107515061006912143c024049038032580003501442804518000c0455907400340c650ac000e44280a0b004a0201450700c901a0480e04544401198118592075490341001080d140020750207103000010030b5040d00803100c0c42110382c18401d519180210180341c030640c01104000301c1510903c04280502504c104100e140c954103105d0804910384000001c80300c2c1e100d5000240901c203c1c0c0c00182110201d01c04c2c5c2c42644044141c40f0064007240516 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 952522985 1250 952521735 952521743
    0xb070e03070317070b0f010501021207030f03050a0216050303160806010507150b09040305071b12081309110a032025050d0210050f0408091c02060a1d030109 69
    0x180002e100044070200918070354004420b2141c1000d005464950700b2240955001c0d041c000440c00601c65940c1c18068803940c40d0604049500c1c2480581d07000308001c00311901c003010181c0c0c1d840450307410b0209404446080e20104607841c1022100e00740a51640d10550700c800c0c17540701211441c000c4c1c6010300302c1c1a01c5804161200d03810180f8544500d42e14000840d56040034039951560f1440d07903501c4103080e5001b140030303031303120f9880796002e20b055a9403220401c900e08095038051020000a28444050600c503603200458030384a850310440e0211240d1590040c1c84032a0408005100001094024001e0400c459405208100684850524402000e0f9171488040c40402c200540d40502d85941407480c050f01001c401d2440303403500e070103040c2000c40700c40b00c0c010b1700941c24121954146014041e04075256070072401050500e40c2e1000b00354030411640c680541d401c1907203250303c20030800884c45081c2e0007421082d920f0070301c410010107102202205a40812485204002c6410144034078000941d00c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 952524235 1250 952522985 952522993
    0x1030518030f070f05160305150c250f11150703020a0201200610230a150203070804030c031716032114060a080f060f0c090904030206040b070e03 64
    0x4030400c0081c80d640711800a444d20001ca200807800118100800b8400004034080d00d04a6420351420b2824001800603102034607113603405001d0707049030302d800311492010300044505181c4043c418017031080f502ca50029001c046030070712460a010365445000f400750000c5070075000c4101c0d0008050070600a07000060016480f00d0307640f01c01540210010715161740203103903803c01c00c1a0002d100c2e2074403070108e64a003110540203000704082c480b042980d402691203984107021580141e004589000f8982c4281d002003403803a2901c0c44003500900859640a0304031034511345e5140c40e4206103030080190301c0101d5581706280c00741c00000602c401552206801e102024403c000035890498014003034070041178021100c040f250741410760b00e03c6191407050603d450544035180a20400c55213481a9006900b1500b2001c0c01c1c80340041d000c0346613544075044142c880c5054450803140c64283c0140c00242d500002010144030a050300000e06070320503485001c040c0100d60301c1e01c40c2260018404040d5940580c4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 952525485 1250 952524235 952524247
    0x2150c070b0406090f03030c0e010207060206130c0e0916050603040f061109040f06030b0601050f0406110a06020a0203071704140409020315072105010e06010f0908011a0103051803 79
    0x4861108160418090f100100f041440c0307460740305140245400c105c000c02d0f034440010500980044800d80b64680034005050007074500310700a9110380008152506020411449004100c8010940b01c0582030100304031040d0301d4268031003913a500044004a21480281c0c0001489250140031640f086511030101c81003103206e9541c88001e440c0403183c0d0160b440c41440484016103031403041030903210394044041940d80c90342c10030790034415020341f5080c10888100103100b18a41d80404403070460305503103002d000012285288504001c190071009080c2e03800050400d10440e4000090151140602c0100074000c40204031060346c3d00c41c40c41080e0b031082d505541c0d02564505584420145400602139130040f0301204951690010b0072142c2c803001c1590078010b01342e011030881c0300d8840d4503480003040029505045602c408020000c2030541000741141000505521980c1d10500a1006200901103400001e80075400c1e041050340303503800030707180c40001a4510502c001c0302456403225005149004 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 952526735 1250 952525485 952525493
    0xc011826090d11090c071104020901211401060c05060907080c040e01060f0f0608010929120f07211509080715141e01061808100c02150c07 61
    0x8500c02c1c140c031120710300c0340690309580794800024818160484a10359854080c642030002881c0c01402034000c40c03043c8042c65059030811004e4035615003603c0350301d00c00006041c0d004058800c10f11003600c0312800000000c0c0030303604a14240d205511071416605240e03a84040707684d56520b580b044003804d80c045e001e01c00c060700b0f01f580400310414100f00041032813912029040511141076000c0c071804011200100100c07644880b1943c050610018140810030441c840d6514044c01302500b0711554610482101c0c4c3ca42e00d100e4801601d09644c4192404880e80c00d411580b02e410303601c070700107444a0000e80182d0f200502e10f21042c0241d170150035014004210700f0004001d0420f21411070390407104021030404120121140150048032650104034608002d001e00324811002d0000c00002c800c200041041e064120074140c15a0360610b01400011800c4071009280c0c0400d60040740c0500981c50148040c00c1d45400600a540c0e46400311008413800410048042000b102c880c181e806c03003172000100017 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 952527985 1250 952526735 952526749
    0x6040212030f28210c0507051e06090d08010b030912070b0a06050d05031c2909060d05150403030902060408010f05010f120b06060c01182609 62
    0x1405118100d90074a01030700c51504456008204190000c0012403003198070f5848548046515030071460024884602070808082c12680e28160034022078803464810b404911400030f69400d503400200312040028000c2c00f42403050070700c2129624a01501d4000b80110000050400340030100340d45250f0580e10f0b0440c80811604080c05070310752800345a07081c00007104c5c032101802c1c041e80901300b4a01582010000740d003c4910aa001c50302038514041c510b030225001205583c0c001540140c5141c00401030180c500041c800644450940321f00000304526a40007000707103d6200100741c80c00d0b4426200c840c1041014090480024003d43c85400d02100e00c00910003100c3c0c00c14131a0501040030707500c5031b0005541d40c002c1d4202c0c0722aa03546104801412415001c0c45004200d11600043c400e81010740e02c007103002a4540140107000084081043c0381c0b184002c4a0171406010000c010f4596400300c01955401092800d0303030389951500801c1c0ba298004040148440045182680381c005140c090101d4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 952529235 1250 952527985 952528009
    0x1806090d050306040b030a050303090d081003060b010311040807061412180a020d12030b0d02030d0c030905030102040305072303070510020a050d0306060327061116050c01170603060402 81
    0x130780c5841c0440d00d251410488110914461005181c6070319000c2d0b00c103458200c0521810f401c001103202886000c0c41030f81101c80641e6007200010407101800d000507000752400c0f03000d07680c40e84000240080c6508020481e003003642d009580310403a04003100c000e0074683c000e0400800c441300030640400c04a40c070411126131084000025140c00724a1600081c0c004020342c1d801340c84c000041241020803d900d4480c40e00c3c0104205c900c07c201c00019000b00341ea038102c44070008180310210380b030b038000e050107525000020900103009655454680c0760040d1209103600c203148014001820208a1501d0b1051a03000804041c00070300303120b4645001c12400704d0401c3c01403030a40c00384036007610200707405104250340b040c41510042200b41c0f50840c014102d0310501071900c2082910041138030381c007200340650307121030350030035000301e500550b0300c146047c41d1240a42c0005503c410b0b600310b004101c400314516050b508240c9501d1003d644142001c031003004100e070314650540200c0b002400602d0400d40400e5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 952530485 1250 952529235 952529239
    0x9030c0f06030f1b0d020a09080f0a110303040801110c0c180a090f0816030f020a050c1302040f0e060a0e0c1903020415120501060e0904060b040f0609051806090d050306 74
    0x1542004120600d400c0d544680c440c8004241c00045447e009900032603100018040341c8001c2c003a51200e08242525068103040c001d011100304946141e49580410a4070b0141c09524000c000b2005603041101041c1c1c00700d5202200d50254088041746c03841c0141c0c0010351250310175412804c0340d440102c250002e00a003001194540e9040489501203091080544050303210701d03184642c071031407509001c0c0c070041e001c803020030455006107002030000e01c010490924034441038604220701a036803214403011340030380e810513000d200700008000b400c0f0f51031202d103900514069070340007000da4a0b11296501518101d4011841040411055640c1c14441031101c0b20481145401030a00f6100e0020780101500b0254020000f0446c00c100d0584240d2846114014426414003400d143c7d81500420b14051004001030422603458014205030307240d5401401c001000071804120840d00d401701d0364020f003000d6811405080a240c0890322540f400a1032901400040d0000c1000b030a0040701140c540c1c0c0000c20b195 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 952531735 1250 952530485 952530511
    0x1009030303090201170a0504151811031504050d09320117090d030e0a020a0515040e0a0c1101110d0e0c0909010203041e0c092c0309030c0f06030f 64
    0x45d030a08031450507a000c1d8055a02c042201e0a240c20056041001c1e84098101c661078074095010002c00000313000351a90f070012203506181d001100080c00c0c0320b14000ea8030710040d100010007040210101e0b40f03050140701c03900c4406845072500d0406034a285090765030307640ca01c01c0580b0200c2e02141181005010f8405240441e90b000d80400500c400e07420549038281070b40d200c40420124160140100040c1c062828010100c5284a0300051001d0390144102401003415400c2140c4440215003281c01804859514041609244002d00700600c170085010740080c4a2309105803541ea0103000d80b2240c0da124200300d42c142080ca48450703004150000d44090a8820080d40071010740300d0582e450302c184c1601c1c000580fa4a41828400740c4001c0034402c68101c41f680322180400900c50071501c0054680403000000c6122540880c0407000090304c420b00d000c4101d040318210200700010080866840560590342e2810002c4148400e04854401541e40560700b400094036080c4c18280c6543d0040380d1002034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 952532985 1250 952531735 952531757
    0xc020309100c050d081f032108090613020118121403033105070b04141f0503070903020405090a0510061a0a03150315060e06090a09170a020106141009030303090201 72
    0x20141414040d40304230b13166403503a0348130126528100000b4042800c2410075421500c0d003542c0706034650b40000e021903028442e144055003564403400244580c5401d2042c9070000c2d0b07032140c000700e80e6180f061b60b003210001654030101c0200708022040c0c0307011303100a000603019000200b2002e844142c1c4c10b081c3c1c100c4c1a0642483c0d0005c64010000c1100174400c80d140309544074100031040003102c0c9040300a40c002e200582c62070106070b03051009402d004c402490202e80381d8551240840e4000d8480d071020790b100b4208414400110780104004a07028440c2003100c9a03c00301003540c8050300c80078800c81081c3c49001558901aa222500500599203580303030006600049108400c00f4030300e25041501d1814000c00700301245003280c032503a005441c422240515034a44140022040c5600510590300c0540f21151081000704c0e10708032084074118094190340b50503c104000b4003c00892060010308403403030b101a5050304007100c1e2f0055600366a0b4070300d4000ca0035500e0503170192201001c200d0411080f5005 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 952534235 1250 952532985 952533031
    0x1d0601110319030e07080703020112180f0b0f1f0b030c07051203090f0703020603060d0c09180309050a031101140f2709010b0316030e010c020309100c050d08 69
    0x4040c2d4032106440c001107001d450003819281c580990840300c03a0341e1000e201800580c0e00000310400140f0703410804100440c030200120100b44480500500c8800b4042c6130204120369101500d1041100d20786000c8540d6513416490702c04003066200b5844240013401c2403100380c4009004560011b2210b07101c5142c04034650750780e8504030340c400f02c64408207004028005140000d01c0354031f90705844480240310483c21178000402500c0b014180921920714022070f01c040055505c0f03004020030310190308201240b528154010030000813038040307000400142d0f0200351450406101800d0320b030058000c05050301048019144201c142c0c0040207120400c0c03008400381d1034050300402c078605185400100340082c0766001c40a0624280d1942d2040303106800500c00c9a00310b0082e41e5000f40a4800300d11121302d5002d054005011411480c000c550174030202c03000caa60004001e1520343d400341c0b41204500d00049044a084500c818003c1040d004011071048c179505c2041c4841d0030120f422403040402d5276a0076 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 952535485 1250 952534235 952534267
    0x206030106170f04050304150e0d0c06200304050105130e040f0611031603020d02071a0103020916050306041a03100f0606020d050f0a0201061706040203071d06011103 73
    0x404600042c409404405030800201e0049402c401c45401e051402c0c1043c0d5500d903280d01490058048940451028080041c8104050b43e010500034050024162040c14080d2000d0180e020b400040f910715840d000d908005000c0c0c00030f0780056031000c1c50501d410030b001100c0d1b552190201071610004840040760000810350440c0c05180309090344403e007002c0d840d1690a80d5460003003401c43c090705108110f001000b44551181c4459149401030b5240016803000b00240074900340500031161171544284600c0d580210700e03051320700803202010a0781e03641c032580034003001040031074000400600204603682450b80014a0100d00c0140841c1000281d8002c280380c032941c5030b10030101d04d48806541044200c41d00c960f1000c0c24140c4040c0c080781c0c11011001d0080d108090f078444503200300041c103000c40c5100794441000f401c1c0c1c06811099a40c015101c07140c1d214070a64042e4030030300540c5170000e01034203027210060710000c2d90700e08006180d55100c0151518220310031070600300e0208101e00c0f041401c071130f5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 952536735 1250 952535485 952535489
    0x408040312050706050f04020d0b0402120d05040f080309031902040f020f2115061e031303120203061c06090813091503022101020717041404110406110a02060301 71
    0x40d403543d48510b0141014000e079980503064a00e203a0090f82880302580703442200d0301e4403d8100564403c00d48691020038003851541000d44454016100f240051651040081c03007110511021004299140e0006076202c0c03061034241581036009403141000d0000c0c0090850030180014000519501c8003c00002030b81d004010110040c0d00000e5002010309000c0c1000c2c0540181424220691a110030180d0500d800e81d00140d20801d00445c140301e00000c850f062040c9000a0034a0685900b00030f41c0c2d03107040119080088000c0742012400c0c4210380001c0c13080d84e00c144401441102c0003100e48400001c00d100b190b006440d640e84844200c004030383c0d0b550080507141d1000c1039182d20113140c9020340c07080300c1c100203c01030006902002000903a40e00d02d04140041c0c603130164009881c1d42c010072540284036a003802030141403944103078100011040003400c200c0c1c203002590345c515010401008100c0d03d0910100341c2202d0305000034014540309149c980c07003040e1204100c1d0700c42078907500024101c4c1c00036 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 952537985 1250 952536735 952536737
    0x120409020a081005150c0a0f110a14100c0f05151005010206091209011b0305070b070305100b0310030b0103060f18050c010e060d0903020606030613030909050408040312 74
    0x60141c5250b61003119141e0015900f00407803806070400c000202c44555600d00110300e40f10102d20301c00303015020700890b400c00354040e00146c944d0784246048000d0100e401c907410301c03030022040005038481d0105214030b0218001040714074115800314098681c900c4a03407040c0c0b40b4250302c00403800040c50400c4503e0100e00c0e00170401034140340c6802c400e15007603881d4100720f045400041c140305503100c002900102c41c1580705034103511080d10000480361f400a400608081407400c4601c0030626400c080100b6181c0d0141403075010707d0f0f40302a81030702502c000b034030780300d9030f20400c1d10082007055100400365030010407c0c00e00702e031141e681e922051164030003a0401d94001c2e59454250503940d0b100d101c0c8040c418880300e4200c0103182103844a9850305980002c1c141407000c00300e5407401d542c0e00d1504071541110118404c102c0702d000c030b080003540c03282c00700d4025000388600004500c1000e428840c40088540c9551445145403d20181c81c02504020b04100c8402005101c0800000e01d4520401c3c034180d12 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 952539235 1250 952537985 952537987
    0xb0a24111f0605030c0303032403072d140d030e030f0106050f0406051f0e0418020a0b03130602180d120f08060a140f03240604020309070e04030212040902 68
    0x4a0070050480d00c4030340c4101d1080e400742854080585021080d243d0002d00302101082411824001514414480f01c040340d16001e05600468840f0951603015101c22401e25000800310000a20718044032003401411400205500103201500d049410b03000114030918245010051280c08241341c092660460388541e512400c062210f030070222300107028108111800d2009500e0702000c12038109450341807914040700c40e0559140c06004401c2d01701c1c5008094007c0000c0c01012800e07040d070a2400c0c0040344180b200c408002080030407a0152405031381d4442c2c50724954000740c1da40000079400000840c00ca94882d031a141410b0f550710041c940c40900803c504c10f1840e003040300003040c020084543c042402001002e009142c2c40340000300081c0c40d04244074184501c05000012a078a030484201a0701d4415824001d6124074040a0144c844d2411041d51206868190800090340400c644e41c2c041070b840707104100820203114100300d40042c040d00540313054205424100e02168440c1e08a100300f150 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 952540485 1250 952539235 952539283
    0x14060306041506111612030c0c15050405090a060e07110a0c080708070605072112061403011d062715100b0a1e050c030c060601030b0a2411 61
    0xa400e010031803040c5058154180e05d24203041c0404480c01c180d44001e0108620318100c4820030652200140c060b00b01c0c0c03541da035031039401000e0041042c0e03c540681401402c542c80482c41c046294050181641c452000d81d4510f40e50301744003100c14080141d45000c662096520502c0800c3e820711201000d81340d1100a8107440b41840c40c003514240c040c0e4010001c000c4100000e80108204004007950400301155001d2407814168044440c280180a0b80310f4440c0342840001d0400c2c52404600d086040179002449144180c0214031030351040c1241c1e004654201e00005100c11106c40d03242006091a100c40741401802c3c070f1440c0e440c040b058860881c100c9520018040c211800600020061010420b244e10348031840c4001040c09400c7d00300043c016110300141010346010385d040e91302100c0120212a01d460408202030395820040c0d44450210f071501081ca002030a0010382030b010b642540114030315940340c81d2080d00794000098902c05c1001050440310811761070601c4800c0e040c882c8002e034286220 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 952541735 1250 952540485 952540517
    0x30a0212010f0f0504021b1c0e01020a031d0d17281e0509060a03050105040605011107032018060906040c0e01030e120a08070e0a14060306041506 64
    0x3030381a00074110680054108020080300e02c25010705a072015500503032110007100040a400c003049602107401e0113280c0f1140800c618603100040740d4813442e41d07410500c00c0568010380e04c412403548043d0000700d44196504606061a548200008007c1d00c40050491503071038200108c601e180107181da084e000520441c41803404c0390212482070848a4001d1440604840549850743c2684040d003a01ca4015045a40500980c10340711204400307801d065a4035034124000b0700408003401214881da10744030011425511800c0c0501500580308020004a4150384944d480d40c00c480e0100440d490880c1c010315856250512807403c41c0c01090312517262814a8401c00c0380010000f45054015440c00e1840c04a5a0780309107132511040081c03c0000d0900d01c8100c030103042c01251003041e5a402400a0403c4481d940f00a0369446810390366210103400a5010800c182d804440c82101c4c3c58100c040e80c540c55a2500000440c0c100d54002c200040994111004000c2c0618a40c050b9000c91108101c0038441 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 952542985 1250 952541735 952541767
    0x70506010f06080708040203070b0d140a0207021c08090a230d020a09090828110f0d080604090203010e01020c010e010b0a1412060a09020a09051003020603090102040b030a02 76
    0xd0500d4a41800d82075042c07090081c20080020010010492100003003415514240140c501030031030703149070f690707140c844c00c0d0300b18058102c03140d040040c19507a000007000078541340700f0381c0c0c900d560080000480060f0000c1400d20515a810140c640302010050701c003003503656080d004000c14800b03032242080a051320820181284405806000c8c20f1107062800059440440b18802c1e110301c0200004d00090f1810000154020000130300300c1c9002801c0c50f40400702281801441d0288150f441d60386080904c07501760340320347d41100419156481a0640403a581c0034958451303200754050070001d24400e0720b400190954a43d2003000c80c49950000b8922000c4100b80101e2442e81d1a41009210401401c030102c1d0355868940304d80007250075405c90405007a981c503100074405d138900804885c01d505082d80c00a00402d4194004c82c8039002e083c000007810708050080a1141440c401c0c20102c42d8074640a000c0250310080000341c45550030400440e003071401001860040304100d5006858007400380c102108 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 952544235 1250 952542985 952542989
    0xb130e070309020916140a03020c06090c0a060c0305030109110913050109060506070c03080304060207020604090e1e032b09051f050f01180f18170c0d0c1103030f07050601 75
    0x7036111709210105103107802c0200d030f01d04091343e000c815541d04503540045000740035040080c443c901802c41807210410000600210400c1d00f10381542641355902016614580f5100f001400b1030b0090004105007845940110641140040104d19000d0000c0c00500c82040324401400280c6d51400140320b212010b200c2e40001d400160707001490322680780c40300003c038461840001c200040001c0024100200c42e01901c25203940940895202e540302c40b5610050410310000050b14030070794001905031303e240b541034109180c4141c003462502501d80d11424800c07a20150110030300055500c1c8814138100c511031030606070f028002070201c16415001d2200445038044c0020250341c186010300003286400740c00719044a0510649007081e4400d049590f014003540c10013510b00614001c030b10120247e551420fa82c10310b1060800c01105d8841107140c40850040a001401da40d100e00300403800d07640100c240c000c0d0700e4000c0825054800306000000d1840c1e02c40d800311a540b00d0b0203c3e4020800070200001c0340 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 952545485 1250 952544235 952544251
    0x9120a0206100801051e040c0e0c07060e0a0305040e0618010b130506041406030a0b1c0308090615060705011b200d0509010804150509031b0f03040b130e0703090209 72
    0x854240600b44d5110400e007003404806e43c10f04400441c0400c00d0704511040200029280101d0b41d103403030b0280e220740b5003000740d00741c50050810100146a21022039461221941502c0c2c5038201400c241c010740c180e41c4c0080841380c0180084144c0700800300740d1404c2d00e00034000c80207400c1c2e07145800401004100100c0e8040f070b002ea117040c84184044180c1100c7d10402c030324150342080d101da54050740900a841d4072581141c0201e6803921800020a007000b682840501a80f240601616100c50403959000120744c4043c811a1003c91781201e0700e08400141503041c0103900126101c6100d010201300d51103d804141c0200e02e01e6040a40c80741403181110119011b41c2d0081c0c10300e0340030040c000e000782c4a00c1d205a0704000c50f0000003010490380c07100c2c641c02d800c8002f80c100094545080720036580c2c2e100905843d40742205040c0c01200c920001420150341902d08042d5041524102081d07006400c100c5481c408440a0400032405145009800788142c0316030760042041405ca00500004400107880e40c4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 952546735 1250 952545485 952545491
    0x2070b0f091b06030a11041508040b060f0906010e0d0b0a050f0709060e0f0a0e240604050a17010207051b04060f150c03091e0e090303061809120a0206100801 69
    0x1034070a43d25002900c2d4040944c11002c2406000030000700c246201d150400002c21f09007140c0721030003586c040c140c0c6101c0da2040c1d601c00045c0e1100b80030408448600541e850340300d80e0386c0300020401d510458401d088884003801c9400b09841da81c0d40c400c0041400c4824607215660f81080102094000c80c40c1a0049054107209118504042c4024100784004924034007809042c02061035a03204c0381143c0c001024075580314011810a0080003551000e06410709400e20040c40c892143c91601000316801c552000348410b4610345041c203001c0ca8012040300d50b0003a554284040800301350103000d200110f262212480700c0a496050800007150010b130069010414054000d201d600c090f0051420000c0140c100800d03220b4442c50122030010b8150081100e106040c2c000c0042e170101d40e0707044410741d5030190007800950344280c00c4a90300d0000701c90031640b20000c1040d82c003480045003003054204142d02c003680c041d821401a5103105521030312251005902c20700402000d61908101c82d0054940070000b8 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 952547985 1250 952546735 952546783
    0x402040515090f0c0405060c1b010207080c0418121106091501411e0102030304020111030c070e07030c0e2808061503160f090207030302070b0f09 64
    0x850b40300e2070010140c074406680ca20200b10b0b00010002510700410004022999a030f10340e2984940768844480d031401091906a4044225800418190196a4440d0080900800040070840503280300c1c070705900505500e071042808201800441840080c9545501070000342101455282c140c0050a142907504180080d01c0d6440c84824814110742d902c4044943c00580e41195000a60300100d0442402c000f00b11020449401d40004805904c0100c03010f080650000580e40e0041310f40c07021032401604100005401580604051403002c1c0c0840b003117900704030940754228680384c0c42d500449031021010042200c00d40d4580909680003105180c230704a0101604041400291103081906100d64840c0c1c0c00d1000d0074903108070310020040002101c1e140e0401096280948030a038004900a010305a541c80305a655000101d003150100306001700514600b041c24002504510b030203c003015000c000d5140400d4030183c80078044c1260080e0728800c0d0404440742c5140c0122400d03800c050b50100151 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 952549235 1250 952547985 952547989
    0xf0209090f01270216230109123b090c0702030a03050a1815080f070c1502120709080f070506090f0a050d03030f1416181d0402040515 59
    0x103411a4407000c0300001e0480410190f08101a006543c0c4540c451000358280d9401c0c4a80fa02030119440c07403d0540380702074000d2140307071803d90383c1004002e45017170b19460b0b4165601d03209504100803844080e90080548024038001d9040d040800707841100c4500c4036143c40c0341440c0c241741e0326400195901125240c0506540440c1e19000410005001d104012802100e280d000d1030003000b00540449110710000e4032107070503980820010b40c030400090840c0000540340740076621114001c034001c0c0c80d88485c05400ba510407481210145403641815002e11400c5a58000e250a26002c1c1041ea20354200c8907040c264014584100c40203e544190f000110810041e1070740c00c201c2c0c111000c1618000c0807010080082540303c01380b40d01c8983c01c022110745010525a0550040c003d04112800500069080e24104070050318203950044c0300c801000158400e079401640d801c04403000c51040900050390f100700751220811b48142812915000000708400c43c0744c20b10507258028894a42e920b0b4403d04000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 952550485 1250 952549235 952549259
    0x191704110f062502150d050108120c0619021b03190801061b0809090f160e090118110a0c150218092505072325090f0209090f01 56
    0x1001d2050a0001d081c100c044d9252002500811611600790558420840a004c40201403d01c14030505000e44070092418801d01d50403900d12004960051100f41c459140050140c2034401075000260390801c510980d10451182c9000c0d080ca00002031038550704104103044540c0603909040c000c01c0440d070300500c201d540041c480d40c201450a84d690b0482e000310b02c0d103520640b02d95120954040d880c6410464600b5013481c0a0344a42500314424040344071102099035414800d04529502c4243c080040c84000754038000183e1756010f0308070102d82c41201690a84071544a004e8a1001035001d01c004c806004016000c400c1c40741c8440d00440c40c4c00640d034010504840c003000042c1c070038200d03207010070071150b182d40c1c3c051000018880045034411204201500039800180102e80803440401071481500310b00000d140020445400b074900c4076080b0604402c00b4800c405907a064410104003c52406281d100d244440c1411000c01680c6100240070028201801010030145031000d8005002d4a10045 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 952551735 1250 952550485 952550527
    0x21f0c26011202010c0c0906030311030903060a0203130f2303041203270603021b01051b2a061b0c1c0309060e010b0103051b191704110f06 61
    0x1440001c1e0b5015440100d80b0080c0c1510f0190a071301000b0404549814a13074400c41c1200d01c02e031074070311007055000c0a4540300d006204449505403c030200181c46280c03160001c40d48010b400c500d407030060302c06503a101490f4101c080266a1510360003401c50398800080a000c40700c100100c01981810700c0c1201420a01101d13440040401c1504c133294003400b1200c0d610903040e0480403c40c0d414a0ba10b0700c4004000b50000a171030b0503010000c4d209a4002c10b410711a00b03000d516000d4070002d10b07888a100700d044550184c0702e02101144030b0000c00440c2195456280745050307620014103402c0c100b203051500c0134504800c03600d007078406c104014800e490307001483c1c040421b60701c080340c0c1d42205242c2c025002490b1000d0b024140d0b9092003000342042c0ba06500030840c070f20090301d00b0416501d03030100542c1c02c090034032502c0305407034000c01078086000880300c2919486040307032504101c84259030700c400e5200300c0256011201d09107100070500280c94541c2c1104480b01050381c0075410b06460282c910b141c48100 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 952552985 1250 952551735 952551749
    0xe1c0c050c1203040e01060c05011a0907081807170c030d08040b04170406030b0a08010606050403060506211605090402010801060809010f23010b0403020619021f0c2601 74
    0x850442a2181c40c24000e4030000c01440c0c0050051b503a407444082d00141980408a56035461300a1001c00b090020080295080d000b405103c0542e80e1941c05403a5642e01400310a290005800d0303003484828204a41c030090032200742d107503501180750b000c05483c09940b02d044520982100c0596180160301420303855025401140d41d141da130721942030265003074100ea4a1440701c2c40c00000c002c10501e406802038100a401681d680c001d07170b559114154200d401a00070391002403c03c03c4208086903031f0350401c0e070b00100000c00202c0c0b00c01701c1c0d012030f080341158542a01001d401604503458a00e0f00415004000c01e02928540c00c80d107801d600007054407205015003001d2080b40408540c11140961059102505192040144070018403202c14094602445554540312400012401118030002d030747c100c0354054681c42c2000481048040400e2000c0210b00031403003460b5004a00440fa0100344105407006640040c4075002c142c0300800b0406062107040c0300d800c10b0039103000944426103ea6044542c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 952554235 1250 952552985 952552999
    0xf0222030f15180305300a1109031009140a030f03020706091703010f050f13091b0e16020a0201080a0c0e090c030702070609081b0a08010e1c0c050c 65
    0x81c0b0b490000203102c40c801d1607852880800380001059041002010f10000e00a0701d8100c08041d8800d98100c092400034010040030141c001c1080d01c4410303001040440c1c01039a15609080318080864601454402007001e059190310388d581c1801841c014200c407403c100d50284c10503d000e510054014265a4400010142e001440e0000d0019a80c03040f66903681c03086420645040c070200d0364000c0d400a0150341d128202e00480020149030101e5002c001107006444d240c4460000f21000c0010216508252103500140007000e40881c14140d669000e8250114591510b051151032400c03c106102c84502c1998030035415031001d03030703001000c42d548081c610b400451140c50b80e0304200c2d02004e0700341519800c1407250050029881c42000514402c9150b40e00f191030b241e0766001d0448500c2010710400080f03400c00f981411462150b8840301c20030700005460b14031b22079518500d04d821282c55074a04a11600442000e42d00b02c103030500e14108140c81031034a07510000603a1140350300e940c2071443c118460f4403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 952555485 1250 952554235 952554263
    0x1401030303061e0320031009330911030d0c0605060d02091b09040c020c10020703020d0b1b0f0702130b060405040504060e0625090b030a020a02100f0222030f 69
    0x210303a00950405d19005030940b244100400c9051020b00081c0c0c170221400b0900300300384181e21060350081d0003000010040c2c021000d0000700110010300c1400e00648403c1e480310040d11407078408002d40120700c401a0b4808440c0c0d00241070581c105c50024200c00d10407420900f402c0d000d6030f16090001d400c44070000c1c5001aa207440005100b0a20601d85440e03009400c101418081c02e4000c05c10350b103c18025200420082090303041280c5510f8a030100952160740c43d84003401040c90005000e622624413070060f47d950882810050300c1e80c01403445501843d40006104085042c520303c100301d4811000380030310105071035a0000e0300342d00440c054540504d55850000c0d0a206c0190440e0007103240b288141c851504281181065501000d0168000d01058448032908113104181d100111205203005900391740b41c44901e40042e5002d8043d140862003a800b400221505c0c5109002c01c0344034207070005070b4950f00c0298105522030580c50f0744580880310142000807a09080f9041c001503030000142d500d410b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 952556735 1250 952555485 952555523
    0x2040e01032003121e041a03040f0203060c0a0216081b01090302120f0616090e1e0f0a0c0c020a0312051903140c070c03020108191401030303061e03 65
    0x11880451040c0e044c801c1601145844c0070b50801000340840d04d44400084a00c101c4550b1035030300c103e100c1c0500101803c0a4400041003840103107400a00c00e07400c604800300036030006440c020040e1110070a0801c0012001d1a0680410a41d414814429030020106103840f00480d1540d0485403600c21000c1c500c040c1c00340580c49042040c000d1036004112a07200520007002d40e580d8415503a4003e0315200300404240d12404a20480202079141d64820980f1814107007101661003026081131f00d88050380c8100d0a011204818207032142013404d13a0200c407071400c0c050740ca00b642c207082d1800e802c2c02901c001000c050780b50f9018640070340b900200203010040041070110341500c9130f8007002c012a40d14071110706600344d0641000c00c038800303078100b000c1c1141c50380480c4804a1146150040c40303988001010001540035000c015070100e010b01101c1203455005000e0015515181011028202400d005108040d01842184042d04603c40c241c0c0c042d207000889206104000d00000d451600c0c40b5001041c02 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 952557985 1250 952556735 952556783
    0xc030c0807030e03090406090b04050f0c09130b100305040303050c0705060a2a030504030f2105041e0516081c0c06110d0515030607200c03010501151202040e0103 71
    0x45c2d1002e80b0802581d561884044006c20513039052520a600b01804601d0041d21500014041c2d01400b9889241581d03000400c40842d9013900e0048001da25078020340303920f9075031a0390700001c030416440102d26407509190040464000a0840c1a920340a120200218000058036540007411720b00004d102d8060b40758054428403040d1416240c90702c03161080c522650325412842c0141c0c030988402102c00b40c2d41100341c455003c1c60141c600e18404141034071020507080e8115681140c010f16242c56412110f6001c4044500f0300f420036203007a481102c0340180c0003051000c0100502520002c0c1140b004003c83d0740511140c0f44080d0310400491a82c00700505c00355500480d00b204d8021035482da10102c0042090117013100704c44503003030380040c1040f980040c00c0200d40070b4400d0300303a9500d0f62012590f042450000034004c52103041944100d4002c84890b440903c00e550113002c0d04450086084080040109103620509a001025005000c01c0081081c0a484a4103480c1d11503045800b41c45007860000003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 952559235 1250 952557985 952557997
    0x370e16030b2103070501060b16030309111201020a02071203050301030b09030c24070906050307051602040606110d091508061210021309051311030708010504050c040c030c0807030e03 80
    0x8101e442000c02d00c48002c004002c02e01c662045c0d00901c50300d546c840004000e40034508240c14090070107500c3c0800a880b0f5404040003511070b81d000c054801910b07011880d640d100b850b8942403a03600203040d0808680421111009050303c02050003034400503a00104940010b00c0b0040c04140d1400210346200024802d0300da07081891802c87e4803079104851070041920711809080100c406140205030042c1c81114140141d604035114146107880700c0034200d906038012003413042c5104205c0c0000c0700503079950003070034010805a65103040c5020001215801c0c600022804003d21042101c10043c0306400b2500c001c4031261810b1122859481002081511400c0400d800050080304409600c1c003030140d001d080441c0e248a40781076010f455040c904200e900a0b15094481d1062040545c00215002c40c040d082c00b001405941d0b61302d9545400600b503030811c0c1c1c0c0c00c58850700012919003240c00e291043c2c181054083c9000c2c040740417a6130001d0207102000e0048410107841e00110a0360324010411958 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 952560485 1250 952559235 952559269
    0x90607030512090a060c1e0e0a0b0f030604180515060607210806031f020d06080a0b0717060f011d030706090e151e370e16030b 56
    0x1055250003281503803216201107048580c04d2030300300c0e076002c070521031291f80121001403040c45c50f01c02615281901c0102c00b48419a521030400400402d140d0040805061606400412180c0b2821b15204000a589a9071041000100288425408554006022843d0751030041194000b40c4803440803540303500c02c10502410100000703480082400c1d05014001d0f4554943d55145115125241050b4032072942282801515180a00c10741144c4074680c01010003c0c1c0c000000200a07590382000b90500d0700322401070328003101d03840821642e15040ba950071820218810124001d290020008a416054207002130400c081100c101c1080c0002d030014106591004040b14071007950f81c0d174010500b628500a6036444088400410800d90034100a0308640c03000420b045122030004c41c00c11010880c841805a200c03418103044154001400030000041d0f0300c0c80036034020f040481d04c14103086040c5610000c1041d1440082040d1441d4105201203140e070309240104225146100103060000340c6e882d040 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 952561735 1250 952560485 952560517
    0x3140a090f0807082502040f110a08130b0106080906070e011b1b0b1e0408190305040b0a0815030d0905041107060c0f1b0f06022127070b0906070305 65
    0x214181c6401500401c03014807c98050142d40f0007402250190f0307400f001100c002100600002c076000d0b000c0c4007440d610101880541d00c4e00d01c00743d1190200c3c55002e80c00714022480c007905100402d80d060001c150700c5100ca007044118540ca4200007816131485403120413180315808000000c20a0b001480800034444040020000c0c2d00c5010070107260b4092110940000d0f1000000d008900c2420142c404445543c0c001c0d20020303115042c0300540ca00440d00031410403004200101d050380000b0050b0401c0303e12552a100c80789020000c0341d100c42c00e4181158400d40c000400101c8103a0f011504209030b0304103881c040382c0249062954520760255070401890a810800784840c825440b08084608007116659030b91001000024100e00c40039040002d80044240c400290203d1007580040964284039007001101c6080c60203440c50344441a02d015200500c82c030802080700c2882002d84503a100d400e009004181c3c0381c03e009200510490014501a04003c07403904207040c0514156600745001005103 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 952562985 1250 952561735 952561777
    0x80721021c0f06060c050703020103052e18021206010e0a42090312201c020304080606130902091003020415080606010e0411040603140a090f080708 65
    0x2501902400d051a84900d10348440004d03614850f2401130102e94000021b451000d0545d00114007a200c0208000c0c5400c00c6844100078508a01544251556044400311017241c01c01100710a90184400742c107003510b0041c4200e1a101c1d01404810360010400d08104c800c003101170001c0b0740201c0d0203030701055078079000e840142c00040b08003005040112550745c040d102d00040c036114071030003040007044000040d04c2078014070006105100400c2d0040325070410465500c0c0103031816280041e14020740311140c004c0741d05211041c216003c7c000710000320340055030030541001420359461400602c2180308140000925484c2c10169211094094000d0a00d48091810401e0000300045d00e110480c001c0c0d250559040e52a0742c07c80c810015208040d010740895142d98004440310440780741072951140e9030740724080f1000d0389040288003c10346a1800701d82c1103a00180308501c0c03e0f0007404140e403141041403507000122181c1c101218694081e4889485a03c0d90501485a0040301500a012049032040c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 952564235 1250 952562985 952563037
    0x60a080f0702120c0c3c011419140313110a17031801051e0702150d1505150304030804050c03190212011103060409022205010e0708072102 61
    0x20202da0171505031011050743e000207800c1542185010f005480446003081d80e140618034814210303143d00b00525040e451254030a01002c20382c1c0c40131140107000021844180d0b12580c100900d0100b9412040303002d42545842030001842d07a00e008001000c1c6580e0f0003801c40644d43d06880c54010b0400c081500854544c50a4074640d26031040801c0428601e0f0035041800c90762092081355014000c0313a41c0904450f191803804c1034035402c441d00407a4003c0c0400203032a10340b10400701a15070304c40c450b000030801c3c1085c000d07091011003068201d10700035040018064500290301044a40040d03052510440c666206c0c1000303070603c150800c2d280e6140c090310040c078884040e00d40740e10000d140203c600146009000701003500f214680020314800c0101400081c00610746540040511400035020515501005900c807036100100d04100070b1043d40c1e00014040742c0f503142141c03680429541030111040c109103c0142003d030b40300c1c0002560240b041d820341540c900035010764899501d01458583c08da40c507900 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 952565485 1250 952564235 952564243
    0x60f0c1406040506010e01060f05070201031b0203091801031e0c0807030803011a03151c06050a050a0518060a020a1116090b2715060c0d0905060a080f0702120c 70
    0x1070540c2c15201301000803510308880140141202d19985030520311140c035003400c1d2202d40128006078141035983c002e0003004c0c2c115140541d000348041c0d000c0c41d40d801042003000f002c00070f50324000e03030000621001400065aa40c0030103448044403c101d414801d0145000c0b400618280c0225105000301280041002200b07000745058441c0f4040c80701d01030501504c81c5800c1e00040300e945100844002d07044c4858100784a00308813000c501c068580c4507c02917160401642c0003621300040903a5504200303c0d02c000184501034205003e00c102c840c2807110810303220707524000588101c50b000c3d400a03089210a010b202d25540006d40c0c802960201250100c0030740003199030388903071400307076043c101100b60500e081d42500c151840c0e0300728180003440307512280e10700d821402010400002044081170015680f0344004d0009103c0a030002e0010214917140100780f6002c0d40d102038000d803401c5c03100c48406030300b004085500c8620628003c0407070b42c550b00101d140c018011810300e5030070000100b198007004041 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 952566735 1250 952565485 952565491
    0x40b04172d0c1e010609060b281418040f05060a0e06101103091203040312050708030109230a0c0e0a0522060f0f060f18060f0c1406 58
    0x3140c03484000503481000c49840b440b4004802034000410880307034407641c0e031602e110320b0300910000180c41780c440b05508220b13199600410700640e404503440c4000709a031024000300d5002d000702c2114120000308043d11001d9101c001058542010038001c3c0d556401c02076154010030000c2c4240f0058440401c50001040256090345c09104080000b040d07449849413214040c03440a040c1400d06440b40200b01d80301c24410301407030502d000030022140c0c1e03607603103038010900145000060344da914594074008000c1d030540000581440380c03d014410110305901c040d00d0455103124004038807855071504c20707840e190700c2e000302ca5030041403c0c040c043c4201c001d40c400c81c1110003a44458005000384010001240014803809600c00c0c5e070b100007041d1140d00034080e040c440108800104110341c594001981c2001a46c0014a40380f0000c0b90402c5203650289001801c0e281e181000001c039440585c007241080318900403071003401f448004507140e803441100d40c9040300d03030050170200303021680070080e580b212025 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 952567985 1250 952566735 952566787
    0xc0c060e010b01020c060c0313030503090a0608090601030210050c01240509040b04030f11120a081f0519050d080c0105060603071b03170a0608010e0c09040b0417 71
    0x480021460201442002c0b84020140c0042207190007040c00c1001580c000c04142016000a0000b601c0f000086281c00c0061032141d8040e544078011003090041a1007542c0c00441044001c000b4001c0081c000300d001c505403a0161203d401b182140d000a50b182d01c20b1070160410b0798030700200794207001620071f008030007170303030031016900d44942d60b60f0400408841c04c5d500585000c4069011a000070700a007012a950600307403d01e11504040b0400c2c20741440301403110700b04a07040c00210421840d600c43d414039448440010007000c0e4010f00860703d4611440b034001c040c052103c41c00318105460300e441008004102c02448580d0141640c5420030103900403601c0f04070198201004110240780000a89200e40d403a580c0b80c100447c00c0400349a041d1000502c2034051020200702c42d200c0600c1450f07a180704980206010411520313050035182111885504404c00f0f030000f07071000c0c08c1540c55451003608141c03c044d140c1100e80b00c505000041c1c00610460300d031000000202c544500c0030718001c22a00c1c0e20f40c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 952569235 1250 952567985 952567991
    0xf0b040614090c130e1f0e060108011a040507050d0507180906030615121b050909060f01080c01020312060f121605090c2d0d0b0a05040635010c0c06 65
    0x20801139641542c068050000c41030700040b00c040048190343e000068505040d80300800d0010f45101e410781401ca00703030031907a8a03945949022030b5000c203440d8851881e030400d41d0b0811862034441c3c8000c2080c000e60184201558032840400c0340c035841341c003000584c1e03130007060311402296951110000910081c0302c1220042c1c204280d04041c203000840d8807003120780305849030741681c00c2c940d5024206181c0303800503808403181030008252a02c68444040c4168060070080005003000d00c1c00c03540c00340341688203801d540e0011982c081d203a40e0100a81d120000428005443c070b03268000054410b02e0000c0405030014402c0c042510201e50005030007150020001c000c03c03405c2d450380144001c40760119004510400b0400509104880d840c03142d86241400c499003581000c0b80c099030036059032040035189041600c81c2410707403030342ca01444108014203003106c04000d150b14040e01c0d84000c0340d00d040850f1540300c0c2d050003201c0c0960000702000044c50310900030040040c4041024004d132000000544080b8a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 952570485 1250 952569235 952569259
    0x60f120a021e010503040f0303090c0e06031603082212030302040e0906041a04020622050a050d0b04060e0703050a12080627060f0a090e0607020a0f0b040614090c 71
    0x440d01c1ca00c82e014a81030b50340d140f03140d0f40c54541005403000c4210032030030541e50350040c00202c0d83c0306040c1e00103404840c13488482828544105841d0144a44031001005c044141c00c05c0000c0300f0000302c8a080240a00c0a0400e4550381039640011800358041c1300d10040400e42c607410140e0590040045e950620402030460b1160f00000382c3da49411203000300b1244202191844804851400981c0302d440101220b1400f03030280c0c04050000459403881d40f10441d0703440e00317000728a043c02c80000644025994084242029111050016409000135002c035686414a0480503405d01003a4081c50b008011506110210701c0c00034039299441548a0004140303101240180c0380088071042540c203101849420408004420f084001004d81403a6000e0121b215081558035104040c0000301a100d000140341c40806c3c1caa203081c0100108044115000b20240d0030010300c00d0329030250300725005081c0c079645956030b16014000304660546c001f0180030303d9040040340030000406249601056440342d41c581 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 952571735 1250 952570485 952570519
    0x61e28060206042a0b1902060721020912030f07030305010e07020d0f09050315041101080c1903140421030501260a08161b051305060f120a02 62
    0x1019540284404c8044a07aa000c4004004c1c001c130080441d2205460305950324140c02550343e1040c0e410307980c0c581e007804641c2400c503018080c40781d001c50b150a003201039144c11600b6404040c090f1a00c09200c2c1d5021441d030085849000a980f84260848101c951b58018a44080d102c1d4214041c00c0340040d0a00002164016480d12894000c1415400421030124003800c26a10654401400f07010400008030001d0290380c1002420708a003800e24000041e4180307414008546022424124140a0610706014024001c0000c072100984918480c60308907050030011005000e01040d005000e071017000c181300c1480200c2c50001c01240c02600480c2440220020a070f00b6654248074110315942c0290724080640c25030070100c07810900c00019070b040c2c5500c0340e4406446030019400790019641140800d401c202d1181144034056240410a8414928117400684482089140b440030552242c000c1040c5071074140380ea0f801120700906103400071400c0700c0303095039520640000b64031606a1001c000006 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 952572985 1250 952571735 952571743
    0x6080a0b01020a0f3f2c22020310080c030a050d0e0310020d060807170307020d1a070302030a150e150a0306060602061005010203030708061e280602 65
    0x895110402d05020321068903105c07500d56089401070860b042c00e54545406201044c280c02070402031080000c1c03000110440100f01c6880040c404030808108100030400000881c0103000c03c0c4401c5072125071825161000254100c030410114510a0000c41408209031180303005c0c07000d44880d80101c0c4c1c0b11024407410503540c0d06410902800b16004000505845482a90b03040c41a0700c02030704442000d5441d0013410b049038041e80020005650b00c0c2e42c240200d81050214a0003800c80c02d01e8903000540345000203450b481b5100c6c00078450320302a2011020452140000d515480d41c4100d00c030030610b415940500a54800c8030a0302c095490a0101007602c83e0310040715080e40d80384620415190303103c03c4086021090041c9059100c20502000800a030f83ca02915000e488503a004c0c041e01c1c2015803020700608155000b203410741d0003d000300106242d004032402c1d80140200c6441e5461800c0c0c095800e6001c40c440e0080e03400440300305600f229003004544544200d03801020a03d5520754038a402c80e16 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 952574235 1250 952572985 952573003
    0x80f03131205032802120907030302060915190f0f0615091a0304030509130b032406010c170c01090b060d24180506040309090608070501210606080a0b0102 68
    0x4e4000318000203000000030ba840203562030402003006150002c0c06200b2013420104030303018070036584582c03800e200301681070010503005580e50008051110000198030407400c0c0040540c1e580e0200c0000c100c0480501d50040184d40000900030005c3c1411406040f0161140d0300800c208104c100c08911070003032207118030000b1901036041d2034242c440000703c0da071140e6002401c00d4041102c02c1c481081c29555280c90101da4004840000800301c079460280f50501594051200c6000c007207588505102c0030104a06a11201c00d28000c540140c5078a01280d50144001d0340421240c0040f03090351307003040158000610b07203014810a1580d40d44810800100c01c00c50003005215088110301811040191410180c00521940003c40c07440d07202d01e44100700d0149258161001d51290301400141034000030780b4001341513400024080b8506140308250365000a05c1020f04215000c5a80101440000481c0b00d980c900710350700f805415528140100f0f0341ca8181c4940c80441d20344040400c00f58000150014 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 952575485 1250 952574235 952574251
    0x308091e1209180906010819020a15120213080c030c010203071e051006320f011106010f0303020f010b1003050c0706050c0d1a06040b07080f0313120503 67
    0x3901c101054658064104480080d0030842c83c0e4001c518212500e40814030800041005140d290b240982c80c41c5004d15940c2244040d4111003000740150300c031000224190b8000141040d0420403100f4115682c030500319150103031501c00701d0210303420007441076414110780041c806c84500320403039001c15845240300c11805015900800c990000034464101c1c0c00c0d24140b80c40200300c100340c11921118146020140d1a156507a0354443c103100003480d294140108100300d03044400d01200007404a000c030610f5a156920408043c4e003858000d038400c040441c00f9545610a4440559507a1620340101175903001c101c01500805c0c40701034610700c05204005d0800001410602c081c03000000030340042c44c001d4111000c3e10300c100824000701d6510f0040784e0060407240210765a034a4070460000403100c880085415035a4100c602200564900042c0c0c0c094032048046e40e5601d54a525210070b0b03620501802e110121000b10805c407030068907402410a49000b0021407030100e120700403c5590b40b2040328142 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 952576735 1250 952575485 952575493
    0x503161211030304120803070f080f0a1e0204091508030c10021b0a0c0302011805030307022e230c0307060c020f0a0c090e0f060408070c120308091e 65
    0x200c0819603118500040c40400307802d0b00c3c5016210340c2451043c407895202611300d401c001003072040e0540c2c007c18005c0400c0c030034038000007141400480d03810320301d034040c1c08d00302c419171120b696041c8401c24104021440101e0b0b44d045645039640c04418000d88250020741c840c6c1c115101c000070305050b0110403550364072800c0c400f40641529080700b81d8025003010f20800741c3c81d034031501d000c51015020404c0c0c01c44039000b401d240e00807501d58400100b50240e0884a040142d415502c100074035203000041e145041d90449002d003011801880c0d541c00c084c03205800103501e003034110020090603000921b00003182c40380c8942c100c6120f080c042601d1584039819465400350300400003031011070703025840802c034038010b481500c1e0900c806090003480e2507520002541c0d01910500100000b83c207a202d5607210f850113801a000d20152421030039110180103101600c1c60000040c90f030108485c0503140000b4050502c550003132000d5a00380208800000c40b481d98044c403501d855441003011400d40b40c00303c950301340010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 952577985 1250 952576735 952576769
    0x150909060f0b0f09220b04050c100e0d06021e04030b042f010503130b010b04050102010b090106020a08070809040603061406030604170f130b120a18020405220b01050316 74
    0x1448894a042e000500000c1202d0703090342c0046d8407201040d01490003200285035140c0c03500b04200c1e0030b045034030040062005050003c5c1c0e554407200c14100989400c5200141c8402e0070078000d690072590600c06421107140054003104201e20003411a0040b406000c0417180a000442a106940003280b0300f0015000040c88800456114800a681c4045480b883e8054000503940d1143c050800f03811460780d0704070106040c045540d0900c03800c2c1480004807031800a5524201c00079450b02da800c6406881c40c400024100c040c0a2008120703181e56070302400070048a40e8a0030700b038000313208039256242e58950b00c002203126442c000403103d0246401c119000300c00f0b80e54400c11185a070000c42d04121160b81440f150200074442d030034001c000c02d151341e115591440b058050f6903014030000c0000502c14076000303022080d030130148000103a140e816a4002810b446844500c04004d298031801001e00400c50026030410803000302241c102e400070b078100d03907071802c1704081d103c0c42c00c10324015074007901c1441c062 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 952579235 1250 952577985 952578001
    0xf150301081b1e030f070e1b030c030a02030c0c03120103200906010f0912050606150a020d120e1b0415050d02060a030b12150c0403050d03150909060f0b0f09 69
    0x200c484101e03002011590000c21803900031b801d01c0380301e500c8000c0304801c120030000c044291410118005062a001c1469441e001c4101d409a000140811011650220000d403072162008104c4090803140c81c00c60ba203d01403081c542c1031511003400121038003110b024001c0d2010740c80320b510740b01924005001c822103039500c000440b031002d180c03190b020412200000004080c584c04610f0040c440c002d1015210a2405034107010440d0540907040e04858010071075000703001d40c04912424155014580600301d9041c800002015000c2e4805c07070711407402100c041d90b070541407140102030310f1501641d0500c00044c01e20000c1d100c41c04180f28250b0000c00f00490303040180703001002031005150760700f40007030903484c3d81000c1030144000c01107243c00c42d409044407200c1c401e0000c40c4c140d03002d00b0001204d4640350a581c4c0b020345400020b0b2954044c5500c0b01024180801464134440191024403400c00a0003100e052004c080d00d0454480300d400c625003807045506081940303115190740806044e007005134441d441 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 952580485 1250 952579235 952579279
    0xf030f02011211070501020d1b02120702012d0f0306050102030403021201020d09200307030206121008100213080a030813030306030f030305040b1302011202090f150301081b 76
    0x20502c10000d6071101854003082d10362015100140c00b0740700043c0c41d00040380070103045411021284501c3e80108820b1040e440c2c0c0018264080c0a5401c038540c7c43d03404034401a515410316006403600314145488001803805045906403c0f01a507541d0f00d643e00b42c41c0c403000d40032600c0c9805814016002048203002508004803040030040c1030a000510304800290b0400c11a8104441260310031041c240e004000418403d942c0717410341b812005080c144d031443c2d0006502d80b10303a800c842d41c9501c1e180000b980c02c00400210b40003c2032144280d415000300010104000d44c40811229850a001c0d00d0100341325a0015012003543d0713064031403034100d4403104e0b1021145070001400702c0c10075807a41008800181d033340300c94803c054441c0d24040340904146c17410510800c402440040b04164509818000d41c4e80000a425201e4850302d005030781c3e0418001164442c1d00c140c1c403090700401841c0f04100390803514030041d4101c9003140c05990310304404000c0c40540c20318a50301240d0090040b40144403d5400703913 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 952581735 1250 952580485 952580507
    0x70813030c05060411090a02160b0406140c0a1d0d03030207020319110a0506031b03090a020901120506010602060103050c090a0f05090c150c0715020a050303040506100f030f0201 78
    0x401d0a444803940c07640c529140581c01c0342c00700c13420740c9503c000600c0c504210768000d42000c1c0c404015410041903850380c0c10140324854024001c0d48108000c01d0030f018066025503d85c15419400107068a00740e1214507155000d1400b4200148104c2d1858030130300e142442076241020f005200301e0f417480e0b184d00c0c102c001c0d4008450aa0780740c05645801003041c0920f80c00c0c02102440f41d000d41e94095071100801c0048800d50340006c0c0900d000f0020032000a800380749140a2160440c0125101e46564000c1480c21401d031400942114003c0008107080c03080058030705e030180c414422541185e80351034003240c440c0e4081c4001020341e40b181541d0f0301e0314030b41541859800103609200007600c3c805003251005986007602c1030320041c1c200c451424220f040900444080398945900340e854046240b194559546041c45080d171503140400c001c6c09624808e02816101c00c3c0c02800b00c0f038980c24036081050f2617280964041c1e108800011001176002901d11003c0100c0c0d42050300e00300c003c9000c1d001540c802c0d4803e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 952582985 1250 952581735 952581737
    0x70f020d060e030c071508070203093115090b01050415050904180201030e1f02030c1603050a080115140309160803130b030906191121060907081303 65
    0x41c4960b811102410005041102d02400003030507110700c2c0c00200072400c0f0765420480c0070841c0789000c00501035000004c454140d003003583c5c1c101a1814412410300003c850300064504841d00402c00d07405070340150810b00031402400e10350352400c0c0d0343c2e4108408070f450405a007804074000748010009114410304d014441c440c18244680340500c40800038044036401c41080202240306201413055513810b107d200240b88008000f41004d03100c0605041c500c0c0d0703403002c20154240d00000011049280901919012081c0d810490203021545c070300071380b46400918184000505103c000114480c0c6120803460524598035601540050682d0102140d4030081c00a40c092154884003842c807460009100000c12001025588800c03940c144200c0f40e0071654060300e684c610a0040c421290b0001c40c007a90019600303064918862104400300026110282410060620210b03050040c14075461322098443c01000c41611145c3e0341004000706610309844a03000030705110001841e000382030003490441030003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 952584235 1250 952582985 952582991
    0xc0904140a060c090303121a190b161a071b020d050d030203090c04020c070b0903070b0f03010e01060c050601090507020a0b09030c0f070303080a0b0a050324060105070f020d06 77
    0xc40e84030407041d01e1500e4840c40c00a81c0c0460100300707040d8400034204540347d40320000d00a03484105009003281d01c2d0742d04103610411322840002e81c0c204500c041d8000170040441c80c01d845d490030340d05001003813803200d0f0243c03421070310100310030111406801b10300c0c410b01040d100d0702162054120785902199001500300e03080f003121082c05c00820001c11011110b083c05e541c015a60340b501d184018107207000460540c8c0106d0051200002c2e03018042888010345480b600f01039111881c04000030320300b290340e030300424100e1400110000382c000d0650041d0b05035891071303500000d540d9941d10708403011590460040c0c800d401c1540140a00305150b046180c100a8610450740e01c8040c0b9142c880c6119030540301342959610000d8154070016060000301400010300001c2c040041c03460720050082c580c020508040700b9030301d80440d0940d47d07407050404040c260240440d9030b45840201d1101240940d00030a02032400008001581c9600c10000c5905540d80001c20a155201d01e40c203110004048000407681d16031 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 952585485 1250 952584235 952584253
    0x306060203130b1c180606080f0307120e090403030b030c0a1217040b0a05070203011a10080718060201090303054501091217070527030609030702040e0c090414 70
    0x2d824015903d02d0032030807505012050013072502070207c1d81198050002608400c6480308140c0c2e020094944498002c0d200b00c000d64091981140c070580481d40b1590310142c03503000d0000341a0b01d40d2200b03d10040603811130b1125501d081c10805003500354400d1006402214001030700042251003812070010300c1c2c4140e24185034841c040b900c1182c00090a80b8002400800c074002985000d00803420131381c05a10100880010300d00c0440c101d524840307508000d1064403404208110711403640401d0b45140f03a041c0a138815210a4024040e210400e4103900003414140441c280e815880c010302406008482d50005040580c440d01902110311403066a440000041108122900b801210507403807151103150105650705001901500b007990101404501080411a40710f070420700301ca1a8018134140b10b11200c04000704101e900f0341c04400c4903050300400b001d201805078000081d14031544220303001c0c030001601048060b603c0d180c900300e084e0f2054070f150206000c0b8100055100d0140984419100081 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 952586735 1250 952585485 952585537
    0x241b25020a14041802060a180e04140f01110a0e18040501091203090b0114130f0b0111010e062703030103030806120102090120010204030b13030306060203130b 70
    0x1194552241d00b00c9142049071040c0782c98a0b115094400210089114000c1031980200364940124401c81080c82914201e9400035500e82500c00000c11603207440385114506032600680200e01140300c0e0100f44982c0303203624900717074060043c2110881c0c1d10040c0c80c2003910540e8101d4118100c01c0c129a00241d0321042c500c54410380800142c461401040081255800c0380360440702100c3c51100b8100305854008003400113041d0b200503d044411380100d1080c019101c00c0003402018405144c2c0e42c4a038a40b4100600ca8003050b0080700400c40262a0700707246000503007482d42607540c3d19031908115001500061418909030b14140040b594216500541d101280702d400e01c0e551003a042903001c40c081703404009035803902861400e036420050000303508029030707000082d0103a040d00d21401010301d28021000c50626095050300c00442c1c220b540d9031880e003003c000341c4c0c003403650001043d80001d00b01600450401c0c000000c892400c44140640d05025203010b4900391a500064207280c43c0038495040b80c0444 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 952587985 1250 952586735 952586749
    0xc0e10030e06040804150203041a0a0e040f0b0909030715020d0b03100f050c2d0d0603031d030304030b07030e15040302010506011e02070504021b241b2502 68
    0x18030b00c10710189503506d003454241c500c10092203d8500466004100078098a1281c5540c2604240540051510350640100603104110303d01021900149800c041d18400080c64004161a51054901c05034640f00d000804d6100c1c803d820b0040d1101845803c00601505294024400d1040781040040d0404012000a0810b05405040003189440c2d101c0c12450311198400c15400c1190003128500d0070040002d00951610481162210b200c1c0038100302484821003030031900c0481d0f518908100e49516440c1c09441440b0b0440f42d0150000d10300c2d14060981400802c039000d403504030a0072101d580d51301038118040c11111349440c00500880600d40c0f0038001440ca070500a5110350008030360352a0403400100b8a80349040b9012002d180188555042c030b40102c1c0520607100e0913500540d0382d40320b409201051030030f0f12104080c50310690080d0504c10200c209004064007100d0707010340303068440d0b031004640140280b01041004400b000208100010100c0341c800c0201e0307010f00305402462070b80020f150 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 952589235 1250 952587985 952587991
    0xf1409090109020a03151503030f0c06060915170105040822050603070f1d1005070201090807030f051606080c210f060a17060103021903050129040c0e10030e06 70
    0x140c803a1410040c0f4074003403240500c140c1300d47d4440680700051715648000349207103211400720f420f021409201d2030038040d25820540280038000f1050100a10310081d6010071445446203c6550000e043d80c00d034151010b010303150246401815080c10100e01a480800c400040c0340810706802046000189075112440030314820303401a01e8185442d554243d010b042101d07101215280a554881e002c1701582e070f0a5590118050b886c03070080d40341c641502c0113076030100c61604814442c2c40b5480c0c0000030800485002c0042910034001e660789200480c0c401140f0389100d00603279011508000000e0110b140140113410b14264000307034081c6030041c3e2041c921084206581403031030543d01b04100441c41c1080740c1d581d00203100c0030314640b126440006013591a1081804024460304456048600ea03040b0701e2202009150800000c00004113003003405540d111000d80100000300091500d12654541846107140581640d21a1005920f605040010390122050b400701810b5890f802c000c009507081058502c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 952590485 1250 952589235 952589243
    0x903120e010905180403051c0e03090a27020f090409260c19111302090a0509061315080f0303010f0e220606090507080a05010f1409090109020a03 64
    0x20408090030005011040c0340d008103000b00c04960145000c2c0312402c00b0b09500c41e0b050302e8015140c043d103c543c1825002140030417640340b03040c040602d0b013522011005102c2c4100071541c031401e00b13541300142d01c4d0342c40d42d01801a215a1106c03140c4806030407507400624070603801c100c001d8500020000014101d5220040649101b00c4c4d442604400392881420005800400d00c0d000781044908101071790749250040c403080b203031003a6054440c104200c80342134080000f40141100902c810b01020780c8000c3d000020002e10134072000c8000640b6041c900d00b213034040c0c180030381104114000101040054105190140c0703c01c403401000041d503810511100540d81500f001440e960b51426101a0920559400103903d01c07601109001e0707a45009014107850724580984120030041c1400c0000007427045a10071007200e03003004c040054240d84480000e12641085a0420032a600d48a0340140750000d4014840404959460401c6515002d80290f921005090011400048a502151518030a544121 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 952591735 1250 952590485 952590497
    0x111906151806050316060c15050c0a03050601051c051308030106031a100915020f010c05070201030f050708060d0c0512060712050403091a12090319021f0b01090312 72
    0x30041c0351030240304000e140c22001070684803101c404250002a880c802c9000744090341c0184410803000d0044011594000c2c0410442413402d43c0d1028826440000c00000082c40c200c00910385601032002d40301c800b200311600d20340e100e1120802500410000e419060945008150b480005401e0401180a440c4e80d60303010805142944039501c07190010403011b44902181003a4840c4650b00c001d6000c1100c100340d00001924554840580c02c0240d0800300713004550070003004001440e0401e00404800e4401c1e6800c01852030014100011200c00b41c030f0b04000190500c0103d801890807003160070010b40280c0c55003e0060f541c13000581140d0306990f041f00075802280c2048481508550341020400021005124528081c0e800400d550042e02a02d981625600f0070390011060303010942c5c0521182d4026000c86081251030540c0e20f4100031603d401c0380c4410289000b180c0d102040708080704c50b0210002c102c402003108040050400b905240c0e041020b212000804200c0e03041c1c850071f1340242e5440720 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 952592985 1250 952591735 952591769
    0x1210501060b180406050612060607051507080c1306030b012001051506041d0403030e0d0c0507060905030615030a020d030507060b18070305070311121611190615 71
    0x101c580742c04149075511840c41c1c07040800030768490008230358480e08858403a040c26a81c40002895034003450f54083c145204141090f01102c4800c18424092001c0d601c0d40100340c0e40f120381c881428400c40c3c124840e04c00105508000c41c41c040d030401650314105051140c0103003c40018100d1200c9420312a251036916a418062542c02c01a03100d0304500c001d840203480c040c24a00c10410451105003400b24000104000605140c070a9106540c036141880c1a00c0d111802440024100142c80209554038042d008000440034090800e40e02100c1d0090b0141100d60354894001d403601039590082e940500038040031070300595460951100e60b0740310391141d90704c511090a0000480b021034407180c0c05581075940d807000c40305c07903003d040e64445024a004141c2d9625031500300c000d00741680c85080300500114807542c40b03000d400c0645100d1103041c452000b922101580894004d14000c0c01d89a031170300583d080740c03102100560052800b6010705000718090712082e40e26070032031000b90300400c0c00d5420208a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 952594235 1250 952592985 952593007
    0x6070303061505040501020304031b0e070e030f0601060c0209090102120f01030614010b0f0d09053f030c0a1107060302120a0605150706060518060a06080c0301210501060b 75
    0x10100220702d6240203400d0a0903c00041c0d07403480380e0702001e0040c00c50500310644164000d6225805003210134090a10382c2000c400141005032002c4401d40710f4000c00890210748800050494100c0e01e555440c1d011f03001c1a07400340308020f28040e028040a5408006603044500003180c0b0f42c0c0101d41421841b4060344c5135041160407203410400801c0340311032000040101c00d08042c20740394034440b800c405980d01d82d81d01400d02c00802c5000381c02080b5001d0046d0454002d40c1c2182101c40900280c105070f1105175001100d50711042d001040c0910410381070000c238503892402c0f4050722514138242811409980c0b14078603145000520f610400000780c000604204a168640306250411440300742403040908001c006100c81a1040741d0140d0340074046062030601080d0380110740200310103021624504681142101140c00449013035010f41c0140c03d000a0591060040c18800e10700200c003d8196400e1001210840c01d51401c240d00c191701030008040440e60a2159100401c17940c2c1440c0c0d42c0b901074140d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 952595485 1250 952594235 952594259
    0x150112030224070815131505090c0f0c030d05150a06020606100e060d05310305070201080402010e030f060405060a02040803090f01230a1205071b050c0607030306 71
    0x150241440503406500d0b40c8900300300e0030076000a240d0030002442c1c0c5c0c0d4005081000006a07008582c040254002c120304800180e01c65802c031510a69640c4034241c540d01031104a41058030a0744000314100712000b21401160040c003141081c080c1547d01d008030400541081e2007080d5201456010580c84415180c9482c8542000810160014144a2810b180001d28034014075540800b4011022126407031513803024120341c0e003c08140400c100600304007841c05c1c0070038200380c90f08199044c42c0140300c4080d2b42c19100d00080e00d515990380362400c0700544c0115002e420150049062010300b0070301e100d566905000e2000d4558442e0010702e418a0305080c502d240c40405402080d807035104100034001c040c404012101c9801040d182e1030583e2100c10012520420f415034019140f100c2ca912004503142d0301c41c01000a44041d955200107180c3d40d83c220320440d103040da202008921b0480d03865011a080a045004050180c070a841c0e2098041000c10883e5104080032000603a07240340c28002100b040d4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 952596735 1250 952595485 952595503
    0x606020c0405090d08040615230a030f140111030406020711150904091a100f060e130b040621020a290d06030807080405010e240a021501120302 63
    0x7030701844141000c2d444030b070315620208200c000300884d002c0041c05000d41a0030142031842c8140300c0a40340303981e82840000040d04c00c0c1ca0904044110b012520355450441d00c8001030301c1d00266409070851107503030b0b60100400d00ba11406171654840c02443c0c094900745016510030f60290300007507543c0800e450581c14860844c500144a042e804101c024134181281c1a243e00c01001d603000900e60205040400820141407285520740748000e04001c02454005642c404441055841c2c0015544410082c0c654111801185400921b81c1d0b41113400d03114241c0055110007006400040c50503162900b4220900d902c02d031000c10080c580180504604204c0c1040700100025802c0c80454183c00b01c10041004400710648509100400c0503845e040180e07100c0c4008580c0722441c01e558203110b10b0194bc0030740042c4103003408201c01b10080c160f01d0038070a1000c0041c0c08501d0701800c403402c5180c83d4000300d803c003c0c9203408501c50301c4000c942c0c501e250003000303010b0981808604101c0d491881e000745030250803 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 952597985 1250 952596735 952596739
    0xc02120a080a030e01140106020a03180e0403141204140d0806090c1308071d18120f07080c0303010906170309011d0d030305090d030c02151b0307030606020c 69
    0x284000c08041210700c000e480110340945400304195400c282c800d80900308540c021040192080000030b5030716000208800340a10980350303c050041048035816847c0c90520614450340c0301d0100003000603100d54961780440c0d88040e401d80c223245080d8a2500041800c82d01141c604a2070780340b4020030300e82004560310803800fa1510728a146000c40100f02c00c06000703040401d1805c00428030301c0c1c0c051601940031000d40703515011204180e0b0381f0a91040304982c41c021241200d10031b0b00100b0009040c0b80310010780f0b548002d000307080111501a858103181d02514a40c0841c88081c084c000000341848014a03071340c400f40300190746950601980c44204c90440c0d101c59a01c0c80040304c210004940401078880c1642d090800304a6a8044101c52000c0800c6020030b603803003010b51101d00f0070140c25900c071a0003400d00e1000c580600c200c04c88240c045031442d40000c0003507071101c646040c011310303881541640860211241e4004414401ca1030042e90416264400401c4d01c510060040d40c2c2c0c1000300d40d07150700f07003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 952599235 1250 952597985 952597993
    0x5060711010b2b06110304110901141020010c110f0604020a0b0c011d0d020c2d030f010c0807020606061608030601030b0a171005041707210c0212 64
    0xf00c4518080007810310360760745900c111582d902006101c0d05900c9403c5103100052000c0c0e4030300d040d19125a06284075040c3c107200705181c00010680b010300342c40050103030704082c0c48000c42d100819030a448009103201a4001041d0080c07052158031030a02418841d0310a94031000007400070030300d00a08020f100c074580c0d003940d840b403010800543d0f01c000e055000c981004400a07940c46e01d0040040c0074081d04201106030b0045e013182001c14400c00180c1250312116a400d03100501540760401c08007415041c0c40002500a2401111901100c0c1302c003007410180003001c41e2028648104102c1c2591440304005000c512403404001100f501030250703680c016021034400c1d02e001c0c40d07003046010945284001605141c8044000341e00c9074046d600402480d003000b0503031004241d51782d81c020034003c200c0c03a0498107401082d10244450110740122401035900c501c01e69140107041001c40c0c415000401d0568000e68a24102c084d0003404052218642c40e1650340c1400c040703030900510860a60100d003458050b88 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 952600485 1250 952599235 952599259
    0x1805031f0e0d0915030b0d0b0a0c091818120903031704021c0302031e180114041e030c06020102030a06080a0209040b07050c16030209060d0b0705031305060711010b 72
    0x83d200c0d90751415604a52040e00d1212100f0504600806410039400c1c0c012100400c1c4809001c45215020700c51034184005005a80004030200d070003c41c5445080001c04030240030080c402402c0e000781c6015032101da40380b01d0b0588661601c2440300310313007410341000c1840c030407041c014954412004000501860b822103e141841d81c04100c504003281d0420001d90340041d000010984240700310740712031040b100150b40100a02c8010039683d40503c610314006080c2c940040244c0d405185190000d1685841080c101440c22305411000748020381c540030070045494001c00042c0070907038420087d0031503034001616890700e40c80c3d0004550041d0001d00482d40034118500c0166a4851450360060b84025243c81a0f00d40c0764007038810703008444030307580180106481d110000c100100428103d900841e03840041c0c1c0c403000180a40c8032101d10010f0944da44c0440016041402040103540150051043d60130144280c5c480c1400c060301a81c1410006400042000b4121424000d20304140c90803110008110 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 952601735 1250 952600485 952600487
    0x5130b030328170a092a0905090c060d1812050405040c210b0103181b060810170a062316050405300601060311090a05011805031f0e0d 59
    0x3050080c0350758041c82d1200640001c00100508544440c901c64075024114546c5036020180c1c40039034064400400d182600003001e28a00182c80482d61002403e0340749000c4000e01c901000c0c0c0800c00500c3c02101020101c080059009000d02003200121341da0389072079a041c00c08010980f40a45030140801c085c007051351402401d02c00c4495601c503a07242000603240d60402c01a03014203240c54035202080c2880c0304032801c0c020b050a00407c0059004468500d1503115042500c10102c15908503252100c4c0720300500220400d40b0800c0d140c044d40c9011030318440f5031303980c030707401030341c08250303859180c0e8410070201d032540c0c8950b640c4140c000c201c8100540102d190628010010b00941c418140b240c003809800d5021000840e0380c0785000207103261410581c07000710f00c510741d45500a10070840040d281c1031540d17101201681c1643d8a240e0001c1c00701030035620b01030045550101007810321250b010304050024865400708201182c00a0507071001000b0b07008442c0c02b50032603000003959115034000340c090b04041 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 952602985 1250 952601735 952601777
    0x130b180915061807090302060f0703020f07080d1803020d060c080a0b061e040503011d060903070c09110c06090705030c01050c06040f1502040f0f15080105130b030328 73
    0x1d1503c80c070103a0059a500603003241e24a043e035101035081580050f110b101c05400c40001c000082c00f80d02103c00b596650300c0003035034800980c89583d0450300804001c020b140d20400f20b030458078210010866809407280c0001306404081e610071038500c0d5441d14002d44650700414030340c0d40405d10080420094400c4404a1f0b06031040c4c883c1c00c61020000b1361405140c0020000b5a00030f40405002003102c3d040700600100c0070b0034200403406661042000280340e14000004464186520002c940742113850000c44ca4007424002c0c2104040000500a6005144080196620481440000b420030918140074581032041e9900d506040040820026140500c005801c540281e403051800f800e41340e25023002880300d03040c2c0c295805035500015000450102010b070f0102594012001c80d80c54aa03514068903a0031401030000c40400e1030200100000c1c5042402c20540080c144408a8105a503800090456010381516004d003c0352900610100d80303a008480500c031840c0c00e051282d1000e540f60440380d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 952604235 1250 952602985 952603009
    0xf0e100b03090f100b090f1b03101d0a0f090c0b030a020708070506010807060903151a0402040b0d06090509060414100e0a05010e060106090302130b18091506 69
    0x180c04000010442c10300c010030580968030115010f44401e9561181c60802030540c0303203201d6104014500104003845501100702340207002c3d0410700d0142054801c0d000055410041041161034404600018014010342002c4000140c04001c8181850135039511000c0b141c0521103003040900d022110740025640194590550f100418a103403240d840102c4c0c1ea0183c80b86040040407441c0c0170500c482004400210103040c3e035100700995000d40d4582804a42d080010302c805400c580c09015046070380192503102c5030204180c41380c2c1e560403c0001010506a07030060340000c1c07a401000503910041440e610460b0041c01402800340450704000403d140e40c2c40002c2c101810003d15042d18200380a000c2041040e00700a0b17207070520030100219945501d4040f100c0095903d5400d00c01550b410f10310105403d41030301c0c19521421415806c0d0380078021484030052220f504655a40d01448082c1d90350317104250280c2e03001940b001545840c0b100320b401c101740349848150300c0d04100c4c2803010313640c0c4090045c12 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 952605485 1250 952604235 952604249
    0x60510050d02040918030806090408091c12090602010506030106031a1e0414160501140f0d140403020d020109050a140a02100815090c0702010807120e070f0e10 70
    0x81c48000224980e4002d100f80e0b03206402492811080780035682d103442a03103200c035001c0c0d03c6920555503140d0074011006012100101451820811504541303490b01640300568011051902444903659031511048115075400001c5903295500b0804a5424001c61340c1c02070056000388851031071981e5641c00f0000c140045450740c590300000411040c02408a16104401e407403d400040c2054104030304009500c801041d01802140341100840701d42c410f8040c211101a5502021700c01c182c03000c00742d190480e111141d2a501c0812200000d5a0540a0134407000c0e030110600c1d40908151502030f281030101d1b00d020040d039060841581c0030400201c4d0408100c2d410182008587e1100031031142051074610b4020350080d00c0d010303691401035110104602c1042a003040e44052103400c01002950403040b10201e0300c5401c10070510005501c05d0000d00e8101d507160a1910409a040b01d196007903803034019916009a2101c2c5080224000e24a0a14001d21400074040003e0412a4446038005a1401610 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 952606735 1250 952605485 952605487
    0x15190c2013090b040303110c0c01050306030c030f012f03010b0703272d0504020c0705090c090301050703020a020a1202251e05090406090317090102071506051005 71
    0x525226400c101e00129140081003240160500c1c01000702c1c00c043c1ca0a030006880d000078840b402060f4030403030320003421103401030a240c84910011162a400102526014040c401000c5800e40302040407188050350f840001c0342e081c803d40c2c13050400c0e0903080c2c81c4180404110100c0c91300c41e091001142c2c1560a41d4501950365404c905042d42e19508094023004010703101c1140300454594030140005660000c40f420fa1448946192900c8449401021000c4041c0a90040005140039401801680994001d4415560361000003032900101220010240c810004440000746002c0c0700c1c1c0c0b80e001000d030404600700081140000d40d5a81000c8005015000c500c1400c0c40003402000035040c45503600001800f28900021503801000403403040d1012005100301a00c0b54801205104054440240110320540d5454942030042d010f1107005400740221008408810001036442c0b40c401c194078000940d40d64a1480c2002c0f11105401e10306200c94a044000d02c002d07500d0060070342d03c10515107007071 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 952607985 1250 952606735 952606793
    0x1209020105040b070b3c0a110705060f07030203040f02090703060b1602031506010f0c0819050306030c040e060720060108010b090108060f0402060a0e15190c 69
    0x140c0c0e0a21481d084104003c0c0302046010810400000441c8650110350340170500c141060280d08039500005180d418120074490160481317007881414540c044032510b00480e0b140f1100140d0390762540402810743e001c3c0c2058080001d105c0d105e018850700103000380740440c910700d07054a45003d04206030380001c0c0b09003010700100e188a8800d070441006400c7d14181941e17660031000c0720800e0f501c0e40e50342c224028014100380701d51240c007003102d1500c55481a114904040c2c4c00300000c0300d90460b000740c12900c01c20184032a8200007900340300050a903034551581603590501034201440c1088081c4c1d0303d8443c0d428050054400c400c00300380346d90000c0a0781040207c2c09602411583e6681d4050b1449000b4424000000340c4070f40150080311310b00c0000d4408148590f25200600e440b40d1046400400d4034550301302060043c1070240c001e000380003e0b46000500c0180840000e0355044082081a200510106840b0601100c2c40100c064035011810102c1c840386155031044800303801000c4900e1841008480b03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 952609235 1250 952607985 952607987
    0x15030c03021908010602160f0e0912071a220201181d0f0f090c0f06070b0711010506030309180615040f030507060e0f0f2202091f12090201 61
    0x10b40d540e800311075040c07016035408a0802004810300340315000052250a01c880c441c43c4509513141c080d0340c0e0003c02c1c0e5116a081001050440c0300c040d00d015014410751b030240003081c1ca0003028141c0d091084007503540c14403440210600d80070000d03040707031000040580144445040d0500340b0001c00c5e420708286000b8201000702da2003001099201c9906143c10107600c0391201007030540180308400715410950310342c0395903104040c1007104480d842041c0d0300140384c9a03082c1c9008602c2030340d10300c0020401440c200440e43d89140c0740e1030607034005e0b000c07803044a02109840c07000e00079503500030800d0f001141401c0004d03001540040c100342206446224030401302d40b060301c4001034054401c0a41c040c29680c0c2d40c0c0c8803038440b600314582c03209803810b008208001c29682d204003040110003800405040c1906400410403114240d0051840c0d8460b041449601500c034219076200e1038405003400060f224001078080c00718070121080c0c0f0b503000c2c0c581400182c0b5000d4108030340400b81e0252f204005278246180c40 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 952610485 1250 952609235 952609237
    0x1a0f060d0c050d0e150f0405010615020c01090e0c0f030c070c03030f0324030b07022b1403070503011707122d05100f0f0c0302090a0f15030c0302 64
    0x34482802420200000507242d0028002c214009210344100116000c05900784c0c0c542e0720710541343c00c024001d400070400408070803000d25002400740d000010b46540d01ca8041482206a16640380941c000c1c941d040072542c0c014018130000c0c0620f6881c05040d25150750540d0f0700e4414552b505800c0310010003c2400110101c00340c81d152580030400d03035401038490038041c203003941e59a0a040003a040103000340c2c003a0130700c4d10b14802411614030382607052401c41d981c480d9405401040c00302103200b41d800100402c44846d0300851041c0c0000200303950318004c42402841e20400700341d89400803800b001400440c661040480c3d044908111808550880d10015641020b2040c0c6c44086e204808040c504103000314001c2c80c40403440340030000000c41a0050001c03140000400020702103402c9402003200a4545070010411079280d5800091940000300d0343c3e00484070b00c03240d06400644e0100d850819030504000602c00780034282c102e84140751911404881031509910070004140c2c550711042c0c40d46000790 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 952611735 1250 952610485 952610497
    0x20f2b1706130908040602011e0e070e131704052103040605160c091505040b030a0627050303160503090304090c14031510030b0603040f0201051611010f031a0f06 71
    0x8184c0d5403150b075843c00034060800026200a01c0c00c035442e68510010382c1e4801d80a680601c03030007800845103001c40012145000400f00b2200030f86041105001030801040006011881c54010381c4403403d20b004d022012000301d0302c4811201c0510301450a625000040e078080310424640140d03150207040382e000f950000c091008210038a81c94000c1142d441e1074000c0421101c500c3c48d0388220a6a403404c000036140c05d241d8042c1c150304030108500100d0f8054001c8103019071980b0000064201407081c03005405511300b001c2e9500d4002100703204c4a50f034a60441c0081c01802c4c80c09504500302001000d80b284550f03c201c128007a03656482e91966030281a40c00d01c03520200442507100c0c6041010a182100c408000e40e01c1031004e440b0014442c0c3c080d100310105000d000c0c080e40d0131a070b201d568005800e0b0000000341c0c18090107004400d428100d00014800e5176100c0c4109044800c2124009040f444000700000700749800d200503048141348410810ba0321480c11100318002c4840e40b004104c00780320301 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 952612985 1250 952611735 952611743
    0x3030c03041715070c0212160303120b0a030308070309031202040305010c0305102d05090403110f1f0b040615090807090614060a020f2b17061309 64
    0x1103000a011590311a048030703400508070584569004843c40410b01c0715044850002244110702e00c3c201504000c0000110001c066084990115800d140340e00500029801200005c00b1302800b0400c03001c003800780b2107595000391280148107045503000303001d10400a002d0010581e55903050800d061180e0500312000414000c11550307580c4a0500a000c1c110040c0d00b000400e04140201d800d2001301e0303034410101c90a0200040640c10342007209140b107070010502c0404803050000c0130a90399203c041681c0a58401d489210740e000e201002c043c1010486a21b144103500b00c254503007624000001d5282820005d00c90000d251040880080d0041c5500d42140f6031000e10140c0c1c90210b541c011907924191139050046a0281e5610802c1109665140c081d0a008030390302c58014247d82800c0c030103404c588040380181c5007400a02c0c08810f20701106290300707010b80076803611a101810101010084114082c0c5441c001a4588511b05440c150002c0c00c80fa01031502d40c4d01101c030240c1e10741e000072469584 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 952614235 1250 952612985 952612987
    0x2030f0613060f12030f020f1e010e0d0504030507140102030a0e01030e10020a0311070503040603020a17100905091504111206010e0f0115021005040809131e02070c050d0203030c03 79
    0x300c800840340d1440142c403c8020400744881000301c00d000054546010030a00e0080109c24500f41074484980c808100d120890341d01c48240000300380040c001e111501c542c60343e52a13280c500d07504040f4903028640e480070f480166101d0300c44a951364040100ca000010f1420001380b0003442d000100c00410003200040070700e0181c012002d02019003034000700000d898948c7e05000215100c0020700c1c9611505500405c15801080104481c1d8003a8015200d80f0a403030800004012281c88810300c10700023107840764200c0a8508040c005135016104094105003508020100314210078a8540d200d440504090301000c40051000181c0e070307030b04445d16100001c06046d551607596550810400e1007042c0e03000000340403204008621094502c5480104031f01560061111442860039203001700800351003a294a00e041007841002e44402c0c00c20584600707846800280175810a030400f0142c402d8a503a0121680100201c0001c240c3c0c0b860154181d8404a444036045003c030b1000900d584504005542e031400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 952615485 1250 952614235 952614239
    0x120d02031f080a08092b0203070602070e040b180f01090b1b0919090c0216060f0c030f140c0d090623030a0f050f10060c0c0e07090e15120102030f0613060f 68
    0x1b00000751043c14800d60444200c41c0c0c40304000da864020038005e10401c2d0041c50009004142c60f840190303000421062034407015030901c0b042e82d0410b1001003151310681c0d1900604d40030480f0781c03c103c60b8007040d40414080140400e0440045902c15081ca4a10890800407a101782c0e11700300d10488010071404400304801640900301940720109008001c107255103c410000341e107030250320221818000350340c40d080c641c1165035050ba0030f22403003204102048400c2d1a40c061046000b001003c8441e12640200860f0070200401004007140360011001c100b150343c001d5194078511040d516401d82c0e001036407600c03540d0740c0a080d002000d00a02c041c0c040d034181424000014079200010b0f00456080002c00f035416142c4805540781d60340e481000340303100c4502c241003094a62071024142c1114507442c1c0121850b0760340d00c1a00f80410207451303000801c0d04445200103580340042d28070001040d100002d50551400c5005881005001820b540c0120005d40c000381080d140caa0040006d400700150070580e8603 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 952616735 1250 952615485 952615549
    0x15030b100903140a12050309071802030411190605180d1209090c08060907120905011a041808030402010c060501030309090e060402150c120d02031f080a0809 69
    0x6006440103030741080c9003ca480008800200780c0220003034004001402044031004100d480f640300901c4c0c040540a10350300840d200503001c02231454483c000f00d0250302ca041605202c807a00d608403011910a01d0307a80d224200c039600c0f4400c180c040b240c1b6800c001351203040c900059540319001d508645c0d030295410301072000b08491079804440440c1c155988070314085e1a8441c0c182101d25105201c004141808002107a929100d8103a560241180c03030030300c140c6c007602c210450a445400d00700b1500d13039445e04200b10000031500c01d50022072108550500140c1100e5003890100070500c1c5001d084508000300081c00e5900074120544940c3d8898000c120641e500d0800414804c5c00d4091814440d0400580d6410028000380c0140525001020180700104005070240b5560001c10801580d028100f01d14038089400c0c4054002c400c0903841c05aa60301d040030501c03000220215000c00c807114002000c1c0202c2d900043c0b03010083e680300003415907940c801000501c1004074800840c2e0135030281030a02030300d2 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 952617985 1250 952616735 952616747
    0x15030a052509150801060f060804060c20150907051f2f010f05010510120f0213030203150c031b040b0a030c080a050121020d02120a0c06081015030b10 66
    0x11450700001b001400c0c0c80e03070721380c00400000d13106100000308000081000b0a40b02c2d44680b80940c02801c00051a0010b400110312040c040710790300200760407004541540c0c5050300102030b4847e89160182010a090200042400c0d881006614180d805040e15214081c045c88100085421426a20180908044103d4980c000c01074204070f4550078200f81d0301045506004150507039200600030090480e036000111174544141c80031a02c00c0d0345445410f1581d582e90b1000703100252090030038403441800c1d0f0041c2761409210030f00d440c070051a002d0403c1b40094442e810350790440c2c1c1048480691882514203076071180a180c10680d40101d0005000403032541561048440369600e0b00d840440c0c0d50b80c0c0c540b1000f102d60903c112001c1c66010200114a0103007ea0103060303061005003814480c0c6074940105a4640b2062001d5156602040460040c030072001d64900c000c0ca21442d1111562a06003d02c80c0324a440b40308911492000017104030115000345c106108111014080a94400c01e0100003000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 952619235 1250 952617985 952617989
    0x30d030b0f0918070803040302010e010f02010f0e030901080f040c051e1305161706040c0c0807060209091302011e020a050d0503060a060e0901050d1b030302010515030a05250915 78
    0xf61080c20400903031004040240c6048a030140c460182c4000c0c000015128010145915030842d541e64402807190b8809100d05103881c0000d8004503100c080c810000b40060b0b4000c3c0403020740c6070800701080300286005a4200a51f041901c45845207030b519061100030506001c1f04a51007211244107100d140b0559201c1845040d0201445204610407401943c495641c4582d0440d09603030340000442c00c0c10242c02c03a0301c0914041c074000a94078999292440039421400080391016000620401d483c0b420900d51600420005c48060300c0c00c5660b030029044101c00d0144100d64150703142c0c06181d250080c0228032505401500340d801078241e03450002c060f644103d810910681c050240401c01034032030114503100c15000307000315905900b0442004101c1114140450720310b03051541c085241c0f40301c0ba5110f0020b5201e5000414141880c000d5804942c2030441628007a07030111a2180100300c00191086c0c00307009560068001d04910310000b07212082540008190500741507000d106030f1034010304181 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 952620485 1250 952619235 952619281
    0x30f07080c07120e0d0203120c0c0604080a0b060411030f01030b1003171e040b0304030314040b0a0b0418110a060203030702120901090f060e040b0a05030d030b0f09 72
    0x186580c1d204100106015a610141c01000c0070101003102c0c600642000980c03070401803c903078040103581e000038500725203a00d040c0208100400c9107048000308121602c96210300b22884da0606043c8000b9941d40c3e183c00d00003621130f00e030300000f091503031302c65602400b20000807084044ea40d00d42024400c110140178442120010300c3d40c0d000079205500c1c800504290380c5d010002615a4a40040981080d007001003900c04a10100744084043c07540d103030041008108070111540ca9180c18100501161440c8011507590006c01c410000050042c00031141d121100c0740c000900700c92010007141c0186081080c004d4480452801902030203291b035078650389141d0031a8030070103480d1140701c1241c49020170350f031010260340084502c1c41030200540140c10141c2c01032500c45900d40d66000d202030100c000e90300060101e80c5982d0440100d0600b0f0041c3c3e081d410080d102c0360340b018500004280d0351a420314a6004141d615000c10f41d2660b95500710f8980800000d100704402c0c1412401c4446050030204111 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 952621735 1250 952620485 952620497
    0x1d061c0209150c1e161805091504021c052d1b010c061401090f0e06070f0c0807052e0b03030f1b16060314062112030f07 53
    0x5000e00e0342104840030310380124083c00308100d801300700d001c1ca103001c125691294000c4800b803566000d20715010304001d1000c803100300e0240810400c258111000980012030641005c07030005400d8808101e0907403ca0341c10380f603050322070307181000d12900e803140c00307800030010702500c0d852426042c0030040c42090549041c504002078501d19641503903c0340c0101e07840c2e030400524680b02a0343e6008101c0054880d014807408a50886110cc5406642c1c01c00d801401c0f025035610050380e441c5189100f000350194040d00201401d041c20003000e001240380400000800201c20381c0181086071407000da50445502c00100c9400044032019040c181165108140e0f208090700940386090125003c0c005420401a01031b40c5031240d240f2905a4a0f8008900c204c0f94040f806080e02148004005911806d22a80060500c03941081c000501f5200c404408270b81c1d20540384188181d43e0381d070500f07600401c01c1c04034655150321210115503040c200030190741c0c5c12248021007088444520000082e2081342d9580d504 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 952622985 1250 952621735 952621759
    0xe030f030c1e06012916170711060307030603080403060207020f031c0c0f020315040210170117010e030318120a0522050a0b0d0b0604061d061c0209 65
    0x402c2a1031050090604103a21040041043e110a20007480c0303201021007545481d242c1c000b1441c0e0095200781c07060402207049030884414045001036412081d803101d420145014440d4031450440d02844031118403c50000010411172b41c01b03980700a0007982d12010b03042e02c440d0f49040960080d0080c3c40141c0c0035241d0511007901a00d808584221800900e419584014582c0d400449600c0d807010740484102c012403200c03c01607901001051800003080d0301c000c00e54a05071043c043e010700054800c0741881810030ba11781288041c44103990555511241441d2042c7c420460310b0f014104011003203140e0701002007031042c0b10150940c00c034450038200084850899844065011501c01c8000704c100040c0180040c2e94482d0031040c2c011a50141800c40c01e02450700c0748002200e003079aaa00034420785000007000c10403031004c0d01401258540403200345080078900701000d44280a40c03190803c0703454400c0d0003181a59103400603500d00701c074000480c0e10309601c0324560328000d501419046128508540c00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 952624235 1250 952622985 952623013
    0x30513050a0e0f060d140606040b1207030807050a0c0b04030317060109030803040203161409010e01030c05010f17040c030b09060402130b030a061b1106090d0f0e030f030c 75
    0x1010701110708003803204615940da0442d071034907a1006450030754010201c0c40c00c403005c110000080d01070000e480c0041e00b41800d0400801c411103040d50703002030189104005412405001180f0030007120741001e01c0b00c0d85e400d4685045070400040c0078000f00780703017a03022011884100900182c416030303102c1e484250b484850385035000f40c0c1009c01c650039400144030201c02d000082000c00919042403000d0101c80203407441c0000d072070a86141c0e4110142c02d00c8903181e9a605c034602030500034010f050b6100342503031a5046403241840000d40d8010b080c18010600203041c7c5142c46a070541000060240c403294203800e1034074080505038002c0c0f00c2582c01c034001c903011030400240030034030a000e6940100054149042e10071000090842034204640c14002d407118a03020440741c0c00303211307500c09007080720481840f07121034041c254222980d00c641d0325511400400c5102c040025a200703030a0258104000300402520f42100c91008a41079a0b03010f00500140d4252400000090301c0c201600400340c45074404a0f0348 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 952625485 1250 952624235 952624249
    0x130b1206010b030115050c0d030510051f030507090f03080301030c061d10180f0515040614090a03151d0a050c040b0d170403051218040b010210060303051305 69
    0xb40c1c9001d000100f00401950200b24032000e50b0302c00c1c84c1011414444014075072070805a060814202103034882c400c0042e0000001c003034102411085454201c103400c00d810441030100421898001d0640e11004181c081d401030410800030985400c42c94000c907200e1500d100950070a10045407a449401e00115100d4014010129880c24504c0e40070185510b003410002d126404211a0040c80356804040302c0c8c2014110600c800341c100603542000142c5004207011a03c4040001003c0110727041c001030203d10b602c00301c4014290200d030321141e150058800010103143c1c859000500e039007020750680c11121402e4000780c040003030f00c0021642c06614082c0d000c4e2144500c1400820326044103803203445e03924095114407840c5a000e490101900e28941e521000314100030035034090b0b00300209040027084405c001c0700c0b25084003c014103060507400e0760104101c00c2203030f65642c4200d40341c4085003803692081080000c2183c01d15014030809680e8200a00194401940c80c0c801c00b810080118490600300 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 952626735 1250 952625485 952625489
    0x15070c090b130507081f08012a020a02031f150905070306060f09180225050c0a030c05060c0c2710030803010303120e0a060507081b03060d11130b120601 67
    0x117291000710750f83d0916041002906520b5040d0042d103502008682020240704804032046840d00e4000182d14004810356401080350301d81003103501c500f5041c0010388000c98428280c000300c18150001e0742203001c10201800500c102042c04071511000018410540d0708201d00402a9441c10001c0755207505007201e0340701a206070700010420011040041c4242000219848001d41d60010300f024030307501c4684100901c0c2c82c828000d04440310038070418003005010400c80000d0445040109a142d075441601082c02c1d40300c1c0c03d02c1b0310b401140000c01c40105000982915400810100f1440c10104070304c042581c4103001c441c200d55075007000aa203012048800003c2d0f1381c10602e100d055a1856030102ca03904011503500d81c090340c40c3c04480c0104982001401020762040f080401c4615001d0b00040a8940c0107002c1440c5135040b82d5640780d40348844088941003034040c0c90b05120a082d80c03c289030300c0710b84c4040168005000303440ca040a86899408140389860480b55a00c084440c0c04030300c1e648103828 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 952627985 1250 952626735 952626737
    0x60a0506030601140d1b0801080f0604060908071a0115050c0604020409030207080703240209010c062f0c010506032b0e030a03080708061e15070c090b130507 69
    0x1c00c086941c0f0341c02020404600d00b95840c50502d0401040f08140648039078001c2c041d07036215810880c0500d5600202030a000d071120700014901c0700b20340c844a50380c541c4040c0019044942d42c480c001c050296003000c5590306da800008404840010803403807003220340e00b4465105000d250182180601e445881142c80c000c19200040880391659000c100c0105200c110460561052920004001d00140500310007503004091841030160102d80c0030044460b80c026401d0074910401c021003081c0c1c1c00c518605500d0f60069400210079500c1d820429414a01816040d40c1c140c1d09040404503035901002480a401110300a01460f150709003407540e22503d4940d111101d40c000481004185680d28240c3d800140620709a0142c3d036651001c0f07418403a901e1002d0340000c42500400041981040316580c200c88140d80c480440c01d00c000c40c000c50718044807102840b45000103401580303a404103013a20b40301504206041807036075854a14400424644407000c1c0a0b0400d0020030003694800d2103101d03c12189 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 952629235 1250 952627985 952627987
    0x1060207151d030703210e0108040506040f140a0c15020111190302070f0b0a05060603011a030c0405190e010617040201050d15080a261215030102071505060a0506 71
    0x20003801c040042c040395034002e8161040c0280000818003e1010300c41408001d142d69010114610000701802c0484440c40d06000010381070200184001400a41c4203421080c01c14401400b440c082c03107000c80d05422000d6a22440203031000b070068483e4108121145658100070140b054a030590076503c80f400340034002d5900388400042c0c80101a01e142d0b8401140c030b00146060b1865860310b8100c4881700c415144958507004001c61481c140c0716694001c03004a540d1070966140800c41848500300816404101c070000c004122607181c0c0c44e05550140134002c03e076994005010500c108490403902c5542042c3d00d0840c000a00d542c041c2c440e000800c0f00041c56004c883ea11500107658a5000010010100d03951b140c12000301c0c0f903507049a40140240d0f5000d085a2034407402c15828000310980040001c400f5980fa40805880301d000301c40c4034079858980c090640d910703000059120300700b280c1610380550001a03007008000d050101c0268410b00302d40d0801ca40d4803408140008414940145900840 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 952630485 1250 952629235 952629257
    0x11502012405280b0702040c091a07110a0b1e070c03020103020f070f1101020f0f15060105071703010510030b09040605310204270b0a0e0607080106020715 68
    0x3040d554000f0315207560743d2040c0c0011500c408103034400e0429800013203141c001003686421031502d4002d481281140b46000030155003440049105100c01d02ca140307441400c001403901c1040408940e40c504a9001031000041e5a9220741448042d813010180007a01e840c0052035031100c041070300a5a29035a045111442502c0c1554019402540034607000500c0000501c0080d000a5020354152031140c4503d0b5102107542da200006882c0c1412600d40d00c0d40c5800a0601408002d07001078080346950040703101c0c1c21282c440100690f0a8491000c000d400d804041d5080501c04e881c0d840214102c50044e1440d074550301d0180d00441c1200c102e0194a42d03c960130401003004920305401803604172036002d00508000104911116099810750100030000d01c08022120035490548160301800070b01d10049044104005114460040c400710000c10080a40d0f011661100346540200706480a10f8121451030601500c054030003082481888014803940d02c0104031502c00c0700d102d0304041c001d0b0700ca03024181 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 952631735 1250 952630485 952630489
    0x30a0e1f0504080c01090303060503010f2706020702130207110108010518060a1206050103060f050405070b0a0530060102160e040206220e011509030204091a011502012405 75
    0x201c0003400684110000384445442c00c94284034218000c7c1c0310342c900141e910314001c145800e68003002c005009561800040542c0c004154442201c3c41812054103034030180c0a10701a0001e01030420042d40119001c1c81d1480c0c036440b554010640c0743c0c0102e440074003110003c401114000030900500740c01c105041c80401d0644890606281c208a005181042c55503d171046c800c41080848410b0710b00396110790040084c003046110725584029034050030b015610b0321381c8645554003d9803085c00c403080740000d07500301c801d8800e5040c0e4903900c0c6c41c01c00741340303c2c54104c52805101e4840b0fa41c140c141442021301088003580000342402c1c201d10010210303c03c50b40340c03130b0522315442e500074001da0b00403404014002050150441142d24540c0704520250712a0070050b0480158005801195507001d83c0c04154410942141c22003040329411180450352982c03c6c42c0c41b5050b40801c04180b040030425000101d554400302c0481c2c0d0400c3c0c410350080004401e54580b61780641e036100e8801e2201001118144624 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 952632985 1250 952631735 952631741
    0x60108251e240e06071a10090f110f0307021203011d060d11100e0301020409020c0f030705060a050411040501080705010f0305010510081e0a0510121203180c0b030a0e1f 74
    0x190040010104002c845144002109412544041c00c110307d20f2060044091a02c81c084a040556030104031680501041e07040c9486030b82c3c01c04468030400310004030141d208004840707500440039600da841c4d503500d0300d401544a825012a40700408180002541402d100c0364042c0301a400011080448004c00240b1aa84816211030700401111090000b26901c0900042c40208071040c2c2c0140d548407503607002c600b001405108a02c1d941c004101090126800140706500486c3d040800039940c0c40c0e5141c0080b0043c40f8458840e08a800c003030001429801c0411160100c031401c1c0c0303c90f108150740400c1141203070024012254004106a1100301c001d02c144005a48400c10ba480c902542000e03241850941c80b04541850b903003a00c0310200a51f14407154101c200038071070b0000c40d82401c802c0765509040829803007141d40402d40e460750011450a01c84081c0424107400000002d11103455020b082c80c184e20403034042c154070341401404041600009242c0b0403841940902d200011000c500034005 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 952634235 1250 952632985 952632997
    0x9100e0c01260604020d0905030c0c1206040f0b10030f060e0d110a0b0c070b2e060206060d06021308060a20040312050706050106020d0809060108251e240e06 69
    0x81d180d8030a02100002c50409c010a0301d40c0442000b040c200c00d070302080010f20090310b040c4150640101091100143c0030190708012070764059080d05c040c0d643c901401d4106800e81e8006052001000b00000034001c85500106c8030700311500580d08519044802039903103426206000138190320505d19000810010351060f42c1140040040a140442613141c450714000140c0700600b0b40c410420100c1010200b040407141d0414201c4500074041307240c1900a504c07000e0052440e070103100c00c5003441080090300d0341150301403440100303564440e0351104445a81c1d41d038100c2d2084007051500c00b10960803150000e844481c0310758200350a141c9801c0d542c88244040750002c4c0f45c01888018080d0000082c42405028080c16a546c01012120b800c07440061043d04040e0180081d5044040148050354021a8040a032065800c90740c1180751040000038425115610818510b40c800c840c021034541c8031103801044601603441602101200b4409252083c0c2d140003410216407480c1c00702041d4205040600301c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 952635485 1250 952634235 952634257
    0x503010204061d03011113090606170403030b0a080d0504051306030206192a02040f0e06010b13150305060a0b13060c0501140f180705030c040509100e0c0126060402 72
    0xc800225030b0403003c642d000b00c07c1d82040c450a00200b4804c24482e80b0500c00181100d10703007034181c00002c40ad030407440c1e10040d0010b401c040d2504140103450b00c480c034291004010303c0084a0300c2078100b500c01490342e0028051140f1401c404108010f0f445054000d4400340d0750010051031600ca10640c00d428500c0115a4140500c0440c003900e1120b485041d407440039111019100c200d90b03640720b10400c021a03030100608001a454060681001c02001030200e05441107502c204d0b40ea44581503800034580c0030b42c2e100c20111004240d5426002d80c0c15040b46010b002d0507546025460f440d0a40300e5400e00618400340309c11010100c081009502c00d610300036106015100004202e41d031080d410b14408070480d5000c2d8040d200d0024004d244102500340c28191000b5000303485220306120000f51505000c08407984a00d4403000881e0704c100381400380c41040400701c00c0411400c0610b10309140c941111841550220f4a0f88139411005509551501d0420b80c03da00110f040740c1d2100108402900100c507411 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 952636735 1250 952635485 952635491
    0x203101d0a0501060905220204110903030c0f0601080a0803060105090d210e1206040f11091f1505031609080706091a120f0a32010503010204061d0301 66
    0xc41095414401000d001d4003030380001c00d0803424000010241c54001c3d0803030404100300e600309403180d0004401c0d80f030701540c100c4001c2804841c903c0703440c03041e009900d50154940000589001100e10015200031a40c4104044d11079030781e42d803041551501482d500140080804000042e02507200703800401c2200001451860000599103a0f0194604400070301c00003034031204a10495103030090180e050320001112400c1c695080c0d000d41a8517100d0260005004550202d269820040c13070012183c01403070050700f2035100b0310b01480d40d80092401c42c2c0d0141a800b0040710040303035880b50100400e0500f000ca4071500d181d41c54600704000545c2020703a40c00704110442d100030801c000306214440041030f0715070380c014180307007044a00444800320010350b4a40603000c11102181c0c2c021200b07280d07402403840002900e107644a040e403002415154010442011005a951100d40c0c41d88441011100c405203107012140e0700c8600f818200e2044d402860045024200062103940104404590088020b4008 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 952637985 1250 952636735 952636781
    0x5151b0a03021b0318010c0611070b07030e03040e0609040303271106071e051501090c1704020112020d060e04060c0f03020a0c0803070201021e090a05090103020310 72
    0x1416190840364451002036000140102c2c1200145030041e003010040b0082c620f0501000604c032100340c401c20105050121940790717401813045aa1003402454140da01441c2e9802e841e2038042040c3c2070869007000424640000841210000000d0710281c075000b0000f1545a140c003000c02003a4007001b40110105034668070b202800c5481d4640050500142c500710850208403883c06201c041000000b60303004131070030f000240204080681240c03c80c0d80c0714500d003031208030f80e0400340d00f40300c80c03001c00d60000d086920002502031480c0d44600000d00150f40c5c1c0003007003c070f04050040000e0f4150b602a0010701443ca44094000c000d90040c5050039911100240040d6070340900da21400d800c650907142507665802c103413005600030907a07010440151030304624003440c516000d007034070200d020040c214100c00700000350341c00c1c003d6044805030000041c40481c0e03000d810401340225030080612070b029246220000419040c82c0c61a24103882c0d0041c05808040e6107001141c0003010800d1041080d1401d00c020 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 952639235 1250 952637985 952638031
    0xb0708091e01061a070c060c050f030c06010905060402030402031c0302070f05060109270f150213091b020613050109020901120507060c1101080604020405061b070605070515 76
    0x112030480000703800120b0100d203041e0304440186095410714969110800020000850f0780ca01d190980d4081c0c1441c1126640310706084c7d10340300902e91055494400003441c2c1108420000d4014105c4031030580c1030003140d82e8441440140e01050b20000e4041e072080e1801c207010140340c11a100070400c40d14005041a0301500c0d03048203001104001e40e01da800c144010b01062001c0d00400800101c040c04043c004c0070b0015030420f5080b008140901800c1450303a046041103090a4914800742007007009544402d20401070610311503440c400c00711002d00d8808240230100c5600c400c0d907540d031500d4014100036513620461340700c1101c40079030842d91550389100e404010380c0e80781040ea01a055400b000c1d15080c00e01d2a10783c3c50b10110341c00840a02c0580552180010320b0b462100904140c00e01c0d012801d6111070b0003280281c020ba4010b01e5018102003030103085860700c140c2034648400e00c001228411a5240c01c161441d1140c2440034000d500620346074901c0407950f000d9640c1010181d81501d242c0920821 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 952640485 1250 952639235 952639273
    0x3140c0a0b250c030e0d0b012c10050405040f020916030c080c040b1c0608100f1103280c08093a0203090307061e09030b070809 56
    0x4800c880c000024001c1c080c1c10560292038440310366951110355900441084058118800d24100804001a034442e00c005e0f900e43c4000702020f143d019100c0842961608034200c0c0b02d0007180344460316154035454551010f608011f25600070500305950341c1d0b84a08003024007015040042040d81d41b00549614640140c0394460350038800e150318040108036803d8610010155103901c40c40e0b60403c0100b5040c000f0003800780b4100d400300e607600f0316a0342e6280081e115503882d0728807030006801842d15113403000808000200c1c50407942e04903244100580340c42181c3d0401241c0600405801c078400078400120b40e60100c54800c001c02c94860300340c000c17010b8134518900540300f40c0c115200000b041c8000f40403414100f0000f0503a00600d4445641032001140f1002c1950b400015203e01c0c8801c1001054542a00910846802d804003a0a13114119110800a840c214844c075400f070f01c082000c0510400d4074881c03080305041c5c030f1b441a107228158846400441c1d40b0031024085007402d000d001c426550351140c0c01 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 952641735 1250 952640485 952640503
    0x1090f020c03121e01050a090c1803030503010510020f0a0206070206070503130518040b0c03100b04030b040308070504121209051e09090102182b0c09050a1803140c 72
    0xe20311118510f804510380003c0032403d41d6018138180300380d0042c06240d85202080c0c0030380e9460600094110754100d070403200d6070351620117100203241a240100a041d4842d0046042e560240d078844000c9150860803030f5039040090000c402d070340100c86030340300503d0008024080c0b45c1c002801d2030706040003030b02c1c2e0750704560001001603011320f051a010441800c0003600381e212003001e4030b602e600c2d51400d9215107840c8800104080740c00c0303000000080940c000d501c0b01c8400340104126843d2259100d140607030f135000e01a9000e40100c0c034048000380c4164411407c03201a9596051420203441d403a95607040c1ca41203010030f030700600c48510300100701a168138121000ba5418a0000859480d1040901a4601d8050038854a036401081120254003140d02c01d204400425035002c2000d820203d640040380075000d001888220214400d00d040c84681d11340413080da000c90390200210344802405504032400700c0c040351075a003480c14520780840d005800012400c0700b0380060600d0302c214a040213042c45100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 952642985 1250 952641735 952641757
    0x905240f0a170702030d05061c062c1009150509031209070f1a1e0a030b0306040c270216150b092e2408070801090f020c03 54
    0x420944a019408110482101c2d82584031045500302210000d44903c1511101140b4070b449070040b60070364840080344c417540031041d64101c2d203240032840c0040c00b40400341c05100100e4908041030002e04120704451484002e0140100000d512454052000c1d2040c84c02c02c3c3c41c184140c00f600015140c0b0b50140901c50208400a59030b2484041e590365034601c0d014100150590206106002e00250624045c0660f01400e2505168100d0114100014403d4894102088150501401808209001a011100c80350b01c06020386c0c4079070001d040c1e03034038030864001c0c04003401a5410041001e403404100148010b1002c6244980b1000c0950402d90b071209000e42c3d44c00e140030f242141448103004660748100d001c084188806520440002c42d852000340011120004503041c55200d40310b6140c0100e00e4240c03c001e190009a9035070064141d020104001078800d4184440a40c61644164209403017800e094481001990a21040c2002090f8411040042c69401c00c0015100360040029025405003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 952644235 1250 952642985 952642987
    0xe0408030106111f0b03070b13030b010e07020a02010804020d0b04050303010f050111070e070903150213081603030818070e0a0e070303091e051309140d0905240f 71
    0x1402100604041d160001d201c0f094202c1400c403c030002c500491140c800d003c00b140400c2c00c00c4090000b81c107104407584800f240d0782d0002140c20302170b040c004011084134000c1300d2201240e80c1e500d5990145035000c035081401070f0465003140c0010340c000c0c00c1040c0c0250018003a107680c4079042c1d5802207004801e83c1e094030140d00c0400100001c040e0319003148003410081c6080d11503149511503569070340e0b21900400c054102a42c000a80480c031464007580103503000030114a070003441c0e481c01d0000798008001d100341524080c00103e102c401c0000c1035941c1c03008031004000700e00c0c5140c8084070440c0300a46503020042b00640002104001006248080d2016504505a5081c146900e100701c40c007820034040c644c1c0085100304080390300419580d04503400d00c850745044049200d02c0f040408002e0300b10592060190030207205103002c2e940071100492007000100502030400910365075620721a6a5000004e44030282400a070515042c9070204e005040e0b280e101f0a80c00240c2107205800026507110a000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 952645485 1250 952644235 952644239
    0xb042108060915030a080d1b051207090302010507060504060204050d0b06190602070e0901090f080d0b041a1302070c03140c0d0b010605031008061e1e010513060e04080301 75
    0x10300a0303510303904801001110b0310100f0034140403944815403020080c005145c04a03002d00c1803505600100440c03c41403400000106003000d020b0055080244007820745801c4800044085000368200e0099a8051311058281000d5a44040184c04018400c0352099020b000019031922100e002a038514822408854240b03450018001410084410940d2a90034200c00700140c40d00030441d00103a4007103100160550b600d1300406d601408030311000505401c3d07980c019200380081040a007041d0141c44070b0038000c2c1503e94081106841d000050400d2081d0390168000030b40c076040035266000034041c0340250401c80240c4504074101c07241d500030347d12806d5515500030048414449119a80402c40d0076560b80070103030316000750903801409814184280080800e2620521661500042040c141103030440d1810555007811103208412245008400a0120301040810325450083c0c50340591032020b56031900c0c0400801030980040401c0d001d5940002082800b14150b65034480c40c0036400300ca5880d4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 952646735 1250 952645485 952645489
    0x313230a17100c081305070509010e16020109120e010c20090a050c0d0c050c010c050406120902031504080c0d020a11031911040f06121214070b04210806 67
    0x1e111000b1a001c1494040540ca8458100481a4100e817061800c1c94000e04280760142c0317058010303006254440c21400000502c3c403094a203282c410b410b007100103400621081010790aa030340300b00005010024202406428603c2000c030308058460524086050b484551901d258103280302c0e403465001c0074041592215402c2621b41c0301d4101180182c10402da02e003060b40c03040740340a05440941d0b000e464001c2d4030700161250040e1070b0141c1044000300a01c00c040b48024149622034400d480c0800c1040f0310103110314005120707401e02180c0141c0648040384001109907400c62008000715070300441400b0803242070800f000250004d04054000b091052580d0405200c1306c0c1100342c02a210384d00c40041c1d8042104030f0040e88013610b6224580182e207001000004019040c00d1001b10740b414582840095080041c44100071051302400c2d40034440c610300c0070102c49200f800c010701000c46c2010088940040c81018000d5401070280852240440c2c0c517803003414400ea030101d21b4a0020b80c068007400713814 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 952647985 1250 952646735 952646743
    0xa0606020115031509020402040b0a020c03071707030b090316030201150f03241e1a06030403020607081504050115080a0c1b1b0b03090105090313230a17 67
    0xd9403000404107405461607680c00a0004e03103007518406a074640241c20119250794060764041d0041106075070b1a000b083c04001c0d9503041d1a0b82840c400d00c91114006a200c124502c4240d5103482200544401c5042d0340302c440383c940024100c0c4e031003031204100801105604110260702c0c944650b0020a400070465495500959076410402210052200070000565000014034142d46422198241042c0c0b9402c0e000c0102080e5032845480348182030312020000596012503000e02001a00e0049165204c0c28890303c1c0c001114001d0243c0d00941c007042e840b40c015000b195000e24030b48040110710864030f0200d000d4a40c2a4842034140809116003c030898100480356400040a102045141c85822006042442841c90000300b15440f15104040c07150609404005411103010350000c1a916003c004040d4003c4841c0400703035280c100030401004002c022508100798136605100780c42c0c20f141003050f00702030907254481d0442c070644101c1300303940314100b204009046071101a8032101c41c80240d1410 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 952649235 1250 952647985 952648001
    0x3100b0a050c0d021c1803020618030f0607020a0b0414070f0503061b0f0d060e040309031b060e061614011505060304081b0a080d1d010c020d0f0210050a06060201 71
    0x795000004041019000030018070390017040c43c40c0004074000c411000c901c45080c0c5410103074000da00011560807500c064641203040075019011034600d145d04040c00d03500c82c0702c240e9400e801600441c0305140401d40408405030000e0245180e05007020401741c80c40d240c11800e80c00300c100046410b400f04494a801d00147c0d0340a00000503690300c1e900020407100c654464034403110000940883c5d0401110700c1c1d9882000544080c0d000314085041505001d410510390f8882201c22043c0300704040001980350380c55a049600d9911010305681102040143c9500054440592030070701c1414078010600486083c1c019660000000402140a00b420700350480c0f69048a0300402c402c00078007002814541c11a00c00c0d10300815180507644a240d070307090604942030006400b0040c003007000d00c02e20101e540100c0b6440e106540608409504840550980f29a80300d00c1c40503801c2900d80c0402e250056150b000e4a1040c0e1054070010080303041401c0c04c4072015107500c01702e5980c1c2c13401481419024860702030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 952650485 1250 952649235 952649237
    0x70b0402010e180a1508010f0e160b250b131704030512031302090a0c1d100e041506090f0603140103061505090c031603060503100203100b0a050c0d 65
    0xc003ca11481e6a152250290100080c1544c802c9a1101020405074100184c000c1300000c3c03011003550300c0040007600084410150710b01138100f0400810200c09915411942d21004081c14008518010200440c400b9880000300c0c82007a070b06400103085400303540c4070302d5500501101000d4642441840c0751298520f6600c403450421090002c40d80001d5031003002032a1402065403942da4031030198440d070b11034500a4000400c081804086052074012510b00303100e0b80d8444241260412140c2c541c0244032035421b0300200d182a05040d030510510001000b0070003d403012a11484401c9523445da00300f240d10420014105000c00e001d003420b0a111107008003410324050148010014008050b0901807000070600c1d81d550f440d002440e07201d40d03104030003400000d0400007145400d80502c000e40d441100c0b6000280c0c0c40c0c02025603060b0103849402c041e100c01034010729006034104407510096001074101c03284034a2b6001c0018604522000034100007999039151600c8440802c000340c07600c403182e401d81b0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 952651735 1250 952650485 952650499
    0x30a0806040c05090909030c0111030a050618010909020409080d1e0905121e0a030204051c0c1a30010608090c0409110904060c090605031005101103070b0402010e 71
    0xb285520005880001008940c26400381c0c4400102c0380c654030880315501d5065081c00036060300420014051845070030007000601565950008008101411400b00029014103400502810300d1301d5100f811a68805000064680041e48130010260007004140340965101d40a01e40d52214030400c9540c0e00b4682c80003804000f81550b26103442c0c0c440160740111145020820401e400407441300019040c0c004861185c3d03640c01840003d0182d486401010b0091008102601c81b03008400d2030031400d9038102ea01c0030845800c00394800c507861b0040750300d0400d001c0140f040c2c80584c46202d034144e90720b540c075441c80c0041401c081d58401e90722005900c04000c0c04a03000c20000c145c000401c20025400040f140042e800080d890815601c0581c0024203401011b4481003104201c0d1580c0581442050744c1c848003161595050704403514481211010046070300b02e0320030010350405007506080302c061810200d000c100c140042a1554212070000e59204113901c040c0802d42d60020180088200251008 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 952652985 1250 952651735 952651751
    0x10e0114040302062503090f0e07120209012604141204030f060e06160306081204030f020612040308011a03060d110102011b0201020304051b10121508030a080604 71
    0x190040c1d0266200181c0103100010b1554504c030054080e02c03500e904405013280880000d400c00509003000c50044941414031000041400071008584500c2045181da0b0034015852400c0c410010390003544119050214140c02c05041c00010310032003400c8900050302c428507140500380103101261500c510a51500f1a424540150750000211003d8030340005161010081074034002008000d1030360307210f1145c0112001e0150440c1d51486151041e030b010f80d82881a1030b196100581c552000c8184000d803000200000c1001594092804084038001031056003400c4860303030500b4036514104c030102c000500f104014001c0039003d1031403001d00320802e100c082c01d5140c10b0000c285c801c240e031131001d0012900b9081e00d0103507a1007500184102c103000483d00c0290301c60908082c1c00303900141d5003111540244800350b03940da80c10140c0f124034031034001c18810070410604001d0b0340c581c0c4a8201061415143c599400d018010254040f0007000200300465450400500050800c0405011213100754145800 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 952654235 1250 952652985 952653017
    0x903021f0605100f2606090c0406231b07030302120307090909110402040b12090a050307120306230f19180e1c0f09081f1d0102030105010e01 62
    0x24082250a050522805824011a05441d031a0b001031030001c034001041017000584500f160154001c203804d54044195407a5040a0b43d1280182d00840c000130f5102285601c01500080e02641e0414101d404d141ca04200c1d1620001c00c014070000184140d480801d042081690400c094910011003952041c2181402c40d801480007445201d121002380d201c850718410301288108045100800400465840f1750714826009141c101200c0320003003814070ba00060050101080040003603a0210185140c0780a641e1840400501d04042d01b0030582c2d1410046201c250869001441090742889480c2c48600c0108100034182540d4034240101d04104140c42055115144002a40e10325041a001445c020b0740790802411007030b0701c1072038502c542d202e105a10840050b2403200e100c1c50b81d4600020780130041064941c51210311482e03095a00255800a044004650b508144800018081485281282000259030350701c40b81445695000004010568121b2100c654160342030a00c1ea19038040210 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 952655485 1250 952654235 952654249
    0x5060f161209060e16060908120409020f1e091215040206090f0a090501030b07020a0b06010e0103090b04051c03060b04090c0207050603090609011127130903021f0605 73
    0x7410300701c4035464000c0402005501e400c8500300040d00d0301290035070401c244402d00861070900c600e00100b03482c1c042c04070b20b2000218580a21500100b81c01d03281510300030364400254005941060014010302065098050050103840340000f012201c8d0b131140b540000704801041300c03107000788031640a603040d991518100060726074002d404840c6c1c6901c4441c00f4001c00e00014054500790b91002e40024003003076840184d803200341641d004d1007105c3c0c0d240e520030100f61313640c110040016001c0ca02c840e0004419602c2450703064000041890042a03040003659811f60943c030584003120030741c02002c249800c6c1c0500c0070794110f4025035440c0501c881b41c0fa086903511684558040e00c44169102d201e041076442c000c01c24400201b50243c0043e6982c80d2000407952251b406480e0380d10b95500300051104122291002d035681e0380d40542c0685c607103c02c81c180c2c140b0705e05000790340580c0085004c1e180700c480061502c00c0c21585402600507040b0300381e2500000c108200d00c0809001014074005045c0b155840d095 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 952656735 1250 952655485 952655507
    0x615050705060f070c020f01050c1e0c0d050604110312041527180e0307200301022a0f0102130603060f0b070b090f07060c1a010302090606160206040305060f16 70
    0x47c40d403460b0500e01000403a102c0c420f4542c401d00ca4401c0380c0b0030714505082c2c01428100c05000e84266034814103e40704105021035941b4026006038800c601040c04125058030350141c040c001400c4442410100002802c40c0c4c002d0b80c0044400b4100200c2500d1a03500240042281407020303410411042c903202030031081c0e6400e801140048880340202e10130f020860341c020b0101043c248102c80c0c80710362274600380b00d240c0030b803294104291a56244054042c20140240c1d580100005141001e400c1030058462244082c0903050400d0700c100e4600d8240c0c043c080c4001c0018540350301d2424503560803c44d015058a805030b00c41005150441000c2000852107011f5600d20f0340d005107200c0003615401401490418070508901543c05824000280180c0141c0c001c00c9103403183c4c00c82d42000014480119400400f4400a50030025a0b800101e075841c00c48002c1464a054000054002d4001d8001c0382c115000b5800803a01d6601030707428010a45400e09849610012600750400c0c014005540104148585 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 952657985 1250 952656735 952656739
    0x50f0f1b030112020a050915010f0305090c120c101e09030f02190b030f01090f0b130e0102041a030f01080609281a16050c0c060a030615050705060f070c02 68
    0xf4062900441d80d4800c0e56000800b002015044c40d428159042c1c040044541030190126143e5080400e03a14060f00030548104408409410611180814400300814040c191400c50051038554085036441301192004800e070703603482c0280e100c0a001d010045080d85400360303081c030907220743c2040020109100b035001c2903419260f1541d09108809030348010349942d040394200480110030060f000900041c1903040303039100c080602c80200500b030518212001450902c2c0c01110003906c2d010402100d410039401c2895400006181c2036403080044000050801394404c42e900020030310807412000380d412405082088007629980c10000d0115a8854a0075001d107401101c91144560110b04e010310f640040e42c10084c10a01100c06180318200d00c5000c44914003c3c0d0742113601803200920410942c0e00c0501c02c90001c0ca802000b140420600c0e4011031054020992143d0b0080b402c80030150380105002da49450b89a1541158070340759051400051009021490a00070041c6040e880420003032902c0e01 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 952659235 1250 952657985 952658009
    0xc1403120c0a0b07020d1803020d021905030f030d0509011e090807020d050a030822030e0a1a0301080d05120105100c0524060306070e061606050f0f1b0301 68
    0x3800c001d1410441031030000791208500300700b00038180c0e802290030015a281c43da940d0302c028021100400860b00d0b68000a0341050f1384004010050034407190310010856084103100803107950300b0004e45440d03901c104c10300f015000840e5854200c3c41d5801950780040e0401c00a01520055441d11105242007140078415192a40c00704424083c10754100c40900f41c01030b2090040120341d0800607907440040508500248500e0002051b540001880050003204146400003002d07198600711800c403c4040800d030711110000d000240d40000c030322486241504a01c5050720b96241190040c00e00c45407034151b906011081006c3c944450814911030706648003221448a002c840740d5040761b044401c160001c00c07610980c0b024117030311002d03c941000e2403440066420603660b201c0c0c0500d512684140c40c0d1801244074002100001d240c05d1001e09510420008900d0b00340303a0a45411056610a60b0144540000e00d41070082d00d565481c0030381d40c4a107544000f407032829103000c0410310b83e04c01407098240f40302d4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 952660485 1250 952659235 952659247
    0x50d080f09191401110d260403031e1802042304150b19090908120f16021f1d0a150c0206090706050307050f0310030c140312 55
    0x4190545103466405000a540420300407002c03007000700c9034010910081010b076144003907036200321442c1211048501c050417070350303181040542c1c24034104144001044980c0c102e410200100041c802d203d280281d9010544800880301c030101842030015068402d8101014104102c0b09400a0204180d040da0000340044841e51007100315444802e0a481440400c070070b103c180400d4003d0f030070303002000c075808011002c2d14104210f09030500c500710924008400000f04140821a80442c425074054070740c442c6003c0104450880b014030440d5540010540813040c000005601706500c0b0100b800c43c0024620031032542c1d154070741070462062000e00d10f42c41f40c1e00c1480140741145212041d02c43c010454a482c11949002280f01180052003d00c0302e10b8400c54003c194230005019006e0340841c0041c0000c5400d0040444175540f009003080309100e81042600a880401c01c01540f0841010000d120424110701d800c000013001c40d840780140c6203c1010700e28145d40d010400038000c080a02c40595606 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 952661735 1250 952660485 952660507
    0x40308150603040c0f061b150605030a0311012315030705060a02010b03010b010e1804021903030f110d0e011d09070512010b0a0f110106030b10090510050d08 69
    0x880390389011a0824808000d10080120151046098440202e12452101c0d210b2000b00e0340c40c1542c01c035a80302030003a80c5401c40400d4014540c0c44114034901c801044198441c80400e203090041d1904900250218401075800358003882400c0400f040c54890400304510042c0301012242c028080e42c4903100041c0d481400ea903010004100105409031089444010b04103000c0d0080042025840c040e509040440c0e00540c4075040310700f00710714000c0c5100751440700035142c000015801031040b600881c101020b8240800c24400700320046120b940c41610146213000d008000b04c05203d0010300603400041105080ca80005882d441100c0c00c0c130708010400c04200d69255240043c85900307170009143c0c0c040c40b54242e4404020401d1100900c9008002e07680c0d01008407152284c2012003000500c4040c010400c6880341f240944150780c3e0200200e822601c9450704113000f030042c1c800c4580c445540b80200300c0680c59010300703688000e49040c1d41801c50301e031001256000c90749540003403881c1400200015a4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 952662985 1250 952661735 952661761
    0xf04060f0605040608220b13061b02190b0a0c0c0c0f0f1e0b0f090901080d03110405180402030715050304030908030a020a0201080a0608010509010903080906010e040308 74
    0x4041110035200030036038030a806082035006000741000200c080d400610b00c802c1d002e00d11413808001c82c5004600b00190f8441c1d2411300c001601a458201991041001140f00c1d4021200030644891005400c11443d0b00041d1030080048032580c1121030780f100807400304d407039200f00309e60000300c502d400f28241801080864076000004801010342c1040c200108100310000142000d40e2206080c2c0362201e0b855088081902d118050158801c44a0002c01c0c04090b02c03800c01f0b0030850694150980c203108082c80000c00703441c0c00340c01031035641d4403040c002000140e05000307442d903651945240c03600d070500300720104164104d2141060605105032004c101103450401c00c110040c42c2c0c1400030440c00c00740040052555006950603400507540c640003046071000401180c10502d660340086c034000105174010350301038200034010003209079501c0000a070b4043c01c0c000d0f02e01c0b03407506000020340c8607458035000d0a803000c00381250740154071550040c000d00a402c88840d40094160134800c0d036599809142c0482 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 952664235 1250 952662985 952662989
    0x8010e040209040b220506010f0611030304030f0306090e010e060606091c02060c0f0a0c091a0409060e1f0608030a0210050402040209100c0510111e0405100809100504110f0406 77
    0x88114030b81174814420702048150684401c10109a189550b54408a5250000748842c0070f840c6c00030000700d80003034000c02140c5801c0c03000b810081080c030b940b010b401045521660542e08280d45580f900300414506008159000b41c04484032420a104503000c5040c1c0c91034000c150108224004a04040d9a11003055034002a04141118505800b0130b400340e0322420111380031160341720500004119044140541d6251901d44208000c0308a00e070010040501181203040d17030002d80d107807000e0b00d001d1410310050101000101c201c0c02c0b0411041080b01c110b9125501840301c5030800d000320301040c0d9003c15544414103801c1008640e070b0700c0c1c5000140c0248107001809a000d01041121040507410050703e00e030f103501132010750702800d2800d84288281c9203102501c0080e45000c10070110454002c20a88625628404240d07041584820116006e41d16410000001c17a419508116441d181000340c903100b4288010309101e00d040581e196091810041e000c20702c42e9802503a40380709030b15141e1003440 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 952665485 1250 952664235 952664281
    0xb04050d0908011518021312111f08070c02040e0f07050a0506030c0a030b0406090506030d03062106060905090105090d0203090310240e060f090906010b130803070c0608010e040209040b 81
    0x80d650f48141220780c2c13234550084841041030062030301240b070680a00b411051640782d140001d070207410303c102d501c080c7c0209003101740b1068080744409a00c8920400a000c095000185440302101412906c0d040460b0300082c40307960440da0a00554480304141c2e600680c5107050300340c440c0c0d0303038000c250060f21032003405030b40280c6000000200c000254200358051402035050740ca030f0300d1000e031084013038580c18007506d1641c10729410344944800805c0c8210260600407680026860344903802b179070a81d203060342c0118040c0c0d1914140040c0c01c5c03003449031408032440d5000452401c0d0200c00825101c83c0c065040d401c12a40d10a080991000c00d903504512840c0c541000305522603e80f155152482800d5510600032298821440c2141c1403050040d401200407070010b0050380c1c640322602303a440c3d10501044141842c0b9240c001180d030001c000ad00300107841303028410340300e42c00c6c054000c00300344050f406103003904200024800562141400203030020340122085001d0707612110f00c0e001096104406070 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 952666735 1250 952665485 952665517
    0x7030305181b04050a0e070b0a14070501060806100e010b0918090d090b040b22080f030319020f0d09140d120c03050405030315030a0b04050d090801151802 68
    0x7060051540380c00c04142e0125070401c13580d1a110f440c0c108036a20110941d19650111606202050240e0003403c01c1003420310b803c803400a4030000709032880d04242d9040350260346030b0308280b104400178071159522121084404412034940840c0c9001d6080611550024400018500d0400c0d101c500c86003002e01005060900c8505044142c281d0b0b4844980849000072685100403502120410031174041343d41c0a260541480340d04003040358203040300306a09000305c032032240c00140305d982400a41140600340b800755890b454110701311001e02c0b07110480005500c2c030400c2000340c40103c4100340e0340e02c662400400980f440051030841d00344220460302c0113242c0308100310340e40d07603640c401e00021880003002400c0c41442d120040030303820796605690091013034000b4000a034500401100030300f0780000080c11212100c010791154034100d0000e650941c1c0540110202c1c95020342c0101c0070100402d0503000070854608004e0712496610260b00901d80c104940000c414104280340d0161003050307001c01504 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 952667985 1250 952666735 952666753
    0x15020a02100e0f0402090f0f04021209060a14070804110114040f09060503060103030221160605160e061614061302090c03010609260a03020c0a08120703030518 70
    0x1d802c0848a034071143c4111103d64600c03105003024001e0700c0310304501034405c42502c4420300030031a0b00181503002e1500142c0c00e00800c13060f09480f5046900442100b0f005d40720908050003810140c1d0902c0541c150044082c1c424070240c0c0d41e01c94400c507406034002e0301c000e00710214400100c80c0c0c0500b152055003000e001203030108200840c00002001c4074040c480401c4034581d00c105243e141c410034400035016030000c0741c1c00c1140103506441400022440c1d2040780c505004030070546004209180d00b40c50180c0d440c41003007038403c00440c0170000154181014150542e46800060292041442c0300d8600c80420351207408010458000e56100180a429500c0f10300c0e201d19840030a0a069409a01c00d140c420007148000c00701c5411681a82c8040d40c5144829050243c0ca20140350044460f0070b41e50103401c1407000b40c480038004203180a03c29405019284076060400100101d00d420640b20f0707400284141c0075200c1850221050a07902d41404504e5603140442d07030781d481b8401e82d52003040340521180 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 952669235 1250 952667985 952667987
    0x80c09040f0b010e0315160504090608030304140118030e060408010e100c09060f0e01050d0518100216120912050f1c02190813030605041a0c030115020a0210 69
    0x114076101c1c000e0b84d030640030042c10410142d0b01c031500084003803606605c40c042048000201d4106501c03402c1801e00e43d01d42542c0c1c0704c40c1c100701c8103d07038452000c9800102c00d006c01c000325000e2110b9802e03481002403200244110505d403048641c0d000080078401c5520f600b280d0750720356200b61401065914000c101c0114200080d0751a40744050b0b0b04208180b42c4240d65201138020031070001501d02d01d546804840120342429102183e080345032a05010040c01008001769842c013030340384a00e2081c46075010500503580210701c0e081e0407840680d281d07070051100e60b03076030320368000450380254000e00001804000d0b90b20a0324183d0700c1e0f400900c2d1a400c60388803803003171110001340c1e1140340300c5ea641250b1a140f40d10fa42e4120708200c3c0134115005030071264040c444607101c00007040b2100c0c0604943e40c80d050000024401d019881d6001311441703904d900c100010301039503840c1140c1c41540e204039200300707107807522000103a40b00c14080e100403d2680300d55001568802c000300d01d40c4a5014250040c202c13000f5078 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 952670485 1250 952669235 952669241
    0x11030d0c0e0a091a01020325050307060f0e1b180402041413030e0a031a15031b010201050618244606051617071b080706080c09040f 58
    0x64500b04074012650751134500e52000080b80da41c0c40601025600c501800e142108000c2c40e0200d042d01c15120a00003500804d0b03da218800761501041030005903503012081e02824900800c0e004034251601c0c001c5840d06440d114400712980c40c0001407502150380301e00c005001842c074282400c1c038114414003000724030b0704c030403840c11716050113600c41001002c1904208031141065010042c4032030341d0001e10341d11021010001d03079041040200c03201d648980241c0800c1c82c00d4200103010098034210420b007407072940c081c4103040e00050141d840c54803145a6501e40058041302902400740710041c110f804805040000b81c403401e1000040080101c1c0321400c0903891801c1c5002c0c0210080071200904102d1030000340a00d220040040b01c2420b1a40d00d000700c161055000b400d013062102405841032070000710f0000e0b0040260005440103a1200040e00300345211400c001c1540300d04114086003031100c1d440c001100c80c100c80240ca80001d4036610f0b9560500640110148150000d007445000c001004183d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 952671735 1250 952670485 952670501
    0x2030f0d06080102160317060109050402180d2603060f121501180609020930061905010b0c0a2d0b0f060d110415050d05160611030d0c0e0a09 62
    0x340e141f030715140d40340d21450081001940c1560103c0c1aa00d030400c4142815000713041c607100c07404526541c003440400420050600308070b0403242d00042c1b0042c940c481c00d01665440034490f0112440341189003400200d091270030948083d51107003440045542808204000350600b81d0001c1c100000c2c3c0396900e1480322a1003400c1d4005c030701d07600c0c1001008150903a45e4400d070f8100c60030082058441c00a0001d1440c021901050a102189c55100c1d0b4603541071800c0000c940203c0d8030701c460000c41e10307044182d20129001038111229a01d401c0000c141052400204400c005400001002c807800c9100c10f8480900000d517004c9003625000500d040c240710b00c40540728030806401f0741010081d5550b00401c07248114054004244116145c441086400c0540c08020b418021081c00d5008035151000900440707034080302151075600240341e9210542484c1420401880b580c140f0240c40401060420b40301d000b2403007202a001d030b889140c0ca011602c6148000c2c40d500340581580c5206031903040b840080c080780 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 952672985 1250 952671735 952671737
    0x10e010b062b020d020c16060c03121e1b020f0c0604030602030c1e04030c1517070917071a121909050607031b090602030f0d060801021603 61
    0x2004040450900c102180c40300201c01c8000252400c2e589520b0321101000460324000981c2444640b0003440140b0042c80003000311401414031000c0b005850041d82001d80200c810000b90345018000283c0281e406401400318070004282c000c0300600c012140c103208448824101d042102d04621265900c1d011800b101c116420354400c00d13035400d1065034610301c400c0801d4101a0030001000443d0301ca901030340d0800c06e8a9480b171703d03000c07444c1081081c040d509062000c000c900003074104100450201c07403074018a5050b6040c02405a4031070301a005500b0700b1000d244c8043c210001896052060302080058141990301e0080c1200c0079242503a50003da01030030b070501c1b000c020300890891582043d5180f048110071030503000d559140e440b5950200800c107280019440c1c40c00080096828082148214100d030350000f80e100e900d0f0b950301c28980d041c0c4101c500f0302001000c02d101c47c3d54080212030700e0b1500488590764441003140640000c0c0000d034004e11181d40b001c9203c58030f660004445101c45406 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 952674235 1250 952672985 952672991
    0x3032d150306070306150f14130513050c070b0a141008120306030c220e06070e102a021302130519050405040f02060a03060e13030c14070314010e01 65
    0x3c404054007110100d005500c00010710b1802050000e11525841e100c029a51620403d596031111140c800f41d000a41d41003060b680c500001d100904041c3c500d11400180301d04244040d040481d0700c5409803050031409823040c0d80400c0090360b07a901580210300e03030314290060380c105840c01911149441c00c603030087e501203000d6102d0a4042c840003800350b034080c0700c00401801004018400f041485403000040b240b6180c0440880000d07a601e900c2a001403150b81406002c452414040051040d00c0d8501102d1055441030030442c00c01f640703c3c11444c01000c0840e404400c05018082c10310032409070810003980325500341e40075080d410242c1c0180c0100b003011802d0060054503482080f2454a041e02000d64100721000200070502d855001143c0090060030b551341c240071a5000300b0115407200c1603080200e501d4010800c0480588800c55501860052014400c11041d94008140c4141e440f40940b132580308280301e800c45003003441510000e40d404104416011406581580078150301041d070b40302546 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 952675485 1250 952674235 952674241
    0x2a0f010b03070e130614151c0819050c031b010510080a080a090506040b12240d02130203010e0403021c2109080c100e0f03032d150306 59
    0x380000c10303005480300c00da02c4102c10755903940882c4c1c00f0f211029041d03030741a80301c8107100031403000600c07450f004901049209201d0300111042c80400040303110100c02d41c20313010f0442d1020070303010700c103039110210484140344e55003000640880d410b00403c06070306000d002c0060150071182c005000da0b4a6101048000d001d85eaa50708a1220f206846100c1c03200c1541200b080030000810b4000182140052410107030b000d1a1140003207a0340703030481c0d00b00c411300c5403000070001540441c0c1102503a010445510101c42c221604696044025140c04250b00030a0180300d60b42c110742c1c1d02c40d503607403098981031411512507954811000d0003500a0b501a00580160001c0c00280d24410503900003c0c07485072100300c110603121010a49092080d604141c50540e00c080c2c040004182200400d981000d1400600c40629003107007020482d500240101c04079480303442100c201c1000841a29441000040c000240340301d01629008880c2c0a8081c405002c1710382e41c00c102c1003040305140295407690903021680a65 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 952676735 1250 952675485 952675489
    0x60305070906080a031b05070608150901060203041e030b160f0509090114010c0b0708160914010e01170f011517180f03190f02030414062a0f010b 64
    0x10034034001d440f03180d00301c4e06584000c1783c0610803141e40c0c40080c0285c0d40015400e07489040c103000380c580000d8000703429002030004240556164050458040354450000c0d490003002955070710480c410341d00c0d814205038214120b030845502c800011034010705298047e24040b604440c07940b8040310141d0101d544051110201442501a0b50b2112030280040445908040f40309078441c0d050322629040200004204d00007440b0400e426000b582251507070202da00300001c0c100240b8084980480410890351010800e203110815526001c0b0000e0030030a40c042c404000480308040030303c030030020040c1e12005009080f01e038180c185040300c108403141001d80440040c12251600250104010b220185010030941c0328241c0800444012070300072516403010014003203080d03800101b4503800e03d5041c04a41800c01d07420a100c110707081c034144003952800d801d002c1d182007460b040f0300049000c0d45012501d900d42a02c140c04040c0a154403881d042285140319407500c1c0e0768091146807292075424024599818 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 952677985 1250 952676735 952676741
    0x215010b090f0607050307050c0f03150a0f1812080a0203091c021c0816030e070e1e010e04141b1c0605040b040b160504051905060a030603050709 64
    0x390303950002607860710080c1c8080051402e000740110740e10840400c00c520010384104002c281881c81100905031960040b01085552150018198000d810103484103c5010070300343c1090788514a40070015a0701405030011000709032060840c561002c08044d490140580c400714407001c04060340d40d00b00c40c1d5940c5021542030f4001592400641d85c40540600c0301d100888204d009240c4c0070384103c40800c5152202262100a104406000304a01c1c01c00c0c0102658800d40840002e0a542401c0c0527100a0628071950340400348150450784201c040480c28007800300c900f40c510903401d141242d40700c0d40c5030303107000c1140c0700291000c0710440c035901191000d0200114240166600c05446101102100300501160650281000e042c40405260010002d400f520849010b28040c803c1559a8a01031800041041015040c245200307000010010302c5944581103034151202510201c3c0701414915810491812541203140d00141c00b14491a009505074400300407603006130103c0c4c1c8002ea4950f071904c11 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 952679235 1250 952677985 952677989
    0x80318030708070b0403120609020714030a1e0e0a241e260405070e07090e280e0d140c120708040e0a050a06050f090406110c160501021501 61
    0x352042c14040500410380f40c5480d1a40a806404c1c45442c0c11120384a000841d0516000b2580306540403402c0c00602018403100c4980102400c029442e244480790043d100400c044444641803180400000310540310382d000051009002d400c1046180e102c000781e070305420880d1582e09001c810300ea5610354941c0b14a042c441c107041c10740d00745032511591a030110342c000e4088920103a480340c2c42c903003e17048446060741c0300d01c00e90141020f04440c038102000044c1d03884000d00080704002c05084180079414034000e03011f4201c01c154414400745401c240c0d51003419901c0c050850086894510804034001000c12900700c2c00c00503603181a000c4480300707429581c0c1c0c0100d070100c0e10117500031080d0ba20301134141402081200d004059060500355160b00ca540201001c40b080d031915510b40c424000702100c5c90080101800007126956981d1540ea00070500250700100302401c1661610003880180941c04122541240d0341070a031961140340e800414110340041c81058018454a0703450b08115100c16107c0f41 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 952680485 1250 952679235 952679243
    0x521030c070e0f13080c03130e07080f04081602010c02030109030807020c0604141c14010603031d01020c0f01051614070905060303030a09020604121104140910050406090f0803180307 80
    0x403001342c00e5160b00c5039a0704041522a020f00c0100209516102545690030041500d0701c03014020b490444402000c0c044040c01d4101540b60a205020000300c0b50000e031000125031030030349802c4203202d000484581800780c0d00a501075103400044814154083c010520a8902d5021121031400c12000d0018502c103500c510ba5030804207098400c8030f8540409180c11550039803030007421a036a6500d5419110041403414592a9903c8800300209504000c144400c1030076007111260442071800080d46030040202954070030075081240b012581e00501c1039582e00f0034441c03010315107950302d032501140d1a907031f5a6030580c16201e40b520014600c1e049014403403141502601440c02d648030f01007940d018004080040703900c40c40505c000f1031624003920414280c0b5008100d4461014035000a200032039400d890740c80d408000c2d800c1041003000c0001051440d8a14045002940d44c0c2d4905041d4003c012000c0c0040c01052031181c03203000d1045440103180901c1d181814030071161250b01d0a59645e1041d448014 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 952681735 1250 952680485 952680511
    0x3030b0f0609150f0307051b120d2a090e060f031903140313020f01020606010e0105070606090501140109060c0c03080a030e010509070f140a0521030c070e0f 69
    0x4128200400c030030080070346008480e810f0000c1c1c0c24009210350021200040020400302d52005200c21081004c8c0d40c1c16100d80140c0201905a040d0461900c6054090300c980c075101c41044201e40150915600130700c81c0e03080d05800040140d0070081c0300c42080d02c218042d08041c0000b06805141c0fa522000310810020000c00c0c52500c0c030424070a0201e4203007029400d01245440c4029035610840041d480340420507102c0c1c0f520711251041011507064485014115406370041000a9821414042c6210024240107486581c1850008064080b0750000c04441e130404000160810004a0342d99a030f40007602c40e880c8864660700110381400304524050210400d0350310400201e0a84e40040616a0380391070007144208400c00e660b401d4540c26200100f940d440b424080055800c031111407400313000d0142d081403400c06440c0000e1035110312401038600c1401d40c4901f4811240103030400c805140d81c8003060300e449170f40394005079071105c20500c26130508102c440001150030b40340000c101c0c4a00c01d942d00003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 952682985 1250 952681735 952681747
    0x5060c0c01031e0f0c08070203071106180a0306091e050a0602030402041418070603020901052a1b090601140d0b0307050307030b0412020d09060302070c050a08010903030b0f06 77
    0x1180580300090f04540c1901e1061a000c030314100034050040c92107240e103004034104907040303401012107900502c03800464006120703202c0080c20120700143d604a00b10741c0e0f20785606181c403100441502100c020340d40016404400410416246c220749202400360060031102000440c621040013402e003c01451a00544443d0001489a86c0510380140c0003520002d258803119410404480e010347d044908802c42590b250b0040c441080b80c100034160614040d17040c03802110018015004403040e928650b42c40100300c10081150203601c11000881000721588090030031410308a103221424090700800b01580081e20a5005448150741200181d91442c94000244c06450041080c440884d505000f05800090561350800050000d180070342145107460809181001980e08201600c0007550001c107003d820050700f00b101c410446085060240c0e4840a40c5800201c0c0d02203a080b80d54401c640d4030000c50501415844000c809200b0b450820442e059101000060040d40198681c080b42c02c000c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 952684235 1250 952682985 952682987
    0x507080c030a020d031407062c0c0f09250f0f1b020603090f010c11061f030b0c0d020a0e0103051f15050712050c06150306010605031503100b03010605060c0c01 70
    0xc20700c0e1080c9011035050421959940782c1d015101110403805012040749d48801c0020042d401441042101d1001010a09040b6001c50030200358002c9041c8101328000000781d500950042048209101140c0c48025031040c00c40504000f40b0b03006094002002d1a440c0b020541c0a0000c03800000d00c00c4031064444403141d800c004d0141d000810344641c5024040125046403024002c2119001c4951500e000e000c04c922812894a1801000328111a00c03004001c10682421189241507940252200d501030343c4140080010b4400d400d00c44290324400101d00a426905c05012240c09000340d1302407006484a4034000202c031010043c441c0c1c0030110310010801401000180e44040764181041030801181d03031280e082081031a1034020214500040040c40c2da00188201d0750300038401580314614015007000710780d4070038050250100b4060000081110068007444250710141c00604403807c501e054400709000c0d0803000c8100d030280d806c020b030106592030700906231a00001904010000c049c07000c40 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 952685485 1250 952684235 952684247
    0xb0c0f040b07050a1704090b031c2f0619050f060f040f2903060108060c0304030e100315060507080d0c0903020a030b0412111b011b0507080c030a020d03 67
    0x40480f09840346000c035070000382c5620b038072030340b030540c5400203076100c0d4500a515001d5441207907919100fa00302c00302d620303103460b031007200b8900f94201881e00d05142c507412490240042c02d0050400f005881081c401c2030301000028501d8800d0204100040d8007071001245181952000d440303801b1910400b07000513410342001d0b0400d05003440018004500000c0300c6500038121507071400000c0c00141400a22202c0e0b81d1240b00c584241103007031f00104034640c54008201c2e224840076001000500c0008040703820b0501c40c80d414400a103000300011030005151202400605840398154402c52050400040c4540220252000e9a400102c142d180808000340c01c001001c070515020103001001001201607202c510300d20019602c03075990180e442c00d02e81000072180c0f800700c004c101082021101860070242c0804c0700d40c2fa2a0f100d8001d03002c0001d044005035030740c402d644230500b548401d00f00d4203824050b001440d07200319a16041a07800a10780310b0180742e107901d0310000c00394000e5200c0300c400d000240309035 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 952686735 1250 952685485 952685497
    0x3061b08070804020f041e0615090602150a0902040609153c080f030c060a0504150c0c080d1515050a14130f031505090c1018080a0b0c0f040b 62
    0x18400150145901c4140c90007021006072504400da231000305001d41818019001100d803458100b00c4155454404020764440e0412304c00003c8001040100e10448100d40040443d198014000c0c8041c0e0b40382ca170400000d116040c9a40c54603546928001941c500642651070f0740d1074601d04140d044030082c00000c0e2600e03480070352403503100c0c00c101c00018007001c144500080102031801440d6221540020305140a00c0a490103403141d1420041c08005002044408042002104086142c20111368151034002c207000d009480741ca030000328142e0110440e031124108080202e6030044c0c20340c440c00c00741c02c44180180c103440483c1081142c4c2c6070143c01410000700032002c21154a1410360382d60403640c1100a00e80c8030107000840b13407a0902c1000b1b007982c2046015007181c0410400d500e055192940c1c1c89101524141c0101181c00b041e054191040300c0c10085e1548440b0300c0c0110964039000c055403040d1001060300c0710750041380861445240302d400c45124241000c10a4141420000c3c64203240c1c2c840 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 952687985 1250 952686735 952686739
    0x3120b030309062a06040314040e01060c021c0b1008030702090604021621031b09060f0e15070201080610020d0810090c021513170d06080703061b08070804020f 70
    0x13242c01c2001030b0300f00807407445440001c001038255400c06140c0a0500700c1c400320402905101400248002c440108860b070445110785481c1c1c15600c0c4074008590002e00140801ca44800400814824848090a800d00900040025080c00c96039412255200d0003460381c003c3d40028200c1c04240c151400d500034002d8030000d0f02c452907074081079640e000c060400280c02c3c101119503064810700070540520810180c0d819005554044240d0b03118000c00d010b20a02401045c044904002c81c07525120720f00441204401805c1403071003069101a070b074000d8000c0942203000a281e08002091350500c0b0340c2182102180390024184101800e1098034020802420003036408024007002070041c01c2c50140c0c11000c4002e03000f03407044818140705038403480710003000d000302d040f68002c5400c006104500072460003074203055002c3c2c440c05408100f10140c0396650144045d80314200000c030900410f50300c040388800b54510703504a07060316240d055680071030132503105e000b05841c640040c000d8105074500303800c01c800c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 952689235 1250 952687985 952688017
    0x206120a060503060a09020109090603080d0903210603050f0d170705070602070602090312091503100306091202012007030305070e060a020f2a0d0501060f06050703120b03030906 78
    0x49501013458142c0c115016071407161503003028400e55070401034800c080d0680c07850502c542415511122941d210380603840701240d59034003107101414801d042c0d22940960520303c1050007650f0803000c4000d420107000541d0540540840140c0101000445000d00441d544568680f449134892102d074020009001809101c0100712400000e802840180181031181d1001a2210420010705240081060a450a44070f0400031200c0ca5a81c404401c0f010401001010f0341d04d548026070b0350303c0c1c83d00c544c0c0010140380c2846002420003020908a9050a009500802c10200f21450b14281a07130f40d400038208004c020480600468420381055500008a050180c400c01080002c80c6969010740c00c2400146c0000c012000103800c103000c00c3d0601c41d83e094043c40345401045914480018550340648901c0c200d95180d020803001390484002000c5e840b810001c001da481d4800740003903000c01d9003140016641403180210645601c14640e04000c00340046040c00301840c24440940c0c040b4080d1280c0101c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 952690485 1250 952689235 952689239
    0xc03051b03030112112b0c05030d1707031a0103090609171e03150f03070306050108010c0806190509151504051c0b07080c04031a04020f0a030206120a06 67
    0x1080118001d101c01840d03610404d031242001043c100315604500d1040c50100c2c0c1c03a015400ca11502c00d00303034040818081c03103111303c10301d01904000d10781d43c00950180100b944280096412600e804070000d550500403d5980d10301e44200c0484030748104014020048013200c05c0709500c40e42c08484118441c0b00006141442625006000441ca5240e00d4515000050034402040c5404101d010080d13160451400d40c1801c104044030200044080750140302d0b018042062070750200a920b0055400440400c00d80d616000c0d810702a09070881c001c00032175005004a06075017411031499000c0c51003500f0012100341042c04000c080d44001c1c001208134003121204035610341d00c0b0a030700b900ca14801106580d075585400c1c2485004038051005800110b907000102012030420f02c036041d4498541c0c5020003482d03481e0f4030785108501039500041e001003003200b0b403014030b0054a50444d028500032a880003106c0c000d4001c01044003002d0200039080b500a20018400c3c80111241c20780040b1280c801041090b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 952691735 1250 952690485 952690537
    0x50609040c0e1009090c060306060203071a0603070b0f031605030f07110c040c09090510030b0403140d0e06040302060c0a0909020702060c01050c0d0f0b0a120f021903060e0309010c0305 81
    0x1c10800055822404c83c10f010000d192309449032000400d400d0003d1400c100382c648800003607140103488500c130061000d000035030030b95043c802c06002d4003c406c800b40d200c500401410a00c6d4104880c41e1805050805081c480b1600070010369200325000b0402404d2360356046002c44100c00407180341031240c401c919408180f9500c3c3d008078242d440066961106861400da6880f05503039001d08032080717205590f642400850b1844c0b01e0140d0064040c00d2902680f14150006121840341c002102c8005207046060401c09001092460055019600700e90850b01c40c001d070100644900e101020214010800c00c00c10041c054015042d4203000400684c10114610900c6095610450302401400740c000b55900340749070180b00700010420b80c0e001c2007040281c9600401e100701c0700c42c01400080030391103a101003000214021022183d5014040458002c07008540300c1c0030004600084800300d00b8500c20407c440f01c00800d4442e4107005035070b81c01100d0700030784050352070b54404500744050443d6260750072400 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 952692985 1250 952691735 952691741
    0x1413080711031524090601030906090c06180e0403050901050c0a0605010e0f060907051905040b040602012007030c060b0f102c1806060d061e060201020c0a03120b030a0b0a050609040c0e1009 83
    0x137006548038003000109250925881503c207401c02032200c4451014003001c00e901c0f00c2a980020300a01740265280d80c4429024945482e201d0020300e000c1c1000c2c008601601d200341018003a148074047c81c402e0b51607102c1086180402204c0c81301c0061000d201c9040340050f0a0180c100d850110b0801925154450b2039034015580240c02840160317440304840f03021501c0049180d419416442c500c242080119900180f4003160720328017504442e11954410310300c0e501e41081c0e51008000074030244101c42c0c82c00e0302030324140c8090000c4502c00780400c0f4801c45941c40342c44a101045004101d646002510404241c3d4020082d0809400000c00c0c82000c1114181744a518050408107003440b07581440c500303550251011a07000101164018001204a4440050001d5001d0f80c07504114110004070b4104500600300c0003492541481400094401c5c4542c91000c0741c015242e586003030150ba0703101401e111800c4816070b0010401d450396101080f41440141c1161382002440031120352403a510313041c441c16 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 952694235 1250 952692985 952692989
    0xe031c1a0d08090108010602070b040b13170601060e1203041211090a090203160b19050d0903050d060b07030207030312090b010305060a1413080711031524090601030906090c 76
    0x180000040c0380c2c040c0d680000174580100114802424140d0400803c01954000c038492007a80c8503000c5210403180c0003001d40340c006440c500d410030684080c5160034030307030310142171203041e022581c14500444e19041100c414406c0701070a0000398a0503141505038403025101d20740c265000042c1050921140c1c0e034480c2c4450080122500208007040c050040508101d80006910224010820100104030742d42e001d40d40c6495034088550684a600401900e880c45030b100d4032a4007500d0b00501900b00741e0020090020a0310310a000c00025490345100c694a2080c0765026000d030703114a40170070000f44a01411101c940d4068000302c2c075500d031541da00b000b02c40207130800c650302d4020303e04105c410745051003003501c3c0c01e800c80010f43c03aa0030030450086140b82400d4001cbc0440714001850700501c05030300e41c421a040e10180441d0783c524100d141c0190286400d0b10207000c180152a00106401c50310402260078840c01048206180c40f03050054004104042048401584805103000458080c0c507032000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 952695485 1250 952694235 952694243
    0x501091a070806010e0d060e0a0506190e01060f1505120f01030308090615060f12070302030601110309011d0d0606090b03071d01170f0a0507090e031c1a0d 68
    0x181c1020180600042002401d05040000b040110768441d550404c109080d5500014000b42e200034030b8401500740045500042c1c80e510500091040c02c80c1010b48500380c904d00041e041211064682200e800e80340244242e8400002200082c80140c0da690f24540034900b05003040c1c0c0c030b0600503924000c982d40040b00c5100c9802c0c00704e00100103054200c950329a020072208040c008529000044034030741c005c03401404c2c0c0203c00208441d501000310030104c440c080b501d6910411039144c440401406980220b07156400640c00884c00618180b0010503105100320584801060010f0702d5405500d02d03030005081c541c0b0000c10703500c14010886a205060150140345008529000040185498881a50312179146086101d8120600405190b50355064890401c4890484620184101d1514610300c4001d1076600480d1230310800c000c1c0020f42c20f801c40e901c04206100c0301840c042042d0312405003080c0002c260884c03402d200c142c60441d41c4414651039180c003900141e9440d06000c11445c0075012000c079 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 952696735 1250 952695485 952695533
    0xf02010c232203050309100e030d080a0e0610031e0506070507060908130603050603070f0308070503070209070807020d0e090402040c0201061d0114090919050721030e040203010b0f0304050109 84
    0x3511500300b1030f81c80c080038401d50601191301c00c4500d0200381e45c8d20392816108102f04003000402c800e10303503c1c0c100e5105051014109c4500d42010000c11341d80601f00d11040380c034a504c55540d0030040044070f4604803850340100150090703a942040c180d6543d4004001200d5081d510345140000542c0600038008203400500100c12103820203801400704c0d907003e0305492080e2b001c0101080b2107142c2c41610429a94407005030b64460040707192640c554014984020351200d66641044116903001c461584112080d5088400b0952100016548003500014444d04000f54000003005402c040d04058032030a02d41c400000c229980f918504182c1e10304803408440d00e69800010050038044608904072420202c40000e0182042070207142e03202101040c00001c1c013010180c4e00203100003031081381700a010a10608005074540c0ca8407290100c1c0c08003003100864030f455111000c6007840d1090707a0586035040000b0f46020301d500844802c0d03820050048420750f4a520b6880001185500100c00d01c0707000311104 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 952697841 1106 952696735 952696747
    0x30b24060f07230f0c190312140a030204050f0315070804060212010e06030114010e06060c2a0a1508181c0f02010c2322030503 56
    0x1540c500001c43d010340543c00001c903d440120741002d00792400300c3c50340e00801082c465038014405103880010004c0c40003441c03800035442c2c0b001090038041c0e0743e82c0e81900c4016807544010788100010b80c0201c0c04028505101c103031800d52400480141804c5621001d0060b803110303000f440d1500700308040300404c044c8a900e5044415403400124251031541c2c40e80e035103403000d0f40c060382c94500a40c60203011240160302c0c9a1110b06944181c08105419212042009165041a036007900305001c0c060b090308030801c48a8480d148110920310b80c039000d590450400034511155405066003d4540080e40207040e440a5000c3e4000e809000500c40800c150003400e00d40243d103007a401c020b003100c105090945400c0f00715419100d08580c0240510507459a0403165140c04081c800140c1080c182c0c1150350070713516005480b00c819202c00000011150601070b800d07246c403d60064070207800014030 = true := by decide +kernel

theorem cover : BRFrame.Cov 952517985 952697841 := by
  have h0 := BRFrame.cov_init 952517985
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952517985 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 952517985 ≤ n) (h2 : n < 952697841) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
