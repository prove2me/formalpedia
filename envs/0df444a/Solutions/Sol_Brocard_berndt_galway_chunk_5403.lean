-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5403
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:45:21.319992+00:00
-- url     : https://prove2.me/submissions/d6f7d48f-37c6-4b35-ba7a-b586a18ea216

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 971582733 ≤ n < 971762589 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 971583983 1250 971582733 971582761
    0xb04050307061d060406030f0b18070e060c060a050403110c0f0f0f10200114011a0c0115051302090f0f06091302310927110906010e0a0905 61
    0x2600140344c5992540c6e1840014080c00104400349001d510744040c0000c10f19003420000307005103880341d019078195102101954030618080740c03540c11031000c103c548003a50b0184003441c07040a11610000d501c4c100b908004043c1c0d80301841866459004450f004001da0b10303a019403070001d1080f80c2002d060241d10300400c96014440c1c1c0110742010402d2110210a42c0002c00040ba00300c13540d40300b03241380b040b1503507003804d13180072072501e0200f590480014440400e500b14810303d402c1c08170070340c00e1504c0307400110304c0d007120014802d0304200043e02c039041c00249444064100d10701e15003070f000e50410444c00f0006d404504031000c0c0c3c9126004c190358020711a00c5000c1941c8101900400c190704141e110210303140070b940a03902ca100c0045a20803150b2045180002e800f42d0341516580c50401c05090680040040403c0301420300000340740720b200f101205034180241c0c1203501c59a411a942041d0100f442107054015001605000140240c00c0540d124408904221101c182c00403a160700c481c1c034118040 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 971585233 1250 971583983 971584037
    0x41b0b1207030b0306161202070f020f0303070c12050d050315010f0e04090c080c011b08091c030201150b1c09020d0803010305060108070501050a0912030207050a1805010b0405030706 80
    0x4d8041e40b820864499000b0b03061a0300750b06c0e0340c2c550240e0180380107402c904a10640300c00804641d04440d010026090542c0e80c0751080300060b04a0389000440d0b01c0f4040407459a9106061002c031054214040102c2481840462071150905600358100505040d418003181c10003181001203c4215090052181e4109a00c0d5800a841000f1407072240c1080c0340c158401e801140128407698982c0b0320305501c80c10001400c4808407801550400c0a40d41d25003490b40642e000c1584030754284500c400c88012060107414092090b0000104d648422560b44031055050340309205500741840300c405010030b1051411401c1841a80001d000ca0084c4009042e408514101a05220b8044008400c0060028106050714203400403130b00c1c541c2e502c400443d100c0c03207940340540005110120811a8905104c00903071690300c6401500e480708e0300e40f1b012a40320442580440008419162107902c0602d040c407887d8050310101c00e8076443c107400c02010a54036102c0c0c2c41001704008400e51840d0340060035001c60031003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 971586483 1250 971585233 971585239
    0x1905030912040b180d03020606131509091101030b010203041712040b04060215010506070816060f0506010906090503300c03031b130b18040203040b041b0b1207030b 72
    0x4a40c0c542c45810b83d550400c0c200382c10906003002c00000786180034481688441e5160303000784401d0380c030001442180c6d109038600044040d155058040700041d6403407840e0113010300050000303c2c00900e0501c5802281c054050505062a02103d110140da0201c21a802e03141c0620004154041082c5038a1410a4420b40304480680214010424880c104001c0085400541c21524280d60070320140082030000e208160340003900300540c00004080a000d016020000701c140b80958030030381c4410094038501780e10002025514002c0040c00e6800144420240c000d62605071112414072010030740e0344061804040c40030f101051a600e28038102da1200182240504005e41c4507a070000140341d0302c0e041510f1440000d03078402e102400c00041c503016a140352400358481c5140d00d00c0c2880314030703196002102007180c0c0c01e031074000f05030b15441c1c60004500403840350300c86100c2032400b17003810b0b00000580201c81c1c4413540181c104109504254090b280010088100d401060715142001d0303000348120300540c0d030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 971587733 1250 971586483 971586487
    0x27051915030203070b030928120908010c0e0a150824030319022b0c020622050405010518071115040809043c02040302060304050d141905030912 63
    0x200c1194040c0650b0041030307890200c500c0d1141d5080541c03980c07608d045c1a00790240500c01c07410081001181c030300c50b0b0100c01d0308121040644810145003912080c000d0000071030307a20401800c1a04040d60b12800401d1041000c01040781c0c03210340102240c10141500700c0c2d400c80007000c0d8035021400360020b0180c8a004045940d00d6407142e5411160390340c0719080d800540150010800c0000d4a0100010092900700c01100307048000300303041e160010f07404400c4e60050414130400c1c0000c00b14081c050109900c41006014603450181000182c1b20140c100b240224103c01c4404050a03a50741119040369860400d040f20141d454800e83c5081140c00d507046020343d801c001d0005004260b0300801c402002501c0138400210302c10f15411101d5414405403004e0585500042c0c211003800d044000b00b614040b10140c41c0a5803074000403081d820540c1c003a103154000c0c0e1060030300a5001102151100c0300d001c030340c03800c240ca12403450344450021101078080c400000005221401d041c08441c03c07030000805056 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 971588983 1250 971587733 971587739
    0x906020f0c060f01121101080403120e0106050a08030a05040510120c050c0c090925031b061803020a090504050309031c091d01060c0218012705191503020307 69
    0x81e619841915403003010f045100022481c00f44920039001c0d52074005540c0703c111202403004483d4407200074010b070f0401c4003001c01419804000d010303154148100b1000131501904110811406905540c400a9164010805582c0064201043d00c04950301101c40000300c4480d19001c0c2d914807400361902d2101ca140105003440780360060060b0005aa980d01207840c030134018030911119200c2034860043d154890703201e03000b01c280700030348848816201804545001343e0702c1e501e42c0d0b000c116291441c8500540c5c0c0000340f1a00d41d100005c8001c116440401d000b0052a54001c2240300080b0301030a80e1040e1907200040900004208903021004013600300e6680720444090040303011199401c034800108080d10000c0c1d00c1404c0000055000551441c03110305900c1c1c560180d0740000c620100b05e8101c10400801c011400d0740c00e080600030302c001801d8030004d2000f030b150341784030811310140741941030700d0002030107059082c1410422842c0441840058030808001e5100c0014200382e000039030510407180e000c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 971590233 1250 971588983 971589007
    0x303110d0207061d191202011503120f020715030504030302120f01030501061a0d0b01090302270a27020a08011e050c0403051f27020f010815040906020f 67
    0xe01d109404e0f9400b280c4046001181561030307026540070141c14003044060000402c920b442d07517803820003150000140780901003003000700701c1440e940140d8408071280745103a0013a42204400e01182d600340301410400d410112500004500c110501041559600018040500941c12240020307040b403c10a06403604007800d00308458240004c41d01c1d9400c054001031088101103401d02e0240032803240904100b201c0000900800e10090960304224110708004050b8440402d0158100d84149060f408010761030407410b001c0001911981001d49451b641400180c2d011864184103d031400030398000c01014000590340d0003282d0031055865207408049264402007100c83c22213b40745060510940d921400c101e4100d00451102601c40e070800c03c800720711110050b030010b05c810050080013803901541d01d500400c500041c41001800080d008e81c00302580f90042e400005c1c03007400d191214242c545160310140c81800c0c0c0000340d00a0fa10340030360004008441e0180d0341102c6204034069201d903881c1c564 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 971591483 1250 971590233 971590241
    0x203010b030606030a322a0d060504020d0b07050307030e07050a0323030c0102270a06080a0e1c2c0f011b0c05090109021303022b11040c0801050d0303110d020706 71
    0x807145d6150051400301c0407403030020078046240c030780040231041c20803010740303c000c06409c3c0200100c0e48061907100100009030341c0321400f0f0003038940e07a0320540c03a0301c1c0020010342141c610700400c0c2c4840d0b012031403c0005030b44100050050381c1d4131400c081d403003c1c40d000c2c00441d00c045d0004520010f01010515000040341503021700183e6130b86d038010010318900d2064003252402a0108543c0006207203000344901070142030b0441d00684004000500740080c5803201e821328161200700da110000d20440c0c6266580d008800304030421801c0d074158554103a507181c03c10200004403805000e0395411003614050380c02800c3c00ca0a100f100201104120510b2901203400710250003584e10443c0400001b0420321031034400e407120405c45410390340c0c80c85d08613001c00000c18071020640c1c248020003480c0e1010714001103c000301c003d01c1040d0011031001014104401e403039506c40b00310100142032004000c0c0da502c0b03458540c40d658250800180b058843c20802031a4840c3c1101c0c40101400011540100070541d40 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 971592733 1250 971591483 971591503
    0x6140903130504050c0909130807050604060b10120b030703050111030703110a0905061e0a0926060f060a031b060909052e210203010b030606030a32 65
    0xa141c041081e151820442215410340d0300c54809442442a1a400e06081034000e8108001c204403041c1841c09903611221070303108107011616504040d052004020702ca02500780ea48004850080c500c040f5044004d1070030121050745036005d9110740040b11907403014003407200079540050083c000792a1060f00828250300584135440024a401d00c0c50040003025029507541982c1507403080a03c515100420809400c4601c80c1414107000140764a19031a11078018000380300c0a4540b000001e03c0d04050020f11140d085034042100c80306603480c81212400305a8a0b44441c95007151402c5840e41004111034801e0750300000c100019489607241e41d0b110000016007100d089544903000140c8902c0c04909444044c1c1d0041000041d500741003034034514179000411040780c1c1407070004403269107542c0f100401080c2a0501b078202d54a84c01c48081d41820f006200418105400401140c100a804280e5a841c44140603100c9100152204402000812900345030fa110030180114400800c000a4030741c80125 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 971593983 1250 971592733 971592757
    0x31416110d09080c0901050d1b051003050405010f1803080910050f012408060105070f0503030a0906060b04080a14070f030c0501030e01060e071d0409060203180601050f0d06140903 79
    0x310401004e85040c0c1e444506032070029007520756202d455a20200c00b0b80103040c0500241e8400c071008105078503400c0842e121402d031540c01140c94186402c0042c210380ba01052001d81c281460030400ca001807a80a400b401a45494aa0000d075284c1250034200a6950450400315090500b4480f4038580e078020581645d110040c14003803034400746040751509a03244560404145e0140009001d903000b04041c00b8168007810300c041010080e03030340321811540704803485840300da40c505245050004e00c3c4100005820b8a8030420707d02418074150981d11048110020003041010b409030030550010b100050040c0582c200b5803148507100c1c0390811125000d03010711400280b6000d410300d82070405024540c205e40807400242050b460b58003003100c4480442c4414580c0c1143c4030000070702a1903900c544042ca07809448016100d0400c41e404181200c1050106072196204d80e005005e103a540300d50145045004440584100800386005005000c040c02c41d201100d045004010340650040000c24a8050725 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 971595233 1250 971593983 971593993
    0x703030f030c080f090f1606020106091505091003150c0e09060a0b3612030c070b07020d02041d0f0a0b04060f020f0c0d030507031416110d0908 63
    0x6008100d04590000050a0002c1c0c10301c00440c084441c102a0203812080a8068510246007480140e21f0001ea140000d45821000305080100c00da082c81000c010380326602d0305010807454925014241c01c80b901a25100d10700000210b410002181e036454011584110226025507040703400d10000c0849004107800310b0304030000c4c0c84461070041c95913841180007c00041a2a0a100d10b420301c542000801803505460f883c1703941c440c0c501040e0040800d101c0711104040c41144042408094000d01e0500003582c0d00502ca901c0c9020004200305043e01c1d8850700c0a41c9074441800014070101c000500039400615080d0460a00d80c500c48818090305413840840f0844156440c149658452103e0042c21080c8032201140010310103801c0500142c6882002500b4104d00081d640004e50255907504900d501000c1c104003401c0c0c2600a03264003642504040000450f00a000f818500d4010120601c11064844a9261501500380304400c481030700c0031111040380402000e00744455a01549540340301d4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 971596483 1250 971595233 971595257
    0x10b1b0f0312100810050403051b07030507060311030a11130e06090c190e04141905070f0804060c11060c040e0c09060a0f140f25050c0609010e09010305070303 70
    0x4036500802100e45104c01014442403502100b0300a0130084c0c0100c04100d42048013520040c95000454496200c02001e805102c0c40c7d46841450441d450340200140344c24042421200d4110300240d80d4054156003001c119403001c10082d100c588900090350341d035400d88000102c3c411403c2c031040c6214070b0080e9120105500c6d07440d00c1c400c460250000000d0040054401607605c4c1d4880c890b2100300303040190010802c44d11100c00ca01d00108200d4104420b4400072010101d0f00e105030090541200842c200740c010103442980041101400802c060955600d40a00d00c002500c110203a600041c400026100141800d04104201d5480340c400c0c0c08554004801040c2c80110490840d0100d040062543e440d0544007071068584c1020050340c442170003044c01d80f00c641611990b004001c501d2070705400a55904c05850b581d071004800000044215442ca403010b00080d02c00581c0002e60746003201c0442c0c4908507030340102d0351914040102d941000801c0000410464001fa802054030700c280c0b01c0702d4100300 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 971597733 1250 971596483 971596501
    0xd0b09070309051b0604030b0903071505010e0f04020d120e0f19060806130606020a0317191a030106080a11010c08040312030b040e0f0d0215010b1b0f0312 68
    0x21560b0301c068403a800c600210003032440b00c40100c0c0100c20300941114203059a94681c12031113401250701060581001841c0c00401100194007035019516410411455040194002d0701c150020700a142d40216200820f080d984d4812000900796442138094000200881005110401a0b140d1070701421103441c50750328500e4202d145820341e00e2800c074456011407a2a41c104c40c3c0c21006446035811615502e0411825551401580e0103054250001c0105100c03d01d4018494200d1405001c003811218080c0844185000100c40590b203101c0404100701c440c4400807514610070b084070315455841e150740001d400b900852041c43c03140c0a101c2128010194000548100f83c00450040034404100001e10000c2c0d03203078001203418180d03480c00154007240708e40032408540049881c441c850f4001c40e5a0080880300300680c1203080a2440034000c0070b224050842243c1006008032010824007003840c1d0345011500d02134030421402d80c02142c568000305000c0c1d6850b503018295030703621a003c0d2000104031304 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 971598983 1250 971597733 971597741
    0x90e090d0e210a120302041404020a0c290a0203070c030f050c0a0f0b010614032a030109020c160b1b160e01030b10053303090f01050f16110c060d0b090703 68
    0x723180d8210014a8000362042000030341c080c5142d14103120040d00c03200040340015040b0400000e9001c2c2980700c44070007803800750101e08020428005580100204400c0581c80384a5201c0541d15045c901d0a800610301c05450a00440652410754030030340b4060030a10048414111099009503d110180c1c0d0301c0c4c280032950984011958001d0300401c2003c55082e65030a00151030074000c0303180b51025419070a1010030294001e9000c444141e0300410041c000e05010722550700300c2d0303605500d17580161b8030340b0000300c2d224091710b01c07002c9101281c005104c11408003405018081c1c01c05d40c0b02d0100d200c1d16403000040c604400c3c0810317544081340000080c0c10361720010340c00c8240d031002400034100b2903405001400c0403002d58084c1e44d5120171f402c441d05a000c049005075000300d1210002c2c4c01c083c851031407a24210f403070081c032021554503a1800c0c0914070b41e0301030484e07401d41200c0c40d15030b5a182a8042940c40c106032580760700d0708500d0016144007100610380c0a141145400c0f03d0202454445c200304030f050f2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 971600233 1250 971598983 971598989
    0x9030d0f0501120b091c050a110a0b06040b0d02211c170c0c06010f06030b03210c03210601140c121c1b090e090d0e210a12030204 57
    0xb5242031003600740131a100c0c40304d15a000381000103c50f0010410503800030034002c05035001c4080382c0003007607504550b46c202020454280c1e03650028107250103a0f4440da04009400343c54680100d0b078500030442c0302c1d101c0d58101116141c0140640031303241c55210580519030780d03074119144e0b84c0c010f025550040b0a1071402d000b8200b082ca0b5140012210200c146007a028005405d40e00c0071401000504404201407040e60300800400108400c3c0526240015059680c01c0f41c420348071303422641120240450095031f52000d424a040c0c00c58407001c0310240c440c614400d010004003404291000d03611052000c0da2200c1c030484081c1d03107000280014054401403405055000b13403440d007000320704c071148280100240035205601803a0002006081600c4011120441810391926041071050300c0f5142c1c204000e540140108100c41c843d611303080c06195141c05c0743d040c6000403c0341c0860604101d03951000c581c103480e0903981c3c3d42d103084800c14041c0c81e42c1d490075000484041d00416101c0213158068401e9400f2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 971601483 1250 971600233 971600249
    0x3040614040b1906090c09150504082505130906110306030a03080a06180905010606140a1206090e0c0f030609030a200102120916030218130b09030d0f0501 68
    0x129150180180c0484002030f5070b1501441c4d5842000401440c6401a852882c0040d102c8050b441d0804d079503045050901d48201d801d005081004024444000030a0140d41ca101000c500410810202550040383d0544c001390f03000f00004044004200a60700c20320740d1030f00c41e0f003080201000c12070030f084242c0422107500303905030085185803010074090440d03141c1c491840c071760010b4800d84a070000401c000750703018150951980c0b240500304001d400d01c0f408010b8001d904014100c40003003032861006105013145c900c20030444048100e40420160400d02c05041584070502403002c40580180c1e41e0001038a144d88a12400c0640c40c10500700803c1d800d000d000f111014500d0100b00d0242034420030003a1524003a030002c3e0614a2205050030b02c00307050200c032402c0150a1505041d04d510b40f4081e290303440b554003075400700ca0410040e59400c001e074480c4203050b03540b442c203a610840e120f01c0d01c94412102812140e9400200480010040000c0000c000315600404c80c1582d940b68013000c45000b4090300c10 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 971602733 1250 971601483 971601503
    0x150806071b1e0204060504021b150f0711070506040306020a030b010314010920070515010e0c030a0e01090c0b0316030605031b060c030d0b100c031d010516080304061404 74
    0x20001e1880d45180382e628000382020030a1903440c00801c04036480114800f40e608481100301c050002c003809490f290b640c00d040c0324a2941812111b01d080d80101034800c0080c0600070b4540c860045007400000700800e40140015107841d030341e060480103076020f4580500024a04042c801e0301d980644034080c060f031003074902c0d00b10580c2001d00c0880101060405118441600c100304140841c081004001c114800c1002c0c054100030902d41d01342600060700040da241f8201030420099180039010340e84d0162080324041500500f0030b040b00e0040c101a14041e100110b11440818a01429001980141c1d0307100c000c81440404c4150440484206004a540c9500020558400d03d8444009803e4030f032401000c0d0f605d410404c90909140d640030521216180e074071001650f01a2800e583c2c0c0c0000c078401800c14842c074001d15640102884104840040b42e01e810300d0640840e07074800c034246c030b602044016540700d282c1003505110002e83c00c00c450850340d2a0a028208081020715500d40d4000d03580a04182d03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 971603983 1250 971602733 971602763
    0x2031c020a020601060e01030b041a091b0a0c0201090b1b07050319020607060b0d061b0503060f21120301080f030a23070206162001021906150806071b 66
    0x1203400c6c0e01c204c82e00c1d0416894007652143d0342e03075600c00e4144a0010701c03031144131302c0c07029000e000c9417843c010403181c056640d80240c1c03060058000201c40043e02c5516042050410720702c0162400785141d00015820600421040ba82c200c10a090400039a1038504071010103079100c2c00c056858404850701d10544100340007200060601e50090190144907600105032441c42900cc02c80e1401c004605451032900c0e8854406c2003468803100c0c03c14503445250151035450301c000400c200012002c0704502801354480203010400c0d11002280090741300c0750940b07469800c03545081e00541c1080c02904404c1c000d4855020354140d000040300c0060700c2c1c076150f480650b018000100707460b98a60600c2c0205980811800d00141d803000c00a00c0f841d0030b80c2c04181c20300c000a080c402e1180c2071b8030f0150340301e4036030005810503141e0300007403542c030501e01100710349074091454079007803015081009041d100c1500d031000200c0d1010001c5006803058513665a8658840c820206111000c04c0d1400042c1891281140c0340d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 971605233 1250 971603983 971603987
    0x6091b061917100f0e09011119080a020f03040f1548050a050706330b040b09030109021e03100207030914190609050109170303010e2502031c020a02060106 68
    0xaa07030b06c0a46003000007042003084c2402c09030b541c404541c0c42c011800c01000d40d03100c0c98200c01020380042400500314101170518818100314800039001074848030490803860704000c980000210543c4d442501880b02c02000104104850b06582220100b4141e15011b10060a502140042104401021512580846031060300c15034030061740c1d80c0401c0f004000803400f2038060302507161203010450210042505c811802281e8041c1c0c444100711904200104001c400d000d07030295410307280c81c0380b102c5a8885440c030000740117080d0400d000307401c08210f214900d0080c0b6181040d1820030800d03429900880c0e02b444a01040303118503400100401c0c80031109124080f02c08105083c00d08016200b480400d0407611010032014459119000252000109024659129103000024240020741c2c48030400c913043e10b1501c030700050246684200e2503200086001c3d048000e000010340d4825041c0e4000000090025201d51110220145c54120090400e021480d1807084543c0b00c40d00340d015010303076404c00c002 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 971606483 1250 971605233 971605259
    0x9030a05220807090b01030e0d0806010203160f021206101203110f010c181d0402013b101b0c09110408070806091b061917100f 56
    0x1911800004000540800d020720a040c081c10202d4024219980b50007018402d58011040d2103040504024510b040c0b41c400080600c403941e4039082441c2c0a82d103000c0100d00d140a203200910320299621080c6007404808400e84103858001c0c0d4030701d000b880400569035a07031081924109400c01903807008006c1a4203249020f0500c07880380c0341058440041480603031901c00c490f4074124072030350368003480195030b0b4100b0941080b0103800070562000c0d0346882c50041201c0300410041914402400018013160300c580c0700296096074400021144a0011040c1c203215051842d82100354100b12400c07101c5841c20080740f1160100c1956001e41d00c1014a09240c1d404409640c01c0302d071300030441c101103141700880c0a140040d0b00d000041070b80b40d80c5000040d5107040c001e607201500c0d64002c3c6003030011012000c642c1d4039020b6909007545500307040e480c0c0810194401c0b540d040312083c2d0b45e0300d1711a603559072020505805011070080c80009842c1c0080742503020449211f071701000035400328100050000916 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 971607733 1250 971606483 971606497
    0xc0314150a02030606120c0c150106020a1106040f0f09050c190c1b06020a05060a0509120a110105100504200a1d09070216060201020f1806091306170609030a05 70
    0x70f183c2c02c042901b28280805a03064074240c5d00a03002151101d40301c0010050348861602020b880005545003000194807422a510f010f000c007100a200e070525a00d0b4402290300902d0020804801c0715034540c400028144d580c014010402c8c144000304d400b451160003907404100845c4103009800481140c191022201550216085829500481c01d42031401986c1c0c0000c3c030303c0d50040e001c9d02581d4504281440c0c40202004441c500e803c0510a0020700096503000f02660020303420798a186980082e030340d02c0e1001075010915803d12042040b00c18001024070200c3d08151010f12007000080800e4a18070b400603445a12600e040c00710030206071003a08031901c5202d00303094642084400c039010402c550300c1104d100025911403185940c086501074100b0004101a200071410a02c04140800d0184501214610162401e900d1b2110f5507071a0411500300a90041500762002004181035000c8c0c01c485c0324640c0440450b105e00c01d110100450344503c190180e40285141c003100010a441e2500008 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 971608983 1250 971607733 971607739
    0xe0f01120f02030709060507050604060e0a06090507050109091a09070c080f03151206062106070806010e0d23010912020309031605030c040f0e0a0c0314150a020306 72
    0xc40180040112481100d501aa41c00c0000d65a46012140035008512170740c024001c000d0200078070b00c00b241012034265085580100301050300b5058100040c41c1a880d2000a480140340205030707001c20034005501d004440d000c0c2c0300d82c03401c01d0b9114801000c5401ca607a1440b401c1c9074221191400e03240c5030f1141c1e82d02c13028a00f0100d07681c0000d034407100c0c0c0e29048003801060a080001c240704088031418150b0070b060701c0444480cad20065000484a07201c4101034226405013441d65070084240a0a8035055148030448003126150316110038000c04600050301c2d0346000c511511404400740c20b040e01030cc00c0301500301c60407003060b10b0001c0d111419801ca0340e8200c0c150395030701e104150010380c551009450194042e0300540e19403070b2030f008250419004203240780d4952641d00c1c0c20041502c0110350102828803c9500040b43d51840c007801000c1c180c840620360007400303100c6842040081c0d000980d000d1324003440c1d000b0800d0380d0010032180c1d01c02032405540c040703680c100e00048104030a030b001140d1048010b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 971610233 1250 971608983 971608997
    0x3030d0b030f070e0406061406040317071505040b0c0f040e1b0307170a0513020907020c15040306060906060206011a040308070c0905060d02100f09050607060c0f020a02010e0f01 78
    0x904207060400c0c034140c0002201340c06803000c0c0010f00c60a400303650042c000c422840c0180c1d03040e80c0b0020341b1074801e41c440101002d5080e201030703c2421425007551240c580014000d1000e202d40c00d40c0c8002030900703d5080360b0702848040803c0c00346506000703441c40301b9200306100e4605404c110700d81182150040c0000c114200030704140203080c25120146014001c0b50b11081008098138401e000120801001082a145002c3c10800d40c2c2841003c082c1c601c50301070f2703080e0205807103441e0202e0801100e81d2581d60001404181c420490304a400200200d9028000c1003001e2600c901c01d020a84249200d68401640f01c03c00611180c2c3c8220b480b40400c0540480302d42c03910782d4a0b940d080003508200000d41d4101c0600204115403d43d50180d10361007002261b029428049640c00113010105090030b00d010054014031945549000d1000d10001c2c00c00140202e850f5011450050060111004850009650b102100600700d0000504104031a4161103c0400e031203a881070105408070400d038030b4108004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 971611483 1250 971610233 971610253
    0x10021b0f1501051234060e0a030b0c090406080309130b090c0a1101060b0d0c0e1012090b090303040201020c1503011203050409021b120a080f0c0f03180105010605040503030d0b03 78
    0x5503080c0c040307103850414254908a031404e00407031701400c00e5070040040c810640c2c0414401c1c2d8a9800f85401d813170744625040c0702500c1e24080d0b11b1072070288000c20760b00720b40750500106515200001400054000319400400301842011480588a540c001107400c400000081818043c0301d03c0940708515061a007003c207119800100c2d42518078031b40c4090351454001645c14043c4089000320403921580e81030206009248801085801e600b03814000d0800192101986a0f401603801080180740c01c0060403901e030a02c10742c85a00c951007602c3c02c9004d031090401d140d150303003844140000c24a803105122400c50b880c002c928101401c280008800300001080042555242032020b80320700044200344015a0121200310f9142802480c0086a03802090056180540d0f200c1c0c40c2d19030104c400c20b5000d069489403910200c80d4014407002d204240b9001c801c000456001e50024181c40e501103000380480e90383c4e02c106503200e1040e03015454064000b0000d10041c002590801c150031803000d400c40e885144 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 971612733 1250 971611483 971611513
    0xf030a0519020102101e0911060a031a1903031103070b040506040506010806100326070b09070b070b070c140d391410021b0f15010512 59
    0x504500000181c40c1041e0140d040d0350741000081005c102122017088110064900310748011520b040d048000c03915204030100300b1003400d801d002c0368003028107501e40310311141c1c9018001d003e821044220188488074200194075010b100d404101d0080051795030f0641c00c680707040300c0c0000d40040d042428402003003440d000541c2e1f03804d00c80c400c6014001908040c203041c07034010f0502c081a03119120550010b814010a6011106800d046a90000e01c060060180c01e42c1e00e0401c0b1104400c624070042c010680700c083c4404080b809104000395400e407110151603580110450196a20160003140840005071010f40600f405154a5000e115a4040c07240c84135919890300c80324000303440020741104241d004041000743d0120440c0c020204001550034982401d20000300d00b1400034101100810040c002d41d40184000042100d95900540d9070b80591083c0f210500503602c19502d20b48902c0d440c0d243d00c16004500c09850f1810828008890303443c00b0304014801c55035a00801190060424181c2103903 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 971613983 1250 971612733 971612743
    0x20901060f0e0306310b07180305060901021902120a0e190b0a17010308162102070e01060c150e120304050c1002071d0a020903031612110c0f030a05 65
    0x1000081580b185c0d005140f00e692540c409205102c1e4070400f8004001c8002145c28080741d03800304c581d20300000700c0200c00c096940c6074507150340082c1c828001c900c1840910901034005104440161200da5058081d0580403607580c1f506a40305204d030ba009002e0484d800b0300c07594011209010013824a41a041300c1d8a10100b0080c0660000c41044000541c01a03825004080306180d51590060115203601d03644817490b440c4602c0010380d2890061107841010040303124800c1311030803041d481601c4035550500c00a540c42a4501601801a0b00d80700002910351242030b40000b031307951140040704098450001d500150250070000421030055040c000603000114028500c42c0f0f0081c40208051102c0b1403d009903a240450400c045400041c0d00784850030900b5058038002c00b070740ca40c03100e840c0e0f60006048000e0041011090723241c04005032803400c20501d000480c55540c0034034403800581011000c25030760101c074210503034440e402c0454040719614005c441d01d010f0070303006400e442034038110f56104c074148 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 971615233 1250 971613983 971613991
    0x330160614010f1e0504020f04080604050604020102060a0e0c3c0a06050405060f030402010e0901061115010f0b0306030c090c0c07091e1e1e0b030a020901060f0e0306 73
    0xc8154001000b49107010203507100204000e20300c951300d19030402c4e19520130400c40d00842c1c2c0500d40005c1d543d015405100e0880c1c00804c2070030251035041c1094602181ca030007044d14107a00611034000462070043d0315225098040094000800380c07880400c3c2402031100c0c00c05da80c121036400090101d00142e08030011b459060600444140542404030304100300e841c62078103c281001002d0006000360b8480e1001c9841d881c810300c4900b41c4a80c0c0314401250384d086034101c416088100c08000245443c0c100303028041403194030080c1d5204031030414003526841c10922034460340142c0031008000d1004000000c541200c005002d4036121280000840d416560a44800140300400a1030308084c81c41400042c003e04407a80c814402e041040228040301d10181001000742e40c1d03540720b40d415000c21001c01c0b1401e09040c000c1800b0810100a04840e07e00c0c410100c41a060706154075401c041c40c000c01d5a001055009240d24020b0b42403880481f882d11007061a0804d0000c1c10a0020099500304071407841 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 971616483 1250 971615233 971615261
    0x30314010f03141f09050106120203060c0d1b050a0305090105060a0519050303070305120f060a0302060a0c0b040308070e220b032109211011090a0f0503301606 70
    0x30717555a030310300a801c40c0e0255110341201044214841c0040e0b070041141604012918244c94a07001c0c0042024000c0ca44143c60010590741004201d51664020000d8403280b9002d40301002150350f42d8581909070b07232003103842c6984180303d040c050000745004004420550354152140e24115240c0e4003003032969000400640101d100480c5d66039822000000c030070740c0300d400d08000f0a03c5080c19804903540020a00009200c0c0300c01061001c80c692164000600f00b82d000000d031112402c1500f00a8802c032802d0b00c0750b4001810358880c417801400d00c640f0740150080c3c5040308c20900c01c40c1e00310000051142a038810380c940180040c980420742142514001d154a1030712160f5640b2002082144a019580d2020485400840020003118003c01c100c03031011070301c0e0340c042245132010504100300e1140a010607404042480081909924618244143c2e0015003c0b1070107401c5001c09682d14541c2a0080c1c80121041401110180d505401515003c0e100e080034000d15581651a6000d950300140b119407 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 971617733 1250 971616483 971616491
    0x909091006080d0e06070609080304030908060105042a021204091e0b0609152512020f07030f17070b070806010504150c020a030206030405030403030314010f03141f 72
    0x112080300d2180c04010003a1100501c0e403180c0c800c402030440c401e020380903440340b01c020031038805000701c1d50800c102030350340402c5243d981d00e414500900b5180f40c5000301c1c005480b0f25800400c042c1800d104455000130100800c2884038081160710805421210181046006441800040c07002e42d8010700041c0c61001c40c089280d1640440c0030710001401f00d412800c0d2400c0841c0c094050311542c084540050099400c0700929885c948800c409204281d07000c100390342200424042d000001d0b08100c10948910400345c541894282d0880c1d42c4c4249040c540d9043d00138020820001d41c8260726100d40c0c1d4814102001b01c1d110b4104c404c051a08000015034a08894400708008180c0c01190b241d40a202420850300b06400e0942510742e8210b100320010a0200c5407150405565800b50031f04001d5134000c2007165a8a0a46009526034000d480110040b81c1486503511010204000060586c0c240e042c4071448246191105204801c580d00d149081c0c0c01401c40080b400d0980310004e10300a002010042 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 971618983 1250 971617733 971617753
    0x1507050606030114010b0c0c12010c09050a0303080f130f060204030318030302060a1d1905060a0504050a02010c0303020c10051f031e05070f030302060604240e0c090909 74
    0x341030403030080c4210302c42c0e40751014000ca0210040030b840d0565038007202041c1c03155804403043d031615443e00b1041d64030141d2600b0303118103400150001d10a6503060340d40e00b50206d607603c0034800e0701c2c042d07400b00402081000300068100c01020312240e0781322060482003442441e4507101d00d00e812210402c240c0740c054000406200307058200c440b08410040c486144141c02d451510001e45400015080d8043c10717489440c103900401c3da020705644803014105c00d0760b00591001545001610740f43c0402c8405000c1c900014240483c02d12403188a541c2000c05400d500380f07158011108110021012001e00d03500b0b1108003038038241001a180381d501d0ba50b000003403d040641541041c0803860403041c1010312007200500014207103506072805084a240d442c1440e0980d8a0024140401500503000700c070002c41c400030a01da40069582c2c000e02c02039800304102141c40059001c0389511102c0c1c0c9070760000307001c03007040810f0040701c40d140d101c0c040c540c6035400c0848840c00134401b0b00b41981c0190b8144d200030b81d46 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 971620233 1250 971618983 971618993
    0xc05070c080d080f0a15081507020a26070b0a09060e0111070b04020f0d110f181306020f0c03030103020f0f010c030503070c0c0605030714030705041406091507 70
    0x10030241c519100181003a1030340600092072808002c049021102c12080403500e80740c0150005040f1480e1282441402c40e221804c140e41ca1400544500d140950000403580700c40c00866200012a0459902e001050b4003582490007104c1c40300d050301400d001001807501042d50800c989010788400f25001ca41045182800c0c2c080e515402d5030710440b645803404030900401c40c4011a801c0d0340c0d01c256a4180c0d641c5500008104181c440f001d16042080707850440100494020707041012001103450002400d112002e00c0300042d140074429040c0e07610b14004c00d1400d10501440d44440d8030451000d440c0007100315049800e1780181c520004107610100040c0f0440c90404405881d0319003c2d103669a071340c44a00002820b90500d180054180034000000c1908540300e40c1c48591750507000864107490985e2030b07070f00030f120394012540b15001031007100d03807110703034014520880740680c000340d9030541031605040100d00001c024204071680050704029900940d01c4801c1140c0085070b550070b806890300e0b254101307 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 971621483 1250 971620233 971620253
    0x1831020f010815270c0403060c1404090f09060c020c090604021905070602070501022106010c05030405040b0112050109060f0e0108060a0e0f010e030901030609050108060601031e0c0507 81
    0x6060141a008001180200c00301e241c0d50048103c81401e0b1104d030740403400d601500c4c2c404148400704084410000030261100040c021240f02c0e00b41081030030200001244c8a031601440480d0344c040402c410420a085078018035000350741c41c280003c81e04c4075940c0d03000443e05904400001b681180c0c016034054a042c0c055158440d5044c2c0c5c0c1940380c510b414078410312002c1e0940b24402448404200741080c00569415916969071160085503500c00600c609860100000300750138000020798000b030400e510540c010107240b036000004500306400c100400002d00200d040e850304000244041003030120320380c000d481c0242881a070014405003068244084448547c003c03441801c0c5000041044542c000b481e280e1146640030300080032441454198200f802503246000d02e9070030055001d40c503443c003000070152248242c8040100f540e0351242c1c0070542c1d901344121140354200c2000902154029000302180903807801130140307001c0b9516080021944140480400504003248e08010031258480b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 971622733 1250 971621483 971621509
    0x14040b1008010212240d0b0703061a07080a0207031703040b0601030b0d0b0606070602030103120f1103041401050d02071112010902031c020703120305090106051e041505031209090f0402183102 84
    0x58bc034611400a44a132070a0340b0529a00406200000401005580c03081c48200c0165600c848150782c0c602500a40d0741203900180d9068030903c580c07001252881d030003485114a113180140150701c040090340c680802e0220000c0082e0340000c0c042040800080162004602071440780c100398828500072440284483c409802000a1140d0300c1d0030401d00d414008113403003ca602e401840e0704000604401200c1d50701408011780c242ca40003081010811810900f2074012050950728900c8100202c0ba485080e900906030194140d045000c0c420802040b4007946c2e07a45403440d0045800e8540d07203585184001c00100c000400003075962050000d1110207001360801400115145c554160301c2c0020685502080401640701c1c03903039200c1206070032007003100d540024040107065654a240c003842c0150307180d1081c4811841905460005036110340c02c1e08481c0d00642e00600b203120604190b0051602c5000b001d00140550703190851505850103000051a2201c5915010a1f01407a264414403000445000c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 971623983 1250 971622733 971622749
    0x1110f0d05010e040203060115090b0f0a0e060310030336171c18051504090b040515210706090320011b0614040b1008010212240d0b070306 61
    0xf018840942d03070014065040d240220540c480d01922600291480f0340164444030b001381010a1180c2c03000130343d9018211070880e9840d1071051080000810480e031108440d0f100f0454460501807011a10400607000302a03d90b1075003903030201600a440e1034000d540c03d40b10080c0000c20720240890340c01003425a941080d10740050820b121200d0008000c980c44080030003c01c044001000785c1c6d07140c8100c08500505014203900340c180f8200340c149069901500a000c01503092400c186d0315428203100c0c10384070380214040c2010f150303603500400904d012250301c0100c40e8116940034191201003400380070300501d80c98541002103403842c64000c0309044601c0204000403008102c2a0080e600b21001c02c0304040301d80d0016040501d1403a02d2001000c017100c602c1c810002060811080100040d03103039010307103c2c0c500911041c43d9030f200c1c1c4900343d1059182a1f5501602c00010442c0100e500e4520500d00d03011140d4951450b0b007890109034203600c0309600b522803200e0340702800380c529010b02c60f40018060407 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 971625233 1250 971623983 971624009
    0x9120315010e011704061b05070807120908060903180d0b0f0901200711030304080307020f0d0b090a12140f070303060e070f03051e0f070201110f0d0501 67
    0x1100041944040c00300000341031044050702000240e110705402c2500548804061050341001d04020005003407860880b28010303c07061655807003d016030151740105a102c1e4a080ca00700141e0b071607030711007546211224144240b5941c0444da07040c0a10806200b4240349000f19103420010b002d580012205500c00d40c080c0d4004110280840d00a21780300341e000e0000030310084c040d01c52102a5006003c01d500d2585050004041810340205242c010805980035a42d03d00340781c0440800c00d5242e208900c5200406c4e4002c011000040c00d003c0da4642903a01d00419103085581c19031900c0282140444c0d8040107501f201507070504001c0d4a03030398403034822880d03d80419038801d030b04821401ca11030848445a4000041240390815100380c0200d0003514821189111500f03000c000500f607040c0c00c40c4104046401d180000340e150b0300d0007841d140d0360001c02004001135100c0107001300a218000c1c01c4c840c119500c40d1556185902c02900625103a0400e04400359a40b413010b19070303802c8030b4060300001100040 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 971626483 1250 971625233 971625241
    0x605030403231e130303110c0a151115090a02011715010804061d070906061b020f12010c09051e010509010503221415091902030c0402040e091203 64
    0x3082c800d85a0003441c07041071010310341c5035804030002402000c2c0f41d4600300d5020640401090380c0542c220700b004410404440325510040300f0004002c86500603901208a00c00d255081c261044c1004407150b0b003c00b0555110f008141ca25407001d182c112402000c030b51096080e4021564411859840300c10303165400e0307000e4200389040c1c00c2e200b410400600d040180c031501280030310050340d001c1ca075440c50b00b12804000c0340380d1400c481d880d441c4520507003c010380b0b4004001045030040d0883c03280f08580d540204100b512682c200803000351020040c030b80003216620740d800450024803441e46a00c0d40e64450344013091400003080b042b20324075080c80c84444c40e10800510140d07000001d4849400e030908029480c2c3d0b41c0c00142c0ba0f040301540d001c40c1e04840340b5510207424400000040c4000c81ca14a068414145070000419102c88095504030300710b621005c11440b004010000c1d4016840c030040968004030000300004040c0c0e00140c00000e81d2050320002c0c00f840d108100206001c408032201c2c55070540c64 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 971627733 1250 971626483 971626547
    0x12060307050310090215070f02180609060d081e0c0d17011a0f030403030b010f110607030c050405030a1505011e091104090e010c03060506091f03090c0605030403 71
    0x201100c3d040d001c150b111042c4000b19900c4580d5464800c481000d51520740c0154200105010340c00401a0701448100c9005800c0380c1c503c81c45c4a2107098050010100c54503190280a14019080002e42d8800300c203004c0500c0106040081040e0200c0e8024041d44550503806140d0800d0881d012010a0000400554a04604003c5d400d41101c0c24102c074508024100000b90280d0301c034400350b52440b8000002048109034050344607a2142100ba61a03610258000b8800c0d40e14100307400d010030007584020f000640051194010300c4000c031035403038034900b040e6440004c81e2404d03025040c11150000703000040c01d0241040d10a8500500f40c6481c0201c100092003c40c0481c02c916008061005071a030342241c2c14092418104c0f002130000400c1041242c0000180900914649540000103801e12070005400d1400e1010b031051060014035040c081300e91f5800305c01000454000f05e004ac55163b064980108600d01c0110005000f1034481c580e89240078a0001d1480114949070b41c1e0b06c2110840c0c034503500e5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 971628983 1250 971627733 971627743
    0x60d0f2006071a04020a0f09050106090f031a0603070f030b06040f050105060304060b0103140c0c010b040501051302030a1d0307060c1b020f0406051e040501080118031d060f120603070503 82
    0x444003880604240c1c407980046801b8040eaa04240f611407071207407001480315203550205040750426502c41c075a0030744880e140035840d0410b120252101004403100312022103840c03081600608002c00721410180c0c0c446261349664150341c07069a00407405001c02846003401e00440740c101c000c3d0320040020398104000551140005080544101c0e9038000c40001d5034000e0340f026040c84045a4410442d18024158200310350005442140719400c0c08407009940c2000c2c06070a041c7d1f200103001684400b200c61066000b900700030184212241c55043d00c84003414020070302c60b602c2c600c44000c6c41c1d803001982808000e407858503c1d61010400f414800c001c10040403821503010a50455a01c140e240b1030100007405405503420031540b00e2800381c5034140100000220641701601682d0500c9680c0e41c0e540d00390300701c5100303003050620342e10350b00401000248034140c1c0a0281100803129000c4036508070100d0910341107a0a8800324040004180c440e0f40a00010150b11400c100d00070001d05061001007910b517 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 971630233 1250 971628983 971629013
    0x4140412110f010f05061e1518060705060603070e010e040605250e03101109120a060c08041e0f03051c0234080909060d0f200607 57
    0x1000200c1c56041100a1194844152215000b8080e520103800c03d20024074040e41c0c0e481c0f080806808601080300195454000440010002c980d0900e0798044581280d001044407510800134034005c050b599141c1019011503030007100103058919044091501d0300710643c00001c9144071000040150007600c01c00154419030000011403a0344a400c4580a42070a8154003840303503070b400c00185081c1d64000c16110002204600701c030605040681c4400c01c0328201c0e00032941d900801c000701e19031400d024107601c50307420500301120105401c40c1c80d44811034040c018003800242181041c0001d01c0000e691200340000c144490280c04403a0b96120a02c160304404020305100d404100d000c00544804032010710003e28150130b41d0769120403610700320030200350400380d942103015041c03144c004107203480e4244240354840303075aa1610405030104542d08900915059004603c9220080094203100c1c58000862046200440760b0920000f44c0284240c84100c00f0700485052102c0008208100c01c03400e88 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 971631483 1250 971630233 971630237
    0xc1a0c0a0f02040b0438060d0b060903120403020a0b12041103010e2e0e0706052a010b120619090807020301060321030b0a1e080105070203070204140412 67
    0x141c001d50b840414003900b0b01c00d030758a5000780350440c0c1851007820090424040d030002100465400810100122410b01d084905900b001c418004544011803c0e8820000070f00300030503460030b01441c01c00007894156140411740590390301040403c01c50074030f5808030340544100050719080c609032076000040d2400080000e03203054002550422a0349082d44020902c00010040d9400220b1440301c024424a16841d0510550100c4040003d01c02144c402c1d0241c0c42c0e50301c405082514030b0603a08903010742141e000c5641c03940c41443d03900c01c2011610300c040c60321500e4400214140d40340400b0000041c1d10350103040619082070381000001d42401400041200b88550005004a01d0741451000381c018260025003541c40d1400200c2408030f000c0380780400300404801640103480d11001102552000654203400441110080c070402000b4040700e50b0b2100c1403040c11134195650342c042400d6035010303180c40e405608000b0b0420194141400380780070559030010754114600f069a541103480c2d02c1c0b5459401 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 971632733 1250 971631483 971631503
    0x606110f0c0d0816020a08010b0a05100f050705010612210e060318491e05160605060a0b0c0c01030c17040c150f27120c1a0c0a 56
    0x311030700015a00d009494015080406e519100ca40c0c0c18001d180b000703041072149250f50300000302032618680740c12480c00c030707a5943d09100d000004243c40a42007610100c85030754981ca8040303818103050055201c618055002c4146207070100f0046a81418003031080020040c01c0c0020700369540b1214200c0750883e1050480440d0003516099540c20f008545411a28601045d12105d5000c00800e40e000c000003044441111214003039600c001d06001c04040340400700b03084005000140e10940021182902c550401c1c0c1d281c14452104400084403180084490304d076102d0078800359040800030300000c0e11030718002d185000c515840c100c0c1d892042414484c10180c58042e000303081da2142c9586440544840410342090606291110140d030060143210300d6540c40c800d0001e04031344500342041044659407108000c1c01101081c0f00c580400c1c81c2c03101000d0900103180024045211070f0304002c424014002482c1c035500707008400711400440340d014020a402885151950030000c25001c0440d43c1c0002544 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 971633983 1250 971632733 971632747
    0x509151f0201140a06030c0b0304050604080304020d02100801060801150e0603040516030f02032109010c02061e0d0c2105060d0206180301050705040f0323010606110f0c0d08 76
    0x2400740c42c00e003c41c21030420f00c0c0c106004100409030000360650340301d1b503600c1d0300301604d070a280c0d0194042202d000e00320303901001c04180031441312401560440c2c000b40508125a9544e00070515218442805400044180e00100603081d401440a409000142d1000000400451006100c0d5148185092041c0700000119080060800100303d00c1c01c0e61010228602e940c03810155032242c0008410b81c00713401440541c528000702d90741c0034210203030b54022150400350307035900442c0d9014075020201e800a03802c004004c80036000002c56031282441c9504159103019259141050310b0b0b068916000b07000561104420050f003207905150340d9240d80900040316070354000010045885d100010303410900001d4660003400f0001aa0040399900b07800900c4251640801101d1a100314802c08101c0d012041f400e100058012a498210780300403074004c460400a5010301d404c50b80c49502c20b002090000b20443c2e00f6880c00d006041e00380600d500070348041d03100329000c103a480d00341c50402408994002010 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 971635233 1250 971633983 971633987
    0x71b140d15060f0b0a030c020a0b01030809040e030c071403070602031209070302150904050f10210c27140f09010207140d0e03240403110a0c0509151f 66
    0x1c0040a640c0b1440c443c40d640c8001c00f04166001e400b0510004c0e0410800d010010700015030b0b1007101d9070100748409142e1031a1910801c9400854030168001d032284000307081c0e03040400107041d0540140c00605121840c1656901c40c15804a1505019410003c1d003000391a8000c001c1d02c4030008110412051903031840c048500382001e80d040251300210002d04100000ca9a402501203035a041d1401c01594440c017419041c0d441085420941c01210340e1001d00041c10003a0186a090080c0900c0303440403420341e5511040c800d0640c014000c2c1c51090200105041a03580078206500d803c0b40080108005029101c0c6c940f0710000c007404020350085020504d40c58095049407182508414034030051014182c240307440c5c0403080340c41e00c0011a154120005841d0104101c00c102c1c00100916441e01380343c482c140c1a10703100034010340a00a0032003070369000e184d081c003001501502c1100006405400d020820502c102c003d0009400c02400b07030313a840c1c85519080c05120450070003c0c000c1001c00440c20013 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 971636483 1250 971635233 971635241
    0xc17151c03021f0504210512150306010501050c15070c0f0302061902041d0a090c03030c02010f0306030f0b0613290d020306070c080f071b140d15 64
    0x1080c0c940401141a014550302080f40e050461441c42c0241c2801c020400d0407050700c1c0d0540700030b040c0010341900c150402c4c59444404444d07520300e0801e603003040d150042220580030110341140411412543c100315518007440f5460240800b420164107201005c041584d4030401c200ba100c51070750400c0d01060105018280e589007880d03011f0003420000076103141c001d4580d481943e03400c050900340c02054030181e13464003c3e10705640004143c200b004c0014080348440d164060301415a0641c0c560801c00429210125040030f0341c0a5160380d4038211042c03000401c4080340c40c880d401014901001440042e0341c1c045910201508128a00d4031074079444001014290405c0c2010f040c18a40600e6660141c481c504801450564401c2e207404814030a060020381621548025811341089000031115800351440c203804a020300b0042e03080515a568052441d84000c0d4142e07001304000700507500840c038507006d100103000c10b541046000380580011a5403900c405800a1944107102c40070075401d40e60360300c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 971637733 1250 971636483 971636509
    0x70507090f020d0e0d050d020315040c08010617041101051803030d060e0a02032a070501230615091219080a020607050a0903021201021303150c1715 65
    0x104260711110010030000e510254064240504200000100000c041450040703406075866840c40c0c94a4214480002d50004103124070101180302e44821a8859200e80000c000441e03c5682665041c0207001c2d010085e0124142ca078040f06000704400100b1180080081078000c6c28915182c0c0c4461a859800e00e03206028141c03d440045100701005007990001d2044642c1191885025155106038405903c01110895031661540980c00c04d200010440e5030001c207540c0070361600701401941d0b21401d40e0800744858110182c4020b2800c0005501e03011140c00c00c808680d00c10310304406070481d039094081d0f00f0702c0034410b544882e15441642005d2160b07a0104021481e070b030301d107254180740514440e0003000110380103100d420b000031280350148085900c850781c541c44010b041461355081010340f2510062203a9195000d00440042295040c0d401001c2c5201e8801d503644003045104140880706500c01c040304100c4102d49910140c7c42c04c00241c0c0e000082481c0c3c030306500c4540e0000c2514415058 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 971638983 1250 971637733 971637749
    0xf05090a02090d080a0e030307080a08090f1014090d080703020a03020d14011a04210204142802040b091201140a020d0c080c03160905060a0c0203070501020a0c0b070507 74
    0x1043c100100411400105005103094461520380b038008003e040d41c902491074003c02440042000c1580c090150390322590001c80c030400c035010101420b298030304014242c1c20054259440b280101e440c080f8190341b07554403911845c024600c50b440203078018031480002d00401d06043e03002403020f0b8a940300b90100c0d103110480c2a0248035400c820300d10000042803d1050054a9030f030304c5462116400301d10b00f05d50803122100e00090706040e45580303d205200031054105d1348195689500d0030f040c3c40500545220321110543e410b49280c0a8002c0300c1c4000700c2c610000c04451041006201403201c0c5010303140050800c0e034090218051f8091a00d0040040300304901181d07210705c00300600480ba0790010103842c607a40301c0500800861a00c181c80b100c2003500d40c1e02c4c0f518424400144026040707025080b584d441441d03d058980e0381e0308081500c03a4003010455002490100c01c00d400d6081c1084850001c080a10003044400401e07101d0b490004510702603000e10303440003d01041800000c11514000e40050 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 971640233 1250 971638983 971638999
    0x100b03012301030507060e03030301090b01020313030515100620070b030c03041505060a23040608030909090309030303010605070c0f120209131509020109031703041505010f05090a0209 81
    0x10a80800c00c0c40c1c091000316100d1040c2e40c00030540c10f211301c050360b0803640054011030960742007001c1c1074040c004451016045100500c04400d452070031404032030066000700d025107001c3d1603404a0b5008408010094010400c2c044400c211040d84254442480300741d454080000d040020841410500359500140101c000402401124103a1074000c40c01188210300e02c0000b02e102c101420140c1d40c0c110380003036000e0700740f0344208003031655080404062240114a05039170308110000034100c1d14290055280340d0b0000ca143c40440c10700030880c0c0d4110001c40300440c1403070440710000383e4a03c41405114108003001c125a82086181c044850107025110b118a9409854103c6240080803002c01a4402d138034030310100b02e068001d588220902a00b250607a40c0b01c480d132002000107080d0b4007808070704120302c0403400800f040c4605100055402d01a00f10351b070301e08203414a00000d1010120208040f85000c0042040020200c1c141085401c1600c10388a2039503640d400e14002d0082c0a180d03a000040307 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 971641483 1250 971640233 971640281
    0x1406211e06012402060c2b0209040c0c020f01051b0601080105041a07020d110c090c0a270e070504120303060611030f040b03180a051c0e03100b0301 65
    0x404100c40d81a1000603801240d040280d2100b140410043d00c02c00d00582c101d6001b0400e40119070000b4000075018041141c0900c49040030014140071801310f003c80c282d0701094594140c43c25004615140405142a12a0700b055800040110414002c018140070000501502e034a213482c014100000014050b110305607560262140a40b03c225002c5516010481c00c0d03c0303c11003e10142030040c07807141c0c001c00d042c1d0004034058032541800d00304250385102d00800e9081c40d0341e8410100e03201c0d502c00c1035101d440d0012007002620100c00b80d0040b5010412940342c482445a0900d40082103440300000c058203030f01c801c18207032041d106540100c01804600ba0400c41070540581000d01140c1803552000306031070701044440d89074012188804030803141040208152109600a103070005416464840c0301071004070780fa407034031000c080111901c2c0c020180c2c04204a1f80315401644054141c01d000120844540c002070b140c40399803500711181580c80300880e04c01d8500b54090107420340641060030007000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 971642733 1250 971641483 971641543
    0x90503070e130b010306050610080730060b0714030702010804030509040b090103110a08120d0915020324030307030c0204051302060d1a0a0503150a24030303140621 72
    0x108540080c0109c11300204541c416200301e000034030507a01071b5101e1402d0504c0a004195020386072a00750048699041198030340d0940d0700c1003000070a552004941e0315800b500d082c08000543c0c040e61384d240e4000740080307000343c1d03080031420390301540c5403a000b030340e9141c030100140c001c228031020b060f045265440088100140d441e121948100204e8610341c02c1603480161540c3c5150705800c0050040c81403000452540d981e03040820028410a114100e6803c00c00000c0d0403a04100c03445030003601c1c0a6a4400da441d0b00d500d40c02e060301d005801030361a1141c00e40340130f400d5406c2440001d0083d561000007540e00582071070448159079006161aa44142d404490000740c10782d8025010309104031030942c0c5142c079141880e08102c07500980601b1100106003900214001d00030018000b040e22a0b00071180c448050103c200121010401d500c1002c0c15814018125503c0228280443c5410003e210b140d91f94001d4481940c82c0e0380340d01d0102428050100740c1030910035100c2c1c40703400d032180e0b01d0341c5d010384 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 971643983 1250 971642733 971642741
    0x10c0e090c190f020613111c3302040b0f03060d050f030903150906010611070803030a0f0c080f0a0c170f0a0509031303030503360d090503070e130b010306 68
    0x3030f16642100c419403201650700062400d0010010a10f050a00c1c03203c41078100144003401500d44c0510389481401c9584500d0160300d009040f001d107407603c224480300c4064610500340c0c040c803200d483c00c604042c10141c5041d035900c104104144141d2001c0300140c2140d40b0f00e180314801c83d03404019a007000700c021200607502d400c5101e0030b070310038060000122048024401e50174490031001008007403d910b0103800762500a15070007020030700e0140540105019000300b0080d4014448080700040720096505000211082490410100407200061224000c40c800c002c0790007004240d00012040301c44041540d1030458145c0d81803094464000304483c1400c401081c0d4403a440c0ea0400b40403036a039005509440384078081c80a510760090281c1400440e11035405168481c00314000443c07011070340b2100e084d0310302c1c084146c0082c0b407044080317600d4540c1c0300340907104400c0824246801c1145c14170b00000c1d00d5403150700400c0c0d141d111b203a000070211201c000910241c40d0b00800210000d50310780c24000064 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 971645233 1250 971643983 971644007
    0x2012c0d0503090d08040804170c1f0909020c0a0c0f032618010e0a0914010b04050d060902010e060403060903020c09160309050c061b070506030601050307080709090614040509010c0e090c19 83
    0x50301d440a2f0410010800c8840324248000c10350b01c1040c824200801d08000b1341018449107100d1107030104540003d1580d0a80300d02408802030010312a91031880c0c04610408e00d041c6d106600604014045070160024098510880f44002d010030a686854012203041c041e6002c12544005102030000b2101015440000e41c3c0503811203808075a078071814071070000e204501c84d803900049040e44400c08a4403590140440e24070501d000700800e089100010201d0700103070002d071801c6a40d1080030003010380410a00c80e10384025551400c0038600610326480d0781010b82451420305031a040c2200c20002c0a001c10b1110000080c0200c0d02c1e041d291840c1ca00c003da41051002a600c14003a01043c1c91400a042d0b80c441e81059559a14503903e0320402c4417906e030040c00c160300740305d46550046106a6107000d0390001e01106910341e28038810380010403040d07c00c064460750340c592500302c00761104c40e07026429200507001910652295104c490352081c60303100d07054010407090511101c0c25103c65000300d000341d074 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 971646483 1250 971645233 971645239
    0xe01021f0c120501050f09180307030f030f05060108012c010609030b0a02040b2502030a0809010311030609070f020f0f010501090c080609041202012c0d0503090d08040804170c 77
    0xaa5920b00c48039004641d800e010300c60b07004010142108481c40c2650b0090342c040700712a403c17003d011307040a25500d150004841100031a601da8608480d0b103502d441901d00c4200c03107010501c00350401d02c0011784286010b0080165104880800c2c0c10350b010260480e508940303002c117642c2c15940c0d64200003020b0b0001c5010449510701540041240719000d4020b450607598042c03401403514090840030000b0820401c040c014088a5012480159130188001d02c2032600481e43d07990383ea030f805c000043c05c8a00c50810503e03c5181071041c072189407100c081182e4400480d00b005a002c407242c2d00c046c0c2c900103205090324858802c0c0000804c2c0502c1c19081079040341d000d00000d0102100014050b0b4401c182101d0b12a04500d40100041c04a90b030403442960340102c030f0000003008090501c2141c000d46000003501807250700c51000460844040014412005092811600350305000c0562030301c901000502c14100901000882e0a105444045034000c0849913401044825480e07031043d1544141d40401784 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 971647733 1250 971646483 971646497
    0x90d0803010329071b0213060801050a020703021e0111030106120617030a0807030f020c0c03070602060408030f0405031239120c0403050a1401050903090904030e01021f0c 75
    0x10b41c00c01c280d0415841c01d10004000d00c01680d43c01300807281100380c05864019a262910f5010250701c9500c04003040780071540b07001c5000c5091582003070039035001511980c5110301c100940c0000c01d50104080142c0001d105009400b01d501640030f41c054184900c11285000f0000000221030f90040102c020b40050607030107000d8650764032090f00841d40e488001d000650002c1251b904801d108449090b4004403a090001d00481c80d4100c01e004c0b6005120075200d80c2d440001c0070520f0303140070040b200c000c01c4203200900d840d103899a6518118080034003000b0440075084003041c200b0a00f401541e07480d0700b41140c0c04017145400408115400321000c0c8581c44c0c0740078040c0088020442c038a01507004d17055800204d1804208a101400d2080000c0003910021814800070002034414000c103225140907007200000f04220003490343c00c549010f880b9001c2c0d81d01c00c0051021071f44500e100c0a038856014104441031586400c0143d0509418000c1d80700402c0140c644408520680d0740100100344041e070f6409 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 971648983 1250 971647733 971647763
    0xd02061c0b030a0c05040e0f060c0408070b0f120c07020315060f090702120a1215060206250507030536030708060f0402010c05010f0b04230601110102090d08030103 72
    0x55203c0b420028080c206000b0308500780040e08081d000000004070000440c0c490410090744141044030544102e001004001030030000c3c040100325070340140c280c40b00c0c2a45000d400e03201c481e2061241c10b0070080b03446520f40c00070f04490740d082e0a5518064026040d02c031108404c514482c07a480e400ca460350303c00e81c6044c165980350304000300d00d40e12402440d0000c086520841c076241c0c0c410340042071b540782046103001c085666000759000b0310107245c0d00e610350b91161904009020b070a08034018100c030154114401c540e00c28021405140d112038401d8101180c0d40e80700d5090031561886820090310f010307101c1801481002070003880503164248150030035184a20800e04242c0c48401a1086070011f5121001081c180c08619040c00e41191050518110b2038120f40c1e1414250381c01c020076400483c0d030b9001210034030b0400b13001d001c403a500050724075012410849103c000645001c1c1c035090401103000c6050120502c25030403a140c4000007080100030380a145050003c1d94800d0004440b4202102080 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 971650233 1250 971648983 971648989
    0x90f03030c06010b1b0d0c260409021206061c02072307090c030902031005090a0b090c0301051509070309170403150e0304030f260f07121407110d02061c0b 68
    0x216510007941e50320b14400c0d47c54850343c0f000380ca5104949000031740303c20104002c2401900910041000c0303070002d41c4450000321203001e201001800d036030140748100b03c814034810004024490340a242d10700140c417a011402c01c905403148912480c000c40b4000599900442000136445044852030442801013144100084003941c01c41d500094059101b5020152103420942200d036201030a0f40440740c2540c0340e900d03000e0403544161514903647d0001141031000741028009c143d0b21800003604c1004000d4a40041024040c0c014401800c06944c2c0d02c00030104003804c07040394841d0701c82c49691512651681052070b6000703240c8040340201450580701c0c180072400030090790200c940104061203190b00607218450495280269001e504841400d2003400300105d8010301400310b9018002511030100d458801785040b0050070100502500303006003c0b0344120343c03049a02c41f0360f10003501d040200d900c4c1c0100c2d0210512800c002e5100b140800d540c4030014001c90ba00000c4800b41d24240107003a402814 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 971651483 1250 971650233 971650243
    0x60106030c051e1c06051c080d14090c0d1205161205040810092312070f030e0a03110f04020c060a09020a0e07080103060b060c070f29090f03030c06010b1b 68
    0x19150014107410401d0a00c2009501c46081940140441c41c6009d4520680100b22402007812120b0f40c3c8114040c0407092208024001903038000382c452000c102910389800e48034400080c541c004000001949044802c540018428040d50000c0c14802c8500700c418082c203160098050007500b84078007008010302147c0c1e07006200440c1c4c0c000d660190321220032400d00d180d0024444a00400d8800d41044042c50070086000303120141c0105002c0002841c1850004c0c25100d9041c5428401d0b420701e03000f440410350080405c614034000301c2c0c0955840f999100801d01a008010072104070740254010050580d1460b0410140309200320341000055440c3c0000c248250700984041002541000c0140001020399126008042c40200740714100801c0c0c0100d1840c00d00590486040f2900c02d09003000354207003090787c4034421a08403440200100040240300345900403911014403e004c11a502652514148100d82d100045681551195a103800c0348440e15400449045c41314506044110142280810 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 971652733 1250 971651483 971651489
    0xd030c05042103140d02030a14060a21020d05100624050f0c1b0906011713020a0f0e070905090114090a15060305040c0611060106030c051e1c06 63
    0x180507485000d03402900c80c54044101e6080b418010076a81c44a13142e0703007200c05040032109140c80541d42c1e26095a00500703544100001c03200400900007030000c10380c0e400c542d00b02601c0d100029010705031000c800301010b117240803a01035040801406c2240c144080454041220041c141c01842055075501000a0f130711800004020302c101c150701014800c62140d4018403000b550b0f51000d50400c13440304a0182000307851040b500360754002c032038100c8650400c407903203e501c00d0090904c40244ea41c0c03240d0b221041c0000602c0c00358075003004404801155a92070300f107400740182d008400b921a1b103c85404800b1503040d40d440c4081400704100085915204e952581a1222240a0002c41440d1024480c41203406880c402c2d81a80390b12500807075901c020718000092100f5500031503c0c0c1018100325174408803a4100004004801407400112400090380504403111807400003055840c2c4074040b41c1d035000f400c0c80c203500b031000700b02141b03881d04101d0b026280342c0100e40d600c498000c07d404106411500644 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 971653983 1250 971652733 971652749
    0x14010503070608070309080c0d090b0f040b03090a060204060c0b01080601180c0c0b0916090212130f020a18151401050c030705100519060303080a020903010e0601080d030c0504 77
    0x41c42844a24483c4209079000852801e001c514206965141100d60304880d405170b0081d4043e80d004581d00758003c0078400140507a600c0d8500c3d021207400001d44602c50b501a4245081c000008140000400c0203800c0c40240c001c18215111915020001d2081134140341c1a150030b9590320012510b10760100390503040b100303021090302d42034020104090103000c40190900c1400015940c4a0108118102461103003941d407010300703032054420004036000055600803409061051008402c40f1b11111103245e04a642900d1040083c041072a01407200804c06800940094607004000b580569003030340400d00503490f18080c00f100445c3d54404c0c44030340903441030b2000d2100d115050034241d4082d030010400400b4240c190f902d000000c2e01d45074030707059a0019111030165244100300092440000c02c50071502e15840278080705146450041801001074883d2a05070340c00106a840d640d0254040410040860252012076039580d18980d04c5040c820a04d1011030b00340303140e0020f264842c0d0300b1a02600c03180 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 971655233 1250 971653983 971653993
    0x3090a021005160f02120105040602040501090803041d13290601020102210c071a0702240406050a180b0708100f09020310080f010b0a06080103020f0f010e10090914010503 75
    0x9519103404c0101c460000703903001040b03081298100602030090324400d034040c202c00360340c942c40c00d000184140400e62001d045600180b0080c80380311940345480c03c1920241c00844000d03107400364010140441d40000600c42440540c5a1004000030100b85483d0143d804206c05540d4901005901380e00c036030404c040d1a00340440340d41c1d0070043e150100c0c035000103d01144c03509014055450030b4010300713046002c07503011100404000d00285c2c1084500c0084810100c2c00d01082c64614401400000141000303000e00e4440700003c03041901ca40c8034074a156007850404056401c2c0d41040c49022109445080020351510000745a03014910b0820084902108000e4003892400c4001130094001900ba40b0081040c9070300054005800c002c0c000b9201400c0b00001481007007481004074101b031a62042c000d00c11980010400f50380c0781c0c0000040c01a003a02c4c00b010184000d0300403141c0070103260342254418000d0010000c0e060344482800140c0b91402e8041054941d51003800c000c0300704c2407040300d0349a480 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 971656483 1250 971655233 971655277
    0x40b2b050c0a0c2a0e0a0c09060e0303190c0b0f01054f0c0201060e1302120d090e0903030c0f0c0a050619150602030910120203090a021005 61
    0x819400031a8031401822284608079000513003503a44e88100302e10600c20b0302e84070003e00880e00108515604507150310020001c00c045080044c1a25001d441040d0520201d1138070b00d01e054400b0310840c2c10340050409201143c0000d1480a000c40081c2001a07d0344814400041d50710320354141480d040e10b03002494540b4142640c1980825038260000d00038403a0307128059070340508a400303001c41140c0382c1d2241646142c10071031000d40880d00103100003400c580c1000d03000c003c2c000240882c40d406c081c040500030000707242400400d00070301407158120407910036140598500c0340c2c4081098261b405034404409141c84040d112940d0740000d48024041920070014034840c07509030401440030038084030a4440f41c0e101520b40504100003161055804102c0231003503d0141d9251041070080c40c070400c030300300f80e072070801d14000e50700c1c01004d043c240150761340c00105401c0d40c0a88a001480d0441c0d2005540d28600040816160405030034224040d03074001400c1a03546025400341c1d41c10000c8000700c40e4030094 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 971657733 1250 971656483 971656487
    0xa020307050d0309050907020f0d0305041e0227010623030601082206090606211b0506030405071406070812040804090207050a17090102030d0f02040b2b050c0a 70
    0x1001c61000c40134403140280002c0ca07a10758104407440b4901c950050482203a0301e555450801c0c4030782d6104000c16144c50308000c0040c01d00840d40d4482c009843c000c418140c070b5480424041e040414400c4802040b4044909440f82c0b9444150305840091b500d00e000340b40460441900100c60f460b00049241c3c042c400182c0303a5221342051644040783c00010105843d0400d07070040b5107040028190790850b205c068200a0103100d00401d0001c11401c51000100d06030044a0819180501402090304030441101c00101481e075403044040c02000b4090340e40c4c0e0a1914006a0326012442810291220202d081c2045c2c5015001da44030660407040d41803030205a40c2e481c122440000348102e480107006d00000c1601101031003c2e004480c4188020b186424646c18055612403a42001c0071540c4401c1003100000e9902000340c45002040c0400401c1c807542c3c15806502a000c3d98100703524120f000326416001d800d0680703280504d00c0c1c40074001c3c164603429010300307000e444080318214860203080004404140c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 971658983 1250 971657733 971657749
    0x10e070b0703020312090309040b1e090720100f060506041e09090f020a15021e0f0a081b160303120b040203010f050405010902070201092d0306060e090a02030705 71
    0xb4880d10640b46403144500c00840010f40030703161941294008074001145081038860b14071800d00c00c5418900d010502c18542c01d8820320990a68011100b110218a1541c054024100c0c2c0c00308076030749200c40d28009001241d0702d2021403460f181c1d580c10200f0b80e40d0b080455100b84400d850010f08224902400c0044c4d01c820006104044201c000ca00d2000003aa24880c1c42240b07841351161400c01c500d505140100413401c0c1d01a044580452000001d007030240d80c00003030070078080964010056815002003080350a004c011340c42a02240900c3d0118020032500d01c0081c103103500034040c0503801483e04080c2c1681e40c4034158034010140d03a40c010074408280105001007000b201d294000c00e420302100c0108003681c0084e030040424401121007405a460180552070241844a0b0304604142d010b0700020300501003845122200d002c4203507003c0d01e03e00c407090901100c1409516940555649180400082026106034100640e030b01010401884011500045903600180100405400d0400b001000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 971660233 1250 971658983 971658997
    0x20904050a0605131a07090519090608030c0712020a060c050316080406020106050d081e04030b0c072109090b010513030b1501050c0d0804171911010e070b 68
    0x5124109000c0700050150107054455840e01003000058842490b21601e201c00e032018800d102c41e440b40411000c0e030350188800003102c0c6c04846030b440f03060080d00c42648000031a004030104504000c4086140600000100b150701d903900c044402095485003900840580c00300000d5021007610800c205180c411451405200d0085056900e41911551890a2800b42b050102c03071004000c20200101c907028443e05000706002c0d42c044080e407074540c0c0d0720410303403040da828814424102000580c10484400a803005545e1110391302d0124100041032048540120301d00f101d020300100400c0d1031000740030001e0401d10f0f1203501c5501849087c405000041e1520080031810040c0c180320101c118030000341c194000b07501920040c5080d0805a110b14482c6051a12440c1401410008a100004006001c0c1d00700c0c996440e05d07169030307242c510340031204a9038816160b1b16880b000c070340300400742208046406001c2c6151903031003030324000031103003426128150100685908901020481440f02000801035 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 971661483 1250 971660233 971660243
    0x1305151806210f010819120e1504150302091f0e191802030915041e050102030717062b141c0203041503090f020306090c1f0c020904 58
    0xd2290841c0d10150261503040e01080103004001444640366092a440d4090941c0c40081d0002009038100c02400d01b076984402045502e1100c08000e03128813901d00c10340c40a5005081007117800d4504205503442c0c00c00e0142e03030034801082e1111644240070f40708440c0000c2014040340c4465084070007030103140000360801028081c00030500407040d541c2040b921401030484140180c0c003420301c45a00ba0b0f4105101c25070072103500c100184041601c0024284925600c0070b00d540c6001c0e540c5141942e0b00c091610801c0c1101c101001c000010004190080e502c20b98041d5a82e0110074001041425503010a03030303010b80c03c2901a007001c1010401405d00041800c1d101080340c9020560340d41d10281c16291295119854204242417110040390080e800c15052462008505040c200944000314842d030100c0d0000385950b4604210801c00200280840d20b03800405580c4103180c06d0301d00d03944401c5451030051107100da012081c0070024003e42c0ca900c1b082096070b60403520448030b17800c0c0720000401400940d1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 971662733 1250 971661483 971661487
    0x4020d05062401030c0e040b240c0c100c0b07030f021306020f060f06040e0c0d03020c09090c060415020a1407090c0503040b0c1b0607090e09032b0204050a09021305151806 75
    0x540580a9400907107041c9454500580e101c4603150f11070305004c103100600d0301c030301c07000030330344405c182c0c00b00e0081482900003444003100e45800030164014038034400210016400441c0602402c51003070100012944103400703503480400c01494442c0c48403412186140b24268003c0440c64a0400c0e52000085a9400d01110840b1980b9130014040ba004443c0460041e4041007807003d040c01c100c5d108a41204465004102e85000c01000400d02e01650003614090700c0804695440d0780e100b0401c10903d0b80c0c020388094414070f9034503c2c03103484802a02880b540d442c140300020b800c46102e01c0449200d01d810042142240c1c0318010740300c00552001124087c409244800080c0444051010501410407921001001860911490f401d02c20042c252000d94006010074002e07510074068010300703e40c080d01003d071301c2c0d001e8048a10007401960441a044103586501040c0c404907079004140c0c6103050754541002c603545a0401c0760941e42c41880006011091100800c41801704110400040740102894 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 971663983 1250 971662733 971662759
    0xc030c0102070b0907120f021014031f062307020303091203030f06060307020d2109080301140d0503040306050a0605060a020c040c030c020a03050304020d05062401030c0e040b 77
    0xe0980e001420242c810707104820034824030348410000c0c040201802052002e860607951104801c0e1101d200c00030f40240311942d103400707509104007008206c0c903c142028030b4a90810b542c01c0e904040c2c401d0000301c440d90649c040803881a0080c1f0003c00580140b100100c1c0700080030303100c90091b4003e100b0413600342c401400841810390750b5031918114416420002d58480c07074070171002455070f0f4014003402e000e51740c1001882501a030200d41040e605400d400d21101e015608981c103c1c403140020748080c400341c504030f10441041254002903048030b0503500386113a044180001c0000380102020006c2803035004100c10000030b119908515400040e40600081041e0703980d000c6030f2241c3c454007200006030016415440c003403a00e0f114501000784035250420030640c0f80c00020790b4420070140041e0501c40040002821942c2d0182c610090f25806029144981028445c5a100d000381c081288841c1440c60f07803d14403544244610844d01e411076840b040042c9400c1c0500c402000d905942a0304201185564 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 971665233 1250 971663983 971664007
    0x110f180603040321110f03060109180b030f070e041b03050d05040305150108030406050c011b02012a05160204090b070f0909141f1a04090f0b150c03 65
    0x910301c02d0b030007922a2030825640200b0b0041c0f94082c0242e00702c91034a042d01e00780c0d030842501c056a85620007105000d5598407460b0041c1ea00d07a8603a881541c1400006400e45120000d80d000349400c4030040d8212400382c1c00081449031500114050350100b00d01c0c3c00300103004200482810248a80100f00c0100b0306a117944400b420048004543c10100384001800c000f0070a0800190180c513000b0b001c409060b50410070031315100c1c8518451001002404203000c00d0320071080d402001d060207000300c0146198000d6902a000c1e042040b0320308003940110802c20900c1050b49070300480c3e18890303650f0615026942400c1413183d2010320042e80c1143d40d0700303035080001d102056068042c0201e6104c980c40310139481001054482150081401d450030908802c42140256a440d0380044003400880504e0511582d060300d1602c1c698050014010740083ca491143d843c0401041621020380c414440250702c000550296661629401d40100c140c100709004403610030007030b0000704103843c1945c1c540820310041c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 971666483 1250 971665233 971665237
    0x121b0304061a0603060a0b090609041d070605030c12040305090904060506120307050a020607060e0a06050603190209070c0203070f170d020703080307030207021801030f03080901110f1806 82
    0x104031405a030b6214220540300824100d8000304500700c640a00d185400300c00f00b41e8036038040c071a1038400d003004900300c00e030359903003505881010001034410803540450851410b5030b200360100c182e449010304036011500c240f192040302c2c4190044600d41c1c0c50408200541c01807214020301c160204002403140c44040d607110b0b660240101e0181c1d41c00300b00e50414004014a02501c0209003070f07242d1003042940001980441c841000580498819840340402d0800320302601c015011a40c05020b601c2120040140c03507440140903c1040d821158041814002c0d04040307034590300044c0d0f015048000040080c0c2c440c0701031480c1503101074292220590b8a900508842c1016004400b00c0c40034844420320f02c0c0d00410454101c2e0907584000d013911880c41c6c0301c400d818800640740004068001540e0340564560054000c0d00100c20460ba407504c0da52802d008500840401007140000c08900104681c0310701401100e051032240b4071300a181000c02e801600c9150b00c0b0328146c900d8903128204400643c0d40d1040 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 971667733 1250 971666483 971666491
    0xf230406091d0f03030106090b030903090a080f01181e110301022d1912060f0e0a0509010605030c0d02010909140711030c030301090c0c0605010603020904060e0606121b03 75
    0x40902945480b0a60030002980c078085001c1e0b0040c0010000690b00440130303021a02441002d5175680c80d41c3d4034103230851050f0310500b038004181810000c0c000c40d00003194038413545e40c42c00030484501e141c142001c446041e55005424102c1c0144105082d95000c010782410034800d070a07210420003a61b001c00e003603070400008003069681d910a4003003c1c80015400c0b4102088002039203280c2213554038405074041d002001d0340d0401101c140c104102581d164080009003c229000d00d4580703603112012907024808503010984603040a010490401301400b440d8180d550003030181c04203002406c1032105010202400380d04104c00302d60001082906842084400b03015800441450702e00524042c0074402804a141000c3e4020040700c0d10030360021003030ba415219148404104054210300131070780e4a100d40030103000c007490000000741c3c01e60554000e2081903400c0d50305204290755542010606142111540d8001e8420401c0030306c0fa00001074115401030710320300240901d510310414403005800c12a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 971668983 1250 971667733 971667761
    0x905121c05090c011103070b040f02130f1d1606050f070c0e1608240a0b0a02010506031908030f042603070318030e210102070501150f23040609 63
    0xd200301c01070f5921031071a13440c011004c2c00651607c0d01603510744a02c0c40c1c4c0180007a10181001001d40215170f80d000c40030200c0652000148504400200d011000b0040c5c1442c032051440070481710141114003044402d500c0100c0d44400000034580321054035550b11805c240040721504005c2c1c5000940399903590001b80450865002581c68410708144075081e00704440c03000d003c14a4208403e40c0806600c1d44e20100d91502500c140c0c030b103001c003c54081c503080c0c0c101c610801008901084030582c1503101c1c5100e41c4040303040341c01407000308295000d0f40040381406040e0303041c200f000074000270002c0303045c44d08117100301d17190800d1901e0105040f680b5002403910105200e000018880c0541d4180104401c0f907518801c08101100740d0360380600075003103035003420b40503915803e00123104541e48115174524026510095585030b000d858914004c000340c840310380c0208007608001c2401c02d82c0701da00a056410490307404808403484525500d2000014500e154420344855001c90480c02600544010312044 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 971670233 1250 971668983 971668993
    0x70b0a090e06041104061211070f020f1e0d050f120301030b01050303130636060914030604020d0f020402070303090b0f07050319060b1216030905121c0509 68
    0x1801407180701800341c4454071840c00d1160718008520f07198116005c0f21403a0a05c46e06480c0080c402e0b10280402006034900d0620114108080c48407807298840518400c9400a402c500c5500c03c2000b50304480382c2401d038442d41c8420906450411243d100b0400740a08112048403c1419489103440000315804d0101d0b1004001002080a00b154042c05018218055401e140b126500504518502d110366002c0000c25210740b0301c02c2c0c10b074a040307060140b9a8a040342c00300e038804001c640d4503000d41c0709035400901601070000700b9842600c0280c4c40c0c0000140546107540f00c0c0d070204081400e0600054490b00c3c00040540b00513901c6100500070701384070791808202010b10341441c10314002c0007080340f10a0b06090007041040d582c482c040b43c4e400514801d85000240c6148000f00c020003241c0c011301000240011100f0b49121500301552203400402c0c800d001c100d106510031402e450045800900030342c00310103800c0e03542141d80302600359052600001c1003021f07000b4003500c084d124150750341c04d82a08a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 971671483 1250 971670233 971670239
    0x1202030a050a05031e040e060f060903151801020909131a01081e033a0204080307022404150e031e10090c0306110702030307030503010e01060c150e070b0a09 69
    0xc030045e280c038000341038071070805190a01d0504030b004001c2c546449480303100b508415581d51001501c10140700a41151122040c0c5a080300d010003041e26500b0074041190000d1340701c0241402100c2480381c0c0070b8016040b984411071804118042c1d19412940b461140c1900c02c846500d8500d014000c01185008050b010200c2074088200300140702c8584890304100202580c8c2c00000d00c03040540c0f0456200305c803104030081032224a8071800c00f0116046400054000b03103100b0004003504005000f143c251803070032070391081c600d410308a6022103002c050040c8010002c0300405420000c0e148031505140805180e040c0010381040400c0c00002c1c1c0c4010a4880030041d11004c20170740d900c074440c540040022610a0303c030001c0b495001e100051a0355100d107040070039034a40c0c005480d80c2c1740c2d0207400c40f5283c1b8214580684250000d000300321140c480c20b13000107022403044520007003590304042185501008200040050b211042c1c00f0141031007030300400508445a0401000755110300c5d90341c8020141 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 971672733 1250 971671483 971671507
    0x2220608011502151015020601090b1215100e09060703061e0b09040f0c05030f09010501030b0406020c0c1302120a05041a1b0301030b0901050702010e071202030a050a0503 75
    0x481030700708128014640c000c410709a50001a10410f140d4a03080b5a0403170313510300101e60b003c00040d41042e0002c000c0040c4840b0820f800181f11812303114a48020b0040400d00010710600c0148855151003a80c407143c580b42d0030b640c4440026802040001035500642d485142441d00401c3c2600d41d03032940e0b8401c00c01c1180e0198140703e020013909081e00441403102d1590203d81214040d0b004001e0b407800700044510302d664490780208100e205842050044500803040642203801c00c4070708450401c0039800040840c0c00602c80d060582c2d901c03003100c180c1178449440310802504038101082091092501c280e20715a40c403450041d020f444c204015a4482c981000d82c450b501014105203e107034240030912001802d80c0004480851040d028001607540b40038110688020400c19111100700010001c02444103018045100700c09400003841903440345070b012401c075010500c90384031640040700300b44030281c0d4505001d210980018200d40b102100e41d01c03094208000d4140440d00341d0301c00200c404e13841b6 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 971673983 1250 971672733 971672747
    0x1f030f09081b0703020906010f0504030b1017190b132a05010c020f01141210031403130b030a0204051503010305070509090d0f03091211010b1909020a03022206 70
    0x490242003d24a142d022550003c3e014041d24140400d05c2400301e20b442c440d000303172802980c00c080c140d2803074100703104007083c1464640034240000420712403017040040300081406010001c0d848041310901c46848403040c00300e0103040c030a41d10f024501440003107547e04464185c2002510b850300003c0300780c6200300b08080f10355480141404411802840513a6460a020092450070700308003854040040034442c0500c100003140755015280b2040c08020550890b2600c240c2c0d10036503110b5142c60351449203999038000c11803100b0602201c00014010500503201458110034908000740c08c16403583d00003100303445180ca401c0d1525070048010000d00400b007040000500054940d0b1003075081286005854664901025061100c0b410301c4011039482540a10314180e0403030703141d0310090407810004100540740c0501707003201e41c2404001e009500d00402d030721060381015861030f00c10034904803041020b03410048040082c95802d001d412640003146c1206030741407005494143c2c055081c54409049a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 971675233 1250 971673983 971674027
    0x906030e010c0e0f040b2101110f0d110408190210210221010e101401051204050c060c0604140c010804060b120d0f1103091f030f0908 59
    0x6607051205a2400e1600810f1140400c4401c2e00c0300f41c0449407810100300039100c3d04901c59049807030140c1d4554200f203c0340582640d403c2d104028800d120410084040502800000c0742030341101b0030061080000300d81c0200700d4082001081c9042a0b5a10600d07410001c00b148400c50004169402c10110300c0c0c11085442000303418104502002d070280108524001c4585040000b10f03400149185c000d050784107000080502100440320395a110040810320800581d9140c90316084072101181210002c0d800d20802c030fa069441c00e0070610700c1460702c071004801800c2038507540507840c0000c400382ca54400500d00c040f0070780000d112505251800e04100820003c0d158002d4111090b82c01c07050380d001080682041e0050f030f0118106000c2800940302101c0c800c2c000c0458071403030005c180440c1c1c1090300c1000c4200307036844440307242c0480b0501644034820f1008003079100300c9800040702c4001c07020070b1060350700c41070380340001c2c042000015040886030110307410f0361000c101041d002c1001c0d502d8032000300d08c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 971676483 1250 971675233 971675261
    0x30309210201050304051f0207020108070c08030610050c07240302090105040b1c0f05010f06230a1803080403120c121412010e040b1312140f0307090603 67
    0x14400800e00c400c010216040090401c000000801d05000c0200311181c02000f821041411044002803c200258040d1400300e001c03074a000c0026032074601aa10000000f9040301d0f003c6d15641c1c03410100311030100300e0030000003846402d00c18118400c03420890300340a00b991103294801c0130749041059501005040c00701c010107004102052403a40c3c0242900c0c1182c0d0718642c17042d01c8800c074a07110ba0b01040090580b900007494190321071160f60302d5410203030403282441c0382000303d1500c6440403a581701c0c0103101e142c04c4007140c510f0031080c82849002402e600b003031480e054440300704501d103131503120400b0341c81900d1508011500f4014413104c3d01d502c40c80120b450401c60518001941c0300c0c3c400340050000d031001d01c4090b4070a211404048811210f0001c400220181c4541e102c1d04100c0d4602d00c160350a0303924480c00030001d032440d06022181005c0c150040c4403105150a41c07a400c5442403205840040c28007024040d104401d0b01100c0690301a050544908080500380000202140c41845000326 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 971677733 1250 971676483 971676509
    0x70e060702090c0d091e0c270f0e0102120406050108120306120c061603023705011104090e0105010503030307090311062b0e21070c1208030103120c0c0e041703070207030309 76
    0x4420b600ba90004142350a6814013091000c2c0103440f4400071700c003143d02d4500550000448420319a084020f042c8200e10030007003000242d88955010303548200c03801d200c0308034180c1080031032800c1c40c0022081c43d0801c103500403220500820b101164464005c0c85400d0140d82030400c8001c100354051100341040b480b002c000402a4514840724080c40148104450003c030034244500c05000080d0000780c5086204c0c10030581d169580d1015800030591400206515480c5c031001154515002c0308aa00400c0140d503528985415030b15030072002110018203a81c408001c11084507500e0503a0a00007084501100500818002800700400e54564610241141c1c0120500c0002519014001140c039a0b924040300d0b120441442d2000d01d0031000e4001440741000c41e0010000c2219440007107040e248107016a04020541c11000e0706c0e4a80030740f1004003052150b51080c0548010908520ba0041c054810449082420f210207a155031050701d4401c0181c000150a00a0541000000c0c00918440039100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 971678983 1250 971677733 971677769
    0x1805010e280209010b0703030f0e160b0a080c030a0e150402030c0108010f140a1805061504032d0b04110a0807240203070b090303070e060702090c0d091e0c 68
    0x180f014201406407078009480031401100f8584242d100c100c1c0c28182590070013a0f803041c80d4480daa20280782c441c18501242c4081c022880d6280d00c016190480300a4592401a884100406c0d4441c0c0004042c0d0b8401c40e82c0341041f400302c4004010888600c2d0035080200000e080a0042c117041c04e070b0005032700d8103001408004104264002d4040806c0f03881c81d140201c4001400000645403a4455004c407288100380960a2001085580058021302048604802c01d44034021024503034041e0b403001400300d03c8251a552406070000c00c055005907131a22000d034000556503210001c8002c26241a01c10b8800107501c1c6010303041c402500d4000d01103040003082500e10700180c101c1e418120402c9082c014488000d2100128000c0040d9803039540d01007940f00e101c0c40c0c0310091a80e2034004441000008607101090101820320204850420760090403104056440c107005143c60b61144543c2400e95a403044040003261560407555040301045213001d00082007030a011f40281c0081d0081444c1380d580c14a90 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 971680233 1250 971678983 971678989
    0x190b010e13080306030f030c0f0105101406030a0207080c0c0306090f0a020d02030a150b0112020901021902190f1403032a071802190e01121805010e2802 67
    0x282410382d0003a00d4654a0b83c815000c82d0418480306540754044c807001c2420125400c0101c0e0190381000444009c01c90f42c0c1e9090103d600c109064031403030503180a949040340103814040000c41e80b1000b40c0102501d001d4160360b52421645c800e104c815041d80007100210a1403034280130147c0c02280c01c1004100540c00b4100e1141c407244503e034001e10800583da07404086440500c20311001542143c000140e00c00d980c0e000b00b01a0001e01103a030f0010f00034117480003041c00c6520079120381b144103a00420200e8203011031503010f02c0000c40180d81c80320303515016042c3d030301c12400e810005c0d114045a038030f0003500e00b40c0c98034040a42c040a40307110f604240680211845265020f00c2e01c804200082a551006540c9071401d103040c80d006210640090540241501040d800629500038807581d00d01d01140e04050840d80380c10701d50400c1d0300240340c213640c0b410600400e40140402d1b406c1020095003509446c1d44245c02c460016008079800e400c2060b029840d603800283d0040088801c42c1000101c074410740c00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 971681483 1250 971680233 971680261
    0x12110102060c0904180206030c0c0d020a08030f060d0215040f09090809090a0b06070c0e0a062102060906041203140901052b050411030f0c03030406110f190b010e 71
    0x341c42c0104e56621201e02031202541d510301d1174a030050203844d41e074109140420b40e50340c0481c080e02800c2c40307601101d09201d0310014800b250345030410700d01e07400e6031140f8040210b1441e0141c5455840a5100508405686e5001720381c0003d400d10061a0f030ba5030f281402c11684040300d40e101106407032402c0d11440c080b60508084582c200800c0310742085681e1403d10000c0200f0700c012500360040d1010030840100540204620141e03004a01c000c00f056442c0807600043e1a01c50161900034a1400218844152021059100d441c07000740340750705015001010074001e0700140e0092042c1e031142004c541c18107800c6042d004401d800314696900c1c1c0481400060070301d22480c00d80d0345240b6064402c0c416400b50011038600080440b8509000320300b85401c0070413038065600c2015200b4002c1c800d085c00345042c000380f500d04000003e4044c40c06d0900c2c21505a9210105414200c0300c1d0190786c0100c006103909104140c0301110140c6518040300e91820702e4000313240140c104550401500c1c00744241c9001e0207407 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 971682733 1250 971681483 971681497
    0x905030d020703021509100605040903270506030f070906112d010911040b0f03071824090f05010602060a050a020405120a0213060302100c050c060412110102060c 71
    0x40140c2d9501d42458100d14048000e54040c0d1002102810321004080200b02d0740c00e009810750f000d220443d11741d4104003c0f100900d0008002c80c0d02000c09149203426100b03000c2000844d0700c0c0200e1010740d50310104580780d2007112070004403680e503c100003030b03280c1080700f00e009800c01e0701d40b240240c0c09400800c0d5582a240c0d0710500040801d100c041205001c804801000c1035012009002150a0385081d070820700d0200034030381c0700341e061494080c028101409049000e0000070018100c0901e01603000701a4220603242448050301e506070206402410f50101090796111101c2102d2645000c3d030f641d00300d89528800507180d0341080010001c0e5640000d051b41c00c82810300000589031580c81901c002031140d40d11940c0c001004070029a420403010a8502e121070080e1140e04400f90000b1008048174120300000350b0240d00d0000f08000a80300b60354240c199485181198400320380c100000d40960844c1d801800309903524a1160f0400c40b0800380c04281210031f00091030f2504100240b080c1701d000b504 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 971683983 1250 971682733 971682757
    0x1b050d0e0d0909020d0209130515120a02240703080103050f0610090b01020a12090314070803070f031803080903100e03031302060405090a02030f100b090108090a0c1e050301090503 79
    0x45490150171a9550445245050061103141e004611026441c00b8140c12907603903a84000f00d4120001500740614100d440c404450040c1000070000e034204003c03540c03048114441c410341a1007031500c41005030010002c86010381c0303900c0e0080d0715502c2d01030b24012004c0340f010100c0e007005c1e0911428585c0305528070b05890100c00e000c87e00191031030040349088000107019024441003a035040e07130260089012400e8a0203000c80201d11111100d0b041d42e01d020078481c40000d64400c0000b0004500460070440303400f813292600c0d500039103088059100e620101d40095541c940e002443d2074151404108002e002d258400c0c05012002002034115104d001c000c5c403451548200010480840d514501114054003000380780c070000c3d0402802480c000e40003100c01404078280311010400201500b8110001c49203034245480c0b03010070342c800440300e54001030268403461150325400400a01401581d50207054a1a41c1705441c41103074414a020000b1644140d009034503000c2c24001044021040300c98000001c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 971685233 1250 971683983 971683987
    0x6020a0807032010060504061707140a180c1e08041101170f041406190908040b0a210b090c0c0c06070c0302130228031b050d0e0d090902 60
    0x1031002006500c0f442e4081001c180078000c1c40c2d00c1e1124081e0b04c9501500c0050b1030800009880c2c0005010400d50820210b6040d401410100402608a681e000d200900a06030681c4155600d140201000c50880d030768017015220450040040e42c00342500754550b481c1040010380c221003040203442d50401420142102d00f2403910745190380d0280361040765039170303d68841610500d0710074200003003030506840c00c46500c0010f05008101090016003103000742c800700340170425007840080c024000c2100030012914614180400902510a4000781c4403080c060f4a030024502100b50b4090041d403038030307101090f1440c5041c22818240d1183c40c6c03aaa84102c07007041c07040e03881e081c030000c00b4985052005043c1c0c3c040c900054240c2000103d201c1c11081f244203803440c40840300082c214078143c0c0505644206401c0c528164a242003e8039009010540d08034203000030b4420f074002c0c4d40c07c412400a030100002c1040051820306110300c510981e1120070070300015125140b1004c00c01400301c580703889000072107600 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 971686483 1250 971685233 971685257
    0x18091718090c0c0f06090606180a02031e0a151e18090209040503040e0f0127090b07051b03040b0910111f0f0e0c0402070302030409090f02030706020a080703 69
    0x1e2441140d00c50b81102080f10040c0c0490100c4c1d90f51a43c04880e002542d014250200e1030505015000340f070002c44103003c601140d0359101e602d0000790401421500c0c0000101601c0b1610500c3c454400d01444c60703500080350529645032051002c1c18280d1100705a082a09c11115000720b800c0703401010394994514203076991001098101c00b4021444000e58817880c00c1084c0820080008001c01c01c4449800741c0c40d509644400c40c003030100000b4820044400c05441a050340c02c2068148040002a08280000d100200c0e88804140c10011101e00d00401c0d4000340511080f480c4401020390494070100031443c3c58180700f68101d0034082c030803a080c06000d005108021440c01606500c0d5140c5000e812241d240554024140b000030f0000711030004d682c6010040f0740c10310504c1c012109d074114044028400c5240303040501009601c091800e0382180070600010660318a580281c5412a00800c0d8441c002a003600400d42481d000713034010015540071062200000708208169006141c05d400d0441d49824 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 971687733 1250 971686483 971686501
    0x61501090b0912010c03020417010623011106180c0607020d030c05030c0d0215060906101d060c0d180f03021005210103120203070c1703041809171809 66
    0x4291262402c455003416040036080d64141c1c00b030403c48101080300b202440080049c0790880d02d0f240104180e6104903101c50345103410000045140303403010300d0802940c00d41010f00701c0c108a4159450014104c03880b41800e02500200144400540c00b150700038a031518a45c001541443c141000a0a20030002c2c40c0100f030001c00e00c19907030f10b8a02c0f40180c0d07942d00c2c0302840094070b4580908006220314111008242c05082c20b031031041c481c00000d0f0100500c0424800140c8410580a40e401c450500032504c1070860348901001d01a12100d083c01802d2a58131a00040c00d40014091142c161610303e0004001064405558000300d0f03406540b01d1220791914007044035140705d10500b6048203845d440140c014000c481a400b4126409100c0b4101c0f0001000004c0b82c4038450f1903005092140020000c3c80321b4944140c4000d05400003000300e03407030255221502c0b002541100030820340540d42d40d074800144041e034140200701d8180b0004072450704c4070102c0f8800e20b100e11200f00350b0182980c0000651440 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 971688983 1250 971687733 971687749
    0xf091101020318150f13030b0f01080c150441060d0b0a03060513152c07050d03090e010506030c0406050c0a06051305070e0609011a130e010602061501090b09 69
    0x3149003c0d0169540348070001002c6c044681c2c40100c9062a40800081040b0241c00307505040c0d49068000d022400d01c2d01c41005000303e49194041d18144080100003420004a041c01c101e80c58170140e4103100801003494400302100001086800003406101c0c521107554403000c896007540c1602000588118100c0070414500d070a8100400780d0349014142314801d4040804c180e5030b180b007240070498107400c14444200f0345c1c050706403801080b40382d001c48940000c0c042e180541400404001c40380c40a0343d540001c1d40c00d01e42c44506501007514000c090100081341c040e01405060107a46103451401c2c09001503000384203070300c108030800c040418400342541051020300c1c00e4a4000c0400e2220307043c040c000c0031001c428044116114440c0d500b0000d02c1d40c0101c121648140401889400c041e0328003011101c1040c080c10129070403e404008101d603a00314000424003500c0814001c180560401902078500480600345115110f030054441d0b83c66079202d55000103803544800c41070b40703403040c840100e0800 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 971690233 1250 971688983 971688997
    0x23031c180317070210020d0815030f010908070b07110312040302012c010b01080c071e15050a1a1f230a0806010512040f02130f09110102031815 63
    0x480d01d8041d5584081c0e8802d80a802d4560089480c0102c12140c6842a0398600180210305e010861000000c0d00c14184410501c08604000d4140c0340d03d40300c4282c4072401c4071607003c0c0480f80c1030b401081c0c44052000030b2007003550194107401c040b0320742c800113016984d0b00c0c05002e5003925080d4241001900700b510039042416603840681816151150031801c8140a00a14002949940c81e000c8400300961007201c865000b409400c0c0850315110b100d4645900442c0c0714581403803400010740ca154009001c6041106000650200000d01420086240c40c00e40e0b51007000750072242c0c502d03111480f540e91401c251a58151203200c00c455106c449000503518070b18042c0c201a0840709104403a45a0501302c40282607030b91640c0d452414955036800107460750302922203116075200c403440c0010002500c0c1541e42c045140010300b812080100000708000740e520080e903001e452038407424074000704090080041c40100c824001f550030a142c5500c040034414052101e035105440080f040341600d42c40e1006c031100 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 971691483 1250 971690233 971690243
    0x4090c050909070e01120209010903060902120a0c031e050d0f0918050a0c09060c060507030b1c0510020a0e091f150e030102070b06010f090e0123031c1803 68
    0x51490103c8014000c0319040c14294003003510030911240c005403c0c800ca8940300c4058544c0c0c07542d6400c0da2144801005212000ca030400e4210403143d0040070100244080e480c450201640600c3c19440c00d48080c7c1e128004101e1440c1000411100081010498411650092400080032005454104c4041c1c0b1164440c40d401802c0007051005003105070413175031191076070322414002c2c566121021140c050841c466000090001e42c2104001121078002603000f050381e1802089100d081030004030b81c5010806044d2110700a84050410050107000001241080b07a10031401c0c112004009442c52020031042482803009000083c40c07900444e16002c030030756900d91001c000a841d0110f48240f204010725600216008010030419071070140225a02903500c184d030302c1d1098546000640b02041c0e8080040e0034081d01000c085540b44c5000d202e28003e205215010909180f50442c0030400d01d001e250b4207000360800070b01c603c0110364114210000395128a8810104401c3d4500b031140e5603040d40000b09 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 971692733 1250 971691483 971691499
    0xb0702060d1401180612031b0305040f15030b181f031e1a060102030714011d100609060806011203050c0f010c0e180a0519050c04090b030303010b04090c0509 69
    0x144050740316601200714183c4603041000a4951103455061000c01b807005000940c44941c06205416212406014501c00e041250402c1d44401c2c10140c1119260000c443e0034280095940d50700703506001d04c1044040a590f80694203212090081d51100000c007058001d0040c0790160340e502072015500e000039904949454500208544c0d0218090212401a0380c04005070406c19003010482128a00501050300114900a007543e1061030080c40c02548480c01e540e1001030103c1400d02c0c40b14107080900c00e40140c41c01c88421703000703501214601e40009548502d0000284460000010f295054440d0060001c9403103100d40340071902440b490780340320b98601810341506c145400c15080800c903002192241d4140c00d240e5018000701000f07540c50f4560180c0500082100016554002600b0411040031080c00c800d009121031f0070740b081079900122203540054100000740300c0703101e88071095804802440c6154982502c2030b020740201d002d0080519540c00846440394042c204803801114054004e103 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 971693983 1250 971692733 971692739
    0x30d23011e031101020f010603201e010c0f080a110609010e030909090102040f0e070f110d0c05030d0207050f010501050a0b0a0807051903020309120a0c080d0e03280302040b0702060d1401 82
    0x41c0700c004c400100c03002070010514000c010380b400030102f07030301d03141203000c0841412204401101d2107a021a01915581207950810002c0f442c654003e180011254554030109035074800300038600f44005180010b05c0c1d140c0300e01032010280100880e1030144003103c1208180d150b00300483d00902c00c07a0b0203c404040c191303070001004050032000c0c0d072189525444e261091a8588000d440c40e01c09004645240d800c0201403070940ea008201e481c104134011021207041584980005003280d00000c000d4565a02110100071a10424041d560140c07000b5200e2a0015103040c40e40082800b03041c2822042c410010b00094840c1e20035001da902c1e407a11040050580d054907400030b0003d50054a0740202d60260001011271040208210384003405165102c0059907099140c184981d04030305102c0440907100d48070445a480c082020f030400101c41c8804846820113074035000411070307010300c000e000d02d80180f10402450000b40103940c2c1941d0141d6465558105a00d03800b40200302000c1e1000705040070130008 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 971695233 1250 971693983 971693993
    0x503040807261615030b19170a02030a030807021f05061009260f0604030e01020f150a0209040e01060b090117040f0204020c030d23011e031101020f010603 68
    0x802900300031402510b052038490308903030340c0701c4019032007010241c85207500400500580040b050043d0b003907407800040b00c4030103a0003c0d0035100d441c40e40c1d07240c4070040d038000c0c00070440c1e03980000400e2102100528a50150fa80440d46030104200007506000002000401d071301d000f401340907890182007500f11483c043c3c1035403050040200f0344505014a60545400c03405a025107119820390b4540540344240282d81d0020310f0f0350000175414001302d80100c9404a20710b41d02000b107613004920030b89a55402040e00800246019911043e0144550000c00201c4015840c24202c1d034200800507400b60b660019103001c0750241c820031520500ca980380010000e0442142d40180c982102c0990b107005410010031084802d40806882c007070500c41d680705400d001450213600401c121107e84040e0f90a0400c1e501509040f101000c801404040c010b0b4404000d000c1407600c0c883c05000d080440c0081c82c02e804020b0034101e8117600004040c911a000f10030400d03070007006030660b0441544000d20010781c9920f02 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 971696483 1250 971695233 971695259
    0x807061505010315090519020d050115080c030a180b0405061005040e1902041e05161d010e012a15090305031b0712020d090515160503040807 62
    0x8a08111200c2800c080340d10b40c46800745000c0d902c50440400c2469080c00360900060001400c1c5c00c803198030048440303030208250b0015040c007030703034600f000a02c961500341d002600b07002d0315030f90300104007202c8100140d0480031420380360031068203032000900802c0e0322550700910302e05031320261000040500b04800c1240008925100d080c41c1c4445a42d003a0340c440074001502c0411f20614030540010f083e003203680032503924004101d400280046001c0c50582081219a07409510903107140d0307103540802c2040900007400107010207152424801103200040d2285450245201d01410041071a148400303580c41810340b151244041c90300d00455803003a480c5c00300e11501a140465100f990003610203c0c0c0002ca1260700c9100346c043e2145407441d6500588404036510240f03900c0b464600904c500004032b03031a19141a5a40800d4004100803450040040d01d4090b02d0b500c11403142620010350110038ac080c0e8140c5040c030051001001052480f494403030f00b580115006001d8502c10300c50300290524030280c1d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 971697733 1250 971696483 971696501
    0x160f08070203150c04030308060d0c080601060201180807030c150509010b190608010612090501060306060e092b0c0f0b041a06010e1002011407110d020c0319050703080706 75
    0x101c595842807600364070216a4100c034802403124085c40104042806040f90690190000301010225102c030b0340c4025145030980c014080e150321000c01404125024400c51942564000e00c1064160840d5109a410322a2202c01020001c100100303004000242c440040b00068a0005000d1880c04407182c50003000c0c0e0200d0035204000c100c04001d45507a03064004c0307050b95126a5508426800c02030b003560640c2e0550764000f0129a6140c11a020079020b1052201440c0303d0b20300461083c2c42c0c481c1d074421a2601420700c0d6103640240c3d50410003011440a071320b01b0442000414035244c46581c40640788403045800280889001b4602c000801c500c40191500c0780348504d4200700494801044c5c0902c2d01402ca8885001c41e03803910040c1d1142c0340c2001e40d00c2e694885480085401d652010354900b0014044c0c4012000c43c3e403d080006046d2020b010140008646200500c051640c070000655240313002441b11400400000b15030003800000d00c84200519000f115903542d66000d0b01d40b007001020811 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 971698983 1250 971697733 971697739
    0xd0509030a030c1b11130912270939030513121b0602120601090501020a05030403260f090a05220f0e010608030918040305040b160f080702 61
    0x220341c08403481c020070380419820101031580b86a4085a550301c16178041e103d28059000e24006644040410240207011034240710711030381c9159182c1080044c09182000301d00e16080042101c801d01c035244003c100c0740c11222400b41c0400e21566040348000904080041c035161003c00724400c440014804a01c031094000b50740e82080306641d02c0c002010301d030786012001003180a0120720511007070b00c0780361138081c94040030380004083c6c0780c56030b0380c0022684040f4001c080621510100103440d80c100c0407400003042e0038005050b42103041d0755200d03241c0c8030344d0000600b05180301649030600003220880d802d481348001211940e84440d00320101e25900b044142d1403003003126540100e09030500d48040414120080caa00f0314000d03958103510040c00007a070518003500c4c4e4803280c4c4801c90b04e09004d190000d22954002d1641d48a00c034047c812449076520555001c07100030418000025400b808440403103a0500300c1c640c4402c884400c1c4c10010801c2c21001c4c20143c10090100c081c841303c40020031000d4130031 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 971700233 1250 971698983 971698991
    0x60d05160905031203041502190f320403050a081c020405010e01052217060f0f0c0a020f0a0b010e09070b030601180803041e090203150d0201050d0509030a03 69
    0xd10072161000079000781a00b680110aa58803200f54100140d9009445040d019071a0010308003810200c2e0410050014000e200c00030003007003503400005101003854245014540c0000d40d40c41c4e0a4080100382e5030f0448a803950010f540c10070300d0002610007655101d41603414801107814103038100c1e0004580d50003a1200c01c0442c0308440301610803a001c41e50180c4441050705500300040d0780e203801c80c203049032a51042c01820b00040300000c40c10744c09030200c074040b110b00c1c0c00c0007145a490500000c000d0041c01082c8000c1c800c0e2090200c055540c4400070314103142e6034848112080b0b00348a0400c00784a242e104241904c0304008441e040c45042c0c031300502031160075079240d00c10207a59031240d2180780160f0b441017000c5025544241602400703d4414104441d4096646082d140303541c2c0160701000e0a0500c0c00c41440340311441040400050400b0b00095086060058030801e60100f645442881500b0b00201b210071640140300343c400030100704074100400e280c0184000e445c0d034400080c110001c3e1034 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 971701483 1250 971700233 971700271
    0xc0f21071701180201080601050d0e010c021515120a0c0e01170109020d02090615030406091b0303120f1407020a11031b0907052502100806031b01030605060d05 70
    0x1482100340f0441a09440300e034101ca69001503070081400340c8260304216041020040500301d50150b68900c540c100c00010740324103a1480241459810b1041609242c4460300740712940020014501028804541044a165801d2029864142003d1000b00041d008440024400d8003000103503040f9404040c29080c0722000c04100e508854848000940c0031600701d482d400035003012100540e1003140a04407070881c8450882501d4103801c1210101c3d01d064446202d031080007441410510399040c8840034900150a594000d0150161039261501e019901e156000240445400c0003c0f88484007000b8602400c02c514000c0d10380141c94410b640c054805101e140703071130400040500c0c5000b07181c0d07010314169072401d00308441c00304090400020020280500700e1070103540464032410803044894200c00000c5841440280c201c4000e0b10b0382401981d4081040903200422022121040da818440040c81780e0781c01030b0020803080d0051038105c000031442d0320400e034070f6910060050410340603558004034 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 971702733 1250 971701483 971701529
    0xb1207270207032106121127040b09030d18030801080d09140307031e0506072d14030c04060305090106030309050d0c0b030a1407110c0f2107 62
    0x1c11480000c3c00070f060b00d0103541d800e01c5003071213000020200720b42c007040c40c03556a00ca450b001c001041068a000e5030507080604a45800825556040514608a401044420103520240030000c4c80542105840400101606030600c211000c03400660420090449207182000d18800d808038110040b43e0004000b103004040006c83d041c550322541c6d01c054010341000b40b25543c2401c50319440303401d40309402c0048005640a020210b040260000d4101241a541007403403800d2000b4042c14103221b558420f401c1100c5080c07030000003a21200104000002e038078402151428500101b0901100000c410310440c4442c0d140200b0490b885550144502d0310741003d9182252460320004012801c4814200176500f0403600e02000140100c104401080e613848488100d03501c1255401f41d119500d51001018044e031220a581080c0303240741c1810029410800c07241c6c1c4540603e141032041c1e268500c1028195107903105092203032441403140030414070030718441d0390301d01c15409030219139401540700102e403103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 971703983 1250 971702733 971702737
    0x22090b010309021c03030219022a0d030503090f0105161701080601030f03120c0e01090902090112020c0f160e25050912010e06010513150302040b12072702 68
    0x5800130700c551302c11203c2d070740d10720103101070380c0d81c100d040c55020f0203440100d04d040d60a1144004842c2c010f02501e184c035143c010540800c801900000a04000b04015103482d51569104034907030500385140d5036121200700a2404000b0828a0129030810003045903030700c1188a414a900d5068540055041400045030f4507100300b401340c94040d903c03110041012401d00c0c40320303010441c0a42040c0c600e0030064001c800a646070008828045510181c0f208055607111300402c0080c01d0440c42142810500d0000034103041200d10f0b00e00401d60041000005010705000041001d00702400b1120b8000e84503444105101c15803040c1c0c5014000740c4000780c1d440c0149403542d40804095400c01120421041c3c1c10745c5c884d001441183c0c0c20000381020070952a809208628112494100420040d85440304100004003400c058030b038030a06106620b00c0441541c0c0c5490f06607641110080340685e0014086420241411754111039803081c8080000d200918075000c100c18900b4034292842c00ea02c0c1003001c8141c2c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 971705233 1250 971703983 971704001
    0x1302090606181e0a030b040209010b0a0507020118050d0b090c0d0b070f0e0a0b0304050c0f030d0503040f020406030813050f0a14010c0605070314060406082122090b0103 74
    0x540d00300302c542c5285282116400c000007100014801c07114401d00042007940d41950011640c0120b40d1040c0415450494115070060274240d114a140c0036255400402c03034011004024140200121012080c0503d031100102400c400741079089040440c0c200818400002e4031076005c0c40c010101c0d00d1f601810040c500841e0603421000006050300c1e03228040760150014241d107010490381d5207041c0081c0d030f41c810340715000b040400c8c5221345905003414003e003400500134015104240385505100c0744d450128140c8480811801e08648030780c0d4904001a1038a90320100960041c60034802108208401019020311a0900203029075540c80e42d003442201c544040d415a03100c0303e410010000d01c100071242100c0d200d011700d020342d4554200d607101c2050314800d036428404641c84016640d4241ca032069500c0d8081800c5406118691804142d69200c01144a031f0740e05008000d1741e0070b550800c00200304c992071007100c802c0c01d411111905581711504894021203240d0703410140b58120f158441d015400c90 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 971706483 1250 971705233 971705257
    0xc120a02061b0703020619021b1c0c15020a0c0e0f0f04061d031e04181d19030e040905060609060d0503040e0411031f09020103060e1302090606 63
    0x6042115030304408240c42103002ca450318030030103001000684911000c0c150701d007240547c130b0b074019110f00406400c00003c2030720159400c2420182500541d60f2251031100c1e030030794842030b5141007590700307083d000718542d60001c0c030311080c0040c0b98644c0395a00045801001d4062035030300c600c00b512031a044181c1c00d01660040c411512041c0420307031040d840e60005800c18442c20740041c0c00907604d000d411100c0c908944004042c0c00110b240d04051246403c0c5401c5004180d440900e0036050003401445868581c940d00c1034aa03031071840403190b6a901111070300c2e40c1c00c0403040314066100b0f05002c61215140e403000303c0008032120240c031444d04150142440c41a0302101520b12556510248028602c00a12640c2d0140301d41c005180428130900080010b010341c02c121185601e4103080800f550007204035064085c2d80500400c08207095002c0c40000c00401102d4040f80c1080f441c00100c01400c6245c04c0098207100000074080440303c001c00d0303000002e00c250ae503488680c5d141002c1103024006c140c1110b031 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 971707733 1250 971706483 971706487
    0xe1003020f060d0507110706030b011205070c0f0c0815070c0213060b0409090606060c03120c05070803190f020a05250f14060c0403030e0d02041d0c120a0206 69
    0x1480c1c080d078030120401014041d01e08103120015120155102600d02c100841c0c21401403030400f4005114103005020349081c1444481c98203070000b8900c8030018090140c00e903482c404183d000d8400e0358111641e40c4c01808400d040009418900406801441550468498030124002c48200b8008561290510303481d040c0e1002599020b211a844045082130b040d0fa955040125508035008050b0000d0125428002642d0ba002d24061044580d290081400d001440582a00007035010b02c14550b4401d15200103d10b141d842281071750749001d4590700034170900d408000c110040d810b000c41a010301d58030020500c021400001058100d00c142000840051802c210000520101d82d2404000c00c60b81103e2982c4902070781c031000160070001c002145d402e490804080c0e440d0f4010000190001c0061641900d0985942d81c00b610b03a41e06510243c0c0100610b0405c4010340d40c071a8000d0700880d00c540c155a102c01042ca10454903a0400c0c101c10f03106101070460b28040c0781001480b050010b41c0071705094 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 971708983 1250 971707733 971707739
    0x30b010f180807080c0423011503020910050711190b0a0219030e0114040b09220e0f0d050f220915050109090207021e010924090e10 58
    0x121480204081d800010401e03000000e088402080310600502020014243d0710303507a24100300944030702c2120001038643c0f80a9000c14120400718141c1128001020841d00d4410030400343e000c1e001d1629400d034051202060313440780c682c010000708800c034031544000c0c000c45030305810802d140034800358001c2440c2d0103039406c1c0544a00e520040003695005d00440e10100c0c050003145011240f2100c0840000d82d100403248600d50700203640c0c0b400a02d00100c1d180c107080c104240e040b01030085040161240250900c015680f1b02074002d600030306128039905008460100a42941d2032143c020021054440c14202d100218496800e840d210003d03039940501c0c1c5942c203a10f144031030784485c0c01d608100800300d0700001d1403e11440f60090b84295110902c0e055880c0100140c00004a940b2500100b0300411000005a0b500040d4201c0907071030f001d0406100c1c200c90012103000c0380c1c07904400490705584116118a060422046241c800c0300c1c0c2d01c01c001c441e1180d0603100d280109881444600808080034 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 971710233 1250 971708983 971708987
    0x1d120a06020309070b03090106170a030507031b02091006090501050c07030f05070e0a060801050106031b211a03060a06060c08030a1b0e10050f1e040e0c030a0c030b010f 74
    0x2c1d50451880c508030361025441e03506005a6034415622600386039907808007000303254001c00c0990184c980c0396000c0d003000325003514054660b1203010380040801c400da80c0140981c440107003100b030341150054150030007441e021032504008000381c020600030440c40030300010150321030301c02c5a012140e610054040c042c5559100c4100751215603040311035016841012408009120f8014030401002d071000c0b0b0003d140c15407907400c4480603000b5008042c18044e2450f00030305030300800240030101e454145c0140c07903204400103414200003003004542c0d04048401c01d103140026040d452002040f0285c0b41e0b541c171810513850071a0101e2281802040d00340c00380402040050000d1540301610f00c0000c82c40740b400c50450904004e4900c0d0003400310b03048504049003800c000d42a91045003141c00d025207400b00c07261494032640107140c8207842c2e440e4400610725100080300d094400a02003d03508a1081c2060b00031400b00d074004441c0848914030f40300c0d003608000e109025100c803c4906071a509428142c083c02 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 971711483 1250 971710233 971710237
    0x60a0c14070308070803041a06010903080c0c040f0e100e06040312020d021911060c2d070b0f0a0902130536070f1401200d1d120a0602 59
    0x2100094007803508000702084100300184070140c82002101d69034a054a00324501e105400f580280c5104080c040001c540d8210544d5401d5981041d212030303c60201c09001450010100c590541040c181401c014080c0403582040e1010207a500c15280c55500c0304174000102c490110784055542d00200221740442d01844040011014200780945031241813148002070b030348186400d4452404d071780c500026056020741014480882038001d41960300304030030340c083d03e4000d40100305213018a8407a0200c08200038441c3c10800c1d02c690b503200d501c4030031506241703440c981c0441e40f465201d200c50340054012082d84c40b88903c01617000700f80d841003020719007104c001040000c020f4418154101d8024861498142c210000040074100d01d0b0b440c4201c0a00d2903041c1442c60340300012000c1341c503505112103541050b04104640007860400c60282141400006240340b20600180324018041c902d9880da80c03000c40502c284803558030a07105c070010001800398540c51b40c2c0104400b5040468010001406130300 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 971712733 1250 971711483 971711513
    0xb03030304050d05070215190905060721020304120c24020a080d0e030c0d0201182303040b040803071101050f030411130c050c0d1e11010212150f060a0c 67
    0x2285c5901100000841800341e804032a9214107605038400c00c9004030381c0031081c9c030007511043c0c1e4058108001a030314804c0d0b80b5640460888400f40300050110f0740707403082043d14001d100d4084e01c621701d00500d007442141090313507014541044000701d82091011111003000c0c400f80303e0960043c02c3e00701d1280c840008903000b03201c0344c04c400d9446440003108280108080e105148003140034200c4442400c0000e4211226a00d00302c1941c805800c01c0c5005c1440c0c4001d204031050030044c50018885032003409402d621a94101c1089158040380c00304406800101030030f074440c0700d10080341800c501c080040d42c45004942505401c11000c00001d4009000b89600801c01440541022640321065035200184c0e03000701006400510b001c540040340c3c2c0c2e41000a8a071154060902400c000c1d808203500000703200c4a061042404a4103a00a050040035412203018040d810414122400c2c00001104902c8841d20075a102d400729000e0025a4503141040b41c04c0341d40940c4944401c403650741d98504030110321507 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 971713983 1250 971712733 971712739
    0xa0b030601021e0c180601031a0d171b1b0405010e06040c0905060d141501020c010f0e100c060c03060807060c060608121902010e0a0b090f0f0601090b03030304050d050702 75
    0x1210944a803107820031724000c055a12039100d028640800018100d5801ca0503030100c2d15201030348500d941d2903d840c601c3e50300b80c04c10b04041d03901406ca80403803e1486501241080703405d103210000800b0201080d000410404a0144007441c525881000146c1d4400c0c054040c81c1c0d242000401c602c0d252135440b10358039407007500b4000030169940d0005081608081084941d25440d200c940650800e000c110650040d8000401018200502c0000f9034840344203500c5030602c1203c1c1c00340b43d14240641c0a82801102c0140000b85440d1300ca00020704921044070122021800e010b119400d40c0d0180c01844140e41b06c19004102c441d18080d402c0726580707a912010351b04560390380408142c19006104140040160041c1c0540d500115003d0f15228840010002c08691502c031001c0c0d480d03000841c48140b26600402000d04a4030b81440384d509241030003d0310b681511440f03a801c09505408100e003130403030b0480c0c04200000d1058006260322403004642c001e1a540012001d010098018ac002e0100e0398005 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 971715233 1250 971713983 971713993
    0x902030c12030406090504110901030203190203160807020d0c0b0c04030b010e1012080306010c1a0906060102061518071806020c10320d09110a0b030601021e 69
    0x38002140c062001040c10711400d800000d018402280c02075800c070700904041c0c500b0800710319600c03880c00d0303240a040d003a5030400d50000045102104da900c4800000c1480c0c01c3c0466903030620380c0c1d02e60404400d0001c1c00002c150140001000580040303202113554a190700c80701c000c46a02c0d56415500d0788010021035580d10140000720100d10700440041c0178104c0c011290155040066010740000341c99880220300380c81045c4810001402c000030b603500303d8002c0c24615a0400217140c41e2040c41c500345441c00a502810041207100d600000e103542c080c542c2038080d150240c41c0d158900c101a800800c842e43c01c1880c0801001d0b1114610f0485c56000b00c0f14903000e1192800c00d4030400650300c1d980e22110047e0321061001c0381070b05d840340504070040d605080001c1c1d280c1500c40c4c0b450402840b4280c844644401c1120030713080e01107442c02c58000000030a41085011702e9454043c001a2805080d039002e82112580480d4214404048a01884058000f040a0148802c80c000c0d401441c8052918038011 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 971716483 1250 971715233 971715253
    0x618080307320f07091b0309030201060914060108060402040b04060c0204020c01150305010507080106080a020a030e010606051809070e13060b1c0b150414031906060503060a0902010210090203 84
    0x8040302c40c1c402400b01d000f9120042824050074500740300e40d000004400d02d4020386621583c3e034100c01d0041610981004110304903581010780c0188a035a104411440c1841e02c0030403400d128003000752058500f6240c641150b00e640c41441300300d02a41c000c01c22445020002400170328022464910701d1840104058503000e05c150741d0320b09440c0c68080c0c0580c5003281c841c00380200002805629800440fa140c6581103600d001002880200c001d08074603070703659000a01c02e0b0200d2083e044aa01d4450500c000d0100c982d0f140e0004103582d010a41c080c10681d40c1c040030000d00e141c003000050180b5215590050740304030f0781e02040382422101a0003500e6598642c000900084c40f48054880042c640c155200c55040c48032502090320b0400303280620541603003101d15560f2a250042c1c81c1510080da2400040d10224000f00c0d243c91114041c04a2400088200030100302e11504031906441301a001d40d0000d440d020041010f48400490003070168115211740c2803504450f5000020140c0001c00b140c4201c18 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 971717733 1250 971716483 971716553
    0xa03020624060c030405180621010e0106080705121507050903161e091506140d050a1b053105060d09110303040b030c16050d0201060618080307 63
    0x3c4100b00c601415040030404103c54901211030398261481640d00004514100002400710810481e183e90380c601c82115081d07a4080c00d601c1701a15081210080048039103819005a030b4081a1049500c0380c4803c90744504c60381404a0b82c402c86241c03a1403c1e04094070345a40c01d54003500b103d01c5c0c45070144550666142200340c4100c0d140d008050900041003150074400d264907409440c2d401c41d20081c2c0c10b00704113504a15940302c039013084601503d00540706840d5600c0048051240d400c9400300c550a100c00d10032080b10301d6015039407080d40009000007a285030401540c50b070080072201c650460f00c1c2c880e01c0d2562401c51008104550354070402d0b0b0306150b1150002043c0e6002501e03000501580d0704004820018001e81601c50000c003103000b5400c0524080c0100018800140187c0c440300d0042000507003501c54a00c50400c0720340c0241500c0740700c0300c0304000078000d0115115405c0000c02c0b5600b0007500241120170441540d81c200c018510313040154648100d410700c600c0c01110f030030241041840c1c64070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 971718983 1250 971717733 971717737
    0x1e050732060714061501180602061b040f0815010603150603020d1806022115040207060b06032a0f12090a15020a110d020706081302060a030b01030e0a0302062406 71
    0x4142c17007105030020780c17010004103602d121800d403250020314001d050005540004206502082c0d8400302031143d4810024240309002d5035110705001c000c82d900100d403641010034103010201003140d91079083c0e80d9413070f400c40c00e490b00c8180c00c41c1141070b4080140803281c425002018401c1014402048051805a8494003071241501c1038525544c080703140101340c000c0d5985034084030320405020105003044440300d92049085170050340700701d500040d59010483c49412030035100000401e81034030391610049400a00c0441235214001c1002d880c0398050200041041e10704c0f200c0c654480c1410103030b030340c4070722303444040080c084181170b100c3d8021442c000780b0120f101c84c01c101348260005d41c641c4260540036210300c034081e440d045103810034a185010b555000504c141124030320700e00031440d0703100c41d2a002c114030034100020390007200000c0d5070702403681c054116080141c0280e0b0208003c801c3c11940c9510368000c2440140140c001d480800c030b0031942078084111100d00c4812041c041400c80300010015 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 971720233 1250 971718983 971718991
    0x3070908061006030f050c0a05090315070c05240402040f0219050d0b0109140d1a07080106170403201906050403030b15161e05073206071406 62
    0x89007842c401c0c881c0d10760600a55400540c0d4903020301c05401c0c1000010f250f0b015950004d070401001040110003690b082100540150300f544071800d490030710100003403011104040640342071003881c42610040e1301162010381c0030a850050b0300c081d074649a0810000d4542500101ca247e6000e011030340248a8807404484004043c2d11469916081da40c3c80c1c2d01500c4042c802070b4103001c0c01c05c0040084001c003180c440c14129003200c070459420220b04c0c11610f88181e110300750341039104d100100309001c0d802c4406036068a02c0358035170200107441684504030088084030002d000401c80d9810f103003a100c0001035804000400d0007034550004125a035602200c1101c41e0580c4d03900d8552050005160b00341c4a4401c0254042e00c108540740703601c0e803100c100c03807040540010700c020600300d40f10140000362108004281d40c0708a5a82074040a080040d80d03481c1c2030240404100d011801601c668145003421542c845402c40c481d40c1059041c03040102c280c100b80800c0c0d5840c11841c07030300d43d80d481c82400700e0383c4a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 971721483 1250 971720233 971720251
    0x120f060406080d02060a060602010612020f0103112b02180907142206080402010203120619030b04060b0103020c2e060e0f01050d0201080105041a031b0103150f05060307090806 77
    0x22070700d00150810182e603403688c00380e4150f92410300144008049440c5200c0501e406951200200c02c101c00100c1c000d00c42c0b210843c45c0e090000c00c00c4501d8800150448814511009034451581e11081da54801c80c441c074207002e6440c1d001c42404600a00385060a00c2e40064a41021803030050303010320b201c290703602a03042d07000320b6a01c02001549003010741105001400301450f00350654a011340c0040d6982c0300d40140385c0300101440001611603981c880791903041101c3c50309080c008668a1601140e168408e40341150200c0c10a071b41848654480c0c401c2d100c0b0741c003c0d64010422800d001816060007150150404e0348141c1a90301d481c80000c0300c0c003030a0024880c0b9505080680781c500c5043c003100406030070891040484c0c00120000d83e80c00b107400d03410346204940001d1141b1b101400020f0000c01500355641501039060706244c011149a65800c19040a0304c2c01c1c401d03502941142e684d0840136000b0440198001401403003c4e041c800c0195034400740906105507210340b0381000900e400350880344210 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 971722733 1250 971721483 971721493
    0xb060c010c081008071a0d18050613030801090e01020d0e0d0207170a03081314010c02071d070807110105010906031a19050709051e15120f060406080d02 67
    0x10341d81d4060a81688540c94146112019007000c600c903403541e1040c456900404d01c0041c0074540c052810003192003412203988204000042c103242104035121104058845004100009e00000120400d007030100f80d26644184d804d81c207000f1000024009000003d440c4d45d400d014268940c0e1241c49100a01d04600000340741e049141c2d04001d01d403503219042840000410f0035100c0314088005413801c1e405506091241c4142d8032086e201c031005108910140410981e40b8a00e1407940c0194040b4212007903540c2519070050b01c07201e40032000b9808244041001101400041c465840b6081c00c580010171403602d420000307030030140a0b003035503007e800040d041955407004108001e40300001000807030311022081c50503c1d020422898010010f0500e50050342c4482c001503456202c0d014060140800030b200c00d00030540c0003164000101d44401543c0a0000b0324040601c0c07001c0e07241681e50300010080d2103241641c4510003240030a030040c20403038000340c40b8080803656130f10600407805102c107070ba80101 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 971723983 1250 971722733 971722751
    0x2a08070b06090603030f09040506120a1209060201060f09050c040e0f1e0606071202030906070b01081b030304120303020405040203010801050f150d030e0d1b03260d0f0b060c01 77
    0x40040c0700b024003003e00ca07030300405c41001c0500d203050a4682c00c000484002401d40c0c2c0b0040800d03460140c21a641c0307001e0007504000070400c0004145620342c12140d03a00e0010391510f80130103a007240e1040c01a0f000d9402141803c000d102da8941100e90710042c0c619036142440e076540d000030703142902510a90002c1e03c0c10010010407030300c40140910501c40507206003000740dd102c07000c9403440c41031400161488407200c080017003060080040b80c000d2600544025074030062410310501ca00400c0c01144118000d940003604910580c0d003896a100100502a600d0a840c04450074805000303c042101410b4080c000052641d44ea44003a41c020314004002150b580340c03026511040810042c140384180052055040494460880307c1c1d4000b41e03d410419160881000040c0d649110580c00070050581c0c04203041070007660f110307100101c0380b291a8400c03c3c2200c4200120f20b4582d0001c080e40e020300d0074000c144003000c00390442c41c5034180e1154002061051000803e170103500841130100c2580d11041c1031 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 971725233 1250 971723983 971723989
    0x40e01060915021515040e030a030e060c03040c150c061503050c09270109020907021e0f060609070c1406070e0a0509010302010c2316152a08070b06 65
    0x40c401c01c05852015200711411a07445881d6104c02600300f100188560b49151441d840e6944650401d9643c0d004580d04e40c050400002d0141c13600d10000d005600070340e400701d044804140f040da03014507444040d5900b480c2c204161401c150342c00c001078030704001120002c0f5012600a10640c43c032400001040c5042c5400c505150b0301d400380c101d030440c3c000c01c040c804001e20507001c030350b04c40351001c014040502100d0008501d24003515040a001e50b22014100a01a50580020340009801002d01c09688003507120406540c560a07402680e490a800500c0000c0c282d01c1d1000f4440d0307001c4098102880c0c0c01001703458a4021740e4500c24540d200e64416000d000f10b10790041501044628126000c180c910f05042c0031074400201031000a06100c4034016201c02c0020040c0d4400340f01c91500c0020f00340405041c0400d580da51801c14540480c00049000f10301c8144400100d1003030841c546585010304807410982d00d0a445602400c80a6880340c0c60603400101107500900d0150300071054582d441c1012420 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 971726483 1250 971725233 971725259
    0x40516030b0708060d030c1209050a0909140d0c06050402120a06060e09070302062d0f04031205040602150703200304140109020d030c06200c01060510021f02040e010609 74
    0x4100c0c840c2c50440320100006c1d0b84040c3d0382600e56849201e03800384400154054400c06513542280f5030200946078080340200f100d5202280d03e60054000c0c2d00b003984c9400401da121440854813800013209410351001280ea03079084a6002480500181880307190701c4111800c088006404560719130b195502040805141080580c0001605000d810880d186a001501500c500d401c00061815000900507021080f00e4641c168180d00d4042141c0d10901c00488482035800350004542500c000c003c119801d5200310141d40945030207030005c00e10440021603000c46200c00401102c205526207104c1080640c1082520b00040a140e140c65260f003041d1804003a01c0344240083da50580c5001d10f8000542d844044200700a03425003000403a04a45040882c060215802d0840961b6888149229449210740c010b15004402c1402005a1500d407002c01039030340f550210742c2e030041c3c1c0403000c00e015084e40c00c40c02400304022464018581a41e5a018400c07440702603201c0000308211400801101d010502 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 971727733 1250 971726483 971726491
    0x3050d23100503070303030b060c010c05120112080a0e0328050724050c010213120b0f07020303240405070816050313171204110406050324040516030b0708 68
    0x15461900b030070704000c00d41c0c40c3e101e4403002e020507407100e490b522252580021503080b001800001c0c0141d46c620b00000d49180c2c01210203c0c00314094000005d4400310000d120031040e0b81c0304609a103059080c5000300d4607214506007441d0b041c0640c00355104103290b656a001300503107200c40c0e0740642104a00f40b80e030a0480f26800f080003c0d00e00d00580b110320b00012040c044140503801c05036141d41d1854001030090040c0c2c4418880c00080f52004241d4565503005e03429454880c040b681c0a0340c0d5400d80c600d4040c1402d8071000f02580c424400700707248094165180000341c0c2038881403114220000009402d131481a0350a030301145002c000e000170941560b014450a40160030018a142004404800f4401c44a54007500c1e0700c504041c180b4203944e142c4122907001e03078224014071142c1841d00740750103402000d0903900e200d0351504c4000507040c20041110015100c0d9940c0c001d14103611f14000c1d0104800007031049405006042000750903825008101d409513000e41d44070183c0785007a03007028022540c090 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 971728983 1250 971727733 971727751
    0xb0307050409020a090e070b03010303020c040513030e090a090b0a0203090606100c0b250905010e030c09060409050109081b0705011b02040e0304081207020a0501170a0903050d23 78
    0xc1400000358440c1c0e541803044441c030150000c0c0c510200c00201c7c0c00d0000039041402c8424001000106160380041c0002c0c1c1c04000300e6040001d0703101da41c40e0080503420108000e02003512040e004500d45040d640c80c0f60f020f050140082044203440c0d9070781140300c2d42100d200702490b6020003480380d2102c0030400c190b030000055902580840300c0f05405020b2100c0c0d1140204084d04042c001303102c0b01c0400094070180c51010060043c5040d507002c000d0b1101c04039004450010304c080032220309515000600c1107450002400324074498a490050202510368042d00340c80c03a6489031403950006103081c0041c81d05160611458505404003076030282010060342c045030421514a039100100c0b6408144099070550450300011030f203658002c954218040c0354000c480c1801030406006c42c2101c88002011001c0c4204c0c2c003400c4280c1c0b0f840041d40e4814004030421f101144603800500d0348080c0390f100e800303807900130b00b031031810552072003421001d50b00f10f1001901c010300010092942d4905c82055590407032550 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 971730233 1250 971728983 971728991
    0xa11070509010f17010f1b0e090c0a0c1106040602100506091006180806070c0b090313060c110603181c1e140301060206250903082b0b03070504 63
    0x11883d203000803812401003600c01442410041c6180c0c40943c01400c403007084480c10b10810204985142e080e0020844200124000f00c03070085183c98646000307031041c11464103280c01c01011540c01c55900310041d40c12074418898803074001b00d56071080e020f84020841170f03009003030348100078102500741e0303034040d01c400d008400d00c03c00e001d0421110300c0c440d8203071085840c111031600c00404d800c41c0c0c20b1050754041c1e0200c0c06050248404647d00c8582141000c1c0034040d12030064507800829541c038481c5195050042c1c0705100b0502085102d00e204110050203803a0001d400d006070740014146501c159007040c0702d070588105103040444284072824141140c2c080f00031000589103400350080c0000d900c1c1d0300c40100c49030501c1c64505e014000041c15088034598141e1250b84a480c00ba684500c11f46590890f400c50030511418140d280c10801c40350320190b0f950b40001460740e61141e6164003e240148421391007030b0039822401511010f00207600410302c4012446e82142c2c0180744c2058241d4004500640c10 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 971731483 1250 971730233 971730239
    0x102040b0418060b03070309031e030f15120219090e060403090e040b0a0b0a0e0a0207032703082a0703030e0d0c0e0604090b0c0309070f05011d010e060a1107050901 72
    0x41410b50364411107d08020504581038541120107901a0160140c1307030303107010500b900c01641540502d032440b414810401c1049140ca0701919809664411100003035030081a1a005003030219050700400b54840320740214a0700e40c00d200041e04c5800e80381d40709c41e0b40410704110503d41d00840c1d080041c69200034038207203070401e80c031102d150401c0240341010b8030341c4500814020362102c80e4102c00a128030746074017480381050000300003c0d60124000350002401ca43c0c13992544d20304548140d10f40e0740c51000706414035185540d450b01c141c0054606003008080400d03081ca0701640f40d1440c90510480001505c02a400c43c074000c0e2070040320410f032074081c030104002e25001410310308800040d1000c17030100814540d00c650014000e401410b00042c04d41001c0000d0140b03403000d10b03003d980143c80707410544003015100c00c06a00840c1040c0300f001d000a0710102e5403041032200f0307140359038145010b150620744c07109401c011808681c8480da41c040001e40e12103202c1c55045003401030202074a01100c88c00d1441d45 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 971732733 1250 971731483 971731499
    0x5072c09040507050406031b1d0106081306060b0901030f0c0905061605123a05060a0e1006020f030406140a1b4d030c030102040b041806 60
    0x444025424010601803000c1414803504100e00c030010400240244000754903494046e00c1150303004881c080382d85e419036010465100e2642c0c0103c03d46002e101616a6030b181c483c0490707182c8406801c2000c2d50300c046035614040b4460340141c2000d40301d01c45103a90340e50f004900040071150314200c21040c9510b0601a201039035841291131003165002c41c0c0564a4450411300d2041c04074054200900e90303c900280c40c0402d1540c03401134540c44880d19990344491800003418a030910b50a184003d6941c600d94410700c00f0001580090b41015001d820824400d07166500c0c801128000e0358401482d5014000420055904100d00b441c070022090166040900d06000540200d949141d00b0000043c00700d0140012f070700c142080c001c8102c41205d6130340100030701e00703010300d84040040740004038818803092484642400030045c56140c5400c6003446103c039030800e401000001e40080c2d540c3c1401a0400707104544e800340054005043e0a011300b40d595441c042402621503030550316200150300700b141c01c01c0414 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 971733983 1250 971732733 971732807
    0xa0c0e0f070e0f0103020c0607030b011404050307061202090901030303021c09020a0501050a020f010c050a030c020105070c02060c0c0904050c1c0302032d0703020f06010b0c370302010507 82
    0xb98090382e005404240c1440103130064051045144098450481004030407580764200141000080c0c13105115545440403101c2644601c0c010585c1560040b030041101c035200d8000002c880c448100d0060030245c034840014500802a0b1060f80001c0d0042952002803083c68884220312400e1007080085541d41c0e070102d121a9050f00c40c16050060120703800880500034002010b1400400008104107841154007500580000354001c0c006860000603049581c0144a807900a84042c1c692049100550b420800160310a1006d08500e0007401c5003d0816210300391401d004501c1917015085283c85070341441540400c01c2c0301071803ca07403032000c2040480e03004011206a06035544010400303030403520400115010704015000c0c910300000c0d140040c5070b40420303003802807a9020b0650f4442c2c1d0ba110003040f01030062a41f074112a810003041da2104224007001c603544040351290980040c6418001e041c0a04a0200241e000d80d440d1000c221100ba801000ca425441c210307610150080c0310760071060040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 971735233 1250 971733983 971734007
    0x60b12120d06080f06010603051522060f0603060815061f020109080c010f2004060c11150c0709140a1d03180918190804080a0c0e0f07 59
    0x601001510048480180c2c0102001c2c06000007180c115156284c1d409030f0b204000d1040100180c5040b011590220148541600700341b00188603030000a07050441109124400080c801040e03500c40000074601305100c0d402009006580700082c0591900c824a814284d42c050155564452031341040b82c4c03035841e648078403001001e896011081141d500e005a005040c102e0014140450208040000c54415004a540c040001d601848000450b00791050321498507a540244030382d0510050019a1040002400c01d038043c0088201000b020008100490800c1250302d110a8000070079000b5101d003000018003e04c1c4010f0100300c46101008140e244000c041d04425016481e00b2076200c02d80129000821a1040001525a513000c0000a03500c1c00240e086ca680c0214031050014100403044d03c414070038ad1103048085d1011101d050320421010340c0c806001c65502c1e2050001140c015002c10603020114400d0040510090400e00d4031b07100c07280c0c000c00258a0f50305107000c00c02c59503400004600310b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 971736483 1250 971735233 971735263
    0xe0a1509030c170618010e1009050c1807030e0715022802010507080309031908090d0c020916140d23040f02061b0a06150e010b0a0503040809040903020604060b12 71
    0x3176a1590741101c0d002d81034040c80703100c00d403064100c1d20303075010349643c042a80144260100c1d8014008401402544d0a00707600441000c800040010f00d020300076004240074001036070a644100703449200c6084100700e00c41d94100143c0c400d6024501c0c55001d80032030a151409450312a09400f0282c0c0001c107584a0144020521400440420010f2070200142d501406007030052416150700d0f041c008003102c03412140c0f0440c520a564998554600030540342403406d030050000d0302d00d541c2d000c009208800300d1041c1e10701000210f641c0d42008003c0c95001c0c102c00b00d2024804100c04880842a1a010015007040d40f80010750741c0901000810b44141412000ea0542d02a0f0301c0d0141c50740000100005124040320500a1041403000c105090b031041c40c8000307140d03824a00d42c42d11050450307006c0009024600070074a007044001202c500490103558071511500e00c02c1e10300354000003c90243c4110040443c0980c2c0080d0a21080000354040c1300000e01c000d80c1c46480b641c4d049800750f0707070311107000c1c4910030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 971737733 1250 971736483 971736511
    0x1d1b0909010e0417190c08040e0403081906180203060f060f180a12020409111c020909010908120c0706020a11010e01020a052b050f0a0506010e01080103030e0a1509030c1706 76
    0x1000b51f04070030b50700280000c46031010f880c6001d080c003030600d80c0e0482c0c15509440c1d00003042d44020989220321030640d82d004507494489030540f1100c00083d440602210360000d0f5030344250145643d04d07001440b034070000440080c1c8a8050181031f6461503030080035588940c191500034410504150070b50001c0e0384c0c0440700820500b02c80c1c03c18002e42000c00070041c0e00103090070a0300d00e0002103400d5130310b0020300c00c2c0c40d03014031541c0394a401801c0301c09015000303101c25020040c41900b1411040741c2500a44c02e903c00b40c0ca40b040303942d147c5040380d00040004e40490481450f417a4209030a12811a0144101c00294070344480000001c04a03c5610203143c00109210903d08803004440b50041d1043c1d0110010801c9041c286665203121004075034011b50907007081c0001d6480e5200781f201c444502e0f01030b140c0341c1041e421603500b56852000103500c0b0750040c81e614000103040a0074003482211141a03100c002c611410b40c1885030704000d49030461550603483c908405804100000d06c560300c0075403600140 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 971738983 1250 971737733 971737757
    0xc0311120709081207020307150e120705130b100c2105040302030d020303190908040320090a0501080c030604110f24131d1b0909010e041719 62
    0x10b02c950000742c2007494a885440701c114001c0d9900030040a18a0088045601c07440d07039401030f07034200c940a8215000150b0724014007461801c2c408580101030b5041803ea510305500d407008036940c445100ea2420306540c40ba40d002145082043c5403094404041c0b801100d0035883c2c3d151035401c290310100e402a101021415009903901c0703102950080e650050980360b080c400001c00941d00e8000b903031400e082840803071b03134028a001a4400e20800036444005203082c94035541304c07803400c8841d1804015884100740808207541d6684011240b080108110006041d4101a581c034030f40041c49207540c3c001ea00c0300b4144408243c2c4801601a1650212094070001e07404030040780c8a8281100c9546055051141261034401d0740c07000307444108003040e411f004261361006140450025141c034451001c035580e0200b054181c113032074101c45001c8010300c1c1915000c1a1404500d50b00340c240c1c031102d000040d41040c0b008020744910710300b50541a10030354a00b0004507140c1d1840e8148804014001d20603c11301039 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 971740233 1250 971738983 971738987
    0x1a030d1403060f0d050304080c0d030207030209071b0b0103290a0b01050403080715050604020a0806040b060405130f1b020601060f020a060f0903020f06101208041203020d030c03111207 81
    0x100031245006400c4064055162170440d9403a0030034001d08040b0300613020740b4110350030300c0040c11480a40540c01801c174030349140c0900c941558054a08410031181070100c680d0301d6803844102d03c0c041c2c420304a43c9102c0d80356040140004240c29408030f0504102e130501820b1070080010070341c01050081000801b1001440162101d21450340014008403000c00d8040501500f06208480c081c058442480780d40e854000300030403841151490004240c4100c08118503091a038000e0525050142515140940f60000101e081c20b141160b20f80154030350050103103050032400f80c942c2004800000b003020350ba0441d0085c0d201d1005008030b2007003103003074803014005c51704c01c224072940c95800c400300704404000002c2182c06804240ea00340c002d40306119028203960340005034144070ba00401c0c2690f040600f0252900c91034405840196048402404041010010303c080464203503ca600100b0000c01c41180140c15600130000480074035251030442c84240d100181140c1032400504902d45031a0307542281 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 971741483 1250 971740233 971740249
    0x4030b0a06260f06070f112a0a090e1207030315231f27060201091707080901050930010e0f0309010e0102030706050403031a030d140306 60
    0x300c0020612400d810307801809800a10104800b8505035100c141d2007140031a41c4000a071100b1000030740d0701d820030004a120321005400c020021040c0d608501481c07180f4044018030b40402d42c00c204620704642c00d03600c0d0000d09000204840c003014040c00740b4030700041b0345911511881285602c1c001a10b102018440c2d8015000411442d180d401156190540da9807042403100c8825a80800d42a0351b001710b10b0030303d0000503d903280740c1e046400c512003a02d084680c1c040b012118621109945603c03108030810503a40000307000e15900002c3c8040b5141015050850741a807441c0400c0c000308000310108900d503040307540c41e0300282407082d52070b00070001080d5699001d100f540007049510070540005c0ba50341c80c0400801034040028010714909504854850f104800b1145d00740d40b080041d104d0650046070005041003050056174180700c1c15440d420f068135012501200040d40e54118260210b0140d018040741e01008d0b80140000b001030b58020300100086d00491408000100c0041d04070741e51041 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 971742733 1250 971741483 971741489
    0x2f09130207080403031b020306071103121806100e070e1503040f1419021507051c0909050906070c111518011b03050d1107050309100e0604030b0a06 65
    0x90440d9900c8150a10581e01d400c240022800070354409060715450701d503101040c200d1900203001e00220307102c514047d201c08210340c610600074001800b2009449105510b400c0c41448603801c44014020050745503424a0002042c1a00f00400c00c0c1c400c0c810170b000640354540c81000d6003050317024800d82d04001008008096004804a9400020441003002030010002a00d00c1100c4450070710160a10180e2130300b154554807030682d034032042010b01519105101d5005c01070b458039803e191044540703500781000d0300301d803250a1000b01382c881283d00310b51000c4024024098a00700708407504110b8070442d15500c002c1c10050130040c070003a01d142400f940c80c450803402da03001069004400c1c407010b0405025004004054600070b000141c40d00194012030002c1540c04407880080c4c1103a02aa4066070650000516880502d5685041c0d140c0380d2a000014080e1306e000b40d00441d114a000070030400b522081d0107a903002c00001484c0701c8101d40b2500142c2e019603038060303c7e100c9942d1719072200e20014902c1354 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 971743983 1250 971742733 971742769
    0x9061e200a050d0e071203050711010306230d0204020a0f0e03150718080303151c0309120c030b010308042d050d08090303040902130b0a020303160e03070e0a2f09 71
    0x480e4446c10180c010000b411014802e4444224100c490401034040381c0891140780c45036030317204280e00030316941f0f0340024480e544014503694a60640360041000c0303805c902503a10218030910368030842d0a410002e00308201004800078416140301107680907034400701812081c01e03c414030400080c0580361418120140001d00c0442e40c407480e200c540700c1c6032640c101e41a43c0c042e40240100c0da016a00c00300c1c0c0d01031003a8254855030035691501424256080d46400c0c10384220008050100020350074215071030007140200030468545040c0032820301c0030008174185140c030b400c40c040380b0b1a55840b44000041210704c11203803891a4045030901140358482d6003050744d414000010042050b00301a13002d0300c0c0302c00948000303d00c803503260800b40a1a1041601a0f00582c0c41440014a020505c1f09402044000c500e42007004460041c0400d01d40082604036002e0700080000f080404902c0f4441c41b4500111110002243c05012850700c20948651000b2070724000002601042900c642c0c0600240907814 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 971745233 1250 971743983 971744009
    0x506100e030c0d03031b262805060405070e030a02060d090c240903080906030406020c0105070324030c09021e040303050705070e01051309061e200a050d0e07 69
    0xd403130010001c005001c6a0403009481007102d60580d4403030815060206121a100045000d100c61994032000c401003500c80382560408001c030744260315441c03030642c03108104400300d0b150030454100000d0300c400401c2d640800c0400400841e80390340002c0d600c240b407070301910201c1d91110600e00f442c0203400e0b121001740c406040c1306000209404140300100ba40003120342210303100005910f0445031074105101c00340c100c01081c8005105843c00e10015508103100b060014600710b111544030782910821210000800d070740b82c44148c9041c80d10b10300040e1803040d40e1000d005c1182035a0310081c01a41034001d0845641c0d000c40c1e0007605800e04040d44091112044030f00c0c1d219903481c03070010040d90203c04100e036180185103000550100d45604641a01d500800310504907011900c40401490303058800e4803019154011000302610708080c90400101042d404a1400090a040030170304102084014402e80100030010f60f05510000340c0c0d00408040c00042103200b00c00003094904141c80d00916160804 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 971746483 1250 971745233 971745259
    0x1501120e1507020102070b160c150203070905040506150f0c1e07080c0d0f030c06061409090303040206070212010905060f010914043305100e0a0506100e030c 69
    0x400611610408074400c222001659540d000324242d010340d82e001046456104080b03141c0980f41e070b040150203407041c0b800c84c0801c0c400e6169465040c0e01d10851a505940c00010300070b007183e2004c03410700503007000c0c0d80c00e01040c2010070120701c8201200c05000000000031030191504480c0034222594001201d08680c0d1001404182c6400102d801064040350310640a00044c81790001c16045080b07175006002102c990f05079154221800b007800300441c1080b418031185070005549114043c0540100d0f440310f1440d0300031100307016010001901080d200d6000b4800c01c070043c1c0e07402d801c03104401d81c141c50312031408034131004a03409442c00580c000c0c0f281c0620340c00c11100c0030701004068129200c409081c840c1015020002d0401d0b07109540c041e2180d040314a000e14003d0910081c02c5481000280c0c250b00d081d00010240c04452040e80c0b180741c0e40c0400842000284421000c240c0c000300c0400d010016814002c0001d0151001180400240405075210007195a07050013004001507024001c60b40340b01e0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 971747733 1250 971746483 971746511
    0x40801020c0123040507060503070216060e180108300a1d180a2c03090f090c0d090f020607110415082802060c0115090b0603150112 58
    0x3c0601d14031000d485481c01c0d040b0a0b581400f60150180d03030050302034404141840c500300e503c0e03031006040d0415440380c2e02c8140700b441000c1c0c1e0b044c00201010341e00c0030910a1240108001726801203909108000c400e401440307503c60110391070350301383c4103a00b00c1240c1c05903060400d464424070081507156494041040740c41540c0001c100d810407601e644069090b010582c0404c14484603030b440c140113860f0700324009906024a548444c4456440982c40e03014680c2452118408101400032144030750800b0405203003c0c00c03c10b900000002c012940807003280741c100d003480d1040c061011001140390701e50303c04c0d200340601c1d030780500542e58005d08a02d5aa100a06208000f4503503003039900e01951506260510308900001640e056070300c4c420141007040a21440001000c034488078440510003a2000200103070788813001060380b0f071101d034008100c0b40109003e03414191115484428264108003401c621030fa00d005c100c9074000c071401010304040d0580c00040b07500a0f20114401200351814490f020084 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 971748983 1250 971747733 971747741
    0x30b09060105130612030e04180f020301050a060501082a300601140c0708030403030f0207060503070e09090705090a06030c1d0103030f14070308090c0f0105040b070305040801020c01 80
    0x244160340c101070fa0002074980d034003160050303c103038031003803024002d554002442050500100c1c2402000841c1c0b0660511850080e449615002c0301d05140c9103044170210b080c07e00402e580300312415003c1001e18900390010381134070340040500c0d5072103a411000120551004865020441000c84107a4440c0b44024440c11421112007000320054a500305481225002d500c08511501069541c100f11141d0251104100d81010a62124074020500301090348041040a08000c40c000d5440501d40c403000c41000e8202041a040002080020020040c005400c800100070f0a0415a2808400c1c0d86955201d030503c400f5400c5990700c4800f08090003504000398100d20196402400c03041d039610760714210307103610f010141c1ca540700d01c0c03d40c10010400f0900903004440841b405081501040c1d000c0c1604c3c3c400303a80189401c9000c41e0a20083c815052020440c40746281816990003202200d07040c00a0310501a910034028007460000c1c4102c1050702c6003040c2d500400c00f2038001e54a803440c403d41c1c0c0d03001e4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 971750233 1250 971748983 971748989
    0x5030d021c1b0c05070302030a0812090c010c230a03031e3303050307030206070e180c3601030b150d020d02120901060806010801090309120309030b090601 68
    0x8522070440010746480640305207180380b07010307070209115084242000d840b100f03200903090300e0b603000e40d80d000000b6840910110400234416040203a035110110380c680342180e0050304019599004020380c0619076000055204081c1e007000402d84090325442c104045d4450a00020120707008480c1c05400305600354100d4007810003060a0002460300ba642d83c0c0d02111404da025144c0c41c0b012004140e0180542030803100d40c0e41404818417200b98a9441d601e266a201d00d0080f001a031118082214007584120f4000c0741d9101260303c818211301385d5644031407007400078021400d440d00000d1005120314110b00c41a558120821800e03000003401f8034501c1c0149880303030a0601207410400b43c1c1d040c0d0306d403c070650f45280309145001420107402d4220f82009400c11003c0307aa081e9820000b20713100c1415400280e22850607a400442c0e03050030084007608000060380100c066a0500000c0f1000a0300034003114143c41403044600b4240c14241021501e072a00ca900103030a00c403400b0305210b10227002080c0a410303 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 971751483 1250 971750233 971750257
    0xc0905010207082107020a030231020c0d03150f0902041703090607060506041512032a02040510090501030b1609050108060f130501140301050a02041a030a0905030d02 73
    0x1d10f550301403242e1202c83d0032401e45614055100d00040342c03050701c0e01601d101030024000384e2403070781c680c0d0100d0032002e906540ca0000d040c5402041407034800f181400c50b4802c5c0250300a40c1004500318000703558160b528808020315454501c0701c00382400b0281e81000031700742d061030110b46550b03070200400290f115001d54a041d0039200e00c0082030060000488411a602521007460545591500c0001340800f4080aa03c42e0300c428900004020400402c0c0143c4403c410f140c1080e15149005405601c800e1006c14034540a01c885030345003000b51b80030007002c0da0103a41c00b10303e542d1001c0110a4480350340c1c02500c034440c507080001c814842e6108c8083d1242c0d0350f40380c4956003006018415105c190b0a0b100341030019014400041c100c4c00d1803000c131000c110025212aa030700c0340c074807076060036100300341c00803844a000d08408400910b8240111500060b07a00300840c03801e81400b281760744000c000c400140144000102045044c1d14941c0112b51803500002542c0c2c6032044501080301a40c041800180 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 971752733 1250 971751483 971751493
    0x140a051f1401030305030115050d0903110105060906060301090213091803111203040602180d05011509020306090a090512210c03150405091f0c180602060103170702040c09050102 78
    0x410254054880380c143e81e0180ca6090860307280914904141c107600c000502044000c1c4202103401d4060b014140303089200340c03101d5801c100b02111180c01c40304010b0190384a040c140d024070a458131080122415a001c48601582e256210601c003010025240c0c4440002e91a00303010010444040c2030b0b0b450380600c680ea4110040d22026002a9181159050711005140820208000443c40e60003010b0001c800f00184e1040ca90982c00a0b401c0d04400c00b040d14140d44175a0359003640201506440003800302a042141181401d10116942c600c00801e007214440d42e070071400c000d00c40100880c40c030740c0540c0382c41c081c1d490040400c8455603800c071030455035400000001007800c0d4201c2806603442249882440315282c6c42070380401c000f0701805032404000340906500b00d220410102d6a00b00700314240b460210300511111402000c0301d103001c22101024000714814000a54045142130459400850900800b00e111800807654491444000d605c0307454400240b203929008034040045840c01d800341e507 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 971753983 1250 971752733 971752751
    0xe04090f0609111e0103050a090f0605250215071419020d0c0b0a0b21030c0c0a051302030a14190b0105160b190e0a0c150c140a051f 58
    0x2100c4004181001d034800420044c1311031255100b0b03807001c0da2010161001041d01031450301c0302c415a014054042e15070684075010400c0340c16606c020341d6098001c61a580100b108048802520341c401c1c030f40d07801c4540c00001c011407003442c410b019050030511415412592043d15500250380c44c00004040405400703507525031240d0714000c04444030f00640048925007075a0720035508800506003031001c5503122100000e400c144040c6080030b10240d1032200300a507942c015212041c2d01e409039004034903104200d5080c043c4255202c0b0041000001e03030b144400360f02c9848881c4080082e0001040011b130220240d0200502d01d44050804141050000010000c02c0700f41401102c1510900319400b64004202a00100050205113101d50140158041d040e911a801001005607019840c207810309500c1000c400b4180a4170181d20390041c2003420a100e241190446d001d0141c81000700c0180000c12502031200144000b808203d04482c0d21a0944485d0144110031082030080300c0800801c1c00c0c41d1007008 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 971755233 1250 971753983 971753989
    0xb04060306080a03090b07150f090b160903261306120e0c0d0503090a030b0f070f0e0105030a0b1503180a02090a0c02070e04030203070b090610060e04090f060911 71
    0x742600c5505039640d1700c40c2038102543da501c17645c044d04080380e000440d03031060b503001d6005110701915203034406808a420213803428080c0440001601c0007041000d441c2e10a5096034012201d8011a0350021640c003154000183d0040da00e02c0b1741201c0c0c2d44c64840010043c205404032002d1506441c40c5880b01a882d05107406e410040b604200c00010b516488417401045520301350318216840741c4114201e91521f51403d0125040841980c070488180c11380001744110240700861080c0d20040a16205030101440d0b2002840c01c13006003d52814400000b001c03d465840c10341142505c490064214030440c4d01703200840d04503074422a20200340a03501803081303803514804145140501c0c0c00074426079403031302e4049c00b050040c00070701c860006510410500044440b030480300544514001c0d0081c584030100c3c1d0a00c0201d0300740c010000074040d04520100110704c101490440155030880c034065500d4241007012030000c000c03c45000d4058440f540030401041103a0b005070ba89140306450001e1510202024 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 971756483 1250 971755233 971755243
    0x17030a05010906080c0a0506130308040b0309071a03040605190c020c040f09020f060912120901080a0501051e04061e183606112a0d050309070905010b0406030608 71
    0x51790f41d00c910700b2007040185241c208080d190700d208440044a000b40e40780d503964410303400344d403100e014204040304000ad1240144040d40c01003100a04604580850340c0020419100040c0020980340c1c0e44d2020821780305443c007c10700c4a808504c0200310445503000040e6698a2039152503100c2d60030281c24248404481c084c20700c4540e405800c101401c01e2680400550340c008203845500881041a00e000494040001900c845208009150b642c0d41c036200040011100a000005441c108001004691509240d4140e0340340040203500c0c2031040000003401030b1000f030340702d048103441a112191300d00e02d0444605040320419402214848041c902c40416274103c0001c128294590001c24800500319600c07070a9a013000c1020020400019603e50048580409101045007000300750008940c404881d0085184620462200c002905103032096540340c2282441c02006800b0000c20715950302048400c0142050400c1846690307125004180190440d101c1c0e4400241041c0d00000d80103404030f2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 971757733 1250 971756483 971756503
    0x30233033603040902030c0c150109060603090f030f140406030c020f0f0d0f03180305031807080316140604050f0d050f040b0a020a120801090c0201020c061317030a0501090608 77
    0x3071030420345070202c4c403c0203400003850122450b10402595408001c1800203000a44c0005985a400d50400300711508a0384280c1060b41031600c0c4c2410070000c101000203c895640e40351070300b42481130051408484148025810100110300858040b038415055004250950740b990300311003c200043c6440f035030354821090f000380305420901e1809040c0f0701c0340001030b190354203c1c1400b2034080c40c12881e1803001903a1040030390000d80f0201c148151800a1025400b0142c0b1840040113481c0c01c204107203480c0e2186010320480320030200c07030340004c01503152904400180401c1c00c0d10b407070740342a04009886203000640c0e041d2500600d41c0004500d80281c00365081801c200c42c80c02d0030207041a40161035a03101080001c2944610110a00003550580340840b0442c21541c60b4409545400d80760002c0e9501c0d00d6000c0b00750b900501c011190000700040700c1e0ba0150b9103420b448003c102500f41140ca00b02c180041400310600001007054800c015041281207541c20743c4204500366488a4290700d840701d01c1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 971758983 1250 971757733 971757841
    0xb011a131e08030408030a1d03100b1305100602061e061908100b03070909080d05060a050d082203031b0804050415081603023303 57
    0x40030502070301400390641e004000300404000c10341502c1d511000d18507080f42c0d1081101c1e500014500300d01c154800401d0b1407211511060003250b82e070076000642c07101510b4801d10209603940440d01d40c5683c0d480180100002030300410865802d01c1007900005000c903004010241c480c40c00480d0b0b880c0060942515160707e0301d242502d07035448034001c02040c08400003190380b5000b060340c0042205582071240115840440c080010540c0181c010703d03041c005542d001605852403d010f02000c0780c01007040b14543c000f108030000e603513600d5800044960046801c40350b00055004554802c0100f501c0c000d11280401100100610001c0da0032201152298000100003520300d4821050002d440c40d0442c5619210780c150b6070030b150b02c0b940480e0886040da2501c0c2c0c80c0d040b03501020007100038113100e4140444000070007002c0c0507081d0740106400d5420b90804c042100b0f02040068070a003100c0f1840d94005074001c801542da400e1803081c0f40036101e1003c481d001000c400b08050040308008402d4010094510 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 971760233 1250 971758983 971759017
    0x712060e01050315093003090d0f1805040908040305061017010504020d06052e0905010902130b0f04030609060b04140603060c210103031715030703080705100501030b011a 75
    0x3080e01b208070030b180c210740344480281910400408594901451090b000c1d000182064850142c0c000c0800111304950000d01c9041614600300c94202c60068ac203071141540c01103111200c901d0103a10794401d40d40040d2260160001f070111584150505004840c16100d003004445003202200b0b0896006490003503015410051a4001401e02d4101d1580030382608400c0007000b0f0360f5000035161401c010380300542c6003d905400e21990300c1900c00e09000d4121818214100321040640716071146c054003070b0001401f00426000301c0044018211005140c0c4004c0a200b40c20851801c0705c080d12085200f148214200585400300c036001055151040704010018116500c0342c51080c0c0240d4030402e1600c41d54882081c0e440c40034100c000a40e07008500ca641e6600c001000c400c0c41c0b026202e4041d00c0400105551030004140d60703000204c4209598000d246180e4412075880c10a01d04044440428400381c10140000140f004a880c0b0504807550300780482c500116840c0802c10307504c42c400e090981070100e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 971761483 1250 971760233 971760253
    0x50102070611031219060824150f03120c071401030911060c010f0203090f0d0f0504180f051611010b0a033c06150503150712060e0105031509 62
    0x200b0b9020581104c510000c0c140c490b48580c1405c41035846a400ca42da4540c407003d500b07454014800c82d0803030041c1d01d0150062107030030142c0503502c4e04080041c020703115961484000f51655000d0014540340350310305511070740c1c0b0100c40803a1a21144103209000c0741200a50300b01e0030550082c002c00c000180d00c1a894042d45c11800d00304805608490608201c96680e00d4101a004005100541c0502e007040c004180b0320700400d50613450508980c07251401c010495030013052441d0032006503010307074880345203846100310780c2c90044e0014941c81070002e4a050030300050242c045a41030380c0c1400e20307101d0303643d849510502c00c14041c2a5103400f5103158003c402d0320030400c042600c4030040642005051111410748845e090107052800c0d0054014034124455604002006400d1089010710440907044083d907d10300380000c3d403140142c9030400301684181c00003c68407441524501c1210124031001c11485480d402446116003090080724028400c140c020300da00e04c00c4a009602c11076840c0010010942 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 971762589 1106 971761483 971761507
    0x8010204030c1811190516030509040507050a0e2b03320d0b0a0f090207051612031b0c1212080415180206030c030105010207061103 58
    0x8a0820a9154120107a05507030180c0c540c4201820b240c01e008805a82d11f01c51201c03803004c0861000c10301d01c1016001000b8100084040e02c04005d81d1342e1b03108080c2c403036100307005604010410008405510f440c0c14581c28540405003601c6010310314104201d55403d420a460840100d40900d005044148100d4055410000248000441084c2c0502c1424441c4078042c40c42c80003a4581046005580351541207070000c1103406c403242e140036074600b0144020340140e8011100d9001d080e00340c2725503040058040b000c0d524911203645203034859a400740e40300d00185200d00981c64161407103002084030039074008020140751500001080b4079150501584900361428024022900c1c1440003281c0f601e40600304846144000081c8039100d04071b540d140600c9010025400140001001254a801406941203803800e80031a0a030a03180c01003074841003e03d460200340350f441485070101c545 = true := by decide +kernel

theorem cover : BRFrame.Cov 971582733 971762589 := by
  have h0 := BRFrame.cov_init 971582733
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971582733 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 971582733 ≤ n) (h2 : n < 971762589) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
