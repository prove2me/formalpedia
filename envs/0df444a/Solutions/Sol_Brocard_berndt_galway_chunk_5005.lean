-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5005
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:26:17.003736+00:00
-- url     : https://prove2.me/submissions/4a36ffbb-f087-406f-8c8a-2b74f46f066e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 900000000 ≤ n < 900179856 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 900001250 1250 900000000 900000011
    0x203071e06230a020c150c150c0906030916080c01110d0804030f1421010501110c040b0a0902030f060f06070f080a14030f0a150302030d110f010606210c0c0807060f 72
    0x106c03605100401c22200c40070115510a03941283c2001c2015040b04c00300b10101080c400045181042802541d2007501c080030b540158000c400020001d003181c1d00700c80a603520a0384a0317a11541c100e85055903000c0d4120040c049160707484002001c010380200010200001040208199400b442c111402c1c4044e82c034407035407074800c0415951081140398166210701d180782d0300006247c0d4010020a032150014001815040c1480420300020384158130300150049003030f04e000a499007040c0702071401031021901b82401030074103404201603004076800d110702c511000c01c181400290003401d0b461606910290032511022000010b0760110424580e000a4010000130031401492581c1801d03c01c100380f41c1d08001404503601072043c02e24003800025010f1707201c1d9040c03842c2e4600807584460482000c900312065294002c0b00107007526440d038402c0000c907034040b03036102000381c0071441902d070562074031003c110000b10720310010100744036414083e001031800191303981484104d80141c85d0800d660032080c040c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 900002500 1250 900001250 900001279
    0x100506220609020f271005030c091002010e0c01080c091314010e0106020d051c0902150c030702040608190201110c0a06080f09150718030203071e06230a020c 69
    0xd40317030b00c445440140021071600b207803d418596468000215009004601403040160702521581e1000d080d010421509000074041039441c0303400031203010b00a5001080244109651500d800100c82d4141d040c41050001c0007115100c7d101600c1d500002114014a5084440700380c50040c80c00e1048c1103501ea40010010403900818a0500d0480d11154211000000610f01c12a80ba000da640800e40600001200200b107003510b03080340c204c2c2070004100c40c0d03000d00c1040000c03416a010201461603508042031078800d501d880c3c40b40800502004010340340e0000c0c000c2c5030b11185921444003d060024114403600320705010000112030002c090312415400c0e85800703000e0071b9943c0c2103459100c40c3c4d084c00005190400b01103003040307034802a0b0200311841c0d01c4c0e0910070744020b00d40c4a8130307541001c0d6410f000400f5a800700038200042403d0040f20342c191300201109204070801c0e40100b07040c4801d420078180c5210410021401c0910004025501c4076103580040741401c84c02c40c0302d1507114004040410707 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 900003750 1250 900002500 900002527
    0x50108122d120702010506010912031e08160215070302070804030b070c0605060303190e2e0e030a0503030c18040516091208072003030c0109030210050622060902 71
    0x1195030380c840302d0040ca5565140e4100c0c2a940200e0724a4000703251850104400c0307410417409910103101c0c0c100a00425940288203d900c8415010345001811755070911079229880c05000c0c100400d684094440c10180d040590710045001d0018400c1540c000f03072800500500d1000d40f40510f40c410f004010b80d081c440c900902e2002110015107420345401c01140321407500000b101c180c10004031541c80a00b03c0350b9801d903000007801040716007002e448049500c0c1d21a01c6e908e80b035101e400201c42002881c4503c10000d2170040f20120090003a44003000d200042840001680d52200c403410307113965107461181c005444a40380e01d00d80c50700241002c0c1446081000c4e00074110b0101b14036a03418003040d40d580050040c80c01182c0d00900340510402130300e008220040b0044203000200420008040b4660001c00d143d13a215403407013540c43e59900303000405c06034148440001c4040580080c0b1860030124002620300b030705041031400350b01100a02000e81d50f1207030072040042003d443c0440d02c2d0440c80d8040d0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 900005000 1250 900003750 900003757
    0x60103020f0109080a0b19060305011e020f121504050915060f100e061b031209120a0302130806010902070620090d0c0e0424050108122d 60
    0x220311a09044038540c1c05544502400000c41e4006001403000b2203450f242c8811511001c0c05010b41040c124000c111132007682e0250400030340c843d80c00002ca801d1880708845d603400040030040d0546004001c1120721458003403c0d1596080c005940c80290345407594802440b0b0141e800d40703600301d030501081050030280800d003035600c080303c0c8428102c02d60b074850410511041c0c0f8001c8a60280203110003900301803003050b84840e00c0b00d025007079914000390030110011110900703a0a10090340000307151000c074031840d114241c021a0540042907400c42d0b202c0d402d40c060040307401d00001c150f4003141c1013900c9004101100b0080c07010206032030a0b0b5031124900b0001c0c2d4001407080c0d03402ea06202040c07010354003140101080604941000d804d010901d410080008040c60040c0d850004003900811048801c0b040d850245104000241c0040a4225614007131010051549242ca20344801080000780c0407907071000451250480c4d595600c08110259451540c078004810700f03840c1854211101500d44004 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 900006250 1250 900005000 900005003
    0x3060a0b010f140d0903030207050f03071403090a1202042c0c0f0a172a040e0d0f03020c030f07110111060112060203070e1201050703182001030605060705060103 71
    0xc19122140641c4140c400d40102003040c9a42e0204009020748498640d000010246c442c1c40e0240c60484030f07449540ca401007818102469420000f04401040581450407800c00c0c8100059410315400704001104449240308120102c0d500e032a50b60110b56543d44200b454000910864214001e02d0302c5a900c0740200c040d5141061103628140030f0240342c5810002520803004008005079030910580034101030040ea80b841da648107522045010642c000a40e410b60312001d15200d00320f0900e0070401054502c4d40b030441505812840d501310f07050707602044000300203089007005070b501c160303940d030840c51440323144500c1e00007140126921007044028032800d15a803200344d0362403491a0046159a07140d544c01e03c1242c0c40b5403e00044400000d2440c0c01840d0710620764108000c0b00341d07103003010032405143c500048065954500810940039010b100e40c81924808040518503044640d40312a9038002e001030b000741580295540d09100d030701c41e80100014000145c82c0540b94040340c60200c0d42c4860a010 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 900007500 1250 900006250 900006257
    0x6040c120207050c03251203020c0a03060b0f06070312090305130806010801060e0105010f030906060b041403011109030307020f04200403120c030507020609010c14071a0c030909070c0203060a0b01 86
    0x50841c801e0000c0c80d00f407000040c0b0031b40c10303140003131400c1020154000e04000840950054490b4070b040e41d510b800e0443d00840c0036001c023144100200c01000010307004854641c0c440c801c1031106a0200340d2001c0c1d074850008006034000b48030002d6060030b98990180700100c0032440110b0340086090a000f203201030407101010000d00140d51600c06142c200c5109008081c001004582c003540c41c140319401c24040c581c011080054500c0e120a141501039025400c41d0080f030340034038410f00c020b04007442a0300c5001c0103c1801401d00c28208002500c80c4150040a44038120118082d102a40d40da48414107a50100c210441c0000040510030310540040c482a50500c04003420200d40d01c6c085c19200c500d01d54150350342c41c41d01c0071550812003190040e4280f00d04015a04008100103003000c05a0800003036000020000c0c58a44015600304a00444800080c02010722001003180c00000c1558100e0400305e80380907041da1415001c03211030303084030406541071142000380f005e00042540400c090328005c0e40d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 900008750 1250 900007500 900007513
    0x6040605070b1005010c02361f0803031807091404140a0302060105090a02160501060510020106120803091002030c1201141f0c08070c08061b0306040c120207050c03 72
    0x100700e03100302c2154404d85002c50b24500c0d01c0c80c01403401d4941c032040e042c02201c5000c9510030740d09100d442c100c10306600c2da1184405509105407112420b0152060aa26204082400d82803c4c021030701c0e4080a0103c0c1c150b20300d9208071620204c42808880050000f442e8108080903640703017100503249060300d05903403034042d46402680c00200070030b440c0c2000b50190002e242d545d20b02000d001a8940c001c103044034a81d800d1005080d6001201d00342c1c51080c1c05400042030050600081001101c4006000780035680341003010807955000f90300140203d038000807038584070341c0c0300400d283c01c1900001810240701e100000b0400000c21a0000d40b50801710f800e00c03900d42da038030390000400110150003070560110780881003081c0000c41ca411401075004501e4901481001641e42d40395941150200300e8002440031828000c00c803041210070750140125900b00510744041d40011814400a000a070013552110510040301c2c2c01042e0001c2800ca040e0011581d07a9018245161070b410f10b206034a200c0d01400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 900010000 1250 900008750 900008761
    0x1050907050301030f0c210605070912060903170a141006050d200403030c1a130b100b040e040201080a05090c04050405120a021b100801050d060b06040605070b 70
    0x1595548680d14a4844510b5a42545c6460f1400e01d0340b41000c03290300c4080c12020400f130300e00e00d0000585c81c0892207034084c4c81086107000000d4440090415003040b043c40c4040008043e8207000301980c03900403400107401411410100c0340b00003011203040f0b808001e030041c00382d0310107158070800303000c0407000d010720481d22844100d144003c1c0d14882c3c1c00000b20140b01e000b031280f095a000c6084a589002d0782c80d2607454190741c044c902d8006a2040d00800c0c01085c804d02805202002044018201d502919480c030303003c81d8100600d651450064030300c404100014032120307c9031001d007000c0d188100320540c445075240d04600d4200000c4908a0000d110180803c0040e00c0f280035990007800782c000a440d085112105200080500800a8a052040110800850744603a0080c01024110b03409441d81140540c0e0314038541c11004e40f828061000d801d5030094882d8003140240c191403040340c0c1f2920800c400d05102c4060007501c071006601c490009400502142c001c1c00802400c0d1003210340031055a02d1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 900011250 1250 900010000 900010009
    0x2d0501030603080a08250e18060901060c11060d090515061e010e1c02010f0203040e010e0c13080303161706040c0210065a1e06080105 59
    0xd5100050200303206000d2884c020780614540303540004041c0d44080d420f8000700c41c0d174200c0d600085003030000c0303902d84480e4881c030b0801c43c42c406002e0421003400e16460a1071001320700c0c42001442800c080003913080b1140e040100d000d02c0d2650030140103001d580c1303035005002004010010440d00306c5040c8640d160303155030594000d00d21392150100401c000441c11100d0201e071000c500038400d9030304002c044100800380d0340c1c030b01c07006285081d050a90000c1950036071001606c04144240e2070300c20366005000400c0f111651150b21410360b2000c1c2c5404a207912201c4050000f401035059100340307112000c40120302400c00001440c8240540e080900d1804482e1205588003c4101070380709114102d44001503182c103143c1c204441712005441290108000300700c0f100c049800980040f14200c03104001070408082d12401d601145030080314100c104004400300b040038a5009a6452940003818010003009541c1c1013000000c01d80b0860740c040803c2e021821040e45400760203040085100d200020809050 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 900012500 1250 900011250 900011261
    0x180606010c14250914040f030e0406080f060412090b070b040c030b0c2a03070f23060603010f0606170a09080c011a030f0c09040501062d050103 63
    0x101a12558031a0309192600c0c48142145003100d0040c0c4100300d04107580c07030f140d21078440c2c40042003503003501c4031820406400103079110300310a0032401d41644240404208134004107c02c83d68035040220700d07042e03500046006040d243c0d02c403110a0040780004048028082001c611640c417503180fa5481202941054541c2d00c3c150280d204074120511000d030008070f8100840350068003c00390a214295a60384018000e80201c44001c0c0b400d1010030707202d003502194040000201034407040c011204117107c056503a83d00074041e024002c844d100c030711141444030100c4841000c1d0105462441c880900030910366a03120306031601406986000c00e19922049a846003009a03681c50b41c0303034901d4040304c82c08011000b001a00106982c0d503114030150004040394020322a0320416800070910030030b0004040d100d0406524024041c1d00704469450005501262146e01014222886040c58499040c076034010540d581142441c070400a145824003050009800300c45d2104032070240d070082c3ca40e070044041c0d81 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 900013750 1250 900012500 900012511
    0x807051509010c0c0221060124020d08040b100803190806030c0a0618080318010806010e210c06070b040209180c0603070e090403030204170601081c021c081806 70
    0x601440c40b0200514000a5920a40040c1c14401d486c3c4041c41b1302890401c10203a20480107000075801c0d078295100071501700d56082003a8005002e400604600181102c44010030042c03c00040c40c00040340c0181e80621403000e401300c8411a51100030300d1072507801198401080001107251f03c0c0000d20140740000d8422800e840180102cbc0c2224508041a41d0102244214142c50040e81401103000d01040020304a8603ea80384120f46d0107244100240030f0310400352010f410480e000e01d050405132038160185a81c0c23482c41e001401e030400c08445040c140b44040da80540d121100061a8091100b030b041c00c20300a0380200c800081549904041400c03801c1c003d4200d210582203000e059219241c10b0000c1d41e482046803c0407880030943d800029003440c41103800304c0201c1d6020405100841c08042d1820002d401400209995410154056500e40107140500b043d05194820410001d100f80a000e20403c46c40703900d160b44030400c82010309071800440303101d201e030340f03075511040d100e8030001403198021b0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 900015000 1250 900013750 900013757
    0x9090106451208070807230a2018070e06031005030111030f0103110f03060a050a0513051f02070b07020d030c030924021b0703021309150b0a030807051509010c 70
    0x102c035175541c1035180c0c00510040c2d8160040d84441c01b10015404040102c028101c0302511480c8940c0c540501c0c16181d82c0c407540b030030022070700c0c0614044d114000c5031102c4070490000b0070314980e581a005c03940300c3c2c2000d5096400c690b0200a00808011452082e02500c00883c001d1010103d840c0c200e0169010032210380c06244821300040002c500100c0b140121410094003000d90140c4000110f40b40c40c00a8a40141550b40d85040043c280c0b854800c00740c101d50058455002452580c80b042e588905048160410030700505240f072069802c0e60448003c03540c0101c00000510340a5400307526110b4504403c070200e82810504a00103101344214803526610011240c2d41000004120700c10390700c01021907840381d500b042080300910040841c03880720b001040c000c2c200b0034114418410500d581405008800b4101030081c40082d40d100140c07031041c0008071000500c0e1640c440001c50764240c1d42c0c000350240d41c0000b4582c05100d804036081000c0250194026a1510364891841c202c2e82c1c0c514650001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 900016250 1250 900015000 900015007
    0xb0108100308090a170615010906020a15090210081506031603020d09051b0f0a1d0403020715080708090a021e06040302040c050304050d0509090106451208 68
    0x692a20b014151545024081d407140e60f0f1141c18800c403035007200294a0151340305004000300d001010101c450031800070301c0d142c40708a20f480c0001c3e5848459407002000b08042c03c1001b101c60002d075102420035a0014901041410040710182c050201a214040031188000b8000340714105601106d001e045803012203c070707841d2212400c03002500200b00d40350915880320410000304000308003111845070b103c00e103140882c43c2d40c410002c8031b2a85584003030242e0300541c2c04118010a02e00804d802800c840c0c460220303581c41c1d2074100e003000350030f800403c1c03114281440c84007001d51020b4080d204e2105a2036603400c5448045d1402c4c0e440d02d02c00780080d488420400c0e80d030152448c0c41202e0f1003c560190010703003400c1d1641d0004061307807640303080c1c40e0004002104204c103100d01080621403100e4581480c0c0d140c0042080030510607141405501309102101c1c002d0304825481c207104c101080303001c4040740a041e850b03005680320032026214210101003400008144644019044d01c0200e6103c9800c618 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 900017500 1250 900016250 900016253
    0x1806050304030e060c0a14010c030b1203030103020d0804181a031f2304060c08070822020111190213060b070b10030b01060c03030c031b110322090b01081003 69
    0x5030301c0f00054405d079000e60705200d00081c14413185048058004000441c42c1c0c22390320001001c4a03429183c076403040700d00f50141e003401d107804002c0381d05482e010b9503c8082c0c11040c0c140380c4805e1046500428006221454a40e1f405c405030744200c0d079074252600f4292119088100301a03440350401d9080c4060101080f03075104004040d44020110400070302020300e000208203020064403012034059801580300d620700307440a0360148210794440030300d08201100d4100b00341c0c000000541400c2c6129807240003640c1409681c0200d14030320f0305940d46822504071140665050f012110120012801885500403110b01c1340700a020320029200f01c0d461a6040520b507444409004a025040b920062078a00d000f1000c2030702d07594428042c111544508050f41c0c1540381c010100e481c000e070101c042520b408441541c42600f10201c0c0140b001924101d0484884a40070a045218807100d0f408070901a0703803440c9007030f945241c0840445107203100c10031541030711f50700641d4140350032959a80c064441060900 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 900018750 1250 900017500 900017509
    0x150705060f0711010212010e071803080309010f06140306070302040b270d1b08010908121e1314060601080c18030a032109020105032a03071806050304030e 68
    0x1507001c0c040b841e040503e0415140c1076400c90b4844100f411210381c030300c4e0050004003064401d8640100b154a0303c80f12240c04100d1280c0c141209010082002c0c2e000008a11081c900350001c2000d160b2100d810007901341d8440300c00d4810344561002d18068021000040c00641c003910946048580301c100441c03400041d41514040044120910390042c2d81d44904501251104803d00000740d124485006a800030075048144424080d4000b035040e80c10314020100044c510004d81b4026078030688041c4040d2141111104007541e5100344c411050510410485c00c54020540440007900071203c0c80310300780c03075040c0050300c0300ea003102d071940414084004210540118001014424090250f4a256a01c2080000e08080003048141c000500990301140c1c031454000180d002005500d004010014696001a101307000040c040182100302d164400b000d1108001c00e02c2985d042000c13103e0341e9140510000d44030800d040c05076400141c0c0c40f10b0110b0a0f500903c12a801550141c5402c010390740c035482080b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 900020000 1250 900018750 900018781
    0x60312030e10090f08070317100506040501030b1215160509150f0c03040618120323210f09070b040b07230a02120a020a0b0c1c08010515070506 63
    0x1c13511021a480d000740450720080103021074038460303a1181046441d8a0260b02c0c2c490000e00615000203940f58100481c1d52505e003110102e48003820013203012140c3d000080c0003198540405800c43c094545414155550400040e1091503800c03100b13030b074202c0c00c24030803180e1740150350107907401008503207420604510200103020f08a4604800c2d40c038221080b15000d00b1900700d5802480400c600e0b420b803443d130002c00c0000c074010340287c10740014860308a40b4001d083c10103400d0891201c139032001081000d80d0012040740c801c3c031440c01190002c1000041900a40d4408444400c1c042d0407044c0440e904640115440b0201c40c0c40c400c0081c200790a1a0700726500794401c0d02d0131039a40d130340012014801881068a010102580d002801c0d103600180140a02060384004594840c0c110145a10050352082019806e95120b44551034070740c2c84503121107203480c500086048160500310b0395820b069a00084c10f40c140c92083d14140640e50408112584600035107800070800d030414030015840300802c0007617 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 900021250 1250 900020000 900020003
    0x2007030305220218091c0e030d0804111207321008010303050c15090604061b050403110301020c01022a010504080d0f0b0907050403050c031c0804030201090c09060312030e1009 77
    0x580728125540c101e80e0126540b01b01d203010104103100761103903661a050000001110840c2000a4507240c1039843c004c0082075204084c1c45040d00c00340803c1e100204021600c06084451442205501c83c0c24036400400f112003100300d080d24007090350300700504210000390726100458070349110a90031903805840540115160f0389591088038a10481e035030b1180200c602a80000e4040c00f45400e0500f000c0d81521583c541445150240c00800d01c2c0030355200c4100c0d0200e036000060410141ca2030400603003e032088887d5802c0642c0081a0f100d10040c410320300e000303000e50f441d20300f5245004020b826800e940e0102c07000782c135900c010300001140402d181c010807410400040c0000c1e040180c0000154045010348a040018802040500030400100005000080124001d1035030100000318210010a030138000030804ca06000400c0400d4001d410440000d0f80c02103000076007a48654040c0300800b0030b03110649000140280c0d0840b90b5020b0320078401c01405003005460004601d0300c51001070046000e0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 900022500 1250 900021250 900021253
    0x4111b010c09030f170304060b040f1406060c01020d0f0c020d09050a0b0705010905060405032101080a0201051c050106020102190305060a03120e150a0908120d200703030522021809 79
    0x4e85d010a945c000007140300700c0c425000010080d0b01602803008440012000c030608600d040780101c420005460705543c481d0048601130f594008400348240a8040c1e01034816090b070030070003041c10030009a00129078840c450390840314103005001007101e03511440d01c10f80350040a80700080c07000c818004000c21010b80a88004214519507607100c52411008403420707150381e000441c40142403030141c440000344003404c405110140d410200c03502d49401107480000c4c14010001075000070504459000746130a03810103c108103030360355040064080d5012040f030464060501c000c000c151070080c8240740c05400d001c2c010003421400e40e6212054881c0544070441480180d4141c03e00d9030340c2d40818410281305001c030060319800c1500020b04105550f130801852034001021a2404030000c2c0705446041c45101c2000c0b480610311034094207060328800c40740380c020a00080c1c0409250301604030340d015024608594400000d8a0384032020301500c6e01c0000d62060101203540e115240045505401c101d0700b00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 900023750 1250 900022500 900022523
    0x32e180f090b07090504110a0519180e0105090a06080a0f0c090903031b0c02030d08150901060f02060f010f03080c10060e0a20030412090504111b010c09030f 69
    0x202d5210b0807074021215580080d10448050002d410980a50444480540b00740e41c2424403a1300060a24041e110507165040c02954884004601c00c81c004118110443c180c6500b50703440d1500c0218030308003400f94030f0080940d600450a054074900c215402c541244000d01841500ca070340d0a1720910074200c0541d0716607081c2c040072440369140e10505525901c44c1c1c030f001403a00c2c80b000c10b0034005002d0811050a20094100c40f601588000c60800c4070445546000030303040daa030780c1001d8102031000d1280c0390080524000440c0c40743d00300c91107000020268085030381035540c0f01c80b400f240c940e090141d1444614400b07410800101500042d00300c84000a00360342101800721100c000b1244c0d40c2d88404503039141c50060040c106450300c540c00104241003e800c44c8200c102501580b00d1001500040840d02c001d03104c602014416052078018003070041c014008002c0d110701034150798000d1001e100d8400510011407410101c1441804e0144c4502d03110311800a2440d2103546a4018601d4161901021503 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 900025000 1250 900023750 900023753
    0x6010f2106030b07030f0608010603051f020c01050c09030f0c010f120b0603090a1a060a1203050702130e0706020309131508010c0906030b04200c0c0303032e180f09 72
    0x1414803c0c45404517903400034440d4101907818054440a50006610764508542400403170740129003400c45481a030f0381c0002074000c10108400034400d0000044640d440c040178042c007040004024906450114100c1d0310490015108684a0311217258460200300389251405046005080c82c408446001c040000e00340540c070701103885948202e070034040c1504180b40d280100103145246925216240245145501d4190080307841000180124002c43c1e140300207580416200e0380840e203007594050800c1c01c0e40300c1311550340303000f80c05d08005c8200b40340112080454001d02c0001918a901d8004003900d000b90101c9220030010403a03001c1d403100c2c411a41c000420086400d0140d108212655a5004c0349a13103401c00c02401c440d40e440380c09120342e0401c40e0b803107662a031040d504d6007017042c0d06d80d8080d40ca080e400203180c03034141800078880e01800003001b0071114640744408407d00c1d01000050107091100f50084129802807800341c0300c08a41650388401047c07140303502c071000080d5000c500003040c1419 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 900026250 1250 900025000 900025013
    0x11d1506070609080705010509030414040b0f060a32090609030f0712030f0306050f040b0102010f09080d0b0f1f05130311031204140d0c0302042306010f210603 70
    0x1203c80503a034000001884a0400c01c0c00d03c103035540901c40d1006541000d08040c0c00c65800001051110b00c21601c4550240203940d4000d8400e5440c0c0c0010f042c19540c00d100321000d030400081c85040a145000940da0031451203401c401c541f80304480c198090314060a0034100305854009800c0181c040c4100c24240035541410004000942044000002e102ca200d01d4000c1c251514a03625004240c02c20300208026210008403061041d412940814410800d8004074010b025548500034410f0401102c40d080c0100c5000800707500b00c060800380070840c088400e0000c40341074495110b0b0000c648030480039000c03403080c4a08155840750b2500501c0c140c00d45003100c5100c040c07604252000ca0650b030f036003886403400304011201e128400b00002c1c145031620b40500008075100e460780e400740d40010035541c10480350710441c6018560040081100355210388100c0c003816145000c0c207101301c1880d00451036560084c007001c1c0c02c00d0981c0d42c46c00e100020000304070040f11240403c01030b1881e11400c02000013040c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 900027500 1250 900026250 900026261
    0x9060706022b1a1f02010e061003050c060310120503040b030408090108060f01140d0b1f0212160201030209060712231c02090a091107020405011d15060706 68
    0x203110710030380100ca048025400440e1140310141072260030200341d60320642c42d0040740c221040c2100550f807802901513101680503111900481ca05809124200400e1045042a030410359005108803600240d50b8000c1c01602c0c401541c160100c0045403000f0403401214007501c0050920600540341806e03031b2502e800003030360400d86040710403c07070208400303d00c1e5a20410403507010900304c42c1e00204942e40030000c0c1412172045501c551013000041d190101c00e00642180880e0b0001a10807011400c1c1c407034401185030391007500382e0b00601540204900c105601010344d0b24441200b0301456540c2038641c0158001d501500c40503410040622948020038011540d4008080304c0f9101c090583d0410341d04c0900300f505140402001e1300c0c05120448586e00c6100c6070142d81a601308006a9803590381c030000303400002d0342d801556001d003400a800d1010752444054003020b8800c1c3e8040c000c90f621174006070a649a6454501c003002c0002d000a0708a0034032840c14800000041c044c0c515148036030b21440300742c1e007 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 900028750 1250 900027500 900027547
    0x327031103040b190302340503040e0106020c0307080c100c063b100902151912110a0e0a1505210405150403021515040e060c0906070602 60
    0x98000c00c000c4c1c8034542c0d0201d070307408441031803404520313004508034404106121150701403840003a1816280e1100b40440c1203a0009030048101c0342c50390380e102c3c0c0500c0d00b4003003406164014064101e00000c1070a0004668042c2d41070800584100700301d1000f400792405040c44020100100c0341004408035449106084c6004812502203500c0c3d5000000d4450100c000081c541140344146040c4109180120307001e03034220349881c80410360003907500002c2c000100c40c414800a01500140103500ca4000f1000c0114540b807d88841403105064610032044400804441c610481c0401c1608000383c4205840c88401c0b40040c02c00b00c3c0701d0384520035a4003984000348403031701242c000503003111154074a6888041c0f00056401448283c074140e0b5036942c54444502400109400f402d021038100346c02841407109005480c1c40d59480d9191400745500c08070000d8540ea8011860540c14610650000c2200c0707203d00b1214448600c3c115001c024010386a0010000740c82c200c8d400d0020404544142900a2821 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 900030000 1250 900028750 900028769
    0x220906090b01230d0b03070e0c070303110304031205190227040207021f05070f03030c0f0c08040501050c0c030706090302190e07120207020a03080d0606032703110304 73
    0x507518400241c640d00140f606030b40b004510751082d100c0710b40203400315045070004400200e00c00c014a03012924104a541004018072031160070400030800d000080c062041c020340e001e1000d50b80c0401c41c01e140e1301c0709450283c005903138600c0080d0f00c0d4460b5048140c2018089050311113400f04888150100e03044403040d40700c0c002c03004100300311940281d00b41500403a022a021840c000c1290300099031800b1042c00d50801f0020103590f0a4000d001f807054600c1c2c20740241c42c0351000011894010010b20654800e54041514844407010031440340d0005800309600110701d0f850306044c42c00664050300841102c584621a070110a04551400d0004000400003a00da0110306401c520410034640301104441c007100d60104410401d8050041340c20b9044070083c00c14940c01036684203e04003034480c0a41c041d40244c6200300010411480344018584004110402c000f1a6140c00c021400d0320701e0054103045502c800c400e17408428580c14224003a0a11a00702042c00d0480c504030319040d50840d60180d18035 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 900031250 1250 900030000 900030011
    0xc0c0b040c230a030b0c071407030c0e10170c0a080105090c1e01050702130219031a180c040e13170702033403060b0f0307050622090609 60
    0x400b2440b55400310030b03500d40d100344030700b10341c00740d02103401c11076184030181c1903801d1500070030995161007088401c00c9801200010a10045542499880205100481e6000c501980c0024a03119072400240100300a40901810903d0800c0000c6543c02041d0221218001d0004000107645c5d80b440c068001c01d00900003003070b28036050714814100034100c0c4255000740305003860540c680001400203061840c007424041d80b03c85160002c00c00022304403840c254031510014a9520245070720501e115510015034050240010302c2c18005180c003d07400700c00d6009200038074403d07506903100d07428070362100c881040c40d810160740d003801015070350303050b00c24440042070021f51b0070070f120000d0345445a010001800c02e20744405503012903600c81c0103628040c100402c0d0503003d10400d07000400e09181c1280c00911100003a1070341065030060101000540c03007484070525884041c1004a9200101c5400911480c20100080720f001c1c040e40303202928074518400c0d0030002c0b90603c22881180c01504001c1d400051 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 900032500 1250 900031250 900031259
    0x61302131a03010501140c010f0603060219090807030b06040905030307090623040b070c050613052403040312150f0905090c0901150309120519050702010c03030c0c0b040c 75
    0x42031008454007500303260042006000990700142e508098041451035113903241f4114540900400000d4035184c0d5041c1012400001e12156030040d01d600c3c0902c030000c031803e10003c0c1c81544c20b20313054401d100c0c01c0d400410b0f00300042404000055404100640040b99070b010769980d0a0966004582e90360100b10503040134001c40d940007556400c2c04030030070214000311860821000d00c50080c0d210360307800a00005111400c100300d40d0004801000081c02035070b11540721704c080d08800d061074082c05020306060620318640244160704c5603070150b680060f6a140d070b2640d4404507000054004182c8410741c0740e00b00b1200240046000c18014285d401e06000e803075003400d048109503400503000c60030690052800c88481c0c0d0f41c8003d00c034110380041102180003040070750190302a080900c1c014280040c1d90280e030754215004802030202a035200b9001c11400f819101c155158084d00d00040e00240d8441a60740019009500c00240c407451814a012440100c0e0755802c0060001c070790494016102507030801 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 900033750 1250 900032500 900032519
    0x9190b04030309080c0d14030912010c030b011d040507052701031805070b160b090105010521060601050f27010e040c0221040b0d09110402030c1206130213 68
    0x2000b505914019016817650240043c3e5003040380c42c400f40032400138075001059040c3c1001101d116250180c002d58040d540d9460940c003d1440743c1600000c0303800e0543c440001c0d849860a00610343c0120750b101c400511101c28480102002040c0314148942040181a40c80c3c004051000e24000518080c10540300d02000505482460042140f040c003828038110003ea40454500c05580c4081420380e1100b80003c0c90b0301900d55000c5000c1c1c116582c15050003026001904118140e440036102e905c8170303001d00000ba40302151003d01c007903d2a0000c0f00401c25542c4600002e04a490805000070b09124000b18446100311050070340c100364a00310b40340495107580244050142c0a01201d080001c08288400a52911301c4500016500240c2001c0e0011040b00300c02079070040e00d1131084103501c031641c0810030401070403880c400b0740e031071344c080170200c00585094001c882c0701e84a501c298908250b00d102c0315000000c0c0240905a01120460351480b41140a101801d1000c841c0594142d03020725101010 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 900035000 1250 900033750 900033767
    0x604120519021f03021903051602150a15230109080303060a0909020402161a090c0604060e01171302090a0908090d14071203080f0108070b09190b040303 67
    0x4541440100410401503070303070200064000b40b0420301500c10034107804401c81c000e12a0349861078980000c40304011240358140d010380d00c201600001401027010400085c6c0c0d40b03540707090f108180529010002124561280c03c02d0880455455044202a45429040522180384944203104c080107595803209980d100c83d01c1300040c01c440c005545542800d4011411a458500489581035110401c802c02c40d101c96040324800340c1c8100d148200e0355403500c0c1c50600d0b0701f039030507a0006802500001c204480000b0840350040c003801844286014500841500c1c0c10080e104142e05100071f90380c030010401030010301244501c80c1c0c000440d000011301d10401142d1440074115403000d52920420400185d484022291041310443c2c890032042018540380d502c003001c0074902c0b0024000c1000004040d00030003101c0140301c3c800d07114411343d40ea0b584001080400700340b02d00d01a56012103420000048683c005040e4084050034084c410300751800e10086230500c0d6800f60fa071440780090100285580034441 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 900036250 1250 900035000 900035023
    0xd030c080406050c012d0209060f0408011d030a0f080406090512090a06050909012706140109050d0201082a0c0f0d09240903150906060f0b0d020a0c0206041205 70
    0x3034070032582c80c01255001b100e41ea060180241a4001001491951100140c40603c865990500d43d969102c2c030259000e44041d0885500d10100302a142c015000c0c040181c64100c0301c20f60762810700640c5038a0031a04610f010344184c1d0b000b580c980e0128081201481620041d0b648000d50560382c42201c024001d110000d03a01c800104802805030400302da0321074a1841c11961980130015140001064594001d241c10420741c0384503261040001d92245100e0300da454041d000d8903410355131940d0704140007082c000301c00c000f80010203440c0090b9401661464440ca41743c130506610409000c10b031010103066100c0d41361600554040240426040c60070070140800003101d01e40b00041c00d1418212654040d0782c42d044942414070740841d01003103031007407141100450b044000046220721501e103e40040480c0325080d9029800c0080100303035003002c1202281281c9589104600e00112115030300300030742000c180041082440c03000400560383d298080c201034650b02d0b444034030b4000035103000303803820510021 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 900037500 1250 900036250 900036281
    0x30209030a0b04021f08161b0b0106090b120f090127020310060b0d090203030d06060c060b1c02240403030504080d02071508060102162c060d020d030c080406050c01 72
    0x1008928036034000f18442e0094244100043c2c0c01807200c1e01601c8404001507400301290602001c2303c1400403440c00306040b69640d4030b030030400541b20507000c00140b1401c4c10541c0900d020b5800f041018011941d01c541c842e01c0e41c40000350206000145204258003410300c8101e81400c140c100080d8902807101038028507200d24200002c915200180c10365010381c1c03000041540c1d4800d54903007551014000c0743d207241d2002c1c9042144607201d0001030054403180c0400c0d14010b240018850040c20406000d07240c42d40401e80040200d055517080000810b080f800124003600b0501825503014007407405071005c0c5102e5107400b80c846040010b042d00e07010285100b40110340c064041080b0304110180300d040795804a11b041d480940c1c2d980c0044c0e1800024151071204115044800184241819010411501c0314040142802140a4181c0f2150402c2c1c90301ea0b40400c2040002c00140740c1030034803c4025109050607805020561100d1207190456806040070070400a85010300c0790083c400c2041a024041 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 900038750 1250 900037500 900037549
    0x80708060d0819180f0e09010c082208030f041b0806061509031e2a04050702030c0a030f020c040203061c0309121b080d02100f020c120409110412030807030209030a0b0402 75
    0x84010690ac4000e007049906800c020a901025078601e00038030009500180301c65074a00704080301682c02d4004480a5405050003041d9042c04541840b2100c101c0f1411001400943c841d28200304940360150b0300c141c56600d013008000740649003404a4844162031040900f02010301c40700a0341004030108110403c60744002e4182c001c0d400c0240c420080780400e980009180da222441a451032290f06010043c0c1e100b1000604101a0300207403d0281075007503825252040411800d1000380c0c013081d5021503025503074141c3e00400044034008015071501070326001e03030856038402c00400d110a1340c110503510a07112003210341944c001403900300020040c0e1002802900c2007194001d4940309542c040582242d1681c0005140f0701d107a40586040100074402c0c1c5100220000e9200c61990041c46032136415428240c4c1d200c00507407018269000c80f10748030903c02110903150f82c01c48840c80014400b0742419030a2141130304a44040010082c881d02c030700c50048081c1000d004020031170381c0390f030f50410256a009 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 900040000 1250 900038750 900038771
    0x90e03131a03160e09090a060606180302040b0301020403080304030e040c05040e1303030b0a0b0c01060503010c0c150f0911010207050301020306130e10050403080708060d0819180f0e0901 82
    0x400c2200d600404080f00c110303094890500807565038403560b40c51070740310032400b080c411204004200741030181c1c444c2c001080000d9403481c00341c490440380007030494407095503c001c20260410780c0024200c908000d00061030700e6141c2d61844026082a9810b8002031202503003080070382424410303040300141608109080030b1800b1102020003000030f01d0300303448050300d104120030140a50485660004010010f40955444900300001038000c2440014a03601386480015a030506200d941c04503c0c840d078a9001c40203094484400c01e01070b18402c0806140e0720309034051003c103584110400944034011024010103c0000280340c502c0769081184280d1041091005541d5403044820300005031880101d800301c0300104860410720b51042140364079003460108000c040e030185c0140d1098400c1e842e02105511400188100b03030b4901440288203120402c5942d0221001210403005d040240c0b90849039055240310980b5244250b92001c00740c00600391040c400a0002d8008a03806a03411008010b4003410 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 900041250 1250 900040000 900040049
    0xf0304030f0540060c0203060114010e0d05210c15070801270c180b0f07080f2704110f030103030804050a060207032f1c09090e0313 58
    0x1008803042000e50000c810440140751040911520000f128207594540c00a00300000070007040b0320034091900003146408901d9000c0400307181c1a511f0014201081c3c040c00070b13108008005441c04d02c50360074221540c56454000c0d501000e40d510005403100c0b0800301003443c1c00900c1c1300c0c0480103172189041215159114442c1c60440c0c000c10b0f80514812500c0480c1090b001c0364241001055003400402030045811040c4090180402403074002061340c1c90002140500a1409070380c1ea40701e040290501088100c0054824114010081494001c0204140900442d1090032038500c40000044400c18a000e1041c0010090541e0b20f05141ca00c0c4014481d040d8401400000d0504c00c81c407002c1801d102c402c01000d4000d940c445011075641c102c0e4200500300b0824803000d407881c21040118644030b1004a40c21002e01ca50744402449003800032480071461000c1150003104110106c8000280303040c5c42e00459000e0500607004d586d803141005106022000103421010540f00c0114508440108 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 900042500 1250 900041250 900041287
    0xc1618050f1612050f041b150302070309080d021605030a0309090c05040e0a050115030902130e190c08010f06051c030e0a0e0a141b0309120f0304030f05 67
    0x1c50ba030388010500c030803401900d4040341c0850071100782d45814100310380043e604240300e008030700600c130003ca50b6180d041c580130303007030000d0007800d01c000214107031888500d01940240244601c241081c800340ca884130300491074106030101600040c0d000701c1a0305507a40c02c4440040180200360060190352015803009803144c2080c1c07054000c0b0694030340721810f54512400568001d000283c96038fd50fa41009030490300901002e004000b400c9108217180c2400b28024400d041c0c1803980a8a40d88500100c02d86440003020320044086030390240760702c04415aa100c00c0320003000c41c410b001c0b1410050810450301c0c04c46004289010086107849414096552011a502001d820110750f03400441660314088072500340f81041142c21503240c0c0c0f0b0214079210058020307441040100d41c10420101826a01800c1d480b06480d8000c0681d58183c15040e0840f0070f000460b8000b540c041242c02c030701c078100c0f04518203903c44840c40c1405c5001000b40010103511200c0d41d80d0000203840d1903810072264440c100fa500741d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 900043750 1250 900042500 900042511
    0x4091506140a17070f03030207080d0804020a090b01020109050f42071e050c0d140a0c230a03020f1614040b04050403020c04142203050c1618050f 64
    0x65150b90700700003d00c0e04102c074401801400022170030959580c90040e55511280c040d04409002d5100c4295007036228100075445690003c115240151800700114001d107981022981155200e0211030042541040741e8901000200c0040c02c10780c0b41a400109030064803a441c403007821204602d80b00c030402c2440507a900305412450281541c49803001a14013580c0c0c858248100c00304907840c40074440c1c021000e42a600100d10645001021454088035048110540c10812480a00540b14040e10440c05e40001c0c0e403007045496180000c0c40c0c0740b00c0c18240b00c0807030540290303c10660070701090350511400c200d5502000041848202c50103491900301c80034040c25192404040c0b03140038075a00d030f070000c005114025000308424100381c280207480d0384c05000c0480c0281d0070464071081403c4c004407200e200b54215000170313065800030008110a00f0010205504001c2e0a11a80b1810b0741c081c403208100320f02d0484250f244502c0c0c111101c03070b040d00424248000c989414104034042c48003014255000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 900045000 1250 900043750 900043769
    0x9050a080a020a0f060609061203090e09070b0403050304090b010f0f080c0f07030815100e04150810020a0e010507030c0b062d120105011a1804091506140a 68
    0x181e041c0322040340303401d0880c50080c0200d010403840c1e030180422540304209440f8842c00c00d00c00320351a440044a20110000020f000a80d000340820022855514681e04445140d0a0b140c902d65940d00d5214107410503003054845401c005402c0000e540588a8860207400070300f002ca901c42c11035400648840c008c06011030901807200b000444a07041c1c4822586501c48940c10103485000030705000305940701c01c5801c91480c3e03d91480c0c440c0145800c48290602000d0340d40c901070900614410312000d40702c010180c81c0c02a450841c0440c2e001c600b40280c43d194108030800503180e101d840c20040a028551412905012081103414042070344800c00850791500700b0191007090f12000b0110b00d492804183c45a00c9041846450941d81101546410080d00c00c403600641000580e14090882c5d80c28030684990807022042034000d500c000c0f01a00c0705803032842e80c1900f507208860120b816500d03d003004441d121030390912001d140005100d400c02601003048450000142c08010070403044040c003800302c56 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 900046250 1250 900045000 900045007
    0x5100f0c2307140f161206021e0708070b130b04021c0507080a05070512150408070503070308070305090f060a2f0417010b090a0b040912091809050a08 66
    0x900d0041800c65242c250300c1400a43c0030b400f6202101d441324605982d91803503000303404001090050910175003041d00ca0007840081184071303036034500c402580b000160610411031443d218551407130003405070107072500521600303680350160b1801101c1d5980c001c1411110300c41c550600004600c0700f4455035403180d4103541d4001d8001004c0d0401d40b01c2c40031070034000c04d588186000443d02d0308000c66551942d42c803500071601aa43c44404001c0d042c070b9500800e51580d0300005a84421040900b1055081402030340d501d45003c606442d024113503441170303a094005c07803042c40c141b020f0365905200b42d0360702060340e40190400c140654240c548900021b400d01c0907040c0c0b10315031440d49000502d24141c0004061514404101052201c028641c0003403052403031100001c00b18040c1c504043c054803082000083c0501007903610100842d000344159030907039030001d41d5800c5200010b07a592000d1807040040c0d4640c080900d1400410303209050002804000350381c245561440040c1b00091010f01c0103521030000c1d41c4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 900047500 1250 900046250 900046307
    0x2061305070b0c0c0d050d020106050607050d2109120e120a06020f0c0a1a062e210f240b0702040e060c120a0b010e092205100f0c 57
    0x103403058044902d0703400400e0000185c01c0084c0040c0c0186240c120742c00a2050070780d210100009070265880241454001c0310141340c2c694400d100301e850040c05c110392610f01036103100003502160160034086402c001034401a0700300c035070000a1086066030031109551610070190603561104501c031401095150049a80c0d00c0d43c2002d1010349000c0380c1000c017122844481420610100c3c0c0c00090421011081c00f000701d109030030081d50091224510314040840c501a5209200d6418031140040c010040e0210600740c0b120000c1458007841c402140006c1001110340094a04481e480000420300c01c0005400c08240c0e10000c0703a01c0211403480b00c080b0348031409030002c0b40c0034040780c2410080c503001d544100000719555002800b482110750052460654411108008480042c983d40d404244544441001482c004540a07880440c09003202d5468501c440d00c49000040c218003101c07141c00820240030558042d114000c101e1442d40d00a04c1603010001002e005400243d00c0558091207030b298024 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 900048750 1250 900047500 900047503
    0x12161704080d031407080408070b070c020604060f110706020d031508010c020d171509060111060712140709170c130911240a020a14030a02061305070b0c 67
    0x400811001d02030741c2c0c0d142c8218100800a103a611004040319038040080782d601841824242d1081d07a02040080c41e01016880e8504881802421781c410480310680c2140181c40c1c0d00050402000f0a44403880c541c4e80709103025022400b0714048030069803040038200441d942c00200e1400b034007441d00740010081030b803612030262180281c00004040d03003800c55214400c0d03800620410342125950765071480340041001c1c100f54040944000090002003107402c1c80c01d1502c11b0300c0303a41001c0141030100b001440ea1504600b010411208400880d1003030500d142c660f0030a005111102000400b40b002078a4060800f42c0b20a400e405140004a400c50781010314000412140b10f070f84070300030101e11520303118002c400c01820340050126000e40203504040b505003400c0c6200d41075081c4907142c180360040340d101d500ca25034209101000440c41046404400b003451050000b03000202e82028503a2400d0140019140c0301c405003480055410713089042d4045840810000180d070782034a00c0315503498500c030005 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 900050000 1250 900048750 900048757
    0xc1e01090f080304080712020f1e041e0b01260618010f03020a0506030f04020411040f08010e0f0f0303010302010f05120a0e0f01110d020c01021210050102121617 71
    0x5501d440000d80208603080c1c0000500201c50800b01201c2c5200c0d1141050300311720016100081d0041c0884031070075518902401090b20f0343e0089000d07035a50309030351400241664595410313510024000c5448000b4884580603500340c692081c01c00000c45100c400f0340309201550384001440015580300411256901c1c49028000c0c81c0b120101016296110001e000d11218188401c80c86550305030800034640c1801d00c19240f1039103910101c11410740d0390303400b0701c0050003907140c00d50020350040102164105040c62000094050b0720000142c09143c0040c60f403a00c4410505091264010401c86c58080000030031241925030a20340f120701540c0c141f0f8190303005c0c0511100c0390340c8a4001c00c20441a181c50b0f80c0162000e03072072481140c2002d0f00c040030391400ca4026200041300d62404001d14400346803540c0050014079241d0000510f442070441c0c6013a0440740a0307411401428854504110642e810003144071507808140170782d40390017549080c941d02d20840043c01404008002008200e002401064 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 900051250 1250 900050000 900050009
    0x31b1110140f06062a0c040908030a090203191505090a0b011503060e0405030703082406130b13080105010e0114010305041410020a02100209010f1d130516020c1e0109 73
    0x5a2030082c843d10b440e06807851940d224107400d48106c103d40200e40c64280034050206422911051440e10b4041140014081121003aa0036110302410511000425000403501724001d4189680e2007441601c84030681e0f101418101c07496200650080110b070704a60105c0c11260442d400c502d841d0804241507020700480e50044002d03200540401c02440804001015000d200e82d0b60304906558040900121b400d100084014015504003291894103000c001003100c2c580f42d80da040c0c1003e50750045200c00386e109a140118810300007104001c08034090240b1341c09003141002d50b03041c40d8104214a00040800c418217410151a0f41c0400c00303011810303070700e50390200081c415100d10328400f48004000c3d40c440d9001d00d0052095400031045161941701b690641ea105030740e81c84200c3c05200049408900212070b9000c01c0301000140790300e0781d41d050480c20030701b20050000b141d03920303003000c183d074003003601c0304a90056410a80503401250390b29040d0343c1200c00390703000545542c502140101d41080b2641c02 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 900052500 1250 900051250 900051277
    0x20c0c012303130b0a05011512060308160507060e0d02010311130603021c1803030519050403090f270c031d07030c0503030f04090b01031b1110140f0606 67
    0x1488500e03100da1080090f003602602d0140c01685030010140c0071030b002440350007490b030001502e41b40324900c104210b102c220390300207003c101d20f41c8903242c0804952280b0003c40862440e0408101000fa045c00190028030440c1007901455102c540403030b01143c180c4400a04050761600103440400c9a0380a0700c904036101840c1c1c00030780f0f440d0300c8050000d41c8072020502c081c0810440c4101020310900070550300c0d0b41c46418214448c03c190b03606402410024207184110844104002c030104030512030b0502c1940a9503541e400185800141d10080307070a40c000c0341c8a50405158144144004082c081d00301450360700018141c002500200e006089550b444da040001e4200040091a4000f54410a40307004201c411071055443d01010350f20310a810941c070a05405002c00c010100240e4003103c504c400c107040100c0d0f4400a002902210300422140e03c1c0456860389030101e030180301304003100c8900c40f680b1040002c800110f00380c14010703030028501901c0165100026200342c81e490141d0b18101c52000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 900053750 1250 900052500 900052507
    0x70f0503060a122a0803040e150d030207030204060902192a0819020309031b190803120708070e0d020310060f181505090403090315020c10020c0c0123 66
    0x50030135519110100d889212810310010000284440300019040b99400c50080d8681031602c100c10189000c0200500081143c0e82d17a803008603100c181c1c100d40101c0c401d902a0082c6829032041004503516500070181d601d1041c094440500c907244c0443c2c402200c00d050400e00d001e503046102c0e00018800070b00c03810403012585103500704003486014041039030244c031070859207202d4500101d903a03014010401c1d50581c0001040446240450003030300e5040c001405404280070441d44140c110341c0300e41d01a07580c0ea4030010305208150302351a0ba1b1138000c10140f90460076800c000900030100c0e80312200d000d2281001d130a02c041156004c2002400da000c0441090146560b120b007800b80c14601c034071907034a025040c0e64080003204400c3c861003049807a83c1c0d050000d90340c1801c09000b00c4040040040f003d021650380d010001c240790610808034501c00c604050307031780e52040c0903590600031000e001c3c0107005e0052000f00561240400d041c0e003400f90078038040d600d42c4e94100c250fa52401ea88500110403d1000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 900055000 1250 900053750 900053753
    0x607063206090103081c2f0304030509060f1201030809030d110606041e0507030204060207120f11011205040c080f0703020a0603021303240c0516081c0213081203070f0503060a12 78
    0x103a11182c03800c458182d4241e178250407c12010705120465004000950402540040740703003200c00340c91210315000c01c00d8240540313005c07a1011440c2c00e0b003042e1080f907404600f8008524007000900111b40792450701e0011a4000701d080e546e500c03005842c1510840d00c41454801441c0007800300841448840000c2c07045003003800d0054020360080c0184001030294080100341f8044002803580c000307030301484001805c1540c3d181d10055802c3c3c1c3d54078504101e401840201055450f0141138000e90260034004c03d001c2c50034515034509000304401c00301d150407500301040940d458550410490b40c25040c0507961744c01a10362070034613920541008020250b03006000364400d52490801d80160094042044518840ea0043d42d0b40d015210120825001c0d000e070340c400003000600900007480404607502c12401d11040000d0680e08005102c0900310b20000c0308020304401006220804055400a5032460a01c610000c0c0343d018159160f109000c400404071b902503c91200f01d600074000705600070b444102a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 900056250 1250 900055000 900055031
    0x1110406110304081f02040510030e070f06020604060903140a030c03050601051602010c03180b090906060a0903060e120c0c0a0b0412110607063206090103081c 70
    0x1034014400003500311400042508030010481d000d8480703140040c002c802c044583c01c204071000c500c01303008058080c40009180d0303c41105070420031960385c6000c0307101620780742c8052800d4840d5202074000103207100100329039900484c030135400c00c0e00541d01040780c00a604041e03990b0010486984401c2d00c0c001ba0741140640e0640c49a1050016641c0502680d00c41030011900b0b40600080b602c82c0c0341700c420100700158000c0c071400c6c804030310030705000303c0392116803030900f0800041e64403003847d0000c00518890245804100c1a80c4201d04954050400d0440000107100400900008041c282d1f00d1444c10303000f0342c00304050380b070f0b2108110450f651000b0602e500d5407204070160340700b070194108801c00329400005405440a507007400b141034002c081c0b2525010711102c19030003060780000003000410003284440c00b03000c041e00040c0c1092040e151145100b00c6049403d07400129003034404c81c05110380f69030342d0490941140c0c0c00c00c6046448010811043c1c45425802c3c107e443e16619108600110100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 900057500 1250 900056250 900056257
    0x11070209010e0f090a0201080c0706110f120a020f03040807030e06030a1b0e010f03180f0f0302070b0c1e0c0406080106050f040603050304051c150614040b0a030b090a02030111 77
    0x1075021000785a61640d60300a551703a660203000902003110040003408140d420005030003804e000d8540444e11840c0b10451100950100d21802981540024090780d500441103080c1c0c1c1087c0701000442c58202c82980c4404c4500000d40000d01450303002610405041c49004c0402001030014071242d03403070800310780c248001d10342c00c0070015048405105a442040c0941480c51304e201c410303140c86105080c400411001891205400c0403400c02540c94080855020640d29a41d81e1144861082100140c00c02a1410006501a00c0150b00801403c0b0b55940c01007082d401c074075102032080345441e640c4503085013030520b0800d246802a2070000c0020b0100c1054000e101104c00503128482c0071050136044c030007130f10828040070342590310030041001282000988a107017072069440400489000380e4030082c80651a500c80d1600540b141c406029401c030413480b807001c8480c00c56041141000910115600b00780c1d500c00a000c0f1700c0e640001504001003408244440340e030043c000c00106110900c140e44030303007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 900058750 1250 900057500 900057511
    0x105010f0906150e0906041107120201050f0709030303230411040c0c05071202060715021903090323130f0311010207030c180207060614030d05090a050411070209010e 73
    0xe0a0010029001d150420103403d00c800343d035124110850380500780141000040c1c0200d40040e03940c0c0c036410540d41d001c4094a000c511075034100603500c030201340003825180080e02e00c00054507820184008030350021501e200312a030608000c103180314508a0640d188204c80300b0500302c07016040401c010080004500801120203e50410185603034030300071101c0d5503c1140c001d15990002e18107124104c082018102080e20090a0038a02183d0b40d40b0159103c103441400700d08540c001c215040e846010500f6890b00c0d1415180400c1030072801c1d18001c1c000d00c0d01182d50400851400324011909032a002255600b003c0d4003440d0354125a01d40b8580010650703440155920b0802e058060f02030341c030100b0903404994101c07220520890810312050300d0742000302501024103500f0004030000840c68020345000304001c1e0b1311001c030610364500345805e09820401050400600b080603a8441d0760340340c00d0b4016100c066600282005110302c00e41c42e00d20406201941c0304505800004090096070388107446003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 900060000 1250 900058750 900058769
    0x90402160302070603060b09090907030204110a26180a0c0f0302040b060f04150302271f0f0e061606061d010303091203180b0301080f030306130902060c0105010f 71
    0x71364910048044410780e008068070100104192161458a131b0704494100c00c90703605607010650340f070340001c080ba82c510605a000000104440380038a030040c000b44454202d03074000c00700000c503459015262010041001c03907140c14083c0c108810f81410844c100c000c03944100c15503010b94640c0021080348100d0300c41244280d091280c0c07402d150900b03400380d4000750007044600b07003080e00b0700760000004071101001c0d06c05c26900b44400d0280448107095402e110403e8102a00c040b00c4040520404656810303140c8410380d40d001b4492042d581c803030500c201904191030b0508070b0080740b03c00181640300e410302c00c1c05d4103040301d8000c0301404020f030f000d0411a10041058402c4c01c2e81800303c400d10420900c800b9022400307540e000c20202d501140d40d140c2c4140700b442d0103100450900360701e81c2c0c011100c0e00a0300b80000040010310401c4c0b03080010742c0802c00c04000660840c40c1000c00106502c41f402900314600f51504549070031511098180c89005080740000e00c081c0da1a0400b40482103654031491542 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 900061250 1250 900060000 900060013
    0x27060108010c030b0a03030302070516091d0c09070810030605010816050d030c080306040912080405010b0609031e0f0d0f0f030e1e07080a050a1b0f0614090402160302 73
    0x10301d001348560f070002940a000c2c0c410b06469074606900a410030b03e4141c4460080316005040c480d42503400201504a24100081501c4c04544000b00003051840d00cae03040341d004140d0004140d8405414683c03100703203031418184c030355500e825510102c00e003a0b1000741000c3c02c08001007410a40402c409081440b00503650719a1b0341e941c001c0002c041c03031261001d00400c4114070054081600d04000b154003080107000860f020186542d805c064101403108440003850040922081180a0007407803c110011540036041a508200003900e030017900003a10000d00303004202d04582da40500840300d54a03020000c1e5480c8980d48200a000143c6a100c2580080c01d448040f0304994045d20480030090704d820018402ca0f244812030402c1462461589011481210780006808204015511540b88a50003601c0c2500151a2691380f00d101d20502c050414140c030340c28810468880559030131217000d4a440e14103804400c00c0c0301d645114541d0000d80107800042c0144c0303c41d242200c03034410180b02c0e9086a14 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 900062500 1250 900061250 900061271
    0xc030203041205160305030621010209030601091505040905101407140f0d05060a0f0b091912020d0f12110f0c03030406230304030306210305030f2706010801 69
    0x400780f16122584100004008114012a200f0340c01f655001c000508510002c2c2080341841000b00407103038850003aa07400050902c0241018030086004181550080c0000041c0400040c15201b83d030240c01e0040d030f6200301d103a041c46010424a0f5607010615001c201d403070050424007000d02c808842c20b07401f1400ca111410002d403210f108644030110025005410400350150410250001070010359001180c241d0100d83d064008400400410f40890410b548a1400051090769010080d20080c806010302c01009180c14a41800d0a10760f4101c4081e05110705030b15100c03621080d00d030f10207004150b10b0301200150315000b00603400301141010841d071002c0095500513070b8502e0200e00142d0140c0090004005140c080e0b121414a08a140210b0002032400703420400980c004440980000741ca07617030104103c10002061036030341e621044a5410300c004c140c4001d000c611015080c0400564400300081103141034428564415480d00030342488001140308040d50b0f01820b000b07644481d481d0216040 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 900063750 1250 900062500 900062507
    0xf010f0b03090601120f0506010b04090606091809021f050307120e0706050f1c020a090501050a02070e061c2f031c110a0f0506070804080702040f0b03010c0302030412 73
    0x244502c040744020202e0381e0030b18021407902e89003180300715031801c10041c1d006e0000b542440305601074010040d01644583c603209440c030a450480e03100c8018420078001c06e11072003000f0010510410007280001c82d40c0b4940f0701c04100000c1b01114901e45070351000510140140e03010000754080c02c4960b0390b041c04c0c1a1001114000c43c0d901044210190b88060710070001c05000300041d02000c5c101c001081d00b000e00e10b15040300c032904030094080b20940d00103440f0204541054560000d001c0c02c3c601a810070810f010b0203544c0c0d0420b03024404142130980300180c0c1555070b01c05880442100c1400d040d45091261904d00a9a45c001c0382050585c00c69042ca14840d90355080e91415207080200140070f80340000b4141905400308103920010025107036205001004100a0f91904902c1010010340589040c2051030402001034000f8041040e01818071001c00ca2041c281e4114075012100051038074040d03074440008011002005401d03500b060f0021200c80d425a02031449207009882e40b480d881c04c4108e045 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 900065000 1250 900063750 900063757
    0x528080609150f190602011b030e1b061b0c150316051303021f1119110d023d0f050c011401030804090c020f030d020c12030f010f0b 58
    0x42184688500c103031400e6241c0742c00f0168004601a0402d1012520b610b407860b0a07008640084c07026031b444d48010039a40308014051180c080080c40d041101e40b0004211075190b00c0006c5413145485180603001c08a5540c1d8070071512003130301c2144000480140144101c0d140c5000e8aa81031156241400d651980d0506030102d034825008962008040c101d400003d0300c0581003141e01000842c06483e0100041e00c540d076440c0b03000c068040c02d460409107a003000410b44e40c102e4000e41d03140d40003c0b118504403101d04413541a035603030055044031070140709804a0b4112030b100001950040440f0140800300310048990140700e40d000d10011070220005c5140da8000b801c0403204d0002031401980f240596100d400034180c0c9000d0704001180003204445e01c80701c030500a800540b546540020100810380c180d1041d83c0080506002400302d000b00c4601041e04c034004e05144001194002600452003c820f110601509000d000b007991641000703000c000d640704090142d00e102070040c24000c01c0c1002d100098 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 900066250 1250 900065000 900065011
    0x6040b0409030e0d060f0903111b0a0509070c0b0a0b010e031612081b1023010608150a080a17070b0402042018030138010528080609 58
    0x80350f804149101c00d01001030000c0400f030ba0603595561001400f45201d01800c02054065501e1899111300201c486052081c008000102c1506401101c030300c41d180d03903030141c080355021102140c10303507107107442030741c0d10a10008003c00c1407850104002030081d0b40da2201419070808e81ea02d59454510700e041c1070b603403040c2c040c0020905205080800920384420f06940702144030780d044034201800c504600701e40b100c0d40c0c413585d26140c0001d034110300c1d462018850842c41c0703c42d07084400f60742c1e6131881c1c146140e5001800b8003800c0007655000224520703020480103040d40c01c0038012008007903442038129280d0314a500203d03081d009070030341906100101020f035411075030070103564a0191070303681c00c2000400f5085422010349a00500d03924a021303c12010f48810401c80e2060700a62604070101030840d40000d10004021014035101c041c1c0c8a404482c070300c502c189002c080c000502543d00180d900d40030341c5034940358249022001c0d480c00c1016047c1101c54100701c0d00c07881e6947d2144401c00c42042401c80d034 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 900067500 1250 900066250 900066257
    0xc0c101b1a061014070501090c0b090f04020901211b0903120f02030313020a09090b0613182907020a0501060b1903022109161505090d1509060506040b040903 69
    0x944074032194400c0f00030700a43e4400c0000080c0d50301d040e510201002a998015500c12b800402d281c01c01c1c2c1010070071012402000c41d02103213000341c5138001800060b0055150703c1c1075111815614107410443e0701411945000304115184202c00c48002004403031540012228141d9418480009030b00600c03c030600207200380c01850442e5601d030070391a4041070280381681c0c40bc52041c00050710041c0e522618009034000d03140c1044915100f0140800880740700042e09160f883c10b07012041f000892010008540d0744280391800b260704c0c01403140020885c40314448500c4014400340010301d0380014102014600c101d000340202c5a5400301d00c0c9076401006030000910303071401a03081c00c00740b00341c1c001c07c0100460103043d031182031041a541d0b440d8a0860300b1a2090b4001e00080b58003124034910318000380442c8504401394170204e04024004e000e00030106026036003000904003004102c400348000d6264003041007181e001d035810a000601401d44075140150310301100e454640c1004d004141943e9010789 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 900068750 1250 900067500 900067517
    0x1009051507050f1314310e0304240f0503061005130f091406060403080a0c0501090f02040e0d1403061302070b15060c0c101b1a0610 58
    0x140d568040000051000c070411030104680045482e1000240842c045003044131304440d418000440018141c01d070034680b081a1100c918017000c2c540c000f00c1c420500c944200130200d4218050400701810f021140c01c041400089000303d182c46104008007002c491032083c907103076804549002d4414a2403a0703641da0019a0810005907103040110a2034038a01691401b540360a445808400140790303950012000714510b10820401d030b082a024100300d0120001030541c441c01d0010015581d0700c101c0c030000b461060003207840940715000d04801051150000005d00076801c26103030041c03000c144210b04074410303480c06d003030951015000580344641c008540c0b1003500980094284a9075030f0802800b15a00c1000034007140c041d507030703240044c2c6429481884000c0c05c030701304141c080540f138121200d01809204240008452440000f88020707030000144c9002c0001d45683c0c5088800040c208071540200040e07092503400c011b81e910102c00c2c01c4015500484031601c0f0701d0100800c074040c04040d0300001f586038 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 900070000 1250 900068750 900068773
    0x130c141c02130905070905101b06150f240801030308190e0a050a110d0804030b100b041203030b0118050f0d02180f10060507080702180a020903100905 66
    0x1a4010b25031901c0100610744502da036006400203036101125075400140790070710108114100044400846540c0d414101c070007440110002c01c00740440b0f50060240ca0b00d640c101911241070b01115000380c415a000c0354074554032017a5014602e104003400600d00802c3d6030103003420620821805044c1c0341d041da00d500050302d514034055200200c100d00468817641c1c41201c19410710080001c0100325100368080c00b030b030004a0070501c10010281e0362680c000c468200001000175805000c0318203695108907070020644a007031405100c2111500059035034540001c001c141c5010510346405042d2296a0900605000c00011500010031070303020802c54a50500a1041d45040005296007500241c0303944004226500000c00304400140640c07041000c9400340304101c05403103030301d0342e120500c0301c040d405180ca41b1000403c01e02c1a100042e000c40408107101c0c013103568001051080000260091501c0d041100e5000c1c002d60003a410319210348110300c058107107441d40d405440c000da50030402520424405 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 900071250 1250 900070000 900070057
    0xd020106050a121518020a0905070503041202120418200306060c011112090f0307020a0303030f02090301090501060801140609070333030209010503010e101a130c14 72
    0x31400803198800c000c58181340301c00580c0704018020203001131041015645005000c0020519007140000074146010030000c5600a012260842e5109007403802c14403e8550481c02c080d442500007045031000140081c508018200c040b0034a000d2010400450400b200d854008007861001003030001f1041c40068403501e005000350801420000010508425002080e042d0794404030701e400c95010130341c042c080460780400050b02060f460310021440c04240d600017410104081c0301c010100360700c921000c030840c001782d0191f0b00e20141c058002d00c41c1c0310b643d203801c80c060b164500036009258070f00a14104420320042140e80030325006000d6100702e440313020085010f0000c91000004401518912150010303068050014018507904203010140c290710400c9520901a130280d4400d0703040454055600d00081001159031500d18400504a5413241224071922551203007036502425003484401c81003030030341080300c003c14160f89036030900e01100101000c5028900413811800104400100d0034881d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 900072500 1250 900071250 900071279
    0x2030a0c060e121b0c030a05061609150206040b07090308070b060103060e1003060b0402091c030e1008010f060c0804060e1305090d020c24030604020408030f0c0d020106050a 76
    0x600070a07203201800c0000b00c240d041c0c3c08015001c1c1400c09040c840d1302d201c10184132a12940c1c800f2809400f941959884043e51910f0142103c01020600d18080d40750354000c902c100c0050021020440649401d1a8081d40320070040ba0113070344202c255000142c00e00d1007548084240d80c0e011991030b00f4250151076648000f0300052040b4103041d0b451002280300084007108500c07818401c94004852825440c1c940300791070424050342c0c021401404295169520020411101402c03a1110040c010f42810111035080c00b40c126560020007181c0400c00702031f400203a40303041c0c8011b80070340d002e034aa03520400c603054090303100c0c041c000381402d1000f405107510030400b03d074420301e00411411944111220840449509680c8410b40303900c1550081d03250b68060204102d8107004a401c91200c06100c071849103801c0c907450343d40ca1110300003c0010840d44c1d8580c1500d010b02222021291510204106183c3d542e1010003000b043d0b2242a04180d2550b205001e0b6a003541d03800307080c001025150a400200405c03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 900073750 1250 900072500 900072521
    0x1b01020a03080915090a0606050411030a09060915060509181507020f16032a050103020d150f03260f0715090c18020403081213050d02100c02030a0c06 66
    0x3c2d4002644c0488003403034440c0c004d942e10006001400f03041d00d8a401212503c0d8045806141803802e800a60a000d200340c071f500141403040450400201d162200c0240800e032401019213003900d01e007000b4003096a1141042e00c5003502c20342000d403500f20034000f01a8100c540f090455004150000d2040f0103001c81c25008081801102e030104082d94000e41403a03c00e26140035000c01102c0c0030402e00001c0000d24114030031141c660b040c0f400418681d0141010503010b0b25043c941c001802c005c00347d28540c008401c0b440885561400b09842c0c610f010380d512a184000e0b610310032101108540c852015548900101d41a210701d442e24035245207481d21600642401e850b030b21814580344c2c05140300d5018003d88680f01d0381405800e03600341a6120309240405945510841c4144800e20000d030f82841284c0342624603034007680441e5607223a01082d04a03032001004025000700c089107443c41e900000c200d0b610303c00074481030100b500c1603403040740d490003407001d880c0004e5683c48070751300440c11a601c4609002d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 900075000 1250 900073750 900073753
    0x406031515080a050105150f01091a040e1e09060c030403030908040e0f1b0705030706150b040e010306112502061911010e1507052101090e1b01020a030809 68
    0x8590b6600c816040c090034080980e0540d454104111106641900140c5107050489480345081c1c0d0600008064281d64007031007208200050100c081910f802d4169001030241d1801c0320a1440e10a1540041c680c482d25103107001203420010860345400428250f108101e444215400d5a0b9a51404c4018104c08003003038540700401c04c0081281d000e40d02c1243d1140c44007010340c65003030030020025a00f2000300080b08030a06c400380480400a034011080b25441d0790419800f04802c0c119408401031040030b07034062000301000150020b0300901500046049a0148000301b28107060780f80c1080b80c5106107010380040303a041d004100b4a80c4a0301d00d1181c09640044c00260511444a4141c5151705050580001142c06405090a1040309000301000703410300c50040c1900a500941118035090041c00201c00d02c000401d400f03e16a1a4598440442484141d24500d6581d14480d000050000285600841c050b00030b854085040b80085100c0d0050113174024041098251400c5440000161029019 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 900076250 1250 900075000 900075041
    0x8160807021507170a051803010f0c020a03230a11012c0601120c1502030d06030f020f0901060203090d050c030a08120a0c1d01031b110c04060315 64
    0x90307103412800251101c00500382e15510309650030f0506000b8030b45845502c200c20700304180d240c0194048280c80b10800c0c0b00200c00003000160000a000d443d20451140310b142c0b4003c0e40c0c4c003445600151802085001c0d458500c081c0104440e190541c404400700c3d503c4a6000300802c1d000d05209051458089540100004088140443c00d05070001c0c2e1040d0541800c10340045000e50036010710645004001d04508040c1400075a504c803000c1d1083d41c030880d40f1351800355007200d1303c140c024400c07200150005d00e01084803544034541440c1d101460314003640038148944c00050b05040c074405a506075003481c1c0007035041c440424100140c0d1000a942107885028400074500152020044180b02a104510341500e03100001d82c1560122402090751080c58113040039205010740005d04c045a5a17403c460038000b808103000103802a00d121000c0301c0d12241291a2407400540c402c208890381d1610f0802c1d00c0407841c80ba4200016201f4500020342132882140d8a1010080b20b944904048a0032800200e034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 900077500 1250 900076250 900076253
    0x8070605010906060f02032d0705030a0909180c0b0a12050c04080c01020d0e01050708041701090629060705010e030a05090301060504090f02040c03020c0f070e0a0908160807 76
    0x40d68002c0c1d001c2d8802c1520343c1c0041c0813050700a0034108980650b840103504043c2c861300c00811120304403071032a0580300d0b042e0344030a500405500b1541c0e01ca400c08200d9507a007032007040c010a102820320400c404c3c81e03c2c03c603e80c2008035250304039100f803607000106c0b0a6031900701150f81c0225171010164505005450901307005600890181ca03121300c08154249440740c2ca0865100d060000314a58141190800d50700103129903080034501c1400b00c42843c03c55240c000078940b810710b922540c0c20144000401241e0420912015004100030a2094105014041549494031500050344070640344c02510341d4142103903818044085c0020601410000c540203406548060035030b403004486e40c001450002e04640c1509003401020010001a00d0800008900d0f859084155a08010007407246403203090011501d481b80c1c05a030024501e11090721013003c11b4000c920f59a6030030f446407400b0b03481031100080000c2618442c000e23440386c00c4032150745844102e07203500100d03140003002241c0c10a0306000010 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 900078750 1250 900077500 900077513
    0x120c0406030510051e0a0f24050906030f04020607061a010909020a020d1803021f030605101704060b091513110901050a120f021b07081f090203030327280807 69
    0x40043c80c00341c8c1c00c00c8080380806042212a00b102050300e091220802004007603031104421650711850741c0002c10895110343c4006000c505c41e142001e000542000d141b0041240d003500b5102042400742c03150429555100c005000b603000320a02c08015030031080f0130001c80c0307008031003040c151409647d6000d0490748030340c002140c2c1c0741d25091407003071110240855440e0030f030548a14000b4082c2242c0070001002c42c0d900c02030100444584400b0800b4000300802c080042c1038120103810270006015070543c1c94800d08a00c6841107540c0f40600c655495003641994001c00d11803a400c0d0414801202e25001c40c1400546569114607107510820103000e041c100170807800c0c0700714040b541c024880540e90f0356000548094007044010707505500c0e080f01c58208000ca0001074001413000800710049644000c0031410305c000c000040010350980400403c07c86032031a40d02d58503c0243c05821014002c540380e1007001e0f6240300268195014032091462800c0111500d003a03261494821003c0910349012543c0d4403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 900080000 1250 900078750 900078779
    0xc0d03030501080f07080c0f1c0308160c0b0403180b04060216090209090414030d0603060e0f0d0c06020d1b0309021005090a090c05120c0406030510051e0a 68
    0xa400090352203005008a4505006a8a202000d0801401d0480c101000705407550b0215000510643c0f440041d11155160041922805695104040c00600242c1009046140111f4642640320341030a800034810340542d49000c081c81e004840e620b010b03a03880d50140e9803010b01c90421295032720782e00300003e0182c20400042028000e20f5001d85003060b504543e0003d0050a6007108031002d005003c0c041180e151400c2c0309034081d4220350707207655203020080a1800c40c403411071990842414a41c1c0032042c0710440e00101c4001c201501250300c1100d810301d0054031480b000001a0004040f010040081039664001d008894001003000403907032200e10b10b021041466000e442c4c0481e03154441103081d85003918510180e9149414854640000440000d000904900a02d4070941d41e40711081d42c158803034415070780c19048644490107142485c040740e002c60b0300107215480010b414a800560103188030b407800c104849000d001c1c2c4c550418041c00d200e030034400525a60790082c403903180c0061000c0c00007251 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 900081250 1250 900080000 900080003
    0x120c15060501020601050904200103060f090b0f09060d0611270a09110702010c08040b040b0705010513020d02010305070e1306030b060d0507050603070315090509061302010509040902030c0d 83
    0x300d20303282200290500e44140c0c00719215401e0703802040046040c510702c802d8030240128200c0b00e03104200c4010307001441c06401012076131800341c034040380c00503182d804a0811141210240e0aa035036000404c003020300c0850b070064010f800520309200041c426048441c40e01103a1001e0b034107010662146102e44501c52648180c0981c1c850b500848900b005410400500014007092000000b01c2c501c90701c441c401ca08000381001071020500c0d0a00030b850b002d5601400041803003541d04c41d51510f5102c0d07a6040b2000c2541c05510701701c00b04a0350000141390549071170f400b404044043d4215001500149001450213080c80005009041d00d60340b400001e490100901c0400201c2e1030442c00c041d4441312000380140d00804841340010f02080d800111501201c500700c600c15641d613101b01045000d03003203a06031200703e0181d0800114518080f500094032883d400c00c01c40d41c40b070351100c801c0d59a81259040290204000704034611003401c1035040030454a0010b4122140e0180e2980401d01011100e0030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 900082500 1250 900081250 900081293
    0x60f15031e040b0106110105060a05010e1210020304050f0a030206130f060c0f260a0c0909020c15060904111309050f07050a0501050307082205010c0207060906030908030103120c 78
    0x50101c41d81010195201403070300130023002039181250201c3c13204c500c2030003124103000b03040062440d20b556096805880183c12000e4482060244070010003035003096604840311300450500c10440305000403403041441d0103900070145038603608000c3c0000c00624400f41c45183c4000e40c0707140881c65500400c41d0304000d5555031402d1402ca020020000c000c3c000e500708000e41220012a5603302802689400200c030040000c1e0710a9011810b884852203039001c440a140007003101c1c0352500001c95109108082901c1c810b00c6035640c1010030401d11402c503002003030000300c90b81c2036201c0e080c4104104000183c00d00000351200098481742e20f010f216001d81c007410b902c00d80040c070080c24102c1107280101002e007010342c00c40c14005400303085010002c021816040512400304014043c41160440c0160480020006031001040007510ce0405010700008030f1828040090b03070510078400d04402d140c11900c401c0c156400c40d40c405211041481021007001700101000000c903000c41d841c201c80c4800a40c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 900083750 1250 900082500 900082523
    0x7031d06060112090305070204050604231603181b05030a0c0536091c080a050603071d090a080301080307150b01091412030c070509060f15031e04 64
    0x2000510500c03000c818900303c0c90401c0305010010b0f8011083d1503010b0750445000c10260340321804140100012209410640a09114540380c00031100003903004803404400401000719110043d03064842d00351100150100410300c50020541100208407021000c100c1d000c5034540d1080064a0600c00b648152151078000b02c1c1040b051815802141003410300c8061201c9946481c20044a100f460385a0242000da8120000d50103407020b120070405c08100c2c0902e040c00e0100c18100500c0d02c00100c9002480e1881e00000c03a10500c1d00084a1044403004410309502009007042e850800901510100d034510649030500700068602c406140a0708260000b99180c2c82c86090042116410104842d0030510349041007100d0303644402d2030815030300841445111aa140c0d0045202c0165404860380c1501020981140d02d060109e004000c03240100c4003050262a194208190030303681c001c1031540150340300003801e00d00b210f14014582c0300d1002c00001710420700e1401c4120380f689080300d04595003103110 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 900085000 1250 900083750 900083761
    0xe0109240e09160c050a0f1406060316150519260705073201050108010c0203030906041b12030305071b1a090f03071b060819020307031d06 61
    0x10341109140c140884003801c050814500540d501040390403480100840c03840140b0601c0406c0144580190b40080041260005814200b103064410640040785000c1e2402140d01c0c3d290006040c40d14244a040580090b03280c0340640140c2c104074a4000c0912006101c1840070b4041e40148100082498546038910714860031a0300e900880c0c0ba801d2305160319580103002242d584101036900070303544100c0c1e40804010408105210030380e170140010f2600c0300144d01b1201010107400660488110400a01c100340c0e0020060b600c0b80012120b98135107038800c0000801091020409141000e100d0400d40388458a4030034249503100440c07400c0e000b094076242406516548292450400046021014120081d590b41e040510003603c50f440707051058080820140e800c18032005200c5c00c1100308036a40c68250b450042d84500162030344000c1d40d880d528001680c18082e00c0501e104155000207060900300b0b241c0d50314020740004e070180f020940d51741001012000b041c000800800c10080081030079240c072 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 900086250 1250 900085000 900085007
    0x150515131514130e04060b0405010f0308121308040801090b01060306060c02220e010e0c0d0510090807020604030305090a06020c030c1324030b0f1003030e010924 71
    0x159804000203000107a41d24500301d81c03003a504228501031480d115500d030b00445002c89018441d81003010043c41d44030034002002100c6c0d0022204c1c5000f6030f407e0005e60798030b440510070000b442c480078010030001c02200c002065095612640031031070f0780d2003d10344511515225019003240d00100a560340da00c50b80c0d0244290400303500d00602e0f0900e0103120341800c0c404000e000d442c0c8280c000303000352043e082500803100d1407103481d80c130300c10011010400c181d480348400380230f041122581802c50040044115590424480001d002030708000100401d0011000d50306c010084603c09444d800800e1200000580e203920040000314040d07501c064072503210108000f90300100c1d81c030070019540030510110154501191112003441c00300c42d20312a1800131540000644010000d10880440358054200c0c9000d1401c01e840c2a02c2c017440090b007003540d4038105105401d9082c5c0e00781c518650f0f00c40080001034400c20112003d20010300d0000022076580c203241520f90500315202c01c0381d40e09004040d440551 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 900087500 1250 900086250 900086287
    0x1201060b07030c0c142d03160504110901081305010e0102070c090e060906011505300c070c0b07050c0d0c080d05130603110c030304081c14010504150515 67
    0x185954a022517a07000081d550700c50341141440925a9060001484109034003406400380007400390713200e2030f0300840500e003040458060240b01d2480d0484034000802c0300d000750744081a06840d40401500c1c0d96801115000c51890200c03229034a0700700300001c5d4102270000d8611507102d4090032141d40e0404030310308241d4140f80b88108603a0b000c031003000401d0400180c2d060440b0280f4207080d00d584070200040759180b103108500400300d800c2c866080c0a4040c0794900e00310440d000250080592a80c0340440c0880c82030340b0015018181e84007091081e11800300040c407110307224004a500c803141041c04a15980c503455805d071410350049078200001141440310702850901c624019280c4100d095852040303c5850041c2c0d020940d56081d1200e140d5210421600b50104e204100c03516840c003454401d80980c88241b545003035401d0500034103803800681c0191400350071806180d030300507800c1c0300a0100410640c1c0c1140302d40c8590320000140c3d0307155484055483c0b100c414286548004d140500824002d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 900088750 1250 900087500 900087509
    0x1a0702040c0f200106030c0b0d0e160e0a060e0a0906050601020a0203060f041403030a020d0c0e031c0504171e0c0108070c0213020a110c100e1201060b07030c0c 70
    0x112070b000c0c1c1201c40e481a20103601e407000500741400c4083c072840e007500418254100421080815002084581f0401c01628103801c17440404e0220b0010745000c0e0742c40d040c0500e0303003115038854441c007480700c448000c0240342c0c050409080021900c0d40e039803030f1031a45c5074160341c003800d40f135900c14246051000e28050154851000c2c00104a2080f159001c0f03556008009c28080020402078003040c00c1001c2041c0c03481f2500d501c103046903180c1c01c001c107820000303500681200044ca8175081c040300050380203203190b03c1c500000401901881c1c140c1c00c034a4801c01c101c090b183d000c01000b0080450604080c1c2a800c4080341c40f54002c2034038900c0740c0400003095403580171030943c6902019140aa0b40c0e0310400090707004120780f400b507003d00011302c0442c0c2c030103000715600013401e8008070b0b49114060384001614041d40450049402d5006c5035010302107101080041500007402446d8243c07860b052015400300c0082c0d03500d00014490356140842280d6802c4144101c0004401e850080180700c0c00032084400b62 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 900090000 1250 900088750 900088757
    0xa0509011e02091e01050702091009090813061814040905030c030c070f030506042009070816030608030906071a0901020714030f0d11190519110a0204090c1a0702040c 73
    0x204c1c85000040d10a00801d10024442c202040016403504103405c1c41c14001d007140a0103200803c0307280382c00081900034070307212441c1800740d02d070002d6010f200e095001c2041400c841403a0a1505004a01070003400c001c1005801603100c4c40e4000009504100170151030746100c0c09103441d00001102d40303083c010b40c1d61216854048140051000c503d0100307159801903402084842c003400800e41a4201d00320080d84550b102d44560200150740341c0044c81c140c0300b00200e826054642e60760b17200c00c0d030440350140240b1804d517209004260060401d5801410828050b031440410341c0c2e2101c050001c2c4450884003458140d4010441c402000300b005e50846d01000321001542c00d0018042031117080e03010b000b03140c0701c820703840f03149079000d03600c00104984800440d103d8121000a0086000d0b24035403202c5812550305002c00402c64441c2c0c4950f40c0034801016000c080c064041c955000c000c06010010015500f2411403140011040c0300d503094944004200288a629945d1600400045a040f40038480a1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 900091250 1250 900090000 900090049
    0x7030e0609070b220e2d04060b0105070f08040e010b0a080a020a0516060c120e07030b06061312060c03020406052d07050606040f0b0303030a0509011e0209 68
    0x400d00c08102c0d0340a03501101030351500c48015030140109002400d081d640c240304c2c0010040381004100041512070712810003007800c40350403841d02107103c2c00d0002401c030807116100003090008103150080980c0034014904242816802e032208004280120011114404001001c102556402e11701c503005040c001d00303840c00d0071001030014150380300060101d030025a0000700c40d10440e004005440e90210586149807900350607243c210001c1001c40b201001044c03100460040303100c041c1c025007403403402d0a005000d5130303031659880c00d00d40a4094801580404140316480b42160150302140040c03000302c1100001000c5400c0440403500a20b5101d410503004100038010380d42c10408440c20504480003400104102c0844a1441c0710030145181ea045400a107450620100060580c040d00c000c81d010040128801e64410484d6030080da00c5406400900000380038109a41c4043c0c1d00c05805130020802c044e0030507120a080c10b80580c80000140d020400c01030604143d00c02c010200d2100106001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 900092500 1250 900091250 900091261
    0xc03071403030a0e03030403080d141f21050123010b0711090a0b03010c020309040e07080d05033601140702030d0221180d02010c0e0904021c0b07030e06 67
    0x202e92080c0ca5221003400420400d41503c0d0300c042003120001d54114080603111040d4034041000703441031900041041840c54041400d103110718200741e00c55440b41c00f10800440c904811001c48600f1901c107600c10140e48100c0b1030200c0d100303015091000154000c80c44241e002c0020300030303c500c030680180090000601c03ca10015100170f4240c001c440d0b0845450741c2035501c100340c220140c030004081075059401c0c291184035164001001e81015101194140010200d00020b907598041034820b810203603204118120b28a80101c00031500481c140d1440c0654210f00c079448140300f4103140c0012003003140e400030a175044000384100c5d41610215079104a040c02c2c42c0600179541d00810b0700340b91242d03600041940c0250902c2c1031049080b10703000c0e42c0c0119407400c5078404944800c074002440950080f800001a140d02c1807280d06c0d501035080c0c0303c4600444540d824000b50043c018000c0380c00500003845c8102c15207006459110303041c81000108214074000c2e100600b503442c1e00e05013544070b50041c0103114 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 900093750 1250 900092500 900092503
    0x110604020405270106140409020a0509060112020301030c0e0a090201080601080901062d170d0c02211b030a02060706020d02091c061b170c0f0c0c03071403 68
    0x150855011500440c0903201c050044812081908060b89540c0015401070a60141904513008454850f010244d0030400d040030700040d0790403414025031100100740280003604d410929035810081c18034207509465040e041100890b8420b0b0003e81c0c500b2180301082001081e0b252126900c0041c150090010026a50020b000e82401600440c140030807070700040e005e20800d62181d07005080032002900c00d03022800c00d402000b002c2d00620b0000b6070307000f0008210301d4169071884244942580060111054a40381142c24280507001240d22006420203040c00d10388a030fa0800a02100002030851540c034040300f094001c01a551480c000d40042031140c025a48240940c0c4106400200c00f50340c2e00e54540950001780f054441003644161000003954200a0781100d0500315441640104840201c10100504100410109030000340358a8a14a1908600000c0e00d8008007414400c501b880c1c00400e210406400414100d0740f2640f00813120700541c60f040181d08000c002c90201100b07180c40442c08203 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 900095000 1250 900093750 900093763
    0xa0c170d110d031d030d0e15011a0901051b01050f0906130303110d0c0819061410021204180b12060601181206091203050712090c0b070c03030f11 64
    0x240180f5948100711007003048030007403444804084c5400c1d00e81d0368941e440d040f801040050a050540d00c160020502c10210552019045e01c0120200c55155101c140c8501c1d4aa4440f00d16035040000c01d100c1805c0c0040481080c48503c44088004078080c03511146101c1c1c1c21500800040e03940d4000302c02d1118848040310940c5a207501840d0120700c0a4004a8009180c410038240703030141840c203003403031a40c240e10224141c06a2802c44002c20386000540c000815a03019000700c40d00b414441160f098149880b1110b50903549030780c010344a54011001c9042030a0f005a80058406004c006690302040010320905002c1001260000648180c10403002d0f5070f900000c0100b4144081080c060100725a41601c0c1d100a100c584080b0304014200e180c0203002e46040c2604940d0310f40c4031354030650207034068001e50340b0130071903651a02d071310300f100b600d5620203408906c00603038005546c9035001c40c0d1a01440000e014003170265862600d841d18500d402403624000300c0b086002c11800880102402d400802c12 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 900096250 1250 900095000 900095023
    0xc0612110a18080a050f120405100e010309061b030b0a0b040504090510241721041e0f0b070807080a05040902210c09150c0a0c170d11 59
    0x10000d07601640302d0070341030160690444001072007001050320401c54000f40e02940e95240c5820f940300115548803d10f2140901e01506500002c0e600c08102010300c00c0000426400052401150844d01c1c1d8403240f00700da444031401900b0f0242c0741d0b02e05401c1500b5001da15103945040d2100310404d0f117000400d441c180a180581031040b91070f1000501071003010819903440c2c0784851020024040c01040041c0481200500c800c3d510a00d41000105c04010030031100241c1182e601030f001c3c0782c14410240342c400d10402c0030700d080c0c00c4003440089031149440704400510110687d42d41841402c002188004040315480b01401c003004004000c0041c0e001010f907643c01c0d031701c6079240392107500801c01502c59001700d42006100502c045088114005102141500001c482610000546400c4005540c904c10300e03180e160401c0382c0c0c5010000001c0820000d200c08e25021043e11000445c036036650403140e059500008400e00c0d42000201e03034540501640030b145503541410003000c0c210640098485060ba40c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 900097500 1250 900096250 900096257
    0x70c0209070f1706180c22060806040c050c0a03020307022b380a060f050d1b120309081002041d040c05090108010f0e030f040e070e0603040c0612110a 66
    0x2046140d01c0d84805d1031840030014400008038035102c01502559044204205100320303030320320500208075004c04d4407400c3d0b40b090340d100c81103981d502040c4009000071103160010000108400c2088003010300000140382e109a000d1980d5503014010000a4003110700d0b00d2008444128907841504010403e0104556124007450740500b40c0d01030170b1090104120904500101030100b4810001490507443d11032076a0040800c903840d203405280d0301d000b100d0701560390000c403042a07080c0420f1000d4540d403e180341c412141048035458100c1c04030248503101045000c503000da40203200d000414062224800403905086052a01d042c0229003000703103085042d0210005000030400340041080c8882c09000041c1a40c0c030507580d02c41849009100040c049811342d4606003000c0061440481110341a202802d981d504060038a80c483e03101101c041c1c14441840340d92008285580c50b44405984603502a800001d025460500041d101c0300000c0075010300649000d88020284040c507050301d40c448c0380c1d0f14 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 900098750 1250 900097500 900097547
    0x209030105100e070c051609091202010903140f0903010c0f02060f04020307151209050c0f03070302130209180702100605180f0601090504060b1e0c030a05030618070c0209070f 77
    0x6100b424460710807081c887c4103511074030201c0c0c5039030b841c1c0180d091320f4070484508180600d0200101d00b00d03004458000c000030301c541460180b042514001c0c124100d88540f0461400c0328890010382125030355041d280215501e030750403051058044c0841c03548007020780c068540620b01540000c1e120300c22070182c420440e140141d01c54166100780041c04d003510304007000b00030503181800c01c9507484607440543d074450441106030300301d18240441d9040403a9800b40003c40340c82d10902c6000040c0d000142e00c2900300840324128a00000c1010700580681101d030068004070004420346015150940c00550103110000b4281d070220000803c925032000c0c02d8280308a01e40c079800d004070b5520806500450303000c1c1c00c1035030109003900044000e10303010b0f181d0302442c4100102070300022030a0107004001000360700300303000300a03090b40604001c60340550002c164244540100715200c403108010344000c400a1170164800c030441c1170410065401141134285115441d04504004041d9603801301010912101c1a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 900100000 1250 900098750 900098753
    0x108060a0b10141606090311100204050102070b0c011103040b0a1503030c030f141201150306030519020a09020c0d141c0b0604090504120906030b060f0a0e030304090209030105100e070c 81
    0xd41d03044c0c1c025544003206100d4903035942002880c251108500c94214020020709100e228483c3c03003158100c98042c0c014103405c510707021400300e07203412550081110303540b47c0040c0a00c03001600300a61242d48030709501005030401c1201c443c100c078210300c078140801c04800d0040c004250404c00240c1c0c02d507031624080c803500c0c03c6400119840d0b40009080325080350041250703160490072580e254180c80242c1b20440d0190003503c401c030160341c4a484040c0440d00b040c9841c4440c409070900c00810b45002030441d18007195202c1c0b074041240d2025101c5005608105074281c25580d1026600da4660080508141408110f2181030704071140c1c140b0101c400d81d50340040e0211030315a001550010f1031000da08208500d0300d4240301c10a604182d102000154003801c3c0490728034044d204140e144800901543e0600010b03035201c011b02d510440d05c10041c06413501c4240c245680400050015084545000d82c49a13581d00c1454252003010b0805c0352964402c0c80184034403040502c0b455400005440c10394903082c00d9 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 900101250 1250 900100000 900100027
    0x2040f0306051e090c04150b0703080408040b31050f270906010e070804170c0a0606090608161406160501020703020601050924100e090108060a0b1014 66
    0xc3e10340340e5a99a0201c080000c440d1000c102245000c80541d0300b44404400b640e00210140b01c90b01131219081c00034021100460300c1000507035809445039990300e1402e5203414000d00960010384800303401020031104459040048041d60340c030f0bc00c25100c440000e60030480041d5004002000e058051640900000f00c0c1c0d0340d0410594441291000c1c001d00d090412080040c0c03946001d009a0b0101000040416849031058481c107202c1c50700503400400000c0b800580806a600041c40c1d108688269007407500400e6080c41180c00400003820300003001071420310b9050500303000c903502a44102055004002c0516110a452002c038011100035030307111072103100160f0100c51a54007600d20342c400b1a5075000c0680018005068034000c80d44980c9560b56046c40300d450304039070b4a1010351644070038440c078038a0030310041c030001c460700d107081c00803486107a00d01060b1390280980c000f400940c008400e100011340e840c49104030f102402d940c0380d14101429000070f44205030801428020410010350801c10304603 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 900102500 1250 900101250 900101281
    0x703021003090f060e071706040303050414160609060e010e0907020718090303060b0f0d0905071a12090c090429040f021201020405010c17130b0d0c020102040f030605 73
    0x2c3c842e010110158041c14140300820038190030705028495804040754240b148404100517410030340041802c1ea485907003c9020300310240c41114807119884903088801420701144440141c0c08400395000c2d444e0032401400f06056a2202c0e0a00c40c0c400034108141c2d074070074900a00e04409641d02c009a8a981104901d08031076680802050007040e4850306c108041508503840181c006d43c0d041c0701c80c9071180c07215047c9104030000781101250410034401e100e100394011900c40e40c00350041d9035031160b81d800440c20210b40b180c01c81c0d601d1880050302c409804280b80c8030300c3d080041c510060000c8920000403980383c070300180c805890020036002d8050803108600c0701002c0e10081d403040c4401c03824103150440100100d902c0803489641d103e540c0c0e1810800500c240e6040307800503942d0f9035070074030642c844010440c41d610300320b56054001c01a10b500c020400508038024202410040d40e46c007043e100718021202c0c030013004021a4010082002419007400000041d00d41201e000103070380e183c091001e40710a0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 900103750 1250 900102500 900102503
    0x50f06070c030906050a0816032721091e0302030a03050a030b040504260c03280908070b0c0312090102030a0b0d0203030a1103041e0512010509070302100309 69
    0x4542820894a00d5008280c521114400d440e000034080c0c450f20141c0303180c011054940c0000e01c408000a03400c6500c203819410000e49800c0c001400c4641003040201510428803980c40c0d24801c07041042040b0a011210b000b036902030000341a400815080208020140e100f920b4079004e6a082011540d901c1c2d90384e080055034002c0032107502c1d0790303e460007502c143c100d00303086000700e4504210b52500e42414080c90340300c0c0b540701030401042901d84003403807040200f8104e4078000080031300c4102003640040004141540588140c01c066161440301410554107070900003081003d40d03541004171520004155040d110300340f030650744071a05100c4d80d0b455801604441c1002c2020542804214030040d8010340c0102070401d028010001c0b0382e030a00c5581e800b01e00c402074060340208190255640308400e1003890126000540340361540c4c540079202c0c904510008140e0400d0f071203404102a144c14402c001031418840c000f40300500d0b060a10985580b014440a8010030340034070340c2908544240d0002e82001e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 900105000 1250 900103750 900103753
    0x10050703021f060306050702011e050c0d0501080615100c030c321009020d23060709060e010804020d030818030f040305120c0307030e0a03060c021006092007050f 71
    0x10b0140000d00014240070311080c3c1e00f491505010501c802d106000c1c1019141c180e480506a00304010400c07001000300030300c10310035100e0070300a4a0440049006043c000c04015000301810700300030b13641c0140410260b18480c80740d40060f40512030b4030782000100c1c801580604002003411400d0070201c4803079280201c980d0030702000c0050005041c19441d9001002c405c200c041f980c070810741e440018102d4030b0010010f54410200d000c0720300004c14150018031060b5006282c2800540002a82464040c040c0d94400108800c064144a4190b01c0660304a9100d02440c141c8954200b64000c03806500000f03c0c0a820040c0c0f6000007281500b03224034900754001c020044a42d80c000c1c2c030800b49440c0c0c005c0d01081b100c40c0200000754220351851015140c002140340055860580103540a54001c0d9107903003025000141114008081821440361070004130085d00602866400001e20038216134107a0400700b0841c0c5400c0e0242501c1c2c622951051101c8044080941e48a03558240175150503a5071250694030f = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 900106250 1250 900105000 900105043
    0x290901030f020d060f0905060c091509040608010915150506121519030b0109020304050d1b05241605180f091302120303150103230a1d0c1005070302 65
    0x20801650005080f030303007c3d4096940c40d80b511005400c0500c40c0295095000c001034503001102203025008100c440e800400c00500980c0e11132181d42036911844003030340c400542d81d030b0344d41040c010f03400340d400342000394250b9040072414a00092998000d507807000c0100c06038440040c100e0f1140300d0541501c07481c002c0c0f04a00d940b848a28048500e0451b0004940e980d030800c0000a41c0c1041c0c1c0296805941d2000c050450003030340070412625003a0b0308500207404524828010003041c1c0c00d000304a508400b0311400030b0201114482d00131180405091629150700c01d0244089a07a80603040d6103000c078800301d04c0b401c0b003c000c400040c01a00b414a180f640a10300318180000980c800703401c0c64035a4400d031010300504091802c0e00b6260302003101c02d070554011034450b1078003561003584450040b401d5402c00c80084c1090700e0200065a8003140c01a41c100c0e5a0a00c03c0c058080740440b00c110041d800d002401a140720101046001d005040500c041c02404208481018024030541c1c2d182071994900044 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 900107500 1250 900106250 900106271
    0xc06090b060406082b18030b06010e010f020a0b0c0d05010f0501020f0d02060708070c050f070f051e21060903070309120803130305040504020a03290901030f020d06 72
    0x1000401d5600d2031055240c5040081c403d0310205003680750710361032595941c000314002001000e46407907805680800080300e1000705001300ca12aa00b01441c01002a00312614011001501051410b4046814010324010340ca40d003650024049940c0b5501070746552040d1142641610701e8011149440f118030b090600200d04490307000c020504403182682212542100d901442e40c0340c40f50000c1480050700100b0000700600c2c00b40242c42e0b00711950b4541900e030302044da00c0b070741d082c00b407800364001468001940811062014040810142604640000c8214071041c1c1c000803c030f202134082c5c0e00410407000038440e00c4030804000202500c2d4881982c0207850001d4403281c89600c85202140031406060020406c009900e41e1840e40756440b03604c0500d1600c600844484906400f403040303082240c1044082861385075030000d000c07a82540d40b804550843c40c034a5940000c0040c904003c1035200b507204103521651245065411aa085041b40000d85694008144100350781c8074041c4c0918288070401a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 900108750 1250 900107500 900107513
    0x1c140705060405070e10120528230c150d06150311030106090608060a030c0b0a0206011e0b0d090f0f05160506180307030203060f22081602010c0609 65
    0x780b08a200364280c0d480ea0b900d600d007101c90440c080d11a81211240d85d84103000c064034100740e10b913210f0f02402c1201c0f2034024411182c14150120340700c60031950318081000d0708104042c904509807900c90326401e0361454150400c1c50380c90103a110940e10503840c07640c0804041400004403000c0103048101804060780b14400041824000c540c0030000900c0c15804d2018070150f502941d0513a000c90740d03201022803070043d0441c2c948101400d4150701800082d030010000c3c0d034010820380200070301c0c00410313103c121140010341403450580c0714880c91840040080c1c10208900080806d460b8098074064130344640066840041101010082c245d1603802d1400040c0a60341214032005d80c811821608415a1800c010f0310307203001489142c0d00000180408070444044031034050003582d02a0460300107a5682d000030b483c003117040e1404800e01030520240254040c0914940003002c0d035604041291007060384c1d0704001407098000c800d80700315004010310300f10f80c4109107170718035180c010b9401e02070307442c1e079042c0700 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 900110000 1250 900108750 900108763
    0x200607030507090b1213030341150918010c180803161e021810080607020a030311090d0c090b0109260705060a0906030605121c140705 59
    0x810200e80c0c15003000540c81305900444e00315100c02200c001c595121000000d01481c2103031811014161114485918040b6540700e140b41c001c882507221080030031310901ca20b11100460590010000390404200603141c1d44112001a400c0c241c405102c60b41d41e0028031425130035580010700d0380e075080413507200390164490884061112600003d0307020650750340529a9a10807030001c090044c40e405500700105040e051f00d80078084080d00c004415030f000d0340c00112071507041c02d074600800040074203010300501e0420051018003108d43c0144068184094080c0d1b803204a05401810181c441c90042403000c0021f042d0381692201810401d00402c07146040ca6010707055000c0c64604514140005110790311030700d0b0410449003d41030400e507045042010b800555012141c28060303200c0c030702c000074240c0c803040c1c0201854a0156641c2e41c0c160301b04031000341a034595a0101d4820050480b460300c8042c0d02058280081080b0444026402d030300b01002e03260078000d0480300c0c1a8a6011440c40c00f803103401300340e2 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 900111250 1250 900110000 900110011
    0x120305010f0909031b0c05042d06050901030b10150806010311090109090207210c06060b1809130804060c0303050f0103170a02100203240409030f2006070305 69
    0x1038040e5540703030200401124203001d0302400040701041720b0700544198859845a1030300941e00181d5042e00c80000c981a107150791019203110301034543d000d03103105400d06d40f00f848511041e01840124030b0840014408a010f0001810f00c0c109040400d102806880494000744004440010700b40c908001c0078120100455009010a0078141c0c89100d48410b44103c1c0e8514505071030701346025041000060094010b284201e81320342c0d02c81c2408031001c0348140c001d000a41a580c1b44c0410b0440303440e00f60150b03803003684444000c10b03007801209024418108c00d10000e92054410150035518085810f40d800411a005131006000080c0810035030303404803034904450302a4a040c00240c490b041d03282c0c0e1010092101611035602a0780b0400b60f0421003006144003011841102c0022500002d0b0408992040e19150030600701c1600c180d50f2054000090389918004030740807c45001980c40c0544006d010317010a50070004c0c5046c98440410060100c1d912604045045560b180b034500c0c00a001401c1c140c46 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 900112500 1250 900111250 900111269
    0x12020c0610050f010e031b030f06011412010501060e0609060d0908031005191a040e25030506090114030106030803150f0619080a180b01030c06090b12040501020712030501 75
    0x4014030f05500403500c1200e13408002d00107103600d0030300441c40039219174080345090f814080c00c100c0a5000c0d004214482c06050130003056103540c1111010050640d032850b03076401d842c1c1d0518004002c03068105031449106070043d1038803551a400d180015107544128084000ba15280c41142d01c01d202c0380001841c42248601038680d01143c4807802c100c460300c24002d48844145032150148125031100c01c001c000f280c1090606030038961034000b4458407503811100e140c11080c2003040c81da01402036541106070103c0342d040c100010b041040104000c00814002c00c2c0840400c2200042541c60944c0000300442c3c1006925849082004500c44881c10200e10ba03441340100700c80b48103091405404556850401480080f52580440300903942c2c40c0303004264040d09907841185090b96203001600025040c401e40350100650b0462404050381f0311250428001c000200a061243c28141d000300d81d03500780da031504481c82c1e6a0350320b0b14601a104000c0000d20b904040900441a590181c1109060316038189 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 900113750 1250 900112500 900112519
    0x1031119050315040c0f0f0b160b010b0705011406010c060b01050903010c080a05070206130f0501060302060c030a1106060d0611070231090803040618060606050d0506150a12020c061005 81
    0x40c0c6201030002d140207016600300500d030f04204400422008200c40c0d444503406848502c41600d862b49544001da0041d0760040001071a502080701c28820002c00e00f58640d4602168101030300001e00c0072003440e000901c0a555469408543d0b8012825901503a00080013408814018100103180c5902512560001c0c0c2c00d100101d402c090001c02c226200300764400d200410741340d082d21501c0c2c1c048540c02080d2059561648080301503121a40140a240f104034021540e0300c0541c0001425544d0034020400d5641000b010710034150b8030f1608820110390841004184103201c0901243c180c030134168001c1d4814210581d2403a240b41e41412480ba00f9100d04043c9500c00d042031200b815200813507030081c80c0b40740402c002000144c040e441011100701071144500502d00365902e400480b05190000c20104101150842ca46020f074090075901100543d189010541c08142e0900c450243d88591814840b4034030240c10340728400d0b410b40c0c075243c0141c41150b031242401c030842213404c4403d000e007600412081 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 900115000 1250 900113750 900113759
    0xa0c05060a060611070305030f031008191a09070510090e18101401261e0f0705060327100906060b091f0c0b011410020601031119050315040c 62
    0x17090b40300480350800302851074403180110180303155200910349454009072100c04a02031030304011000171510300000608001c0040e041c0f200c046c8144c6e401d100c8600403c0800c0000030900030440d5001c0f030300c0650700c10b403920f614084150b9086005400c85803041000108020240c05100b180780e1052130440142ea055440c8070f000c01084d200300d802c9241c00c001d0f01320010000030b804525801c06403402200740c250712402c158685410308006c42e1050781884504050f00241c40400d02158040c00151030040c0405442c044c046000d5020060141b01e5040422144502090304007201c04900100380064800400c5220494001059240c40076a9014509000400d00003105402c8070b240d144010400c0c885981100c0042d0110403081e04844201f20140109100142003142c2c2503001e007407030050804480340d210050107244000b00520340d045601280041002c41c1d000e0300342450301401501c00d0050244012107442e80310169900c261b4151040405002400022880d01c0380182d00c1000d04480b195501c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 900116250 1250 900115000 900115003
    0x8150d1a0f100b0901030e0d0909051614070f0506090106090b040209060910030b0d05070305120a08040b0c04320604061b0f080415030b0a06140a0c05060a060611 71
    0x40b1028100507148450070300c81e2001900c00703410001c0d014036000c503c06160030740d010308000c076580411012815a403070034400c1c0b000a019590b07101c0c1d2100381403141400400e50050032600c030400c41118040000403e8824007640c14000f42425420004644240c24200da009009100502c251050103141000c00401032034075000304e448040c4014000d80c104001c0804021007440c5407440f000c20715030f40f0741000707180d03407a40030340101c0c802d00420141071b11601e181031150402c5609032401d031591a04011040c0200e810048a540040c3c020300c0d8429560b076140101c40041c411600b181c031a440c44000209807134441104000706c0d041448107000d0502e82c515007889480d005070b003c1e180200f400c01152411031280b0f600350180c81e502600400c8664905074881076650b40c4150490708085a540780d10700b0449416000390740440900b540e1046c0b40500c3c1caa0010701070580c907895590806d800092681c40d00e4481d981c030001d86074108080d66200d0400e0036440740200078520443c00410014019031480c0e850 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 900117500 1250 900116250 900116281
    0x221d030c03070b13020d060507120f0c17010501091206020705031603030c0810060f1e03050621100207020d021306060e0102030c0d050703020f0303070206010f0b070c030308150d1a 79
    0x6002e1b02e141d070b5100303040c2d5810000d0f020041c01ca03420002c00c400140200f0840380103144114242c0d480002d0f01110029000700303030b0071340d10801b0201200350000400069920406040c12549141c110258486084c54220083d1103100800b5040344004101c138405d181c0d4070700e0882881440f84d02e003008548e1040d0410358507524116030f0340103100b5001904020460041114500403111460301d502c51104414103981409001c1010800280c1d5840420010f07013040c01100783d02030400c003072181209036046a40c5507220180300b01401c210382c001c6204000c644a42d00300502c0103500500902088140d29032540c0204034501c00da0000640818101e41c2c203500210840f040c41c2c2180d0040e02c5041c607015010707251035000c03080032000c600c0f400490180c004020f002450040382c541d80500380035450700074461504200307604041c02e080e10801c210000601d07040c500ca0101c99140c01c08400964815602042c01d01803402a44d030000e039121010303020400142003c40d244007030726000c41550340790300c80d00309084034 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 900118750 1250 900117500 900117503
    0xf140901080f0c01051e030a0204060e1504060509010e06070b09010c03180219030503041404051b1204060e010e1f020a0c15111611221d030c03070b13 66
    0x4015040701c05035540300304018805403020106c002c403000f000c80000e030384c2540110b40858a482e4045070a0054562000300d1281907070080344c140840c1c09a0006005191045100381014080b0025a103c0907900804980043c640020320050321001103007810850420304039414411940703850361310740306c06009114100b07000e60803c2c03400c0b180081d564244182c45800c400c2c1a644030120010000010300200000c0c405000e01034102e070451003540061200ba0340014110030768154560f042542440404810368122000c041c0040c03000f6103460070145c000700005400202e1650901442c8680100000361012061400d106610414180c000d901c1040f030207052107000004101884c0000850700d01160040203114100740040c032482c3d8004140e4a943c0000d445804d8000901036500503c5400f4151011122055440222103503400710101c048112f4071120074000e60f0740c1d98134400c500c90302c8180c400080503000f048030b60f02d80716107035074a503070382c001a0085070802141400559a0044400d8181140317 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 900120000 1250 900118750 900118753
    0x901080a060b03060705120402030307060507050403140309010518150a050a090518130813141804080d02160507060503100f0e040f02011b080901030e01270c0f140901080f 75
    0x6c2201f404041c2c40c2580070748141d0b89441705100c0300d00490850b00c5140d0040e40140c9641c2d44e6240b40d031600d00390340c1040c0c4041d0822904140000b2895076003100881d44400003160810742e0900002001480d20088548059040000840c03510460b540000007400340c04540d84442d40c0782e5590310108000044282002e80c40c1c0c0d808040842c0442003032820034280c0b14803444072503003000d8112400715601d03009680001e0110135247c4520800e8103000c00e0040c159000e0144444182c6060340303980a40d44202c0c0c459040042e800110507650641000488840307541c05802d8400d0181d0f50300c6d00420350380003680c8601d20710b02a071500043c0e016070741903180122003e411904802e40e503140c8907400c0220809e50107070306100040c00880c0c10f4203041c920382c0d00c040384942e19164464825000040440c0e682c4003c14078180c0c90000820f081d0900c40d010074410440440d00040244120300d80203c4000781580140050380316803d004c59240745225014200351802d80340b03071400c0e0ba40d65403400c2c1e40d60094a0344000a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 900121250 1250 900120000 900120007
    0x9050a03080406033c06060507110111100203090d0813030f0c0213050a09050f0f25030512040302040b090402060d0b03030f16050c040621050c0901080a060b03060705 73
    0x2c3ca4000d810082810907004044082c01e10b07901c52001d143c0c0d600f0301c01040b03100340c00744651507004254030402011f00964503105040c01050340da10074800d128015003a05121401c100040180820007940c1e2201e20011015074490600001c04d40c0c0d900700010000b0049500d9600040e14010060605200b490f01507880d024040c3c0094000c0c0d500c00900c8030103030781018804064103010306450040ca8040c400c0c03e0ba0009010f1500d05016081c051250001c000940088011281c2d41c1c0000415a00c40055000051903c94684829050b81121307a071005005000d0070000300384010700c0324080c0040301e00a030340611200500700704000703040c0310485000b035000d9014030510311200e4044d8003d0341161300150889252050708103500407250010902189002c0442c8000030070071600f484040310701d54040d0b6062119500b0310405090701c07003901d61031804416000903464184007081281080302c1c1005003000840b56103546980351101d08440e0140c5400e0705120810710385050015a0758805c4100da81d41c03a05 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 900122500 1250 900121250 900121259
    0x4020109091a060f030906011a09010e06071b06120c080109092303180402090612070e040603030f170c0f130803030a1508070506161b0b0a09050a030804 67
    0x80402e881e803460a07804848014265846001c01010340603180b8510940b40c0c640682c650340b9010058110701052094075007203e81034140b500c00d40340d6041d42424550a0390500101042d41801a041301505074030301d1009802c0340c11407294a40302a21210b030745840107007180c00352040a551041820100184803a001040360801c00da0080300d199114440051000004080c1e100d420b030205100b2455036080040c252425408042c1d03034070710110098405600b4509008002072180c02444032418100e0340140c0065200d91044840c140030000c000c00030017203c2c0d100e050040a000d4070040203c0402c04940d44480e11000c070540345481140c881042c0d40c40d140b440b644802d5a6044200c003591021011342010401440c14005107200c3d840460001900c420a6844010050103541c04141c15400c40d00c4180010f81f244001c540641030152891004075105107091a60701c0c580c0205080c1e01a0300243c046090480e0038020410300c44295074a900d4161254200422103889120051040408000800 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 900123750 1250 900122500 900122519
    0x714040207322d1c110c040b0307050907260402011d0f06090a090e010b1008040308011215020703120b150d0515030d2304032f1201020409050f04020109 67
    0xc3c055600c0e4000d4442088086404400c4d42c84604002408500c810000c64607021040080501500c0200c1d818010700780c0c0340c0003007a1030740c125000c0c3e14003803116800001d0125004541076080c07d07480b0340c91003450340081902014108000d5504900065401c034038280d005140700c803007074000a4000d001c0340c080d00610041010b00e92000f216030341c00514208000900301424410009074132000310000c038640040750100410440e186e101c40c42440654002d22001ca98808441d90540e039544800a441e250981416a4900058420080706900002c1d80c541019030203520000058170201c0107111450509042200c0d45402101400010206010307010118456800c103c2d041410710001c45c19000058011a04028002c50b5400c04135041e49091890046100400700c5da1000e422a01070030f05041d50348104403e401c20301a00409a520b12912038150450550160107140c028100b881c4804a07910090203904240f0400240c14078120002c0e90b1349203070581c400e03c5194141e44409071542440070701d070b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 900125000 1250 900123750 900123823
    0x2131e020301080318041d0a050705010c0317040f080a0c0303050105091302010c02040e010e15090105070e040b040e24101202100c020d0b0405060711071404020732 72
    0x1a51194403900c010311f04250840c0300c01c92603074610000c1c2c40b00324002e0800c01d260203980c0d404141000400d1545c000402d501000000701103508003616020303074031903003060700c44072030065809800864001802e0b241640c00020030f4074003510a4900744030f9a03a94408011052404440950f058216010030030300540c81241d00744045032009000050101d00a00306a08403010311201c06520740c0641c0c1e0441c40804140540ea82c80120000240300c60302e400701c402030882d880003400c10300464031000000e00556454000c043c903001940e0444004071642441c00c004e114407000410f018401000100e55424602140181910b104400780003400e00d071a0300384030782003122503900000c00840c0d0040c40016580c84892105240c01142c03114440d081c9400c08500b40100908a4001c2c0080300102400940010036901c1c22145180c120300d2000c0c00031000b08001e88038000000f0b0450305c83d1404841c041d40b0301841400744400740481c010040e00485d81c610368030480c104940b079a80c50f00d880400403114406561 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 900126250 1250 900125000 900125047
    0x100f0b0a0315062a0507080c130209010215062706101706220c0c150b0307030303110d020d0207050d0f05040311041d010b0907020d05042102131e0203010803 69
    0xb8000c01c21385494403403c02c4a10340004985400140442e042e07850310f481c051500912101e0110320300010400080d5480f1081c20343d02d098400d4840c002441c50f52400d210302c10820780000e003a2151480000704035180c00d0220391862041c629142d0105100348941601104080d03042d00414003620b5100c104140401c0700c48802d00800b8444040715148410760103409004a070320345500e2024149440e050007030107800d03803590760850310340703001500e084da8006090012680c1504001642100e0442118454440ea0342120f004030300024208600301c015500910780305001d0f01c02d6600d5841c2140c1c3c1142d102c05c900c4002000103c00348000d00204400d403003a580700b00401840050020341400c81c014000c06001d02c01c441b1a55500b418200350701301801c08135405112031000d05a40040c15901801d5030049001e40c10340c0e1181b0f00120078429004c0450715011640040507003000c065401523000146c0541516241c680120703e003d001c990f0040c0c020b59050301d00b010701850030540c2c600081610103549068 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 900127500 1250 900126250 900126317
    0x90112170d090f11011403091b040e0d090906091811030307151d01050717090c0a0b0c07050d12031a0a0f030611070201080609100f0b0a031506 63
    0x1400000c3d0104103450700e82031103400407040c0a030342c0d1000501807100c44c601c0c030400310354200104400480041031122a0018000100e03180110a00104006100940f5181483d12449606090603030304010b81c01c048900c007202c240100c90319450312400743d13440d00d60361600c902d0341401e110000610140b1011000000902224100032464030788804880c12504100c011517a83c0300e0786518403040c00101a1000c054000a11140c10505030003410040d5040480e01c0180d80f0703001150200b20103000d19142d00c40d00902100c0d01c65114485828154040842443c40c1e03c10b85e88002010304080ea00425159007104048004110100080d4081e04600c804840202a000c0480b4103550300c80e440740014044003200b0407581d50171880c0080854000743c50100c2e05480074001040141c1e8440c0c40954444010b840c50202525034859200400078190818881104240c401081a00c048070290420180d036540520001d22611458141d050031809144001881000002c0c1144d11802a0041100d800d00c0d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 900128750 1250 900127500 900127511
    0x516080403110a120e1c051b040e0312160908030405040507050912070510032a0507080705010f050106110d050f070507120615080601050d21020705090112170d 70
    0x70368807421242c1603511100403624444d101c89407810301d032030f00d21107074404035180401440840d01c52540e52100c3d08c1c800d06030440031511801c41c944598004c503140c8660701d000c032a2100c00c00b60044100c0c61088600340c00001c1800300d25981d6922882d40c0800312000c0c0b00107140391505180c140005488006c1600091000c20888440141c58002060752180000400740c40c25900f0a0100600141840c3d03500040500b083c1010328607440c903046002164100d04a400400c05101a0540d00c5001e01c240c0500a1140800d000b000e002d4103400810126480c04010052680c80300000d8803880102501c0c03461030742c048641301800038095001401052803d1200d41d003842031036515203181083c2900696000008201c0c1c5c82e04002c0a030051304946500082c80e0000e45003010200e82d91918144210380c03040740e110f00103000340b11460054002400847e00001d12044070310001030f654403000d00c5000c1c003c0020f2400014146480e102840c006daa000d00360107000603400035041025001907d100c42c20383d9952 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 900130000 1250 900128750 900128753
    0x110715030209300d1d1e0904080319050712050a0b1c0b010b0418052d04120e03030a031d06091b04090b070318240516080403110a 57
    0x300110921082c10500c3d4154010b8030148490524204020302c5013400800030810740d182401c5070143e82481002d480d0f000004071107400754040794961010068110640805110078001403000035445485140141c44111880340300702c0b0100c500454041c00041c20885a40b00c2c03200281d001290462002540850040b000c0000a08880699180100101103405210301000120032001e03004002e42180715080514010752038100c204200e126000003980c8400143c21003d000140041c0b508254408440c0448240c904000da014140c270181c0d4ac0084968401040c180329003100d842e00704024000e18201144404d00358040c00b034a43c0d43c032540c60a8580724440b0310004210b20352107005a80c00804200701c800310f03424500c0350000d154500540c03c201c0d401002c628001d0343c15401101c2464009203042d69800c1c1001162172000c0024005000c04074407141d07036520422140380c08410403400300320301e49568510240c2d0794172641c0054042295031001501080c094440da0007003080e840700303032042807055 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 900131250 1250 900130000 900130039
    0xf04090c0512010b120606030705010804150c051c0b130e0f06070905120a050307030e010e031f06050609181806010617012304021c020301080d110715030209 69
    0x25642c0010141e6443d6402c886500d800185150301c20117601c040c2c46941400400300b0b84403201ba008182c10700081d030000c141001076152481116400c0c1010070410796400c00802031003603101900d100408000f1000718074140d0050b226403c3c034050003d002c44501c00c58480380c40050601a0b10f00f0005000e45855a010b20505114862003800c081d5952500d0744d040c4810400e600a0f8a00320034000c1e4007080030580001c9001040351603e6070142000070100492100481d038100300d400c5880d4250203000c0c0ca410903603210ac0d00f00000d00a1080d030501001b52a41e0a000290294000036036005601200301c2004001d1400e2041e0403540d45600700c11421018424a883e140c000c5c1d10401c00034600d50b604000b60213191403964058400340c103640140a690aa00403883e0049403041031041340d002035181004602282d5441c41c5141001007552250703551904252540407a0710441c000c036400850250302054080b40036015a424142d20140100e41248110020740041c0d50654200300c0050790311030001320 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 900132500 1250 900131250 900131269
    0x50115020c1306050a140306010f082d03070b1503030901230f0f0712080403080a24030b061f0f030513020d050102031b0309070b1c02030106050a1701050f04090c05 72
    0x70795408034410f45c880071b003410724010050780725205070394008105024011010851010409809441009151111440f90000b0b401c400010300f45200c00039060702000158181c40344603001c10b0300b007411004099070a02d500d92240d0840d5500054141d02800150410000150b800544030b11030306050030030b01803800030b85500c290040e00e84c1070408948142000542d085880c49103140d0f02c2d1425180c1450b0340c0140660001600b000c5601e9184c100342184d180034807188008001540c0c0c40c140c10381c0c1d66414581200391064841c1402040110141214400c410706114a07407c602d50714002c060380c0030f440c2140200f41c0a4042c00d00401e88601840c050303980c00300e0503400b085c0a60001690313400c00300d4002c3c5651502111326070800c0ca05004102e540c09011814004540c11035108541d14a0524a4014015520720f01c00005034404000400c402d0b520102626800d02c80d81c40e0000c41c06030102080518041c240700300340c1e0000520404520364240340c1c1011107e940300d0b0080d43d0a9640710800a43d0300300 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 900133750 1250 900132500 900132509
    0xa0807054204031412030109050a0f022a0a1208220b0601170f07050d15060e011b0b150409060e0d0e1807050c0709060b040306050115020c1306050a 65
    0x200089014400d001d1300c3d8110b01e0360b000341d401c01030008400044a40351640414451921100d079030340001031505507107030810650f40982200465680e20340290391854144d403008040c80c0030034105034a02c1d0001d0001487d0500300e4201c8007844050b4180f030000c03120b0b10710040c13440f004202c0b802c000c0c542c0340c5220100014a248200e104084a1030188001043c0c03601a070381040c1c10100c104103200c4050742c4c203007190f90811441e00e082980c4207040b0704400c2c040c040813002e5107103070078110b1400036145610040d01101c2000076a40e089240c403503d070050a56000b5020007604a000e2000441c401500d210000191858050300101704128a5243c96080f10300801e685000d541003810b00d114425484900351220050484002c11085c6c09484c1c510310780c600c02018941030090000d03084006210811002d2b0007440a12001d1214a49660188081e600148070803103207913083c5030021882d880385841c01c000c1e00100b07600502c0d500d000c1100300612102c1941249a81680c0c60f40040365903100e444c1c043c800b40 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 900135000 1250 900133750 900133879
    0xe0a2303040b07060b011b061a12060103050105130507150905060c011e0231081c26131407090204180b10080901020d050f04020a080705 60
    0x103002a09201c2c080ea00045c261504010a07900c008100c2d5841d560420403080d001b0b20006040741c901a6542c10b03c180c2c0d04100c030f50184409c4d903001921600081c200b41a203101d100280116103862466543e0840d02d008010305d140c2103c81c05011034141001c0c0040c002030149400034545030761b2804034041c0e41c410600f00d885039468410410440e50802c010b0002c00a58940031890300603106038072101594582502c0203202080d01e80c040c182501940c42d800641b03121800d440c0e40401c0b41401c0f501c0d82c481c9042c40300120b14010200100c18802e00c0341d148100d11841c0d01e801d200d0780c2e42190b41c0545807201c5c2c1d04580204031450400c191600810419010706200840140d403642003041002d400b001c611a04c1c2001c900f0081c07080b0140d10395940e00104c03465107003031041e225181c4c0301c0d100c1c1c064051007079400b040d14944020483c0d40c5140d121003d010f203000f600d80c28451a103842846d61605542d000303490300300c4407900035140c080c030080624408001000b4907062114503030242074101e003040c841c05015078 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 900136250 1250 900135000 900135007
    0x6070609061109010c081b010c080a050106090506031315020a030b01140c03120411031501060e10050301050d0609060e0616110a0f020303090a09021306030e0a2303040b 74
    0x2001182d1168002900100c05414204001c10340020404500400300034803100c0045848080454003030001581803c1e03040090040309905d0800504403003080fa5291982d034106000014510b006413035080a8a0000c1d111030310f940d940004007015003545290840340c4503400c1e0141040e80d01c140c8060030301d106044c4c0c3e01060b080326080004200d82c0f0407020400f10050704100404042d040007048428403181d6080002455590b400c10018065040e41480c4d0180162407844400780c620303d550078140d4060303446070092415144180800001058a03920114008000602061610740700c3d20500520902c00811440001c0d69444151801d032209804194484414880c04020319072650140108628141c0b20000e203c03401c2a0313951104610141c04103082084039000c0d51010b104944803e2001380909180c144d07076620003802035100d880a15902c200400011a0a5102e40038411030346a0450040000070026241c002070040703216050f800c0c000d10054500030216043c80a007008000300034207a900c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 900137500 1250 900136250 900136253
    0x304060309021804080904060e13030e011103030103030e1518090a0608070e0610181e030b07080106020c031f11090a0603051006030e0a1218120203071505190e06070609 74
    0x944523103401065085d01c5907010061401c04c8103540d409800d8262600c5000b80503607100586094411071483e1480b40400000841815000244025415420b48001e21050b0310140d074590280511004458040d000311924280d40c40c0403c1a650014801100095020740d2204035034681781b03a07640401d003001d88400810003140b401000d15003c0c20400c1c1801a944400740d401d001c55200c01c0c0c00f83c1041c0c810001c1d84407143c410810307407110286a010b0182e1300c09080807140580b840c0400d01c1010010f100d40d1201c52007a003400f007401100402e6601615828030302540c0e10700c000c3e00c2c1501c141402c6490134401c900141d5200b01d800d2000304144c1e100040d060800d000140058a8107400900506040c1180d468204100089480015404c08030905590114020803604401c1e44011441c3c0d6112210012034425a8203604504062007201203a07966582d0382039102000803c1c040901c0440d00905c21113028000400502290300202d01d0603503020304290000541e00d40141e1001c1e144190348610500 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 900138750 1250 900137500 900137509
    0x717071404020913020f0d0e01050f0612030a0e060d05070909060f030b010b0c10050c09191a0a110717150f180703080406050a0206070c0503040603090218040809 71
    0x3455020036241903240c44030800201d0000300c0c00580705189690700007021000600c903c41038030341140c0422014020301000042a50180c101920a04011400d01010940a00d03003800520503082150b00510305060107840f0660340b44421645581c0c0291080211542d541340521a6510510311900d8942c1c0003030a201c0c8820881b48140c00511400c0100074040c03011400f84404241110030501d1201d5990090303e031032504000030351003a207000301d041000703000070306810b03e001d407008000645d480550540c01340d0400041e84243d20603401003020804031680040905c500415100e142414003803004003080c40311903e018941c0d404500c50b00707102400290191b000f441448104820030382e19001905040700840c00e29a0007030040c000c00e007100c8540d4805080c0600240b00211342010215440744e642d054050010f9200c1c3c84210010701400300080c4489005031440b02a044d000b50045050509205080c0d0007001c0c0f4003416039000d141110b0a1035020103059416200700d01c50351656895030254010710 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 900140000 1250 900138750 900138779
    0x702030301150f05030606090d050d0503011d060d0b040201021c091809030f050309010e030c0a06200313080903100606030e01060608060d0c0b032505042402071707 72
    0xb40d0401c101210070344415580b00e000e880d0005822112250383e140c20b44002001980340380c10060060180c0c00c20303882c0c0103030440e000e10304a86010340e840c0c20b03058951843c3c41155200701c0e2510b40c05043e0911a0010840c640d40c101e92040c41030048030503620414030780217040800220000c00003030000c6402e22400d001c0340001040032030568424801c042c95a9805000d810350805070800704071000c0001600880c00750841c2ea20743d114081640d9a84440b0082c603a01c2d85196101954220f040220414118200c1c603a041c4800c1c10b00500a03003141c4452049565080c40d8841c2a074800c44e090040c400141c1d000d11030050b50352440f4000080540c1740101c003400b901c034040752450090345400d0080208940040a1542c044400caa07002c03503042c0113140c40d20400c0d003144c001c480110000b0040051003200e80a01050361614665044000c0701d40e1030301294948114007400c261048000ba04140181040490f441c0504d0980140c41c0c070301703884000150401988605070900c65109403c100070303080961440 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 900141250 1250 900140000 900140039
    0x512041209121101030f150308030423120a020a120c0c0807051c0f1a0109053409030b09100b03010510062115050906010c0b220b0702030301 62
    0x44240d02e142c15280d1046141400e51030301e05043c5c030b80c16003003041182940001c420502e02c5c003070310450f0341e204d080500c800d820451f0100c9409503604039240075104501104007481c0c1200000340208950000e19000503040f036985402540300c0c241e001070002c1c2c01062140800807056031042d101480509181420700360030b5000c01c1c6550400f80b41070110380c0362481003001301601e00349407500c0103420f403901a044c607000120161000040c03c0c40080e8081c4d402032424122031181038240801d403101c0c1d00c1004101160540d421420040c40e0400d0b12008014698446808640c10f2074408295070791142032801d001210360f20043c0d001390000c0b241e40d528520407018070380e0064008101900d00ce030b160001482c032034001c480500c610b0010102441c2c160700400604980254400e0203c98107503a250301b80001e00e4090319104070200c0000951652003014030038881900007105031081e40740c481504104000342c46078000350700c40389001075012a40c103280c21130040f40c031940110364039032529001d1107030030110b00b05 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 900142500 1250 900141250 900141269
    0x507080411010c02060705070803070314040602101e050a0c030c11061333141e090c0904080405010207150c1104062423030a0b010512041209 62
    0x144004502010074061807060700f030800c0322800c09240001000c0d4000c82c8030080071489075070804550583e001c809003204a100b600d551501c2e41903144503042d58055030240c08016800580601c144d0303500d03904a2130820044d040d0303140101782d0310886d17030003900d00803214008010f440f0440b00322001d90501c500b69500c1c13001c0c50100c00300110800884c1d12500c3c058000306c011802c4195500900150a40001629644da544c041c0c02d0744032505070905150309141401e108900e020070581d103c0308280074803440344001c1e0041e17036094070707504100c1c1c10200c101403c440c15074440c0d0681102e4030386600403840c0c000c900130402d8540310f40c9088002440c0507069000740e160346100d00c81140c002d80d0801c1d18501d0107503006000000c03100c0860080b074002c08156004021500a41c80c0103182104c2001044906100694408602004101e80246c844010805240099070100300103041010507030301140d21041c0500d015842c062240c60705520b440300540d000c1d82ca030404070301009181d41e00151203000a00c524603 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 900143750 1250 900142500 900142517
    0x5060f030f0c040b01110d0206040b180d200d051206040603051203040203010b1f17060f011d0402040e090106080a03080109200406020717070e07140f1c0507 69
    0x45203681c540300c1c10820b8901481c0c4501a4244603030080380c402041d11084403ca0b035141001d07e000950320141a20141d0321400c416000c02c003030341c844a4080103c2070020380205041c92a0783d6048400c4500c00d145a280d001d00d0303450100e0840c406202e5400842e2042d170340e03152103495070352031074148100280840e44514905181040011004600e203942400c1d1a030006440303664500210f40984511000c0e076922880c000b9000305a500046002d42540015a43c1e039100901c0c01081e001e4480d4094446650110040700d510344558403600b51400b151225484030800c0d5100c100c045401d0760427640002c2405000f0000300044030000340b040c54020034007071005090352400c0f5200034081d10f106014481d052500c40c6100407660300c0143d550404288000b8100e9540c954641c3d00070b40340d4040d801070404811141d0349180d0085000039211041c0d400d10380c007020183d00e540806440c0500c50040d00880c6010510134231403401d41600c083c01621070440c86206d142065504040300b2101d00810803005d104021 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 900145000 1250 900143750 900143773
    0x10608010902180a0b041b030b01030603231218011404030317091507110705190605280c060b0108040b060f010c05100e0606061c050c07080d05060f03 66
    0xb02421004003040c03d100c646a210352000c50054641e0080803900507003071540e600b500c8480c41f2051000f43c1300580d41080011800001141900c4e0b4511000d0319004213981144180081c000b4070840c4800b091080325001140002c40e0420b503081400710604141d60084010704030750708038500a005041910030145014295a000780421800c0324029078603a078407000141d0188010461070304000c00489807020940f80902000b4030f081d46032851140da5002d4008005510300300940c41d15040000c0e81030016005091010071951600007003908403400410383c4141000480360b02440c2d203000c020396250703c00c212490a01e0341c00d40d00c4c20301d4124100400c0b0005c100105101e8113049801480464aa510001103500105ea00b0036814401030075600696016000c000c0b0160f002c000e000131160140e95260384c03943d0030884240129002101c0c0010741140e800030500096100940c0508079504043c242110768803016500e4011110211303166940c0c3c2e0500100749010a80e01490040032802000d000810 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 900146250 1250 900145000 900145009
    0x602060108030a030c030b031b030d020312130f02180f0f0106051e1b03040f1406070b0c16110f0f03100b0d0501050702100c1b1202120c07030203010608010902 70
    0x429040f10300f09a910030806030303007030701c241c20074203d00c10f004086400d000a04101c107408251000c9050b8401d00c0b0316488200780c00d00100c01d46810340121000c40141d9618020346000384c42d11180c2c100c800340f6030305c000302c0c0041c2e03900815a04101409041e4964518100100400950024041c042c0d4904038600401405500000b1540c044000300201840c40102c840d030100e8602940420002c0640f03460010151800004094400c0344c0780d843d003030003026544140341012035418041c100d4000000b04020404940c0b04440307160041441103040d86002e00109450203401d01c080c400301c40c0c1c2603e1540c2217038285001d0900460249080360540a40e041c1c480c002943c900e81d1214141109444583d9200365980f440707400620720f900200244003515280030020345546240403a10100c1c0c1c5084200b98240c0d10600700c025030300400d601880380404a6071180c4006405101c0800c00b188100402d8101102819024001c00400071005007006801c1d48105401e44080d07404c1031079142e240c60301c00005a543c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 900147500 1250 900146250 900146257
    0x15010b03061207150f0e1005040b0c0712080c0f0d021f11041706010e2202032a152701090f0b030f06030a022b0507031506060206010803 60
    0x204442001940410b80150381c10241d159200003410032070400c41e065141d800c07481034a05001159180c0c504000e6040c07c00c05050084c00b260130006000780f006104122000b4003c046415040d021101815a20841c0c0c0c1022804150100c2d0030141c00b0842320a181c10801030800300d0344180c0d000c1c21201407503c0001790340b1010fa81e4068008101c40e800740c42c1841c4540d200c08025240400d0040e03840391079080300040300070320041c03110640c442c58000203001108510f0041c000c0211050003117201440c00030542d03d464544d0b409036414014102192001c649100802c0760034205141c1007061840704004200442c0c06008065922003c100804019580c08480c406500d0510400040318614a40f00403103410713484d601f00500e8401000408100480f482014604c141340032602d101155441d0b00c20f258480841040084d00800c2d011100b44100c000c40040851080c0007924001c540e003c25260380c2d2800c4003560081d40c2c80100f03505800b00c1c00005c0d00401002d000a1300091859500d0401d904d60340b1720 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 900148750 1250 900147500 900147511
    0x30c03130312020c091f030c15140f0901080403140310030c0b1c203402010807031d010606080f10030c12031e030b12210c0c03061815010b03 62
    0x1001c25001e5002d9511b03d810420246402c0004410041d44842e855001c0d2a20040d4803c007066505100c54000c40038002241c4031000c04035186400c1c10441001505c0d4840054030480074001914000104034400c04041e51058828015007000a03103542000c803d602070b203070401d10010000304400107200d07e02144001c032800d40d0000018072241c02c450045903141400400e42e4190390005480a040c100f41e05414081ca0310b81705a21141810806002c038014007012402800f203141c40001824041c082c1c0e00040c0940b090510b00350701c4010b400545400c40d46641c003c41d01159072070f018001c450700f0207945a82c0c4290083d03071421070301d07041d903c5542a0310158401c07090064840d04441c0c04141c0b240c00300c200c0303005141c200e81c0200f015120003e8003814403145d0090003850701f81800b081a290010b068010040c01c505860414601d81c90507003410761040c03011002c1d902c59180d900e41d4680b002c00030244139100031781c241c501c6075a5000810b4148002d001500c030100c0588401400100380040c00c8a030400c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 900150000 1250 900148750 900148771
    0x30906040e04020f040c0804200a1502010906060b070c0f030807080309030c0321070f0e1509150703081f050103092906030f01051902070203030c03130312020c09 71
    0x2582e8920000d078118599290041e046401c15620111182d00980a0350003944515506040c1000c4044c024281c072403e41e003141e5110090071000c08c5444c5041c481080c2c814040c0c4000301c1e00103010b0325044240d8050354413840d421140000c0c0c05052042450300030303000c5c2a1600c03441d2022403460b01d40b52000e00130103032301424000f80003020510602042045409200c40b40042d66115150b03540705440c0e44840c412801d01300c0d04076000003440c40b4403030014100c0c10742c05034461482c2034581c9424094130648182c3c15200031030080040455590780c5080611070890b00f9402d6503952012494001e00d201e2015056540e403a64240300b00ca0fa109001e1a00c6040d03500a10300017a500c55603083c942c00714003540400c800c800d1543c681c6240c03555049410241b2a24080c3c085804407440c00409078201c3d00300f150483c0007074010003007854145240380c0040c10201c0c002002c90f401e00305c0395920681594400400002d0f450040103081041101818a0501001050000d440c1d11000d1a0210b0308281c00144200b400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 900151250 1250 900150000 900150029
    0x12080909060a030606030602041418071103160c080c01020703050303070503130f0f03021b0d080a03060b0f0c0c0609060304030e22050f0114280905090d03050903090604 74
    0x1030701e581807060010742c0c000406100c5c180c2d8a0401c0c0009500a00070110b82c000d800b40785480300c1c10f000800700441c0c1165988214107070380380102207a96460b0070001e1385450104103c8000b0a0800c1c0343c1c40c10000380110351000030f0510307000c0303050306d400542c19559065421807c030400c04108040184e80d400802400c103a5900c0da2811740c0d5900304881e152000740200f04040e1100d06102141c06400c43e03071f07803003502210340091110001408209029509507448031010160324006410440501050001410045000c07030f01d80b200103440360409503000720582c0340812500032491003041010341c00034041d40e22614203040b21005c590184030080014052000500000b071407074890501515071030440110407080c803141d80a8400c05440180d805450500a0784004181c1c2480c40140300744401004102d02c005c0190307210000060b40455008040300703445000b001401c1402c03030040d04c3c40303000218041c00c5c503030004a40183c110346001d40040342e154024030034140380e0f89545044a00b1344402d90706034400d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 900152500 1250 900151250 900151261
    0x2703050903120409090c060516031101090519030e100e09040309151d15070b040c1203080a0e0d090902090d02040212060310020f0a030209030f0a0b0a0612080909 71
    0x151440b803200c22039000c140010000f89520715544000c850900c50307038003409101d660f100100c40c031f03010301e440302205200194540c400003405207030998140c0d0400c8001099900441e241e087c2020f246104c0042c3c0c002100a030304003019070254158580600854000e44100c514800c010a000c2e101c3c13032044d000d0780540c00130900303141c003947e1003900420894001101d038418254005111400d066500d5910801e001054052031802240c0ca1104001c02c5454906028080e26081d18000d0080c0064030000000c0c880442c0218404200e440d80a000b1380b00c4000d281004c0da1703030307100f142c0b5a15a80076a075006000e004124603405040e207821a04901e03005600c030310062001801e1041a2003000303505c18800500d82e502ca81508041070b100700402c07001e4031006005141c2c4038090b03101399031061110a4040103c840058041d901501185101800b11032202040101e59032410340030610036560115003004104080c0213901900029040c4410350040d130200c1c5981d441c12a000304103120b4442c4d03440100081 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 900153750 1250 900152500 900152503
    0x1b130311030c1509031e03030a0b0a170102071a060a05090a020c071212110a0623040f061a0d0f05030c0303070c060506011b110102010617102703050903 67
    0xd4a082c0c0185680c0030354681581200c019030110410798001c1c002d170148185c22030455a601c0d014403803040080c524540d5000c45480090400e1007949034030443c2c007440071504401010445080c03042e684001692880d040c1824070f50701240750b0041440d203805404102c2641c13640c00c4000c00715007040e124100641c40e01070404020340500d140c043d04038440c174600080c000c240540c1140515000301c04254815448000480b2503058440340d400d103a601c0242e0302c4001031400d511089210060391511010880301c502440c01d8464180d03402e4130301d454811507800521060707104614000b0305030b1608901010b010004125200341083c4082c02c0000503040410030f1000070300407140d4840c194816241d41e458040000f40c031483c100b280c1580c0c03007460040047c072294002c1982000404040f80c449103981c1c540d90b540c3c0c1c2c43c3c03844100f4407030441d501e45034006800d007140c8050340d440010400c080e00040603180b41103012282501074180082c006100000951505c20000203201740e014986580e4130300b181c40109 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 900155000 1250 900153750 900153763
    0x150d020d0503090d0615081c0f0e1002030d050604150605090418030801090507180302040c09081b0909060c090904030309051005010e1008030904091104050c031b13031103 75
    0x241c04c0035080102ca402c200980c0e1001c155a00301241c02054143ca500e0220b95a40210a0305c20081440e028050082405400d203c1e1821000b450103860009968010942c1044120522005a400407074511420841d5020f030b1540040256420004440a0501000c21281d940300342000e100d07002452212540301c9030040d03c0518100307051110420018580201515000d100340d00702d00c1d01e0319000ca940944034000c1400c0085a001c01405d246085400b048021b001c0c42c8280f0341407200360100047c1c01002031000c40c50001d66039500d0071294a42d0014013201d14801027415146422580420490500c800c040d10000038054940d009141d4580c5404c0c0c0003041400005805440f840ea01e241c40c03400c1a2f08547d060301ea440381e1548641d00c400314800b1054586014150481d0801d00004046061982c0808512130040d4020f40390071112038045000c0b5101520346201741400002040060038819003004001e840014102d8608102005112080e00c00c6010081c00031002110201c4d850394100400f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 900156250 1250 900155000 900155017
    0x10207092a0f020d0e0a1701020d0e030a02010c02070b07080c1204030605190515130b0904060605010e2b0c08030c0f0613031d010302160b0106020105150d020d0503 72
    0x40c0500501c650368040c16a0b0541c81c2044018400c480f0141002845035203891903141002d8a0030340e01d98203020b91080c4040c40300e0204c00442d035080c8040c40710744e80c040c0201c8a003103409102555a88070070480090039640110381107401d5502c403010801031400c115080f40d0303400343c0081019403a0300106c0e10003400c040326440300c500301050101e030100a02074142d2203c3d018485128000c1d043d1821440789030203a42c0c045400c5070f03e0391110f1410125a0030000505510907502c0031000074065107010000f021000140c906441003580d45000b4001540c0106400f103100740101c03904020803180c54110066150000e14800c2d40e0020b10f02602d0401c8005512907010f0170b401d0095039103503504c01d1038040d6901111404d144851040074003107030b4a1409a11241800b6406d0b41c0c1d24118038400503103100300b00580c0d0300e04030f04040c1d08001c0c1001c1111403888280c0e041e0b00c5110780d48007551600c1030003404e4800c003901c00c04440c0c0756102520001d41d40d041140032410f0b81565441801c41c0107040560850042000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 900157500 1250 900156250 900156311
    0x6070c06020709050a060b070f02030c0a030f021011340e0402040c030203090c120717031b1b0904020a0b031302011403070e01140c100501080609010b01020709 70
    0x101059054000c80c44005890440d00204a65500c085ca000d040d65110700c42d02c0680d40c030401003000070402c22942c00401c00d001400b21000743d040200031807210302042d88141d680e80480304031002186404d60510864030001e1074040c250441c0c01034681c1d141c281681c0101400f01e0314030b00c2e1031a0211040302c81c1c1481604680c500c00f840359078500464490404a8080b48101d103407601010040c0c0c0030340b003924018582030004001e1417215406106003951610300702211882020400201c2c146c408810305111031401010b1a2100361410000e05040740d201441e9846812034505051a60401812450380541c00c45112401d0f44035030010030880c3c002908581c0c05014000100045d2850707034108802081d100780e0315402010700c0b0502d100381e940030981d011400a0102008040150311410b0348202c80e840d030044a5140000f00c00c0103a03d046d10040e40d0b042011746400041001220a00c07171a540020040d000b402103102000000791113486c280110300b071165459404003480070281000f03103841c0504c9207 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 900158750 1250 900157500 900157523
    0x10b16050d030c020f0601060806040f1803050c0f06070507020103020a1e0504050310020f070f020a0b0304060f1803170c040f03051b2209061404030305060a06170c03060607 76
    0x660060103012440803c3c0054810b40d40b410140d110000783ca14125012070b941c54050351501c108101c081d02402d0207e031a880d803202000d580c6007840091128245100341c0300e80399a075500d2143c1a0401c0d4107220b85400c07c2c1c00c00b0303080290280e0003100319140d150382440d00580e900702a600a40d4509a642c4542c050f40d035400729111b0032240c11000801c10742d0800c500b2101344521481c0740c00c050f40700f11903c000b1112b109014400006160b00e0b00244d40300d00c0200070740010b9881d0300000e101130700b045405640b141e0b215900c420200009110740b004601c212810b080441c80700307490150a01c400b4000c3d20240519901c001000d08404105032000380c665514556940ca42e00d041040d600c0b40558a15141c0c40907411000f042c41c50000001c0902a4001503000e0101c0303040f061b00b0004100403039044e1607164442c3ca480050291809140b440f481c46a14005280d040090500c201032a09802c0030040c08003001141441e0458030b80102c0c0d2100c00c0c0780c9484d95a68036140400c04070700400100808074800103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 900160000 1250 900158750 900158773
    0xb1e0d020414272d3f0c0a030c230a05061501090b0a050f0c160905060d06091b0b0301081204050114030406060807171203010806010b1605 61
    0x19916445440002c03c40d0750790707200e164112502c0742c500b064101034400700000003440556011440e00e24003c02081500c042d40004d021542051402400c00c00a50355a0007002d4889020b00d202001ca0602c400d1078181000c034110280365842c001d070b082c003078140400100b4117420000c0fa6460707003902900400360503054008184400c0c2d940c0d1103580045689003c0d400c00207000d040200c01c05200308205035181c0c0c1d0881d1610044140d00e41c0048031000800c0b00400c50380d5041c003a80001465006640b8005100c80b07004541825104090781d00100083e0781490284407035680d40282c210280d5400100001da00a618a030088418800e0000048073b045d03501000039200304210040d41c1201d0a001c2503078610750003c20314100700e204a0090710301103440c131902200b1300034405001c0d540c8140f0424000030300a45909a070303460090698464a140288501282450300050000c542281c1e088140716040d9414220032548402d414002e0082240c4041401c030103d880c4c0d01101e100c8283c01200b600c10200c050f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 900161250 1250 900160000 900160021
    0x1050f07030b190803090429130605062a01090c1403070e07081e0f16030f0f050106030612050d0807021203010e0610050c0d0f020f0f0105010302040b1e0d020414 71
    0x602e40c0d10320803860300c400d00c1460038109103008141da526043c200308c812903407c02c00000c0703801c055181508540e21600452207450b01c030001e20182865008000c5800c01d80d45152010205849900e216a410b04242400054001010f907090728803c0c1524401d000300440801d147c040182e1140d2104d03081c200601c0002508070350400d02507480d029109a41c60419051895240001d4035003d0f4420541800a64040310ba2881b0950031041c0340350106a42c0e4100c0303140c00a6424400d24040d21b01d640b8001003040b29090322030f00c80180001a0b800c4044940741d283c282e1111864101c100c2030001040004401901c28003010064400c0c54000d141ca03035031100103c0044c4502100c041c0d000e006c5109125081c0c5005405540c1820442e0004050001d00d624049410013200d5100c0010762181c00500c00103480180030001e2201047c0b00001034640c03460040005075071241548900501007000c0341c2056060165903004000300c161103c040f0b80c171a038404100100f903c6840c06018603020014861074604 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 900162500 1250 900161250 900161257
    0xb0d0303021c09110a080d0215061c03030f0e010c1b0c03020a09050402030607030e0c040b0316081506010f0503040809060f030a021b4201080d02070801050f07030b190803 75
    0x4e050303034030f1404540c445860540d2211040c0182c000750340081d03031a501d800d07d0346120540c03000c03001e040d00b40513902480c0e0084250190110440200c0d44400010000b48400e209444520103500001d000503900544054942140342e03049002c641181d000036400d11a460880c100215130150420010580c0c807005c5400800040d0740c201e21a0052002103041d05100c0e009154500440b00040c7c007011074844c0401c002089022007403030301409101401040159054040c5000348004400317004481c160b9001d0403004079004200506101780c15150006082d40042a02d030b20507030008403240e6503402c0d440024824051000000c81d0b0780d500108000b4001c486402404942020200c2c081c055125140410345400c2614420031103c2080b045e0000d002e4241e8070a010740d6420030440b0032081070b8442c05035050b281d098000e510260300c82004a8001641002a60700074028580200401d09041e001e003c55035001903c0c00c410991201c0e07004450707540c0c0c044180980b9904803001d260440d1760342119602d0b40c2 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 900163750 1250 900162500 900162533
    0x6010c02010545101b030e130e011d0303040b190908091314061c0204060f0602100501060912020f1807120905370c050909010b0d0303021c09 62
    0x1900002c4002400d1009101500413100c0c0c641d4200700359000204414030b5110081501009031041c0d46a0031030b124541003070708200301610f0110780c08030382c805914291241c803d4548a40c280c290401d41d00504003109494120f40d00403014a50740e00c408850f40d03481c140d203009c140c060078548030101c001c1013080c400809c100300c81a1050218403840102c0d00303088842c0400c4a10708900070744002091480c083d0b0050400d18520021255008155000f180032100603810003840c00b080640c0500c104c6804200d07403104c00c603840500740203940c1006130050440c50306100d4a8101c1d003910782c10030b0840d950321444101501d80900301d141c00010742d4492103045041501c401011541e00c141b81d5060142d07900070681c0031038100004200c02d000c100b44800d91030440b19240fa904460341c682d06086400229111480726001da04d00340103d070700f1b00c3c003004900f16010740b06840917032410809070501d071109181c00b0140c9825080040c1c644503680e402d6a80407890791903900328580703008040303020800d0300700085050a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 900165000 1250 900163750 900163867
    0x7091509030b0601030e0a0602030a150803070203061605160809100e041112060f0a170f160305151f06020f15040b22080c032106010c020105 62
    0xe80fa000015001c03aa0400c40070b0425410079807211000c6525a0003e40c0c1210000c01d00041e032184c0040f0a1800714103e03003007680e0a070000074101c130651404004498001034196a001c509400060010b08148122440b2080403088402448240080e89041c0c0d0f8803560040d00c0001105107545005081401a4913018421450b04203901803071100c44040e5240150141b11920030750715460308208179550100c0102d6804485a000812001203103441e140a041452004004805c2c41d28a094200a580790945056200c1ea01042001c1840060b0200382d41103010b10b11206519034160500440354503650422120940004c0040c1c0130383e000946144d800d844105565185c014015070441110050310081c004001035008070702642d01e11038445211040d03003099000b8590326607651f030b1500e03081032581508507007021a125108080003400e46000905d406442d103840d1a080c00044c15440b040e40029040010106000071440c580942a00750301111041c13110219511a04051080f04500b07a030a998 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 900166250 1250 900165000 900165023
    0x515030706020c0303041a09040e0f06132d2306100b0406080901150f17010c050a050c0703050a0507061710120f0b010605030a1a030d080709150903 65
    0x40b8808189420f070740800078050352034180b4143e8401c1c012880f6646080d11700b4001c0043d66444d540d00d2090400c0048030303c01414000b45104d2526040103c018166640d030700c544151540014020700030308a80c1407020800e9442280c8104842040340d01c07860b00100700080702d4861803940e860100c03040403499101011035440342d41d141c20040c000201440f48520b07404041c0014840705002d80051a401240c5030000107660f8943c50070980034183c04d074403c08002c00035032810310124406142ca0015602114001c7c4500c0c40c0115004140d481040c444004008021031215007440d001d2025000035600401120381020b46810060340300c42181c8521000710703560000c80d05140c0c500040c0188a21100840200a103103000a1225120355009040780c2c41501c80c0c1c0a00009001030082d50301900190395050b440f4a0b0261400b800c41b140d0f139a010003106580d114205503907500081030704100c4414034100700d9544036003905480700b140783e40004541030440560780903100d5000c6503002c220b90140000251 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 900167500 1250 900166250 900166259
    0xa1b050f0609030d081305010203010b0d2904020904110d0e010507020a0b041707050d3204030f05030702030601120c090c2c060403031d370905150307 66
    0x41e072003414511509900000102e940f030b203003c0d400c2c03a548141420118044035a007907489070308aa2090700100c1d9401c0020490a000c5461031080040b00c1030030482c078122404500d07001281074541d00c80f09178400d94001801c0e804580f03440e080344041d036106500711034a4901402c040006000c0503c42c0706019032030040000c12282c40092001d0100f07420000240a0f511240c41c0c007085805120200880c51008010f184001481000744d4a1140507664504010014040706140d41c5643d522240c9445180658201068480003040781c0c11203a00102c0155032040c185041803c6001d40302000e98540103510000805c2c0703014064080409116000450040751140c801e00700722183d600442c0c002402c00c6440d401010760001a000b0820030316200181c841400c03000040180e070054004600084400d03103954103141000c43e180c13014200c11100070400c0e901d5100350050b6041c0c408400e1000105004100c0000c5140811000113000030705070034000c519200414402c80c540783d10880e400380c0b089100005 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 900168750 1250 900167500 900167509
    0x2031f110c0c270a0b030312070c0c06020d1713050114011445090706120203010b070f030c050102070b150d050c1e03031201060f03020301260a1b050f 66
    0x20820748500d440100644960808400415181800c5a01b502c41044002c00c05500380e646030b8890382c41986c9840400200e171401c10a684a80d42c00501594085180640c10716000800b085100301120314241050b0f54005074a05600d901102c090003951034a444031344120212828035060b2b880c200e050141c1c05c003550007071004141800795250400c08070441014045103044001c054000b1000014105509041c050a0520300098510003030035030106108000c26600070b03080d00003021406008505642c0351003a04540d034855403000401a03a031f00700180b4201402555401200c40e0440c000710348800403450680c0c3c0c620819200003034040146540d440d0b00f4a4042e040e030b00940e40c171601801d0f0001c00301044c44110007030713031040c50011429000c4034003e50b102000502403051043c0808440c55141600181840d0907a025050402d4010070051108800c02010701043c0c40d50503150902100e481502075080041542c402404482c0144480c8544165400144266a806c40f007a4010301c19850411 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 900170000 1250 900168750 900168799
    0x51605062502070b030705120711010b061306051c050f1e070f0e040b041107110a0b041a19020115121a070507150e1902031f110c0c 58
    0x20070040c2d110718020300801c01c101c005150401c800e030030120b042814001000f0400c00040f160507001a9003514401e0803d00240a0384440720f0301940d600d072609100c3c034044006a421401204240203001800500900080f6400d5028070190241040142440034404a07100001e81e04804206d49180102800b28803000d40d040c054410364139010602d03907020800381c4d501b10700300c07100f954895950444a83d0945450113504a0b406000320000d40c0c803400744c80c3c2506e000c6c120345501d6004030170f86101440400c40000495094a00e01c2002c60450601b540c1144080d110700c00ca0448502c40714180c03481d0140d0150080d030261900c021b0203008040d1a064071244030011079601615042216012244056080e2a41074101030980340c440d1910b100d51700c81050004d402c6a00c950025902d50030024940030500c428100329048004419a1000a4001954a00f011840340b6242d20281c08103074060240703a4400d000494480c0e04080d10391903915a51b80d20b5040401c5803e01490400401992820340c2c220344 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 900171250 1250 900170000 900170071
    0x1b0f0d2003090d0c0510081b041d040501021e070201080109020310060e0d17040e06090103020f10200714030a080406081005040914100b01050313020105160506 70
    0xd5040203188410000f440400400c1922201910140419251280e160248001074503494403d860b0034291a4500720707028110100d81c070302200344000c1c0040740312a5601c0044480b44029040d00c0d858908215009208d624034071000b03003201e4444070b120121400003510180307000740c0781c115840e0f0707841704141c1c16840112040445000ba5080034042e05002d000018190381c0c024024010b0a000e03a40c0b0150800e500e8544100d14a42c0810f0420a0346a003110a0f640801b0540300c15906515603030202d5009090191a40e110340e2101a01810541c03003626200c02c01a4241004540701e036242a03a191251500d014042100100d20190304003410000340f00d1015a5003c071025192a01e08042290b17540c03400b500003508126892400911580c50340648038003a401041c206000700c4402c0801440c0035070500140307511500b0490389060503a003010036039502203a40c9500c195600d02c1d40c4012030f210301c1214542c643d0f42c0d1008182400b4404009034080c854500c0b45000501d4065907101009049500e145 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 900172500 1250 900171250 900171253
    0x120a0b07111005010605090a1401090302150c1b010e0307120308091609151e050906010e1e240403110d0f050c0f0406030807081b0f0d20 60
    0x4150300921035146985580c00c07007801c0c0d490112008400c0000d4407401ea11140004d036020642e1161340c503100d5003100091001008010030240c10b00006482d2580740d11019210345646010350088901002c00c60b00c41103080000e032403400c0c4c0c1c040361941e03581d10860700b954005000e02440035502d05000446009030b409028031b542c000300041c0d400729000900101000098080c1c615404e41d407405090038840642050240031911010491810354800f8041d80405d083c053b1200b075151000b0f2154008400342d4400f03940710180c0790b5614006946a41003001c519400070301c0400034403400182030700442e01c2c00c0f9046412102c0300004101480300384031400e07000740e11608200810000544102c10701441420090900701c40c03071006444406c00c4e11106c4d013041c0e030160004e4941c01a1403405104008622008071402c0200710f003143c44030a45800f034080010030743e2600007180c81410980e42c00c8101510000c10455840017488950203445050281c90003005c260b10031812001c07a030902070401641c800e20070 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 900173750 1250 900172500 900172523
    0xc1b0f0d27120c030b130b1509060d05071203030209040617190201031503030c0605010b0309070b030c07080c160b0f1218120a092405033102120a 64
    0x2c100410780300300200480c2d48004000300040042c84c030052a911481680411a0405001d820403860200c03000b81804424008015009030701c0c0c2c0d81e4800903802030410358014a061260f03241c03292801115400c44004001da07480c1c00020580e16800904010506440074850b082d070700c08205041206245800300307650051442041494140d50743d0890180c01417501040d01c1d03000e042c80d030780045010381080d000280b80c803003504103000180c091640140380e214111440c6240c039051083d15450306005001482d00004085081031200304203a42d507050704811181c0d43c40d040c0103105995610400c2c00c1c540e480e18154000101d072580841a155240c3c04001a103190495041c0300c1d43e60380300d0080c0b01d05040b0303180d05081b58114004010150825a18841d52a607845514001904143c419884070000d0344013000c0c11192040c607038081c8411502d5504040c0c0e01c0b510342440c0340d4005e1514025003002c0c1d8012070702c1d02d05500100c030310754041c03e80252911030ba500c1000408641352026170030050105c04001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 900175000 1250 900173750 900173759
    0xe100b03060c0d110a030f0e070302030601090c2304050a08030a08180f0f03130e100312140a0c0b0c090a0303120e03030a0903020d02150c1b0f0d27 65
    0x600203250f003484551002540e569004a0031149410812940e80000d540d031450b008400218410340c0b640c60303001030003007080e24910760002c0d59a0f001402612210b80e200d04c0d644200c5800f43c40041304038011004004803078003620300510b016812030700c91244075001c90746c0002480b010200480342d050300103907620407080e81c480c0340c01740781460030710b24010440c8107061800c0c001100500141c00710010513400303565a44c2d84480e008056104d00d0300403005502c100c400340624401e03d0340c501411641d010390030012480300800250f606000301d800c907010300300d00000c016180903401414405454845c1c000300c0310903201ca40c1c80a0590140030356880d00304203c12814070100c0e018600c0c50703005034003000011400ea4480c040d210300315042030703809a102988580e160740030150180003119520142d880180114400c3c02d099040720180a044500424400180300d000e9082c0d0110208030701c5007000880740c40d0110844503540c0d070325118042c1c0300000d81070005200317461000e120146e0007040c200d40c103900003400e0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 900176250 1250 900175000 900175021
    0x10b07030f0512040312050703020a0203090f030a08030406090627032a060e07080c0102070e1e0f0f010915030b19150608090a1e02040f020c010e100b0306 68
    0x7100c08900b888018862280c1c48058402003511843c841d6880044228a00c0c503840199000900450249801402031009066000017a100e0440d4210f0350382da00c02c00800080303801c10408007006858001d00201300014004182c0007440e00d1386c4580b10400c40b000084040b80c0040c5582201c3c100c11510910030300012a100d50000e480d4150b0f00c122101024040501b040c80c15a0071040032140303141c503a120010402c60030b018000007408a60050b1101c4410440000c0d261115402504910101c1d00082241a0000314400954400d51701180c007190410f24442d40b60000b0485800084046501c00824080382c14020702d0883c3d100d134403203004d2044c15a900c402c40c8200040c250a1440b40341c2d20300300b1540150b030044c0c9001d8401050040102420010300a0405500030b0040d80154850b141e040c0c00110f1070700300101c60407010869803116190320300c0001c2c090090035200e50003440c00030816501000066211503c0e03500d02208441d5001c03c048003c1055880d007a030120b605811141c0020301c05000c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 900177500 1250 900176250 900176267
    0xa09170d0b0603090106060e0a0e13111801090c111c020102130905060a09050606041401020c03011a120a05060f07050d1e06080a0f080f0c120c01060e010b0703 70
    0x10312100840d0000070503020452640040320030b0561603440f8101013160340d411a0005204080c00d0303130283c20807403c120502096102c003030200c0005070459840007041c0410640004100c800050001c450001d00d4100e400f8442c01c203004100e1441d162640184071680141a05818400040b014000e2100c001c481c0c6c1244440d004241d00555408008031250850781c000f20802800007200b00040d2410848240a5120125081440c3c0c07030340742605010050f0f41e0602960200c0e4803202541000d240844c004174240301400708110b406600f8050b00c8284109052414009110b007520b172451901ca155070420b50f105110070010b441d603000b800104482107110b003607055000c40d903424104d1a0140e004040ca040790896130034824681d507070a10054110001c1d01403040200b0109008005007085910341020f501d00d612402049554001100207480c2230610554902c80306080541d84403a0080318418050b0340195009881d551910802003900c4aa100d15141030b02d0050055608200340c90780c00703541c0c500 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 900178750 1250 900177500 900177517
    0xe071b0b0601140d0203041e21050d05160e060f030115090302030708160f0501050a080403090b0c060103120507030906050c07090507030903030c03020406050901120b0d0b0f0a0917 79
    0x8a014400020440080101a00055102d00690720f11f4503080142c90b00c000102400c1d110688024202d02150004041d0300030320405440090f40314002d840f080c1c2e00c0b0712030042c00e412218100302c10070a41c884441c3c01185964419292075170000b03803010400a0521625129140000c800c0c8010310119290013069440120343e1300b0603c0255459400181c50241140d007c440c0799400702c945c06100c071101d1075602e8024481c0070348050303c49042c840040d15a000340701c001c5c0204141280020180f5104208400080c0050300445580392034100034180c4582007400251035101c003506440404504c00c108803a01150995519800141080001c41e0640c1c0066041a5544a42000860301c00c01c0e43c8a5107010307117600d440000d400000c521f005002c3c0c459261000d424035106010030855980c0140c06c40d5503010007480c10b003945244c3c012201005000b145516a004a04200d0340c00400c980004030314028840d10401190503911080c1440650349030304070041c060650742030340034503550070940a01b5058 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 900179856 1106 900178750 900178757
    0xf03070f02060408030c0c0a1209080114060609060c0109060c0c0209060d170a03060902030f010e09010e070905090109060c090911090d020d14030f040e071b0b0601 72
    0x1408024003c2045040029101d81540c1040c018070303c5950f8411a42d030340800c4441e27801410100c0030b0080302c590b58078002c00002c3c8001103c4c00e65105d04001480d02d460400c45505208898005a00808142d901d5002d10300025002e4050810400003c0e03681e55400045030042082c1c01202070b10080c02000902c00c0c2c1300104440107224502919030005095966070080030850041c40c85501003081c0341c1c804024009801826400d0038100c54001c4126002074442807052404c84620b00d400b54010b9002e49030800003008160811544240c00100005401000c0d8031000180d0703904403080c41c00100b1210f800c1c07008201d01d21030003440040301c4c0010750404480c0c40c00b04054060822000e80716603240c410300f074200107540d9246000e105100e0252502d0b503443c90310b001201e8001c0d025072802d0404502c005900f00d44101c030701001d00d208000d150f03641c050144d00c400e20206000340465040 = true := by decide +kernel

theorem cover : BRFrame.Cov 900000000 900179856 := by
  have h0 := BRFrame.cov_init 900000000
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900000000 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 900000000 ≤ n) (h2 : n < 900179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
